import LogdetLean.Coherence.FactorialExpansion
import LogdetLean.Coherence.ColumnPermutation
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Fintype
/-!
# Transporting an arbitrary matching to the canonical matching

Every ordered matching uses `2*k` distinct column labels.  We extend the
injection from those labels to the first `2*k` canonical labels to a
permutation of all `p` columns.  Gaussian exchangeability, determinant
invariance, and entrywise normalized-Gram transport then give an exact
finite probability identity for the joint log-determinant/edge event.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- The standardized null log determinant written directly on a finite
family of centered Gaussian columns. -/
def centeredFamilyZ0mpStatistic (m p : ℕ)
    (v : Fin p → centeredSubspace (m + 1)) : ℝ :=
  (Real.log (normalizedGram v).det - nullCenterDigammaSeries m p) /
    Real.sqrt (nullVSeries m p)

/-- The finite-family version of one ordered-tuple joint event. -/
def familyOrderedTupleJointEvent
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    Set (Fin p → centeredSubspace (m + 1)) :=
  {v | centeredFamilyZ0mpStatistic m p v ≤ z ∧
    ∀ i : Fin k, threshold m p x <
      (m : ℝ) *
        (normalizedGram v
          (orderedEdgeEndpointMap edges (i, false))
          (orderedEdgeEndpointMap edges (i, true))) ^ 2}

/-- The canonical ordering of the `2*k` endpoint slots: the two endpoints
of edge `i` occupy columns `2*i` and `2*i+1`. -/
def canonicalEndpointEquiv (k : ℕ) : Fin k × Bool ≃ Fin (2 * k) :=
  ((Equiv.prodCongr (Equiv.refl (Fin k)) finTwoEquiv.symm).trans
    finProdFinEquiv).trans (finCongr (Nat.mul_comm k 2))

/-- Embed the canonical endpoint slots into the first `2*k` columns of a
`p`-column family. -/
def canonicalEndpointEmbedding {p k : ℕ} (hkp : 2 * k ≤ p) :
    (Fin k × Bool) ↪ Fin p :=
  (canonicalEndpointEquiv k).toEmbedding.trans (Fin.castLEEmb hkp)

@[simp]
theorem canonicalEndpointEmbedding_false_val
    {p k : ℕ} (hkp : 2 * k ≤ p) (i : Fin k) :
    (canonicalEndpointEmbedding hkp (i, false)).1 = 2 * i.1 := by
  simp [canonicalEndpointEmbedding, canonicalEndpointEquiv,
    finProdFinEquiv, finTwoEquiv]

@[simp]
theorem canonicalEndpointEmbedding_true_val
    {p k : ℕ} (hkp : 2 * k ≤ p) (i : Fin k) :
    (canonicalEndpointEmbedding hkp (i, true)).1 = 2 * i.1 + 1 := by
  simp [canonicalEndpointEmbedding, canonicalEndpointEquiv,
    finProdFinEquiv, finTwoEquiv]
  omega

/-- The same family event for the canonical consecutive-pair matching. -/
def canonicalMatchingFamilyJointEvent
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ)
    (hkp : 2 * k ≤ p) (z x : ℝ) :
    Set (Fin p → centeredSubspace (m + 1)) :=
  {v | centeredFamilyZ0mpStatistic m p v ≤ z ∧
    ∀ i : Fin k, threshold m p x <
      (m : ℝ) *
        (normalizedGram v
          (canonicalEndpointEmbedding hkp (i, false))
          (canonicalEndpointEmbedding hkp (i, true))) ^ 2}

/-- Reading and centering the raw nested sample gives the same standardized
statistic as the finite-family presentation. -/
theorem centeredFamilyZ0mpStatistic_centeredNested
    (m p : ℕ) (data : NestedTuple (ObservationSpace (m + 1)) p) :
    centeredFamilyZ0mpStatistic m p
        (nestedTupleToFin p (centerNested (m + 1) p data)) =
      Z0mpStatistic m p data := by
  unfold centeredFamilyZ0mpStatistic Z0mpStatistic
  rw [centeredSampleCorrelationDet_eq_nestedCenteredNormalizedGramDet
    (Nat.zero_lt_succ m)]
  rfl

/-- The raw ordered-tuple event is exactly the pullback of its centered
finite-family presentation. -/
theorem preimage_familyOrderedTupleJointEvent_centeredNested
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      nestedTupleToFin p (centerNested (m + 1) p data)) ⁻¹'
        familyOrderedTupleJointEvent threshold m p k z x edges =
      orderedTupleJointEvent threshold m p k z x edges := by
  ext data
  change
    (centeredFamilyZ0mpStatistic m p
          (nestedTupleToFin p (centerNested (m + 1) p data)) ≤ z ∧
        ∀ i : Fin k, threshold m p x <
          (m : ℝ) *
            (normalizedGram
              (nestedTupleToFin p (centerNested (m + 1) p data))
              (orderedEdgeEndpointMap edges (i, false))
              (orderedEdgeEndpointMap edges (i, true))) ^ 2) ↔
      (Z0mpStatistic m p data ≤ z ∧
        ∀ i : Fin k, threshold m p x <
          scaledSquaredCorrelationScore m p data (edges i).1)
  rw [centeredFamilyZ0mpStatistic_centeredNested]
  simp [scaledSquaredCorrelationScore, centeredCorrelationMatrix,
    orderedEdgeEndpointMap, correlationEdgeEndpoint]

/-- The finite-family ordered-tuple event is measurable. -/
theorem measurableSet_familyOrderedTupleJointEvent
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    MeasurableSet (familyOrderedTupleJointEvent threshold m p k z x edges) := by
  have hdet : Measurable (fun v : Fin p → centeredSubspace (m + 1) ↦
      centeredFamilyZ0mpStatistic m p v) := by
    unfold centeredFamilyZ0mpStatistic
    exact (((measurable_det_normalizedGram
      (E := centeredSubspace (m + 1)) p).log.sub measurable_const).div_const _)
  have hedge : MeasurableSet
      {v : Fin p → centeredSubspace (m + 1) |
        ∀ i : Fin k, threshold m p x <
          (m : ℝ) *
            (normalizedGram v
              (orderedEdgeEndpointMap edges (i, false))
              (orderedEdgeEndpointMap edges (i, true))) ^ 2} := by
    rw [show {v : Fin p → centeredSubspace (m + 1) |
          ∀ i : Fin k, threshold m p x <
            (m : ℝ) *
              (normalizedGram v
                (orderedEdgeEndpointMap edges (i, false))
                (orderedEdgeEndpointMap edges (i, true))) ^ 2} =
        ⋂ i : Fin k, {v | threshold m p x <
          (m : ℝ) *
            (normalizedGram v
              (orderedEdgeEndpointMap edges (i, false))
              (orderedEdgeEndpointMap edges (i, true))) ^ 2} by
      ext v
      simp]
    apply MeasurableSet.iInter
    intro i
    have hentry : Measurable
        (fun v : Fin p → centeredSubspace (m + 1) ↦
          normalizedGram v
            (orderedEdgeEndpointMap edges (i, false))
            (orderedEdgeEndpointMap edges (i, true))) := by
      exact (measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp measurable_normalizedGramFamily)
    exact measurableSet_lt measurable_const
      (measurable_const.mul (hentry.pow_const 2))
  exact (measurableSet_le hdet measurable_const).inter hedge

/-- The canonical finite-family joint event is measurable. -/
theorem measurableSet_canonicalMatchingFamilyJointEvent
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ)
    (hkp : 2 * k ≤ p) (z x : ℝ) :
    MeasurableSet
      (canonicalMatchingFamilyJointEvent threshold m p k hkp z x) := by
  have hdet : Measurable (fun v : Fin p → centeredSubspace (m + 1) ↦
      centeredFamilyZ0mpStatistic m p v) := by
    unfold centeredFamilyZ0mpStatistic
    exact (((measurable_det_normalizedGram
      (E := centeredSubspace (m + 1)) p).log.sub measurable_const).div_const _)
  have hedge : MeasurableSet
      {v : Fin p → centeredSubspace (m + 1) |
        ∀ i : Fin k, threshold m p x <
          (m : ℝ) *
            (normalizedGram v
              (canonicalEndpointEmbedding hkp (i, false))
              (canonicalEndpointEmbedding hkp (i, true))) ^ 2} := by
    rw [show {v : Fin p → centeredSubspace (m + 1) |
          ∀ i : Fin k, threshold m p x <
            (m : ℝ) *
              (normalizedGram v
                (canonicalEndpointEmbedding hkp (i, false))
                (canonicalEndpointEmbedding hkp (i, true))) ^ 2} =
        ⋂ i : Fin k, {v | threshold m p x <
          (m : ℝ) *
            (normalizedGram v
              (canonicalEndpointEmbedding hkp (i, false))
              (canonicalEndpointEmbedding hkp (i, true))) ^ 2} by
      ext v
      simp]
    apply MeasurableSet.iInter
    intro i
    have hentry : Measurable
        (fun v : Fin p → centeredSubspace (m + 1) ↦
          normalizedGram v
            (canonicalEndpointEmbedding hkp (i, false))
            (canonicalEndpointEmbedding hkp (i, true))) := by
      exact (measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp measurable_normalizedGramFamily)
    exact measurableSet_lt measurable_const
      (measurable_const.mul (hentry.pow_const 2))
  exact (measurableSet_le hdet measurable_const).inter hedge

/-- Column permutations preserve the finite-family standardized log
determinant exactly. -/
theorem centeredFamilyZ0mpStatistic_permuteColumns
    (m p : ℕ) (σ : Equiv.Perm (Fin p))
    (v : Fin p → centeredSubspace (m + 1)) :
    centeredFamilyZ0mpStatistic m p (permuteColumns σ v) =
      centeredFamilyZ0mpStatistic m p v := by
  unfold centeredFamilyZ0mpStatistic
  rw [log_det_normalizedGram_permuteColumns]

/-- A matching has enough ambient columns to hold its `2*k` distinct
endpoint slots. -/
theorem two_mul_le_of_isMatching
    {p k : ℕ} {edges : OrderedDistinctEdgeTuple p k}
    (hmatching : edges.IsMatching) :
    2 * k ≤ p := by
  have hcard := Fintype.card_le_of_injective
    (orderedEdgeEndpointMap edges) hmatching
  simpa [Nat.mul_comm] using hcard

/-- Membership in the matching finset is exactly the endpoint-injectivity
property needed by the permutation construction. -/
theorem isMatching_of_mem_orderedMatchingTuples
    {p k : ℕ} {edges : OrderedDistinctEdgeTuple p k}
    (hedges : edges ∈ orderedMatchingTuples p k) :
    edges.IsMatching := by
  classical
  simpa [orderedMatchingTuples, orderedDistinctEdgeTuples] using
    (Finset.mem_filter.mp hedges).2

/-- Extend the arbitrary matching endpoint injection to a permutation that
sends every endpoint slot to its canonical consecutive-pair location. -/
theorem exists_matchingToCanonicalPermutation
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k)
    (hmatching : edges.IsMatching) :
    ∃ σ : Equiv.Perm (Fin p), ∀ ib : Fin k × Bool,
      σ (orderedEdgeEndpointMap edges ib) =
        canonicalEndpointEmbedding (two_mul_le_of_isMatching hmatching) ib := by
  exact Equiv.Perm.exists_extending_pair
    (orderedEdgeEndpointMap edges)
    (canonicalEndpointEmbedding (two_mul_le_of_isMatching hmatching))
    hmatching
    (canonicalEndpointEmbedding
      (two_mul_le_of_isMatching hmatching)).injective

/-- The selected permutation pulls the canonical finite-family joint event
back exactly to the event for the original ordered matching. -/
theorem preimage_canonicalMatchingFamilyJointEvent_permuteColumns
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) (hmatching : edges.IsMatching)
    (σ : Equiv.Perm (Fin p))
    (hσ : ∀ ib : Fin k × Bool,
      σ (orderedEdgeEndpointMap edges ib) =
        canonicalEndpointEmbedding (two_mul_le_of_isMatching hmatching) ib) :
    permuteColumns (E := centeredSubspace (m + 1)) σ ⁻¹'
        canonicalMatchingFamilyJointEvent threshold m p k
          (two_mul_le_of_isMatching hmatching) z x =
      familyOrderedTupleJointEvent threshold m p k z x edges := by
  ext v
  change
    (centeredFamilyZ0mpStatistic m p (permuteColumns σ v) ≤ z ∧
        ∀ i : Fin k, threshold m p x <
          (m : ℝ) *
            (normalizedGram (permuteColumns σ v)
              (canonicalEndpointEmbedding
                (two_mul_le_of_isMatching hmatching) (i, false))
              (canonicalEndpointEmbedding
                (two_mul_le_of_isMatching hmatching) (i, true))) ^ 2) ↔
      (centeredFamilyZ0mpStatistic m p v ≤ z ∧
        ∀ i : Fin k, threshold m p x <
          (m : ℝ) *
            (normalizedGram v
              (orderedEdgeEndpointMap edges (i, false))
              (orderedEdgeEndpointMap edges (i, true))) ^ 2)
  rw [centeredFamilyZ0mpStatistic_permuteColumns]
  constructor
  · rintro ⟨hbulk, hedge⟩
    refine ⟨hbulk, fun i ↦ ?_⟩
    have hi := hedge i
    rw [← hσ (i, false), ← hσ (i, true),
      normalizedGram_permuteColumns_apply_image] at hi
    exact hi
  · rintro ⟨hbulk, hedge⟩
    refine ⟨hbulk, fun i ↦ ?_⟩
    have hi := hedge i
    rw [← hσ (i, false), ← hσ (i, true),
      normalizedGram_permuteColumns_apply_image]
    exact hi

/-- The raw nested Gaussian probability equals the probability of the same
event in the centered finite-family Gaussian product model. -/
theorem orderedTupleJointEvent_probability_eq_family
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleJointEvent threshold m p k z x edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (familyOrderedTupleJointEvent threshold m p k z x edges) := by
  let F := fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
    nestedTupleToFin p (centerNested (m + 1) p data)
  let μ := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) p
  let ν := Measure.pi fun _ : Fin p ↦
    stdGaussian (centeredSubspace (m + 1))
  have hF : Measurable F :=
    (measurable_nestedTupleToFin (α := centeredSubspace (m + 1)) p).comp
      (measurable_centerNested (m + 1) p)
  have hmap : Measure.map F μ = ν := by
    have h := (measurePreserving_permuteCenteredNestedColumns
      (m + 1) p (Equiv.refl (Fin p))).map_eq
    have hfun :
        (fun z : NestedTuple (ObservationSpace (m + 1)) p ↦
          permuteColumns (Equiv.refl (Fin p))
            (nestedTupleToFin p (centerNested (m + 1) p z))) = F := by
      funext z
      ext i
      simp [F, permuteColumns]
    rw [hfun] at h
    simpa [μ, ν] using h
  have hset := measurableSet_familyOrderedTupleJointEvent
    threshold m p k z x edges
  calc
    μ.real (orderedTupleJointEvent threshold m p k z x edges) =
        μ.real (F ⁻¹'
          familyOrderedTupleJointEvent threshold m p k z x edges) := by
      rw [preimage_familyOrderedTupleJointEvent_centeredNested]
    _ = (Measure.map F μ).real
          (familyOrderedTupleJointEvent threshold m p k z x edges) := by
      change
        (μ (F ⁻¹' familyOrderedTupleJointEvent threshold m p k z x edges)).toReal =
          ((Measure.map F μ)
            (familyOrderedTupleJointEvent threshold m p k z x edges)).toReal
      rw [Measure.map_apply hF hset]
    _ = ν.real
          (familyOrderedTupleJointEvent threshold m p k z x edges) := by
      rw [hmap]

/-- Exact finite exchangeability identity: every ordered matching has the
same joint log-determinant/edge-event probability as the canonical matching
on the first `2*k` columns. -/
theorem orderedMatchingJointEvent_probability_eq_canonical
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) (hmatching : edges.IsMatching) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleJointEvent threshold m p k z x edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyJointEvent threshold m p k
          (two_mul_le_of_isMatching hmatching) z x) := by
  rw [orderedTupleJointEvent_probability_eq_family]
  rcases exists_matchingToCanonicalPermutation edges hmatching with
    ⟨σ, hσ⟩
  let μ := Measure.pi fun _ : Fin p ↦
    stdGaussian (centeredSubspace (m + 1))
  let A := canonicalMatchingFamilyJointEvent threshold m p k
    (two_mul_le_of_isMatching hmatching) z x
  have hperm :=
    (measurePreserving_permuteGaussianColumns
      (E := centeredSubspace (m + 1)) σ).map_eq
  have hA : MeasurableSet A :=
    measurableSet_canonicalMatchingFamilyJointEvent threshold m p k
      (two_mul_le_of_isMatching hmatching) z x
  calc
    μ.real (familyOrderedTupleJointEvent threshold m p k z x edges) =
        μ.real (permuteColumns σ ⁻¹' A) := by
      rw [preimage_canonicalMatchingFamilyJointEvent_permuteColumns
        threshold m p k z x edges hmatching σ hσ]
    _ = (Measure.map (permuteColumns σ) μ).real A := by
      change (μ (permuteColumns σ ⁻¹' A)).toReal =
        ((Measure.map (permuteColumns σ) μ) A).toReal
      rw [Measure.map_apply (measurable_permuteColumns σ) hA]
    _ = μ.real A := by rw [hperm]

/-- Membership in `orderedMatchingTuples` supplies the exact canonical
probability identity in the form used by the mixed-moment summation. -/
theorem orderedMatchingJointEvent_probability_eq_canonical_of_mem
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k)
    (hedges : edges ∈ orderedMatchingTuples p k) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleJointEvent threshold m p k z x edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyJointEvent threshold m p k
          (two_mul_le_of_isMatching
            (isMatching_of_mem_orderedMatchingTuples hedges)) z x) := by
  apply orderedMatchingJointEvent_probability_eq_canonical
  exact isMatching_of_mem_orderedMatchingTuples hedges

end

end LogdetLean.Coherence
