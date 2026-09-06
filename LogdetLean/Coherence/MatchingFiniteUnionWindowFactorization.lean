import LogdetLean.Coherence.CanonicalFiniteUnionWindow
import LogdetLean.Coherence.CanonicalFiniteUnionConditionalCLT
import LogdetLean.Coherence.FiniteUnionFactorialExpansion
import LogdetLean.Coherence.MatchingWindowFactorization
/-!
# Matching transport and factorization for a finite union of score windows

For a finite family `W` of pairwise-disjoint half-open normalized score
windows, this module transports every ordered matching to the canonical
consecutive-pair matching and proves its exact finite-sample joint
log-determinant factorization.  The canonical conditioning factor is defined
for the whole union, rather than for one constituent interval.

No asymptotic or point-process statement is made here.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

/-- Centered finite-family presentation of the arbitrary ordered-tuple
finite-union joint event. -/
def familyOrderedTupleFiniteUnionWindowJointEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    Set (Fin p → centeredSubspace (m + 1)) :=
  {v | centeredFamilyZ0mpStatistic m p v ≤ z ∧
    ∀ i : Fin k,
      centeredFamilyCoherencePointScore m p v
        (orderedEdgeEndpointMap edges (i, false))
        (orderedEdgeEndpointMap edges (i, true)) ∈ finiteScoreWindowUnion W}

/-- Centered finite-family event for the canonical consecutive-pair
matching in the same finite score-window union. -/
def canonicalMatchingFamilyFiniteUnionWindowJointEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (hkp : 2 * k ≤ p) (z : ℝ) :
    Set (Fin p → centeredSubspace (m + 1)) :=
  {v | centeredFamilyZ0mpStatistic m p v ≤ z ∧
    ∀ i : Fin k,
      centeredFamilyCoherencePointScore m p v
        (canonicalEndpointEmbedding hkp (i, false))
        (canonicalEndpointEmbedding hkp (i, true)) ∈ finiteScoreWindowUnion W}

/-- A normalized finite-family score belongs to the normalized finite union
iff its squared normalized-Gram entry belongs to the corresponding raw
finite union. -/
theorem centeredFamilyCoherencePointScore_mem_finiteUnion_iff
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (hm0 : 0 < m)
    (v : Fin p → centeredSubspace (m + 1)) (i j : Fin p) :
    centeredFamilyCoherencePointScore m p v i j ∈ finiteScoreWindowUnion W ↔
      (normalizedGram v i j) ^ 2 ∈
        canonicalMatchingRawFiniteWindowUnion W m p := by
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨u, hu⟩
    exact Set.mem_iUnion.mpr ⟨u,
      (centeredFamilyCoherencePointScore_mem_Ioc_iff
        m p hm0 v i j (W.lower u) (W.upper u)).1 hu⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨u, hu⟩
    exact Set.mem_iUnion.mpr ⟨u,
      (centeredFamilyCoherencePointScore_mem_Ioc_iff
        m p hm0 v i j (W.lower u) (W.upper u)).2 hu⟩

theorem measurableSet_familyOrderedTupleFiniteUnionWindowJointEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    MeasurableSet
      (familyOrderedTupleFiniteUnionWindowJointEvent W m p k z edges) := by
  have hbulk : MeasurableSet
      {v : Fin p → centeredSubspace (m + 1) |
        centeredFamilyZ0mpStatistic m p v ≤ z} := by
    unfold centeredFamilyZ0mpStatistic
    exact measurableSet_le
      (((measurable_det_normalizedGram
        (E := centeredSubspace (m + 1)) p).log.sub
          measurable_const).div_const _) measurable_const
  have hedge : MeasurableSet
      {v : Fin p → centeredSubspace (m + 1) |
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m p v
            (orderedEdgeEndpointMap edges (i, false))
            (orderedEdgeEndpointMap edges (i, true)) ∈ finiteScoreWindowUnion W} := by
    rw [show {v : Fin p → centeredSubspace (m + 1) |
          ∀ i : Fin k,
            centeredFamilyCoherencePointScore m p v
              (orderedEdgeEndpointMap edges (i, false))
              (orderedEdgeEndpointMap edges (i, true)) ∈ finiteScoreWindowUnion W} =
        ⋂ i : Fin k,
          centeredFamilyCoherencePointScore m p
            (i := orderedEdgeEndpointMap edges (i, false))
            (j := orderedEdgeEndpointMap edges (i, true)) ⁻¹'
              finiteScoreWindowUnion W by
      ext v
      simp]
    exact MeasurableSet.iInter fun i ↦
      (measurableSet_finiteScoreWindowUnion W).preimage
        (measurable_centeredFamilyCoherencePointScore m p
          (orderedEdgeEndpointMap edges (i, false))
          (orderedEdgeEndpointMap edges (i, true)))
  exact hbulk.inter hedge

theorem measurableSet_canonicalMatchingFamilyFiniteUnionWindowJointEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (hkp : 2 * k ≤ p) (z : ℝ) :
    MeasurableSet
      (canonicalMatchingFamilyFiniteUnionWindowJointEvent
        W m p k hkp z) := by
  have hbulk : MeasurableSet
      {v : Fin p → centeredSubspace (m + 1) |
        centeredFamilyZ0mpStatistic m p v ≤ z} := by
    unfold centeredFamilyZ0mpStatistic
    exact measurableSet_le
      (((measurable_det_normalizedGram
        (E := centeredSubspace (m + 1)) p).log.sub
          measurable_const).div_const _) measurable_const
  have hedge : MeasurableSet
      {v : Fin p → centeredSubspace (m + 1) |
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m p v
            (canonicalEndpointEmbedding hkp (i, false))
            (canonicalEndpointEmbedding hkp (i, true)) ∈ finiteScoreWindowUnion W} := by
    rw [show {v : Fin p → centeredSubspace (m + 1) |
          ∀ i : Fin k,
            centeredFamilyCoherencePointScore m p v
              (canonicalEndpointEmbedding hkp (i, false))
              (canonicalEndpointEmbedding hkp (i, true)) ∈ finiteScoreWindowUnion W} =
        ⋂ i : Fin k,
          centeredFamilyCoherencePointScore m p
            (i := canonicalEndpointEmbedding hkp (i, false))
            (j := canonicalEndpointEmbedding hkp (i, true)) ⁻¹'
              finiteScoreWindowUnion W by
      ext v
      simp]
    exact MeasurableSet.iInter fun i ↦
      (measurableSet_finiteScoreWindowUnion W).preimage
        (measurable_centeredFamilyCoherencePointScore m p
          (canonicalEndpointEmbedding hkp (i, false))
          (canonicalEndpointEmbedding hkp (i, true)))
  exact hbulk.inter hedge

/-- Centering the raw sample identifies the raw and finite-family
finite-union joint events. -/
theorem preimage_familyOrderedTupleFiniteUnionWindowJointEvent_centeredNested
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      nestedTupleToFin p (centerNested (m + 1) p data)) ⁻¹'
        familyOrderedTupleFiniteUnionWindowJointEvent W m p k z edges =
      orderedTupleFiniteUnionWindowJointEvent W m p k z edges := by
  ext data
  change
    (centeredFamilyZ0mpStatistic m p
          (nestedTupleToFin p (centerNested (m + 1) p data)) ≤ z ∧
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m p
            (nestedTupleToFin p (centerNested (m + 1) p data))
            (orderedEdgeEndpointMap edges (i, false))
            (orderedEdgeEndpointMap edges (i, true)) ∈ finiteScoreWindowUnion W) ↔
      (Z0mpStatistic m p data ≤ z ∧
        ∀ i : Fin k,
          coherencePointScore m p data (edges i) ∈ finiteScoreWindowUnion W)
  rw [centeredFamilyZ0mpStatistic_centeredNested]
  simp [centeredFamilyCoherencePointScore, coherencePointScore,
    scaledSquaredCorrelationScore, centeredCorrelationMatrix,
    orderedEdgeEndpointMap, correlationEdgeEndpoint]

/-- Matching-to-canonical column permutations pull back the canonical
finite-union event exactly. -/
theorem preimage_canonicalMatchingFamilyFiniteUnionWindowJointEvent_permuteColumns
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) (hmatching : edges.IsMatching)
    (σ : Equiv.Perm (Fin p))
    (hσ : ∀ ib : Fin k × Bool,
      σ (orderedEdgeEndpointMap edges ib) =
        canonicalEndpointEmbedding (two_mul_le_of_isMatching hmatching) ib) :
    permuteColumns (E := centeredSubspace (m + 1)) σ ⁻¹'
        canonicalMatchingFamilyFiniteUnionWindowJointEvent W m p k
          (two_mul_le_of_isMatching hmatching) z =
      familyOrderedTupleFiniteUnionWindowJointEvent W m p k z edges := by
  ext v
  change
    (centeredFamilyZ0mpStatistic m p (permuteColumns σ v) ≤ z ∧
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m p (permuteColumns σ v)
            (canonicalEndpointEmbedding
              (two_mul_le_of_isMatching hmatching) (i, false))
            (canonicalEndpointEmbedding
              (two_mul_le_of_isMatching hmatching) (i, true)) ∈
              finiteScoreWindowUnion W) ↔
      (centeredFamilyZ0mpStatistic m p v ≤ z ∧
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m p v
            (orderedEdgeEndpointMap edges (i, false))
            (orderedEdgeEndpointMap edges (i, true)) ∈ finiteScoreWindowUnion W)
  rw [centeredFamilyZ0mpStatistic_permuteColumns]
  constructor
  · rintro ⟨hbulk, hedge⟩
    refine ⟨hbulk, fun i ↦ ?_⟩
    have hi := hedge i
    rw [← hσ (i, false), ← hσ (i, true),
      centeredFamilyCoherencePointScore_permuteColumns_apply_image] at hi
    exact hi
  · rintro ⟨hbulk, hedge⟩
    refine ⟨hbulk, fun i ↦ ?_⟩
    have hi := hedge i
    rw [← hσ (i, false), ← hσ (i, true),
      centeredFamilyCoherencePointScore_permuteColumns_apply_image]
    exact hi

/-- The raw nested Gaussian probability equals the centered finite-family
probability for the finite-union event. -/
theorem orderedTupleFiniteUnionWindowJointEvent_probability_eq_family
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (familyOrderedTupleFiniteUnionWindowJointEvent W m p k z edges) := by
  let F := fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
    nestedTupleToFin p (centerNested (m + 1) p data)
  let mu := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) p
  let nu := Measure.pi fun _ : Fin p ↦
    stdGaussian (centeredSubspace (m + 1))
  have hF : Measurable F :=
    (measurable_nestedTupleToFin (α := centeredSubspace (m + 1)) p).comp
      (measurable_centerNested (m + 1) p)
  have hmap : Measure.map F mu = nu := by
    have h := (measurePreserving_permuteCenteredNestedColumns
      (m + 1) p (Equiv.refl (Fin p))).map_eq
    have hfun :
        (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
          permuteColumns (Equiv.refl (Fin p))
            (nestedTupleToFin p (centerNested (m + 1) p data))) = F := by
      funext data
      ext i
      simp [F, permuteColumns]
    rw [hfun] at h
    simpa [mu, nu] using h
  have hset := measurableSet_familyOrderedTupleFiniteUnionWindowJointEvent
    W m p k z edges
  calc
    mu.real (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) =
        mu.real (F ⁻¹'
          familyOrderedTupleFiniteUnionWindowJointEvent W m p k z edges) := by
      rw [preimage_familyOrderedTupleFiniteUnionWindowJointEvent_centeredNested]
    _ = (Measure.map F mu).real
          (familyOrderedTupleFiniteUnionWindowJointEvent W m p k z edges) := by
      change
        (mu (F ⁻¹'
          familyOrderedTupleFiniteUnionWindowJointEvent W m p k z edges)).toReal =
          ((Measure.map F mu)
            (familyOrderedTupleFiniteUnionWindowJointEvent
              W m p k z edges)).toReal
      rw [Measure.map_apply hF hset]
    _ = nu.real
          (familyOrderedTupleFiniteUnionWindowJointEvent W m p k z edges) := by
      rw [hmap]

/-- Exact exchangeability identity for a matching in a finite score-window
union. -/
theorem orderedMatchingFiniteUnionWindowJointEvent_probability_eq_canonical
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) (hmatching : edges.IsMatching) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyFiniteUnionWindowJointEvent W m p k
          (two_mul_le_of_isMatching hmatching) z) := by
  rw [orderedTupleFiniteUnionWindowJointEvent_probability_eq_family]
  rcases exists_matchingToCanonicalPermutation edges hmatching with
    ⟨σ, hσ⟩
  let mu := Measure.pi fun _ : Fin p ↦
    stdGaussian (centeredSubspace (m + 1))
  let A := canonicalMatchingFamilyFiniteUnionWindowJointEvent W m p k
    (two_mul_le_of_isMatching hmatching) z
  have hperm :=
    (measurePreserving_permuteGaussianColumns
      (E := centeredSubspace (m + 1)) σ).map_eq
  have hA : MeasurableSet A :=
    measurableSet_canonicalMatchingFamilyFiniteUnionWindowJointEvent
      W m p k (two_mul_le_of_isMatching hmatching) z
  calc
    mu.real (familyOrderedTupleFiniteUnionWindowJointEvent
        W m p k z edges) =
        mu.real (permuteColumns σ ⁻¹' A) := by
      rw [preimage_canonicalMatchingFamilyFiniteUnionWindowJointEvent_permuteColumns
        W m p k z edges hmatching σ hσ]
    _ = (Measure.map (permuteColumns σ) mu).real A := by
      change (mu (permuteColumns σ ⁻¹' A)).toReal =
        ((Measure.map (permuteColumns σ) mu) A).toReal
      rw [Measure.map_apply (measurable_permuteColumns σ) hA]
    _ = mu.real A := by rw [hperm]

theorem orderedMatchingFiniteUnionWindowJointEvent_probability_eq_canonical_of_mem
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ)
    (edges : OrderedDistinctEdgeTuple p k)
    (hedges : edges ∈ orderedMatchingTuples p k) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyFiniteUnionWindowJointEvent W m p k
          (two_mul_le_of_isMatching
            (isMatching_of_mem_orderedMatchingTuples hedges)) z) := by
  exact orderedMatchingFiniteUnionWindowJointEvent_probability_eq_canonical
    W m p k z edges (isMatching_of_mem_orderedMatchingTuples hedges)

/-! ## Canonical finite-union event on the fixed prefix -/

/-- Direct finite-family form of the canonical event in which every selected
pair belongs to the raw squared-correlation set corresponding to `W`. -/
def canonicalFamilyMatchingFiniteUnionEvent
    {ι : Type*} {E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : FiniteScoreWindowFamily ι) (k m p : ℕ) :
    Set (Fin (2 * k) → E) :=
  {v | ∀ j : Fin k,
    squaredNormalizedInner
      (v (canonicalEvenIndex k j)) (v (canonicalOddIndex k j)) ∈
        canonicalMatchingRawFiniteWindowUnion W m p}

theorem measurableSet_canonicalFamilyMatchingFiniteUnionEvent
    {ι : Type*} {E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : FiniteScoreWindowFamily ι) (k m p : ℕ) :
    MeasurableSet
      (canonicalFamilyMatchingFiniteUnionEvent (E := E) W k m p) := by
  rw [show canonicalFamilyMatchingFiniteUnionEvent (E := E) W k m p =
      ⋂ j : Fin k,
        {v | squaredNormalizedInner
          (v (canonicalEvenIndex k j)) (v (canonicalOddIndex k j)) ∈
            canonicalMatchingRawFiniteWindowUnion W m p} by
    ext v
    simp [canonicalFamilyMatchingFiniteUnionEvent]]
  refine MeasurableSet.iInter fun j ↦ ?_
  have hpair : Measurable (fun v : Fin (2 * k) → E ↦
      (v (canonicalEvenIndex k j), v (canonicalOddIndex k j))) :=
    (measurable_pi_apply (canonicalEvenIndex k j)).prodMk
      (measurable_pi_apply (canonicalOddIndex k j))
  have hscore : Measurable (fun v : Fin (2 * k) → E ↦
      squaredNormalizedInner
        (v (canonicalEvenIndex k j)) (v (canonicalOddIndex k j))) := by
    change Measurable
      ((Function.uncurry (squaredNormalizedInner (E := E))) ∘
        fun v : Fin (2 * k) → E ↦
          (v (canonicalEvenIndex k j), v (canonicalOddIndex k j)))
    exact (measurable_uncurry_squaredNormalizedInner (E := E)).comp hpair
  exact (measurableSet_canonicalMatchingRawFiniteWindowUnion W m p).preimage
    hscore

/-- The ordered-forest canonical finite-union event equals its direct
finite-family presentation. -/
theorem preimage_canonicalFamilyMatchingFiniteUnionEvent_nestedTupleToFin
    {ι : Type*} {E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : FiniteScoreWindowFamily ι) (k m p : ℕ) :
    nestedTupleToFin (α := E) (2 * k) ⁻¹'
        canonicalFamilyMatchingFiniteUnionEvent (E := E) W k m p =
      canonicalGaussianMatchingFiniteUnionEvent (E := E) W m p k := by
  ext z
  induction k with
  | zero =>
      simp [canonicalFamilyMatchingFiniteUnionEvent,
        canonicalGaussianMatchingFiniteUnionEvent,
        canonicalMatchingScoreFiniteUnionEvent, orderedForestScores,
        sequentialStatistic]
  | succ k ih =>
      rcases z with ⟨⟨past, u⟩, v⟩
      unfold canonicalFamilyMatchingFiniteUnionEvent
        canonicalGaussianMatchingFiniteUnionEvent
      simp only [Set.mem_preimage]
      rw [orderedForestScores_canonicalMatching_pair_succ]
      change
        (∀ j : Fin (k + 1),
          squaredNormalizedInner
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalEvenIndex (k + 1) j))
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalOddIndex (k + 1) j)) ∈
            canonicalMatchingRawFiniteWindowUnion W m p) ↔
          ((orderedForestScores (E := E) canonicalMatchingForest
                (2 * k) past ∈
              canonicalMatchingScoreFiniteUnionEvent W m p k ∧
              (0 : ℝ) ∈ Set.univ) ∧
            squaredNormalizedInner u v ∈
              canonicalMatchingRawFiniteWindowUnion W m p)
      simp only [Set.mem_univ, and_true]
      change
        (∀ j : Fin (k + 1),
          squaredNormalizedInner
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalEvenIndex (k + 1) j))
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalOddIndex (k + 1) j)) ∈
            canonicalMatchingRawFiniteWindowUnion W m p) ↔
          (past ∈ canonicalGaussianMatchingFiniteUnionEvent
              (E := E) W m p k ∧
            squaredNormalizedInner u v ∈
              canonicalMatchingRawFiniteWindowUnion W m p)
      rw [← ih past]
      simp only [Set.mem_preimage]
      constructor
      · intro h
        constructor
        · intro j
          have hj := h j.castSucc
          rw [nestedTupleToFin_pair_even_castSucc past u v j,
            nestedTupleToFin_pair_odd_castSucc past u v j] at hj
          exact hj
        · have hlast := h (Fin.last k)
          rw [nestedTupleToFin_pair_even_last past u v,
            nestedTupleToFin_pair_odd_last past u v] at hlast
          exact hlast
      · rintro ⟨hold, hlast⟩ j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · rw [nestedTupleToFin_pair_even_last past u v,
            nestedTupleToFin_pair_odd_last past u v]
          exact hlast
        · rw [nestedTupleToFin_pair_even_castSucc past u v i,
            nestedTupleToFin_pair_odd_castSucc past u v i]
          exact hold i

/-- The canonical finite-family finite-union joint event pulls back to the
raw full-statistic lower tail intersected with the lifted canonical prefix
finite-union event. -/
theorem preimage_canonicalMatchingFamilyFiniteUnionWindowJointEvent_centeredNested
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m k r : ℕ) (hm0 : 0 < m) (z : ℝ) :
    let p := 2 * k + r
    let hkp : 2 * k ≤ p := Nat.le_add_right _ _
    let s : Set (NestedTuple (centeredSubspace (m + 1)) (2 * k)) :=
      canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p
    (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      nestedTupleToFin p (centerNested (m + 1) p data)) ⁻¹'
        canonicalMatchingFamilyFiniteUnionWindowJointEvent
          W m p k hkp z =
      {data | Z0mpStatistic m p data ≤ z} ∩
        centeredGaussianPrefixEvent m (2 * k) r s := by
  dsimp only
  ext data
  change
    (centeredFamilyZ0mpStatistic m (2 * k + r)
          (nestedTupleToFin (2 * k + r)
            (centerNested (m + 1) (2 * k + r) data)) ≤ z ∧
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m (2 * k + r)
            (nestedTupleToFin (2 * k + r)
              (centerNested (m + 1) (2 * k + r) data))
            (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
              (i, false))
            (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
              (i, true)) ∈ finiteScoreWindowUnion W) ↔
      (Z0mpStatistic m (2 * k + r) data ≤ z ∧
        data ∈ centeredGaussianPrefixEvent m (2 * k) r
          (canonicalCenteredMatchingFiniteUnionPrefixEvent
            W k m (2 * k + r)))
  rw [centeredFamilyZ0mpStatistic_centeredNested]
  rw [mem_centeredGaussianPrefixEvent_iff]
  apply and_congr Iff.rfl
  unfold canonicalCenteredMatchingFiniteUnionPrefixEvent
  rw [← Set.ext_iff.mp
    (preimage_canonicalFamilyMatchingFiniteUnionEvent_nestedTupleToFin
      (E := centeredSubspace (m + 1)) W k m (2 * k + r)) _]
  unfold canonicalFamilyMatchingFiniteUnionEvent
  constructor
  · intro hedge i
    let full := nestedTupleToFin (2 * k + r)
      (centerNested (m + 1) (2 * k + r) data)
    let pref := nestedTupleToFin (2 * k)
      (nestedTuplePrefix (2 * k) r
        (centerNested (m + 1) (2 * k + r) data))
    have hscore :
        (normalizedGram full
          (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
            (i, false))
          (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
            (i, true))) ^ 2 =
          squaredNormalizedInner
            (pref (canonicalEvenIndex k i))
            (pref (canonicalOddIndex k i)) := by
      dsimp [full, pref]
      rw [canonicalEndpointEmbedding_false_eq_castAdd,
        canonicalEndpointEmbedding_true_eq_castAdd,
        canonical_normalizedGram_apply_sq_eq_squaredNormalizedInner_total,
        nestedTupleToFin_castAdd_eq_prefix,
        nestedTupleToFin_castAdd_eq_prefix]
    have hi :=
      (centeredFamilyCoherencePointScore_mem_finiteUnion_iff
        W m (2 * k + r) hm0 full
        (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
          (i, false))
        (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
          (i, true))).1 (hedge i)
    rw [hscore] at hi
    exact hi
  · intro hedge i
    let full := nestedTupleToFin (2 * k + r)
      (centerNested (m + 1) (2 * k + r) data)
    let pref := nestedTupleToFin (2 * k)
      (nestedTuplePrefix (2 * k) r
        (centerNested (m + 1) (2 * k + r) data))
    have hscore :
        (normalizedGram full
          (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
            (i, false))
          (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
            (i, true))) ^ 2 =
          squaredNormalizedInner
            (pref (canonicalEvenIndex k i))
            (pref (canonicalOddIndex k i)) := by
      dsimp [full, pref]
      rw [canonicalEndpointEmbedding_false_eq_castAdd,
        canonicalEndpointEmbedding_true_eq_castAdd,
        canonical_normalizedGram_apply_sq_eq_squaredNormalizedInner_total,
        nestedTupleToFin_castAdd_eq_prefix,
        nestedTupleToFin_castAdd_eq_prefix]
    apply (centeredFamilyCoherencePointScore_mem_finiteUnion_iff
      W m (2 * k + r) hm0 full
      (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
        (i, false))
      (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
        (i, true))).2
    rw [hscore]
    exact hedge i

/-! ## Exact finite factorization -/

/-- Exact canonical factorization for a finite union of disjoint score
windows, in prefix-plus-tail coordinates. -/
theorem canonicalMatchingFamilyFiniteUnionWindowJointEvent_probability_factorization_add
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m k r : ℕ) (hm : 2 ≤ m) (hpm : 2 * k + r ≤ m) (z : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingFiniteUnionPrefixEvent
        W k m (2 * k + r)) ≠ 0) :
    (Measure.pi fun _ : Fin (2 * k + r) ↦
      stdGaussian (centeredSubspace (m + 1))).real
      (canonicalMatchingFamilyFiniteUnionWindowJointEvent
        W m (2 * k + r) k (Nat.le_add_right _ _) z) =
      finiteUnionBetaProbability W m (2 * k + r) ^ k *
        canonicalFiniteUnionConditionedZ0mpCDFOrGaussian
          W k m (2 * k + r) z := by
  let q := 2 * k
  let p := q + r
  let s : Set (NestedTuple (centeredSubspace (m + 1)) q) :=
    canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p
  let hs : MeasurableSet s :=
    measurableSet_canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p
  let A := centeredGaussianPrefixEvent m q r s
  let B : Set (NestedTuple (ObservationSpace (m + 1)) p) :=
    {data | Z0mpStatistic m p data ≤ z}
  let mu := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) p
  let nu := Measure.pi fun _ : Fin p ↦
    stdGaussian (centeredSubspace (m + 1))
  let F := fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
    nestedTupleToFin p (centerNested (m + 1) p data)
  have hqr : q + r ≤ m := by simpa [q] using hpm
  have hA : MeasurableSet A :=
    measurableSet_centeredGaussianPrefixEvent m q r hs
  have hB : MeasurableSet B :=
    measurableSet_le (measurable_Z0mpStatistic m p) measurable_const
  have hF : Measurable F :=
    (measurable_nestedTupleToFin (α := centeredSubspace (m + 1)) p).comp
      (measurable_centerNested (m + 1) p)
  have hmap : Measure.map F mu = nu := by
    have h := (measurePreserving_permuteCenteredNestedColumns
      (m + 1) p (Equiv.refl (Fin p))).map_eq
    have hfun :
        (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
          permuteColumns (Equiv.refl (Fin p))
            (nestedTupleToFin p (centerNested (m + 1) p data))) = F := by
      funext data
      ext i
      simp [F, permuteColumns]
    rw [hfun] at h
    simpa [mu, nu] using h
  have hcanonical :
      F ⁻¹' canonicalMatchingFamilyFiniteUnionWindowJointEvent
        W m p k (Nat.le_add_right _ _) z = B ∩ A := by
    simpa [q, p, s, A, B, F] using
      preimage_canonicalMatchingFamilyFiniteUnionWindowJointEvent_centeredNested
        W m k r (by omega) z
  have hset :=
    measurableSet_canonicalMatchingFamilyFiniteUnionWindowJointEvent
      W m p k (Nat.le_add_right _ _) z
  have hfamily :
      nu.real (canonicalMatchingFamilyFiniteUnionWindowJointEvent
        W m p k (Nat.le_add_right _ _) z) = mu.real (B ∩ A) := by
    calc
      nu.real (canonicalMatchingFamilyFiniteUnionWindowJointEvent
          W m p k (Nat.le_add_right _ _) z) =
          (Measure.map F mu).real
            (canonicalMatchingFamilyFiniteUnionWindowJointEvent
              W m p k (Nat.le_add_right _ _) z) := by rw [hmap]
      _ = mu.real (F ⁻¹'
            canonicalMatchingFamilyFiniteUnionWindowJointEvent
              W m p k (Nat.le_add_right _ _) z) := by
        change ((Measure.map F mu)
            (canonicalMatchingFamilyFiniteUnionWindowJointEvent
              W m p k (Nat.le_add_right _ _) z)).toReal =
          (mu (F ⁻¹' canonicalMatchingFamilyFiniteUnionWindowJointEvent
            W m p k (Nat.le_add_right _ _) z)).toReal
        rw [Measure.map_apply hF hset]
      _ = mu.real (B ∩ A) := by rw [hcanonical]
  have hmul := measureReal_inter_eq_cond_mul_measureReal mu A B hA
  have hmass :
      mu.real A = finiteUnionBetaProbability W m p ^ k := by
    have hpref := centeredGaussianPrefixEvent_probability
      m q r hqr s hs
    have hprefReal := congrArg ENNReal.toReal hpref
    calc
      mu.real A =
          (nestedProductMeasure
            (stdGaussian (centeredSubspace (m + 1))) q).real s := by
        simpa [Measure.real, mu, A, p] using hprefReal
      _ = finiteUnionBetaProbability W m p ^ k := by
        simpa [q, s] using
          canonicalCenteredMatchingFiniteUnionPrefixEvent_probability
            W m p hm k
  have hbulk :
      (mu[|A]).real B =
        canonicalFiniteUnionConditionedZ0mpCDFOrGaussian W k m p z := by
    have hjoint := conditionedPrefixTailJointOrGaussian_eq_of_add
      m q r s hs hqr (by simpa [q, p, s] using hs0)
    have hmapadd := map_add_centeredGaussianPrefixTailPair_cond_eq_map_Z0mp
      m q r hqr s hs (by simpa [q, p, s] using hs0)
    have hjointMeasure :
        (conditionedPrefixTailJointOrGaussian m q (q + r) s hs :
            Measure (ℝ × ℝ)) =
          Measure.map (centeredGaussianPrefixTailPairStatistic m q r)
            ((conditionedCenteredGaussianPrefixProbabilityMeasure
              m q r hqr s hs _ : ProbabilityMeasure _) : Measure _) :=
      congrArg (fun eta : ProbabilityMeasure (ℝ × ℝ) ↦
        (eta : Measure (ℝ × ℝ))) hjoint
    have hz' :
        canonicalFiniteUnionConditionedZ0mpCDFOrGaussian W k m p z =
          (Measure.map (Z0mpStatistic m (q + r)) (mu[|A])).real
            (Iic z) := by
      change
        (Measure.map (fun y : ℝ × ℝ ↦ y.1 + y.2)
          (conditionedPrefixTailJointOrGaussian m q (q + r) s hs :
            Measure (ℝ × ℝ))).real (Iic z) = _
      rw [hjointMeasure]
      rw [hmapadd]
      rfl
    rw [hz']
    dsimp [B, p]
    change
      ((mu[|A]) ((Z0mpStatistic m (q + r)) ⁻¹' Iic z)).toReal =
        ((Measure.map (Z0mpStatistic m (q + r)) (mu[|A]))
          (Iic z)).toReal
    rw [Measure.map_apply
      (measurable_Z0mpStatistic m (q + r)) measurableSet_Iic]
  calc
    (Measure.pi fun _ : Fin (2 * k + r) ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyFiniteUnionWindowJointEvent
          W m (2 * k + r) k (Nat.le_add_right _ _) z) =
      nu.real (canonicalMatchingFamilyFiniteUnionWindowJointEvent
        W m p k (Nat.le_add_right _ _) z) := by rfl
    _ = mu.real (B ∩ A) := hfamily
    _ = (mu[|A]).real B * mu.real A := hmul
    _ = finiteUnionBetaProbability W m p ^ k *
          canonicalFiniteUnionConditionedZ0mpCDFOrGaussian W k m p z := by
      rw [hmass, hbulk]
      ring
    _ = finiteUnionBetaProbability W m (2 * k + r) ^ k *
          canonicalFiniteUnionConditionedZ0mpCDFOrGaussian
            W k m (2 * k + r) z := by rfl

/-- Exact canonical finite-union factorization at arbitrary valid `p`. -/
theorem canonicalMatchingFamilyFiniteUnionWindowJointEvent_probability_factorization
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (hm : 2 ≤ m) (hqp : 2 * k ≤ p) (hpm : p ≤ m)
    (z : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p) ≠ 0) :
    (Measure.pi fun _ : Fin p ↦
      stdGaussian (centeredSubspace (m + 1))).real
      (canonicalMatchingFamilyFiniteUnionWindowJointEvent W m p k hqp z) =
      finiteUnionBetaProbability W m p ^ k *
        canonicalFiniteUnionConditionedZ0mpCDFOrGaussian W k m p z := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hqp
  exact
    canonicalMatchingFamilyFiniteUnionWindowJointEvent_probability_factorization_add
      W m k r hm hpm z hs0

/-- Every ordered matching summand in the finite union has the same exact
Beta-union-mass times union-conditioned-bulk factorization. -/
theorem orderedMatchingFiniteUnionWindowJointEvent_probability_factorization_of_mem
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (hm : 2 ≤ m) (hpm : p ≤ m) (z : ℝ)
    (edges : OrderedDistinctEdgeTuple p k)
    (hedges : edges ∈ orderedMatchingTuples p k)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p) ≠ 0) :
    (nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) p).real
      (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) =
      finiteUnionBetaProbability W m p ^ k *
        canonicalFiniteUnionConditionedZ0mpCDFOrGaussian W k m p z := by
  have hmatching := isMatching_of_mem_orderedMatchingTuples hedges
  have hqp := two_mul_le_of_isMatching hmatching
  calc
    _ = (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyFiniteUnionWindowJointEvent
          W m p k hqp z) :=
      orderedMatchingFiniteUnionWindowJointEvent_probability_eq_canonical_of_mem
        W m p k z edges hedges
    _ = _ :=
      canonicalMatchingFamilyFiniteUnionWindowJointEvent_probability_factorization
        W m p k hm hqp hpm z hs0

end

end LogdetLean.Coherence
