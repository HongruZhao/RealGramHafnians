import LogdetLean.Coherence.WindowFactorialExpansion
import LogdetLean.Coherence.CanonicalMatchingWindow
import LogdetLean.Coherence.CanonicalWindowConditionalCLT
import LogdetLean.Coherence.CanonicalMatchingFactorization
import LogdetLean.Coherence.MatchingPermutation
import LogdetLean.Coherence.NestedPrefixCoordinates
import LogdetLean.Coherence.ConditionalProbabilityReal
/-!
# Matching transport and exact factorization for bounded score windows

This file is the bounded-window analogue of `MatchingPermutation` and
`CanonicalMatchingFactorization`.  It transports every ordered matching to
the consecutive-pair matching by a column permutation and then factors the
canonical joint probability into the exact `k`-fold Beta window mass and a
window-conditioned log-determinant CDF.

Everything here is finite-sample and model-specific.  No limiting statement
is made in this module.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

/-- The normalized coherence location written on a centered finite family. -/
def centeredFamilyCoherencePointScore (m p : ℕ)
    (v : Fin p → centeredSubspace (m + 1)) (i j : Fin p) : ℝ :=
  (m : ℝ) * (normalizedGram v i j) ^ 2 -
    4 * Real.log (p : ℝ) + Real.log (Real.log (p : ℝ))

/-- Joint log-determinant/window event for an arbitrary ordered edge tuple,
written on the centered finite-family Gaussian model. -/
def familyOrderedTupleWindowJointEvent
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    Set (Fin p → centeredSubspace (m + 1)) :=
  {v | centeredFamilyZ0mpStatistic m p v ≤ z ∧
    ∀ i : Fin k,
      centeredFamilyCoherencePointScore m p v
        (orderedEdgeEndpointMap edges (i, false))
        (orderedEdgeEndpointMap edges (i, true)) ∈ Ioc a b}

/-- The corresponding event for the consecutive-pair canonical matching. -/
def canonicalMatchingFamilyWindowJointEvent
    (m p k : ℕ) (hkp : 2 * k ≤ p) (z a b : ℝ) :
    Set (Fin p → centeredSubspace (m + 1)) :=
  {v | centeredFamilyZ0mpStatistic m p v ≤ z ∧
    ∀ i : Fin k,
      centeredFamilyCoherencePointScore m p v
        (canonicalEndpointEmbedding hkp (i, false))
        (canonicalEndpointEmbedding hkp (i, true)) ∈ Ioc a b}

/-- A fixed finite-family normalized coherence location is measurable. -/
theorem measurable_centeredFamilyCoherencePointScore
    (m p : ℕ) (i j : Fin p) :
    Measurable (fun v : Fin p → centeredSubspace (m + 1) ↦
      centeredFamilyCoherencePointScore m p v i j) := by
  unfold centeredFamilyCoherencePointScore
  have hentry : Measurable
      (fun v : Fin p → centeredSubspace (m + 1) ↦
        normalizedGram v i j) := by
    exact (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_normalizedGramFamily)
  exact ((measurable_const.mul (hentry.pow_const 2)).sub
    measurable_const).add measurable_const

/-- Interval membership for the normalized family score is exactly interval
membership for the squared normalized-Gram entry after dividing both
classical thresholds by `m`. -/
theorem centeredFamilyCoherencePointScore_mem_Ioc_iff
    (m p : ℕ) (hm0 : 0 < m)
    (v : Fin p → centeredSubspace (m + 1)) (i j : Fin p)
    (a b : ℝ) :
    centeredFamilyCoherencePointScore m p v i j ∈ Ioc a b ↔
      (normalizedGram v i j) ^ 2 ∈
        Ioc (canonicalMatchingWindowEndpoint m p a)
          (canonicalMatchingWindowEndpoint m p b) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · apply (div_lt_iff₀ hmR).2
      unfold centeredFamilyCoherencePointScore at ha
      unfold classicalCoherenceThreshold
      linarith
    · apply (le_div_iff₀ hmR).2
      unfold centeredFamilyCoherencePointScore at hb
      unfold classicalCoherenceThreshold
      linarith
  · rintro ⟨ha, hb⟩
    constructor
    · have ha' := (div_lt_iff₀ hmR).1 ha
      unfold centeredFamilyCoherencePointScore
      unfold classicalCoherenceThreshold at ha'
      linarith
    · have hb' := (le_div_iff₀ hmR).1 hb
      unfold centeredFamilyCoherencePointScore
      unfold classicalCoherenceThreshold at hb'
      linarith

/-- The arbitrary ordered-tuple finite-family window event is measurable. -/
theorem measurableSet_familyOrderedTupleWindowJointEvent
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    MeasurableSet
      (familyOrderedTupleWindowJointEvent m p k z a b edges) := by
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
            (orderedEdgeEndpointMap edges (i, true)) ∈ Ioc a b} := by
    rw [show {v : Fin p → centeredSubspace (m + 1) |
          ∀ i : Fin k,
            centeredFamilyCoherencePointScore m p v
              (orderedEdgeEndpointMap edges (i, false))
              (orderedEdgeEndpointMap edges (i, true)) ∈ Ioc a b} =
        ⋂ i : Fin k,
          centeredFamilyCoherencePointScore m p
            (i := orderedEdgeEndpointMap edges (i, false))
            (j := orderedEdgeEndpointMap edges (i, true)) ⁻¹' Ioc a b by
      ext v
      simp]
    exact MeasurableSet.iInter fun i ↦ measurableSet_Ioc.preimage
      (measurable_centeredFamilyCoherencePointScore m p
        (orderedEdgeEndpointMap edges (i, false))
        (orderedEdgeEndpointMap edges (i, true)))
  exact hbulk.inter hedge

/-- The canonical finite-family window event is measurable. -/
theorem measurableSet_canonicalMatchingFamilyWindowJointEvent
    (m p k : ℕ) (hkp : 2 * k ≤ p) (z a b : ℝ) :
    MeasurableSet
      (canonicalMatchingFamilyWindowJointEvent m p k hkp z a b) := by
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
            (canonicalEndpointEmbedding hkp (i, true)) ∈ Ioc a b} := by
    rw [show {v : Fin p → centeredSubspace (m + 1) |
          ∀ i : Fin k,
            centeredFamilyCoherencePointScore m p v
              (canonicalEndpointEmbedding hkp (i, false))
              (canonicalEndpointEmbedding hkp (i, true)) ∈ Ioc a b} =
        ⋂ i : Fin k,
          centeredFamilyCoherencePointScore m p
            (i := canonicalEndpointEmbedding hkp (i, false))
            (j := canonicalEndpointEmbedding hkp (i, true)) ⁻¹' Ioc a b by
      ext v
      simp]
    exact MeasurableSet.iInter fun i ↦ measurableSet_Ioc.preimage
      (measurable_centeredFamilyCoherencePointScore m p
        (canonicalEndpointEmbedding hkp (i, false))
        (canonicalEndpointEmbedding hkp (i, true)))
  exact hbulk.inter hedge

/-- Centering the raw Gaussian sample identifies the raw and finite-family
window events exactly. -/
theorem preimage_familyOrderedTupleWindowJointEvent_centeredNested
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      nestedTupleToFin p (centerNested (m + 1) p data)) ⁻¹'
        familyOrderedTupleWindowJointEvent m p k z a b edges =
      orderedTupleWindowJointEvent m p k z a b edges := by
  ext data
  change
    (centeredFamilyZ0mpStatistic m p
          (nestedTupleToFin p (centerNested (m + 1) p data)) ≤ z ∧
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m p
            (nestedTupleToFin p (centerNested (m + 1) p data))
            (orderedEdgeEndpointMap edges (i, false))
            (orderedEdgeEndpointMap edges (i, true)) ∈ Ioc a b) ↔
      (Z0mpStatistic m p data ≤ z ∧
        ∀ i : Fin k, coherencePointScore m p data (edges i) ∈ Ioc a b)
  rw [centeredFamilyZ0mpStatistic_centeredNested]
  simp [centeredFamilyCoherencePointScore, coherencePointScore,
    scaledSquaredCorrelationScore, centeredCorrelationMatrix,
    orderedEdgeEndpointMap, correlationEdgeEndpoint]

/-- Normalized finite-family coherence locations are transported exactly by
the same column permutation used for the matching endpoints. -/
theorem centeredFamilyCoherencePointScore_permuteColumns_apply_image
    (m p : ℕ) (σ : Equiv.Perm (Fin p))
    (v : Fin p → centeredSubspace (m + 1)) (i j : Fin p) :
    centeredFamilyCoherencePointScore m p (permuteColumns σ v) (σ i) (σ j) =
      centeredFamilyCoherencePointScore m p v i j := by
  unfold centeredFamilyCoherencePointScore
  rw [normalizedGram_permuteColumns_apply_image]

/-- A matching-to-canonical permutation pulls the canonical bounded-window
event back to the event for the original ordered matching. -/
theorem preimage_canonicalMatchingFamilyWindowJointEvent_permuteColumns
    (m p k : ℕ) (z a b : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) (hmatching : edges.IsMatching)
    (σ : Equiv.Perm (Fin p))
    (hσ : ∀ ib : Fin k × Bool,
      σ (orderedEdgeEndpointMap edges ib) =
        canonicalEndpointEmbedding (two_mul_le_of_isMatching hmatching) ib) :
    permuteColumns (E := centeredSubspace (m + 1)) σ ⁻¹'
        canonicalMatchingFamilyWindowJointEvent m p k
          (two_mul_le_of_isMatching hmatching) z a b =
      familyOrderedTupleWindowJointEvent m p k z a b edges := by
  ext v
  change
    (centeredFamilyZ0mpStatistic m p (permuteColumns σ v) ≤ z ∧
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m p (permuteColumns σ v)
            (canonicalEndpointEmbedding
              (two_mul_le_of_isMatching hmatching) (i, false))
            (canonicalEndpointEmbedding
              (two_mul_le_of_isMatching hmatching) (i, true)) ∈ Ioc a b) ↔
      (centeredFamilyZ0mpStatistic m p v ≤ z ∧
        ∀ i : Fin k,
          centeredFamilyCoherencePointScore m p v
            (orderedEdgeEndpointMap edges (i, false))
            (orderedEdgeEndpointMap edges (i, true)) ∈ Ioc a b)
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

/-- The raw nested Gaussian probability equals the corresponding centered
finite-family probability for a bounded window. -/
theorem orderedTupleWindowJointEvent_probability_eq_family
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleWindowJointEvent m p k z a b edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (familyOrderedTupleWindowJointEvent m p k z a b edges) := by
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
  have hset := measurableSet_familyOrderedTupleWindowJointEvent
    m p k z a b edges
  calc
    mu.real (orderedTupleWindowJointEvent m p k z a b edges) =
        mu.real (F ⁻¹'
          familyOrderedTupleWindowJointEvent m p k z a b edges) := by
      rw [preimage_familyOrderedTupleWindowJointEvent_centeredNested]
    _ = (Measure.map F mu).real
          (familyOrderedTupleWindowJointEvent m p k z a b edges) := by
      change
        (mu (F ⁻¹' familyOrderedTupleWindowJointEvent m p k z a b edges)).toReal =
          ((Measure.map F mu)
            (familyOrderedTupleWindowJointEvent m p k z a b edges)).toReal
      rw [Measure.map_apply hF hset]
    _ = nu.real
          (familyOrderedTupleWindowJointEvent m p k z a b edges) := by
      rw [hmap]

/-- Exact finite exchangeability for bounded score windows: every ordered
matching has the same joint probability as the canonical matching. -/
theorem orderedMatchingWindowJointEvent_probability_eq_canonical
    (m p k : ℕ) (z a b : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) (hmatching : edges.IsMatching) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleWindowJointEvent m p k z a b edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyWindowJointEvent m p k
          (two_mul_le_of_isMatching hmatching) z a b) := by
  rw [orderedTupleWindowJointEvent_probability_eq_family]
  rcases exists_matchingToCanonicalPermutation edges hmatching with
    ⟨σ, hσ⟩
  let mu := Measure.pi fun _ : Fin p ↦
    stdGaussian (centeredSubspace (m + 1))
  let A := canonicalMatchingFamilyWindowJointEvent m p k
    (two_mul_le_of_isMatching hmatching) z a b
  have hperm :=
    (measurePreserving_permuteGaussianColumns
      (E := centeredSubspace (m + 1)) σ).map_eq
  have hA : MeasurableSet A :=
    measurableSet_canonicalMatchingFamilyWindowJointEvent m p k
      (two_mul_le_of_isMatching hmatching) z a b
  calc
    mu.real (familyOrderedTupleWindowJointEvent m p k z a b edges) =
        mu.real (permuteColumns σ ⁻¹' A) := by
      rw [preimage_canonicalMatchingFamilyWindowJointEvent_permuteColumns
        m p k z a b edges hmatching σ hσ]
    _ = (Measure.map (permuteColumns σ) mu).real A := by
      change (mu (permuteColumns σ ⁻¹' A)).toReal =
        ((Measure.map (permuteColumns σ) mu) A).toReal
      rw [Measure.map_apply (measurable_permuteColumns σ) hA]
    _ = mu.real A := by rw [hperm]

/-- Membership in the matching finset supplies the bounded-window canonical
transport identity in the form used by factorial-moment summation. -/
theorem orderedMatchingWindowJointEvent_probability_eq_canonical_of_mem
    (m p k : ℕ) (z a b : ℝ)
    (edges : OrderedDistinctEdgeTuple p k)
    (hedges : edges ∈ orderedMatchingTuples p k) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleWindowJointEvent m p k z a b edges) =
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyWindowJointEvent m p k
          (two_mul_le_of_isMatching
            (isMatching_of_mem_orderedMatchingTuples hedges)) z a b) := by
  exact orderedMatchingWindowJointEvent_probability_eq_canonical
    m p k z a b edges (isMatching_of_mem_orderedMatchingTuples hedges)

/-! ## Canonical window event on the fixed prefix -/

/-- Direct finite-family presentation of the canonical window event on its
`2*k`-column prefix. -/
def canonicalFamilyMatchingWindowEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k m p : ℕ) (a b : ℝ) : Set (Fin (2 * k) → E) :=
  {v | ∀ j : Fin k,
    squaredNormalizedInner
      (v (canonicalEvenIndex k j)) (v (canonicalOddIndex k j)) ∈
        Ioc (canonicalMatchingWindowEndpoint m p a)
          (canonicalMatchingWindowEndpoint m p b)}

/-- The direct canonical-prefix bounded-window event is measurable. -/
theorem measurableSet_canonicalFamilyMatchingWindowEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k m p : ℕ) (a b : ℝ) :
    MeasurableSet (canonicalFamilyMatchingWindowEvent (E := E) k m p a b) := by
  rw [show canonicalFamilyMatchingWindowEvent (E := E) k m p a b =
      ⋂ j : Fin k,
        {v | squaredNormalizedInner
          (v (canonicalEvenIndex k j)) (v (canonicalOddIndex k j)) ∈
            Ioc (canonicalMatchingWindowEndpoint m p a)
              (canonicalMatchingWindowEndpoint m p b)} by
    ext v
    simp [canonicalFamilyMatchingWindowEvent]]
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
  exact measurableSet_Ioc.preimage hscore

/-- The recursive ordered-forest window event is exactly its direct
finite-family formulation. -/
theorem preimage_canonicalFamilyMatchingWindowEvent_nestedTupleToFin
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k m p : ℕ) (a b : ℝ) :
    nestedTupleToFin (α := E) (2 * k) ⁻¹'
        canonicalFamilyMatchingWindowEvent (E := E) k m p a b =
      canonicalGaussianMatchingWindowEvent (E := E) m p k a b := by
  ext z
  induction k with
  | zero =>
      simp [canonicalFamilyMatchingWindowEvent,
        canonicalGaussianMatchingWindowEvent,
        canonicalMatchingScoreWindowEvent, orderedForestScores,
        sequentialStatistic]
  | succ k ih =>
      rcases z with ⟨⟨past, u⟩, v⟩
      unfold canonicalFamilyMatchingWindowEvent
        canonicalGaussianMatchingWindowEvent
      simp only [Set.mem_preimage]
      rw [orderedForestScores_canonicalMatching_pair_succ]
      change
        (∀ j : Fin (k + 1),
          squaredNormalizedInner
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalEvenIndex (k + 1) j))
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalOddIndex (k + 1) j)) ∈
            Ioc (canonicalMatchingWindowEndpoint m p a)
              (canonicalMatchingWindowEndpoint m p b)) ↔
          ((orderedForestScores (E := E) canonicalMatchingForest
                (2 * k) past ∈
              canonicalMatchingScoreWindowEvent m p a b k ∧
              (0 : ℝ) ∈ Set.univ) ∧
            squaredNormalizedInner u v ∈
              Ioc (canonicalMatchingWindowEndpoint m p a)
                (canonicalMatchingWindowEndpoint m p b))
      simp only [Set.mem_univ, and_true]
      change
        (∀ j : Fin (k + 1),
          squaredNormalizedInner
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalEvenIndex (k + 1) j))
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalOddIndex (k + 1) j)) ∈
            Ioc (canonicalMatchingWindowEndpoint m p a)
              (canonicalMatchingWindowEndpoint m p b)) ↔
          (past ∈ canonicalGaussianMatchingWindowEvent
              (E := E) m p k a b ∧
            squaredNormalizedInner u v ∈
              Ioc (canonicalMatchingWindowEndpoint m p a)
                (canonicalMatchingWindowEndpoint m p b))
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

/-- Pointwise identification of the canonical finite-family bounded-window
joint event with the raw full-statistic lower tail intersected with the
lifted canonical prefix-window event. -/
theorem preimage_canonicalMatchingFamilyWindowJointEvent_centeredNested
    (m k r : ℕ) (hm0 : 0 < m) (z a b : ℝ) :
    let p := 2 * k + r
    let hkp : 2 * k ≤ p := Nat.le_add_right _ _
    let s : Set (NestedTuple (centeredSubspace (m + 1)) (2 * k)) :=
      canonicalCenteredMatchingWindowPrefixEvent k m p a b
    (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      nestedTupleToFin p (centerNested (m + 1) p data)) ⁻¹'
        canonicalMatchingFamilyWindowJointEvent m p k hkp z a b =
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
              (i, true)) ∈ Ioc a b) ↔
      (Z0mpStatistic m (2 * k + r) data ≤ z ∧
        data ∈ centeredGaussianPrefixEvent m (2 * k) r
          (canonicalCenteredMatchingWindowPrefixEvent
            k m (2 * k + r) a b))
  rw [centeredFamilyZ0mpStatistic_centeredNested]
  rw [mem_centeredGaussianPrefixEvent_iff]
  apply and_congr Iff.rfl
  unfold canonicalCenteredMatchingWindowPrefixEvent
  rw [← Set.ext_iff.mp
    (preimage_canonicalFamilyMatchingWindowEvent_nestedTupleToFin
      (E := centeredSubspace (m + 1)) k m (2 * k + r) a b) _]
  unfold canonicalFamilyMatchingWindowEvent
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
      (centeredFamilyCoherencePointScore_mem_Ioc_iff
        m (2 * k + r) hm0 full
        (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
          (i, false))
        (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
          (i, true)) a b).1 (hedge i)
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
    apply (centeredFamilyCoherencePointScore_mem_Ioc_iff
      m (2 * k + r) hm0 full
      (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
        (i, false))
      (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
        (i, true)) a b).2
    rw [hscore]
    exact hedge i

/-! ## Exact finite factorization -/

/-- **Exact canonical bounded-window factorization in prefix-plus-tail
coordinates.**  The canonical joint event has probability equal to the
`k`-fold one-edge Beta window mass times the canonical window-conditioned
log-determinant CDF. -/
theorem canonicalMatchingFamilyWindowJointEvent_probability_factorization_add
    (m k r : ℕ) (hm : 2 ≤ m) (hpm : 2 * k + r ≤ m)
    (z : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingWindowPrefixEvent
        k m (2 * k + r) a b) ≠ 0) :
    (Measure.pi fun _ : Fin (2 * k + r) ↦
      stdGaussian (centeredSubspace (m + 1))).real
      (canonicalMatchingFamilyWindowJointEvent
        m (2 * k + r) k (Nat.le_add_right _ _) z a b) =
      betaCorrelationWindowProbability m (2 * k + r) a b ^ k *
        canonicalWindowConditionedZ0mpCDFOrGaussian
          k m (2 * k + r) a b z := by
  let q := 2 * k
  let p := q + r
  let s : Set (NestedTuple (centeredSubspace (m + 1)) q) :=
    canonicalCenteredMatchingWindowPrefixEvent k m p a b
  let hs : MeasurableSet s :=
    measurableSet_canonicalCenteredMatchingWindowPrefixEvent k m p a b
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
      F ⁻¹' canonicalMatchingFamilyWindowJointEvent
        m p k (Nat.le_add_right _ _) z a b = B ∩ A := by
    simpa [q, p, s, A, B, F] using
      preimage_canonicalMatchingFamilyWindowJointEvent_centeredNested
        m k r (by omega) z a b
  have hset := measurableSet_canonicalMatchingFamilyWindowJointEvent
    m p k (Nat.le_add_right _ _) z a b
  have hfamily :
      nu.real (canonicalMatchingFamilyWindowJointEvent
        m p k (Nat.le_add_right _ _) z a b) = mu.real (B ∩ A) := by
    calc
      nu.real (canonicalMatchingFamilyWindowJointEvent
          m p k (Nat.le_add_right _ _) z a b) =
          (Measure.map F mu).real
            (canonicalMatchingFamilyWindowJointEvent
              m p k (Nat.le_add_right _ _) z a b) := by rw [hmap]
      _ = mu.real (F ⁻¹'
            canonicalMatchingFamilyWindowJointEvent
              m p k (Nat.le_add_right _ _) z a b) := by
        change ((Measure.map F mu)
            (canonicalMatchingFamilyWindowJointEvent
              m p k (Nat.le_add_right _ _) z a b)).toReal =
          (mu (F ⁻¹' canonicalMatchingFamilyWindowJointEvent
            m p k (Nat.le_add_right _ _) z a b)).toReal
        rw [Measure.map_apply hF hset]
      _ = mu.real (B ∩ A) := by rw [hcanonical]
  have hmul := measureReal_inter_eq_cond_mul_measureReal mu A B hA
  have hmass :
      mu.real A = betaCorrelationWindowProbability m p a b ^ k := by
    have hpref := centeredGaussianPrefixEvent_probability
      m q r hqr s hs
    have hprefReal := congrArg ENNReal.toReal hpref
    calc
      mu.real A =
          (nestedProductMeasure
            (stdGaussian (centeredSubspace (m + 1))) q).real s := by
        simpa [Measure.real, mu, A, p] using hprefReal
      _ = betaCorrelationWindowProbability m p a b ^ k := by
        simpa [q, s] using
          canonicalCenteredMatchingWindowPrefixEvent_probability
            m p hm k hab
  have hbulk :
      (mu[|A]).real B =
        canonicalWindowConditionedZ0mpCDFOrGaussian k m p a b z := by
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
        canonicalWindowConditionedZ0mpCDFOrGaussian k m p a b z =
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
        (canonicalMatchingFamilyWindowJointEvent
          m (2 * k + r) k (Nat.le_add_right _ _) z a b) =
      nu.real (canonicalMatchingFamilyWindowJointEvent
        m p k (Nat.le_add_right _ _) z a b) := by rfl
    _ = mu.real (B ∩ A) := hfamily
    _ = (mu[|A]).real B * mu.real A := hmul
    _ = betaCorrelationWindowProbability m p a b ^ k *
          canonicalWindowConditionedZ0mpCDFOrGaussian k m p a b z := by
      rw [hmass, hbulk]
      ring
    _ = betaCorrelationWindowProbability m (2 * k + r) a b ^ k *
          canonicalWindowConditionedZ0mpCDFOrGaussian
            k m (2 * k + r) a b z := by
      rfl

/-- Exact canonical bounded-window factorization at arbitrary valid `p`. -/
theorem canonicalMatchingFamilyWindowJointEvent_probability_factorization
    (m p k : ℕ) (hm : 2 ≤ m) (hqp : 2 * k ≤ p) (hpm : p ≤ m)
    (z : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingWindowPrefixEvent k m p a b) ≠ 0) :
    (Measure.pi fun _ : Fin p ↦
      stdGaussian (centeredSubspace (m + 1))).real
      (canonicalMatchingFamilyWindowJointEvent m p k hqp z a b) =
      betaCorrelationWindowProbability m p a b ^ k *
        canonicalWindowConditionedZ0mpCDFOrGaussian k m p a b z := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hqp
  exact canonicalMatchingFamilyWindowJointEvent_probability_factorization_add
    m k r hm hpm z hab hs0

/-- Every ordered matching summand has the same exact Beta-window times
window-conditioned-bulk factorization. -/
theorem orderedMatchingWindowJointEvent_probability_factorization_of_mem
    (m p k : ℕ) (hm : 2 ≤ m) (hpm : p ≤ m)
    (z : ℝ) {a b : ℝ} (hab : a ≤ b)
    (edges : OrderedDistinctEdgeTuple p k)
    (hedges : edges ∈ orderedMatchingTuples p k)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingWindowPrefixEvent k m p a b) ≠ 0) :
    (nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) p).real
      (orderedTupleWindowJointEvent m p k z a b edges) =
      betaCorrelationWindowProbability m p a b ^ k *
        canonicalWindowConditionedZ0mpCDFOrGaussian k m p a b z := by
  have hmatching := isMatching_of_mem_orderedMatchingTuples hedges
  have hqp := two_mul_le_of_isMatching hmatching
  calc
    _ = (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyWindowJointEvent m p k hqp z a b) :=
      orderedMatchingWindowJointEvent_probability_eq_canonical_of_mem
        m p k z a b edges hedges
    _ = _ :=
      canonicalMatchingFamilyWindowJointEvent_probability_factorization
        m p k hm hqp hpm z hab hs0


end

end LogdetLean.Coherence
