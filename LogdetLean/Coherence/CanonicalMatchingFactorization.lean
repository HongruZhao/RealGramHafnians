import LogdetLean.Coherence.MatchingPermutation
import LogdetLean.Coherence.NestedPrefixCoordinates
import LogdetLean.Coherence.CanonicalConditionalCLT
import LogdetLean.Coherence.ConditionalProbabilityReal
/-!
# Exact factorization of a canonical matching summand

This file connects the canonical finite-family event produced by column
permutation to the prefix-conditioned raw Gaussian law.  At every valid
finite index its probability is exactly

`(one-edge beta tail)^k * (conditional Z0mp lower-tail probability)`.

The conditional factor is the totalized factor from
`CanonicalConditionalCLT`, so its all-gap Gaussian limit is already proved.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology ProbabilityTheory ENNReal

/-- Normalized-Gram entry squares equal the quotient-form squared normalized
inner product, including when one of the two vectors is zero. -/
theorem canonical_normalizedGram_apply_sq_eq_squaredNormalizedInner_total
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (i j : ι) :
    (normalizedGram v i j) ^ 2 =
      squaredNormalizedInner (v i) (v j) := by
  by_cases hi : v i = 0
  · simp [hi, normalizedGram, normalizeVector, squaredNormalizedInner,
      Matrix.gram]
  by_cases hj : v j = 0
  · simp [hj, normalizedGram, normalizeVector, squaredNormalizedInner,
      Matrix.gram]
  exact normalizedGram_apply_sq_eq_squaredNormalizedInner v i j hi hj

/-- In an ambient family with `r` additional columns, the even endpoint of
the canonical matching is the ordinary `Fin.castAdd` of its prefix index. -/
theorem canonicalEndpointEmbedding_false_eq_castAdd
    (k r : ℕ) (i : Fin k) :
    canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r) (i, false) =
      Fin.castAdd r (canonicalEvenIndex k i) := by
  apply Fin.ext
  simp

/-- The analogous coordinate identity for the odd endpoint. -/
theorem canonicalEndpointEmbedding_true_eq_castAdd
    (k r : ℕ) (i : Fin k) :
    canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r) (i, true) =
      Fin.castAdd r (canonicalOddIndex k i) := by
  apply Fin.ext
  simp

/-- Valid-index fallback elimination with an explicit tail length known to
equal `p-q`.  Keeping that equality as a hypothesis makes dependent
transport across the nested tuple dimension explicit. -/
theorem conditionedPrefixTailJointOrGaussian_eq_of_sub_eq
    (m q p r : ℕ)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s) (hqp : q ≤ p) (hpm : p ≤ m)
    (hqr : q + r ≤ m) (hsub : p - q = r)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    conditionedPrefixTailJointOrGaussian m q p s hs =
      (conditionedCenteredGaussianPrefixProbabilityMeasure
        m q r hqr s hs hs0).map
          (measurable_centeredGaussianPrefixTailPairStatistic
            m q r).aemeasurable := by
  subst r
  exact conditionedPrefixTailJointOrGaussian_eq_of_valid
    m q p s hs hqp hpm hs0

/-- Additive-dimension form of the valid-index fallback elimination. -/
theorem conditionedPrefixTailJointOrGaussian_eq_of_add
    (m q r : ℕ)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s) (hqr : q + r ≤ m)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    conditionedPrefixTailJointOrGaussian m q (q + r) s hs =
      (conditionedCenteredGaussianPrefixProbabilityMeasure
        m q r hqr s hs hs0).map
          (measurable_centeredGaussianPrefixTailPairStatistic
            m q r).aemeasurable :=
  conditionedPrefixTailJointOrGaussian_eq_of_sub_eq
    m q (q + r) r s hs (Nat.le_add_right q r) hqr hqr
      (Nat.add_sub_cancel_left q r) hs0

/-- Pointwise identification of the canonical finite-family event with the
raw full-statistic lower-tail event intersected with the lifted matching
prefix event. -/
theorem preimage_canonicalMatchingFamilyJointEvent_centeredNested
    (m k r : ℕ) (hm0 : 0 < m) (z x : ℝ) :
    let p := 2 * k + r
    let hkp : 2 * k ≤ p := Nat.le_add_right _ _
    let s : Set (NestedTuple (centeredSubspace (m + 1)) (2 * k)) :=
      canonicalGaussianMatchingEvent k
        (classicalCoherenceThreshold m p x / (m : ℝ))
    (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      nestedTupleToFin p (centerNested (m + 1) p data)) ⁻¹'
        canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
          m p k hkp z x =
      {data | Z0mpStatistic m p data ≤ z} ∩
        centeredGaussianPrefixEvent m (2 * k) r s := by
  dsimp only
  ext data
  change
    (centeredFamilyZ0mpStatistic m (2 * k + r)
          (nestedTupleToFin (2 * k + r)
            (centerNested (m + 1) (2 * k + r) data)) ≤ z ∧
        ∀ i : Fin k, classicalCoherenceThreshold m (2 * k + r) x <
          (m : ℝ) *
            (normalizedGram
              (nestedTupleToFin (2 * k + r)
                (centerNested (m + 1) (2 * k + r) data))
              (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
                (i, false))
              (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
                (i, true))) ^ 2) ↔
      (Z0mpStatistic m (2 * k + r) data ≤ z ∧
        data ∈ centeredGaussianPrefixEvent m (2 * k) r
          (canonicalGaussianMatchingEvent k
            (classicalCoherenceThreshold m (2 * k + r) x / (m : ℝ))))
  rw [centeredFamilyZ0mpStatistic_centeredNested]
  rw [mem_centeredGaussianPrefixEvent_iff]
  apply and_congr Iff.rfl
  rw [← Set.ext_iff.mp
    (preimage_canonicalFamilyMatchingEvent_nestedTupleToFin
      (E := centeredSubspace (m + 1)) k
      (classicalCoherenceThreshold m (2 * k + r) x / (m : ℝ))) _]
  unfold canonicalFamilyMatchingEvent
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
    have hi := hedge i
    rw [show
      (normalizedGram
        (nestedTupleToFin (2 * k + r)
          (centerNested (m + 1) (2 * k + r) data))
        (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
          (i, false))
        (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
          (i, true))) ^ 2 =
        squaredNormalizedInner
          (nestedTupleToFin (2 * k)
            (nestedTuplePrefix (2 * k) r
              (centerNested (m + 1) (2 * k + r) data))
            (canonicalEvenIndex k i))
          (nestedTupleToFin (2 * k)
            (nestedTuplePrefix (2 * k) r
              (centerNested (m + 1) (2 * k + r) data))
            (canonicalOddIndex k i)) by exact hscore] at hi
    exact (div_lt_iff₀ (by positivity : (0 : ℝ) < m)).2
      (by simpa only [mul_comm] using hi)
  · intro hedge i
    have hi := hedge i
    have hscore :
        (normalizedGram
          (nestedTupleToFin (2 * k + r)
            (centerNested (m + 1) (2 * k + r) data))
          (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
            (i, false))
          (canonicalEndpointEmbedding (Nat.le_add_right (2 * k) r)
            (i, true))) ^ 2 =
          squaredNormalizedInner
            (nestedTupleToFin (2 * k)
              (nestedTuplePrefix (2 * k) r
                (centerNested (m + 1) (2 * k + r) data))
              (canonicalEvenIndex k i))
            (nestedTupleToFin (2 * k)
              (nestedTuplePrefix (2 * k) r
                (centerNested (m + 1) (2 * k + r) data))
              (canonicalOddIndex k i)) := by
      rw [canonicalEndpointEmbedding_false_eq_castAdd,
        canonicalEndpointEmbedding_true_eq_castAdd,
        canonical_normalizedGram_apply_sq_eq_squaredNormalizedInner_total,
        nestedTupleToFin_castAdd_eq_prefix,
        nestedTupleToFin_castAdd_eq_prefix]
    rw [hscore]
    simpa only [mul_comm] using
      (div_lt_iff₀ (by positivity : (0 : ℝ) < m)).1 hi

/-- **Exact canonical factorization in prefix-plus-tail coordinates.**  The
canonical matching joint event has probability equal to the `k`-fold
one-edge beta tail times the canonical conditional bulk factor. -/
theorem canonicalMatchingFamilyJointEvent_probability_factorization_add
    (m k r : ℕ) (hm : 2 ≤ m) (hpm : 2 * k + r ≤ m)
    (z x : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingPrefixEvent k m (2 * k + r) x) ≠ 0) :
    (Measure.pi fun _ : Fin (2 * k + r) ↦
      stdGaussian (centeredSubspace (m + 1))).real
      (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
        m (2 * k + r) k (Nat.le_add_right _ _) z x) =
      betaCorrelationTailProbability m (2 * k + r) x ^ k *
        canonicalConditionedZ0mpCDFOrGaussian k m (2 * k + r) x z := by
  let q := 2 * k
  let p := q + r
  let s : Set (NestedTuple (centeredSubspace (m + 1)) q) :=
    canonicalCenteredMatchingPrefixEvent k m p x
  let hs : MeasurableSet s :=
    measurableSet_canonicalCenteredMatchingPrefixEvent k m p x
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
      F ⁻¹' canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
        m p k (Nat.le_add_right _ _) z x = B ∩ A := by
    simpa [q, p, s, A, B, F, canonicalCenteredMatchingPrefixEvent] using
      preimage_canonicalMatchingFamilyJointEvent_centeredNested
        m k r (by omega) z x
  have hset := measurableSet_canonicalMatchingFamilyJointEvent
    classicalCoherenceThreshold m p k (Nat.le_add_right _ _) z x
  have hfamily :
      nu.real (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
        m p k (Nat.le_add_right _ _) z x) = mu.real (B ∩ A) := by
    calc
      nu.real (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
          m p k (Nat.le_add_right _ _) z x) =
          (Measure.map F mu).real
            (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
              m p k (Nat.le_add_right _ _) z x) := by rw [hmap]
      _ = mu.real (F ⁻¹'
            canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
              m p k (Nat.le_add_right _ _) z x) := by
        change ((Measure.map F mu)
            (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
              m p k (Nat.le_add_right _ _) z x)).toReal =
          (mu (F ⁻¹'
            canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
              m p k (Nat.le_add_right _ _) z x)).toReal
        rw [Measure.map_apply hF hset]
      _ = mu.real (B ∩ A) := by rw [hcanonical]
  have hmul := measureReal_inter_eq_cond_mul_measureReal mu A B hA
  have hmass :
      mu.real A = betaCorrelationTailProbability m p x ^ k := by
    have hpref := centeredGaussianPrefixEvent_probability
      m q r hqr s hs
    have hprefReal := congrArg ENNReal.toReal hpref
    calc
      mu.real A =
          (nestedProductMeasure
            (stdGaussian (centeredSubspace (m + 1))) q).real s := by
        simpa [Measure.real, mu, A, p] using hprefReal
      _ = ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
          (Ioi (classicalCoherenceThreshold m p x / (m : ℝ)))) ^ k := by
        simpa [q, s, canonicalCenteredMatchingPrefixEvent] using
          canonicalCenteredGaussianMatchingEvent_probability m hm k
            (classicalCoherenceThreshold m p x / (m : ℝ))
      _ = betaCorrelationTailProbability m p x ^ k := by rfl
  have hbulk :
      (mu[|A]).real B =
        canonicalConditionedZ0mpCDFOrGaussian k m p x z := by
    have hjoint := conditionedPrefixTailJointOrGaussian_eq_of_add
      m q r s hs hqr
      (by simpa [q, p, s, canonicalCenteredMatchingPrefixEvent] using hs0)
    have hmapadd := map_add_centeredGaussianPrefixTailPair_cond_eq_map_Z0mp
      m q r hqr s hs
      (by simpa [q, p, s, canonicalCenteredMatchingPrefixEvent] using hs0)
    have hjointMeasure :
        (conditionedPrefixTailJointOrGaussian m q (q + r) s hs :
            Measure (ℝ × ℝ)) =
          Measure.map (centeredGaussianPrefixTailPairStatistic m q r)
            ((conditionedCenteredGaussianPrefixProbabilityMeasure
              m q r hqr s hs _ : ProbabilityMeasure _) : Measure _) :=
      congrArg (fun eta : ProbabilityMeasure (ℝ × ℝ) ↦
        (eta : Measure (ℝ × ℝ))) hjoint
    have hz' :
        canonicalConditionedZ0mpCDFOrGaussian k m p x z =
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
        (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
          m (2 * k + r) k (Nat.le_add_right _ _) z x) =
      nu.real (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
        m p k (Nat.le_add_right _ _) z x) := by rfl
    _ = mu.real (B ∩ A) := hfamily
    _ = (mu[|A]).real B * mu.real A := hmul
    _ = betaCorrelationTailProbability m p x ^ k *
          canonicalConditionedZ0mpCDFOrGaussian k m p x z := by
      rw [hmass, hbulk]
      ring
    _ = betaCorrelationTailProbability m (2 * k + r) x ^ k *
          canonicalConditionedZ0mpCDFOrGaussian k m (2 * k + r) x z := by
      rfl

/-- Exact canonical factorization at arbitrary valid `p`, obtained by taking
the retained tail length to be `p - 2*k`. -/
theorem canonicalMatchingFamilyJointEvent_probability_factorization
    (m p k : ℕ) (hm : 2 ≤ m) (hqp : 2 * k ≤ p) (hpm : p ≤ m)
    (z x : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingPrefixEvent k m p x) ≠ 0) :
    (Measure.pi fun _ : Fin p ↦
      stdGaussian (centeredSubspace (m + 1))).real
      (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
        m p k hqp z x) =
      betaCorrelationTailProbability m p x ^ k *
        canonicalConditionedZ0mpCDFOrGaussian k m p x z := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hqp
  exact canonicalMatchingFamilyJointEvent_probability_factorization_add
    m k r hm hpm z x hs0

/-- Every ordered matching summand has the same exact beta-tail times
conditional-bulk factorization.  This is the pointwise hypothesis required
by `MixedMomentAssembly`. -/
theorem orderedMatchingJointEvent_probability_factorization_of_mem
    (m p k : ℕ) (hm : 2 ≤ m) (hpm : p ≤ m)
    (z x : ℝ) (edges : OrderedDistinctEdgeTuple p k)
    (hedges : edges ∈ orderedMatchingTuples p k)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingPrefixEvent k m p x) ≠ 0) :
    (nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) p).real
      (orderedTupleJointEvent classicalCoherenceThreshold
        m p k z x edges) =
      betaCorrelationTailProbability m p x ^ k *
        canonicalConditionedZ0mpCDFOrGaussian k m p x z := by
  have hmatching := isMatching_of_mem_orderedMatchingTuples hedges
  have hqp := two_mul_le_of_isMatching hmatching
  calc
    _ = (Measure.pi fun _ : Fin p ↦
        stdGaussian (centeredSubspace (m + 1))).real
        (canonicalMatchingFamilyJointEvent classicalCoherenceThreshold
          m p k hqp z x) :=
      orderedMatchingJointEvent_probability_eq_canonical_of_mem
        classicalCoherenceThreshold m p k z x edges hedges
    _ = _ := canonicalMatchingFamilyJointEvent_probability_factorization
      m p k hm hqp hpm z x hs0

end

end LogdetLean.Coherence
