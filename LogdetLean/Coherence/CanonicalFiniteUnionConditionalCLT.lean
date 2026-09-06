import LogdetLean.Coherence.CanonicalFiniteUnionWindow
import LogdetLean.Coherence.CanonicalWindowConditionalCLT
/-!
# Conditional Gaussian limit for a canonical finite union of windows

Fix a finite indexed family of pairwise-disjoint score windows.  Under a
common lower bound and positive limiting total union intensity, this module
proves that conditioning a fixed positive canonical matching to fall in the
union does not alter the Gaussian log-determinant limit.

This is a canonical-prefix theorem.  It does not transport to arbitrary edge
tuples, assemble factorial moments, or assert point-process convergence.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology ProbabilityTheory ENNReal BigOperators

/-- The lower-tail-to-finite-union one-edge probability ratio has the ratio
of limiting intensities as its all-gap limit. -/
theorem tendsto_betaCorrelationTail_div_finiteUnionBetaProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (c : ℝ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) :
    Tendsto
      (fun p : ℕ ↦ betaCorrelationTailProbability (mseq p) p c /
        finiteUnionBetaProbability W (mseq p) p)
      atTop
      (nhds (classicalCoherenceIntensity c /
        finiteUnionClassicalCoherenceIntensity W)) := by
  have hc := allGapBetaTailIntensity mseq hadm c
  have hW := tendsto_finiteUnionCoherenceIntensity W hadm
  have hdiv := hc.div hW (ne_of_gt hnu)
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hchooseN : 0 < p.choose 2 := Nat.choose_pos hp
  have hchooseR : (((p.choose 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold finiteUnionCoherenceIntensity
  change
    (((p.choose 2 : ℕ) : ℝ) *
        betaCorrelationTailProbability (mseq p) p c) /
        (((p.choose 2 : ℕ) : ℝ) *
          finiteUnionBetaProbability W (mseq p) p) =
      betaCorrelationTailProbability (mseq p) p c /
        finiteUnionBetaProbability W (mseq p) p
  field_simp [hchooseR]

/-- Canonical finite-union event on the centered right-nested prefix. -/
def canonicalCenteredMatchingFiniteUnionPrefixEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) :
    Set (NestedTuple (centeredSubspace (m + 1)) (2 * k)) :=
  canonicalGaussianMatchingFiniteUnionEvent W m p k

theorem measurableSet_canonicalCenteredMatchingFiniteUnionPrefixEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) :
    MeasurableSet
      (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p) :=
  measurableSet_canonicalGaussianMatchingFiniteUnionEvent W m p k

/-- A common lower endpoint dominates the centered canonical finite-union
prefix event. -/
theorem canonicalCenteredMatchingFiniteUnionPrefixEvent_subset_lower
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) (hm : 2 ≤ m) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) :
    canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p ⊆
      canonicalCenteredMatchingPrefixEvent k m p c := by
  unfold canonicalCenteredMatchingFiniteUnionPrefixEvent
    canonicalCenteredMatchingPrefixEvent
  exact canonicalGaussianMatchingFiniteUnionEvent_subset_lowerMatching
    W hm k c hc

/-- Exact canonical finite-union mass in the centered nested-prefix model. -/
theorem canonicalCenteredMatchingFiniteUnionPrefixEvent_probability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    (nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)).real
        (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p) =
      (finiteUnionBetaProbability W m p) ^ k := by
  unfold canonicalCenteredMatchingFiniteUnionPrefixEvent
  apply canonicalGaussianMatchingFiniteUnionEvent_probability
    W m p _ hm k
  simpa using finrank_centeredSubspace (N := m + 1)
    (Nat.zero_lt_succ m)

/-- Positive limiting total union intensity makes the canonical finite-union
conditioning event nonnull eventually. -/
theorem eventually_canonicalCenteredMatchingFiniteUnionPrefixEvent_ne_zero
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) :
    ∀ᶠ p in atTop,
      nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)
        (canonicalCenteredMatchingFiniteUnionPrefixEvent
          W k (mseq p) p) ≠ 0 := by
  have hW := tendsto_finiteUnionCoherenceIntensity W hadm
  have hpos := hW.eventually (eventually_gt_nhds hnu)
  filter_upwards [hadm, hpos] with p hp hposp
  have hm2 : 2 ≤ mseq p := hp.1.trans hp.2
  have hq : 0 < finiteUnionBetaProbability W (mseq p) p := by
    unfold finiteUnionCoherenceIntensity at hposp
    exact pos_of_mul_pos_right hposp
      (Nat.cast_nonneg (p.choose 2) :
        (0 : ℝ) ≤ ((p.choose 2 : ℕ) : ℝ))
  have hreal : 0 <
      (nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)).real
        (canonicalCenteredMatchingFiniteUnionPrefixEvent
          W k (mseq p) p) := by
    rw [canonicalCenteredMatchingFiniteUnionPrefixEvent_probability
      W (mseq p) p hm2 k]
    exact pow_pos hq k
  exact (measureReal_ne_zero_iff (by finiteness)).mp hreal.ne'

/-- Conditional prefix bad mass under canonical finite-union conditioning.
The shrinking radius is evaluated at the common lower threshold `c`. -/
def canonicalCenteredMatchingFiniteUnionPrefixBadMass
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) (c : ℝ) : ℝ :=
  let nu := nestedProductMeasure
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  let S := canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p
  (nu[|S]).real
    ((standardizedCenteredPrefixLogDetAtFullScale m (2 * k) p) ⁻¹'
      (Icc (-(canonicalCenteredPrefixTotalRadius k m p c))
        (canonicalCenteredPrefixTotalRadius k m p c))ᶜ)

/-- Finite-index comparison: the finite-union-conditioned bad mass is
bounded by the common-lower failure ratio times the exact mass-ratio power. -/
theorem canonicalCenteredMatchingFiniteUnionPrefixBadMass_le
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) (hp : Admissible m p) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i)
    (hS0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p) ≠ 0) :
    canonicalCenteredMatchingFiniteUnionPrefixBadMass W k m p c ≤
      canonicalCenteredGaussianPrefixUncenteredFailureRelative k m p c *
        (betaCorrelationTailProbability m p c /
          finiteUnionBetaProbability W m p) ^ k := by
  let nu := nestedProductMeasure
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  let S := canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p
  let M := canonicalCenteredMatchingPrefixEvent k m p c
  let R := canonicalCenteredPrefixTotalRadius k m p c
  let B :=
    (standardizedCenteredPrefixLogDetAtFullScale m (2 * k) p) ⁻¹'
      (Icc (-R) R)ᶜ
  have hm2 : 2 ≤ m := hp.1.trans hp.2
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_canonicalCenteredMatchingFiniteUnionPrefixEvent
      W k m p
  have hM : MeasurableSet M := by
    dsimp [M]
    exact measurableSet_canonicalCenteredMatchingPrefixEvent k m p c
  have hSM : S ⊆ M := by
    dsimp [S, M]
    exact canonicalCenteredMatchingFiniteUnionPrefixEvent_subset_lower
      W k m p hm2 c hc
  have hM0 : nu M ≠ 0 := by
    intro hzero
    apply hS0
    exact measure_mono_null hSM hzero
  have hSden : nu.real S ≠ 0 :=
    (measureReal_ne_zero_iff (by finiteness)).2 hS0
  have hlower :
      (nu[|M]).real B ≤
        canonicalCenteredGaussianPrefixUncenteredFailureRelative
          k m p c := by
    simpa [nu, M, B, R] using
      conditionedCenteredPrefix_badMass_le_uncenteredFailureRelative
        k m p hp c hM0
  have hsub : S ∩ B ⊆ M ∩ B :=
    Set.inter_subset_inter hSM Subset.rfl
  have hnum : nu.real (S ∩ B) ≤ nu.real (M ∩ B) :=
    measureReal_mono hsub
  have hmulS := measureReal_inter_eq_measureReal_mul_cond nu S B hS
  have hmulM := measureReal_inter_eq_measureReal_mul_cond nu M B hM
  have hcondS :
      (nu[|S]).real B = nu.real (S ∩ B) / nu.real S := by
    apply (eq_div_iff hSden).2
    calc
      (nu[|S]).real B * nu.real S =
          nu.real S * (nu[|S]).real B := mul_comm _ _
      _ = nu.real (S ∩ B) := hmulS.symm
  have hMprob :
      nu.real M = (betaCorrelationTailProbability m p c) ^ k := by
    simpa [nu, M] using
      canonicalCenteredMatchingPrefixEvent_probability_eq_tail
        m p hm2 k c
  have hSprob :
      nu.real S = (finiteUnionBetaProbability W m p) ^ k := by
    simpa [nu, S] using
      canonicalCenteredMatchingFiniteUnionPrefixEvent_probability
        W m p hm2 k
  calc
    canonicalCenteredMatchingFiniteUnionPrefixBadMass W k m p c =
        (nu[|S]).real B := by rfl
    _ = nu.real (S ∩ B) / nu.real S := hcondS
    _ ≤ nu.real (M ∩ B) / nu.real S :=
      div_le_div_of_nonneg_right hnum measureReal_nonneg
    _ = (nu.real M * (nu[|M]).real B) / nu.real S := by
      rw [hmulM]
    _ ≤ (nu.real M *
          canonicalCenteredGaussianPrefixUncenteredFailureRelative
            k m p c) / nu.real S := by
      apply div_le_div_of_nonneg_right _ measureReal_nonneg
      exact mul_le_mul_of_nonneg_left hlower measureReal_nonneg
    _ = canonicalCenteredGaussianPrefixUncenteredFailureRelative
          k m p c * (nu.real M / nu.real S) := by ring
    _ = canonicalCenteredGaussianPrefixUncenteredFailureRelative
          k m p c *
            (betaCorrelationTailProbability m p c /
              finiteUnionBetaProbability W m p) ^ k := by
      rw [hMprob, hSprob, div_pow]

/-- The explicit finite-union bad-mass upper bound tends to zero. -/
theorem tendsto_canonicalFiniteUnionPrefixBadMass_upper_zero
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) :
    Tendsto
      (fun p : ℕ ↦
        canonicalCenteredGaussianPrefixUncenteredFailureRelative
            k (mseq p) p c *
          (betaCorrelationTailProbability (mseq p) p c /
            finiteUnionBetaProbability W (mseq p) p) ^ k)
      atTop (nhds 0) := by
  have hfailure :=
    tendsto_canonicalCenteredGaussianPrefixUncenteredFailureRelative_zero
      k hk hadm c
  have hratio :=
    (tendsto_betaCorrelationTail_div_finiteUnionBetaProbability
      W c hadm hnu).pow k
  simpa using hfailure.mul hratio

/-- The canonical finite-union-conditioned prefix contribution is
negligible at the global null scale. -/
theorem tendsto_canonicalCenteredMatchingFiniteUnionPrefixBadMass_zero
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) :
    Tendsto
      (fun p : ℕ ↦
        canonicalCenteredMatchingFiniteUnionPrefixBadMass
          W k (mseq p) p c)
      atTop (nhds 0) := by
  have hS0 :=
    eventually_canonicalCenteredMatchingFiniteUnionPrefixEvent_ne_zero
      W k hadm hnu
  have hupper := tendsto_canonicalFiniteUnionPrefixBadMass_upper_zero
    W k hk c hadm hnu
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ measureReal_nonneg
  · filter_upwards [hadm, hS0] with p hp hS0p
    exact canonicalCenteredMatchingFiniteUnionPrefixBadMass_le
      W k (mseq p) p hp c hc hS0p
  · exact hupper

/-- Bundled prefix--tail law under canonical finite-union conditioning. -/
def canonicalFiniteUnionConditionedPrefixTailJointOrGaussian
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) : ProbabilityMeasure (ℝ × ℝ) :=
  conditionedPrefixTailJointOrGaussian m (2 * k) p
    (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p)
    (measurableSet_canonicalCenteredMatchingFiniteUnionPrefixEvent
      W k m p)

/-- At every valid index, the first-coordinate bad mass of the bundled law
equals the direct finite-union-conditioned prefix bad mass. -/
theorem canonicalFiniteUnionConditionedPrefixTail_first_badMass_eq
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) (hqp : 2 * k ≤ p) (hpm : p ≤ m) (c : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p) ≠ 0) :
    (canonicalFiniteUnionConditionedPrefixTailJointOrGaussian
      W k m p : Measure (ℝ × ℝ)).real
      (((fun y : ℝ × ℝ ↦ y.1) ⁻¹'
        Icc (-(canonicalCenteredPrefixTotalRadius k m p c))
          (canonicalCenteredPrefixTotalRadius k m p c))ᶜ) =
      canonicalCenteredMatchingFiniteUnionPrefixBadMass W k m p c := by
  let s : Set (NestedTuple (centeredSubspace (m + 1)) (2 * k)) :=
    canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p
  let hs : MeasurableSet s :=
    measurableSet_canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p
  let R : ℝ := canonicalCenteredPrefixTotalRadius k m p c
  let D : Set ℝ := (Icc (-R) R)ᶜ
  let xi := nestedProductMeasure
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  have hs0' : xi s ≠ 0 := by simpa [xi, s] using hs0
  have hqr : 2 * k + (p - 2 * k) ≤ m := by
    rw [Nat.add_sub_of_le hqp]
    exact hpm
  have hD : MeasurableSet D := measurableSet_Icc.compl
  have hmap := map_fst_centeredGaussianPrefixTailPair_cond
    m (2 * k) (p - 2 * k) hqr s hs hs0'
  have hmapReal := congrArg (fun mu : Measure ℝ ↦ mu.real D) hmap
  have hfirst :
      (Measure.map Prod.fst
        (Measure.map
          (centeredGaussianPrefixTailPairStatistic
            m (2 * k) (p - 2 * k))
          ((conditionedCenteredGaussianPrefixProbabilityMeasure
            m (2 * k) (p - 2 * k) hqr
            s hs hs0' : ProbabilityMeasure _) : Measure _))).real D =
        (xi[|s]).real
          ((standardizedCenteredPrefixLogDetAtFullScale
            m (2 * k) p) ⁻¹' D) := by
    calc
      _ = (Measure.map
          (standardizedCenteredPrefixLogDetAtFullScale
            m (2 * k) p) (xi[|s])).real D := by
            simpa [xi, Nat.add_sub_of_le hqp] using hmapReal
      _ = (xi[|s]).real
          ((standardizedCenteredPrefixLogDetAtFullScale
            m (2 * k) p) ⁻¹' D) := by
            rw [measureReal_def,
              Measure.map_apply
                (measurable_standardizedCenteredPrefixLogDetAtFullScale
                  m (2 * k) p) hD,
              ← measureReal_def]
  have hjoint :
      (canonicalFiniteUnionConditionedPrefixTailJointOrGaussian
        W k m p : Measure (ℝ × ℝ)).real
        (((fun y : ℝ × ℝ ↦ y.1) ⁻¹' Icc (-R) R)ᶜ) =
      (xi[|s]).real
        ((standardizedCenteredPrefixLogDetAtFullScale
          m (2 * k) p) ⁻¹' D) := by
    rw [show canonicalFiniteUnionConditionedPrefixTailJointOrGaussian
        W k m p =
        conditionedPrefixTailJointOrGaussian
          m (2 * k) p s hs by rfl]
    rw [conditionedPrefixTailJointOrGaussian_eq_of_valid
      m (2 * k) p s hs hqp hpm hs0']
    change
      (Measure.map
        (centeredGaussianPrefixTailPairStatistic
          m (2 * k) (p - 2 * k))
        ((conditionedCenteredGaussianPrefixProbabilityMeasure
          m (2 * k) (p - 2 * k) hqr
          s hs hs0' : ProbabilityMeasure _) : Measure _)).real
        (((fun y : ℝ × ℝ ↦ y.1) ⁻¹' Icc (-R) R)ᶜ) = _
    rw [show ((fun y : ℝ × ℝ ↦ y.1) ⁻¹' Icc (-R) R)ᶜ =
        Prod.fst ⁻¹' D by simp only [D, preimage_compl]]
    calc
      _ = (Measure.map Prod.fst
          (Measure.map
            (centeredGaussianPrefixTailPairStatistic
              m (2 * k) (p - 2 * k))
            ((conditionedCenteredGaussianPrefixProbabilityMeasure
              m (2 * k) (p - 2 * k) hqr
              s hs hs0' : ProbabilityMeasure _) : Measure _))).real D := by
            have happly := Measure.map_apply
              (μ := Measure.map
                (centeredGaussianPrefixTailPairStatistic
                  m (2 * k) (p - 2 * k))
                ((conditionedCenteredGaussianPrefixProbabilityMeasure
                  m (2 * k) (p - 2 * k) hqr
                  s hs hs0' : ProbabilityMeasure _) : Measure _))
              measurable_fst hD
            have hreal := congrArg ENNReal.toReal happly
            simpa [measureReal_def] using hreal.symm
      _ = _ := hfirst
  rw [show canonicalCenteredPrefixTotalRadius k m p c = R by rfl,
    hjoint]
  rfl

/-- First-coordinate concentration under canonical finite-union
conditioning. -/
theorem tendsto_canonicalFiniteUnionConditionedPrefixTail_first_badMass_zero
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) :
    Tendsto
      (fun p : ℕ ↦
        (canonicalFiniteUnionConditionedPrefixTailJointOrGaussian
          W k (mseq p) p : Measure (ℝ × ℝ)).real
          (((fun y : ℝ × ℝ ↦ y.1) ⁻¹'
            Icc (-(canonicalCenteredPrefixTotalRadius
              k (mseq p) p c))
              (canonicalCenteredPrefixTotalRadius
                k (mseq p) p c))ᶜ))
      atTop (nhds 0) := by
  have hdirect :=
    tendsto_canonicalCenteredMatchingFiniteUnionPrefixBadMass_zero
      W k hk c hc hadm hnu
  have hS0 :=
    eventually_canonicalCenteredMatchingFiniteUnionPrefixEvent_ne_zero
      W k hadm hnu
  apply hdirect.congr'
  filter_upwards [hadm, hS0, eventually_ge_atTop (2 * k)]
    with p hp hS0p hqp
  exact (canonicalFiniteUnionConditionedPrefixTail_first_badMass_eq
    W k (mseq p) p hqp hp.2 c hS0p).symm

/-- Conditional CDF under canonical finite-union conditioning, with the
standard finite-index fallback. -/
def canonicalFiniteUnionConditionedZ0mpCDFOrGaussian
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) (z : ℝ) : ℝ :=
  (((canonicalFiniteUnionConditionedPrefixTailJointOrGaussian
      W k m p).map
      (measurable_fst.add measurable_snd).aemeasurable :
        ProbabilityMeasure ℝ) : Measure ℝ).real (Iic z)

/-- At valid indices, the bundled CDF is the actual conditional standardized
log-determinant CDF. -/
theorem canonicalFiniteUnionConditionedZ0mpCDFOrGaussian_eq_actual
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k m p : ℕ) (hqp : 2 * k ≤ p) (hpm : p ≤ m) (z : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p) ≠ 0) :
    canonicalFiniteUnionConditionedZ0mpCDFOrGaussian W k m p z =
      (Measure.map (Z0mpStatistic m (2 * k + (p - 2 * k)))
        ((conditionedCenteredGaussianPrefixProbabilityMeasure
          m (2 * k) (p - 2 * k) (by omega)
          (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p)
          (measurableSet_canonicalCenteredMatchingFiniteUnionPrefixEvent
            W k m p)
          hs0 : ProbabilityMeasure _) : Measure _)).real (Iic z) := by
  have h := conditionedPrefixTail_sum_CDF_eq_Z0mp_cond
    m (2 * k) p
    (canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p)
    (measurableSet_canonicalCenteredMatchingFiniteUnionPrefixEvent W k m p)
    hqp hpm hs0 z
  simpa [canonicalFiniteUnionConditionedZ0mpCDFOrGaussian,
    canonicalFiniteUnionConditionedPrefixTailJointOrGaussian] using h

/-- **Canonical finite-union conditional CLT.**  A common lower bound and
positive limiting total union intensity suffice for the conditional
standardized log-determinant CDF to converge to `Phi`. -/
theorem tendsto_canonicalFiniteUnionConditionedZ0mpCDFOrGaussian
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) (z : ℝ) :
    Tendsto
      (fun p : ℕ ↦
        canonicalFiniteUnionConditionedZ0mpCDFOrGaussian
          W k (mseq p) p z)
      atTop (nhds (standardNormalCDF z)) := by
  let s : (p : ℕ) →
      Set (NestedTuple (centeredSubspace (mseq p + 1)) (2 * k)) :=
    fun p ↦ canonicalCenteredMatchingFiniteUnionPrefixEvent
      W k (mseq p) p
  let hs : ∀ p, MeasurableSet (s p) := fun p ↦
    measurableSet_canonicalCenteredMatchingFiniteUnionPrefixEvent
      W k (mseq p) p
  have hs0 : ∀ᶠ p in atTop,
      nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)
        (s p) ≠ 0 := by
    simpa [s] using
      eventually_canonicalCenteredMatchingFiniteUnionPrefixEvent_ne_zero
        W k hadm hnu
  have hr := eventually_canonicalCenteredPrefixTotalRadius_nonneg
    k hadm c
  have hr0 := tendsto_canonicalCenteredPrefixTotalRadius_zero
    k hk hadm c
  have hbad :=
    tendsto_canonicalFiniteUnionConditionedPrefixTail_first_badMass_zero
      W k hk c hc hadm hnu
  have hmain := tendsto_conditionedPrefixTail_sum_CDF
    (2 * k) (by omega) mseq s hs hadm hs0
    (fun p ↦ canonicalCenteredPrefixTotalRadius k (mseq p) p c)
    hr hr0 (by
      simpa [s, hs,
        canonicalFiniteUnionConditionedPrefixTailJointOrGaussian]
        using hbad)
    z
  simpa [canonicalFiniteUnionConditionedZ0mpCDFOrGaussian,
    canonicalFiniteUnionConditionedPrefixTailJointOrGaussian, s, hs]
    using hmain

end

end LogdetLean.Coherence
