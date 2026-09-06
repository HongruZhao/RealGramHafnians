import LogdetLean.Coherence.CanonicalMatchingWindow
import LogdetLean.Coherence.CanonicalConditionalCLT
/-!
# Conditional Gaussian limit for a bounded canonical matching window

This file conditions the fixed canonical matching on all selected normalized
locations lying in one bounded half-open window `(a,b]`.  For fixed positive
`k` and `a < b`, the conditioning event has exact mass
`(q(a)-q(b))^k`.  Its inclusion in the matching event at threshold `a`
allows the existing lower-threshold prefix-failure estimate to be reused.

No sum over edge tuples and no point-process convergence is asserted here.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology ProbabilityTheory ENNReal

/-- The limiting intensity of a nonempty bounded window is positive. -/
theorem classicalCoherenceIntensity_sub_pos
    {a b : ℝ} (hab : a < b) :
    0 < classicalCoherenceIntensity a - classicalCoherenceIntensity b := by
  have hc : 0 < (1 / Real.sqrt (8 * Real.pi) : ℝ) := by positivity
  have he : Real.exp (-b / 2) < Real.exp (-a / 2) := by
    rw [Real.exp_lt_exp]
    linarith
  unfold classicalCoherenceIntensity
  nlinarith [mul_lt_mul_of_pos_left he hc]

/-- Along every all-gap sequence, the ratio of the lower-threshold tail to
the bounded-window mass has the ratio of limiting intensities as its limit. -/
theorem tendsto_betaCorrelationTail_div_windowProbability
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {a b : ℝ} (hab : a < b) :
    Tendsto
      (fun p : ℕ ↦ betaCorrelationTailProbability (mseq p) p a /
        betaCorrelationWindowProbability (mseq p) p a b)
      atTop
      (nhds (classicalCoherenceIntensity a /
        (classicalCoherenceIntensity a - classicalCoherenceIntensity b))) := by
  have ha := allGapBetaTailIntensity mseq hadm a
  have habwin := tendsto_finiteCoherenceWindowIntensity hadm a b
  have hdiv := ha.div habwin
    (ne_of_gt (classicalCoherenceIntensity_sub_pos hab))
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hchooseN : 0 < p.choose 2 := Nat.choose_pos hp
  have hchooseR : (((p.choose 2 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  unfold finiteCoherenceWindowIntensity
  change
    (((p.choose 2 : ℕ) : ℝ) *
        betaCorrelationTailProbability (mseq p) p a) /
        (((p.choose 2 : ℕ) : ℝ) *
          betaCorrelationWindowProbability (mseq p) p a b) =
      betaCorrelationTailProbability (mseq p) p a /
        betaCorrelationWindowProbability (mseq p) p a b
  field_simp [hchooseR]

/-- Canonical bounded-window event on the centered right-nested prefix. -/
def canonicalCenteredMatchingWindowPrefixEvent
    (k m p : ℕ) (a b : ℝ) :
    Set (NestedTuple (centeredSubspace (m + 1)) (2 * k)) :=
  canonicalGaussianMatchingWindowEvent m p k a b

theorem measurableSet_canonicalCenteredMatchingWindowPrefixEvent
    (k m p : ℕ) (a b : ℝ) :
    MeasurableSet
      (canonicalCenteredMatchingWindowPrefixEvent k m p a b) :=
  measurableSet_canonicalGaussianMatchingWindowEvent _ _ _ _ _

/-- The bounded centered-prefix event is contained in the canonical matching
event at its lower endpoint. -/
theorem canonicalCenteredMatchingWindowPrefixEvent_subset_lower
    (k m p : ℕ) (a b : ℝ) :
    canonicalCenteredMatchingWindowPrefixEvent k m p a b ⊆
      canonicalCenteredMatchingPrefixEvent k m p a := by
  unfold canonicalCenteredMatchingWindowPrefixEvent
    canonicalCenteredMatchingPrefixEvent
  exact canonicalGaussianMatchingWindowEvent_subset_lowerMatching
    m p k a b

/-- Exact bounded-window mass in the centered nested-prefix model. -/
theorem canonicalCenteredMatchingWindowPrefixEvent_probability
    (m p : ℕ) (hm : 2 ≤ m) (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)).real
        (canonicalCenteredMatchingWindowPrefixEvent k m p a b) =
      (betaCorrelationWindowProbability m p a b) ^ k := by
  unfold canonicalCenteredMatchingWindowPrefixEvent
  apply canonicalGaussianMatchingWindowEvent_probability m p _ hm k hab
  simpa using finrank_centeredSubspace (N := m + 1)
    (Nat.zero_lt_succ m)

/-- Exact lower-threshold matching mass, rewritten in the common tail
notation used by the bounded-window calculation. -/
theorem canonicalCenteredMatchingPrefixEvent_probability_eq_tail
    (m p : ℕ) (hm : 2 ≤ m) (k : ℕ) (a : ℝ) :
    (nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)).real
        (canonicalCenteredMatchingPrefixEvent k m p a) =
      (betaCorrelationTailProbability m p a) ^ k := by
  unfold canonicalCenteredMatchingPrefixEvent
  rw [canonicalCenteredGaussianMatchingEvent_probability m hm k]
  rfl

/-- The bounded conditioning event has nonzero probability eventually in
every all-gap regime when its window has positive width. -/
theorem eventually_canonicalCenteredMatchingWindowPrefixEvent_ne_zero
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {a b : ℝ} (hab : a < b) :
    ∀ᶠ p in atTop,
      nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)
        (canonicalCenteredMatchingWindowPrefixEvent
          k (mseq p) p a b) ≠ 0 := by
  have hwin := tendsto_finiteCoherenceWindowIntensity hadm a b
  have hlim : 0 <
      classicalCoherenceIntensity a - classicalCoherenceIntensity b :=
    classicalCoherenceIntensity_sub_pos hab
  have hpos := hwin.eventually (eventually_gt_nhds hlim)
  filter_upwards [hadm, hpos] with p hp hposp
  have hm2 : 2 ≤ mseq p := hp.1.trans hp.2
  have hq : 0 < betaCorrelationWindowProbability (mseq p) p a b := by
    unfold finiteCoherenceWindowIntensity at hposp
    exact pos_of_mul_pos_right hposp
      (Nat.cast_nonneg (p.choose 2) :
        (0 : ℝ) ≤ ((p.choose 2 : ℕ) : ℝ))
  have hreal : 0 <
      (nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)).real
        (canonicalCenteredMatchingWindowPrefixEvent
          k (mseq p) p a b) := by
    rw [canonicalCenteredMatchingWindowPrefixEvent_probability
      (mseq p) p hm2 k hab.le]
    exact pow_pos hq k
  exact (measureReal_ne_zero_iff (by finiteness)).mp hreal.ne'

/-- Conditional bad mass of the centered prefix under bounded-window
conditioning.  The radius is the existing radius at the lower endpoint
`a`, since the window event is contained in that matching event. -/
def canonicalCenteredMatchingWindowPrefixBadMass
    (k m p : ℕ) (a b : ℝ) : ℝ :=
  let nu := nestedProductMeasure
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  let W := canonicalCenteredMatchingWindowPrefixEvent k m p a b
  (nu[|W]).real
    ((standardizedCenteredPrefixLogDetAtFullScale m (2 * k) p) ⁻¹'
      (Icc (-(canonicalCenteredPrefixTotalRadius k m p a))
        (canonicalCenteredPrefixTotalRadius k m p a))ᶜ)

/-- Finite-index comparison with the existing lower-threshold failure
ratio.  The only price for replacing lower-threshold conditioning by the
smaller bounded window is the exact mass ratio `(q(a)/q(a,b))^k`. -/
theorem canonicalCenteredMatchingWindowPrefixBadMass_le
    (k m p : ℕ) (hp : Admissible m p)
    {a b : ℝ} (hab : a ≤ b)
    (hW0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingWindowPrefixEvent k m p a b) ≠ 0) :
    canonicalCenteredMatchingWindowPrefixBadMass k m p a b ≤
      canonicalCenteredGaussianPrefixUncenteredFailureRelative k m p a *
        (betaCorrelationTailProbability m p a /
          betaCorrelationWindowProbability m p a b) ^ k := by
  let nu := nestedProductMeasure
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  let W := canonicalCenteredMatchingWindowPrefixEvent k m p a b
  let M := canonicalCenteredMatchingPrefixEvent k m p a
  let R := canonicalCenteredPrefixTotalRadius k m p a
  let B :=
    (standardizedCenteredPrefixLogDetAtFullScale m (2 * k) p) ⁻¹'
      (Icc (-R) R)ᶜ
  have hW : MeasurableSet W := by
    dsimp [W]
    exact measurableSet_canonicalCenteredMatchingWindowPrefixEvent
      k m p a b
  have hM : MeasurableSet M := by
    dsimp [M]
    exact measurableSet_canonicalCenteredMatchingPrefixEvent k m p a
  have hWM : W ⊆ M := by
    dsimp [W, M]
    exact canonicalCenteredMatchingWindowPrefixEvent_subset_lower
      k m p a b
  have hM0 : nu M ≠ 0 := by
    intro hzero
    apply hW0
    exact measure_mono_null hWM hzero
  have hWden : nu.real W ≠ 0 :=
    (measureReal_ne_zero_iff (by finiteness)).2 hW0
  have hlower :
      (nu[|M]).real B ≤
        canonicalCenteredGaussianPrefixUncenteredFailureRelative
          k m p a := by
    simpa [nu, M, B, R] using
      conditionedCenteredPrefix_badMass_le_uncenteredFailureRelative
        k m p hp a hM0
  have hsub : W ∩ B ⊆ M ∩ B :=
    Set.inter_subset_inter hWM Subset.rfl
  have hnum : nu.real (W ∩ B) ≤ nu.real (M ∩ B) :=
    measureReal_mono hsub
  have hmulW := measureReal_inter_eq_measureReal_mul_cond nu W B hW
  have hmulM := measureReal_inter_eq_measureReal_mul_cond nu M B hM
  have hcondW :
      (nu[|W]).real B = nu.real (W ∩ B) / nu.real W := by
    apply (eq_div_iff hWden).2
    calc
      (nu[|W]).real B * nu.real W =
          nu.real W * (nu[|W]).real B := mul_comm _ _
      _ = nu.real (W ∩ B) := hmulW.symm
  have hm2 : 2 ≤ m := hp.1.trans hp.2
  have hMprob :
      nu.real M = (betaCorrelationTailProbability m p a) ^ k := by
    simpa [nu, M] using
      canonicalCenteredMatchingPrefixEvent_probability_eq_tail
        m p hm2 k a
  have hWprob :
      nu.real W = (betaCorrelationWindowProbability m p a b) ^ k := by
    simpa [nu, W] using
      canonicalCenteredMatchingWindowPrefixEvent_probability
        m p hm2 k hab
  calc
    canonicalCenteredMatchingWindowPrefixBadMass k m p a b =
        (nu[|W]).real B := by
      rfl
    _ = nu.real (W ∩ B) / nu.real W := hcondW
    _ ≤ nu.real (M ∩ B) / nu.real W :=
      div_le_div_of_nonneg_right hnum measureReal_nonneg
    _ = (nu.real M * (nu[|M]).real B) / nu.real W := by
      rw [hmulM]
    _ ≤ (nu.real M *
          canonicalCenteredGaussianPrefixUncenteredFailureRelative
            k m p a) / nu.real W := by
      apply div_le_div_of_nonneg_right _ measureReal_nonneg
      exact mul_le_mul_of_nonneg_left hlower measureReal_nonneg
    _ = canonicalCenteredGaussianPrefixUncenteredFailureRelative
          k m p a * (nu.real M / nu.real W) := by ring
    _ = canonicalCenteredGaussianPrefixUncenteredFailureRelative
          k m p a *
            (betaCorrelationTailProbability m p a /
              betaCorrelationWindowProbability m p a b) ^ k := by
      rw [hMprob, hWprob, div_pow]

/-- The explicit upper bound in the preceding finite-index comparison tends
to zero along every admissible all-gap sequence. -/
theorem tendsto_canonicalWindowPrefixBadMass_upper_zero
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {a b : ℝ} (hab : a < b) :
    Tendsto
      (fun p : ℕ ↦
        canonicalCenteredGaussianPrefixUncenteredFailureRelative
            k (mseq p) p a *
          (betaCorrelationTailProbability (mseq p) p a /
            betaCorrelationWindowProbability (mseq p) p a b) ^ k)
      atTop (nhds 0) := by
  have hfailure :=
    tendsto_canonicalCenteredGaussianPrefixUncenteredFailureRelative_zero
      k hk hadm a
  have hratio :=
    (tendsto_betaCorrelationTail_div_windowProbability hadm hab).pow k
  simpa using hfailure.mul hratio

/-- Under bounded canonical-window conditioning, the centered prefix
contribution is negligible at the global null standard-deviation scale. -/
theorem tendsto_canonicalCenteredMatchingWindowPrefixBadMass_zero
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {a b : ℝ} (hab : a < b) :
    Tendsto
      (fun p : ℕ ↦
        canonicalCenteredMatchingWindowPrefixBadMass
          k (mseq p) p a b)
      atTop (nhds 0) := by
  have hW0 :=
    eventually_canonicalCenteredMatchingWindowPrefixEvent_ne_zero
      k hadm hab
  have hupper := tendsto_canonicalWindowPrefixBadMass_upper_zero
    k hk hadm hab
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ measureReal_nonneg
  · filter_upwards [hadm, hW0] with p hp hW0p
    exact canonicalCenteredMatchingWindowPrefixBadMass_le
      k (mseq p) p hp hab.le hW0p
  · exact hupper

/-- Bundled prefix--tail law under bounded canonical-window conditioning,
with the standard Gaussian fallback at invalid finite indices. -/
def canonicalWindowConditionedPrefixTailJointOrGaussian
    (k m p : ℕ) (a b : ℝ) : ProbabilityMeasure (ℝ × ℝ) :=
  conditionedPrefixTailJointOrGaussian m (2 * k) p
    (canonicalCenteredMatchingWindowPrefixEvent k m p a b)
    (measurableSet_canonicalCenteredMatchingWindowPrefixEvent
      k m p a b)

/-- At a valid finite index, the first-coordinate bad mass of the bundled
prefix--tail law is exactly the conditional centered-prefix bad mass. -/
theorem canonicalWindowConditionedPrefixTail_first_badMass_eq
    (k m p : ℕ) (hqp : 2 * k ≤ p) (hpm : p ≤ m)
    (a b : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingWindowPrefixEvent k m p a b) ≠ 0) :
    (canonicalWindowConditionedPrefixTailJointOrGaussian
      k m p a b : Measure (ℝ × ℝ)).real
      (((fun y : ℝ × ℝ ↦ y.1) ⁻¹'
        Icc (-(canonicalCenteredPrefixTotalRadius k m p a))
          (canonicalCenteredPrefixTotalRadius k m p a))ᶜ) =
      canonicalCenteredMatchingWindowPrefixBadMass k m p a b := by
  let s : Set (NestedTuple (centeredSubspace (m + 1)) (2 * k)) :=
    canonicalCenteredMatchingWindowPrefixEvent k m p a b
  let hs : MeasurableSet s :=
    measurableSet_canonicalCenteredMatchingWindowPrefixEvent k m p a b
  let R : ℝ := canonicalCenteredPrefixTotalRadius k m p a
  let D : Set ℝ := (Icc (-R) R)ᶜ
  let xi := nestedProductMeasure
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  have hs0' : xi s ≠ 0 := by
    simpa [xi, s] using hs0
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
      (canonicalWindowConditionedPrefixTailJointOrGaussian
        k m p a b : Measure (ℝ × ℝ)).real
        (((fun y : ℝ × ℝ ↦ y.1) ⁻¹' Icc (-R) R)ᶜ) =
      (xi[|s]).real
        ((standardizedCenteredPrefixLogDetAtFullScale
          m (2 * k) p) ⁻¹' D) := by
    rw [show canonicalWindowConditionedPrefixTailJointOrGaussian
        k m p a b =
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
        Prod.fst ⁻¹' D by
      simp only [D, preimage_compl]]
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
  rw [show canonicalCenteredPrefixTotalRadius k m p a = R by rfl,
    hjoint]
  rfl

/-- The first coordinate of the bounded-window-conditioned prefix--tail law
concentrates in the same shrinking interval as under lower-threshold
conditioning. -/
theorem tendsto_canonicalWindowConditionedPrefixTail_first_badMass_zero
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {a b : ℝ} (hab : a < b) :
    Tendsto
      (fun p : ℕ ↦
        (canonicalWindowConditionedPrefixTailJointOrGaussian
          k (mseq p) p a b : Measure (ℝ × ℝ)).real
          (((fun y : ℝ × ℝ ↦ y.1) ⁻¹'
            Icc (-(canonicalCenteredPrefixTotalRadius
              k (mseq p) p a))
              (canonicalCenteredPrefixTotalRadius
                k (mseq p) p a))ᶜ))
      atTop (nhds 0) := by
  have hdirect :=
    tendsto_canonicalCenteredMatchingWindowPrefixBadMass_zero
      k hk hadm hab
  have hW0 :=
    eventually_canonicalCenteredMatchingWindowPrefixEvent_ne_zero
      k hadm hab
  apply hdirect.congr'
  filter_upwards [hadm, hW0, eventually_ge_atTop (2 * k)]
    with p hp hW0p hqp
  exact (canonicalWindowConditionedPrefixTail_first_badMass_eq
    k (mseq p) p hqp hp.2 a b hW0p).symm

/-- Conditional CDF under bounded canonical-window conditioning, with the
same harmless Gaussian fallback used by the lower-threshold theorem. -/
def canonicalWindowConditionedZ0mpCDFOrGaussian
    (k m p : ℕ) (a b z : ℝ) : ℝ :=
  (((canonicalWindowConditionedPrefixTailJointOrGaussian
      k m p a b).map
      (measurable_fst.add measurable_snd).aemeasurable :
        ProbabilityMeasure ℝ) : Measure ℝ).real (Iic z)

/-- At every valid index, the bundled bounded-window conditional CDF is the
CDF of the actual standardized centered sample-correlation log determinant
under that prefix conditioning event. -/
theorem canonicalWindowConditionedZ0mpCDFOrGaussian_eq_actual
    (k m p : ℕ) (hqp : 2 * k ≤ p) (hpm : p ≤ m)
    (a b z : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingWindowPrefixEvent k m p a b) ≠ 0) :
    canonicalWindowConditionedZ0mpCDFOrGaussian k m p a b z =
      (Measure.map (Z0mpStatistic m (2 * k + (p - 2 * k)))
        ((conditionedCenteredGaussianPrefixProbabilityMeasure
          m (2 * k) (p - 2 * k) (by omega)
          (canonicalCenteredMatchingWindowPrefixEvent k m p a b)
          (measurableSet_canonicalCenteredMatchingWindowPrefixEvent
            k m p a b)
          hs0 : ProbabilityMeasure _) : Measure _)).real (Iic z) := by
  have h := conditionedPrefixTail_sum_CDF_eq_Z0mp_cond
    m (2 * k) p
    (canonicalCenteredMatchingWindowPrefixEvent k m p a b)
    (measurableSet_canonicalCenteredMatchingWindowPrefixEvent
      k m p a b)
    hqp hpm hs0 z
  simpa [canonicalWindowConditionedZ0mpCDFOrGaussian,
    canonicalWindowConditionedPrefixTailJointOrGaussian] using h

/-- **Canonical bounded-window conditional CLT.**  For every fixed positive
matching size and every nonempty bounded window, the conditional CDF of the
standardized log determinant converges to the standard normal CDF along
every admissible all-gap sequence. -/
theorem tendsto_canonicalWindowConditionedZ0mpCDFOrGaussian
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {a b : ℝ} (hab : a < b) (z : ℝ) :
    Tendsto
      (fun p : ℕ ↦
        canonicalWindowConditionedZ0mpCDFOrGaussian
          k (mseq p) p a b z)
      atTop (nhds (standardNormalCDF z)) := by
  let s : (p : ℕ) →
      Set (NestedTuple (centeredSubspace (mseq p + 1)) (2 * k)) :=
    fun p ↦ canonicalCenteredMatchingWindowPrefixEvent
      k (mseq p) p a b
  let hs : ∀ p, MeasurableSet (s p) := fun p ↦
    measurableSet_canonicalCenteredMatchingWindowPrefixEvent
      k (mseq p) p a b
  have hs0 : ∀ᶠ p in atTop,
      nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)
        (s p) ≠ 0 := by
    simpa [s] using
      eventually_canonicalCenteredMatchingWindowPrefixEvent_ne_zero
        k hadm hab
  have hr := eventually_canonicalCenteredPrefixTotalRadius_nonneg
    k hadm a
  have hr0 := tendsto_canonicalCenteredPrefixTotalRadius_zero
    k hk hadm a
  have hbad :=
    tendsto_canonicalWindowConditionedPrefixTail_first_badMass_zero
      k hk hadm hab
  have hmain := tendsto_conditionedPrefixTail_sum_CDF
    (2 * k) (by omega) mseq s hs hadm hs0
    (fun p ↦ canonicalCenteredPrefixTotalRadius k (mseq p) p a)
    hr hr0 (by
      simpa [s, hs, canonicalWindowConditionedPrefixTailJointOrGaussian]
        using hbad)
    z
  simpa [canonicalWindowConditionedZ0mpCDFOrGaussian,
    canonicalWindowConditionedPrefixTailJointOrGaussian, s, hs]
    using hmain

end

end LogdetLean.Coherence
