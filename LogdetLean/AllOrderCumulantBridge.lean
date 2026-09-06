import LogdetLean.AllOrderPolygamma
import LogdetLean.NullCenterStandardization
import Mathlib.MeasureTheory.Group.IntegralConvolution
/-!
# All-order cumulants of the finite log-Beta sum

This file closes the distinction between a formally defined reciprocal-power
coefficient and an actual probabilistic cumulant.  It proves that every
order-`r` derivative (`r >= 2`) of the exact log-Beta cumulant-generating
function equals the signed reciprocal-power series, and then transfers the
identity to the complete independent log-Beta sum.

The exact finite formula is Xie--Sun (2021), equations (3)--(7), printed
pp. 430--431.  Rouault (2007), equation (2.10), printed p. 189, supplies the
underlying Beta Mellin quotient.  The proof here is a direct Lean derivation
from that quotient and `AllOrderPolygamma`; neither source is imported as an
axiom.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators MeasureTheory

noncomputable section

set_option linter.style.haveILetI false

/-- Translation identity for the exact log-Beta CGF. -/
theorem betaLogCGF_add
    {alpha betaShape t s : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < betaShape)
    (halphat : 0 < alpha + t) (halphats : 0 < alpha + t + s) :
    betaLogCGF alpha betaShape (t + s) =
      betaLogCGF alpha betaShape t +
        betaLogCGF (alpha + t) betaShape s := by
  unfold betaLogCGF
  have h0 : beta alpha betaShape ≠ 0 := (beta_pos halpha hbeta).ne'
  have ht : beta (alpha + t) betaShape ≠ 0 :=
    (beta_pos halphat hbeta).ne'
  have hts : beta (alpha + (t + s)) betaShape ≠ 0 :=
    (beta_pos (by linarith) hbeta).ne'
  rw [Real.log_div hts h0, Real.log_div ht h0]
  rw [Real.log_div (by simpa [add_assoc] using hts) ht]
  ring_nf

/-- Local translation identity around zero. -/
theorem betaLogCGF_translate_eventuallyEq
    {alpha betaShape t : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < betaShape)
    (halphat : 0 < alpha + t) :
    (fun s : ℝ ↦ betaLogCGF alpha betaShape (t + s)) =ᶠ[nhds 0]
      (fun s ↦ betaLogCGF alpha betaShape t +
        betaLogCGF (alpha + t) betaShape s) := by
  filter_upwards [Ioi_mem_nhds (show -(alpha + t) < (0 : ℝ) by linarith)]
    with s hs
  exact betaLogCGF_add halpha hbeta halphat (by
    have hs' : -(alpha + t) < s := hs
    linarith)

/-- Every positive-order derivative at `t` can be shifted to a derivative at
zero with first Beta shape `alpha+t`. -/
theorem iteratedDeriv_betaLogCGF_eq_shifted_zero
    {alpha betaShape t : ℝ} {r : ℕ} (hr : 0 < r)
    (halpha : 0 < alpha) (hbeta : 0 < betaShape)
    (halphat : 0 < alpha + t) :
    iteratedDeriv r (betaLogCGF alpha betaShape) t =
      iteratedDeriv r (betaLogCGF (alpha + t) betaShape) 0 := by
  have hder := (betaLogCGF_translate_eventuallyEq
    halpha hbeta halphat).iteratedDeriv_eq r
  have hleft := congrFun
    (iteratedDeriv_comp_const_add r (betaLogCGF alpha betaShape) t) 0
  have hright := iteratedDeriv_const_add
    (f := betaLogCGF (alpha + t) betaShape) (x := 0) hr
      (betaLogCGF alpha betaShape t)
  simpa only [add_zero] using hleft.symm.trans (hder.trans hright)

/-- Actual one-factor cumulant formula at every order `r >= 2` and every
point in the natural MGF domain. -/
theorem iteratedDeriv_betaLogCGF_eq_signedPolygammaDifference
    (n : ℕ) {alpha betaShape t : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < betaShape)
    (halphat : 0 < alpha + t) :
    iteratedDeriv (n + 2) (betaLogCGF alpha betaShape) t =
      signedPolygammaSeries (n + 2) (alpha + t) -
        signedPolygammaSeries (n + 2) (alpha + betaShape + t) := by
  induction n generalizing t with
  | zero =>
      rw [iteratedDeriv_betaLogCGF_eq_shifted_zero (by omega)
        halpha hbeta halphat]
      rw [iteratedDeriv_two_betaLogCGF_eq_trigammaSeries_sub
        halphat hbeta]
      rw [signedPolygammaSeries_two, signedPolygammaSeries_two]
      congr 2
      ring
  | succ n ih =>
      have hevent :
          iteratedDeriv (n + 2) (betaLogCGF alpha betaShape) =ᶠ[nhds t]
            (fun y ↦
              signedPolygammaSeries (n + 2) (alpha + y) -
                signedPolygammaSeries (n + 2)
                  (alpha + betaShape + y)) := by
        filter_upwards [Ioi_mem_nhds (show -alpha < t by linarith)] with y hy
        exact ih (by
          have hy' : -alpha < y := hy
          linarith)
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        iteratedDeriv_succ, hevent.deriv_eq]
      have hleft := (hasDerivAt_signedPolygammaSeries (r := n + 2) (by omega)
        halphat).comp t ((hasDerivAt_id t).const_add alpha)
      have hright := (hasDerivAt_signedPolygammaSeries (r := n + 2) (by omega)
        (by linarith : 0 < alpha + betaShape + t)).comp t
          ((hasDerivAt_id t).const_add (alpha + betaShape))
      change deriv
          ((fun y : ℝ ↦ signedPolygammaSeries (n + 2) (alpha + y)) -
            (fun y : ℝ ↦ signedPolygammaSeries (n + 2)
              (alpha + betaShape + y))) t = _
      simpa [Function.comp_def] using (hleft.sub hright).deriv

/-- Reindexed one-factor formula. -/
theorem iteratedDeriv_betaLogCGF_eq_signedPolygammaDifference_of_two_le
    {r : ℕ} (hr : 2 ≤ r) {alpha betaShape : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    iteratedDeriv r (betaLogCGF alpha betaShape) 0 =
      signedPolygammaSeries r alpha -
        signedPolygammaSeries r (alpha + betaShape) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  simpa using iteratedDeriv_betaLogCGF_eq_signedPolygammaDifference
    (t := 0) n halpha hbeta (by simpa using halpha)

/-- Explicit finite CGF obtained by adding the individual log-Beta CGFs. -/
def nullFiniteLogCGF (m p : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 p,
    betaLogCGF (betaShapeA m j) (betaShapeB j) t

/-- The signed all-order finite cumulant series. -/
def nullSignedCumulantSeries (r m p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 p,
    (signedPolygammaSeries r (betaShapeA m j) -
      signedPolygammaSeries r (betaShapeTotal m))

/-- Each exact one-factor log-Beta CGF is smooth to every finite order at
zero. -/
theorem contDiffAt_betaLogCGF
    {alpha betaShape : ℝ} (halpha : 0 < alpha) (hbeta : 0 < betaShape)
    (r : ℕ) : ContDiffAt ℝ r (betaLogCGF alpha betaShape) 0 := by
  have hc : ContDiffAt ℝ r (cgf Real.log (betaMeasure alpha betaShape)) 0 :=
    (analyticAt_cgf
      (zero_mem_interior_integrableExpSet_log_betaMeasure halpha hbeta)).contDiffAt
  exact hc.congr_of_eventuallyEq
    (cgf_log_betaMeasure_eventuallyEq halpha hbeta).symm

/-- The explicit finite CGF has exactly the signed reciprocal-power
cumulant at every order `r >= 2`. -/
theorem iteratedDeriv_nullFiniteLogCGF_eq_nullSignedCumulantSeries
    {r m p : ℕ} (hr : 2 ≤ r) (h : Admissible m p) :
    iteratedDeriv r (nullFiniteLogCGF m p) 0 =
      nullSignedCumulantSeries r m p := by
  unfold nullFiniteLogCGF nullSignedCumulantSeries
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [iteratedDeriv_betaLogCGF_eq_signedPolygammaDifference_of_two_le
      hr (betaShapeA_pos_of_le (hj.2.trans h.2))
        (betaShapeB_pos_of_two_le hj.1)]
    rw [betaShapeA_add_betaShapeB_eq_total]
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact contDiffAt_betaLogCGF
      (betaShapeA_pos_of_le (hj.2.trans h.2))
      (betaShapeB_pos_of_two_le hj.1) r

/-- The first derivative of the explicit finite CGF is the finite digamma
center. -/
theorem iteratedDeriv_one_nullFiniteLogCGF_eq_nullCenterDigammaSeries
    {m p : ℕ} (h : Admissible m p) :
    iteratedDeriv 1 (nullFiniteLogCGF m p) 0 =
      nullCenterDigammaSeries m p := by
  unfold nullFiniteLogCGF nullCenterDigammaSeries
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [iteratedDeriv_one,
      deriv_betaLogCGF_zero_eq_digammaSeries_sub
        (betaShapeA_pos_of_le (hj.2.trans h.2))
        (betaShapeB_pos_of_two_le hj.1),
      betaShapeA_add_betaShapeB_eq_total]
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact contDiffAt_betaLogCGF
      (betaShapeA_pos_of_le (hj.2.trans h.2))
      (betaShapeB_pos_of_two_le hj.1) 1

/-! ## Identification with the CGF of the actual convolution law -/

/-- Natural real MGF domain for the complete finite array. -/
def NullMgfDomain (m p : ℕ) (t : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 2 p, 0 < betaShapeA m j + t

/-- One-factor real Mellin quotient. -/
def logBetaMgfFactor (m j : ℕ) (t : ℝ) : ℝ :=
  beta (betaShapeA m j + t) (betaShapeB j) /
    beta (betaShapeA m j) (betaShapeB j)

/-- Product of the one-factor real Mellin quotients. -/
def logBetaMgfProduct (m p : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 2 p, logBetaMgfFactor m j t

/-- Exponential integrability is preserved by additive convolution. -/
theorem integrable_exp_mul_id_conv
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {t : ℝ}
    (hμ : Integrable (fun x : ℝ ↦ Real.exp (t * x)) μ)
    (hν : Integrable (fun y : ℝ ↦ Real.exp (t * y)) ν) :
    Integrable (fun z : ℝ ↦ Real.exp (t * z)) (μ ∗ ν) := by
  rw [Measure.conv, integrable_map_measure (by fun_prop) (by fun_prop)]
  have hprod := hμ.mul_prod hν
  refine hprod.congr ?_
  filter_upwards with z
  simp only [Function.comp_apply]
  rw [show t * (z.1 + z.2) = t * z.1 + t * z.2 by ring,
    Real.exp_add]

/-- The MGF of a convolution is the product of the MGFs whenever the two
exponential integrals are finite. -/
theorem mgf_id_conv
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {t : ℝ}
    (_hμ : Integrable (fun x : ℝ ↦ Real.exp (t * x)) μ)
    (_hν : Integrable (fun y : ℝ ↦ Real.exp (t * y)) ν) :
    mgf id (μ ∗ ν) t = mgf id μ t * mgf id ν t := by
  unfold mgf
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  simp only [id_eq]
  have hfun : (fun z : ℝ × ℝ ↦ Real.exp (t * (z.1 + z.2))) =
      (fun z ↦ Real.exp (t * z.1) * Real.exp (t * z.2)) := by
    funext z
    rw [show t * (z.1 + z.2) = t * z.1 + t * z.2 by ring,
      Real.exp_add]
  rw [hfun]
  exact integral_prod_mul (μ := μ) (ν := ν)
    (fun x : ℝ ↦ Real.exp (t * x))
    (fun y : ℝ ↦ Real.exp (t * y))

/-- Exponential integrability of one mapped log-Beta factor. -/
theorem integrable_exp_mul_id_logBetaLaw
    {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) {t : ℝ}
    (hdom : 0 < betaShapeA m j + t) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (logBetaLaw m j) := by
  have hA := betaShapeA_pos_of_le hjm
  have hB := betaShapeB_pos_of_two_le hj
  unfold logBetaLaw
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def] using
    integrable_exp_mul_log_betaMeasure hA hB hdom

/-- Exact real MGF of one mapped log-Beta factor. -/
theorem mgf_id_logBetaLaw_eq_factor
    {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) {t : ℝ}
    (hdom : 0 < betaShapeA m j + t) :
    mgf id (logBetaLaw m j) t = logBetaMgfFactor m j t := by
  have hA := betaShapeA_pos_of_le hjm
  have hB := betaShapeB_pos_of_two_le hj
  unfold logBetaLaw
  rw [mgf_id_map (measurable_log.aemeasurable)]
  exact mgf_log_betaMeasure hA hB hdom

/-- Simultaneous exponential-integrability and exact-MGF induction for the
complete finite log-Beta convolution. -/
theorem integrable_exp_and_mgf_logBetaSumLaw
    {m p : ℕ} (hpm : p ≤ m) {t : ℝ} (hdom : NullMgfDomain m p t) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (logBetaSumLaw m p) ∧
      mgf id (logBetaSumLaw m p) t = logBetaMgfProduct m p t := by
  induction p with
  | zero =>
      constructor
      · rw [logBetaSumLaw]
        exact integrable_dirac (by simp)
      · simp [logBetaSumLaw, logBetaMgfProduct, mgf]
  | succ p ih =>
      by_cases hp2 : 2 ≤ p + 1
      · have hprevpm : p ≤ m := by omega
        have hprevdom : NullMgfDomain m p t := by
          intro j hj
          exact hdom j (Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hj).1,
              (Finset.mem_Icc.mp hj).2.trans (Nat.le_succ p)⟩)
        have hfreshdom : 0 < betaShapeA m (p + 1) + t :=
          hdom (p + 1) (Finset.mem_Icc.mpr ⟨hp2, le_rfl⟩)
        have hprev := ih hprevpm hprevdom
        have hfresh := integrable_exp_mul_id_logBetaLaw
          hpm hp2 hfreshdom
        haveI : IsProbabilityMeasure (logBetaSumLaw m p) :=
          isProbabilityMeasure_logBetaSumLaw hprevpm
        haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm hp2
        constructor
        · rw [logBetaSumLaw, if_pos hp2]
          exact integrable_exp_mul_id_conv hprev.1 hfresh
        · rw [logBetaSumLaw, if_pos hp2,
            mgf_id_conv hprev.1 hfresh, hprev.2,
            mgf_id_logBetaLaw_eq_factor hpm hp2 hfreshdom]
          unfold logBetaMgfProduct
          rw [Finset.prod_Icc_succ_top hp2]
      · have hp0 : p = 0 := by omega
        subst p
        constructor
        · rw [logBetaSumLaw]
          exact integrable_dirac (by simp)
        · simp [logBetaSumLaw, logBetaMgfProduct, mgf]

/-- Exact real Gamma/Beta product for the finite sum MGF. -/
theorem mgf_logBetaSumLaw_eq_product
    {m p : ℕ} (hpm : p ≤ m) {t : ℝ} (hdom : NullMgfDomain m p t) :
    mgf id (logBetaSumLaw m p) t = logBetaMgfProduct m p t :=
  (integrable_exp_and_mgf_logBetaSumLaw hpm hdom).2

/-- Every factor in the real MGF product is strictly positive on its natural
domain. -/
theorem logBetaMgfFactor_pos
    {m p j : ℕ} (hpm : p ≤ m) (hj : j ∈ Finset.Icc 2 p)
    {t : ℝ} (hdom : NullMgfDomain m p t) :
    0 < logBetaMgfFactor m j t := by
  rw [Finset.mem_Icc] at hj
  unfold logBetaMgfFactor
  exact div_pos
    (beta_pos (hdom j (Finset.mem_Icc.mpr hj))
      (betaShapeB_pos_of_two_le hj.1))
    (beta_pos (betaShapeA_pos_of_le (hj.2.trans hpm))
      (betaShapeB_pos_of_two_le hj.1))

/-- On the natural domain, the probabilistic CGF of the convolved law is
exactly the finite sum of one-factor log-Beta CGFs. -/
theorem cgf_logBetaSumLaw_eq_nullFiniteLogCGF
    {m p : ℕ} (hpm : p ≤ m) {t : ℝ} (hdom : NullMgfDomain m p t) :
    cgf id (logBetaSumLaw m p) t = nullFiniteLogCGF m p t := by
  unfold cgf
  rw [mgf_logBetaSumLaw_eq_product hpm hdom]
  unfold logBetaMgfProduct nullFiniteLogCGF
  rw [Real.log_prod (fun j hj ↦
    (logBetaMgfFactor_pos hpm hj hdom).ne')]
  apply Finset.sum_congr rfl
  intro j _hj
  rfl

/-- For every admissible finite array, zero has a whole neighborhood inside
the common MGF domain. -/
theorem eventually_nullMgfDomain {m p : ℕ} (h : Admissible m p) :
    ∀ᶠ t in nhds 0, NullMgfDomain m p t := by
  have hap : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  filter_upwards [Ioi_mem_nhds (show -betaShapeA m p < (0 : ℝ) by linarith)]
    with t ht
  intro j hj
  have hjp : j ≤ p := (Finset.mem_Icc.mp hj).2
  have hmono : betaShapeA m p ≤ betaShapeA m j := by
    unfold betaShapeA
    have hjpR : (j : ℝ) ≤ (p : ℝ) := by exact_mod_cast hjp
    linarith
  have ht' : -betaShapeA m p < t := ht
  linarith

/-- The actual law CGF and the explicit finite CGF agree near zero. -/
theorem cgf_logBetaSumLaw_eventuallyEq_nullFiniteLogCGF
    {m p : ℕ} (h : Admissible m p) :
    cgf id (logBetaSumLaw m p) =ᶠ[nhds 0] nullFiniteLogCGF m p := by
  filter_upwards [eventually_nullMgfDomain h] with t ht
  exact cgf_logBetaSumLaw_eq_nullFiniteLogCGF h.2 ht

/-- The order-`r` cumulant of the actual convolved law, defined in the usual
way as an `r`th CGF derivative. -/
def nullLawCumulant (r m p : ℕ) : ℝ :=
  iteratedDeriv r (cgf id (logBetaSumLaw m p)) 0

/-- The first actual cumulant is the already verified exact finite digamma
center. -/
theorem nullLawCumulant_one_eq_nullCenterDigammaSeries
    {m p : ℕ} (h : Admissible m p) :
    nullLawCumulant 1 m p = nullCenterDigammaSeries m p := by
  unfold nullLawCumulant
  rw [(cgf_logBetaSumLaw_eventuallyEq_nullFiniteLogCGF h).iteratedDeriv_eq 1]
  exact iteratedDeriv_one_nullFiniteLogCGF_eq_nullCenterDigammaSeries h

/-- The actual probabilistic cumulant equals the signed finite series at every
order `r >= 2`. -/
theorem nullLawCumulant_eq_nullSignedCumulantSeries
    {r m p : ℕ} (hr : 2 ≤ r) (h : Admissible m p) :
    nullLawCumulant r m p = nullSignedCumulantSeries r m p := by
  unfold nullLawCumulant
  rw [(cgf_logBetaSumLaw_eventuallyEq_nullFiniteLogCGF h).iteratedDeriv_eq r]
  exact iteratedDeriv_nullFiniteLogCGF_eq_nullSignedCumulantSeries hr h

/-- A reciprocal-power difference is the difference of the two separately
summed reciprocal-power series. -/
theorem reciprocalPowerDifference_eq_reciprocalPowerSeries_sub
    {r : ℕ} (hr : 1 < r) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    reciprocalPowerDifference r x y =
      reciprocalPowerSeries r x - reciprocalPowerSeries r y := by
  unfold reciprocalPowerDifference reciprocalPowerSeries
  rw [(summable_shifted_reciprocal_pow hx hr).tsum_sub
    (summable_shifted_reciprocal_pow hy hr)]

/-- The signed finite series is exactly `(-1)^r` times the positive magnitude
used in the cumulant majorant. -/
theorem nullSignedCumulantSeries_eq_sign_mul_magnitude
    {r m p : ℕ} (hr : 2 ≤ r) (h : Admissible m p) :
    nullSignedCumulantSeries r m p =
      (-1 : ℝ) ^ r * nullCumulantMagnitudeSeries r m p := by
  unfold nullSignedCumulantSeries nullCumulantMagnitudeSeries
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb := Finset.mem_Icc.mp hj
  have haj : 0 < betaShapeA m j :=
    betaShapeA_pos_of_le (hjb.2.trans h.2)
  have hM : 0 < betaShapeTotal m := betaShapeTotal_pos h
  rw [signedPolygammaSeries, signedPolygammaSeries]
  rw [reciprocalPowerDifference_eq_reciprocalPowerSeries_sub
    (by omega) haj hM]
  ring

/-- Final all-order probabilistic identity: for `r >= 2`, the cumulant of the
actual independent log-Beta sum is `(-1)^r` times the positive series
coefficient. -/
theorem nullLawCumulant_eq_sign_mul_magnitude
    {r m p : ℕ} (hr : 2 ≤ r) (h : Admissible m p) :
    nullLawCumulant r m p =
      (-1 : ℝ) ^ r * nullCumulantMagnitudeSeries r m p := by
  rw [nullLawCumulant_eq_nullSignedCumulantSeries hr h,
    nullSignedCumulantSeries_eq_sign_mul_magnitude hr h]

/-- The same cumulant, defined directly on the centered Gaussian sample
space rather than on its pushed-forward law. -/
def nullSampleLogDetCumulant (r m p : ℕ) : ℝ :=
  iteratedDeriv r
    (cgf (Real.log ∘ centeredSampleCorrelationDet (m + 1) p)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p)) 0

/-- The sample-space CGF is exactly the CGF of `logBetaSumLaw`. -/
theorem cgf_centeredSampleCorrelationLogDet_eq_logBetaSumCGF
    {m p : ℕ} (hpm : p ≤ m) :
    cgf (Real.log ∘ centeredSampleCorrelationDet (m + 1) p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
      cgf id (logBetaSumLaw m p) := by
  let X := Real.log ∘ centeredSampleCorrelationDet (m + 1) p
  let μ := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) p
  have hX : AEMeasurable X μ :=
    (measurable_log.comp
      (measurable_centeredSampleCorrelationDet
        (Nat.zero_lt_succ m))).aemeasurable
  have hmgf : mgf X μ = mgf id (μ.map X) :=
    (mgf_id_map hX).symm
  have hmap : μ.map X = logBetaSumLaw m p := by
    exact map_log_centeredSampleCorrelationDet_succ_eq_logBetaSumLaw
      m p hpm
  unfold cgf
  rw [hmgf, hmap]

/-- Every order-`r >= 2` cumulant of the actual Gaussian
sample-correlation log determinant has the exact signed series formula. -/
theorem nullSampleLogDetCumulant_eq_sign_mul_magnitude
    {r m p : ℕ} (hr : 2 ≤ r) (h : Admissible m p) :
    nullSampleLogDetCumulant r m p =
      (-1 : ℝ) ^ r * nullCumulantMagnitudeSeries r m p := by
  unfold nullSampleLogDetCumulant
  rw [cgf_centeredSampleCorrelationLogDet_eq_logBetaSumCGF h.2]
  exact nullLawCumulant_eq_sign_mul_magnitude hr h

/-- The first cumulant of the actual Gaussian sample log determinant is its
finite digamma center. -/
theorem nullSampleLogDetCumulant_one_eq_nullCenterDigammaSeries
    {m p : ℕ} (h : Admissible m p) :
    nullSampleLogDetCumulant 1 m p = nullCenterDigammaSeries m p := by
  unfold nullSampleLogDetCumulant
  rw [cgf_centeredSampleCorrelationLogDet_eq_logBetaSumCGF h.2]
  exact nullLawCumulant_one_eq_nullCenterDigammaSeries h

end

end LogdetLean
