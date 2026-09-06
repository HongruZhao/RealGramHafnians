import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
/-!
# Elementary Mills bounds for a beta half-tail

This module isolates the endpoint integration-by-parts estimate used for the
tail of a `Beta(1/2,b)` random variable.  We work with the unnormalised tail

`I_b(t) = integral from t to 1 of x^(-1/2) (1-x)^(b-1) dx`.

For `b > 1` and `0 < t < 1`, integration by parts gives

`I_b(t) = t^(-1/2) (1-t)^b / b - J_b(t)/(2b)`,

where `J_b(t)` is the same integral with the first exponent lowered by one
and the second exponent raised by one.  The pointwise estimate
`J_b(t) <= I_b(t)/t` then yields the two-sided Mills bound.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory Set
open scoped Interval Real

/-- Unnormalised upper tail of the `Beta(1/2,b)` density. -/
def betaHalfTailIntegral (b t : ℝ) : ℝ :=
  ∫ x in t..1, x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1)

/-- Remainder integral in the endpoint integration-by-parts identity. -/
def betaHalfTailRemainder (b t : ℝ) : ℝ :=
  ∫ x in t..1, x ^ (-(3 / 2 : ℝ)) * (1 - x) ^ b

/-- Endpoint term in the beta half-tail Mills ratio. -/
def betaHalfTailEndpoint (b t : ℝ) : ℝ :=
  t ^ (-(1 / 2 : ℝ)) * (1 - t) ^ b / b

private lemma hasDerivAt_rpow_neg_half {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ y ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) x := by
  simpa only [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num] using
    (Real.hasDerivAt_rpow_const (x := x) (p := -(1 / 2 : ℝ))
      (Or.inl hx.ne'))

private lemma hasDerivAt_one_sub_rpow {b x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ ↦ (1 - y) ^ b)
      (-b * (1 - x) ^ (b - 1)) x := by
  have hbase : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
  convert hbase.rpow_const (p := b) (Or.inl (sub_ne_zero.mpr hx.ne.symm)) using 1
  ring

/-- Exact endpoint integration-by-parts identity for the unnormalised beta
half-tail.  The assumption `1 < b` is harmless in the asymptotic application
and makes every endpoint integrand continuous on the closed interval. -/
theorem betaHalfTailIntegral_eq_endpoint_sub_remainder
    {b t : ℝ} (hb : 1 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    betaHalfTailIntegral b t =
      betaHalfTailEndpoint b t - betaHalfTailRemainder b t / (2 * b) := by
  let u : ℝ → ℝ := fun x ↦ x ^ (-(1 / 2 : ℝ))
  let u' : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))
  let v : ℝ → ℝ := fun x ↦ (1 - x) ^ b
  let v' : ℝ → ℝ := fun x ↦ -b * (1 - x) ^ (b - 1)
  have ht_le : t ≤ 1 := ht1.le
  have hu : ContinuousOn u [[t, 1]] := by
    rw [uIcc_of_le ht_le]
    exact continuousOn_id.rpow_const fun x hx ↦
      Or.inl (ne_of_gt (ht0.trans_le hx.1))
  have hu' : ContinuousOn u' [[t, 1]] := by
    rw [uIcc_of_le ht_le]
    exact continuousOn_const.mul <|
      continuousOn_id.rpow_const fun x hx ↦
        Or.inl (ne_of_gt (ht0.trans_le hx.1))
  have hv : ContinuousOn v [[t, 1]] := by
    rw [uIcc_of_le ht_le]
    exact (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ ↦
      Or.inr (zero_lt_one.trans hb).le
  have hv' : ContinuousOn v' [[t, 1]] := by
    rw [uIcc_of_le ht_le]
    exact continuousOn_const.mul <|
      (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ ↦
        Or.inr (sub_nonneg.mpr hb.le)
  have hdu : ∀ x ∈ Ioo (min t 1) (max t 1), HasDerivAt u (u' x) x := by
    intro x hx
    rw [min_eq_left ht_le, max_eq_right ht_le] at hx
    exact hasDerivAt_rpow_neg_half (ht0.trans hx.1)
  have hdv : ∀ x ∈ Ioo (min t 1) (max t 1), HasDerivAt v (v' x) x := by
    intro x hx
    rw [min_eq_left ht_le, max_eq_right ht_le] at hx
    exact hasDerivAt_one_sub_rpow hx.2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu hv hdu hdv hu'.intervalIntegrable hv'.intervalIntegrable
  have hb0 : b ≠ 0 := ne_of_gt (zero_lt_one.trans hb)
  change (∫ x in t..1, u x * v' x) =
      u 1 * v 1 - u t * v t - ∫ x in t..1, u' x * v x at hibp
  have hleft : (∫ x in t..1, u x * v' x) =
      -b * betaHalfTailIntegral b t := by
    rw [betaHalfTailIntegral]
    simp only [u, v']
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hrem : (∫ x in t..1, u' x * v x) =
      -(1 / 2 : ℝ) * betaHalfTailRemainder b t := by
    rw [betaHalfTailRemainder]
    simp only [u', v]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hleft, hrem] at hibp
  norm_num [u, v, Real.zero_rpow hb0] at hibp
  unfold betaHalfTailEndpoint
  field_simp [hb0]
  linarith

private lemma betaHalfTail_remainder_integrand_eq
    {b t x : ℝ} (hb : 1 < b) (ht0 : 0 < t)
    (hx : x ∈ Icc t 1) :
    x ^ (-(3 / 2 : ℝ)) * (1 - x) ^ b =
      ((1 - x) / x) *
        (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1)) := by
  have hx0 : 0 < x := ht0.trans_le hx.1
  have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hxpow : x ^ (-(3 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) / x := by
    rw [show -(3 / 2 : ℝ) = -(1 / 2 : ℝ) - 1 by ring,
      Real.rpow_sub hx0, Real.rpow_one]
  have h1xpow : (1 - x) ^ b = (1 - x) ^ (b - 1) * (1 - x) := by
    calc
      (1 - x) ^ b = (1 - x) ^ ((b - 1) + 1) := by congr 1; ring
      _ = (1 - x) ^ (b - 1) * (1 - x) :=
        Real.rpow_add_one' (y := b - 1) h1x (by linarith)
  rw [hxpow, h1xpow]
  field_simp [hx0.ne']

private lemma betaHalfTail_base_integrand_nonneg
    {b t x : ℝ} (_hb : 1 < b) (ht0 : 0 < t)
    (hx : x ∈ Icc t 1) :
    0 ≤ x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1) := by
  exact mul_nonneg (Real.rpow_nonneg (ht0.trans_le hx.1).le _)
    (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)

private lemma betaHalfTail_ratio_nonneg_le
    {t x : ℝ} (ht0 : 0 < t) (hx : x ∈ Icc t 1) :
    0 ≤ (1 - x) / x ∧ (1 - x) / x ≤ 1 / t := by
  have hx0 : 0 < x := ht0.trans_le hx.1
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.2) hx0.le
  · apply (div_le_div_iff₀ hx0 ht0).2
    have hsub : 1 - x ≤ 1 := by linarith
    have hmul : t * (1 - x) ≤ t * 1 :=
      mul_le_mul_of_nonneg_left hsub ht0.le
    calc
      (1 - x) * t = t * (1 - x) := mul_comm _ _
      _ ≤ t := by simpa using hmul
      _ ≤ x := hx.1
      _ = 1 * x := by ring

/-- The integration-by-parts remainder is nonnegative. -/
theorem betaHalfTailRemainder_nonneg
    {b t : ℝ} (hb : 1 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ betaHalfTailRemainder b t := by
  unfold betaHalfTailRemainder
  apply intervalIntegral.integral_nonneg ht1.le
  intro x hx
  rw [betaHalfTail_remainder_integrand_eq hb ht0 hx]
  exact mul_nonneg (betaHalfTail_ratio_nonneg_le ht0 hx).1
    (betaHalfTail_base_integrand_nonneg hb ht0 hx)

/-- The remainder is at most the beta half-tail divided by its lower
endpoint.  This is the quantitative input in the Mills lower bound. -/
theorem betaHalfTailRemainder_le_integral_div
    {b t : ℝ} (hb : 1 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    betaHalfTailRemainder b t ≤ betaHalfTailIntegral b t / t := by
  let f : ℝ → ℝ := fun x ↦
    x ^ (-(3 / 2 : ℝ)) * (1 - x) ^ b
  let g : ℝ → ℝ := fun x ↦
    (1 / t) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1))
  have ht_le : t ≤ 1 := ht1.le
  have hf : ContinuousOn f (Icc t 1) := by
    exact (continuousOn_id.rpow_const fun x hx ↦
      Or.inl (ne_of_gt (ht0.trans_le hx.1))).mul <|
        (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ ↦
          Or.inr (zero_lt_one.trans hb).le
  have hg : ContinuousOn g (Icc t 1) := by
    exact continuousOn_const.mul <|
      (continuousOn_id.rpow_const fun x hx ↦
        Or.inl (ne_of_gt (ht0.trans_le hx.1))).mul <|
          (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ ↦
            Or.inr (sub_nonneg.mpr hb.le)
  have hpoint : ∀ x ∈ Icc t 1, f x ≤ g x := by
    intro x hx
    change x ^ (-(3 / 2 : ℝ)) * (1 - x) ^ b ≤
      (1 / t) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1))
    rw [betaHalfTail_remainder_integrand_eq hb ht0 hx]
    exact mul_le_mul_of_nonneg_right
      (betaHalfTail_ratio_nonneg_le ht0 hx).2
      (betaHalfTail_base_integrand_nonneg hb ht0 hx)
  have hfint : IntervalIntegrable f volume t 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le ht_le] using hf
  have hgint : IntervalIntegrable g volume t 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le ht_le] using hg
  have hmono := intervalIntegral.integral_mono_on ( μ := volume)
    ht_le hfint hgint hpoint
  unfold f g at hmono
  rw [betaHalfTailRemainder, betaHalfTailIntegral]
  calc
    (∫ x in t..1, x ^ (-(3 / 2 : ℝ)) * (1 - x) ^ b) ≤
        ∫ x in t..1, (1 / t) *
          (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1)) := hmono
    _ = (∫ x in t..1,
          x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1)) / t := by
      rw [intervalIntegral.integral_const_mul]
      ring

/-- Two-sided endpoint/Mills comparison for the unnormalised
`Beta(1/2,b)` upper tail. -/
theorem betaHalfTailEndpoint_mills_bounds
    {b t : ℝ} (hb : 1 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    betaHalfTailEndpoint b t / (1 + 1 / (2 * b * t)) ≤
        betaHalfTailIntegral b t ∧
      betaHalfTailIntegral b t ≤ betaHalfTailEndpoint b t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hR0 := betaHalfTailRemainder_nonneg hb ht0 ht1
  have hRle := betaHalfTailRemainder_le_integral_div hb ht0 ht1
  have hid := betaHalfTailIntegral_eq_endpoint_sub_remainder hb ht0 ht1
  have hden : 0 < 1 + 1 / (2 * b * t) := by positivity
  constructor
  · apply (div_le_iff₀ hden).2
    have hRdiv : betaHalfTailRemainder b t / (2 * b) ≤
        (betaHalfTailIntegral b t / t) / (2 * b) :=
      div_le_div_of_nonneg_right hRle (by positivity)
    have hE : betaHalfTailEndpoint b t =
        betaHalfTailIntegral b t + betaHalfTailRemainder b t / (2 * b) := by
      linarith
    rw [hE]
    calc
      betaHalfTailIntegral b t + betaHalfTailRemainder b t / (2 * b) ≤
          betaHalfTailIntegral b t +
            (betaHalfTailIntegral b t / t) / (2 * b) :=
        add_le_add (le_refl _) hRdiv
      _ = betaHalfTailIntegral b t * (1 + 1 / (2 * b * t)) := by
        field_simp [ht0.ne', ne_of_gt hb0]
  · rw [hid]
    exact sub_le_self _ (div_nonneg hR0 (by positivity))

end

end LogdetLean.Coherence
