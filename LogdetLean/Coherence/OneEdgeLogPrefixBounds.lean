import LogdetLean.BetaMellin
import LogdetLean.CenteredLogBetaLaw
import LogdetLean.Coherence.BetaTailMeasure
import LogdetLean.Coherence.PairBeta
import LogdetLean.Coherence.PrefixScale
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
/-!
# Finite one-edge logarithmic-prefix bounds

This file proves the finite beta-integral estimates needed to control the
single correlation edge removed from a log-determinant statistic.  Everything
is stated directly as an integral; no regular conditional probability is
used.

For `X ~ Beta(1/2,b)`, put `Y = -log (1-X)`.  The main conclusions are

* `E |Y-EY| <= 1/(b-1)`;
* on `{X>t}`,
  `E[|Y-EY| 1_{X>t}] <= P(X>t) *
    (-log(1-t) + 3/(2*(b-1)))`.

After taking `b=(m-1)/2` and dividing by a positive scale `s`, these become
the desired `O(1/(m*s))` and event-weighted `O(q log(p)/(m*s))` bounds.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Module
open scoped ENNReal NNReal Interval Real

set_option linter.style.haveILetI false

/-- The nonnegative logarithmic loss contributed by one squared correlation. -/
def oneEdgeLogLoss (x : ℝ) : ℝ := -Real.log (1 - x)

/-- The rational majorant used for the logarithmic loss. -/
def oneEdgeRationalLoss (x : ℝ) : ℝ := x / (1 - x)

private lemma beta_add_one_sub_one_div_beta
    {alpha betaShape : ℝ} (ha : 0 < alpha) (hb : 1 < betaShape) :
    beta (alpha + 1) (betaShape - 1) / beta alpha betaShape =
      alpha / (betaShape - 1) := by
  have ha0 : alpha ≠ 0 := ha.ne'
  have hb10 : betaShape - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hb)
  have hab : 0 < alpha + betaShape := by linarith
  have hGa : Real.Gamma alpha ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGb1 : Real.Gamma (betaShape - 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (sub_pos.mpr hb)).ne'
  have hGab : Real.Gamma (alpha + betaShape) ≠ 0 :=
    (Real.Gamma_pos_of_pos hab).ne'
  have hGammaBeta : Real.Gamma betaShape =
      (betaShape - 1) * Real.Gamma (betaShape - 1) := by
    convert Real.Gamma_add_one hb10 using 1 <;> ring
  rw [beta, beta, Real.Gamma_add_one ha0]
  rw [show alpha + 1 + (betaShape - 1) = alpha + betaShape by ring]
  rw [hGammaBeta]
  field_simp [hGa, hGb1, hGab, hb10]

private lemma rationalLoss_mul_betaPDFReal
    {alpha betaShape x : ℝ} (ha : 0 < alpha) (hb : 1 < betaShape) :
    oneEdgeRationalLoss x * betaPDFReal alpha betaShape x =
      (beta (alpha + 1) (betaShape - 1) / beta alpha betaShape) *
        betaPDFReal (alpha + 1) (betaShape - 1) x := by
  rw [oneEdgeRationalLoss, betaPDFReal, betaPDFReal]
  by_cases hx : 0 < x ∧ x < 1
  · rw [if_pos hx, if_pos hx]
    have hB : beta alpha betaShape ≠ 0 :=
      (beta_pos ha (zero_lt_one.trans hb)).ne'
    have hBshift : beta (alpha + 1) (betaShape - 1) ≠ 0 :=
      (beta_pos (by linarith) (sub_pos.mpr hb)).ne'
    have hxpow : x ^ alpha = x ^ (alpha - 1) * x := by
      calc
        x ^ alpha = x ^ ((alpha - 1) + 1) := by congr 1 <;> ring
        _ = x ^ (alpha - 1) * x :=
          Real.rpow_add_one' hx.1.le (by linarith)
    have h1xpow : (1 - x) ^ (betaShape - 1) =
        (1 - x) ^ (betaShape - 2) * (1 - x) := by
      calc
        (1 - x) ^ (betaShape - 1) =
            (1 - x) ^ ((betaShape - 2) + 1) := by congr 1 <;> ring
        _ = (1 - x) ^ (betaShape - 2) * (1 - x) :=
          Real.rpow_add_one' (sub_nonneg.mpr hx.2.le) (by linarith)
    rw [show alpha + 1 - 1 = alpha by ring,
      show betaShape - 1 - 1 = betaShape - 2 by ring]
    rw [hxpow, h1xpow]
    field_simp [hB, hBshift, hx.1.ne', (sub_pos.mpr hx.2).ne']
  · rw [if_neg hx, if_neg hx]
    ring

/-- Exact beta expectation of `X/(1-X)`.  This is the elementary shifted-beta
moment that controls every logarithmic estimate below. -/
theorem integral_oneEdgeRationalLoss_betaMeasure
    {alpha betaShape : ℝ} (ha : 0 < alpha) (hb : 1 < betaShape) :
    ∫ x, oneEdgeRationalLoss x ∂betaMeasure alpha betaShape =
      alpha / (betaShape - 1) := by
  have hb0 : 0 < betaShape := zero_lt_one.trans hb
  have hshiftA : 0 < alpha + 1 := by linarith
  have hshiftB : 0 < betaShape - 1 := sub_pos.mpr hb
  rw [betaMeasure]
  change (∫ x, oneEdgeRationalLoss x ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (betaPDFReal alpha betaShape x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_betaPDFReal alpha betaShape).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal (LogdetLean.betaPDFReal_nonneg_of_pos ha hb0 _),
    mul_comm (betaPDFReal alpha betaShape _) (oneEdgeRationalLoss _),
    rationalLoss_mul_betaPDFReal ha hb]
  rw [integral_const_mul,
    LogdetLean.integral_betaPDFReal_eq_one hshiftA hshiftB, mul_one,
    beta_add_one_sub_one_div_beta ha hb]

/-- `X/(1-X)` is beta-integrable whenever the second shape is greater than
one. -/
theorem integrable_oneEdgeRationalLoss_betaMeasure
    {alpha betaShape : ℝ} (ha : 0 < alpha) (hb : 1 < betaShape) :
    Integrable oneEdgeRationalLoss (betaMeasure alpha betaShape) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_oneEdgeRationalLoss_betaMeasure ha hb]
  exact (div_pos ha (sub_pos.mpr hb)).ne'

private lemma oneEdgeLogLoss_nonneg_le_rational
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 ≤ oneEdgeLogLoss x ∧ oneEdgeLogLoss x ≤ oneEdgeRationalLoss x := by
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  constructor
  · unfold oneEdgeLogLoss
    have hlog : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  · unfold oneEdgeLogLoss oneEdgeRationalLoss
    have h := Real.one_sub_inv_le_log_of_pos h1x
    field_simp [h1x.ne'] at h ⊢
    linarith

private lemma ae_mem_Ioo_betaMeasure (alpha betaShape : ℝ) :
    ∀ᵐ x ∂betaMeasure alpha betaShape, x ∈ Ioo 0 1 := by
  rw [betaMeasure]
  refine (ae_withDensity_iff (μ := volume)
    (measurable_betaPDFReal alpha betaShape).ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hpdf
  by_contra hx
  apply hpdf
  have hzero : betaPDFReal alpha betaShape x = 0 := by
    rw [betaPDFReal, if_neg]
    exact hx
  rw [hzero, ENNReal.ofReal_zero]

/-- The one-edge logarithmic loss is beta-integrable. -/
theorem integrable_oneEdgeLogLoss_betaMeasure
    {alpha betaShape : ℝ} (ha : 0 < alpha) (hb : 1 < betaShape) :
    Integrable oneEdgeLogLoss (betaMeasure alpha betaShape) := by
  apply (integrable_oneEdgeRationalLoss_betaMeasure ha hb).mono'
    ((Real.measurable_log.comp
      (measurable_const.sub measurable_id)).neg.aestronglyMeasurable)
  filter_upwards [ae_mem_Ioo_betaMeasure alpha betaShape] with x hx
  change |oneEdgeLogLoss x| ≤ oneEdgeRationalLoss x
  rw [abs_of_nonneg
    (oneEdgeLogLoss_nonneg_le_rational hx.1 hx.2).1]
  exact (oneEdgeLogLoss_nonneg_le_rational hx.1 hx.2).2

/-- The mean logarithmic loss is nonnegative and bounded by the shifted-beta
rational moment. -/
theorem integral_oneEdgeLogLoss_betaMeasure_bounds
    {alpha betaShape : ℝ} (ha : 0 < alpha) (hb : 1 < betaShape) :
    0 ≤ ∫ x, oneEdgeLogLoss x ∂betaMeasure alpha betaShape ∧
      (∫ x, oneEdgeLogLoss x ∂betaMeasure alpha betaShape) ≤
        alpha / (betaShape - 1) := by
  have hlog := integrable_oneEdgeLogLoss_betaMeasure ha hb
  have hrat := integrable_oneEdgeRationalLoss_betaMeasure ha hb
  have hae := ae_mem_Ioo_betaMeasure alpha betaShape
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hae] with x hx
    exact (oneEdgeLogLoss_nonneg_le_rational hx.1 hx.2).1
  · calc
      (∫ x, oneEdgeLogLoss x ∂betaMeasure alpha betaShape) ≤
          ∫ x, oneEdgeRationalLoss x ∂betaMeasure alpha betaShape := by
        apply integral_mono_ae hlog hrat
        filter_upwards [hae] with x hx
        exact (oneEdgeLogLoss_nonneg_le_rational hx.1 hx.2).2
      _ = alpha / (betaShape - 1) :=
        integral_oneEdgeRationalLoss_betaMeasure ha hb

/-- Mean logarithmic contribution of one squared-correlation beta factor. -/
def oneEdgeLogMean (alpha betaShape : ℝ) : ℝ :=
  ∫ x, oneEdgeLogLoss x ∂betaMeasure alpha betaShape

/-- Centered one-edge logarithmic prefix, divided by an arbitrary positive
normalizing scale. -/
def oneEdgeCenteredPrefix (alpha betaShape scale x : ℝ) : ℝ :=
  (oneEdgeLogMean alpha betaShape - oneEdgeLogLoss x) / scale

/-- Measurability of the centered one-edge prefix. -/
theorem measurable_oneEdgeCenteredPrefix (alpha betaShape scale : ℝ) :
    Measurable (oneEdgeCenteredPrefix alpha betaShape scale) := by
  unfold oneEdgeCenteredPrefix oneEdgeLogLoss
  exact (measurable_const.sub
    ((Real.measurable_log.comp
      (measurable_const.sub measurable_id)).neg)).div measurable_const

/-- Absolute first centered moment of the logarithmic loss. -/
theorem integral_abs_oneEdgeLogLoss_sub_mean_le
    {alpha betaShape : ℝ} (ha : 0 < alpha) (hb : 1 < betaShape) :
    (∫ x, |oneEdgeLogLoss x - oneEdgeLogMean alpha betaShape|
        ∂betaMeasure alpha betaShape) ≤
      2 * alpha / (betaShape - 1) := by
  letI : IsProbabilityMeasure (betaMeasure alpha betaShape) :=
    isProbabilityMeasureBeta ha (zero_lt_one.trans hb)
  have hlog := integrable_oneEdgeLogLoss_betaMeasure ha hb
  have hmeanBounds := integral_oneEdgeLogLoss_betaMeasure_bounds ha hb
  have hmean0 : 0 ≤ oneEdgeLogMean alpha betaShape := by
    exact hmeanBounds.1
  have hconst : Integrable (fun _x : ℝ ↦ oneEdgeLogMean alpha betaShape)
      (betaMeasure alpha betaShape) := integrable_const _
  have habs : Integrable
      (fun x ↦ |oneEdgeLogLoss x - oneEdgeLogMean alpha betaShape|)
      (betaMeasure alpha betaShape) := (hlog.sub hconst).abs
  calc
    (∫ x, |oneEdgeLogLoss x - oneEdgeLogMean alpha betaShape|
        ∂betaMeasure alpha betaShape) ≤
        ∫ x, oneEdgeLogLoss x + oneEdgeLogMean alpha betaShape
          ∂betaMeasure alpha betaShape := by
      apply integral_mono_ae habs (hlog.add hconst)
      filter_upwards [ae_mem_Ioo_betaMeasure alpha betaShape] with x hx
      calc
        |oneEdgeLogLoss x - oneEdgeLogMean alpha betaShape| ≤
            |oneEdgeLogLoss x| + |oneEdgeLogMean alpha betaShape| :=
          abs_sub _ _
        _ = oneEdgeLogLoss x + oneEdgeLogMean alpha betaShape := by
          rw [abs_of_nonneg
            (oneEdgeLogLoss_nonneg_le_rational hx.1 hx.2).1,
            abs_of_nonneg hmean0]
    _ = 2 * oneEdgeLogMean alpha betaShape := by
      rw [integral_add hlog hconst]
      simp [oneEdgeLogMean]
      ring
    _ ≤ 2 * (alpha / (betaShape - 1)) := by
      gcongr
      exact hmeanBounds.2
    _ = 2 * alpha / (betaShape - 1) := by ring

/-- Unconditional finite bound for the standardized one-edge prefix. -/
theorem integral_abs_oneEdgeCenteredPrefix_le
    {alpha betaShape scale : ℝ}
    (ha : 0 < alpha) (hb : 1 < betaShape) (hs : 0 < scale) :
    (∫ x, |oneEdgeCenteredPrefix alpha betaShape scale x|
        ∂betaMeasure alpha betaShape) ≤
      (2 * alpha / (betaShape - 1)) / scale := by
  have hbase := integral_abs_oneEdgeLogLoss_sub_mean_le ha hb
  calc
    (∫ x, |oneEdgeCenteredPrefix alpha betaShape scale x|
        ∂betaMeasure alpha betaShape) =
        (1 / scale) *
          ∫ x, |oneEdgeLogLoss x - oneEdgeLogMean alpha betaShape|
            ∂betaMeasure alpha betaShape := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      unfold oneEdgeCenteredPrefix
      rw [abs_div, abs_of_pos hs, abs_sub_comm]
      ring
    _ ≤ (1 / scale) * (2 * alpha / (betaShape - 1)) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (2 * alpha / (betaShape - 1)) / scale := by ring

/-- Unnormalised beta integral of the rational overshoot above `t`. -/
def betaHalfRationalOvershootIntegral (betaShape t : ℝ) : ℝ :=
  ∫ x in t..1,
    (x - t) * x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (betaShape - 2)

private lemma hasDerivAt_mul_rpow_neg_half_sub
    {t x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ ↦ (y - t) * y ^ (-(1 / 2 : ℝ)))
      (x ^ (-(1 / 2 : ℝ)) -
        (1 / 2 : ℝ) * (x - t) * x ^ (-(3 / 2 : ℝ))) x := by
  have hpow : HasDerivAt (fun y : ℝ ↦ y ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) x := by
    simpa only [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num] using
      (Real.hasDerivAt_rpow_const (x := x) (p := -(1 / 2 : ℝ))
        (Or.inl hx.ne'))
  have hlin : HasDerivAt (fun y : ℝ ↦ y - t) 1 x := by
    simpa using (hasDerivAt_id x).sub_const t
  apply (hlin.mul hpow).congr_deriv
  ring

private lemma hasDerivAt_one_sub_rpow_sub_one
    {betaShape x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ ↦ (1 - y) ^ (betaShape - 1))
      (-(betaShape - 1) * (1 - x) ^ (betaShape - 2)) x := by
  have hbase : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
  convert hbase.rpow_const (p := betaShape - 1)
      (Or.inl (sub_ne_zero.mpr hx.ne.symm)) using 1 <;> ring

/-- Exact integration-by-parts identity for the rational overshoot integral. -/
theorem betaHalfRationalOvershootIntegral_eq
    {betaShape t : ℝ} (hb : 2 < betaShape) (ht0 : 0 < t) (ht1 : t < 1) :
    betaHalfRationalOvershootIntegral betaShape t =
      (1 / (betaShape - 1)) *
        ∫ x in t..1,
          (x ^ (-(1 / 2 : ℝ)) -
              (1 / 2 : ℝ) * (x - t) * x ^ (-(3 / 2 : ℝ))) *
            (1 - x) ^ (betaShape - 1) := by
  let u : ℝ → ℝ := fun x ↦ (x - t) * x ^ (-(1 / 2 : ℝ))
  let u' : ℝ → ℝ := fun x ↦
    x ^ (-(1 / 2 : ℝ)) -
      (1 / 2 : ℝ) * (x - t) * x ^ (-(3 / 2 : ℝ))
  let v : ℝ → ℝ := fun x ↦ (1 - x) ^ (betaShape - 1)
  let v' : ℝ → ℝ := fun x ↦
    -(betaShape - 1) * (1 - x) ^ (betaShape - 2)
  have ht_le : t ≤ 1 := ht1.le
  have hu : ContinuousOn u [[t, 1]] := by
    rw [uIcc_of_le ht_le]
    exact (continuousOn_id.sub continuousOn_const).mul
      (continuousOn_id.rpow_const fun x hx ↦
        Or.inl (ne_of_gt (ht0.trans_le hx.1)))
  have hu' : ContinuousOn u' [[t, 1]] := by
    rw [uIcc_of_le ht_le]
    exact (continuousOn_id.rpow_const fun x hx ↦
      Or.inl (ne_of_gt (ht0.trans_le hx.1))).sub <|
        ((continuousOn_const.mul
          (continuousOn_id.sub continuousOn_const)).mul
            (continuousOn_id.rpow_const fun x hx ↦
              Or.inl (ne_of_gt (ht0.trans_le hx.1))))
  have hv : ContinuousOn v [[t, 1]] := by
    rw [uIcc_of_le ht_le]
    exact (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ ↦
      Or.inr (by linarith : 0 ≤ betaShape - 1)
  have hv' : ContinuousOn v' [[t, 1]] := by
    rw [uIcc_of_le ht_le]
    exact continuousOn_const.mul <|
      (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ ↦
        Or.inr (by linarith : 0 ≤ betaShape - 2)
  have hdu : ∀ x ∈ Ioo (min t 1) (max t 1), HasDerivAt u (u' x) x := by
    intro x hx
    rw [min_eq_left ht_le, max_eq_right ht_le] at hx
    exact hasDerivAt_mul_rpow_neg_half_sub (ht0.trans hx.1)
  have hdv : ∀ x ∈ Ioo (min t 1) (max t 1), HasDerivAt v (v' x) x := by
    intro x hx
    rw [min_eq_left ht_le, max_eq_right ht_le] at hx
    exact hasDerivAt_one_sub_rpow_sub_one hx.2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu hv hdu hdv hu'.intervalIntegrable hv'.intervalIntegrable
  change (∫ x in t..1, u x * v' x) =
      u 1 * v 1 - u t * v t - ∫ x in t..1, u' x * v x at hibp
  have hleft : (∫ x in t..1, u x * v' x) =
      -(betaShape - 1) * betaHalfRationalOvershootIntegral betaShape t := by
    rw [betaHalfRationalOvershootIntegral]
    simp only [u, v']
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hleft] at hibp
  have hb10 : betaShape - 1 ≠ 0 := by linarith
  norm_num [u, v, Real.zero_rpow hb10] at hibp
  simp only [u'] at hibp
  rw [one_div_mul_eq_div]
  apply (eq_div_iff hb10).2
  linarith

/-- The rational overshoot integral is at most the original beta tail divided
by `betaShape-1`. -/
theorem betaHalfRationalOvershootIntegral_le
    {betaShape t : ℝ} (hb : 2 < betaShape) (ht0 : 0 < t) (ht1 : t < 1) :
    betaHalfRationalOvershootIntegral betaShape t ≤
      betaHalfTailIntegral betaShape t / (betaShape - 1) := by
  let f : ℝ → ℝ := fun x ↦
    (x ^ (-(1 / 2 : ℝ)) -
        (1 / 2 : ℝ) * (x - t) * x ^ (-(3 / 2 : ℝ))) *
      (1 - x) ^ (betaShape - 1)
  let g : ℝ → ℝ := fun x ↦
    x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (betaShape - 1)
  have ht_le : t ≤ 1 := ht1.le
  have hf : ContinuousOn f (Icc t 1) := by
    exact ((continuousOn_id.rpow_const fun x hx ↦
      Or.inl (ne_of_gt (ht0.trans_le hx.1))).sub <|
        ((continuousOn_const.mul
          (continuousOn_id.sub continuousOn_const)).mul
            (continuousOn_id.rpow_const fun x hx ↦
              Or.inl (ne_of_gt (ht0.trans_le hx.1))))).mul <|
      (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ ↦
        Or.inr (by linarith : 0 ≤ betaShape - 1)
  have hg : ContinuousOn g (Icc t 1) := by
    exact (continuousOn_id.rpow_const fun x hx ↦
      Or.inl (ne_of_gt (ht0.trans_le hx.1))).mul <|
        (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ ↦
          Or.inr (by linarith : 0 ≤ betaShape - 1)
  have hpoint : ∀ x ∈ Icc t 1, f x ≤ g x := by
    intro x hx
    have hx0 : 0 < x := ht0.trans_le hx.1
    have hxt : 0 ≤ x - t := sub_nonneg.mpr hx.1
    have hpow : 0 ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hbase : 0 ≤ (1 - x) ^ (betaShape - 1) :=
      Real.rpow_nonneg (sub_nonneg.mpr hx.2) _
    dsimp [f, g]
    apply mul_le_mul_of_nonneg_right _ hbase
    nlinarith
  have hfint : IntervalIntegrable f volume t 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le ht_le] using hf
  have hgint : IntervalIntegrable g volume t 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le ht_le] using hg
  have hmono := intervalIntegral.integral_mono_on ( μ := volume)
    ht_le hfint hgint hpoint
  rw [betaHalfRationalOvershootIntegral_eq hb ht0 ht1]
  unfold f g at hmono
  rw [betaHalfTailIntegral]
  have hb1 : 0 < betaShape - 1 := by linarith
  calc
    (1 / (betaShape - 1)) *
        (∫ x in t..1,
          (x ^ (-(1 / 2 : ℝ)) -
              (1 / 2 : ℝ) * (x - t) * x ^ (-(3 / 2 : ℝ))) *
            (1 - x) ^ (betaShape - 1)) ≤
        (1 / (betaShape - 1)) *
          (∫ x in t..1,
            x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (betaShape - 1)) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (∫ x in t..1,
          x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (betaShape - 1)) /
        (betaShape - 1) := by ring

/-- Rational excess above a fixed threshold. -/
def oneEdgeRationalOvershoot (t x : ℝ) : ℝ :=
  (x - t) / (1 - x)

private lemma betaPDFReal_half_mul_overshoot_eq
    {betaShape t x : ℝ} (hb : 2 < betaShape)
    (hx0 : 0 < x) (hx1 : x < 1) :
    betaPDFReal (1 / 2) betaShape x * oneEdgeRationalOvershoot t x =
      (1 / beta (1 / 2) betaShape) *
        ((x - t) * x ^ (-(1 / 2 : ℝ)) *
          (1 - x) ^ (betaShape - 2)) := by
  have hbeta : beta (1 / 2) betaShape ≠ 0 :=
    (beta_pos (by norm_num) (by linarith)).ne'
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  have hpow : (1 - x) ^ (betaShape - 1) =
      (1 - x) ^ (betaShape - 2) * (1 - x) := by
    calc
      (1 - x) ^ (betaShape - 1) =
          (1 - x) ^ ((betaShape - 2) + 1) := by congr 1 <;> ring
      _ = (1 - x) ^ (betaShape - 2) * (1 - x) :=
        Real.rpow_add_one' h1x.le (by linarith)
  rw [betaPDFReal, if_pos ⟨hx0, hx1⟩]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
  unfold oneEdgeRationalOvershoot
  rw [hpow]
  field_simp [hbeta, h1x.ne']

/-- Exact beta-measure transport of the rational overshoot integral. -/
theorem setIntegral_oneEdgeRationalOvershoot_betaMeasure_eq
    {betaShape t : ℝ} (hb : 2 < betaShape) (ht0 : 0 < t) (ht1 : t < 1) :
    (∫ x in Ioi t, oneEdgeRationalOvershoot t x
        ∂betaMeasure (1 / 2) betaShape) =
      (1 / beta (1 / 2) betaShape) *
        betaHalfRationalOvershootIntegral betaShape t := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hb0 : 0 < betaShape := by linarith
  calc
    (∫ x in Ioi t, oneEdgeRationalOvershoot t x
        ∂betaMeasure (1 / 2) betaShape) =
        ∫ x in Ioi t,
          betaPDFReal (1 / 2) betaShape x * oneEdgeRationalOvershoot t x
            ∂volume := by
      rw [betaMeasure]
      change (∫ x in Ioi t, oneEdgeRationalOvershoot t x
        ∂volume.withDensity
          (fun x ↦ ENNReal.ofReal (betaPDFReal (1 / 2) betaShape x))) = _
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
          (measurable_betaPDFReal (1 / 2) betaShape).ennreal_ofReal
          (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) _ measurableSet_Ioi]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      change (ENNReal.ofReal (betaPDFReal (1 / 2) betaShape x)).toReal *
          oneEdgeRationalOvershoot t x = _
      rw [ENNReal.toReal_ofReal
        (LogdetLean.betaPDFReal_nonneg_of_pos hhalf hb0 x)]
    _ = ∫ x in Ioo t 1,
          betaPDFReal (1 / 2) betaShape x * oneEdgeRationalOvershoot t x
            ∂volume := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      · exact fun x hx ↦ hx.1
      · intro x hx
        have hxge : 1 ≤ x := by
          by_contra hnot
          exact hx.2 ⟨hx.1, lt_of_not_ge hnot⟩
        have hpdf : betaPDFReal (1 / 2) betaShape x = 0 := by
          rw [betaPDFReal, if_neg]
          exact fun hsupp ↦ (not_lt_of_ge hxge) hsupp.2
        rw [hpdf, zero_mul]
    _ = ∫ x in Ioo t 1,
          (1 / beta (1 / 2) betaShape) *
            ((x - t) * x ^ (-(1 / 2 : ℝ)) *
              (1 - x) ^ (betaShape - 2)) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact betaPDFReal_half_mul_overshoot_eq hb (ht0.trans hx.1) hx.2
    _ = (1 / beta (1 / 2) betaShape) *
        ∫ x in Ioo t 1,
          (x - t) * x ^ (-(1 / 2 : ℝ)) *
            (1 - x) ^ (betaShape - 2) ∂volume := by
      rw [integral_const_mul]
    _ = (1 / beta (1 / 2) betaShape) *
        betaHalfRationalOvershootIntegral betaShape t := by
      unfold betaHalfRationalOvershootIntegral
      rw [intervalIntegral.integral_of_le ht1.le]
      congr 1
      exact setIntegral_congr_set Ioo_ae_eq_Ioc

/-- Finite conditional-mean inequality written without conditional
probability: the event-weighted rational overshoot is at most the event
probability divided by `betaShape-1`. -/
theorem setIntegral_oneEdgeRationalOvershoot_betaMeasure_le
    {betaShape t : ℝ} (hb : 2 < betaShape) (ht0 : 0 < t) (ht1 : t < 1) :
    (∫ x in Ioi t, oneEdgeRationalOvershoot t x
        ∂betaMeasure (1 / 2) betaShape) ≤
      (betaMeasure (1 / 2) betaShape).real (Ioi t) /
        (betaShape - 1) := by
  have hbeta : 0 < beta (1 / 2) betaShape :=
    beta_pos (by norm_num) (by linarith)
  have hJ := betaHalfRationalOvershootIntegral_le hb ht0 ht1
  rw [setIntegral_oneEdgeRationalOvershoot_betaMeasure_eq hb ht0 ht1,
    betaMeasure_half_Ioi_real_eq_tailIntegral (by linarith) ht0 ht1]
  calc
    (1 / beta (1 / 2) betaShape) *
        betaHalfRationalOvershootIntegral betaShape t ≤
      (1 / beta (1 / 2) betaShape) *
        (betaHalfTailIntegral betaShape t / (betaShape - 1)) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = ((1 / beta (1 / 2) betaShape) *
        betaHalfTailIntegral betaShape t) / (betaShape - 1) := by ring

private lemma oneEdgeRationalOvershoot_nonneg_le
    {t x : ℝ} (ht0 : 0 < t) (htx : t < x) (hx1 : x < 1) :
    0 ≤ oneEdgeRationalOvershoot t x ∧
      oneEdgeRationalOvershoot t x ≤ oneEdgeRationalLoss x := by
  have hden : 0 < 1 - x := sub_pos.mpr hx1
  constructor
  · exact div_nonneg (sub_nonneg.mpr htx.le) hden.le
  · unfold oneEdgeRationalOvershoot oneEdgeRationalLoss
    exact (div_le_div_iff₀ hden hden).2 (by nlinarith [ht0])

private theorem integrableOn_oneEdgeRationalOvershoot_betaMeasure
    {betaShape t : ℝ} (hb : 2 < betaShape) (ht0 : 0 < t) :
    IntegrableOn (oneEdgeRationalOvershoot t) (Ioi t)
      (betaMeasure (1 / 2) betaShape) := by
  have hrat := integrable_oneEdgeRationalLoss_betaMeasure
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 1 < betaShape)
  apply hrat.integrableOn.mono'
    (((measurable_id.sub measurable_const).div
      (measurable_const.sub measurable_id)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (ae_mem_Ioo_betaMeasure (1 / 2) betaShape)] with x hxt hx
  change |oneEdgeRationalOvershoot t x| ≤ oneEdgeRationalLoss x
  rw [abs_of_nonneg
    (oneEdgeRationalOvershoot_nonneg_le ht0 hxt hx.2).1]
  exact (oneEdgeRationalOvershoot_nonneg_le ht0 hxt hx.2).2

private lemma oneEdgeLogLoss_le_threshold_add_overshoot
    {t x : ℝ} (ht0 : 0 < t) (htx : t < x) (hx1 : x < 1) :
    oneEdgeLogLoss x ≤
      oneEdgeLogLoss t + oneEdgeRationalOvershoot t x := by
  have ht1 : t < 1 := htx.trans hx1
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  have hlog := Real.log_le_sub_one_of_pos (div_pos h1t h1x)
  rw [Real.log_div h1t.ne' h1x.ne'] at hlog
  have hratio : (1 - t) / (1 - x) - 1 = (x - t) / (1 - x) := by
    field_simp [h1x.ne']
    ring
  rw [hratio] at hlog
  unfold oneEdgeLogLoss oneEdgeRationalOvershoot
  linarith

/-- Event-weighted first moment of the logarithmic loss.  The right side is
the tail probability times the threshold loss plus one inverse beta shape. -/
theorem setIntegral_oneEdgeLogLoss_betaMeasure_le
    {betaShape t : ℝ} (hb : 2 < betaShape) (ht0 : 0 < t) (ht1 : t < 1) :
    (∫ x in Ioi t, oneEdgeLogLoss x
        ∂betaMeasure (1 / 2) betaShape) ≤
      (betaMeasure (1 / 2) betaShape).real (Ioi t) *
        (oneEdgeLogLoss t + 1 / (betaShape - 1)) := by
  let mu := betaMeasure (1 / 2) betaShape
  letI : IsProbabilityMeasure mu :=
    isProbabilityMeasureBeta (by norm_num) (by linarith)
  have hlog : Integrable oneEdgeLogLoss mu :=
    integrable_oneEdgeLogLoss_betaMeasure (by norm_num) (by linarith)
  have hover : IntegrableOn (oneEdgeRationalOvershoot t) (Ioi t) mu :=
    integrableOn_oneEdgeRationalOvershoot_betaMeasure hb ht0
  have hconst : IntegrableOn (fun _x : ℝ ↦ oneEdgeLogLoss t) (Ioi t) mu :=
    integrableOn_const
  have hmono :
      (∫ x in Ioi t, oneEdgeLogLoss x ∂mu) ≤
        ∫ x in Ioi t,
          oneEdgeLogLoss t + oneEdgeRationalOvershoot t x ∂mu := by
    apply integral_mono_ae hlog.integrableOn (hconst.add hover)
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (ae_mem_Ioo_betaMeasure (1 / 2) betaShape)] with x hxt hx
    exact oneEdgeLogLoss_le_threshold_add_overshoot ht0 hxt hx.2
  have hoverBound := setIntegral_oneEdgeRationalOvershoot_betaMeasure_le
    hb ht0 ht1
  have hoverBound' :
      (∫ x in Ioi t, oneEdgeRationalOvershoot t x ∂mu) ≤
        mu.real (Ioi t) / (betaShape - 1) := by
    simpa [mu] using hoverBound
  calc
    (∫ x in Ioi t, oneEdgeLogLoss x ∂mu) ≤
        ∫ x in Ioi t,
          oneEdgeLogLoss t + oneEdgeRationalOvershoot t x ∂mu := hmono
    _ = mu.real (Ioi t) * oneEdgeLogLoss t +
        ∫ x in Ioi t, oneEdgeRationalOvershoot t x ∂mu := by
      rw [integral_add hconst hover, setIntegral_const]
      simp only [smul_eq_mul]
    _ ≤ mu.real (Ioi t) * oneEdgeLogLoss t +
        mu.real (Ioi t) / (betaShape - 1) :=
      add_le_add (le_refl _) hoverBound'
    _ = mu.real (Ioi t) *
        (oneEdgeLogLoss t + 1 / (betaShape - 1)) := by ring

/-- Event-weighted absolute centered logarithmic prefix under the
`Beta(1/2,betaShape)` law. -/
theorem setIntegral_abs_oneEdgeLogLoss_sub_mean_betaMeasure_le
    {betaShape t : ℝ} (hb : 2 < betaShape) (ht0 : 0 < t) (ht1 : t < 1) :
    (∫ x in Ioi t,
        |oneEdgeLogLoss x - oneEdgeLogMean (1 / 2) betaShape|
          ∂betaMeasure (1 / 2) betaShape) ≤
      (betaMeasure (1 / 2) betaShape).real (Ioi t) *
        (oneEdgeLogLoss t + 3 / (2 * (betaShape - 1))) := by
  let mu := betaMeasure (1 / 2) betaShape
  let mean := oneEdgeLogMean (1 / 2) betaShape
  let q := mu.real (Ioi t)
  letI : IsProbabilityMeasure mu :=
    isProbabilityMeasureBeta (by norm_num) (by linarith)
  have hlog : Integrable oneEdgeLogLoss mu := by
    simpa [mu] using integrable_oneEdgeLogLoss_betaMeasure
      (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 1 < betaShape)
  have hmeanBounds := integral_oneEdgeLogLoss_betaMeasure_bounds
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 1 < betaShape)
  have hmean0 : 0 ≤ mean := hmeanBounds.1
  have hmeanLe : mean ≤ 1 / (2 * (betaShape - 1)) := by
    dsimp [mean]
    calc
      oneEdgeLogMean (1 / 2) betaShape ≤
          (1 / 2 : ℝ) / (betaShape - 1) := hmeanBounds.2
      _ = 1 / (2 * (betaShape - 1)) := by
        field_simp [show betaShape - 1 ≠ 0 by linarith]
  have hconst : IntegrableOn (fun _x : ℝ ↦ mean) (Ioi t) mu :=
    integrableOn_const
  have habs : IntegrableOn
      (fun x ↦ |oneEdgeLogLoss x - mean|) (Ioi t) mu :=
    (hlog.sub (integrable_const mean)).abs.integrableOn
  have hpoint : ∀ᵐ x ∂mu.restrict (Ioi t),
      |oneEdgeLogLoss x - mean| ≤ oneEdgeLogLoss x + mean := by
    filter_upwards [ae_restrict_of_ae
      (ae_mem_Ioo_betaMeasure (1 / 2) betaShape)] with x hx
    calc
      |oneEdgeLogLoss x - mean| ≤ |oneEdgeLogLoss x| + |mean| :=
        abs_sub _ _
      _ = oneEdgeLogLoss x + mean := by
        rw [abs_of_nonneg
          (oneEdgeLogLoss_nonneg_le_rational hx.1 hx.2).1,
          abs_of_nonneg hmean0]
  have hcenter :
      (∫ x in Ioi t, |oneEdgeLogLoss x - mean| ∂mu) ≤
        (∫ x in Ioi t, oneEdgeLogLoss x ∂mu) + q * mean := by
    calc
      (∫ x in Ioi t, |oneEdgeLogLoss x - mean| ∂mu) ≤
          ∫ x in Ioi t, oneEdgeLogLoss x + mean ∂mu := by
        apply integral_mono_ae habs (hlog.integrableOn.add hconst) hpoint
      _ = (∫ x in Ioi t, oneEdgeLogLoss x ∂mu) + q * mean := by
        rw [integral_add hlog.integrableOn hconst, setIntegral_const]
        simp only [smul_eq_mul]
        rfl
  have htail :
      (∫ x in Ioi t, oneEdgeLogLoss x ∂mu) ≤
        q * (oneEdgeLogLoss t + 1 / (betaShape - 1)) := by
    simpa [mu, q] using setIntegral_oneEdgeLogLoss_betaMeasure_le hb ht0 ht1
  have hq0 : 0 ≤ q := measureReal_nonneg
  calc
    (∫ x in Ioi t, |oneEdgeLogLoss x - mean| ∂mu) ≤
        (∫ x in Ioi t, oneEdgeLogLoss x ∂mu) + q * mean := hcenter
    _ ≤ q * (oneEdgeLogLoss t + 1 / (betaShape - 1)) + q * mean :=
      add_le_add htail (le_refl _)
    _ ≤ q * (oneEdgeLogLoss t + 1 / (betaShape - 1)) +
        q * (1 / (2 * (betaShape - 1))) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hmeanLe hq0)
    _ = q * (oneEdgeLogLoss t + 3 / (2 * (betaShape - 1))) := by
      field_simp [show betaShape - 1 ≠ 0 by linarith]
      ring

/-- Standardized event-weighted one-edge prefix bound. -/
theorem setIntegral_abs_oneEdgeCenteredPrefix_betaMeasure_le
    {betaShape t scale : ℝ}
    (hb : 2 < betaShape) (ht0 : 0 < t) (ht1 : t < 1) (hs : 0 < scale) :
    (∫ x in Ioi t,
        |oneEdgeCenteredPrefix (1 / 2) betaShape scale x|
          ∂betaMeasure (1 / 2) betaShape) ≤
      (betaMeasure (1 / 2) betaShape).real (Ioi t) *
        (oneEdgeLogLoss t + 3 / (2 * (betaShape - 1))) / scale := by
  have hbase := setIntegral_abs_oneEdgeLogLoss_sub_mean_betaMeasure_le
    hb ht0 ht1
  calc
    (∫ x in Ioi t,
        |oneEdgeCenteredPrefix (1 / 2) betaShape scale x|
          ∂betaMeasure (1 / 2) betaShape) =
        (1 / scale) *
          ∫ x in Ioi t,
            |oneEdgeLogLoss x - oneEdgeLogMean (1 / 2) betaShape|
              ∂betaMeasure (1 / 2) betaShape := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      unfold oneEdgeCenteredPrefix
      rw [abs_div, abs_of_pos hs, abs_sub_comm]
      ring
    _ ≤ (1 / scale) *
        ((betaMeasure (1 / 2) betaShape).real (Ioi t) *
          (oneEdgeLogLoss t + 3 / (2 * (betaShape - 1)))) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (betaMeasure (1 / 2) betaShape).real (Ioi t) *
        (oneEdgeLogLoss t + 3 / (2 * (betaShape - 1))) / scale := by ring

/-- In dimension `m`, the unconditional one-edge prefix is bounded by
`4/(m*scale)`.  The harmless constant four makes the estimate uniform over
all `m >= 6`. -/
theorem integral_abs_oneEdgeCenteredPrefix_half_sub_half_le
    {m : ℕ} (hm : 6 ≤ m) {scale : ℝ} (hs : 0 < scale) :
    (∫ x,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale x|
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) ≤
      4 / ((m : ℝ) * scale) := by
  have hm1 : 1 ≤ m := by omega
  have hmR : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hm3 : 0 < (m : ℝ) - 3 := by linarith
  have hb : 1 < (((m - 1 : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_sub hm1, Nat.cast_one]
    linarith
  have hbase := integral_abs_oneEdgeCenteredPrefix_le
    (alpha := (1 / 2 : ℝ)) (betaShape := (((m - 1 : ℕ) : ℝ) / 2))
    (scale := scale) (by norm_num) hb hs
  calc
    (∫ x,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale x|
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) ≤
        (2 * (1 / 2 : ℝ) /
          ((((m - 1 : ℕ) : ℝ) / 2) - 1)) / scale := hbase
    _ = 2 / (((m : ℝ) - 3) * scale) := by
      rw [Nat.cast_sub hm1, Nat.cast_one]
      have hden : (((m : ℝ) - 1) / 2) - 1 =
          ((m : ℝ) - 3) / 2 := by ring
      rw [hden]
      field_simp [hm3.ne', hs.ne']
    _ ≤ 4 / ((m : ℝ) * scale) := by
      apply (div_le_div_iff₀ (mul_pos hm3 hs) (mul_pos hm0 hs)).2
      nlinarith [hs]

/-- Dimension-specialized event-weighted finite bound. -/
theorem setIntegral_abs_oneEdgeCenteredPrefix_half_sub_half_le
    {m : ℕ} (hm : 6 ≤ m) {t scale : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hs : 0 < scale) :
    (∫ x in Ioi t,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale x|
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (oneEdgeLogLoss t + 3 / ((m : ℝ) - 3)) / scale := by
  have hm1 : 1 ≤ m := by omega
  have hmR : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hb : 2 < (((m - 1 : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_sub hm1, Nat.cast_one]
    linarith
  have hm3 : (m : ℝ) - 3 ≠ 0 := by linarith
  have hm3' : -3 + (m : ℝ) ≠ 0 := by linarith
  have hbase := setIntegral_abs_oneEdgeCenteredPrefix_betaMeasure_le
    (betaShape := (((m - 1 : ℕ) : ℝ) / 2))
    (t := t) (scale := scale) hb ht0 ht1 hs
  calc
    (∫ x in Ioi t,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale x|
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (oneEdgeLogLoss t +
          3 / (2 * ((((m - 1 : ℕ) : ℝ) / 2) - 1))) / scale := hbase
    _ = (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (oneEdgeLogLoss t + 3 / ((m : ℝ) - 3)) / scale := by
      rw [Nat.cast_sub hm1, Nat.cast_one]
      have hden : 2 * ((((m : ℝ) - 1) / 2) - 1) =
          (m : ℝ) - 3 := by ring
      rw [hden]

private lemma oneEdgeLogLoss_le_two_mul
    {t : ℝ} (ht0 : 0 < t) (htHalf : t ≤ 1 / 2) :
    oneEdgeLogLoss t ≤ 2 * t := by
  have ht1 : t < 1 := lt_of_le_of_lt htHalf (by norm_num)
  have hrat := (oneEdgeLogLoss_nonneg_le_rational ht0 ht1).2
  calc
    oneEdgeLogLoss t ≤ oneEdgeRationalLoss t := hrat
    _ ≤ 2 * t := by
      unfold oneEdgeRationalLoss
      have hden : 0 < 1 - t := sub_pos.mpr ht1
      apply (div_le_iff₀ hden).2
      nlinarith

/-- A clean `16 log(p)/(m*scale)`-type event-weighted bound.  The parameter
`ell` is intended to be `log p`; the displayed finite hypotheses are exactly
what a later eventual-in-`p` adapter must discharge. -/
theorem setIntegral_abs_oneEdgeCenteredPrefix_half_sub_half_le_log_rate
    {m : ℕ} (hm : 6 ≤ m) {t scale ell : ℝ}
    (ht0 : 0 < t) (htHalf : t ≤ 1 / 2) (hs : 0 < scale)
    (hell : 1 ≤ ell) (htRate : t ≤ 5 * ell / (m : ℝ)) :
    (∫ x in Ioi t,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale x|
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (16 * ell / ((m : ℝ) * scale)) := by
  have hmR : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hm3 : 0 < (m : ℝ) - 3 := by linarith
  have hsden : 0 < (m : ℝ) * scale := mul_pos hm0 hs
  have hlog := oneEdgeLogLoss_le_two_mul ht0 htHalf
  have hbracket :
      oneEdgeLogLoss t + 3 / ((m : ℝ) - 3) ≤
        16 * ell / (m : ℝ) := by
    have hthree : 3 / ((m : ℝ) - 3) ≤ 6 / (m : ℝ) := by
      apply (div_le_div_iff₀ hm3 hm0).2
      nlinarith
    have hsix : 6 / (m : ℝ) ≤ 6 * ell / (m : ℝ) := by
      apply (div_le_div_iff₀ hm0 hm0).2
      nlinarith
    calc
      oneEdgeLogLoss t + 3 / ((m : ℝ) - 3) ≤
          2 * t + 3 / ((m : ℝ) - 3) := add_le_add_left hlog _
      _ ≤ 2 * (5 * ell / (m : ℝ)) + 6 / (m : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left htRate (by norm_num)) hthree
      _ ≤ 2 * (5 * ell / (m : ℝ)) + 6 * ell / (m : ℝ) :=
        add_le_add (le_refl _) hsix
      _ = 16 * ell / (m : ℝ) := by ring
  have hbase := setIntegral_abs_oneEdgeCenteredPrefix_half_sub_half_le
    hm ht0 (lt_of_le_of_lt htHalf (by norm_num)) hs
  have hq0 : 0 ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) :=
    measureReal_nonneg
  calc
    (∫ x in Ioi t,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale x|
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (oneEdgeLogLoss t + 3 / ((m : ℝ) - 3)) / scale := hbase
    _ ≤ (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (16 * ell / (m : ℝ)) / scale := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbracket hq0) hs.le
    _ = (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (16 * ell / ((m : ℝ) * scale)) := by ring

/-- Direct null-variance specialization of the unconditional prefix bound. -/
theorem integral_abs_oneEdgeCenteredPrefix_nullVSeries_le
    {m p : ℕ} (h : Admissible m p) (hm : 6 ≤ m) :
    (∫ x,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m p)) x|
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) ≤
      4 / ((m : ℝ) * Real.sqrt (nullVSeries m p)) := by
  exact integral_abs_oneEdgeCenteredPrefix_half_sub_half_le hm
    (sqrt_nullVSeries_pos h)

/-- Direct null-variance specialization of the event-weighted logarithmic
rate bound. -/
theorem setIntegral_abs_oneEdgeCenteredPrefix_nullVSeries_le_log_rate
    {m p : ℕ} (h : Admissible m p) (hm : 6 ≤ m)
    {t ell : ℝ} (ht0 : 0 < t) (htHalf : t ≤ 1 / 2)
    (hell : 1 ≤ ell) (htRate : t ≤ 5 * ell / (m : ℝ)) :
    (∫ x in Ioi t,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m p)) x|
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (16 * ell /
          ((m : ℝ) * Real.sqrt (nullVSeries m p))) := by
  exact setIntegral_abs_oneEdgeCenteredPrefix_half_sub_half_le_log_rate
    hm ht0 htHalf (sqrt_nullVSeries_pos h) hell htRate

/-! ## Exact transport back to a Gaussian column pair -/

section GaussianPairTransport

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Any strongly measurable test function of one squared Gaussian
correlation can be integrated exactly against the corresponding beta law. -/
theorem integral_comp_squaredNormalizedInner_gaussianProduct_eq_beta
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (g : ℝ → ℝ) (hg : StronglyMeasurable g) :
    (∫ z : E × E, g (squaredNormalizedInner z.1 z.2)
        ∂((stdGaussian E).prod (stdGaussian E))) =
      ∫ x, g x
        ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
  let corr : E × E → ℝ := fun z ↦ squaredNormalizedInner z.1 z.2
  have hcorr : Measurable corr :=
    measurable_uncurry_squaredNormalizedInner
  have hmap := map_squaredNormalizedInner_gaussianProduct
    (E := E) m hdim hm
  calc
    (∫ z : E × E, g (squaredNormalizedInner z.1 z.2)
        ∂((stdGaussian E).prod (stdGaussian E))) =
        ∫ x, g x ∂Measure.map corr
          ((stdGaussian E).prod (stdGaussian E)) := by
      exact (integral_map hcorr.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ x, g x
        ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
      rw [hmap]

/-- Raw two-column Gaussian form of the unconditional prefix estimate. -/
theorem integral_abs_oneEdgeCenteredPrefix_gaussianPair_le
    {m : ℕ} (hdim : finrank ℝ E = m) (hm : 6 ≤ m)
    {scale : ℝ} (hs : 0 < scale) :
    (∫ z : E × E,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale
          (squaredNormalizedInner z.1 z.2)|
          ∂((stdGaussian E).prod (stdGaussian E))) ≤
      4 / ((m : ℝ) * scale) := by
  let g : ℝ → ℝ := fun x ↦
    |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale x|
  have hg : StronglyMeasurable g :=
    ((measurable_oneEdgeCenteredPrefix
      (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale).abs).stronglyMeasurable
  rw [integral_comp_squaredNormalizedInner_gaussianProduct_eq_beta
    m hdim (by omega) g hg]
  exact integral_abs_oneEdgeCenteredPrefix_half_sub_half_le hm hs

/-- Exact raw-pair transport of the event-weighted logarithmic-rate bound. -/
theorem integral_indicator_abs_oneEdgeCenteredPrefix_gaussianPair_le_log_rate
    {m : ℕ} (hdim : finrank ℝ E = m) (hm : 6 ≤ m)
    {t scale ell : ℝ} (ht0 : 0 < t) (htHalf : t ≤ 1 / 2)
    (hs : 0 < scale) (hell : 1 ≤ ell)
    (htRate : t ≤ 5 * ell / (m : ℝ)) :
    (∫ z : E × E,
        (Ioi t).indicator
          (fun x ↦
            |oneEdgeCenteredPrefix (1 / 2)
              (((m - 1 : ℕ) : ℝ) / 2) scale x|)
          (squaredNormalizedInner z.1 z.2)
          ∂((stdGaussian E).prod (stdGaussian E))) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (16 * ell / ((m : ℝ) * scale)) := by
  let f : ℝ → ℝ := fun x ↦
    |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale x|
  let g : ℝ → ℝ := (Ioi t).indicator f
  have hf : StronglyMeasurable f :=
    ((measurable_oneEdgeCenteredPrefix
      (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) scale).abs).stronglyMeasurable
  have hg : StronglyMeasurable g := hf.indicator measurableSet_Ioi
  rw [integral_comp_squaredNormalizedInner_gaussianProduct_eq_beta
    m hdim (by omega) g hg]
  rw [integral_indicator measurableSet_Ioi]
  exact setIntegral_abs_oneEdgeCenteredPrefix_half_sub_half_le_log_rate
    hm ht0 htHalf hs hell htRate

/-- Null-variance raw-pair form of the unconditional bound. -/
theorem integral_abs_oneEdgeCenteredPrefix_gaussianPair_nullVSeries_le
    {m p : ℕ} (hdim : finrank ℝ E = m)
    (h : Admissible m p) (hm : 6 ≤ m) :
    (∫ z : E × E,
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m p))
          (squaredNormalizedInner z.1 z.2)|
          ∂((stdGaussian E).prod (stdGaussian E))) ≤
      4 / ((m : ℝ) * Real.sqrt (nullVSeries m p)) := by
  exact integral_abs_oneEdgeCenteredPrefix_gaussianPair_le hdim hm
    (sqrt_nullVSeries_pos h)

/-- Null-variance raw-pair form of the event-weighted logarithmic-rate
bound. -/
theorem
    integral_indicator_abs_oneEdgeCenteredPrefix_gaussianPair_nullVSeries_le_log_rate
    {m p : ℕ} (hdim : finrank ℝ E = m)
    (h : Admissible m p) (hm : 6 ≤ m)
    {t ell : ℝ} (ht0 : 0 < t) (htHalf : t ≤ 1 / 2)
    (hell : 1 ≤ ell) (htRate : t ≤ 5 * ell / (m : ℝ)) :
    (∫ z : E × E,
        (Ioi t).indicator
          (fun x ↦
            |oneEdgeCenteredPrefix (1 / 2)
              (((m - 1 : ℕ) : ℝ) / 2)
              (Real.sqrt (nullVSeries m p)) x|)
          (squaredNormalizedInner z.1 z.2)
          ∂((stdGaussian E).prod (stdGaussian E))) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (16 * ell /
          ((m : ℝ) * Real.sqrt (nullVSeries m p))) := by
  exact integral_indicator_abs_oneEdgeCenteredPrefix_gaussianPair_le_log_rate
    hdim hm ht0 htHalf (sqrt_nullVSeries_pos h) hell htRate

end GaussianPairTransport

/-! ## Ambient raw-sample Pearson adapter -/

/-- Center two ambient Gaussian data columns by orthogonal projection. -/
def centerGaussianPair (N : ℕ) :
    ObservationSpace N × ObservationSpace N →
      centeredSubspace N × centeredSubspace N :=
  Prod.map (centeredSubspace N).orthogonalProjectionOnto
    (centeredSubspace N).orthogonalProjectionOnto

/-- The squared Pearson correlation of two raw columns, expressed in the
centered residual subspace.  By `coe_orthogonalProjectionOnto_centeredSubspace`
this is the usual correlation after subtracting each sample mean. -/
def squaredCenteredPearson (N : ℕ)
    (z : ObservationSpace N × ObservationSpace N) : ℝ :=
  squaredNormalizedInner (centerGaussianPair N z).1 (centerGaussianPair N z).2

/-- Deterministic identification with the textbook Pearson formula formed
from the two explicitly mean-centered ambient columns. -/
theorem squaredCenteredPearson_eq_centerVectors
    {N : ℕ} (hN : 0 < N)
    (z : ObservationSpace N × ObservationSpace N) :
    squaredCenteredPearson N z =
      squaredNormalizedInner (centerVector z.1) (centerVector z.2) := by
  rcases z with ⟨u, v⟩
  change squaredNormalizedInner
      ((centeredSubspace N).orthogonalProjectionOnto u)
      ((centeredSubspace N).orthogonalProjectionOnto v) =
    squaredNormalizedInner (centerVector u) (centerVector v)
  unfold squaredNormalizedInner
  simp only [Submodule.coe_inner, Submodule.coe_norm]
  rw [coe_orthogonalProjectionOnto_centeredSubspace hN u,
    coe_orthogonalProjectionOnto_centeredSubspace hN v]

theorem measurable_centerGaussianPair (N : ℕ) :
    Measurable (centerGaussianPair N) := by
  unfold centerGaussianPair
  fun_prop

theorem measurable_squaredCenteredPearson (N : ℕ) :
    Measurable (squaredCenteredPearson N) := by
  unfold squaredCenteredPearson
  exact measurable_uncurry_squaredNormalizedInner.comp
    (measurable_centerGaussianPair N)

/-- Independent raw Gaussian columns remain independent standard Gaussians
after centering into the residual subspace. -/
theorem map_centerGaussianPair_rawGaussianProduct (N : ℕ) :
    Measure.map (centerGaussianPair N)
        ((stdGaussian (ObservationSpace N)).prod
          (stdGaussian (ObservationSpace N))) =
      (stdGaussian (centeredSubspace N)).prod
        (stdGaussian (centeredSubspace N)) := by
  unfold centerGaussianPair
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [(hasLaw_centerProjection_stdGaussian N).map_eq]

/-- Exact beta pushforward law of the ordinary squared Pearson correlation
of two independent raw Gaussian columns with `m+1` observations. -/
theorem map_squaredCenteredPearson_rawGaussianProduct_eq_beta
    (m : ℕ) (hm : 2 ≤ m) :
    Measure.map (squaredCenteredPearson (m + 1))
        ((stdGaussian (ObservationSpace (m + 1))).prod
          (stdGaussian (ObservationSpace (m + 1))) ) =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
  let centerPair := centerGaussianPair (m + 1)
  let corr : centeredSubspace (m + 1) × centeredSubspace (m + 1) → ℝ :=
    fun z ↦ squaredNormalizedInner z.1 z.2
  have hcenter : Measurable centerPair := measurable_centerGaussianPair (m + 1)
  have hcorr : Measurable corr := measurable_uncurry_squaredNormalizedInner
  have hdim : finrank ℝ (centeredSubspace (m + 1)) = m := by
    simpa using finrank_centeredSubspace (N := m + 1) (Nat.zero_lt_succ m)
  calc
    Measure.map (squaredCenteredPearson (m + 1))
        ((stdGaussian (ObservationSpace (m + 1))).prod
          (stdGaussian (ObservationSpace (m + 1)))) =
        Measure.map corr
          (Measure.map centerPair
            ((stdGaussian (ObservationSpace (m + 1))).prod
              (stdGaussian (ObservationSpace (m + 1))))) := by
      rw [Measure.map_map hcorr hcenter]
      rfl
    _ = Measure.map corr
        ((stdGaussian (centeredSubspace (m + 1))).prod
          (stdGaussian (centeredSubspace (m + 1)))) := by
      rw [map_centerGaussianPair_rawGaussianProduct]
    _ = betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) :=
      map_squaredNormalizedInner_gaussianProduct
        (E := centeredSubspace (m + 1)) m hdim hm

/-- Exact integral transport from the ambient raw-sample Pearson statistic to
the beta law. -/
theorem integral_comp_squaredCenteredPearson_rawGaussian_eq_beta
    (m : ℕ) (hm : 2 ≤ m) (g : ℝ → ℝ) (hg : StronglyMeasurable g) :
    (∫ z : ObservationSpace (m + 1) × ObservationSpace (m + 1),
        g (squaredCenteredPearson (m + 1) z)
          ∂((stdGaussian (ObservationSpace (m + 1))).prod
            (stdGaussian (ObservationSpace (m + 1))))) =
      ∫ x, g x
        ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
  calc
    (∫ z : ObservationSpace (m + 1) × ObservationSpace (m + 1),
        g (squaredCenteredPearson (m + 1) z)
          ∂((stdGaussian (ObservationSpace (m + 1))).prod
            (stdGaussian (ObservationSpace (m + 1))))) =
        ∫ x, g x ∂Measure.map (squaredCenteredPearson (m + 1))
          ((stdGaussian (ObservationSpace (m + 1))).prod
            (stdGaussian (ObservationSpace (m + 1)))) := by
      exact (integral_map (measurable_squaredCenteredPearson (m + 1)).aemeasurable
        hg.aestronglyMeasurable).symm
    _ = ∫ x, g x
        ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
      rw [map_squaredCenteredPearson_rawGaussianProduct_eq_beta m hm]

/-- Ambient raw-sample form of the unconditional null-variance prefix bound. -/
theorem integral_abs_oneEdgeCenteredPrefix_rawPearson_nullVSeries_le
    {m p : ℕ} (h : Admissible m p) (hm : 6 ≤ m) :
    (∫ z : ObservationSpace (m + 1) × ObservationSpace (m + 1),
        |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m p))
          (squaredCenteredPearson (m + 1) z)|
          ∂((stdGaussian (ObservationSpace (m + 1))).prod
            (stdGaussian (ObservationSpace (m + 1))))) ≤
      4 / ((m : ℝ) * Real.sqrt (nullVSeries m p)) := by
  let g : ℝ → ℝ := fun x ↦
    |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m p)) x|
  have hg : StronglyMeasurable g :=
    ((measurable_oneEdgeCenteredPrefix
      (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
        (Real.sqrt (nullVSeries m p))).abs).stronglyMeasurable
  rw [integral_comp_squaredCenteredPearson_rawGaussian_eq_beta m (by omega) g hg]
  exact integral_abs_oneEdgeCenteredPrefix_nullVSeries_le h hm

/-- Ambient raw-sample form of the event-weighted logarithmic-rate bound. -/
theorem
    integral_indicator_abs_oneEdgeCenteredPrefix_rawPearson_nullVSeries_le_log_rate
    {m p : ℕ} (h : Admissible m p) (hm : 6 ≤ m)
    {t ell : ℝ} (ht0 : 0 < t) (htHalf : t ≤ 1 / 2)
    (hell : 1 ≤ ell) (htRate : t ≤ 5 * ell / (m : ℝ)) :
    (∫ z : ObservationSpace (m + 1) × ObservationSpace (m + 1),
        (Ioi t).indicator
          (fun x ↦
            |oneEdgeCenteredPrefix (1 / 2)
              (((m - 1 : ℕ) : ℝ) / 2)
              (Real.sqrt (nullVSeries m p)) x|)
          (squaredCenteredPearson (m + 1) z)
          ∂((stdGaussian (ObservationSpace (m + 1))).prod
            (stdGaussian (ObservationSpace (m + 1))))) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) *
        (16 * ell /
          ((m : ℝ) * Real.sqrt (nullVSeries m p))) := by
  let f : ℝ → ℝ := fun x ↦
    |oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m p)) x|
  let g : ℝ → ℝ := (Ioi t).indicator f
  have hf : StronglyMeasurable f :=
    ((measurable_oneEdgeCenteredPrefix
      (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
        (Real.sqrt (nullVSeries m p))).abs).stronglyMeasurable
  have hg : StronglyMeasurable g := hf.indicator measurableSet_Ioi
  rw [integral_comp_squaredCenteredPearson_rawGaussian_eq_beta m (by omega) g hg]
  rw [integral_indicator measurableSet_Ioi]
  exact setIntegral_abs_oneEdgeCenteredPrefix_nullVSeries_le_log_rate
    h hm ht0 htHalf hell htRate

end

end LogdetLean.Coherence
