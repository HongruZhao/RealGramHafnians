import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import LogdetLean.CDFSmoothingSwap
import LogdetLean.FejerCDFInversion
import LogdetLean.QuantitativeFourier
/-!
# The Fourier half of Fejer--Esseen smoothing

This file converts the finite-interval Fejer CDF inversion formula into a
bound involving characteristic functions.  A finite first absolute moment is
assumed only to justify the individual Fubini interchanges at frequency zero;
the final estimate itself contains no moment term.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set Real
open scoped Real ComplexConjugate Interval

noncomputable section

theorem integral_fejer_phase (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x T t : ℝ) :
    (∫ y : ℝ,
      Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) ∂μ) =
      Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
        charFun μ (2 * Real.pi * T * t) := by
  rw [charFun_eq_integral_probChar]
  simp only [probChar_apply, Real.inner_apply]
  change (∫ y : ℝ,
      Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) ∂μ) =
    Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
      ∫ y : ℝ, Complex.exp (↑(y * (2 * Real.pi * T * t)) * Complex.I) ∂μ
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ by
    change Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) =
      Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
        Complex.exp (↑(y * (2 * Real.pi * T * t)) * Complex.I)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem integral_fejerOscillatoryPrimitive (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x T : ℝ) {t : ℝ} (ht : t ≠ 0) :
    (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂μ) =
      (Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
          charFun μ (2 * Real.pi * T * t) - 1) /
        (↑(-2 * Real.pi * t) * Complex.I) := by
  have hphase : Integrable (fun y : ℝ ↦
      Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I)) μ := by
    apply (integrable_const (μ := μ) (1 : ℂ)).mono
    · fun_prop
    · exact Filter.Eventually.of_forall fun y ↦ by
        rw [Complex.norm_exp]
        simp
  calc
    (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂μ) =
        ∫ y : ℝ,
          (Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) - 1) /
            (↑(-2 * Real.pi * t) * Complex.I) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦
        fejerOscillatoryPrimitive_of_ne_zero (T * (x - y)) ht
    _ = ((∫ y : ℝ,
          Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) ∂μ) - 1) /
          (↑(-2 * Real.pi * t) * Complex.I) := by
      rw [integral_div, integral_sub hphase (integrable_const (1 : ℂ))]
      simp
    _ = _ := by rw [integral_fejer_phase]

/-- A measurable closed formula for the oscillatory primitive.  The separate
zero-frequency branch is the removable value. -/
def fejerOscillatoryPrimitiveFormula (u t : ℝ) : ℂ :=
  if t = 0 then u else
    (Complex.exp (↑(-2 * Real.pi * (u * t)) * Complex.I) - 1) /
      (↑(-2 * Real.pi * t) * Complex.I)

theorem fejerOscillatoryPrimitive_eq_formula (u t : ℝ) :
    fejerOscillatoryPrimitive u t = fejerOscillatoryPrimitiveFormula u t := by
  by_cases ht : t = 0
  · subst t
    simp [fejerOscillatoryPrimitiveFormula]
  · simp [fejerOscillatoryPrimitiveFormula, ht,
      fejerOscillatoryPrimitive_of_ne_zero u ht]

theorem integrable_fejerPrimitive_triangle_prod
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y : ℝ ↦ y) μ) (x T : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      fejerOscillatoryPrimitive (T * (x - p.1)) p.2 *
        (triangleMultiplier p.2 : ℂ)) (μ.prod volume) := by
  have hu : Integrable (fun y : ℝ ↦ T * (x - y)) μ :=
    ((integrable_const x).sub hμ).const_mul T
  have hdom : Integrable (fun p : ℝ × ℝ ↦
      (Complex.ofReal (T * (x - p.1))) *
        (triangleMultiplier p.2 : ℂ)) (μ.prod volume) :=
    hu.ofReal.mul_prod triangleMultiplier_integrable_complex
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦
      fejerOscillatoryPrimitive (T * (x - p.1)) p.2 *
        (triangleMultiplier p.2 : ℂ)) (μ.prod volume) := by
    have heq : (fun p : ℝ × ℝ ↦
        fejerOscillatoryPrimitive (T * (x - p.1)) p.2 *
          (triangleMultiplier p.2 : ℂ)) =
      (fun p : ℝ × ℝ ↦
        fejerOscillatoryPrimitiveFormula (T * (x - p.1)) p.2 *
          (triangleMultiplier p.2 : ℂ)) := by
      funext p
      rw [fejerOscillatoryPrimitive_eq_formula]
    rw [heq]
    have hformula : Measurable (fun p : ℝ × ℝ ↦
        fejerOscillatoryPrimitiveFormula (T * (x - p.1)) p.2) := by
      unfold fejerOscillatoryPrimitiveFormula
      apply Measurable.ite (measurable_snd measurableSet_eq)
      · fun_prop
      · fun_prop
    exact (hformula.mul
      (Complex.continuous_ofReal.measurable.comp
        (continuous_triangleMultiplier.measurable.comp measurable_snd))).aestronglyMeasurable
  apply hdom.mono hmeas
  exact Filter.Eventually.of_forall fun p ↦ by
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real]
    have htri : 0 ≤ triangleMultiplier p.2 := le_max_right _ _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg htri]
    exact mul_le_mul_of_nonneg_right
      (norm_fejerOscillatoryPrimitive_le (T * (x - p.1)) p.2) htri

/-- Average the finite-interval inversion formula against a law. -/
theorem integral_cdf_fejerMeasure_fourier
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y : ℝ ↦ y) μ) (x T : ℝ) :
    Complex.ofReal (∫ y : ℝ, cdf fejerMeasure (T * (x - y)) ∂μ) =
      1 / 2 + ∫ t : ℝ,
        (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂μ) *
          (triangleMultiplier t : ℂ) := by
  let P : ℝ → ℝ → ℂ := fun y t ↦
    fejerOscillatoryPrimitive (T * (x - y)) t *
      (triangleMultiplier t : ℂ)
  have hP : Integrable (Function.uncurry P) (μ.prod volume) := by
    change Integrable (fun p : ℝ × ℝ ↦
      fejerOscillatoryPrimitive (T * (x - p.1)) p.2 *
        (triangleMultiplier p.2 : ℂ)) (μ.prod volume)
    exact integrable_fejerPrimitive_triangle_prod μ hμ x T
  have hinner : Integrable (fun y : ℝ ↦ ∫ t : ℝ, P y t) μ := by
    simpa [Function.uncurry] using hP.integral_prod_left
  calc
    Complex.ofReal (∫ y : ℝ, cdf fejerMeasure (T * (x - y)) ∂μ) =
        ∫ y : ℝ, (cdf fejerMeasure (T * (x - y)) : ℂ) ∂μ := by
      rw [integral_complex_ofReal]
    _ = ∫ y : ℝ, (1 / 2 + ∫ t : ℝ, P y t) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        simpa [P] using cdf_fejerMeasure_fourier (T * (x - y))
    _ = 1 / 2 + ∫ y : ℝ, (∫ t : ℝ, P y t) ∂μ := by
      rw [integral_add (integrable_const (1 / 2 : ℂ)) hinner]
      simp
    _ = 1 / 2 + ∫ t : ℝ, (∫ y : ℝ, P y t ∂μ) := by
      congr 1
      simpa [Function.uncurry] using integral_integral_swap hP
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t ↦ by
        change (∫ y : ℝ,
            fejerOscillatoryPrimitive (T * (x - y)) t *
              (triangleMultiplier t : ℂ) ∂μ) =
          (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂μ) *
            (triangleMultiplier t : ℂ)
        rw [integral_mul_const]

/-- Exact Fourier identity for the difference of two Fejer-smoothed CDFs.
The value of the displayed integrand at `t=0` is irrelevant. -/
theorem smoothCDF_fejerMeasure_sub_fourier
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (hν : Integrable (fun y : ℝ ↦ y) ν)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Complex.ofReal (smoothCDF fejerMeasure T μ x -
        smoothCDF fejerMeasure T ν x) =
      ∫ t : ℝ,
        (Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
            (charFun μ (2 * Real.pi * T * t) -
              charFun ν (2 * Real.pi * T * t)) /
            (↑(-2 * Real.pi * t) * Complex.I)) *
          (triangleMultiplier t : ℂ) := by
  rw [smoothCDF_eq_integral_kernel_cdf fejerMeasure μ hT,
    smoothCDF_eq_integral_kernel_cdf fejerMeasure ν hT]
  have hprodμ := integrable_fejerPrimitive_triangle_prod μ hμ x T
  have hprodν := integrable_fejerPrimitive_triangle_prod ν hν x T
  have hintμ : Integrable (fun t : ℝ ↦
      (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂μ) *
        (triangleMultiplier t : ℂ)) := by
    apply hprodμ.integral_prod_right.congr
    exact Filter.Eventually.of_forall fun t ↦ by
      change (∫ y : ℝ,
          fejerOscillatoryPrimitive (T * (x - y)) t *
            (triangleMultiplier t : ℂ) ∂μ) =
        (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂μ) *
          (triangleMultiplier t : ℂ)
      rw [integral_mul_const]
  have hintν : Integrable (fun t : ℝ ↦
      (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂ν) *
        (triangleMultiplier t : ℂ)) := by
    apply hprodν.integral_prod_right.congr
    exact Filter.Eventually.of_forall fun t ↦ by
      change (∫ y : ℝ,
          fejerOscillatoryPrimitive (T * (x - y)) t *
            (triangleMultiplier t : ℂ) ∂ν) =
        (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂ν) *
          (triangleMultiplier t : ℂ)
      rw [integral_mul_const]
  rw [Complex.ofReal_sub,
    integral_cdf_fejerMeasure_fourier μ hμ x T,
    integral_cdf_fejerMeasure_fourier ν hν x T]
  let Aμ : ℝ → ℂ := fun t ↦
    (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂μ) *
      (triangleMultiplier t : ℂ)
  let Aν : ℝ → ℂ := fun t ↦
    (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂ν) *
      (triangleMultiplier t : ℂ)
  change (1 / 2 + ∫ t : ℝ, Aμ t) - (1 / 2 + ∫ t : ℝ, Aν t) = _
  have hAμ : Integrable Aμ := by simpa [Aμ] using hintμ
  have hAν : Integrable Aν := by simpa [Aν] using hintν
  calc
    (1 / 2 + ∫ t : ℝ, Aμ t) - (1 / 2 + ∫ t : ℝ, Aν t) =
        (∫ t : ℝ, Aμ t) - ∫ t : ℝ, Aν t := by abel
    _ = ∫ t : ℝ, (Aμ t - Aν t) := (integral_sub hAμ hAν).symm
    _ = _ := by
      have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := Measure.ae_ne volume 0
      apply integral_congr_ae
      filter_upwards [hne] with t ht
      dsimp [Aμ, Aν]
      rw [integral_fejerOscillatoryPrimitive μ x T ht,
        integral_fejerOscillatoryPrimitive ν x T ht]
      ring

/-- Scaling the unit Fejer frequency window to the characteristic-function
window `[-2*pi*T,2*pi*T]`. -/
theorem integral_unitScale_fourierQuotient
    {φ ψ : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hint : IntegrableOn (fourierQuotientError φ ψ)
      (Icc (-(2 * Real.pi * T)) (2 * Real.pi * T))) :
    (∫ t : ℝ in Icc (-1) 1,
      T * fourierQuotientError φ ψ ((2 * Real.pi * T) * t)) =
        (1 / (2 * Real.pi)) *
          truncatedFourierDiscrepancy φ ψ (2 * Real.pi * T) := by
  let c : ℝ := 2 * Real.pi * T
  have hc : 0 < c := by dsimp [c]; positivity
  have hinterval : IntervalIntegrable (fourierQuotientError φ ψ)
      volume (-c) c := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2
    simpa [c] using hint
  have hleft :
      (∫ t : ℝ in Icc (-1) 1,
        T * fourierQuotientError φ ψ (c * t)) =
          T * ∫ t : ℝ in (-1 : ℝ)..1,
            fourierQuotientError φ ψ (c * t) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_const_mul]
  have hright : truncatedFourierDiscrepancy φ ψ c =
      ∫ s : ℝ in (-c)..c, fourierQuotientError φ ψ s := by
    rw [truncatedFourierDiscrepancy, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
  rw [show 2 * Real.pi * T = c by rfl, hleft, hright,
    intervalIntegral.integral_comp_mul_left (f := fourierQuotientError φ ψ)
      (a := (-1 : ℝ)) (b := 1) hc.ne']
  rw [show c * (-1 : ℝ) = -c by ring, show c * (1 : ℝ) = c by ring]
  simp only [smul_eq_mul]
  have hcoef : T * c⁻¹ = 1 / (2 * Real.pi) := by
    dsimp [c]
    field_simp [ne_of_gt Real.pi_pos, ne_of_gt hT]
  rw [← mul_assoc, hcoef]

theorem integrableOn_unitScale_fourierQuotient
    {φ ψ : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hint : IntegrableOn (fourierQuotientError φ ψ)
      (Icc (-(2 * Real.pi * T)) (2 * Real.pi * T))) :
    IntegrableOn
      (fun t : ℝ ↦ T *
        fourierQuotientError φ ψ ((2 * Real.pi * T) * t))
      (Icc (-1) 1) := by
  let c : ℝ := 2 * Real.pi * T
  have hc : 0 < c := by dsimp [c]; positivity
  have hinterval : IntervalIntegrable (fourierQuotientError φ ψ)
      volume (-c) c := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2
    simpa [c] using hint
  have hcomp0 := hinterval.comp_mul_left (c := c)
  have hcomp : IntervalIntegrable
      (fun t : ℝ ↦ fourierQuotientError φ ψ (c * t))
      volume (-1) 1 := by
    convert hcomp0 using 1 <;> field_simp [hc.ne']
  have hcompOn : IntegrableOn
      (fun t : ℝ ↦ fourierQuotientError φ ψ (c * t))
      (Icc (-1) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 hcomp
  change Integrable
    (fun t : ℝ ↦ T * fourierQuotientError φ ψ ((2 * Real.pi * T) * t))
    (volume.restrict (Icc (-1) 1))
  simpa [c, mul_assoc] using hcompOn.const_mul T

def fejerSmoothingFourierIntegrand
    (μ ν : Measure ℝ) (T x t : ℝ) : ℂ :=
  (Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
      (charFun μ ((2 * Real.pi * T) * t) -
        charFun ν ((2 * Real.pi * T) * t)) /
      (↑(-2 * Real.pi * t) * Complex.I)) *
    (triangleMultiplier t : ℂ)

theorem norm_fejerSmoothingFourierIntegrand_le
    (μ ν : Measure ℝ) {T : ℝ} (hT : 0 < T) (x t : ℝ) :
    ‖fejerSmoothingFourierIntegrand μ ν T x t‖ ≤
      (Icc (-1) 1).indicator
        (fun s : ℝ ↦ T * fourierQuotientError (charFun μ) (charFun ν)
          ((2 * Real.pi * T) * s)) t := by
  by_cases htmem : t ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem htmem]
    by_cases ht0 : t = 0
    · subst t
      simp [fejerSmoothingFourierIntegrand, fourierQuotientError]
    · have habst : 0 < |t| := abs_pos.mpr ht0
      have hc : 0 < 2 * Real.pi * T := by positivity
      have htri0 : 0 ≤ triangleMultiplier t := le_max_right _ _
      have htri1 : triangleMultiplier t ≤ 1 := by
        rw [triangleMultiplier]
        exact max_le (by linarith [abs_nonneg t]) zero_le_one
      have hden : 0 < 2 * Real.pi * |t| := by positivity
      calc
        ‖fejerSmoothingFourierIntegrand μ ν T x t‖ =
            (‖charFun μ ((2 * Real.pi * T) * t) -
                charFun ν ((2 * Real.pi * T) * t)‖ /
              (2 * Real.pi * |t|)) * triangleMultiplier t := by
          simp only [fejerSmoothingFourierIntegrand, Complex.norm_mul, norm_div,
            Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
            abs_of_nonneg htri0]
          rw [Complex.norm_exp]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self,
            Real.exp_zero, one_mul]
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
          ring
        _ ≤ ‖charFun μ ((2 * Real.pi * T) * t) -
                charFun ν ((2 * Real.pi * T) * t)‖ /
              (2 * Real.pi * |t|) := by
          exact mul_le_of_le_one_right (by positivity) htri1
        _ = T * fourierQuotientError (charFun μ) (charFun ν)
              ((2 * Real.pi * T) * t) := by
          rw [fourierQuotientError, abs_mul, abs_of_pos hc]
          field_simp [ne_of_gt hT, ne_of_gt Real.pi_pos, ht0]
  · rw [indicator_of_notMem htmem]
    have hzero : triangleMultiplier t = 0 := by
      simp only [mem_Icc, not_and_or, not_le] at htmem
      rcases htmem with ht | ht
      · exact triangleMultiplier_eq_zero_of_lt_neg_one ht
      · exact triangleMultiplier_eq_zero_of_one_lt ht
    simp [fejerSmoothingFourierIntegrand, hzero]

/-- The actual Fourier estimate for the Fejer-smoothed CDF discrepancy. -/
theorem abs_smoothCDF_fejerMeasure_sub_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (hν : Integrable (fun y : ℝ ↦ y) ν)
    {T : ℝ} (hT : 0 < T)
    (hint : IntegrableOn
      (fourierQuotientError (charFun μ) (charFun ν))
      (Icc (-(2 * Real.pi * T)) (2 * Real.pi * T)))
    (x : ℝ) :
    |smoothCDF fejerMeasure T μ x - smoothCDF fejerMeasure T ν x| ≤
      (1 / (2 * Real.pi)) *
        truncatedCharFunDiscrepancy μ ν (2 * Real.pi * T) := by
  let U : ℝ → ℝ := fun t ↦
    (Icc (-1) 1).indicator
      (fun s : ℝ ↦ T * fourierQuotientError (charFun μ) (charFun ν)
        ((2 * Real.pi * T) * s)) t
  have hUon := integrableOn_unitScale_fourierQuotient hT hint
  have hU : Integrable U := by
    rw [show U = (Icc (-1) 1).indicator
        (fun s : ℝ ↦ T * fourierQuotientError (charFun μ) (charFun ν)
          ((2 * Real.pi * T) * s)) by rfl,
      integrable_indicator_iff measurableSet_Icc]
    exact hUon
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  rw [smoothCDF_fejerMeasure_sub_fourier μ ν hμ hν hT]
  change ‖∫ t : ℝ, fejerSmoothingFourierIntegrand μ ν T x t‖ ≤ _
  calc
    ‖∫ t : ℝ, fejerSmoothingFourierIntegrand μ ν T x t‖ ≤
        ∫ t : ℝ, ‖fejerSmoothingFourierIntegrand μ ν T x t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, U t := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
      · exact hU
      · exact Filter.Eventually.of_forall fun t ↦
          norm_fejerSmoothingFourierIntegrand_le μ ν hT x t
    _ = ∫ t : ℝ in Icc (-1) 1,
        T * fourierQuotientError (charFun μ) (charFun ν)
          ((2 * Real.pi * T) * t) := by
      rw [show U = (Icc (-1) 1).indicator
          (fun s : ℝ ↦ T * fourierQuotientError (charFun μ) (charFun ν)
            ((2 * Real.pi * T) * s)) by rfl,
        integral_indicator measurableSet_Icc]
    _ = (1 / (2 * Real.pi)) *
        truncatedCharFunDiscrepancy μ ν (2 * Real.pi * T) := by
      exact integral_unitScale_fourierQuotient hT hint

/-- A fully proved Esseen smoothing certificate in the kernel scale `T`.

The proof follows the mechanism of Feller, *An Introduction to Probability
Theory and Its Applications*, Vol. II (2nd ed., 1971), Lemma XVI.3.1,
p. 537: smooth with a compact-frequency kernel, bound the smoothed difference
by the weighted characteristic-function integral, and absorb the kernel
tails using the target density bound.  Feller optimizes the kernel estimates
to obtain `24*m/(pi*S)`.  Our from-scratch Fejer tail estimate is deliberately
coarser and gives `64*pi*m/S` after reparametrization, while preserving the
same `O(1/S)` order and the sharp `1/pi` Fourier coefficient. -/
theorem kolmogorovDistance_le_fejer_esseen_kernelScale
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (hν : Integrable (fun y : ℝ ↦ y) ν)
    {T m : ℝ} (hT : 0 < T) (hm : 0 ≤ m)
    (hlip : HasRealLipschitzBound (cdf ν) m)
    (hint : IntegrableOn
      (fourierQuotientError (charFun μ) (charFun ν))
      (Icc (-(2 * Real.pi * T)) (2 * Real.pi * T))) :
    kolmogorovDistance μ ν ≤
      (1 / Real.pi) *
        truncatedCharFunDiscrepancy μ ν (2 * Real.pi * T) +
      32 * m / T := by
  have hsmooth : ∀ x,
      |smoothCDF fejerMeasure T μ x - smoothCDF fejerMeasure T ν x| ≤
        (1 / (2 * Real.pi)) *
          truncatedCharFunDiscrepancy μ ν (2 * Real.pi * T) :=
    fun x ↦ abs_smoothCDF_fejerMeasure_sub_le μ ν hμ hν hT hint x
  have h := kolmogorovDistance_le_of_kernel_smoothing_tail_quarter
    fejerMeasure μ ν (T := T) (a := 8) (q := 1 / 4) (m := m)
    (δ := (1 / (2 * Real.pi)) *
      truncatedCharFunDiscrepancy μ ν (2 * Real.pi * T))
    hT (by norm_num) (by norm_num) hm
    fejerMeasure_tail_eight_le_quarter hlip hsmooth
  calc
    kolmogorovDistance μ ν ≤
        2 * ((1 / (2 * Real.pi)) *
          truncatedCharFunDiscrepancy μ ν (2 * Real.pi * T)) +
        4 * m * 8 / T := h
    _ = (1 / Real.pi) *
          truncatedCharFunDiscrepancy μ ν (2 * Real.pi * T) +
        32 * m / T := by
      field_simp [ne_of_gt Real.pi_pos]
      ring

/-- Frequency-cutoff form of the proved Esseen inequality. -/
theorem kolmogorovDistance_le_fejer_esseen
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (hν : Integrable (fun y : ℝ ↦ y) ν)
    {S m : ℝ} (hS : 0 < S) (hm : 0 ≤ m)
    (hlip : HasRealLipschitzBound (cdf ν) m)
    (hint : IntegrableOn
      (fourierQuotientError (charFun μ) (charFun ν)) (Icc (-S) S)) :
    kolmogorovDistance μ ν ≤
      (1 / Real.pi) * truncatedCharFunDiscrepancy μ ν S +
        64 * Real.pi * m / S := by
  let T : ℝ := S / (2 * Real.pi)
  have hT : 0 < T := by dsimp [T]; positivity
  have hcut : 2 * Real.pi * T = S := by
    dsimp [T]
    field_simp [ne_of_gt Real.pi_pos]
  have hint' : IntegrableOn
      (fourierQuotientError (charFun μ) (charFun ν))
      (Icc (-(2 * Real.pi * T)) (2 * Real.pi * T)) := by
    simpa [hcut] using hint
  have h := kolmogorovDistance_le_fejer_esseen_kernelScale μ ν hμ hν
    hT hm hlip hint'
  rw [hcut] at h
  apply h.trans_eq
  dsimp [T]
  field_simp [ne_of_gt Real.pi_pos, ne_of_gt hS]
  ring

end

end LogdetLean
