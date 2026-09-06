import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import LogdetLean.CDFSmoothingSwap
import LogdetLean.FejerSmoothingFourier
import LogdetLean.SignedComparatorSmoothing
/-!
# Fourier smoothing for an integrable signed density

The comparator in a first Edgeworth expansion is represented by an
integrable real density, not by a probability measure.  Its cumulative
function and Fourier transform are defined directly by Lebesgue integrals.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set Real
open scoped Real ComplexConjugate Interval

noncomputable section

def signedDensityCDF (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in Iic x, g y

def signedDensityFourier (g : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (↑(y * t) * Complex.I) * (g y : ℂ)

theorem smoothFunction_signedDensityCDF_eq
    (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (g : ℝ → ℝ) (hg : Integrable g)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    smoothFunction κ T (signedDensityCDF g) x =
      ∫ y : ℝ, cdf κ (T * (x - y)) * g y := by
  let f : ℝ → ℝ → ℝ := fun z y ↦
    (Iic (x - z / T)).indicator (fun y ↦ g y) y
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ x - p.1 / T} :=
    measurableSet_le measurable_snd
      (measurable_const.sub (measurable_fst.div_const T))
  have hfmeas : AEStronglyMeasurable (Function.uncurry f) (κ.prod volume) := by
    change AEStronglyMeasurable
      ({p : ℝ × ℝ | p.2 ≤ x - p.1 / T}.indicator
        (fun p ↦ g p.2)) (κ.prod volume)
    exact hg.aestronglyMeasurable.comp_snd.indicator hset
  have hdom : Integrable (fun p : ℝ × ℝ ↦ (1 : ℝ) * g p.2)
      (κ.prod volume) :=
    (integrable_const (μ := κ) (1 : ℝ)).mul_prod hg
  have hfi : Integrable (Function.uncurry f) (κ.prod volume) := by
    apply hdom.mono hfmeas
    exact Filter.Eventually.of_forall fun p ↦ by
      by_cases hp : p.2 ∈ Iic (x - p.1 / T)
      · simp [f, Function.uncurry, indicator_of_mem hp]
      · simp [f, Function.uncurry, indicator_of_notMem hp]
  rw [smoothFunction]
  simp_rw [signedDensityCDF, ← integral_indicator measurableSet_Iic]
  change (∫ z, ∫ y, f z y ∂volume ∂κ) = _
  rw [integral_integral_swap hfi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ by
    change (∫ z : ℝ, f z y ∂κ) = cdf κ (T * (x - y)) * g y
    rw [cdf_eq_integral_Iic_indicator]
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ by
      simp only [f]
      by_cases hleft : y ≤ x - z / T
      · have hright : z ≤ T * (x - y) := by
          have hdiv : z / T ≤ x - y := by linarith
          have hmul := (div_le_iff₀ hT).1 hdiv
          linarith
        simp [hleft, hright]
      · have hright : ¬ z ≤ T * (x - y) := by
          intro hz
          have hmul : z ≤ (x - y) * T := by linarith
          have hdiv := (div_le_iff₀ hT).2 hmul
          exact hleft (by linarith)
        simp [hleft, hright]

theorem integral_signedDensity_phase (g : ℝ → ℝ)
    (x T t : ℝ) :
    (∫ y : ℝ,
      Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) *
        (g y : ℂ)) =
      Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
        signedDensityFourier g (2 * Real.pi * T * t) := by
  rw [signedDensityFourier, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ by
    change Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) *
        (g y : ℂ) =
      Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
        (Complex.exp (↑(y * (2 * Real.pi * T * t)) * Complex.I) * (g y : ℂ))
    have hexp :
        Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) =
          Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
            Complex.exp (↑(y * (2 * Real.pi * T * t)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp, mul_assoc]

theorem integral_fejerOscillatoryPrimitive_mul_density
    (g : ℝ → ℝ) (hg : Integrable g) (x T : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) =
      (Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
          signedDensityFourier g (2 * Real.pi * T * t) - ∫ y : ℝ, g y) /
        (↑(-2 * Real.pi * t) * Complex.I) := by
  have hgc : Integrable (fun y : ℝ ↦ (g y : ℂ)) := hg.ofReal
  have hphaseg : Integrable (fun y : ℝ ↦
      Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) *
        (g y : ℂ)) := by
    apply hgc.mono
    · fun_prop
    · exact Filter.Eventually.of_forall fun y ↦ by
        rw [Complex.norm_mul, Complex.norm_exp]
        simp
  calc
    (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) =
        ∫ y : ℝ,
          ((Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) - 1) /
            (↑(-2 * Real.pi * t) * Complex.I)) * (g y : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        change fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ) =
          ((Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) - 1) /
            (↑(-2 * Real.pi * t) * Complex.I)) * (g y : ℂ)
        rw [fejerOscillatoryPrimitive_of_ne_zero (T * (x - y)) ht]
    _ = ∫ y : ℝ,
        (Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) *
            (g y : ℂ) - (g y : ℂ)) /
          (↑(-2 * Real.pi * t) * Complex.I) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by ring
    _ = (∫ y : ℝ,
        Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) *
          (g y : ℂ) - (g y : ℂ)) /
          (↑(-2 * Real.pi * t) * Complex.I) := by
      rw [integral_div]
    _ = ((∫ y : ℝ,
          Complex.exp (↑(-2 * Real.pi * (T * (x - y) * t)) * Complex.I) *
            (g y : ℂ)) - ∫ y : ℝ, (g y : ℂ)) /
          (↑(-2 * Real.pi * t) * Complex.I) := by
      congr 1
      exact integral_sub hphaseg hgc
    _ = _ := by
      rw [integral_signedDensity_phase, integral_complex_ofReal]

theorem integrable_fejerPrimitive_density_triangle_prod
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y)) (x T : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      (fejerOscillatoryPrimitive (T * (x - p.1)) p.2 * (g p.1 : ℂ)) *
        (triangleMultiplier p.2 : ℂ)) (volume.prod volume) := by
  have hbase : Integrable (fun y : ℝ ↦ x * g y - y * g y) :=
    (hg.const_mul x).sub hyg
  have hu : Integrable (fun y : ℝ ↦ T * (x - y) * g y) := by
    apply (hbase.const_mul T).congr
    exact Filter.Eventually.of_forall fun y ↦ by ring
  have hdom : Integrable (fun p : ℝ × ℝ ↦
      Complex.ofReal (T * (x - p.1) * g p.1) *
        (triangleMultiplier p.2 : ℂ)) (volume.prod volume) :=
    hu.ofReal.mul_prod triangleMultiplier_integrable_complex
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦
      (fejerOscillatoryPrimitive (T * (x - p.1)) p.2 * (g p.1 : ℂ)) *
        (triangleMultiplier p.2 : ℂ)) (volume.prod volume) := by
    have heq : (fun p : ℝ × ℝ ↦
        (fejerOscillatoryPrimitive (T * (x - p.1)) p.2 * (g p.1 : ℂ)) *
          (triangleMultiplier p.2 : ℂ)) =
      (fun p : ℝ × ℝ ↦
        (fejerOscillatoryPrimitiveFormula (T * (x - p.1)) p.2 * (g p.1 : ℂ)) *
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
    exact ((hformula.aestronglyMeasurable.mul hg.ofReal.aestronglyMeasurable.comp_fst).mul
      (Complex.continuous_ofReal.measurable.comp
        (continuous_triangleMultiplier.measurable.comp measurable_snd)).aestronglyMeasurable)
  apply hdom.mono hmeas
  exact Filter.Eventually.of_forall fun p ↦ by
    simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have htri : 0 ≤ triangleMultiplier p.2 := le_max_right _ _
    rw [abs_of_nonneg htri, abs_mul]
    gcongr
    exact norm_fejerOscillatoryPrimitive_le (T * (x - p.1)) p.2

theorem integral_cdf_fejerMeasure_mul_density_fourier
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y)) (x T : ℝ) :
    Complex.ofReal
        (∫ y : ℝ, cdf fejerMeasure (T * (x - y)) * g y) =
      (1 / 2) * Complex.ofReal (∫ y : ℝ, g y) +
        ∫ t : ℝ,
          (∫ y : ℝ,
            fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) *
              (triangleMultiplier t : ℂ) := by
  let P : ℝ → ℝ → ℂ := fun y t ↦
    (fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) *
      (triangleMultiplier t : ℂ)
  have hP : Integrable (Function.uncurry P) (volume.prod volume) := by
    change Integrable (fun p : ℝ × ℝ ↦
      (fejerOscillatoryPrimitive (T * (x - p.1)) p.2 * (g p.1 : ℂ)) *
        (triangleMultiplier p.2 : ℂ)) (volume.prod volume)
    exact integrable_fejerPrimitive_density_triangle_prod g hg hyg x T
  have hfirst : Integrable (fun y : ℝ ↦ (1 / 2 : ℂ) * (g y : ℂ)) :=
    hg.ofReal.const_mul (1 / 2 : ℂ)
  have hinner : Integrable (fun y : ℝ ↦ ∫ t : ℝ, P y t) := by
    simpa [Function.uncurry] using hP.integral_prod_left
  calc
    Complex.ofReal (∫ y : ℝ, cdf fejerMeasure (T * (x - y)) * g y) =
        ∫ y : ℝ,
          (cdf fejerMeasure (T * (x - y)) : ℂ) * (g y : ℂ) := by
      symm
      calc
        (∫ y : ℝ,
            (cdf fejerMeasure (T * (x - y)) : ℂ) * (g y : ℂ)) =
            ∫ y : ℝ,
              Complex.ofReal (cdf fejerMeasure (T * (x - y)) * g y) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y ↦ by push_cast; rfl
        _ = Complex.ofReal
              (∫ y : ℝ, cdf fejerMeasure (T * (x - y)) * g y) :=
          integral_complex_ofReal
    _ = ∫ y : ℝ, ((1 / 2 : ℂ) * (g y : ℂ) + ∫ t : ℝ, P y t) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        change (cdf fejerMeasure (T * (x - y)) : ℂ) * (g y : ℂ) =
          (1 / 2 : ℂ) * (g y : ℂ) + ∫ t : ℝ, P y t
        rw [cdf_fejerMeasure_fourier]
        rw [add_mul]
        congr 1
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t ↦ by
          simp [P]
          ring
    _ = (∫ y : ℝ, (1 / 2 : ℂ) * (g y : ℂ)) +
        ∫ y : ℝ, (∫ t : ℝ, P y t) := by
      rw [integral_add hfirst hinner]
    _ = (1 / 2) * Complex.ofReal (∫ y : ℝ, g y) +
        ∫ y : ℝ, (∫ t : ℝ, P y t) := by
      rw [integral_const_mul, integral_complex_ofReal]
    _ = (1 / 2) * Complex.ofReal (∫ y : ℝ, g y) +
        ∫ t : ℝ, (∫ y : ℝ, P y t) := by
      congr 1
      simpa [Function.uncurry] using integral_integral_swap hP
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t ↦ by
        change (∫ y : ℝ,
            (fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) *
              (triangleMultiplier t : ℂ)) =
          (∫ y : ℝ,
            fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) *
              (triangleMultiplier t : ℂ)
        rw [integral_mul_const]

/-- Exact Fourier identity for Fejer smoothing against an integrable signed
density of total mass one.  No positivity hypothesis is imposed on `g`. -/
theorem smoothCDF_fejerMeasure_sub_signedDensity_fourier
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y))
    (hmass : ∫ y : ℝ, g y = 1)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Complex.ofReal (smoothCDF fejerMeasure T μ x -
        smoothFunction fejerMeasure T (signedDensityCDF g) x) =
      ∫ t : ℝ,
        (Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
            (charFun μ (2 * Real.pi * T * t) -
              signedDensityFourier g (2 * Real.pi * T * t)) /
            (↑(-2 * Real.pi * t) * Complex.I)) *
          (triangleMultiplier t : ℂ) := by
  rw [smoothCDF_eq_integral_kernel_cdf fejerMeasure μ hT,
    smoothFunction_signedDensityCDF_eq fejerMeasure g hg hT]
  have hprodμ := integrable_fejerPrimitive_triangle_prod μ hμ x T
  have hprodg := integrable_fejerPrimitive_density_triangle_prod g hg hyg x T
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
  have hintg : Integrable (fun t : ℝ ↦
      (∫ y : ℝ,
        fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) *
          (triangleMultiplier t : ℂ)) := by
    apply hprodg.integral_prod_right.congr
    exact Filter.Eventually.of_forall fun t ↦ by
      change (∫ y : ℝ,
          (fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) *
            (triangleMultiplier t : ℂ)) =
        (∫ y : ℝ,
          fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) *
            (triangleMultiplier t : ℂ)
      rw [integral_mul_const]
  rw [Complex.ofReal_sub,
    integral_cdf_fejerMeasure_fourier μ hμ x T,
    integral_cdf_fejerMeasure_mul_density_fourier g hg hyg x T,
    hmass, Complex.ofReal_one]
  let Aμ : ℝ → ℂ := fun t ↦
    (∫ y : ℝ, fejerOscillatoryPrimitive (T * (x - y)) t ∂μ) *
      (triangleMultiplier t : ℂ)
  let Ag : ℝ → ℂ := fun t ↦
    (∫ y : ℝ,
      fejerOscillatoryPrimitive (T * (x - y)) t * (g y : ℂ)) *
        (triangleMultiplier t : ℂ)
  change (1 / 2 + ∫ t : ℝ, Aμ t) -
      ((1 / 2) * 1 + ∫ t : ℝ, Ag t) = _
  have hAμ : Integrable Aμ := by simpa [Aμ] using hintμ
  have hAg : Integrable Ag := by simpa [Ag] using hintg
  calc
    (1 / 2 + ∫ t : ℝ, Aμ t) -
        ((1 / 2) * 1 + ∫ t : ℝ, Ag t) =
        (∫ t : ℝ, Aμ t) - ∫ t : ℝ, Ag t := by ring
    _ = ∫ t : ℝ, (Aμ t - Ag t) := (integral_sub hAμ hAg).symm
    _ = _ := by
      have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := Measure.ae_ne volume 0
      apply integral_congr_ae
      filter_upwards [hne] with t ht
      dsimp [Aμ, Ag]
      rw [integral_fejerOscillatoryPrimitive μ x T ht,
        integral_fejerOscillatoryPrimitive_mul_density g hg x T ht,
        hmass, Complex.ofReal_one]
      ring

/-- The Fourier integrand for smoothing a probability CDF against a signed
density comparator. -/
def fejerSignedSmoothingFourierIntegrand
    (μ : Measure ℝ) (g : ℝ → ℝ) (T x t : ℝ) : ℂ :=
  (Complex.exp (↑(-2 * Real.pi * (T * x * t)) * Complex.I) *
      (charFun μ ((2 * Real.pi * T) * t) -
        signedDensityFourier g ((2 * Real.pi * T) * t)) /
      (↑(-2 * Real.pi * t) * Complex.I)) *
    (triangleMultiplier t : ℂ)

theorem norm_fejerSignedSmoothingFourierIntegrand_le
    (μ : Measure ℝ) (g : ℝ → ℝ)
    {T : ℝ} (hT : 0 < T) (x t : ℝ) :
    ‖fejerSignedSmoothingFourierIntegrand μ g T x t‖ ≤
      (Icc (-1) 1).indicator
        (fun s : ℝ ↦ T * fourierQuotientError (charFun μ)
          (signedDensityFourier g) ((2 * Real.pi * T) * s)) t := by
  by_cases htmem : t ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem htmem]
    by_cases ht0 : t = 0
    · subst t
      simp [fejerSignedSmoothingFourierIntegrand, fourierQuotientError]
    · have habst : 0 < |t| := abs_pos.mpr ht0
      have hc : 0 < 2 * Real.pi * T := by positivity
      have htri0 : 0 ≤ triangleMultiplier t := le_max_right _ _
      have htri1 : triangleMultiplier t ≤ 1 := by
        rw [triangleMultiplier]
        exact max_le (by linarith [abs_nonneg t]) zero_le_one
      calc
        ‖fejerSignedSmoothingFourierIntegrand μ g T x t‖ =
            (‖charFun μ ((2 * Real.pi * T) * t) -
                signedDensityFourier g ((2 * Real.pi * T) * t)‖ /
              (2 * Real.pi * |t|)) * triangleMultiplier t := by
          simp only [fejerSignedSmoothingFourierIntegrand, Complex.norm_mul,
            norm_div, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, abs_of_nonneg htri0]
          rw [Complex.norm_exp]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self,
            Real.exp_zero, one_mul]
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
          ring
        _ ≤ ‖charFun μ ((2 * Real.pi * T) * t) -
                signedDensityFourier g ((2 * Real.pi * T) * t)‖ /
              (2 * Real.pi * |t|) := by
          exact mul_le_of_le_one_right (by positivity) htri1
        _ = T * fourierQuotientError (charFun μ)
              (signedDensityFourier g) ((2 * Real.pi * T) * t) := by
          rw [fourierQuotientError, abs_mul, abs_of_pos hc]
          field_simp [ne_of_gt hT, ne_of_gt Real.pi_pos, ht0]
  · rw [indicator_of_notMem htmem]
    have hzero : triangleMultiplier t = 0 := by
      simp only [mem_Icc, not_and_or, not_le] at htmem
      rcases htmem with ht | ht
      · exact triangleMultiplier_eq_zero_of_lt_neg_one ht
      · exact triangleMultiplier_eq_zero_of_one_lt ht
    simp [fejerSignedSmoothingFourierIntegrand, hzero]

/-- Actual Fejer Fourier estimate for a probability CDF versus a signed
density comparator. -/
theorem abs_smoothCDF_fejerMeasure_sub_signedDensity_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y))
    (hmass : ∫ y : ℝ, g y = 1)
    {T : ℝ} (hT : 0 < T)
    (hint : IntegrableOn
      (fourierQuotientError (charFun μ) (signedDensityFourier g))
      (Icc (-(2 * Real.pi * T)) (2 * Real.pi * T)))
    (x : ℝ) :
    |smoothCDF fejerMeasure T μ x -
        smoothFunction fejerMeasure T (signedDensityCDF g) x| ≤
      (1 / (2 * Real.pi)) *
        truncatedFourierDiscrepancy (charFun μ)
          (signedDensityFourier g) (2 * Real.pi * T) := by
  let U : ℝ → ℝ := fun t ↦
    (Icc (-1) 1).indicator
      (fun s : ℝ ↦ T * fourierQuotientError (charFun μ)
        (signedDensityFourier g) ((2 * Real.pi * T) * s)) t
  have hUon := integrableOn_unitScale_fourierQuotient hT hint
  have hU : Integrable U := by
    rw [show U = (Icc (-1) 1).indicator
        (fun s : ℝ ↦ T * fourierQuotientError (charFun μ)
          (signedDensityFourier g) ((2 * Real.pi * T) * s)) by rfl,
      integrable_indicator_iff measurableSet_Icc]
    exact hUon
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  rw [smoothCDF_fejerMeasure_sub_signedDensity_fourier μ hμ g hg hyg hmass hT]
  change ‖∫ t : ℝ, fejerSignedSmoothingFourierIntegrand μ g T x t‖ ≤ _
  calc
    ‖∫ t : ℝ, fejerSignedSmoothingFourierIntegrand μ g T x t‖ ≤
        ∫ t : ℝ, ‖fejerSignedSmoothingFourierIntegrand μ g T x t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, U t := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
      · exact hU
      · exact Filter.Eventually.of_forall fun t ↦
          norm_fejerSignedSmoothingFourierIntegrand_le μ g hT x t
    _ = ∫ t : ℝ in Icc (-1) 1,
        T * fourierQuotientError (charFun μ) (signedDensityFourier g)
          ((2 * Real.pi * T) * t) := by
      rw [show U = (Icc (-1) 1).indicator
          (fun s : ℝ ↦ T * fourierQuotientError (charFun μ)
            (signedDensityFourier g) ((2 * Real.pi * T) * s)) by rfl,
        integral_indicator measurableSet_Icc]
    _ = (1 / (2 * Real.pi)) *
        truncatedFourierDiscrepancy (charFun μ)
          (signedDensityFourier g) (2 * Real.pi * T) := by
      exact integral_unitScale_fourierQuotient hT hint

/-- Signed-density version of the proved Fejer--Esseen inequality, in kernel
scale.  The comparator may be nonmonotone and need not be nonnegative.

The two explicit finiteness assumptions are logically separate from the
Fourier calculation: `hGint` permits the distributional smoothing argument,
and `hbound` certifies that the CDF supremum is finite. -/
theorem cdfComparatorDistance_signedDensity_le_fejer_esseen_kernelScale
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y))
    (hmass : ∫ y : ℝ, g y = 1)
    {T m B : ℝ} (hT : 0 < T) (hm : 0 ≤ m)
    (hlip : HasRealLipschitzBound (signedDensityCDF g) m)
    (hGint : ∀ x, Integrable
      (fun z ↦ signedDensityCDF g (x - z / T)) fejerMeasure)
    (hbound : ∀ x, |cdf μ x - signedDensityCDF g x| ≤ B)
    (hint : IntegrableOn
      (fourierQuotientError (charFun μ) (signedDensityFourier g))
      (Icc (-(2 * Real.pi * T)) (2 * Real.pi * T))) :
    cdfComparatorDistance μ (signedDensityCDF g) ≤
      (1 / Real.pi) *
        truncatedFourierDiscrepancy (charFun μ)
          (signedDensityFourier g) (2 * Real.pi * T) +
      32 * m / T := by
  have hsmooth : ∀ x,
      |smoothCDF fejerMeasure T μ x -
          smoothFunction fejerMeasure T (signedDensityCDF g) x| ≤
        (1 / (2 * Real.pi)) *
          truncatedFourierDiscrepancy (charFun μ)
            (signedDensityFourier g) (2 * Real.pi * T) :=
    fun x ↦ abs_smoothCDF_fejerMeasure_sub_signedDensity_le
      μ hμ g hg hyg hmass hT hint x
  have h := cdfComparatorDistance_le_of_kernel_smoothing_tail_quarter
    fejerMeasure μ (signedDensityCDF g)
    (T := T) (a := 8) (q := 1 / 4) (m := m)
    (δ := (1 / (2 * Real.pi)) *
      truncatedFourierDiscrepancy (charFun μ)
        (signedDensityFourier g) (2 * Real.pi * T))
    (B := B) hT (by norm_num) (by norm_num) hm
    fejerMeasure_tail_eight_le_quarter hlip hGint hbound hsmooth
  calc
    cdfComparatorDistance μ (signedDensityCDF g) ≤
        2 * ((1 / (2 * Real.pi)) *
          truncatedFourierDiscrepancy (charFun μ)
            (signedDensityFourier g) (2 * Real.pi * T)) +
        4 * m * 8 / T := h
    _ = (1 / Real.pi) *
          truncatedFourierDiscrepancy (charFun μ)
            (signedDensityFourier g) (2 * Real.pi * T) +
        32 * m / T := by
      field_simp [ne_of_gt Real.pi_pos]
      ring

/-- Frequency-cutoff form of the signed Fejer--Esseen inequality.  This is
the reusable interface for a first-order Edgeworth density. -/
theorem cdfComparatorDistance_signedDensity_le_fejer_esseen
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y))
    (hmass : ∫ y : ℝ, g y = 1)
    {S m B : ℝ} (hS : 0 < S) (hm : 0 ≤ m)
    (hlip : HasRealLipschitzBound (signedDensityCDF g) m)
    (hGint : ∀ x, Integrable
      (fun z ↦ signedDensityCDF g
        (x - z / (S / (2 * Real.pi)))) fejerMeasure)
    (hbound : ∀ x, |cdf μ x - signedDensityCDF g x| ≤ B)
    (hint : IntegrableOn
      (fourierQuotientError (charFun μ) (signedDensityFourier g))
      (Icc (-S) S)) :
    cdfComparatorDistance μ (signedDensityCDF g) ≤
      (1 / Real.pi) *
        truncatedFourierDiscrepancy (charFun μ)
          (signedDensityFourier g) S +
      64 * Real.pi * m / S := by
  let T : ℝ := S / (2 * Real.pi)
  have hT : 0 < T := by dsimp [T]; positivity
  have hcut : 2 * Real.pi * T = S := by
    dsimp [T]
    field_simp [ne_of_gt Real.pi_pos]
  have hint' : IntegrableOn
      (fourierQuotientError (charFun μ) (signedDensityFourier g))
      (Icc (-(2 * Real.pi * T)) (2 * Real.pi * T)) := by
    simpa [hcut] using hint
  have hGint' : ∀ x, Integrable
      (fun z ↦ signedDensityCDF g (x - z / T)) fejerMeasure := by
    simpa [T] using hGint
  have h :=
    cdfComparatorDistance_signedDensity_le_fejer_esseen_kernelScale
      μ hμ g hg hyg hmass hT hm hlip hGint' hbound hint'
  rw [hcut] at h
  apply h.trans_eq
  dsimp [T]
  field_simp [ne_of_gt Real.pi_pos, ne_of_gt hS]
  ring

end

end LogdetLean
