import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Tactic
/-!
# The real-line Fejer smoothing kernel

This file constructs the positive band-limited kernel used in the Fourier
half of Esseen's smoothing argument.  We use the Fourier convention from
mathlib, with phase `exp (-2 * pi * I * x * xi)`.

The construction is the real-line analogue of the Fejer kernel.  Its density
is `sinc (pi*x)^2`; it is the squared Fourier transform of the indicator of
`[-1/2,1/2]`.  The compactly supported triangular multiplier will be proved
below from Fourier inversion, rather than assumed.
-/

namespace LogdetLean

open MeasureTheory Set Real Convolution FourierTransform
open scoped Real FourierTransform ComplexConjugate

noncomputable section

/-- The complex indicator of the interval `[-1/2,1/2]`. -/
def fejerBox (x : ℝ) : ℂ :=
  (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator (fun _ ↦ (1 : ℂ)) x

theorem fejerBox_integrable : Integrable fejerBox := by
  change Integrable
    ((Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator (fun _ ↦ (1 : ℂ)))
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by simp [Real.volume_Icc])

theorem fejerBox_eq_one_of_mem {x : ℝ}
    (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) : fejerBox x = 1 := by
  exact indicator_of_mem hx _

theorem fejerBox_eq_zero_of_not_mem {x : ℝ}
    (hx : x ∉ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) : fejerBox x = 0 := by
  exact indicator_of_notMem hx _

/-- The Fourier transform of the unit box is the sinc function. -/
theorem fourier_fejerBox (xi : ℝ) :
    fourier fejerBox xi = Real.sinc (Real.pi * xi) := by
  rw [Real.fourier_eq']
  simp only [Real.inner_apply, smul_eq_mul]
  have hindicator :
      (fun v : ℝ ↦
          Complex.exp (↑(-2 * Real.pi * (v * xi)) * Complex.I) * fejerBox v) =
        (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator
          (fun v ↦ Complex.exp (↑(-2 * Real.pi * (v * xi)) * Complex.I)) := by
    funext v
    by_cases hv : v ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
    · simp only [fejerBox]
      rw [indicator_of_mem hv, indicator_of_mem hv, mul_one]
    · simp only [fejerBox]
      rw [indicator_of_notMem hv, indicator_of_notMem hv, mul_zero]
  rw [hindicator, integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  by_cases hxi : xi = 0
  · norm_num [hxi, Real.sinc_zero]
  have hc : -(2 * Real.pi * xi) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos)) hxi)
  have hsinc := integral_exp_mul_I_eq_sinc (Real.pi * xi)
  have hrewrite :
      (fun x : ℝ ↦
          Complex.exp (↑(-2 * Real.pi * (x * xi)) * Complex.I)) =
        (fun x : ℝ ↦
          Complex.exp (↑((-(2 * Real.pi * xi)) * x) * Complex.I)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [hrewrite]
  rw [intervalIntegral.integral_comp_mul_left
    (fun t : ℝ ↦ Complex.exp (t * Complex.I)) hc]
  rw [show (-(2 * Real.pi * xi)) * (-(1 / 2 : ℝ)) = Real.pi * xi by ring]
  rw [show (-(2 * Real.pi * xi)) * (1 / 2 : ℝ) = -(Real.pi * xi) by ring]
  rw [intervalIntegral.integral_symm, hsinc]
  rw [Complex.real_smul, Complex.ofReal_inv]
  have hfactor :
      -(2 * (↑(Real.pi * xi) : ℂ) * ↑(Real.sinc (Real.pi * xi))) =
        (↑(-(2 * Real.pi * xi)) : ℂ) * ↑(Real.sinc (Real.pi * xi)) := by
    push_cast
    ring
  rw [hfactor, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc), one_mul]

/-- The nonnegative real-line Fejer density. -/
def fejerDensity (x : ℝ) : ℝ :=
  Real.sinc (Real.pi * x) ^ 2

theorem fejerDensity_nonneg (x : ℝ) : 0 ≤ fejerDensity x := by
  exact sq_nonneg _

theorem continuous_fejerDensity : Continuous fejerDensity := by
  exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

/-- The elementary `1/x²` tail bound.  We deliberately discard the extra
factor `pi²`; the coarser estimate makes the later formal arithmetic much
lighter while retaining the `O(1/T)` smoothing remainder. -/
theorem fejerDensity_le_inv_sq {x : ℝ} (hx : x ≠ 0) :
    fejerDensity x ≤ (x ^ 2)⁻¹ := by
  have hpix : Real.pi * x ≠ 0 := mul_ne_zero (ne_of_gt Real.pi_pos) hx
  have habs0 : |Real.sinc (Real.pi * x)| ≤ |Real.pi * x|⁻¹ := by
    rw [Real.sinc_of_ne_zero hpix, abs_div]
    simpa [one_div] using
      div_le_div_of_nonneg_right (abs_sin_le_one (Real.pi * x)) (abs_nonneg (Real.pi * x))
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hpixabs : |x| ≤ |Real.pi * x| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
    nlinarith [abs_nonneg x]
  have habs : |Real.sinc (Real.pi * x)| ≤ |x|⁻¹ :=
    habs0.trans (inv_anti₀ hxabs hpixabs)
  have hsquare : |Real.sinc (Real.pi * x)| ^ 2 ≤ |x|⁻¹ ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (inv_nonneg.mpr (abs_nonneg _))).2 habs
  simpa [fejerDensity, sq_abs, inv_pow] using hsquare

/-- A global integrable envelope for the Fejer density. -/
theorem fejerDensity_le_two_inv_one_add_sq (x : ℝ) :
    fejerDensity x ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have hden : 0 < 1 + x ^ 2 := by positivity
  by_cases hsmall : |x| ≤ 1
  · have hsinc := Real.abs_sinc_le_one (Real.pi * x)
    have hf_one : fejerDensity x ≤ 1 := by
      rw [fejerDensity, ← sq_abs]
      simpa using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hsinc
    have hx2 : x ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    apply hf_one.trans
    rw [le_mul_inv_iff₀ hden]
    nlinarith
  · have hxlarge : 1 < |x| := lt_of_not_ge hsmall
    have hx : x ≠ 0 := by
      intro hx0
      subst x
      norm_num at hxlarge
    have htail := fejerDensity_le_inv_sq hx
    have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hx2one : 1 ≤ x ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    apply htail.trans
    have hfrac : 1 / x ^ 2 ≤ 2 / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ hx2pos hden]
      nlinarith
    simpa [div_eq_mul_inv] using hfrac

theorem fejerDensity_integrable : Integrable fejerDensity := by
  apply (integrable_inv_one_add_sq.const_mul 2).mono
  · exact continuous_fejerDensity.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerDensity_nonneg x),
        Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * (1 + x ^ 2)⁻¹)]
      exact fejerDensity_le_two_inv_one_add_sq x

/-- The compactly supported triangular Fourier multiplier. -/
def triangleMultiplier (x : ℝ) : ℝ :=
  max (1 - |x|) 0

theorem continuous_triangleMultiplier : Continuous triangleMultiplier := by
  exact ((continuous_const.sub continuous_abs).max continuous_const)

theorem triangleMultiplier_eq_zero_of_lt_neg_one {x : ℝ} (hx : x < -1) :
    triangleMultiplier x = 0 := by
  rw [triangleMultiplier, abs_of_neg (by linarith), max_eq_right]
  linarith

theorem triangleMultiplier_eq_add_one {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 0) :
    triangleMultiplier x = 1 + x := by
  rw [triangleMultiplier, abs_of_nonpos hx1, max_eq_left]
  · ring
  · linarith

theorem triangleMultiplier_eq_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    triangleMultiplier x = 1 - x := by
  rw [triangleMultiplier, abs_of_nonneg hx0, max_eq_left]
  linarith

theorem triangleMultiplier_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    triangleMultiplier x = 0 := by
  rw [triangleMultiplier, abs_of_pos (by linarith), max_eq_right]
  linarith

/-- The convolution of two unit boxes is the triangle function.  This is the
elementary overlap-length computation underlying the Fejer transform. -/
theorem convolution_fejerBox (x : ℝ) :
    (fejerBox ⋆[ContinuousLinearMap.mul ℂ ℂ] fejerBox) x =
      (triangleMultiplier x : ℂ) := by
  rw [convolution_mul]
  rcases lt_or_ge x (-1) with hx | hx
  · have hzero :
        (fun t : ℝ ↦ fejerBox t * fejerBox (x - t)) = fun _ ↦ (0 : ℂ) := by
      funext t
      by_cases ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
      · by_cases hu : x - t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
        · exfalso
          linarith [ht.1, hu.1]
        · rw [fejerBox_eq_one_of_mem ht, fejerBox_eq_zero_of_not_mem hu, mul_zero]
      · rw [fejerBox_eq_zero_of_not_mem ht, zero_mul]
    rw [hzero, integral_zero, triangleMultiplier_eq_zero_of_lt_neg_one hx]
    simp
  · rcases le_or_gt x 0 with hx0 | hx0
    · have hfun :
          (fun t : ℝ ↦ fejerBox t * fejerBox (x - t)) =
            (Icc (-(1 / 2 : ℝ)) (x + 1 / 2)).indicator (fun _ ↦ (1 : ℂ)) := by
        funext t
        by_cases ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
        · by_cases hu : x - t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
          · have hi : t ∈ Icc (-(1 / 2 : ℝ)) (x + 1 / 2) := ⟨ht.1, by linarith [hu.1]⟩
            rw [fejerBox_eq_one_of_mem ht, fejerBox_eq_one_of_mem hu, mul_one,
              indicator_of_mem hi]
          · have hi : t ∉ Icc (-(1 / 2 : ℝ)) (x + 1 / 2) := by
              intro hi
              apply hu
              constructor
              · linarith [hi.2]
              · linarith [ht.1]
            rw [fejerBox_eq_one_of_mem ht, fejerBox_eq_zero_of_not_mem hu, mul_zero,
              indicator_of_notMem hi]
        · have hi : t ∉ Icc (-(1 / 2 : ℝ)) (x + 1 / 2) := by
            intro hi
            exact ht ⟨hi.1, hi.2.trans (by linarith)⟩
          rw [fejerBox_eq_zero_of_not_mem ht, zero_mul, indicator_of_notMem hi]
      rw [hfun, integral_indicator measurableSet_Icc]
      rw [integral_const, measureReal_restrict_apply MeasurableSet.univ]
      simp only [univ_inter, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ (x + 1 / 2) - (-(1 / 2 : ℝ)))]
      rw [triangleMultiplier_eq_add_one hx hx0]
      rw [Complex.real_smul, mul_one]
      push_cast
      ring
    · rcases le_or_gt x 1 with hx1 | hx1
      · have hfun :
            (fun t : ℝ ↦ fejerBox t * fejerBox (x - t)) =
              (Icc (x - 1 / 2) (1 / 2 : ℝ)).indicator (fun _ ↦ (1 : ℂ)) := by
          funext t
          by_cases ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
          · by_cases hu : x - t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
            · have hi : t ∈ Icc (x - 1 / 2) (1 / 2 : ℝ) := ⟨by linarith [hu.2], ht.2⟩
              rw [fejerBox_eq_one_of_mem ht, fejerBox_eq_one_of_mem hu, mul_one,
                indicator_of_mem hi]
            · have hi : t ∉ Icc (x - 1 / 2) (1 / 2 : ℝ) := by
                intro hi
                apply hu
                constructor
                · linarith [ht.2]
                · linarith [hi.1]
              rw [fejerBox_eq_one_of_mem ht, fejerBox_eq_zero_of_not_mem hu, mul_zero,
                indicator_of_notMem hi]
          · have hi : t ∉ Icc (x - 1 / 2) (1 / 2 : ℝ) := by
              intro hi
              exact ht ⟨(by linarith [hi.1]), hi.2⟩
            rw [fejerBox_eq_zero_of_not_mem ht, zero_mul, indicator_of_notMem hi]
        rw [hfun, integral_indicator measurableSet_Icc]
        rw [integral_const, measureReal_restrict_apply MeasurableSet.univ]
        simp only [univ_inter, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ (1 / 2 : ℝ) - (x - 1 / 2))]
        rw [triangleMultiplier_eq_one_sub hx0.le hx1]
        rw [Complex.real_smul, mul_one]
        push_cast
        ring
      · have hzero :
            (fun t : ℝ ↦ fejerBox t * fejerBox (x - t)) = fun _ ↦ (0 : ℂ) := by
          funext t
          by_cases ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
          · by_cases hu : x - t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
            · exfalso
              linarith [ht.2, hu.2]
            · rw [fejerBox_eq_one_of_mem ht, fejerBox_eq_zero_of_not_mem hu, mul_zero]
          · rw [fejerBox_eq_zero_of_not_mem ht, zero_mul]
        rw [hzero, integral_zero, triangleMultiplier_eq_zero_of_one_lt hx1]
        simp

theorem triangleMultiplier_integrable_complex :
    Integrable (fun x : ℝ ↦ (triangleMultiplier x : ℂ)) := by
  have hconv : Integrable
      (fejerBox ⋆[ContinuousLinearMap.mul ℂ ℂ] fejerBox) :=
    fejerBox_integrable.integrable_convolution
      (L := ContinuousLinearMap.mul ℂ ℂ) fejerBox_integrable
  apply hconv.congr
  exact Filter.Eventually.of_forall fun x ↦ convolution_fejerBox x

theorem triangleMultiplier_integrable : Integrable triangleMultiplier := by
  have h := triangleMultiplier_integrable_complex.re
  simpa using h

/-- Fourier transform of the triangle: the squared sinc density. -/
theorem fourier_triangleMultiplier (xi : ℝ) :
    fourier (fun x : ℝ ↦ (triangleMultiplier x : ℂ)) xi =
      (fejerDensity xi : ℂ) := by
  calc
    fourier (fun x : ℝ ↦ (triangleMultiplier x : ℂ)) xi =
        fourier (fejerBox ⋆[ContinuousLinearMap.mul ℂ ℂ] fejerBox) xi := by
          apply Real.fourier_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ (convolution_fejerBox x).symm
    _ = fourier fejerBox xi * fourier fejerBox xi :=
      Real.fourier_mul_convolution_eq fejerBox_integrable fejerBox_integrable xi
    _ = (fejerDensity xi : ℂ) := by
      rw [fourier_fejerBox]
      simp [fejerDensity, pow_two]

theorem fourier_triangleMultiplier_integrable :
    Integrable (fourier (fun x : ℝ ↦ (triangleMultiplier x : ℂ))) := by
  apply fejerDensity_integrable.ofReal.congr
  exact Filter.Eventually.of_forall fun x ↦ (fourier_triangleMultiplier x).symm

/-- The inverse Fourier transform of the Fejer density is exactly the
triangular multiplier.  In probability normalization this says that the
characteristic function is supported on `[-2*pi,2*pi]`. -/
theorem fourierInv_fejerDensity (xi : ℝ) :
    fourierInv (fun x : ℝ ↦ (fejerDensity x : ℂ)) xi =
      (triangleMultiplier xi : ℂ) := by
  have hinv := triangleMultiplier_integrable_complex.fourierInv_fourier_eq
    fourier_triangleMultiplier_integrable
    ((Complex.continuous_ofReal.comp continuous_triangleMultiplier :
      Continuous (fun x : ℝ ↦ (triangleMultiplier x : ℂ))).continuousAt :
      ContinuousAt (fun x : ℝ ↦ (triangleMultiplier x : ℂ)) xi)
  rw [show fourier (fun x : ℝ ↦ (triangleMultiplier x : ℂ)) =
      (fun x : ℝ ↦ (fejerDensity x : ℂ)) by
        funext x
        exact fourier_triangleMultiplier x] at hinv
  exact hinv

/-- The Fejer density has total mass one. -/
theorem integral_fejerDensity : ∫ x : ℝ, fejerDensity x = 1 := by
  have h := fourierInv_fejerDensity 0
  rw [Real.fourierInv_eq] at h
  have hc : ((∫ x : ℝ, fejerDensity x : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    simpa [triangleMultiplier] using h
  exact_mod_cast hc

theorem fejerDensity_neg (x : ℝ) : fejerDensity (-x) = fejerDensity x := by
  simp [fejerDensity, Real.sinc_neg]

/-- The positive tail of the Fejer density is at most `1/a`.  The true
constant is smaller; this deliberately coarse form is enough for an explicit
`O(1/T)` smoothing remainder. -/
theorem integral_Ioi_fejerDensity_le_inv {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ in Ioi a, fejerDensity x ≤ a⁻¹ := by
  have hdom : IntegrableOn (fun x : ℝ ↦ (x ^ 2)⁻¹) (Ioi a) := by
    have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha
    apply h.congr_fun
    · intro x hx
      norm_num [Real.rpow_neg_natCast, zpow_neg]
    · exact measurableSet_Ioi
  calc
    (∫ x : ℝ in Ioi a, fejerDensity x) ≤
        ∫ x : ℝ in Ioi a, (x ^ 2)⁻¹ := by
      apply integral_mono_ae fejerDensity_integrable.integrableOn hdom
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact fejerDensity_le_inv_sq (ne_of_gt (ha.trans hx))
    _ = a⁻¹ := by
      have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha
      norm_num [Real.rpow_neg_natCast, zpow_neg] at h
      simpa [Real.rpow_neg_one] using h

theorem integral_Iio_fejerDensity_eq_Ioi (a : ℝ) :
    (∫ x : ℝ in Iio (-a), fejerDensity x) =
      ∫ x : ℝ in Ioi a, fejerDensity x := by
  calc
    (∫ x : ℝ in Iio (-a), fejerDensity x) =
        ∫ x : ℝ in Iic (-a), fejerDensity x := integral_Iic_eq_integral_Iio.symm
    _ = ∫ x : ℝ in Ioi a, fejerDensity (-x) :=
      (integral_comp_neg_Ioi a fejerDensity).symm
    _ = ∫ x : ℝ in Ioi a, fejerDensity x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact fejerDensity_neg x

/-- The probability measure having the Fejer density. -/
def fejerMeasure : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (fejerDensity x))

instance fejerMeasure_isProbabilityMeasure : IsProbabilityMeasure fejerMeasure where
  measure_univ := by
    rw [fejerMeasure, withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal fejerDensity_integrable
      (Filter.Eventually.of_forall fejerDensity_nonneg)]
    rw [integral_fejerDensity]
    norm_num

theorem fejerMeasure_real_apply {s : Set ℝ} (hs : MeasurableSet s) :
    fejerMeasure.real s = ∫ x in s, fejerDensity x := by
  rw [measureReal_def, fejerMeasure, withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal fejerDensity_integrable.integrableOn
    (Filter.Eventually.of_forall fejerDensity_nonneg)]
  rw [ENNReal.toReal_ofReal]
  exact setIntegral_nonneg_of_ae
    (Filter.Eventually.of_forall fejerDensity_nonneg)

/-- The Fejer probability kernel puts at most `2/a` mass outside `[-a,a]`. -/
theorem fejerMeasure_tail_le {a : ℝ} (ha : 0 < a) :
    fejerMeasure.real (Icc (-a) a)ᶜ ≤ 2 * a⁻¹ := by
  have hset : (Icc (-a) a)ᶜ = Iio (-a) ∪ Ioi a := by
    ext x
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  rw [fejerMeasure_real_apply measurableSet_Icc.compl, hset,
    setIntegral_union (by grind) measurableSet_Ioi
      fejerDensity_integrable.integrableOn fejerDensity_integrable.integrableOn,
    integral_Iio_fejerDensity_eq_Ioi]
  linarith [integral_Ioi_fejerDensity_le_inv ha]

theorem fejerMeasure_tail_eight_le_quarter :
    fejerMeasure.real (Icc (-(8 : ℝ)) 8)ᶜ ≤ 1 / 4 := by
  have h := fejerMeasure_tail_le (a := (8 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Exact characteristic function of the Fejer probability measure.  The
probability convention uses `exp (I*t*x)`, so the triangle is evaluated at
`t/(2*pi)`. -/
theorem charFun_fejerMeasure (t : ℝ) :
    charFun fejerMeasure t =
      (triangleMultiplier (t / (2 * Real.pi)) : ℂ) := by
  rw [charFun_eq_integral_probChar, fejerMeasure,
    integral_withDensity_eq_integral_toReal_smul
      continuous_fejerDensity.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [← fourierInv_fejerDensity (t / (2 * Real.pi)), Real.fourierInv_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [ENNReal.toReal_ofReal (fejerDensity_nonneg x), Complex.real_smul,
      probChar_apply, Real.inner_apply, smul_eq_mul]
    rw [show 2 * Real.pi * (x * (t / (2 * Real.pi))) = x * t by
      field_simp [ne_of_gt Real.pi_pos]]
    ring

theorem charFun_fejerMeasure_eq_zero_of_two_pi_le_abs {t : ℝ}
    (ht : 2 * Real.pi ≤ |t|) : charFun fejerMeasure t = 0 := by
  rw [charFun_fejerMeasure]
  have htwo : 0 < 2 * Real.pi := by positivity
  have habs : 1 ≤ |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos htwo]
    exact (le_div_iff₀ htwo).2 (by simpa using ht)
  rw [triangleMultiplier, max_eq_right]
  · norm_num
  · linarith

end

end LogdetLean
