import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.CDF
import Mathlib.Tactic
import LogdetLean.FejerKernel
/-!
# A finite-interval inversion formula for the Fejer CDF

The point of this file is to prove the analytic identity used in Esseen
smoothing without invoking an unformalized CDF inversion theorem.  We first
write the Fejer CDF as an integral of its density from zero, then insert the
already proved compactly supported Fourier representation and apply Fubini on
a finite interval.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set Real FourierTransform
open scoped Real FourierTransform ComplexConjugate Interval

noncomputable section

theorem cdf_fejerMeasure_zero : cdf fejerMeasure 0 = 1 / 2 := by
  rw [cdf_eq_real, fejerMeasure_real_apply measurableSet_Iic]
  have heven : (∫ x : ℝ in Ioi 0, fejerDensity x) =
      ∫ x : ℝ in Iic 0, fejerDensity x := by
    calc
      (∫ x : ℝ in Ioi 0, fejerDensity x) =
          ∫ x : ℝ in Ioi 0, fejerDensity (-x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        exact (fejerDensity_neg x).symm
      _ = ∫ x : ℝ in Iic 0, fejerDensity x := by
        simpa only [neg_zero] using integral_comp_neg_Ioi 0 fejerDensity
  have hsplit := integral_add_compl (s := Iic (0 : ℝ))
    measurableSet_Iic fejerDensity_integrable
  have hsum : (∫ x : ℝ in Iic 0, fejerDensity x) +
      ∫ x : ℝ in Ioi 0, fejerDensity x = 1 := by
    simpa [integral_fejerDensity] using hsplit
  linarith

/-- The Fejer CDF is its symmetric half-mass plus the oriented integral of
the density from zero. -/
theorem cdf_fejerMeasure_eq_half_add_integral (u : ℝ) :
    (cdf fejerMeasure u : ℂ) =
      1 / 2 + ∫ x : ℝ in 0..u, (fejerDensity x : ℂ) := by
  rw [cdf_eq_real, fejerMeasure_real_apply measurableSet_Iic]
  rw [← integral_complex_ofReal]
  have hhalf : (∫ x : ℝ in Iic 0, (fejerDensity x : ℂ)) = 1 / 2 := by
    have hreal : (∫ x : ℝ in Iic 0, fejerDensity x) = 1 / 2 := by
      simpa [cdf_eq_real, fejerMeasure_real_apply measurableSet_Iic] using
        cdf_fejerMeasure_zero
    calc
      (∫ x : ℝ in Iic 0, (fejerDensity x : ℂ)) =
          Complex.ofReal (∫ x : ℝ in Iic 0, fejerDensity x) :=
        integral_complex_ofReal
      _ = 1 / 2 := by
        rw [hreal]
        norm_num
  rcases le_total 0 u with hu | hu
  · rw [intervalIntegral.integral_of_le hu]
    have hunion : Iic u = Iic 0 ∪ Ioc 0 u := by
      ext x
      simp only [mem_Iic, mem_union, mem_Ioc]
      constructor
      · intro hx
        by_cases hx0 : x ≤ 0
        · exact Or.inl hx0
        · exact Or.inr ⟨lt_of_not_ge hx0, hx⟩
      · rintro (hx | hx) <;> linarith
    rw [hunion, setIntegral_union (by grind) measurableSet_Ioc
      fejerDensity_integrable.ofReal.integrableOn
      fejerDensity_integrable.ofReal.integrableOn, hhalf]
  · rw [intervalIntegral.integral_of_ge hu]
    have hunion : Iic 0 = Iic u ∪ Ioc u 0 := by
      ext x
      simp only [mem_Iic, mem_union, mem_Ioc]
      constructor
      · intro hx
        by_cases hxu : x ≤ u
        · exact Or.inl hxu
        · exact Or.inr ⟨lt_of_not_ge hxu, hx⟩
      · rintro (hx | hx) <;> linarith
    have hsplit : (∫ x : ℝ in Iic 0, (fejerDensity x : ℂ)) =
        (∫ x : ℝ in Iic u, (fejerDensity x : ℂ)) +
          ∫ x : ℝ in Ioc u 0, (fejerDensity x : ℂ) := by
      rw [hunion, setIntegral_union (by grind) measurableSet_Ioc
        fejerDensity_integrable.ofReal.integrableOn
        fejerDensity_integrable.ofReal.integrableOn]
    rw [hhalf] at hsplit
    rw [← sub_eq_add_neg]
    exact (eq_sub_iff_add_eq).2 hsplit.symm

/-- The finite oscillatory primitive occurring after Fourier inversion. -/
def fejerOscillatoryPrimitive (u t : ℝ) : ℂ :=
  ∫ x : ℝ in 0..u,
    Complex.exp (↑(-2 * Real.pi * (x * t)) * Complex.I)

theorem fejerOscillatoryPrimitive_of_ne_zero (u : ℝ) {t : ℝ} (ht : t ≠ 0) :
    fejerOscillatoryPrimitive u t =
      (Complex.exp (↑(-2 * Real.pi * (u * t)) * Complex.I) - 1) /
        (↑(-2 * Real.pi * t) * Complex.I) := by
  let c : ℂ := (↑(-2 * Real.pi * t) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
        (ne_of_gt Real.pi_pos)) ht)) Complex.I_ne_zero
  rw [fejerOscillatoryPrimitive]
  have hfun : (fun x : ℝ ↦
      Complex.exp (↑(-2 * Real.pi * (x * t)) * Complex.I)) =
      (fun x : ℝ ↦ Complex.exp (c * x)) := by
    funext x
    congr 1
    dsimp [c]
    push_cast
    ring
  rw [hfun, integral_exp_mul_complex hc]
  dsimp [c]
  congr 2
  · congr 1
    push_cast
    ring
  · simp

@[simp] theorem fejerOscillatoryPrimitive_zero (u : ℝ) :
    fejerOscillatoryPrimitive u 0 = u := by
  simp [fejerOscillatoryPrimitive]

theorem norm_fejerOscillatoryPrimitive_le (u t : ℝ) :
    ‖fejerOscillatoryPrimitive u t‖ ≤ |u| := by
  rw [fejerOscillatoryPrimitive]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := u) (C := (1 : ℝ))
    (f := fun x : ℝ ↦
      Complex.exp (↑(-2 * Real.pi * (x * t)) * Complex.I))
    (fun x _hx ↦ by
      rw [Complex.norm_exp]
      simp)
  simpa using h

theorem continuous_fejerOscillatoryPrimitive (t : ℝ) :
    Continuous (fun u ↦ fejerOscillatoryPrimitive u t) := by
  by_cases ht : t = 0
  · subst t
    simpa using Complex.continuous_ofReal
  · have heq : (fun u ↦ fejerOscillatoryPrimitive u t) =
        (fun u ↦
          (Complex.exp (↑(-2 * Real.pi * (u * t)) * Complex.I) - 1) /
            (↑(-2 * Real.pi * t) * Complex.I)) := by
      funext u
      exact fejerOscillatoryPrimitive_of_ne_zero u ht
    rw [heq]
    fun_prop

/-- Finite-interval Fourier inversion for the Fejer CDF.  All integrals here
are absolutely integrable before the interval primitive is evaluated. -/
theorem cdf_fejerMeasure_fourier (u : ℝ) :
    (cdf fejerMeasure u : ℂ) = 1 / 2 +
      ∫ t : ℝ, fejerOscillatoryPrimitive u t *
        (triangleMultiplier t : ℂ) := by
  let F : ℝ → ℝ → ℂ := fun x t ↦
    Complex.exp (↑(-2 * Real.pi * (x * t)) * Complex.I) *
      (triangleMultiplier t : ℂ)
  have hFmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (uIoc 0 u)).prod volume) := by
    have hexp : Continuous (fun p : ℝ × ℝ ↦
        Complex.exp (↑(-2 * Real.pi * (p.1 * p.2)) * Complex.I)) := by
      fun_prop
    have htri : Continuous (fun p : ℝ × ℝ ↦
        (triangleMultiplier p.2 : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_triangleMultiplier.comp continuous_snd)
    exact (hexp.mul htri).aestronglyMeasurable
  have hdom : Integrable
      (fun p : ℝ × ℝ ↦ (1 : ℂ) * (triangleMultiplier p.2 : ℂ))
      ((volume.restrict (uIoc 0 u)).prod volume) :=
    (integrableOn_const (by simp [volume_uIoc]) :
      Integrable (fun _ : ℝ ↦ (1 : ℂ)) (volume.restrict (uIoc 0 u))).mul_prod
        triangleMultiplier_integrable_complex
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc 0 u)).prod volume) := by
    apply hdom.mono hFmeas
    exact Filter.Eventually.of_forall fun p ↦ by
      have htri : 0 ≤ triangleMultiplier p.2 := by
        exact le_max_right _ _
      simp only [F, Function.uncurry, Complex.norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg htri, one_mul]
      rw [Complex.norm_exp]
      simp
  rw [cdf_fejerMeasure_eq_half_add_integral]
  congr 1
  calc
    (∫ x : ℝ in 0..u, (fejerDensity x : ℂ)) =
        ∫ x : ℝ in 0..u, ∫ t : ℝ, F x t := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change (fejerDensity x : ℂ) = ∫ t : ℝ, F x t
      rw [← fourier_triangleMultiplier x, Real.fourier_eq']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t ↦ by
        simp only [F, Real.inner_apply, smul_eq_mul]
        congr 2
        push_cast
        ring
    _ = ∫ t : ℝ, ∫ x : ℝ in 0..u, F x t :=
      intervalIntegral_integral_swap hFint
    _ = ∫ t : ℝ, fejerOscillatoryPrimitive u t *
        (triangleMultiplier t : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t ↦ by
        change (∫ x : ℝ in 0..u,
            Complex.exp (↑(-2 * Real.pi * (x * t)) * Complex.I) *
              (triangleMultiplier t : ℂ)) =
          fejerOscillatoryPrimitive u t * (triangleMultiplier t : ℂ)
        rw [intervalIntegral.integral_mul_const]
        rfl


end

end LogdetLean
