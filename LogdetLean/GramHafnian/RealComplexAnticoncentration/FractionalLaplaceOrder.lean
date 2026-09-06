import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealConditionalSmallBall
import LogdetLean.GramHafnian.ShiftedAnticoncentration.LaplaceOrder
import Mathlib.MeasureTheory.Integral.Gamma
/-!
# Laplace order and inverse square-root moments

The function `x ↦ x^(-1/2)` is completely monotone.  This file proves the
specific Mellin--Laplace representation needed for beta one and then repeats
the Tonelli comparison from the complex inverse-first-moment argument.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The normalized Mellin kernel whose integral is `1 / sqrt x`. -/
def normalizedHalfMellinKernel (t x : ℝ) : ℝ :=
  (Real.Gamma (1 / 2 : ℝ))⁻¹ *
    (t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * x))

theorem integral_rpow_neg_half_mul_exp_neg_mul_Ioi
    {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ in Ioi 0,
        t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * x) =
      Real.Gamma (1 / 2 : ℝ) * (Real.sqrt x)⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 / 2 : ℝ)) (r := x) (by norm_num) hx
  calc
    (∫ t : ℝ in Ioi 0,
        t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * x)) =
        ∫ t : ℝ in Ioi 0,
          t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(x * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      congr 2 <;> ring
    _ = (1 / x) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ) := h
    _ = Real.Gamma (1 / 2 : ℝ) * (Real.sqrt x)⁻¹ := by
      rw [one_div, Real.inv_rpow hx.le, ← Real.sqrt_eq_rpow]
      ring

theorem integrableOn_rpow_neg_half_mul_exp_neg_mul_Ioi
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun t : ℝ ↦ t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * x))
      (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_rpow_neg_half_mul_exp_neg_mul_Ioi hx]
  exact (mul_pos (Real.Gamma_pos_of_pos (by norm_num))
    (inv_pos.mpr (Real.sqrt_pos.2 hx))).ne'

theorem integral_normalizedHalfMellinKernel_Ioi
    {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ in Ioi 0, normalizedHalfMellinKernel t x =
      (Real.sqrt x)⁻¹ := by
  unfold normalizedHalfMellinKernel
  rw [integral_const_mul,
    integral_rpow_neg_half_mul_exp_neg_mul_Ioi hx]
  have hG : Real.Gamma (1 / 2 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  field_simp [hG]

theorem integrableOn_normalizedHalfMellinKernel_Ioi
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ ↦ normalizedHalfMellinKernel t x) (Ioi 0) := by
  unfold normalizedHalfMellinKernel
  exact (integrableOn_rpow_neg_half_mul_exp_neg_mul_Ioi hx).const_mul _

theorem lintegral_normalizedHalfMellinKernel_Ioi
    {x : ℝ} (hx : 0 < x) :
    ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (normalizedHalfMellinKernel t x) =
      ENNReal.ofReal (Real.sqrt x)⁻¹ := by
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi 0)]
        (fun t : ℝ ↦ normalizedHalfMellinKernel t x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    unfold normalizedHalfMellinKernel
    exact mul_nonneg
      (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by norm_num)).le)
      (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_normalizedHalfMellinKernel_Ioi hx) hnonneg]
  rw [integral_normalizedHalfMellinKernel_Ioi hx]

variable {Omega Omega' : Type*}
  [MeasurableSpace Omega] [MeasurableSpace Omega']

/-- Laplace-transform domination implies domination of the inverse
square-root moment.  This is the exact fractional analogue of
`ennInverseMoment_le_of_laplaceTransform_le_two_measures`. -/
theorem ennInverseSqrtMoment_le_of_laplaceTransform_le_two_measures
    (mu : Measure Omega) [SFinite mu]
    (nu : Measure Omega') [SFinite nu]
    (U : Omega → ℝ) (V : Omega' → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (hUpos : ∀ᵐ w ∂mu, 0 < U w)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (hLap : ∀ t : ℝ, 0 ≤ t →
      ennLaplaceTransform nu V t ≤ ennLaplaceTransform mu U t) :
    ennInverseSqrtMoment nu V ≤ ennInverseSqrtMoment mu U := by
  have hmeasV : Measurable
      (fun p : Omega' × ℝ ↦
        ENNReal.ofReal (normalizedHalfMellinKernel p.2 (V p.1))) := by
    unfold normalizedHalfMellinKernel
    fun_prop
  have hmeasU : Measurable
      (fun p : Omega × ℝ ↦
        ENNReal.ofReal (normalizedHalfMellinKernel p.2 (U p.1))) := by
    unfold normalizedHalfMellinKernel
    fun_prop
  rw [ennInverseSqrtMoment, ennInverseSqrtMoment]
  calc
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (V w))⁻¹ ∂nu) =
        ∫⁻ w, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (normalizedHalfMellinKernel t (V w))
          ∂volume ∂nu := by
      apply lintegral_congr_ae
      filter_upwards [hVpos] with w hw
      exact (lintegral_normalizedHalfMellinKernel_Ioi hw).symm
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ w,
          ENNReal.ofReal (normalizedHalfMellinKernel t (V w))
          ∂nu ∂volume := by
      rw [lintegral_lintegral_swap hmeasV.aemeasurable]
    _ ≤ ∫⁻ t : ℝ in Ioi 0, ∫⁻ w,
          ENNReal.ofReal (normalizedHalfMellinKernel t (U w))
          ∂mu ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := ht.le
      let c : ℝ := (Real.Gamma (1 / 2 : ℝ))⁻¹ *
        t ^ (-(1 / 2 : ℝ))
      have hc : 0 ≤ c := by
        dsimp [c]
        positivity
      have hfactorV :
          (∫⁻ w, ENNReal.ofReal (normalizedHalfMellinKernel t (V w)) ∂nu) =
            ENNReal.ofReal c * ennLaplaceTransform nu V t := by
        unfold normalizedHalfMellinKernel ennLaplaceTransform
        simp_rw [show ∀ w, (Real.Gamma (1 / 2 : ℝ))⁻¹ *
            (t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * V w)) =
            c * Real.exp (-t * V w) by intro w; dsimp [c]; ring]
        simp_rw [ENNReal.ofReal_mul hc]
        rw [lintegral_const_mul]
        fun_prop
      have hfactorU :
          (∫⁻ w, ENNReal.ofReal (normalizedHalfMellinKernel t (U w)) ∂mu) =
            ENNReal.ofReal c * ennLaplaceTransform mu U t := by
        unfold normalizedHalfMellinKernel ennLaplaceTransform
        simp_rw [show ∀ w, (Real.Gamma (1 / 2 : ℝ))⁻¹ *
            (t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * U w)) =
            c * Real.exp (-t * U w) by intro w; dsimp [c]; ring]
        simp_rw [ENNReal.ofReal_mul hc]
        rw [lintegral_const_mul]
        fun_prop
      rw [hfactorV, hfactorU]
      exact mul_le_mul_of_nonneg_left (hLap t ht0) (by positivity)
    _ = ∫⁻ w, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (normalizedHalfMellinKernel t (U w))
          ∂volume ∂mu := by
      symm
      rw [lintegral_lintegral_swap hmeasU.aemeasurable]
    _ = ∫⁻ w, ENNReal.ofReal (Real.sqrt (U w))⁻¹ ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hUpos] with w hw
      exact lintegral_normalizedHalfMellinKernel_Ioi hw

end

end LogdetLean.GramHafnian
