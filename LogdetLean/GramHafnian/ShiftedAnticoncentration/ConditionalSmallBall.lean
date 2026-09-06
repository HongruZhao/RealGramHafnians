import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianDisk
import LogdetLean.GramHafnian.ShiftedAnticoncentration.LaplaceOrder
import Mathlib.MeasureTheory.Measure.Real
/-!
# Integrating the conditional circular-Gaussian disk bound

This module packages the final conditioning step independently of the
hafnian algebra.  If a fresh iid circular Gaussian vector is paired, by the
transpose bilinear form, with a measurable coefficient vector `y(omega)`,
then every shifted disk has mass bounded by `rho^2 E[||y||^{-2}]`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The random transpose-linear form after exposing an independent final
column. -/
def conditionalCircularLinearForm {k : ℕ}
    (y : Omega -> Fin k -> ℂ) (p : Omega × (Fin k -> ℂ)) : ℂ :=
  iidCircularTransposeLinearForm (y p.1) p.2

/-- The coefficient energy controlling the conditional variance. -/
def conditionalCircularEnergy {k : ℕ}
    (y : Omega -> Fin k -> ℂ) (w : Omega) : ℝ :=
  circularCoefficientEnergy (y w)

@[fun_prop]
theorem measurable_conditionalCircularEnergy {k : ℕ}
    {y : Omega -> Fin k -> ℂ} (hy : Measurable y) :
    Measurable (conditionalCircularEnergy y) := by
  unfold conditionalCircularEnergy circularCoefficientEnergy
  fun_prop

@[fun_prop]
theorem measurable_conditionalCircularLinearForm {k : ℕ}
    {y : Omega -> Fin k -> ℂ} (hy : Measurable y) :
    Measurable (conditionalCircularLinearForm y) := by
  unfold conditionalCircularLinearForm iidCircularTransposeLinearForm
  fun_prop

/-- ENNReal form of the sharp conditional estimate for one fixed positive
coefficient energy. -/
theorem pi_circularGaussian_conditional_section_le
    {k : ℕ} (y : Fin k -> ℂ)
    (henergy : 0 < circularCoefficientEnergy y)
    (z : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (Measure.pi fun _ : Fin k => circularGaussian)
        {x : Fin k -> ℂ |
          ‖iidCircularTransposeLinearForm y x - z‖ ≤ rho} ≤
      ENNReal.ofReal (rho ^ 2) *
        ENNReal.ofReal (circularCoefficientEnergy y)⁻¹ := by
  let mu : Measure (Fin k -> ℂ) :=
    Measure.pi fun _ : Fin k => circularGaussian
  let s : Set (Fin k -> ℂ) :=
    {x | ‖iidCircularTransposeLinearForm y x - z‖ ≤ rho}
  have hreal := pi_circularGaussian_transpose_norm_sub_le
    y henergy z rho hrho
  have htoReal :
      (mu s).toReal ≤
        (ENNReal.ofReal (rho ^ 2) *
          ENNReal.ofReal (circularCoefficientEnergy y)⁻¹).toReal := by
    rw [← Measure.real_def]
    change mu.real s ≤ _
    rw [← ENNReal.ofReal_mul (sq_nonneg rho), ← div_eq_mul_inv]
    rw [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg rho) henergy.le)]
    simpa [mu, s] using hreal
  have hrhs_ne_top :
      ENNReal.ofReal (rho ^ 2) *
          ENNReal.ofReal (circularCoefficientEnergy y)⁻¹ ≠ ⊤ := by
    rw [← ENNReal.ofReal_mul (sq_nonneg rho), ← div_eq_mul_inv]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.toReal_le_toReal (measure_ne_top mu s)
    hrhs_ne_top).mp htoReal

/-- The unconditional shifted small-ball estimate obtained by integrating
the sharp conditional disk bound.  It is stated in `ENNReal`, so no prior
finiteness assumption on the inverse moment is needed. -/
theorem prod_pi_circularGaussian_shiftedSmallBall_le_inverseMoment
    {k : ℕ}
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (y : Omega -> Fin k -> ℂ) (hy : Measurable y)
    (henergy : ∀ᵐ w ∂nu, 0 < conditionalCircularEnergy y w)
    (z : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (nu.prod (Measure.pi fun _ : Fin k => circularGaussian))
        {p : Omega × (Fin k -> ℂ) |
          ‖conditionalCircularLinearForm y p - z‖ ≤ rho} ≤
      ENNReal.ofReal (rho ^ 2) *
        ennInverseMoment nu (conditionalCircularEnergy y) := by
  let mu : Measure (Fin k -> ℂ) :=
    Measure.pi fun _ : Fin k => circularGaussian
  let s : Set (Omega × (Fin k -> ℂ)) :=
    {p | ‖conditionalCircularLinearForm y p - z‖ ≤ rho}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_le
      ((measurable_conditionalCircularLinearForm hy).sub_const z).norm
      measurable_const
  rw [show nu.prod (Measure.pi fun _ : Fin k => circularGaussian) =
      nu.prod mu by rfl]
  rw [Measure.prod_apply hs]
  calc
    (∫⁻ w, mu (Prod.mk w ⁻¹' s) ∂nu) ≤
        ∫⁻ w, ENNReal.ofReal (rho ^ 2) *
          ENNReal.ofReal (conditionalCircularEnergy y w)⁻¹ ∂nu := by
      apply lintegral_mono_ae
      filter_upwards [henergy] with w hw
      simpa [mu, s, conditionalCircularLinearForm,
        conditionalCircularEnergy] using
        pi_circularGaussian_conditional_section_le (y w) hw z rho hrho
    _ = ENNReal.ofReal (rho ^ 2) *
        ennInverseMoment nu (conditionalCircularEnergy y) := by
      rw [lintegral_const_mul]
      · rfl
      · exact (measurable_conditionalCircularEnergy hy).inv.ennreal_ofReal

end

end LogdetLean.GramHafnian
