import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGaussianInterval
import Mathlib.MeasureTheory.Integral.Prod
/-!
# Conditioning a real Gaussian linear form

This file packages the beta-one conditioning step independently of the
hafnian algebra.  The inverse square-root moment is deliberately a distinct
object from the inverse first moment used by the complex proof.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Extended-nonnegative inverse square-root moment. -/
def ennInverseSqrtMoment (mu : Measure Omega) (V : Omega → ℝ) : ENNReal :=
  ∫⁻ w, ENNReal.ofReal (Real.sqrt (V w))⁻¹ ∂mu

/-- Universal beta-one Gaussian interval prefactor. -/
def realGaussianIntervalPrefactor (rho : ℝ) : ℝ :=
  (2 * rho) / Real.sqrt (2 * Real.pi)

theorem realGaussianIntervalPrefactor_nonneg {rho : ℝ} (hrho : 0 ≤ rho) :
    0 ≤ realGaussianIntervalPrefactor rho := by
  unfold realGaussianIntervalPrefactor
  positivity

/-- Random linear form after exposing an independent final real column. -/
def conditionalRealLinearForm {k : ℕ}
    (y : Omega → Fin k → ℝ) (p : Omega × (Fin k → ℝ)) : ℝ :=
  iidRealTransposeLinearForm (y p.1) p.2

/-- Conditional variance of the exposed real linear form. -/
def conditionalRealEnergy {k : ℕ}
    (y : Omega → Fin k → ℝ) (w : Omega) : ℝ :=
  realCoefficientEnergy (y w)

@[fun_prop]
theorem measurable_conditionalRealEnergy {k : ℕ}
    {y : Omega → Fin k → ℝ} (hy : Measurable y) :
    Measurable (conditionalRealEnergy y) := by
  unfold conditionalRealEnergy realCoefficientEnergy
  fun_prop

@[fun_prop]
theorem measurable_conditionalRealLinearForm {k : ℕ}
    {y : Omega → Fin k → ℝ} (hy : Measurable y) :
    Measurable (conditionalRealLinearForm y) := by
  unfold conditionalRealLinearForm iidRealTransposeLinearForm
  fun_prop

/-- ENNReal form of the one-section shifted interval estimate. -/
theorem pi_realGaussian_conditional_section_le
    {k : ℕ} (y : Fin k → ℝ)
    (henergy : 0 < realCoefficientEnergy y)
    (z rho : ℝ) (hrho : 0 ≤ rho) :
    (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1)
        {x : Fin k → ℝ |
          |iidRealTransposeLinearForm y x - z| ≤ rho} ≤
      ENNReal.ofReal (realGaussianIntervalPrefactor rho) *
        ENNReal.ofReal (Real.sqrt (realCoefficientEnergy y))⁻¹ := by
  let mu : Measure (Fin k → ℝ) :=
    Measure.pi fun _ : Fin k ↦ gaussianReal 0 1
  let s : Set (Fin k → ℝ) :=
    {x | |iidRealTransposeLinearForm y x - z| ≤ rho}
  have hreal := pi_realGaussian_transpose_abs_sub_le
    y henergy z rho hrho
  have hsqrt : 0 < Real.sqrt (realCoefficientEnergy y) :=
    Real.sqrt_pos.2 henergy
  have hpref : 0 ≤ realGaussianIntervalPrefactor rho :=
    realGaussianIntervalPrefactor_nonneg hrho
  have htoReal :
      (mu s).toReal ≤
        (ENNReal.ofReal (realGaussianIntervalPrefactor rho) *
          ENNReal.ofReal (Real.sqrt (realCoefficientEnergy y))⁻¹).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpref,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hsqrt.le)]
    rw [← Measure.real_def]
    change mu.real s ≤ _
    simpa [mu, s, realGaussianIntervalPrefactor, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hreal
  exact (ENNReal.toReal_le_toReal (measure_ne_top mu s)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).mp htoReal

/-- Integrating the conditional real Gaussian interval estimate gives the
inverse-square-root energy moment. -/
theorem prod_pi_realGaussian_shiftedSmallBall_le_inverseSqrtMoment
    {k : ℕ}
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (y : Omega → Fin k → ℝ) (hy : Measurable y)
    (henergy : ∀ᵐ w ∂nu, 0 < conditionalRealEnergy y w)
    (z rho : ℝ) (hrho : 0 ≤ rho) :
    (nu.prod (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1))
        {p : Omega × (Fin k → ℝ) |
          |conditionalRealLinearForm y p - z| ≤ rho} ≤
      ENNReal.ofReal (realGaussianIntervalPrefactor rho) *
        ennInverseSqrtMoment nu (conditionalRealEnergy y) := by
  let mu : Measure (Fin k → ℝ) :=
    Measure.pi fun _ : Fin k ↦ gaussianReal 0 1
  let s : Set (Omega × (Fin k → ℝ)) :=
    {p | |conditionalRealLinearForm y p - z| ≤ rho}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_le
      ((measurable_conditionalRealLinearForm hy).sub_const z).abs measurable_const
  rw [show nu.prod (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1) =
      nu.prod mu by rfl]
  rw [Measure.prod_apply hs]
  calc
    (∫⁻ w, mu (Prod.mk w ⁻¹' s) ∂nu) ≤
        ∫⁻ w, ENNReal.ofReal (realGaussianIntervalPrefactor rho) *
          ENNReal.ofReal (Real.sqrt (conditionalRealEnergy y w))⁻¹ ∂nu := by
      apply lintegral_mono_ae
      filter_upwards [henergy] with w hw
      simpa [mu, s, conditionalRealLinearForm, conditionalRealEnergy] using
        pi_realGaussian_conditional_section_le (y w) hw z rho hrho
    _ = ENNReal.ofReal (realGaussianIntervalPrefactor rho) *
        ennInverseSqrtMoment nu (conditionalRealEnergy y) := by
      rw [lintegral_const_mul]
      · rfl
      · exact
          ((measurable_conditionalRealEnergy hy).sqrt.inv.ennreal_ofReal)

end

end LogdetLean.GramHafnian
