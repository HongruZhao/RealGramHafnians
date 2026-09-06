import LogdetLean.GramHafnian.RealComplexAnticoncentration.FractionalResolvent
/-!
# Real conditional small balls through a bounded resolvent

The density estimate by itself produces an inverse square-root moment.  By
also using the trivial probability bound by one, the section estimate is
bounded by twice the half-resolvent kernel at `lambda = rho^2`.  This is the
form that can be iterated without paying a large inverse moment on rare bad
Gram events.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The sharp real Gaussian interval prefactor is no larger than the radius
itself. -/
theorem realGaussianIntervalPrefactor_le
    {rho : ℝ} (hrho : 0 ≤ rho) :
    realGaussianIntervalPrefactor rho ≤ rho := by
  unfold realGaussianIntervalPrefactor
  have hdenom : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    have hfour : (4 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.two_le_pi]
    calc
      (2 : ℝ) = Real.sqrt 4 := by norm_num
      _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt hfour
  rw [div_le_iff₀ hdenom]
  nlinarith

/-- Elementary truncation inequality
`min(1,rho/sqrt(v)) <= 2 rho/sqrt(v+rho^2)`. -/
theorem min_one_mul_inverseSqrt_le_two_halfResolvent
    {rho v : ℝ} (hrho : 0 < rho) (hv : 0 < v) :
    min 1 (rho * (Real.sqrt v)⁻¹) ≤
      2 * (Real.sqrt (rho ^ 2) *
        (Real.sqrt (v + rho ^ 2))⁻¹) := by
  have hrhosqrt : Real.sqrt (rho ^ 2) = rho := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrho]
  have hvroot : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hsum : 0 < v + rho ^ 2 := by positivity
  have hsumroot : 0 < Real.sqrt (v + rho ^ 2) :=
    Real.sqrt_pos.2 hsum
  rw [hrhosqrt]
  by_cases hsmall : v ≤ rho ^ 2
  · calc
      min 1 (rho * (Real.sqrt v)⁻¹) ≤ 1 := min_le_left _ _
      _ ≤ 2 * (rho * (Real.sqrt (v + rho ^ 2))⁻¹) := by
        rw [show 2 * (rho * (Real.sqrt (v + rho ^ 2))⁻¹) =
          (2 * rho) * (Real.sqrt (v + rho ^ 2))⁻¹ by ring]
        rw [le_mul_inv_iff₀ hsumroot]
        have hsqrt : Real.sqrt (v + rho ^ 2) ≤ 2 * rho := by
          apply Real.sqrt_le_iff.mpr
          constructor
          · positivity
          · nlinarith [sq_nonneg rho]
        simpa [mul_assoc] using hsqrt
  · have hlarge : rho ^ 2 ≤ v := le_of_not_ge hsmall
    have hsqrt : Real.sqrt (v + rho ^ 2) ≤ 2 * Real.sqrt v := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · rw [mul_pow, Real.sq_sqrt hv.le]
        nlinarith
    have hinv : (Real.sqrt v)⁻¹ ≤
        2 * (Real.sqrt (v + rho ^ 2))⁻¹ := by
      rw [show (Real.sqrt v)⁻¹ = 1 / Real.sqrt v by rw [one_div]]
      rw [show 2 * (Real.sqrt (v + rho ^ 2))⁻¹ =
        2 / Real.sqrt (v + rho ^ 2) by rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ hvroot hsumroot]
      simpa using hsqrt
    calc
      min 1 (rho * (Real.sqrt v)⁻¹) ≤
          rho * (Real.sqrt v)⁻¹ := min_le_right _ _
      _ ≤ rho * (2 * (Real.sqrt (v + rho ^ 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hinv hrho.le
      _ = 2 * rho * (Real.sqrt (v + rho ^ 2))⁻¹ := by ring
      _ = 2 * (rho * (Real.sqrt (v + rho ^ 2))⁻¹) := by ring

/-- ENNReal version of the truncation inequality used on each conditional
Gaussian section. -/
theorem min_one_enn_inverseSqrt_le_two_kernel
    {rho v : ℝ} (hrho : 0 < rho) (hv : 0 < v) :
    min 1
        (ENNReal.ofReal rho * ENNReal.ofReal (Real.sqrt v)⁻¹) ≤
      ENNReal.ofReal 2 * ennHalfResolventKernel (rho ^ 2) v := by
  have hreal := min_one_mul_inverseSqrt_le_two_halfResolvent hrho hv
  have henn := ENNReal.ofReal_le_ofReal hreal
  simpa only [ENNReal.ofReal_min, ENNReal.ofReal_one,
    ENNReal.ofReal_mul hrho.le,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ennHalfResolventKernel] using henn

/-- A fixed real Gaussian section is bounded by twice the fractional
resolvent kernel of its coefficient energy. -/
theorem pi_realGaussian_conditional_section_le_resolvent
    {k : ℕ} (y : Fin k → ℝ)
    (henergy : 0 < realCoefficientEnergy y)
    (z rho : ℝ) (hrho : 0 < rho) :
    (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1)
        {x : Fin k → ℝ |
          |iidRealTransposeLinearForm y x - z| ≤ rho} ≤
      ENNReal.ofReal 2 *
        ennHalfResolventKernel (rho ^ 2) (realCoefficientEnergy y) := by
  let mu : Measure (Fin k → ℝ) :=
    Measure.pi fun _ : Fin k ↦ gaussianReal 0 1
  let s : Set (Fin k → ℝ) :=
    {x | |iidRealTransposeLinearForm y x - z| ≤ rho}
  have hsharp := pi_realGaussian_conditional_section_le
    y henergy z rho hrho.le
  have hpref : realGaussianIntervalPrefactor rho ≤ rho :=
    realGaussianIntervalPrefactor_le hrho.le
  have hsharp' : mu s ≤
      ENNReal.ofReal rho *
        ENNReal.ofReal (Real.sqrt (realCoefficientEnergy y))⁻¹ := by
    exact hsharp.trans (mul_le_mul
      (ENNReal.ofReal_le_ofReal hpref) le_rfl bot_le bot_le)
  have hone : mu s ≤ 1 := by
    simpa [mu] using (measure_mono (μ := mu) (subset_univ s))
  exact (le_min hone hsharp').trans
    (min_one_enn_inverseSqrt_le_two_kernel hrho henergy)

/-- Integrating the capped section estimate yields the bounded fractional
resolvent of the conditional energy. -/
theorem prod_pi_realGaussian_shiftedSmallBall_le_halfResolvent
    {k : ℕ}
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (y : Omega → Fin k → ℝ) (hy : Measurable y)
    (henergy : ∀ᵐ w ∂nu, 0 < conditionalRealEnergy y w)
    (z rho : ℝ) (hrho : 0 < rho) :
    (nu.prod (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1))
        {p : Omega × (Fin k → ℝ) |
          |conditionalRealLinearForm y p - z| ≤ rho} ≤
      ENNReal.ofReal 2 *
        ennHalfResolvent nu (conditionalRealEnergy y) (rho ^ 2) := by
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
        ∫⁻ w, ENNReal.ofReal 2 *
          ennHalfResolventKernel (rho ^ 2)
            (conditionalRealEnergy y w) ∂nu := by
      apply lintegral_mono_ae
      filter_upwards [henergy] with w hw
      simpa [mu, s, conditionalRealLinearForm, conditionalRealEnergy] using
        pi_realGaussian_conditional_section_le_resolvent
          (y w) hw z rho hrho
    _ = ENNReal.ofReal 2 *
        ennHalfResolvent nu (conditionalRealEnergy y) (rho ^ 2) := by
      unfold ennHalfResolvent
      rw [lintegral_const_mul]
      exact measurable_ennHalfResolventKernel_comp
        (measurable_conditionalRealEnergy hy) _

end

end LogdetLean.GramHafnian
