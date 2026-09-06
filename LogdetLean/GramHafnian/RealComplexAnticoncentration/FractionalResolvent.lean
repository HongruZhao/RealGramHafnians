import LogdetLean.GramHafnian.RealComplexAnticoncentration.FractionalLaplaceOrder
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
/-!
# Fractional resolvents and Laplace order

For the real (`beta = 1`) small-ball argument it is better to propagate the
bounded observable

`Psi_U(lambda) = E[sqrt(lambda) / sqrt(U + lambda)]`

than the generally much larger inverse square-root moment.  This file gives
the exact `ENNReal` definition and proves that Laplace-transform domination
passes to these fractional resolvents.  No finiteness hypothesis on an
inverse moment is needed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega Omega' : Type*}
  [MeasurableSpace Omega] [MeasurableSpace Omega']

/-- The pointwise half-resolvent kernel.  It is written as a product of
square roots rather than as a square root of a quotient so it interfaces
directly with the half-Mellin representation. -/
def ennHalfResolventKernel (lambda x : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt lambda) *
    ENNReal.ofReal (Real.sqrt (x + lambda))⁻¹

/-- The beta-one fractional resolvent of a nonnegative random variable. -/
def ennHalfResolvent (mu : Measure Omega) (U : Omega → ℝ)
    (lambda : ℝ) : ENNReal :=
  ∫⁻ w, ennHalfResolventKernel lambda (U w) ∂mu

@[fun_prop]
theorem measurable_ennHalfResolventKernel_comp
    {U : Omega → ℝ} (hU : Measurable U) (lambda : ℝ) :
    Measurable (fun w ↦ ennHalfResolventKernel lambda (U w)) := by
  unfold ennHalfResolventKernel
  fun_prop

/-- Pulling the constant numerator out identifies the resolvent with the
inverse square-root moment of the shifted observable. -/
theorem ennHalfResolvent_eq_const_mul_inverseSqrtMoment
    (mu : Measure Omega) (U : Omega → ℝ) (hU : Measurable U)
    (lambda : ℝ) :
    ennHalfResolvent mu U lambda =
      ENNReal.ofReal (Real.sqrt lambda) *
        ennInverseSqrtMoment mu (fun w ↦ U w + lambda) := by
  unfold ennHalfResolvent ennHalfResolventKernel ennInverseSqrtMoment
  rw [lintegral_const_mul]
  fun_prop

/-- Adding the same positive spectral parameter preserves Laplace order. -/
theorem ennLaplaceTransform_add_const_le_add_const
    (mu : Measure Omega) (nu : Measure Omega')
    (U : Omega → ℝ) (V : Omega' → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (hLap : ∀ t : ℝ, 0 ≤ t →
      ennLaplaceTransform nu V t ≤ ennLaplaceTransform mu U t)
    (lambda t : ℝ) (ht : 0 ≤ t) :
    ennLaplaceTransform nu (fun w ↦ V w + lambda) t ≤
      ennLaplaceTransform mu (fun w ↦ U w + lambda) t := by
  let c : ℝ := Real.exp (-t * lambda)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hnu :
      ennLaplaceTransform nu (fun w ↦ V w + lambda) t =
        ENNReal.ofReal c * ennLaplaceTransform nu V t := by
    unfold ennLaplaceTransform
    simp_rw [show ∀ w, Real.exp (-t * (V w + lambda)) =
        c * Real.exp (-t * V w) by
      intro w
      dsimp [c]
      rw [← Real.exp_add]
      congr 1
      ring]
    simp_rw [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul]
    exact ((hV.const_mul (-t)).exp.ennreal_ofReal)
  have hmu :
      ennLaplaceTransform mu (fun w ↦ U w + lambda) t =
        ENNReal.ofReal c * ennLaplaceTransform mu U t := by
    unfold ennLaplaceTransform
    simp_rw [show ∀ w, Real.exp (-t * (U w + lambda)) =
        c * Real.exp (-t * U w) by
      intro w
      dsimp [c]
      rw [← Real.exp_add]
      congr 1
      ring]
    simp_rw [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul]
    exact ((hU.const_mul (-t)).exp.ennreal_ofReal)
  rw [hnu, hmu]
  exact mul_le_mul le_rfl (hLap t ht) bot_le bot_le

/-- Laplace-transform domination implies domination of every positive
half-resolvent.  This is the bounded fractional replacement for inverse
moment transfer. -/
theorem ennHalfResolvent_le_of_laplaceTransform_le_two_measures
    (mu : Measure Omega) [SFinite mu]
    (nu : Measure Omega') [SFinite nu]
    (U : Omega → ℝ) (V : Omega' → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (hUnonneg : ∀ᵐ w ∂mu, 0 ≤ U w)
    (hVnonneg : ∀ᵐ w ∂nu, 0 ≤ V w)
    (hLap : ∀ t : ℝ, 0 ≤ t →
      ennLaplaceTransform nu V t ≤ ennLaplaceTransform mu U t)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ennHalfResolvent nu V lambda ≤ ennHalfResolvent mu U lambda := by
  have hUshift : Measurable (fun w ↦ U w + lambda) := hU.add_const _
  have hVshift : Measurable (fun w ↦ V w + lambda) := hV.add_const _
  have hUpos : ∀ᵐ w ∂mu, 0 < U w + lambda := by
    filter_upwards [hUnonneg] with w hw
    linarith
  have hVpos : ∀ᵐ w ∂nu, 0 < V w + lambda := by
    filter_upwards [hVnonneg] with w hw
    linarith
  have hshiftLap : ∀ t : ℝ, 0 ≤ t →
      ennLaplaceTransform nu (fun w ↦ V w + lambda) t ≤
        ennLaplaceTransform mu (fun w ↦ U w + lambda) t := by
    intro t ht
    exact ennLaplaceTransform_add_const_le_add_const
      mu nu U V hU hV hLap lambda t ht
  have hinv :=
    ennInverseSqrtMoment_le_of_laplaceTransform_le_two_measures
      mu nu (fun w ↦ U w + lambda) (fun w ↦ V w + lambda)
      hUshift hVshift hUpos hVpos hshiftLap
  rw [ennHalfResolvent_eq_const_mul_inverseSqrtMoment nu V hV,
    ennHalfResolvent_eq_const_mul_inverseSqrtMoment mu U hU]
  exact mul_le_mul le_rfl hinv bot_le bot_le

/-- The half-resolvent kernel lies in `[0,1]` for nonnegative energy and
positive spectral parameter. -/
theorem ennHalfResolventKernel_le_one
    {lambda x : ℝ} (hlambda : 0 < lambda) (hx : 0 ≤ x) :
    ennHalfResolventKernel lambda x ≤ 1 := by
  unfold ennHalfResolventKernel
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hsqrtLambda : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hlambda
  have hsum : 0 < x + lambda := by linarith
  have hsqrtSum : 0 < Real.sqrt (x + lambda) := Real.sqrt_pos.2 hsum
  rw [mul_inv_le_iff₀ hsqrtSum]
  simpa using Real.sqrt_le_sqrt (by linarith : lambda ≤ x + lambda)

/-- A pointwise lower bound on the energy gives the expected rescaling of
the half-resolvent kernel. -/
theorem ennHalfResolventKernel_le_of_mul_le
    {lambda tau u v : ℝ} (hlambda : 0 < lambda) (htau : 0 < tau)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (h : tau * v ≤ u) :
    ennHalfResolventKernel lambda u ≤
      ennHalfResolventKernel (lambda / tau) v := by
  unfold ennHalfResolventKernel
  have hlt : 0 < lambda / tau := div_pos hlambda htau
  have huadd : 0 < u + lambda := by linarith
  have hvadd : 0 < v + lambda / tau := by linarith
  have hsq :
      Real.sqrt lambda * (Real.sqrt (u + lambda))⁻¹ ≤
        Real.sqrt (lambda / tau) *
          (Real.sqrt (v + lambda / tau))⁻¹ := by
    have hfrac :
        lambda / (u + lambda) ≤
          (lambda / tau) / (v + lambda / tau) := by
      rw [div_le_div_iff₀ huadd hvadd]
      have htne : tau ≠ 0 := ne_of_gt htau
      field_simp [htne]
      nlinarith
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    rw [← Real.sqrt_div hlambda.le, ← Real.sqrt_div hlt.le]
    exact Real.sqrt_le_sqrt hfrac
  simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg _)] using
    ENNReal.ofReal_le_ofReal hsq

/-- Resolvent splitting on a measurable good event.  On the good event the
energy lower bound rescales the spectral parameter; on its complement the
bounded kernel costs at most the probability of that complement. -/
theorem ennHalfResolvent_le_rescaled_add_compl
    (mu : Measure Omega)
    (U W : Omega → ℝ) (hU : Measurable U) (hW : Measurable W)
    (s : Set Omega) (hs : MeasurableSet s)
    (hUnonneg : ∀ᵐ w ∂mu, 0 ≤ U w)
    (hWnonneg : ∀ᵐ w ∂mu, 0 ≤ W w)
    (tau lambda : ℝ) (htau : 0 < tau) (hlambda : 0 < lambda)
    (hgood : ∀ᵐ w ∂mu, w ∈ s → tau * W w ≤ U w) :
    ennHalfResolvent mu U lambda ≤
      ennHalfResolvent mu W (lambda / tau) + mu sᶜ := by
  have hkernelW : Measurable
      (fun w ↦ ennHalfResolventKernel (lambda / tau) (W w)) :=
    measurable_ennHalfResolventKernel_comp hW _
  have hpoint : ∀ᵐ w ∂mu,
      ennHalfResolventKernel lambda (U w) ≤
        ennHalfResolventKernel (lambda / tau) (W w) +
          sᶜ.indicator (1 : Omega → ENNReal) w := by
    filter_upwards [hUnonneg, hWnonneg, hgood] with w hUw hWw hgw
    by_cases hws : w ∈ s
    · simp only [Set.indicator_of_notMem (show w ∉ sᶜ by simpa), add_zero]
      exact ennHalfResolventKernel_le_of_mul_le
        hlambda htau hUw hWw (hgw hws)
    · simp only [Set.indicator_of_mem (show w ∈ sᶜ by simpa)]
      exact (ennHalfResolventKernel_le_one hlambda hUw).trans le_add_self
  unfold ennHalfResolvent
  calc
    (∫⁻ w, ennHalfResolventKernel lambda (U w) ∂mu) ≤
        ∫⁻ w, ennHalfResolventKernel (lambda / tau) (W w) +
          sᶜ.indicator (1 : Omega → ENNReal) w ∂mu :=
      lintegral_mono_ae hpoint
    _ = (∫⁻ w, ennHalfResolventKernel (lambda / tau) (W w) ∂mu) +
        ∫⁻ w, sᶜ.indicator (1 : Omega → ENNReal) w ∂mu := by
      rw [lintegral_add_left hkernelW]
    _ = (∫⁻ w, ennHalfResolventKernel (lambda / tau) (W w) ∂mu) +
        mu sᶜ := by
      rw [lintegral_indicator_one hs.compl]

end

end LogdetLean.GramHafnian
