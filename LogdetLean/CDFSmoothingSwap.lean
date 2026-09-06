import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.CDF
import Mathlib.Tactic
import LogdetLean.AbstractSmoothingKernel
/-!
# Interchanging the two variables in CDF smoothing

This is the elementary Fubini bridge between adding kernel noise to a CDF
and averaging the kernel CDF against the original law.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set

noncomputable section

theorem cdf_eq_integral_Iic_indicator (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) :
    cdf μ a = ∫ y, (Iic a).indicator (fun _ ↦ (1 : ℝ)) y ∂μ := by
  rw [cdf_eq_real, integral_indicator measurableSet_Iic]
  simp

theorem smoothCDF_eq_integral_kernel_cdf
    (κ μ : Measure ℝ) [IsProbabilityMeasure κ] [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    smoothCDF κ T μ x = ∫ y, cdf κ (T * (x - y)) ∂μ := by
  let f : ℝ → ℝ → ℝ := fun z y ↦
    (Iic (x - z / T)).indicator (fun _ ↦ (1 : ℝ)) y
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ x - p.1 / T} := by
    exact measurableSet_le measurable_snd
      (measurable_const.sub (measurable_fst.div_const T))
  have hfmeas : Measurable (Function.uncurry f) := by
    change Measurable
      ({p : ℝ × ℝ | p.2 ≤ x - p.1 / T}.indicator (fun _ ↦ (1 : ℝ)))
    exact measurable_const.indicator hset
  have hfi : Integrable (Function.uncurry f) (κ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono hfmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p ↦ by
      by_cases hp : p.2 ∈ Iic (x - p.1 / T)
      · simp [f, Function.uncurry, indicator_of_mem hp]
      · simp [f, Function.uncurry, indicator_of_notMem hp]
  rw [smoothCDF]
  simp_rw [cdf_eq_integral_Iic_indicator]
  change (∫ z, ∫ y, f z y ∂μ ∂κ) = _
  rw [integral_integral_swap hfi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ by
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

end

end LogdetLean
