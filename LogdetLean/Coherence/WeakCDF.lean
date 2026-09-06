import Mathlib.MeasureTheory.Measure.Portmanteau
import LogdetLean.FullTarget
/-!
# Extracting lower-tail limits from weak convergence
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Weak convergence gives convergence of real-valued lower-tail
probabilities at every atom-free threshold. -/
theorem tendsto_measureReal_Iic_of_weak
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hweak : Tendsto μs l (nhds μ)) (z : ℝ)
    (hatom : μ ({z} : Set ℝ) = 0) :
    Tendsto (fun i ↦ (μs i : Measure ℝ).real (Iic z)) l
      (nhds ((μ : Measure ℝ).real (Iic z))) := by
  have hnn := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    hweak (E := Iic z) (by simpa using hatom)
  have hcoe := (NNReal.continuous_coe.tendsto _).comp hnn
  have hfun : (fun i ↦ (μs i : Measure ℝ).real (Iic z)) =
      (NNReal.toReal ∘ fun i ↦ μs i (Iic z)) := by
    funext i
    unfold Function.comp Measure.real
    exact (ENNReal.coe_toNNReal_eq_toReal _).symm
  have hlim : (μ : Measure ℝ).real (Iic z) =
      ((μ (Iic z) : NNReal) : ℝ) := by
    unfold Measure.real
    exact (ENNReal.coe_toNNReal_eq_toReal _).symm
  rw [hfun, hlim]
  exact hcoe

/-- The standard Gaussian has no atoms. -/
theorem standardGaussian_singleton_probabilityMeasure_zero (z : ℝ) :
    DFunLike.coe (F := ProbabilityMeasure ℝ)
      (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)
      ({z} : Set ℝ) = 0 := by
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hz : gaussianReal 0 1 ({z} : Set ℝ) = 0 := measure_singleton z
  change (gaussianReal 0 1 ({z} : Set ℝ)).toNNReal = 0
  rw [hz]
  simp

/-- Weak convergence to the standard Gaussian implies convergence of every
lower-tail probability to `standardNormalCDF`. -/
theorem tendsto_measureReal_Iic_standardGaussian_of_weak
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ}
    (hweak : Tendsto μs l
      (nhds (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)))
    (z : ℝ) :
    Tendsto (fun i ↦ (μs i : Measure ℝ).real (Iic z)) l
      (nhds (standardNormalCDF z)) := by
  have h := tendsto_measureReal_Iic_of_weak hweak z
    (standardGaussian_singleton_probabilityMeasure_zero z)
  simpa [standardNormalCDF, cdf_eq_real] using h

end

end LogdetLean.Coherence
