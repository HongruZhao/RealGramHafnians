import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
/-!
# Gaussian anti-concentration on the real line

This file proves, directly from the Gaussian density, the Lipschitz bound for
the standard-normal cumulative distribution function.  It is deliberately
independent of the log-determinant model and can therefore be reused by both
papers' Kolmogorov perturbation arguments.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

noncomputable section

/-- The standard-normal density is bounded by its value at zero. -/
theorem gaussianPDFReal_zero_one_le_peak (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ 1 / Real.sqrt (2 * Real.pi) := by
  rw [gaussianPDFReal]
  norm_num
  have hsqrt : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hexp : Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hexp hsqrt

/-- Integrating the standard-normal density over a right-closed interval is
bounded by interval length times the peak density. -/
theorem integral_standardGaussianPDFReal_Ioc_le {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Ioc a b, gaussianPDFReal 0 1 x) ≤
      (b - a) / Real.sqrt (2 * Real.pi) := by
  have hconst : Integrable (fun _ : ℝ ↦ 1 / Real.sqrt (2 * Real.pi))
      (volume.restrict (Ioc a b)) :=
    integrableOn_const (by simp [Real.volume_Ioc])
  have hmono :
      (∫ x, gaussianPDFReal 0 1 x ∂(volume.restrict (Ioc a b))) ≤
        ∫ _x : ℝ, (1 / Real.sqrt (2 * Real.pi))
          ∂(volume.restrict (Ioc a b)) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun _ ↦ gaussianPDFReal_nonneg _ _ _
    · exact hconst
    · exact Filter.Eventually.of_forall fun _ ↦ gaussianPDFReal_zero_one_le_peak _
  calc
    (∫ x in Ioc a b, gaussianPDFReal 0 1 x) ≤
        ∫ _x : ℝ, (1 / Real.sqrt (2 * Real.pi))
          ∂(volume.restrict (Ioc a b)) := hmono
    _ = (b - a) / Real.sqrt (2 * Real.pi) := by
      rw [integral_const]
      rw [measureReal_restrict_apply MeasurableSet.univ]
      simp only [univ_inter, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      simp only [smul_eq_mul, div_eq_mul_inv]
      ring

/-- A standard Gaussian assigns at most interval length divided by
`sqrt (2π)` to every right-closed interval. -/
theorem standardGaussian_measureReal_Ioc_le {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Ioc a b) ≤
      (b - a) / Real.sqrt (2 * Real.pi) := by
  have hvar : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hnonneg : 0 ≤ ∫ x in Ioc a b, gaussianPDFReal 0 1 x :=
    integral_nonneg fun _ ↦ gaussianPDFReal_nonneg _ _ _
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 hvar,
    ENNReal.toReal_ofReal hnonneg]
  exact integral_standardGaussianPDFReal_Ioc_le hab

/-- The standard-normal CDF obeys the global density bound
`1 / sqrt (2π)`. -/
theorem standardGaussian_cdf_increment_le (x ε : ℝ) (hε : 0 ≤ ε) :
    cdf (gaussianReal 0 1) (x + ε) - cdf (gaussianReal 0 1) x ≤
      ε / Real.sqrt (2 * Real.pi) := by
  rw [cdf_eq_real, cdf_eq_real]
  have hsub : Iic x ⊆ Iic (x + ε) := Iic_subset_Iic.mpr (by linarith)
  rw [← measureReal_sdiff hsub measurableSet_Iic]
  have hset : Iic (x + ε) \ Iic x = Ioc x (x + ε) := by
    ext y
    simp only [mem_sdiff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨hyu, hyl⟩
      exact ⟨lt_of_not_ge hyl, hyu⟩
    · rintro ⟨hyl, hyu⟩
      exact ⟨hyu, not_le.mpr hyl⟩
  rw [hset]
  simpa using standardGaussian_measureReal_Ioc_le (a := x) (b := x + ε) (by linarith)

/-- Symmetric-interval anti-concentration for a standard Gaussian. -/
theorem standardGaussian_measureReal_Icc_le (x ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1).real (Icc (x - ε) (x + ε)) ≤
      (2 * ε) / Real.sqrt (2 * Real.pi) := by
  have hvar : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hnonneg : 0 ≤ ∫ y in Icc (x - ε) (x + ε), gaussianPDFReal 0 1 y :=
    integral_nonneg fun _ ↦ gaussianPDFReal_nonneg _ _ _
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 hvar,
    ENNReal.toReal_ofReal hnonneg, integral_Icc_eq_integral_Ioc]
  have h := integral_standardGaussianPDFReal_Ioc_le
    (a := x - ε) (b := x + ε) (by linarith)
  calc
    (∫ y in Ioc (x - ε) (x + ε), gaussianPDFReal 0 1 y) ≤
        ((x + ε) - (x - ε)) / Real.sqrt (2 * Real.pi) := h
    _ = (2 * ε) / Real.sqrt (2 * Real.pi) := by ring

end

end LogdetLean
