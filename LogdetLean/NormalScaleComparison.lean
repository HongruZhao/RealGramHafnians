import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
import LogdetLean.KolmogorovDistance
/-!
# Comparing two normal scales

The general-correlation argument first normalizes its leading term by its
exact standard deviation and then replaces that scale by a variance proxy.
This file proves the required comparison directly:

`sup_x |Phi(c x) - Phi(x)| <= |log c| / sqrt(2 pi)` for `c>0`.

The proof is educational and self-contained.  It identifies the derivative
of the Gaussian CDF from its density, differentiates `Phi(exp(t)x)`, bounds
`|y| phi(y)`, and applies the mean value theorem.  Thus equation
`normal-scale-comparison` in the manuscript is no longer an uncited calculus
step.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped Interval

noncomputable section

/-- Integral representation of the standard-normal CDF. -/
theorem standardGaussian_cdf_eq_integral_Iic (x : ℝ) :
    cdf (gaussianReal 0 1) x =
      ∫ y in Iic x, gaussianPDFReal 0 1 y := by
  rw [cdf_eq_real, measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg fun y ↦ gaussianPDFReal_nonneg 0 1 y

/-- The standard-normal CDF has derivative equal to its density. -/
theorem hasDerivAt_standardGaussian_cdf (x : ℝ) :
    HasDerivAt (cdf (gaussianReal 0 1)) (gaussianPDFReal 0 1 x) x := by
  let f : ℝ → ℝ := gaussianPDFReal 0 1
  let G : ℝ → ℝ := fun y ↦ ∫ t in Iic y, f t
  have hf : Integrable f := integrable_gaussianPDFReal 0 1
  have hfcont : Continuous f := by
    unfold f gaussianPDFReal
    fun_prop
  have hinterval : IntervalIntegrable f volume x x := hf.intervalIntegrable
  have hbase : HasDerivAt (fun y ↦ ∫ t in x..y, f t) (f x) x :=
    integral_hasDerivAt_right hinterval
      hfcont.stronglyMeasurable.stronglyMeasurableAtFilter hfcont.continuousAt
  let C : ℝ := G x
  have hG : G = fun y ↦ C + ∫ t in x..y, f t := by
    funext y
    unfold C G
    rw [← integral_Iic_sub_Iic (hf.integrableOn) (hf.integrableOn)]
    ring
  have hderivG : HasDerivAt G (f x) x := by
    rw [hG]
    exact hbase.const_add C
  have hCDF : cdf (gaussianReal 0 1) = G := by
    funext y
    exact standardGaussian_cdf_eq_integral_Iic y
  rw [hCDF]
  exact hderivG

/-- Elementary Gaussian-envelope inequality. -/
theorem abs_mul_exp_neg_sq_half_le_one (y : ℝ) :
    |y| * Real.exp (-(y ^ 2) / 2) ≤ 1 := by
  have hquad : |y| ≤ 1 + y ^ 2 / 2 := by
    nlinarith [sq_nonneg (|y| - 1), sq_abs y]
  have hexp : 1 + y ^ 2 / 2 ≤ Real.exp (y ^ 2 / 2) :=
    by simpa [add_comm] using Real.add_one_le_exp (y ^ 2 / 2)
  calc
    |y| * Real.exp (-(y ^ 2) / 2) ≤
        Real.exp (y ^ 2 / 2) * Real.exp (-(y ^ 2) / 2) :=
      mul_le_mul_of_nonneg_right (hquad.trans hexp) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero

/-- The logarithmic-scale derivative is uniformly bounded. -/
theorem abs_mul_standardGaussianPDFReal_le_peak (y : ℝ) :
    |y * gaussianPDFReal 0 1 y| ≤
      1 / Real.sqrt (2 * Real.pi) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hsqrt : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have henv := abs_mul_exp_neg_sq_half_le_one y
  rw [abs_mul, abs_mul, abs_of_nonneg hsqrt,
    abs_of_pos (Real.exp_pos _)]
  calc
    |y| * ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(y ^ 2) / 2)) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (|y| * Real.exp (-(y ^ 2) / 2)) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left henv hsqrt
    _ = 1 / Real.sqrt (2 * Real.pi) := by simp [one_div]

/-- Derivative of `t ↦ Phi(exp(t)x)`. -/
theorem hasDerivAt_standardGaussian_cdf_exp_mul (x t : ℝ) :
    HasDerivAt (fun u ↦ cdf (gaussianReal 0 1) (Real.exp u * x))
      (Real.exp t * x * gaussianPDFReal 0 1 (Real.exp t * x)) t := by
  have hinner : HasDerivAt (fun u : ℝ ↦ Real.exp u * x)
      (Real.exp t * x) t := (Real.hasDerivAt_exp t).mul_const x
  have hout := (hasDerivAt_standardGaussian_cdf (Real.exp t * x)).comp t hinner
  have hfun : (fun u ↦ cdf (gaussianReal 0 1) (Real.exp u * x)) =
      (fun y ↦ cdf (gaussianReal 0 1) y) ∘
        (fun u ↦ x * Real.exp u) := by
    funext u
    simp [mul_comm]
  rw [hfun]
  simpa [mul_comm] using hout

/-- Pointwise scale comparison. -/
theorem abs_standardGaussian_cdf_mul_sub_le_log
    {c : ℝ} (hc : 0 < c) (x : ℝ) :
    |cdf (gaussianReal 0 1) (c * x) - cdf (gaussianReal 0 1) x| ≤
      |Real.log c| / Real.sqrt (2 * Real.pi) := by
  let F : ℝ → ℝ := fun t ↦
    cdf (gaussianReal 0 1) (Real.exp t * x)
  let F' : ℝ → ℝ := fun t ↦
    Real.exp t * x * gaussianPDFReal 0 1 (Real.exp t * x)
  have hderiv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    exact hasDerivAt_standardGaussian_cdf_exp_mul x t
  have hbound : ∀ t : ℝ, ‖F' t‖ ≤ 1 / Real.sqrt (2 * Real.pi) := by
    intro t
    rw [Real.norm_eq_abs]
    exact abs_mul_standardGaussianPDFReal_le_peak (Real.exp t * x)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := F) (f' := F')
    (fun t _ht ↦ (hderiv t).hasDerivWithinAt)
    (fun t _ht ↦ hbound t) convex_univ (mem_univ 0)
      (mem_univ (Real.log c))
  unfold F at hmvt
  rw [Real.exp_log hc, Real.exp_zero, one_mul] at hmvt
  simpa [Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using hmvt

/-- Uniform normal-scale comparison, in the `supDistance` API used by the
Kolmogorov development. -/
theorem supDistance_standardGaussian_cdf_scale_le_log
    {c : ℝ} (hc : 0 < c) :
    supDistance (fun x ↦ cdf (gaussianReal 0 1) (c * x))
      (cdf (gaussianReal 0 1)) ≤
        |Real.log c| / Real.sqrt (2 * Real.pi) :=
  supDistance_le_of_bound fun x ↦
    abs_standardGaussian_cdf_mul_sub_le_log hc x

/-- CDF of a positive scalar multiple. -/
theorem cdf_map_const_mul
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {c : ℝ} (hc : 0 < c) (x : ℝ) :
    cdf (mu.map (fun y ↦ c * y)) x = cdf mu (x / c) := by
  have hmeas : Measurable (fun y : ℝ ↦ c * y) := by fun_prop
  let _ : IsProbabilityMeasure (mu.map (fun y ↦ c * y)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  rw [cdf_eq_real, cdf_eq_real,
    map_measureReal_apply hmeas measurableSet_Iic]
  congr 1
  ext y
  simp only [mem_preimage, mem_Iic]
  simpa [mul_comm] using (le_div_iff₀ hc).symm

/-- Replacing a normalization by a positive multiplicative scale costs at
most the logarithmic scale mismatch in Kolmogorov distance. -/
theorem kolmogorovDistance_map_const_mul_standardGaussian_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {c : ℝ} (hc : 0 < c) :
    kolmogorovDistance (mu.map (fun y ↦ c * y)) (gaussianReal 0 1) ≤
      kolmogorovDistance mu (gaussianReal 0 1) +
        |Real.log c| / Real.sqrt (2 * Real.pi) := by
  have hmeas : Measurable (fun y : ℝ ↦ c * y) := by fun_prop
  let _ : IsProbabilityMeasure (mu.map (fun y ↦ c * y)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  apply supDistance_le_of_bound
  intro x
  rw [cdf_map_const_mul mu hc]
  have hmu := point_le_supDistance
    (fun y ↦ abs_cdf_sub_cdf_le_one mu (gaussianReal 0 1) y) (x / c)
  have hnormal := abs_standardGaussian_cdf_mul_sub_le_log
    (show 0 < c⁻¹ by positivity) x
  have hscaleArg : c⁻¹ * x = x / c := by rw [div_eq_mul_inv, mul_comm]
  rw [hscaleArg, Real.log_inv, abs_neg] at hnormal
  calc
    |cdf mu (x / c) - cdf (gaussianReal 0 1) x| ≤
        |cdf mu (x / c) - cdf (gaussianReal 0 1) (x / c)| +
          |cdf (gaussianReal 0 1) (x / c) -
            cdf (gaussianReal 0 1) x| := by
      exact abs_sub_le _ _ _
    _ ≤ kolmogorovDistance mu (gaussianReal 0 1) +
        |Real.log c| / Real.sqrt (2 * Real.pi) := add_le_add hmu hnormal

/-- A relative squared-scale discrepancy controls the logarithmic scale
mismatch.  The constant one is sufficient for every rate argument here. -/
theorem abs_log_div_le_relative_sq_error
    {w s delta : ℝ} (hw : 0 < w) (hs : 0 < s)
    (hlower : 0 ≤ w ^ 2 - s ^ 2)
    (hupper : w ^ 2 - s ^ 2 ≤ delta * s ^ 2) :
    |Real.log (w / s)| ≤ delta := by
  have hsq : s ^ 2 ≤ w ^ 2 := by linarith
  have hsw : s ≤ w := (sq_le_sq₀ hs.le hw.le).mp hsq
  have hratioPos : 0 < w / s := div_pos hw hs
  have hratioOne : 1 ≤ w / s := (le_div_iff₀ hs).2 (by simpa using hsw)
  have hlogNonneg : 0 ≤ Real.log (w / s) := Real.log_nonneg hratioOne
  rw [abs_of_nonneg hlogNonneg]
  calc
    Real.log (w / s) ≤ w / s - 1 :=
      Real.log_le_sub_one_of_pos hratioPos
    _ ≤ (w / s) ^ 2 - 1 := by
      nlinarith [sq_nonneg (w / s - 1)]
    _ = (w ^ 2 - s ^ 2) / s ^ 2 := by
      field_simp [hs.ne']
    _ ≤ delta := by
      exact (div_le_iff₀ (sq_pos_of_pos hs)).2 hupper

/-- Scale replacement stated directly at the Kolmogorov level. -/
theorem kolmogorovDistance_scale_replacement_le_relative_sq_error
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {w s delta : ℝ} (hw : 0 < w) (hs : 0 < s)
    (hlower : 0 ≤ w ^ 2 - s ^ 2)
    (hupper : w ^ 2 - s ^ 2 ≤ delta * s ^ 2) :
    kolmogorovDistance (mu.map (fun y ↦ (w / s) * y))
        (gaussianReal 0 1) ≤
      kolmogorovDistance mu (gaussianReal 0 1) +
        delta / Real.sqrt (2 * Real.pi) := by
  have hratio : 0 < w / s := div_pos hw hs
  calc
    kolmogorovDistance (mu.map (fun y ↦ (w / s) * y))
        (gaussianReal 0 1) ≤
      kolmogorovDistance mu (gaussianReal 0 1) +
        |Real.log (w / s)| / Real.sqrt (2 * Real.pi) :=
      kolmogorovDistance_map_const_mul_standardGaussian_le mu hratio
    _ ≤ kolmogorovDistance mu (gaussianReal 0 1) +
        delta / Real.sqrt (2 * Real.pi) := by
      gcongr
      exact abs_log_div_le_relative_sq_error hw hs hlower hupper

end

end LogdetLean
