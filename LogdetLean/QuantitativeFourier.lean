import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.CDF
import Mathlib.Tactic
import LogdetLean.KolmogorovDistance
/-!
# Reusable quantitative Fourier bookkeeping

Mathlib currently provides characteristic functions and Fourier inversion for
integrable densities, but not Esseen's CDF smoothing inequality.  This file
therefore formalizes the parts that can be shared without assuming such a
theorem: the truncated weighted characteristic-function discrepancy, its
triangle inequality, quantitative integration of a local Taylor bound, and a
precise interface through which a future smoothing theorem yields a
Kolmogorov bound.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The Esseen integrand.  Lean's division is total, so its value at `t = 0`
is zero; local cancellation hypotheses control the punctured neighborhood. -/
def fourierQuotientError (φ ψ : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖φ t - ψ t‖ / |t|

/-- The truncated weighted Fourier discrepancy on `[-T,T]`. -/
def truncatedFourierDiscrepancy (φ ψ : ℝ → ℂ) (T : ℝ) : ℝ :=
  ∫ t in Icc (-T) T, fourierQuotientError φ ψ t

/-- Specialization to characteristic functions of finite measures. -/
def truncatedCharFunDiscrepancy (μ ν : Measure ℝ) (T : ℝ) : ℝ :=
  truncatedFourierDiscrepancy (charFun μ) (charFun ν) T

theorem fourierQuotientError_nonneg (φ ψ : ℝ → ℂ) (t : ℝ) :
    0 ≤ fourierQuotientError φ ψ t := by
  unfold fourierQuotientError
  positivity

theorem truncatedFourierDiscrepancy_nonneg (φ ψ : ℝ → ℂ) (T : ℝ) :
    0 ≤ truncatedFourierDiscrepancy φ ψ T := by
  exact integral_nonneg fun _ ↦ fourierQuotientError_nonneg _ _ _

@[simp] theorem truncatedFourierDiscrepancy_self (φ : ℝ → ℂ) (T : ℝ) :
    truncatedFourierDiscrepancy φ φ T = 0 := by
  simp [truncatedFourierDiscrepancy, fourierQuotientError]

theorem truncatedFourierDiscrepancy_comm (φ ψ : ℝ → ℂ) (T : ℝ) :
    truncatedFourierDiscrepancy φ ψ T =
      truncatedFourierDiscrepancy ψ φ T := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    simp only [fourierQuotientError]
    rw [norm_sub_rev]

/-- The weighted discrepancy satisfies a triangle inequality whenever the two
right-hand integrands are integrable on the truncation interval. -/
theorem truncatedFourierDiscrepancy_triangle
    (φ ψ χ : ℝ → ℂ) (T : ℝ)
    (hφψ : IntegrableOn (fourierQuotientError φ ψ) (Icc (-T) T))
    (hψχ : IntegrableOn (fourierQuotientError ψ χ) (Icc (-T) T)) :
    truncatedFourierDiscrepancy φ χ T ≤
      truncatedFourierDiscrepancy φ ψ T +
        truncatedFourierDiscrepancy ψ χ T := by
  unfold truncatedFourierDiscrepancy
  rw [← integral_add hφψ hψχ]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun t ↦ fourierQuotientError_nonneg _ _ _
  · exact hφψ.add hψχ
  · exact Filter.Eventually.of_forall fun t ↦ by
      unfold fourierQuotientError
      change ‖φ t - χ t‖ / |t| ≤
        ‖φ t - ψ t‖ / |t| + ‖ψ t - χ t‖ / |t|
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (abs_nonneg t)
      calc
        ‖φ t - χ t‖ = ‖(φ t - ψ t) + (ψ t - χ t)‖ := by congr 1; ring
        _ ≤ ‖φ t - ψ t‖ + ‖ψ t - χ t‖ := norm_add_le _ _

/-- A local order-`n+1` characteristic-function error gives an explicit
truncated Esseen-integral bound.  The constant `2` is intentionally elementary
and uniform; no power-integration library theorem is needed. -/
theorem truncatedFourierDiscrepancy_le_of_local_pow
    {φ ψ : ℝ → ℂ} {T C : ℝ} {n : ℕ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hlocal : ∀ t ∈ Icc (-T) T,
      ‖φ t - ψ t‖ ≤ C * |t| ^ (n + 1)) :
    truncatedFourierDiscrepancy φ ψ T ≤ 2 * C * T ^ (n + 1) := by
  have hconst : Integrable
      (fun _ : ℝ ↦ C * T ^ n) (volume.restrict (Icc (-T) T)) :=
    integrableOn_const (by simp [Real.volume_Icc])
  have hpoint : ∀ t ∈ Icc (-T) T,
      fourierQuotientError φ ψ t ≤ C * T ^ n := by
    intro t ht
    by_cases ht0 : t = 0
    · simp only [ht0, fourierQuotientError, abs_zero, div_zero]
      exact mul_nonneg hC (pow_nonneg hT n)
    · have habspos : 0 < |t| := abs_pos.mpr ht0
      have hquot : fourierQuotientError φ ψ t ≤ C * |t| ^ n := by
        unfold fourierQuotientError
        rw [div_le_iff₀ habspos]
        calc
          ‖φ t - ψ t‖ ≤ C * |t| ^ (n + 1) := hlocal t ht
          _ = (C * |t| ^ n) * |t| := by rw [pow_succ]; ring
      have habsT : |t| ≤ T := by
        rw [abs_le]
        exact ⟨by linarith [ht.1], ht.2⟩
      have hp := pow_le_pow_left₀ (abs_nonneg t) habsT n
      exact hquot.trans (mul_le_mul_of_nonneg_left hp hC)
  unfold truncatedFourierDiscrepancy
  calc
    (∫ t in Icc (-T) T, fourierQuotientError φ ψ t) ≤
        ∫ _t : ℝ, C * T ^ n ∂(volume.restrict (Icc (-T) T)) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ ↦ fourierQuotientError_nonneg _ _ _
      · exact hconst
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hpoint t ht
    _ = 2 * C * T ^ (n + 1) := by
      rw [integral_const, measureReal_restrict_apply MeasurableSet.univ]
      simp only [univ_inter, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ T - -T), smul_eq_mul]
      rw [pow_succ]
      ring

/-- The exact hypothesis supplied by an Esseen-type smoothing theorem.  This
is a proposition, not an axiom: later files must construct a proof of it. -/
def HasFourierSmoothingBound (μ ν : Measure ℝ)
    (T smoothingConstant remainder : ℝ) : Prop :=
  ∀ x,
    |cdf μ x - cdf ν x| ≤
      smoothingConstant * truncatedCharFunDiscrepancy μ ν T + remainder

/-- Once a smoothing bound has been established, it immediately controls
Kolmogorov distance. -/
theorem kolmogorovDistance_le_of_fourierSmoothingBound
    (μ ν : Measure ℝ) {T smoothingConstant remainder : ℝ}
    (h : HasFourierSmoothingBound μ ν T smoothingConstant remainder) :
    kolmogorovDistance μ ν ≤
      smoothingConstant * truncatedCharFunDiscrepancy μ ν T + remainder :=
  supDistance_le_of_bound h

/-- Complete reusable assembly: a smoothing certificate plus a local
order-`n+1` characteristic-function estimate yields an explicit Kolmogorov
bound. -/
theorem kolmogorovDistance_le_of_smoothing_and_local_pow
    (μ ν : Measure ℝ) {T smoothingConstant remainder C : ℝ} {n : ℕ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hsmooth : 0 ≤ smoothingConstant)
    (hsmoothing :
      HasFourierSmoothingBound μ ν T smoothingConstant remainder)
    (hlocal : ∀ t ∈ Icc (-T) T,
      ‖charFun μ t - charFun ν t‖ ≤ C * |t| ^ (n + 1)) :
    kolmogorovDistance μ ν ≤
      smoothingConstant * (2 * C * T ^ (n + 1)) + remainder := by
  calc
    kolmogorovDistance μ ν ≤
        smoothingConstant * truncatedCharFunDiscrepancy μ ν T + remainder :=
      kolmogorovDistance_le_of_fourierSmoothingBound μ ν hsmoothing
    _ ≤ smoothingConstant * (2 * C * T ^ (n + 1)) + remainder := by
      simpa [truncatedCharFunDiscrepancy] using
        add_le_add_right
          (mul_le_mul_of_nonneg_left
            (truncatedFourierDiscrepancy_le_of_local_pow hT hC hlocal) hsmooth)
          remainder

end

end LogdetLean
