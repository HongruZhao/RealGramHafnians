import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
import LogdetLean.EdgeworthTransfer
/-!
# The signed first-order Edgeworth CDF comparator

The first Edgeworth approximation is generally a signed approximation rather
than the CDF of a probability measure.  We therefore represent it as a real
function and prove its exact uniform distance from the Gaussian CDF.  This
avoids silently asserting positivity or monotonicity that need not hold.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The standard-normal CDF with the signed first Edgeworth correction. -/
def signedFirstEdgeworthCDF (lambda x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x - lambda * normalEdgeworthShape x

/-- The comparator differs from the Gaussian CDF by exactly the signed shape. -/
theorem signedFirstEdgeworthCDF_sub_gaussianCDF (lambda x : ℝ) :
    signedFirstEdgeworthCDF lambda x - cdf (gaussianReal 0 1) x =
      -lambda * normalEdgeworthShape x := by
  simp [signedFirstEdgeworthCDF]

/-- Exact uniform distance between the signed first-order comparator and the
Gaussian CDF. -/
theorem supDistance_signedFirstEdgeworthCDF_gaussianCDF (lambda : ℝ) :
    supDistance (signedFirstEdgeworthCDF lambda)
      (cdf (gaussianReal 0 1)) =
        |lambda| / Real.sqrt (2 * Real.pi) := by
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hbound : ∀ x,
      |signedFirstEdgeworthCDF lambda x - cdf (gaussianReal 0 1) x| ≤
        |lambda| / Real.sqrt (2 * Real.pi) := by
    intro x
    rw [signedFirstEdgeworthCDF_sub_gaussianCDF, abs_mul, abs_neg]
    have hshape := abs_normalEdgeworthShape_le x
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hshape (abs_nonneg lambda)
  apply le_antisymm (supDistance_le_of_bound hbound)
  have hzero := point_le_supDistance hbound 0
  rw [signedFirstEdgeworthCDF_sub_gaussianCDF,
    normalEdgeworthShape_zero, abs_mul, abs_neg, abs_of_nonneg hc] at hzero
  simpa [div_eq_mul_inv] using hzero

/-- Exact distance between two first-order signed comparators. -/
theorem supDistance_signedFirstEdgeworthCDF
    (lambda kappa : ℝ) :
    supDistance (signedFirstEdgeworthCDF lambda)
      (signedFirstEdgeworthCDF kappa) =
        |lambda - kappa| / Real.sqrt (2 * Real.pi) := by
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hdiff : ∀ x,
      signedFirstEdgeworthCDF lambda x - signedFirstEdgeworthCDF kappa x =
        -(lambda - kappa) * normalEdgeworthShape x := by
    intro x
    simp [signedFirstEdgeworthCDF]
    ring
  have hbound : ∀ x,
      |signedFirstEdgeworthCDF lambda x - signedFirstEdgeworthCDF kappa x| ≤
        |lambda - kappa| / Real.sqrt (2 * Real.pi) := by
    intro x
    rw [hdiff, abs_mul, abs_neg]
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (abs_normalEdgeworthShape_le x)
        (abs_nonneg (lambda - kappa))
  apply le_antisymm (supDistance_le_of_bound hbound)
  have hzero := point_le_supDistance hbound 0
  rw [hdiff, normalEdgeworthShape_zero, abs_mul, abs_neg,
    abs_of_nonneg hc] at hzero
  simpa [div_eq_mul_inv] using hzero

end

end LogdetLean
