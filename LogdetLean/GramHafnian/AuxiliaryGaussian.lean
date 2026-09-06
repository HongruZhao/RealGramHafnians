import LogdetLean.GramHafnian.AuxiliaryFieldExpansion
import LogdetLean.GramHafnian.GaussianEvenMoments
/-!
# Actual iid standard-Gaussian auxiliary field

This file discharges every analytic hypothesis of the generic colouring
expansion using the kernel-checked scalar Gaussian moment theorems.
-/

open scoped BigOperators Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

variable {I K : Type*} [Fintype I] [Fintype K]
  [DecidableEq I] [DecidableEq K]

/-- Exact scalar moment sequence of `N(0,1)`. -/
def standardRealGaussianMoment (r : ℕ) : ℝ :=
  if Even r then ((r - 1)‼ : ℝ) else 0

theorem integral_pow_gaussianReal_eq_standardRealGaussianMoment (r : ℕ) :
    (∫ x : ℝ, x ^ r ∂gaussianReal 0 1) = standardRealGaussianMoment r := by
  rcases Nat.even_or_odd r with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · simpa [two_mul, standardRealGaussianMoment] using
      integral_pow_two_gaussianReal n
  · have hne : ¬ Even (n + n + 1) :=
      Nat.not_even_iff_odd.mpr ⟨n, by omega⟩
    simpa [two_mul, standardRealGaussianMoment, hne] using
      integral_pow_odd_gaussianReal n

/-- Exact row-colouring formula for a real iid standard-Gaussian auxiliary
field and arbitrary complex deterministic coefficients. -/
theorem integral_complexAuxiliaryFieldProduct_standardGaussian
    (X : K → I → ℂ) :
    ∫ g, complexAuxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : K ↦ gaussianReal 0 1) =
      ∑ c : I → K,
        complexColoringCoefficient X c *
          ∏ a, (standardRealGaussianMoment (colorMultiplicity c a) : ℂ) := by
  exact integral_complexAuxiliaryFieldProduct_eq_weightedColoringSum
    (mu := gaussianReal 0 1)
    integrable_pow_gaussianReal
    standardRealGaussianMoment
    integral_pow_gaussianReal_eq_standardRealGaussianMoment
    X

/-- Real-coefficient specialization. -/
theorem integral_auxiliaryFieldProduct_standardGaussian
    (X : K → I → ℝ) :
    ∫ g, auxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : K ↦ gaussianReal 0 1) =
      ∑ c : I → K,
        coloringCoefficient X c *
          coloringMomentWeight standardRealGaussianMoment c := by
  exact integral_auxiliaryFieldProduct_eq_weightedColoringSum
    (mu := gaussianReal 0 1)
    integrable_pow_gaussianReal
    standardRealGaussianMoment
    integral_pow_gaussianReal_eq_standardRealGaussianMoment
    X

end LogdetLean.GramHafnian
