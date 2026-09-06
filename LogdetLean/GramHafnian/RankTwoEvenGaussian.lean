import LogdetLean.GramHafnian.RankTwoDiagonalGaussian
/-!
# Explicit even-index form of the diagonal rank-two moment

This file removes all vanishing odd terms from the general diagonal moment
identity.  The result is the conventional finite sum with squared odd double
factorials.  It is still completely axiom-free.
-/

open scoped BigOperators Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

theorem standardRealGaussianMoment_two_mul (j : Nat) :
    standardRealGaussianMoment (2 * j) = (((2 * j - 1)‼) : Real) := by
  rw [← integral_pow_gaussianReal_eq_standardRealGaussianMoment]
  exact integral_pow_two_gaussianReal j

theorem standardRealGaussianMoment_two_mul_add_one (j : Nat) :
    standardRealGaussianMoment (2 * j + 1) = 0 := by
  rw [← integral_pow_gaussianReal_eq_standardRealGaussianMoment]
  exact integral_pow_odd_gaussianReal j

/-- Reindex a sum over `0,...,2n` when every odd-indexed term vanishes. -/
theorem sum_range_two_mul_add_one_of_odd_eq_zero
    {R : Type*} [AddCommMonoid R] (f : Nat → R)
    (hodd : ∀ j, f (2 * j + 1) = 0) (n : Nat) :
    (∑ r ∈ Finset.range (2 * n + 1), f r) =
      ∑ j ∈ Finset.range (n + 1), f (2 * j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ r ∈ Finset.range (2 * (n + 1) + 1), f r) =
            (∑ r ∈ Finset.range (2 * n + 1), f r) +
              f (2 * n + 1) + f (2 * n + 2) := by
                rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
                  Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (∑ j ∈ Finset.range (n + 1), f (2 * j)) +
              f (2 * (n + 1)) := by
                rw [ih, hodd n]
                simp
                congr 2
        _ = ∑ j ∈ Finset.range (n + 1 + 1), f (2 * j) := by
              exact (Finset.sum_range_succ (f := fun j ↦ f (2 * j)) (n + 1)).symm

/-- The exact even-binomial/double-factorial form of the diagonal rank-two
Gaussian moment. -/
theorem integral_diagonalRankTwoBilinear_pow_two_mul_even_sum
    (lambdaPlus lambdaMinus : Real) (n : Nat) :
    (∫ w, diagonalRankTwoBilinear lambdaPlus lambdaMinus w ^ (2 * n)
        ∂twoStandardGaussianPairs) =
      ∑ j ∈ Finset.range (n + 1),
        ((2 * n).choose (2 * j) : Real) * lambdaPlus ^ (2 * j) *
          lambdaMinus ^ (2 * (n - j)) *
          ((((2 * j - 1)‼) : Real) *
            (((2 * (n - j) - 1)‼) : Real)) ^ 2 := by
  rw [integral_diagonalRankTwoBilinear_pow_two_mul]
  let f : Nat → Real := fun r ↦
    ((2 * n).choose r : Real) * lambdaPlus ^ r *
      lambdaMinus ^ (2 * n - r) *
      (standardRealGaussianMoment r *
        standardRealGaussianMoment (2 * n - r)) ^ 2
  have hodd : ∀ j, f (2 * j + 1) = 0 := by
    intro j
    unfold f
    rw [standardRealGaussianMoment_two_mul_add_one]
    ring
  rw [show (∑ r ∈ Finset.range (2 * n + 1),
      ((2 * n).choose r : Real) * lambdaPlus ^ r *
        lambdaMinus ^ (2 * n - r) *
        (standardRealGaussianMoment r *
          standardRealGaussianMoment (2 * n - r)) ^ 2) =
      ∑ r ∈ Finset.range (2 * n + 1), f r by rfl]
  rw [sum_range_two_mul_add_one_of_odd_eq_zero f hodd n]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsub : 2 * n - 2 * j = 2 * (n - j) := by omega
  unfold f
  rw [hsub, standardRealGaussianMoment_two_mul,
    standardRealGaussianMoment_two_mul]

end

end LogdetLean.GramHafnian
