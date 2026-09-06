import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
/-!
# Elementary spectral power bounds for the general-correlation branch

This module formalizes the scalar inequality behind equation (5.22) of
Zhao (2026), arXiv:2608.00565v1.  If the real eigenvalues of a symmetric
matrix are bounded in absolute value by `L`, then every trace power of order
at least two is controlled by the squared Frobenius mass times `L^(k-2)`.

The statement is deliberately formulated for a finite family of real numbers.
The later spectral-theorem module only has to identify those numbers with the
eigenvalues of the matrix.  No matrix spectral theorem is assumed here.
-/

namespace LogdetLean

open scoped BigOperators

noncomputable section

/-- Pointwise power estimate used in trace-power bounds. -/
theorem abs_pow_le_sq_mul_bound_pow
    {x L : ℝ} (_hL : 0 ≤ L) (hx : |x| ≤ L) {k : ℕ} (hk : 2 ≤ k) :
    |x ^ k| ≤ x ^ 2 * L ^ (k - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hpow : |x| ^ n ≤ L ^ n := pow_le_pow_left₀ (abs_nonneg x) hx n
  calc
    |x ^ (n + 2)| = |x| ^ n * |x| ^ 2 := by
      rw [abs_pow]
      ring
    _ ≤ L ^ n * |x| ^ 2 := by
      exact mul_le_mul_of_nonneg_right hpow (sq_nonneg |x|)
    _ = x ^ 2 * L ^ ((n + 2) - 2) := by
      rw [show (n + 2) - 2 = n by omega]
      rw [sq_abs]
      ring

/-- Finite spectral trace-power estimate.  In a later application `x i` are
the eigenvalues of `A`, `L` is an operator-norm bound, and the right-hand
quadratic sum is `tr(A^2)`. -/
theorem abs_sum_pow_le_bound_pow_mul_sum_sq
    {ι : Type*} {s : Finset ι} {x : ι → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hx : ∀ i ∈ s, |x i| ≤ L)
    {k : ℕ} (hk : 2 ≤ k) :
    |∑ i ∈ s, x i ^ k| ≤ L ^ (k - 2) * ∑ i ∈ s, x i ^ 2 := by
  calc
    |∑ i ∈ s, x i ^ k| ≤ ∑ i ∈ s, |x i ^ k| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (x i ^ 2 * L ^ (k - 2)) := by
      exact Finset.sum_le_sum fun i hi ↦
        abs_pow_le_sq_mul_bound_pow hL (hx i hi) hk
    _ = L ^ (k - 2) * ∑ i ∈ s, x i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- Cubic specialization of the trace-power estimate. -/
theorem abs_sum_cube_le_bound_mul_sum_sq
    {ι : Type*} {s : Finset ι} {x : ι → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hx : ∀ i ∈ s, |x i| ≤ L) :
    |∑ i ∈ s, x i ^ 3| ≤ L * ∑ i ∈ s, x i ^ 2 := by
  simpa using
    (abs_sum_pow_le_bound_pow_mul_sum_sq hL hx (k := 3) (by norm_num))

/-- Fourth-power specialization of the trace-power estimate. -/
theorem abs_sum_fourth_le_bound_sq_mul_sum_sq
    {ι : Type*} {s : Finset ι} {x : ι → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hx : ∀ i ∈ s, |x i| ≤ L) :
    |∑ i ∈ s, x i ^ 4| ≤ L ^ 2 * ∑ i ∈ s, x i ^ 2 := by
  simpa using
    (abs_sum_pow_le_bound_pow_mul_sum_sq hL hx (k := 4) (by norm_num))

/-- Every member of a finite real family is bounded by the square root of its
total quadratic mass. -/
theorem abs_le_sqrt_sum_sq
    {ι : Type*} {s : Finset ι} {x : ι → ℝ} {i : ι} (hi : i ∈ s) :
    |x i| ≤ Real.sqrt (∑ j ∈ s, x j ^ 2) := by
  have hsum : 0 ≤ ∑ j ∈ s, x j ^ 2 := by positivity
  have hsingle : x i ^ 2 ≤ ∑ j ∈ s, x j ^ 2 := by
    exact Finset.single_le_sum
      (fun j _hj ↦ sq_nonneg (x j)) hi
  calc
    |x i| = Real.sqrt (x i ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (∑ j ∈ s, x j ^ 2) := Real.sqrt_le_sqrt hsingle

/-- Eigenvalue-only form of equation (5.22): the quadratic mass itself
provides a universal bound on every member of the family. -/
theorem abs_sum_pow_le_sqrt_sum_sq_pow_mul_sum_sq
    {ι : Type*} {s : Finset ι} {x : ι → ℝ}
    {k : ℕ} (hk : 2 ≤ k) :
    |∑ i ∈ s, x i ^ k| ≤
      (Real.sqrt (∑ i ∈ s, x i ^ 2)) ^ (k - 2) *
        ∑ i ∈ s, x i ^ 2 := by
  have hsum : 0 ≤ ∑ i ∈ s, x i ^ 2 := by positivity
  exact abs_sum_pow_le_bound_pow_mul_sum_sq
    (Real.sqrt_nonneg _) (fun i hi ↦ abs_le_sqrt_sum_sq hi) hk

/-- Cubic Schatten inequality in the exact form used by the
general-correlation bound: `sum |lambda|^3 <= (sum lambda^2)^(3/2)`. -/
theorem sum_abs_cube_le_sqrt_sum_sq_mul_sum_sq
    {ι : Type*} {s : Finset ι} {x : ι → ℝ} :
    ∑ i ∈ s, |x i| ^ 3 ≤
      Real.sqrt (∑ i ∈ s, x i ^ 2) * ∑ i ∈ s, x i ^ 2 := by
  have hpoint : ∀ i ∈ s,
      |x i| ^ 3 ≤
        Real.sqrt (∑ j ∈ s, x j ^ 2) * x i ^ 2 := by
    intro i hi
    have hiBound := abs_le_sqrt_sum_sq (x := x) hi
    have hiSq : 0 ≤ x i ^ 2 := sq_nonneg _
    calc
      |x i| ^ 3 = |x i| * x i ^ 2 := by
        rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, sq_abs]
      _ ≤ Real.sqrt (∑ j ∈ s, x j ^ 2) * x i ^ 2 :=
        mul_le_mul_of_nonneg_right hiBound hiSq
  calc
    ∑ i ∈ s, |x i| ^ 3 ≤
        ∑ i ∈ s, Real.sqrt (∑ j ∈ s, x j ^ 2) * x i ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = Real.sqrt (∑ i ∈ s, x i ^ 2) * ∑ i ∈ s, x i ^ 2 := by
      rw [Finset.mul_sum]

end

end LogdetLean
