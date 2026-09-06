import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.InverseIntegrability
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
/-!
# Deterministic bounds for inverse-matrix traces

These deliberately crude bounds reduce entries of a nonsingular inverse to
one reciprocal determinant times a polynomial in the entries.  They are
designed for Gaussian integrability, where any fixed polynomial is absorbed
by a small exponential tilt.
-/

open scoped BigOperators Nat

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem abs_mul_le_sq_add_sq (x y : ℝ) :
    |x * y| ≤ x ^ 2 + y ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]

/-- Sum of the absolute values of all matrix entries. -/
def matrixEntryAbsMass (A : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

theorem matrixEntryAbsMass_nonneg (A : Matrix n n ℝ) :
    0 ≤ matrixEntryAbsMass A := by
  unfold matrixEntryAbsMass
  positivity

/-- A convenient bound which also dominates the inserted `0` and `1`
entries appearing in the adjugate formula. -/
def matrixEntryUnitBound (A : Matrix n n ℝ) : ℝ :=
  max 1 (matrixEntryAbsMass A)

theorem one_le_matrixEntryUnitBound (A : Matrix n n ℝ) :
    1 ≤ matrixEntryUnitBound A := by
  exact le_max_left _ _

theorem abs_entry_le_matrixEntryUnitBound (A : Matrix n n ℝ) (i j : n) :
    |A i j| ≤ matrixEntryUnitBound A := by
  have hinner : |A i j| ≤ ∑ j', |A i j'| := by
    exact Finset.single_le_sum (fun j' _ ↦ abs_nonneg (A i j'))
      (Finset.mem_univ j)
  have houter : (∑ j', |A i j'|) ≤ ∑ i', ∑ j', |A i' j'| := by
    exact Finset.single_le_sum
      (fun i' _ ↦ Finset.sum_nonneg fun j' _ ↦ abs_nonneg (A i' j'))
      (Finset.mem_univ i)
  exact (hinner.trans houter).trans (le_max_right _ _)

theorem abs_updateRow_single_le_matrixEntryUnitBound
    (A : Matrix n n ℝ) (i j a b : n) :
    |(A.updateRow j (Pi.single i 1)) a b| ≤ matrixEntryUnitBound A := by
  by_cases ha : a = j
  · subst a
    by_cases hb : b = i
    · subst b
      simp [one_le_matrixEntryUnitBound]
    · simp [hb, one_le_matrixEntryUnitBound, matrixEntryUnitBound,
        matrixEntryAbsMass_nonneg]
  · simp [Matrix.updateRow_apply, ha, abs_entry_le_matrixEntryUnitBound]

/-- Every adjugate entry is bounded by the elementary Leibniz determinant
bound with entry size `max 1 (sum |Aᵢⱼ|)`. -/
theorem abs_adjugate_apply_le (A : Matrix n n ℝ) (i j : n) :
    |A.adjugate i j| ≤
      (Fintype.card n)! *
        (matrixEntryUnitBound A) ^ Fintype.card n := by
  rw [Matrix.adjugate_apply]
  simpa [AbsoluteValue.abs_apply, nsmul_eq_mul] using
    (Matrix.det_le
      (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ))
      (x := matrixEntryUnitBound A)
      (A := A.updateRow j (Pi.single i 1))
      (abs_updateRow_single_le_matrixEntryUnitBound A i j))

/-- Absolute trace of the adjugate is polynomially bounded. -/
theorem abs_trace_adjugate_le (A : Matrix n n ℝ) :
    |Matrix.trace A.adjugate| ≤
      (Fintype.card n : ℝ) *
        ((Fintype.card n)! *
          (matrixEntryUnitBound A) ^ Fintype.card n) := by
  calc
    |Matrix.trace A.adjugate| = |∑ i, A.adjugate i i| := rfl
    _ ≤ ∑ i, |A.adjugate i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n,
        ((Fintype.card n)! *
          (matrixEntryUnitBound A) ^ Fintype.card n) := by
      exact Finset.sum_le_sum fun i _ ↦ abs_adjugate_apply_le A i i
    _ = (Fintype.card n : ℝ) *
        ((Fintype.card n)! *
          (matrixEntryUnitBound A) ^ Fintype.card n) := by
      simp [nsmul_eq_mul]

/-- On the nonsingular set, the inverse trace is dominated by reciprocal
determinant times an explicit polynomial. -/
theorem abs_trace_nonsingInv_le (A : Matrix n n ℝ)
    : |Matrix.trace A⁻¹| ≤
      |A.det|⁻¹ *
        ((Fintype.card n : ℝ) *
          ((Fintype.card n)! *
            (matrixEntryUnitBound A) ^ Fintype.card n)) := by
  rw [Matrix.inv_def, Matrix.trace_smul]
  simp only [smul_eq_mul, Ring.inverse_eq_inv]
  rw [abs_mul, abs_inv]
  exact mul_le_mul_of_nonneg_left (abs_trace_adjugate_le A) (by positivity)

section Gram

variable {k : Type*} [Fintype k]

/-- Squared Frobenius mass of a real rectangular matrix. -/
def rectangularSqMass (R : Matrix k n ℝ) : ℝ :=
  ∑ a, ∑ i, (R a i) ^ 2

theorem rectangularSqMass_nonneg (R : Matrix k n ℝ) :
    0 ≤ rectangularSqMass R := by
  unfold rectangularSqMass
  positivity

theorem column_sqMass_le_rectangularSqMass
    (R : Matrix k n ℝ) (i : n) :
    (∑ a, (R a i) ^ 2) ≤ rectangularSqMass R := by
  unfold rectangularSqMass
  apply Finset.sum_le_sum
  intro a _
  exact Finset.single_le_sum
    (fun j _ ↦ sq_nonneg (R a j)) (Finset.mem_univ i)

theorem abs_realWishartGram_entry_le
    (R : Matrix k n ℝ) (i j : n) :
    |realWishartGram R i j| ≤ 2 * rectangularSqMass R := by
  calc
    |realWishartGram R i j| = |∑ a, R a i * R a j| := by
      rfl
    _ ≤ ∑ a, |R a i * R a j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ((R a i) ^ 2 + (R a j) ^ 2) := by
      exact Finset.sum_le_sum fun a _ ↦ abs_mul_le_sq_add_sq _ _
    _ = (∑ a, (R a i) ^ 2) + (∑ a, (R a j) ^ 2) := by
      rw [Finset.sum_add_distrib]
    _ ≤ rectangularSqMass R + rectangularSqMass R :=
      add_le_add (column_sqMass_le_rectangularSqMass R i)
        (column_sqMass_le_rectangularSqMass R j)
    _ = 2 * rectangularSqMass R := by ring

/-- The entrywise mass of a Gram matrix is at most a fixed dimension
constant times the squared Frobenius mass of its rectangular factor. -/
theorem matrixEntryAbsMass_realWishartGram_le (R : Matrix k n ℝ) :
    matrixEntryAbsMass (realWishartGram R) ≤
      (Fintype.card n : ℝ) ^ 2 * (2 * rectangularSqMass R) := by
  unfold matrixEntryAbsMass
  calc
    (∑ i, ∑ j, |realWishartGram R i j|) ≤
        ∑ _i : n, ∑ _j : n, 2 * rectangularSqMass R := by
      exact Finset.sum_le_sum fun i _ ↦
        Finset.sum_le_sum fun j _ ↦ abs_realWishartGram_entry_le R i j
    _ = (Fintype.card n : ℝ) ^ 2 * (2 * rectangularSqMass R) := by
      simp [nsmul_eq_mul]
      ring

end Gram

end Wishart

end

end LogdetLean.GramHafnian
