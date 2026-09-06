import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.ScoreAlgebra
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
/-!
# Divergence of the lifted conditional-Wishart score direction

For `M=RᵀR`, `G=M⁻¹`, and a symmetric direction `D`, the lifted field is

`V(R) = (1/2) R G D`.

Its linearization is

`E ↦ (1/2) [E G D - R G Eᵀ R G D - R G Rᵀ E G D]`.

This file computes the coordinate trace of that linearization.  It is the
finite-dimensional divergence and equals

`(card k - card m - 1)/2 * tr(GD)`.
-/

open scoped BigOperators Matrix.Norms.Operator

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*} [Fintype k] [Fintype m]
  [DecidableEq k] [DecidableEq m]

/-- Coordinate trace of an endomorphism of the rectangular matrix space.
For a differentiable map this is the usual divergence. -/
def rectangularCoordinateTrace
    (T : Matrix k m ℝ → Matrix k m ℝ) : ℝ :=
  ∑ a, ∑ i, T (Matrix.single a i 1) a i

theorem rectangularCoordinateTrace_add
    (T U : Matrix k m ℝ → Matrix k m ℝ) :
    rectangularCoordinateTrace (fun E ↦ T E + U E) =
      rectangularCoordinateTrace T + rectangularCoordinateTrace U := by
  simp [rectangularCoordinateTrace, Finset.sum_add_distrib]

theorem rectangularCoordinateTrace_sub
    (T U : Matrix k m ℝ → Matrix k m ℝ) :
    rectangularCoordinateTrace (fun E ↦ T E - U E) =
      rectangularCoordinateTrace T - rectangularCoordinateTrace U := by
  simp [rectangularCoordinateTrace, Finset.sum_sub_distrib]

theorem rectangularCoordinateTrace_smul (c : ℝ)
    (T : Matrix k m ℝ → Matrix k m ℝ) :
    rectangularCoordinateTrace (fun E ↦ c • T E) =
      c * rectangularCoordinateTrace T := by
  simp [rectangularCoordinateTrace, Finset.mul_sum]

/-- Trace of right multiplication `E ↦ EB`. -/
theorem rectangularCoordinateTrace_mul_right (B : Matrix m m ℝ) :
    rectangularCoordinateTrace (fun E : Matrix k m ℝ ↦ E * B) =
      (Fintype.card k : ℝ) * Matrix.trace B := by
  classical
  simp [rectangularCoordinateTrace, Matrix.mul_apply, Matrix.trace,
    Matrix.single_apply, Finset.sum_ite_eq, Finset.mem_univ,
    Finset.sum_const, nsmul_eq_mul]

/-- Trace of the transpose-sandwich operator `E ↦ A Eᵀ C`. -/
theorem rectangularCoordinateTrace_transpose_sandwich
    (A C : Matrix k m ℝ) :
    rectangularCoordinateTrace
        (fun E : Matrix k m ℝ ↦ A * E.transpose * C) =
      realFrobeniusInner A C := by
  classical
  unfold rectangularCoordinateTrace realFrobeniusInner
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- Trace of the two-sided multiplication operator `E ↦ PEB`. -/
theorem rectangularCoordinateTrace_two_sided
    (P : Matrix k k ℝ) (B : Matrix m m ℝ) :
    rectangularCoordinateTrace
        (fun E : Matrix k m ℝ ↦ P * E * B) =
      Matrix.trace P * Matrix.trace B := by
  classical
  unfold rectangularCoordinateTrace Matrix.trace
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq,
    Finset.mem_univ, Finset.sum_mul, Finset.mul_sum, ite_and]

/-- The explicit linearization of `R ↦ (1/2)R(RᵀR)⁻¹D`. -/
def steinVectorFieldLinearization
    (R : Matrix k m ℝ) (D : Matrix m m ℝ) :
    Matrix k m ℝ → Matrix k m ℝ :=
  fun E ↦
    (1 / 2 : ℝ) •
      (E * ((realWishartGram R)⁻¹ * D) -
        (R * (realWishartGram R)⁻¹) * E.transpose *
          (R * (realWishartGram R)⁻¹ * D) -
        (R * (realWishartGram R)⁻¹ * R.transpose) * E *
          ((realWishartGram R)⁻¹ * D))

/-- The inverse of a real Gram matrix is symmetric (also in the singular
case, since the nonsingular inverse commutes with transpose). -/
theorem realWishartGram_inv_isSymm (R : Matrix k m ℝ) :
    ((realWishartGram R)⁻¹).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  unfold realWishartGram
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The transpose-sandwich contribution has trace `tr(M⁻¹D)`. -/
theorem frobenius_inverseLift_eq_trace
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    realFrobeniusInner (R * (realWishartGram R)⁻¹)
        (R * (realWishartGram R)⁻¹ * D) =
      Matrix.trace ((realWishartGram R)⁻¹ * D) := by
  rw [realFrobeniusInner_eq_trace_transpose_mul]
  have hG := (realWishartGram_inv_isSymm R).eq
  rw [Matrix.transpose_mul, hG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc R.transpose R]
  change Matrix.trace
      ((realWishartGram R)⁻¹ *
        (realWishartGram R * ((realWishartGram R)⁻¹ * D))) = _
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hM]

/-- The `k×k` projection-like factor has trace equal to the column
dimension. -/
theorem trace_inverseGram_projection
    (R : Matrix k m ℝ) (hM : IsUnit (realWishartGram R).det) :
    Matrix.trace (R * (realWishartGram R)⁻¹ * R.transpose) =
      (Fintype.card m : ℝ) := by
  rw [Matrix.trace_mul_cycle]
  change Matrix.trace
      (realWishartGram R * (realWishartGram R)⁻¹) = _
  rw [Matrix.mul_nonsing_inv _ hM]
  exact Matrix.trace_one

/-- Exact divergence formula for the lifted rational vector field. -/
theorem rectangularCoordinateTrace_steinVectorFieldLinearization
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    rectangularCoordinateTrace (steinVectorFieldLinearization R D) =
      (((Fintype.card k : ℝ) - (Fintype.card m : ℝ) - 1) / 2) *
        Matrix.trace ((realWishartGram R)⁻¹ * D) := by
  rw [show steinVectorFieldLinearization R D = fun E ↦
      (1 / 2 : ℝ) •
        ((E * ((realWishartGram R)⁻¹ * D) -
          ((R * (realWishartGram R)⁻¹) * E.transpose *
            (R * (realWishartGram R)⁻¹ * D))) -
          ((R * (realWishartGram R)⁻¹ * R.transpose) * E *
            ((realWishartGram R)⁻¹ * D))) by
      rfl]
  rw [rectangularCoordinateTrace_smul,
    rectangularCoordinateTrace_sub, rectangularCoordinateTrace_sub,
    rectangularCoordinateTrace_mul_right,
    rectangularCoordinateTrace_transpose_sandwich,
    rectangularCoordinateTrace_two_sided,
    frobenius_inverseLift_eq_trace R D hM,
    trace_inverseGram_projection R hM]
  ring

end Wishart

end

end LogdetLean.GramHafnian
