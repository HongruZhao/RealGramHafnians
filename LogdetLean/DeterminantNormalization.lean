import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt
/-!
# Determinant identities behind sample-correlation normalization

These results formalize the purely algebraic step that turns a covariance
matrix into a correlation matrix by scaling its rows and columns.
-/

namespace LogdetLean

open scoped Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Scaling both sides of a square matrix multiplies its determinant by the
square of the scaling determinant. -/
theorem det_two_sided_scale (D S : Matrix n n R) :
    (D * S * D).det = D.det ^ 2 * S.det := by
  rw [Matrix.det_mul, Matrix.det_mul]
  ring

/-- The determinant form specialized to a diagonal scaling matrix. -/
theorem det_diagonal_two_sided_scale (d : n → R) (S : Matrix n n R) :
    (Matrix.diagonal d * S * Matrix.diagonal d).det =
      (∏ i, d i) ^ 2 * S.det := by
  rw [det_two_sided_scale, Matrix.det_diagonal]

/-- A determinant-one diagonal rescaling does not change the determinant. -/
theorem det_preserved_by_unit_product_scale (d : n → R) (S : Matrix n n R)
    (hd : ∏ i, d i = 1) :
    (Matrix.diagonal d * S * Matrix.diagonal d).det = S.det := by
  rw [det_diagonal_two_sided_scale, hd]
  simp

/-- Exact determinant normalization for a correlation matrix.  If `s i` are
positive diagonal variances and `D = diag (1 / sqrt (s i))`, then
`det (D S D) = det S / ∏ i, s i`. -/
theorem det_correlation_normalization
    {n : Type*} [Fintype n] [DecidableEq n]
    (s : n → ℝ) (S : Matrix n n ℝ) (hs : ∀ i, 0 < s i) :
    (Matrix.diagonal (fun i ↦ (Real.sqrt (s i))⁻¹) * S *
        Matrix.diagonal (fun i ↦ (Real.sqrt (s i))⁻¹)).det =
      S.det / ∏ i, s i := by
  rw [det_diagonal_two_sided_scale]
  have hscale : (∏ i, (Real.sqrt (s i))⁻¹) ^ 2 = (∏ i, s i)⁻¹ := by
    rw [Finset.prod_inv_distrib, inv_pow, ← Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl (fun i _ ↦ Real.sq_sqrt (hs i).le)
  rw [hscale, div_eq_mul_inv]
  ring

end LogdetLean
