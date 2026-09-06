import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import LogdetLean.CorrelationMatrixAlgebra
import LogdetLean.CorrelationSpectralAlgebra
import LogdetLean.WishartScalarThird
import Mathlib.Tactic
/-!
# Spectral bridge for the correlation-matrix deviation

This file connects the elementary matrix energy `a_R=tr((R-I)^2)` to the
real eigenvalue family used in the general-`R` analytic transform.  It is the
finite-dimensional spectral step behind Zhao (2026), equation (5.22), and
the new manuscript's global third-derivative estimate.

Mathlib supplies the spectral theorem for Hermitian matrices.  Every trace,
positivity, and norm inequality below is proved from that theorem and the
already checked scalar bounds; none is assumed as a project axiom.
-/

namespace LogdetLean

noncomputable section

open Matrix Unitary
open scoped BigOperators InnerProductSpace

/-- The trace of the square of a real Hermitian matrix is the quadratic sum
of its real eigenvalues. -/
theorem trace_mul_self_eq_sum_eigenvalues_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i, (hA.eigenvalues i) ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_mul]
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  simp [pow_two]

namespace CorrelationMatrix

variable {p : ℕ} (R : CorrelationMatrix p)

/-- `A_R=R-I` is Hermitian. -/
theorem deviation_isHermitian : R.deviation.IsHermitian := by
  simpa [Matrix.IsHermitian] using R.deviation_transpose

/-- The real eigenvalues of `A_R=R-I`. -/
def deviationEigenvalues : Fin p → ℝ :=
  R.deviation_isHermitian.eigenvalues

/-- The trace energy is exactly the quadratic eigenvalue mass. -/
theorem deviationEnergy_eq_sum_eigenvalues_sq :
    R.deviationEnergy = ∑ i, (R.deviationEigenvalues i) ^ 2 := by
  exact trace_mul_self_eq_sum_eigenvalues_sq
    R.deviation R.deviation_isHermitian

/-- Positive definiteness of `R=I+A_R` says `1+lambda_i>0` for every
deviation eigenvalue.  The proof tests `R` on the corresponding normalized
eigenvector of `A_R`. -/
theorem one_add_deviationEigenvalue_pos (i : Fin p) :
    0 < 1 + R.deviationEigenvalues i := by
  let hA : R.deviation.IsHermitian := R.deviation_isHermitian
  let v : Fin p → ℝ := ⇑(hA.eigenvectorBasis i)
  have hv : v ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2 <|
      hA.eigenvectorBasis.orthonormal.ne_zero i
  have hAv : R.deviation *ᵥ v =
      (hA.eigenvalues i) • v := by
    simpa [v] using hA.mulVec_eigenvectorBasis i
  have hRv : R.val *ᵥ v =
      (1 + hA.eigenvalues i) • v := by
    rw [← R.one_add_deviation, Matrix.add_mulVec,
      Matrix.one_mulVec, hAv]
    ext j
    simp [add_mul]
  have hpos := R.posDef.dotProduct_mulVec_pos hv
  rw [hRv] at hpos
  have hvnorm : star v ⬝ᵥ v = 1 := by
    change ⟪hA.eigenvectorBasis i, hA.eigenvectorBasis i⟫_ℝ = 1
    rw [inner_self_eq_norm_sq_to_K,
      hA.eigenvectorBasis.norm_eq_one]
    norm_num
  rw [dotProduct_smul, hvnorm] at hpos
  simpa [deviationEigenvalues, hA] using hpos

/-- The cubic Schatten mass of `A_R` is controlled by `a_R^(3/2)`. -/
theorem sum_abs_deviationEigenvalues_cube_le :
    ∑ i, |R.deviationEigenvalues i| ^ 3 ≤
      Real.sqrt R.deviationEnergy * R.deviationEnergy := by
  have h := sum_abs_cube_le_sqrt_sum_sq_mul_sum_sq
    (s := Finset.univ) (x := R.deviationEigenvalues)
  simpa [R.deviationEnergy_eq_sum_eigenvalues_sq] using h

/-- Each deviation eigenvalue is bounded by `sqrt(a_R)`. -/
theorem abs_deviationEigenvalue_le_sqrt_energy (i : Fin p) :
    |R.deviationEigenvalues i| ≤ Real.sqrt R.deviationEnergy := by
  have h := abs_le_sqrt_sum_sq
    (s := Finset.univ) (x := R.deviationEigenvalues)
    (i := i) (Finset.mem_univ i)
  simpa [R.deviationEnergy_eq_sum_eigenvalues_sq] using h

/-- The verified scalar third-derivative estimate, now expressed entirely in
the matrix invariant `a_R`.  This is the deterministic spectral envelope
needed after the exact Wishart transform has been established. -/
theorem norm_sum_wishartScalarThird_deviation_le
    {m u : ℝ} (hm : 0 < m) :
    ‖∑ i, wishartScalarThirdExpression (m / 2)
        (1 + R.deviationEigenvalues i) (R.deviationEigenvalues i) u‖ ≤
      (12 * R.deviationEnergy) / m ^ 2 +
        (8 * (Real.sqrt R.deviationEnergy * R.deviationEnergy)) / m ^ 2 := by
  calc
    ‖∑ i, wishartScalarThirdExpression (m / 2)
        (1 + R.deviationEigenvalues i) (R.deviationEigenvalues i) u‖ ≤
        (12 * ∑ i, R.deviationEigenvalues i ^ 2) / m ^ 2 +
          (8 * ∑ i, |R.deviationEigenvalues i| ^ 3) / m ^ 2 :=
      norm_sum_wishartScalarThirdExpression_half_dimension_le
        (s := Finset.univ) R.deviationEigenvalues hm
    _ ≤ (12 * R.deviationEnergy) / m ^ 2 +
        (8 * (Real.sqrt R.deviationEnergy * R.deviationEnergy)) / m ^ 2 := by
      rw [← R.deviationEnergy_eq_sum_eigenvalues_sq]
      gcongr
      exact R.sum_abs_deviationEigenvalues_cube_le

end CorrelationMatrix
end
end LogdetLean
