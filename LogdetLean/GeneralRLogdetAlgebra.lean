import LogdetLean.DeterminantNormalization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
/-!
# Exact log-determinant algebra for the general-correlation branch

This module isolates the deterministic content of equation (5.1) in Zhao
(2026), arXiv:2608.00565v1.  If a positive scatter matrix has the form
`B * W * B`, correlation normalization subtracts the logarithms of its
diagonal entries, while the determinant contributes twice `log det B` plus
`log det W`.

The future Wishart module will provide the random matrices and positivity
hypotheses.  No Wishart or probabilistic statement is assumed here.
-/

namespace LogdetLean

open scoped BigOperators Matrix

noncomputable section

/-- Correlation normalization of a real square matrix using its own diagonal.
This is defined everywhere; positivity is imposed only in the theorems that
take logarithms. -/
def correlationNormalizeMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i ↦ (Real.sqrt (S i i))⁻¹) * S *
    Matrix.diagonal (fun i ↦ (Real.sqrt (S i i))⁻¹)

/-- Exact determinant of correlation normalization. -/
theorem det_correlationNormalizeMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < S i i) :
    (correlationNormalizeMatrix S).det = S.det / ∏ i, S i i := by
  exact det_correlation_normalization (fun i ↦ S i i) S hdiag

/-- Logarithmic determinant identity for a two-sided scatter factorization.
It is the deterministic algebra in equation (5.1); the later probabilistic
specialization takes `B=R^(1/2)`, so `2 log(det B)=log(det R)`. -/
theorem log_det_correlationNormalize_two_sided
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B W : Matrix ι ι ℝ)
    (hB : 0 < B.det) (hW : 0 < W.det)
    (hdiag : ∀ i, 0 < (B * W * B) i i) :
    Real.log (correlationNormalizeMatrix (B * W * B)).det =
      2 * Real.log B.det + Real.log W.det -
        ∑ i, Real.log ((B * W * B) i i) := by
  have hB0 : B.det ≠ 0 := hB.ne'
  have hW0 : W.det ≠ 0 := hW.ne'
  have hprod0 : (∏ i, (B * W * B) i i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _hi ↦ (hdiag i).ne'
  have hscatter0 : (B * W * B).det ≠ 0 := by
    rw [det_two_sided_scale]
    exact mul_ne_zero (pow_ne_zero 2 hB0) hW0
  rw [det_correlationNormalizeMatrix _ hdiag]
  rw [Real.log_div hscatter0 hprod0]
  rw [det_two_sided_scale]
  rw [Real.log_mul (pow_ne_zero 2 hB0) hW0]
  rw [Real.log_pow]
  rw [Real.log_prod (fun i _hi ↦ (hdiag i).ne')]
  norm_num

/-- A determinant-square identity supplies the population log determinant
without choosing a matrix square-root API. -/
theorem two_mul_log_det_eq_log_det_of_det_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B R : Matrix ι ι ℝ) (_hB : 0 < B.det) (_hR : 0 < R.det)
    (hsq : R.det = B.det ^ 2) :
    2 * Real.log B.det = Real.log R.det := by
  rw [hsq, Real.log_pow]
  norm_num

/-- Equation (5.1) after supplying the population determinant identity. -/
theorem log_det_correlationNormalize_eq_population_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B R W : Matrix ι ι ℝ)
    (hB : 0 < B.det) (hR : 0 < R.det) (hW : 0 < W.det)
    (hsq : R.det = B.det ^ 2)
    (hdiag : ∀ i, 0 < (B * W * B) i i) :
    Real.log (correlationNormalizeMatrix (B * W * B)).det =
      Real.log R.det + Real.log W.det -
        ∑ i, Real.log ((B * W * B) i i) := by
  rw [log_det_correlationNormalize_two_sided B W hB hW hdiag]
  rw [two_mul_log_det_eq_log_det_of_det_square B R hB hR hsq]

end

end LogdetLean
