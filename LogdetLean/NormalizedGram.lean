import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic
import LogdetLean.DeterminantNormalization
/-!
# Normalized Gram matrices

This file formalizes the deterministic first part of Rouault's Uniform Gram
construction.  A sample correlation matrix under the null is the Gram matrix
of independently normalized Gaussian columns.  Before probability enters, its
determinant is exactly the determinant of the unnormalized Gram matrix divided
by the product of the squared column norms.

The convention `0⁻¹ = 0` makes the identities valid even for a zero column.
Gaussian columns are nonzero almost surely; that probabilistic fact is proved
separately in the bridge development.

Mathematical provenance: Rouault (2005), Section 2.1, equations (8)--(10),
printed pp. 4--5, and Rouault (2007), equations (2.4)--(2.7), printed
pp. 185--186.  See `PROVENANCE.md` for complete bibliographic data and the
notation map.  The identities are reproved here; no published theorem is
imported as an axiom.
-/

namespace LogdetLean

open scoped BigOperators

noncomputable section

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalize a vector, using the totalized inverse convention at zero. -/
def normalizeVector (x : E) : E := ‖x‖⁻¹ • x

/-- Gram matrix of a finite family after normalizing every vector. -/
def normalizedGram (v : ι → E) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (fun i ↦ normalizeVector (v i))

/-- Normalizing the vectors is the same as scaling the two sides of their
Gram matrix by the inverse norms. -/
theorem normalizedGram_eq_diagonal_mul_gram_mul_diagonal
    [Fintype ι] [DecidableEq ι] (v : ι → E) :
    normalizedGram v =
      Matrix.diagonal (fun i ↦ ‖v i‖⁻¹) * Matrix.gram ℝ v *
        Matrix.diagonal (fun i ↦ ‖v i‖⁻¹) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp [normalizedGram, normalizeVector, Matrix.gram,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Exact determinant normalization for a Gram correlation matrix. -/
theorem det_normalizedGram [Fintype ι] [DecidableEq ι] (v : ι → E) :
    (normalizedGram v).det =
      (Matrix.gram ℝ v).det / ∏ i, ‖v i‖ ^ 2 := by
  rw [normalizedGram_eq_diagonal_mul_gram_mul_diagonal,
    det_diagonal_two_sided_scale]
  have hscale : (∏ i, ‖v i‖⁻¹) ^ 2 = (∏ i, ‖v i‖ ^ 2)⁻¹ := by
    rw [Finset.prod_inv_distrib, inv_pow, ← Finset.prod_pow]
  rw [hscale, div_eq_mul_inv]
  ring

/-- The diagonal entries of the normalized Gram matrix are one whenever all
input vectors are nonzero. -/
theorem normalizedGram_apply_self (v : ι → E) (i : ι) (hi : v i ≠ 0) :
    normalizedGram v i i = 1 := by
  have hn : 0 < ‖v i‖ := norm_pos_iff.mpr hi
  simp [normalizedGram, normalizeVector, Matrix.gram, norm_smul,
    hn.ne']

end

end LogdetLean
