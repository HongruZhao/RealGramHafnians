import LogdetLean.GaussianSampleCorrelation
import Mathlib.Tactic
/-!
# Cancellation of a common positive scale in correlation matrices

Pearson normalization removes a common positive scalar exactly.  This
deterministic fact is the final algebraic step in the matrix-spherical
extension: after polar decomposition, the centered spherical data equal the
centered Gaussian data multiplied by one common positive random radius.

All identities below are pointwise.  No distributional input is used.
-/

namespace LogdetLean

noncomputable section

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalizing a vector removes a positive real scalar exactly. -/
theorem normalizeVector_smul_of_pos (c : ℝ) (hc : 0 < c) (x : E) :
    normalizeVector (c • x) = normalizeVector x := by
  unfold normalizeVector
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  congr 1
  have hc0 : c ≠ 0 := hc.ne'
  calc
    (c * ‖x‖)⁻¹ * c = (‖x‖⁻¹ * c⁻¹) * c := by rw [mul_inv_rev]
    _ = ‖x‖⁻¹ * (c⁻¹ * c) := by ring
    _ = ‖x‖⁻¹ := by rw [inv_mul_cancel₀ hc0, mul_one]

/-- A normalized Gram matrix is invariant under a common positive scalar. -/
theorem normalizedGram_smul_of_pos [Fintype ι]
    (c : ℝ) (hc : 0 < c) (v : ι → E) :
    normalizedGram (fun i ↦ c • v i) = normalizedGram v := by
  unfold normalizedGram
  congr 1
  funext i
  exact normalizeVector_smul_of_pos c hc (v i)

/-- Determinant form of common-positive-scale cancellation. -/
theorem det_normalizedGram_smul_of_pos [Fintype ι] [DecidableEq ι]
    (c : ℝ) (hc : 0 < c) (v : ι → E) :
    (normalizedGram (fun i ↦ c • v i)).det = (normalizedGram v).det := by
  rw [normalizedGram_smul_of_pos c hc v]

/-- Multiply every observation vector in a row-indexed data set by the same
real scalar. -/
def scaleGaussianData {m p : ℕ} (c : ℝ) (x : GaussianData m p) :
    GaussianData m p := fun k ↦ c • x k

@[simp]
theorem scaleGaussianData_apply {m p : ℕ} (c : ℝ)
    (x : GaussianData m p) (k : Fin m) (i : Fin p) :
    scaleGaussianData c x k i = c * x k i := rfl

/-- Scaling all observations scales every variable column by the same
scalar. -/
theorem dataColumn_scaleGaussianData {m p : ℕ} (c : ℝ)
    (x : GaussianData m p) (j : Fin p) :
    dataColumn (scaleGaussianData c x) j = c • dataColumn x j := by
  ext k
  rfl

/-- The actual sample-correlation matrix is invariant under a common
positive scale of all observations. -/
theorem sampleCorrelationMatrix_scaleGaussianData_of_pos
    {m p : ℕ} (c : ℝ) (hc : 0 < c) (x : GaussianData m p) :
    sampleCorrelationMatrix (scaleGaussianData c x) =
      sampleCorrelationMatrix x := by
  unfold sampleCorrelationMatrix dataColumns
  rw [show (fun j ↦ dataColumn (scaleGaussianData c x) j) =
      (fun j ↦ c • dataColumn x j) by
    funext j
    exact dataColumn_scaleGaussianData c x j]
  exact normalizedGram_smul_of_pos c hc (fun j ↦ dataColumn x j)

/-- Determinant form of sample-correlation scale cancellation. -/
theorem det_sampleCorrelationMatrix_scaleGaussianData_of_pos
    {m p : ℕ} (c : ℝ) (hc : 0 < c) (x : GaussianData m p) :
    (sampleCorrelationMatrix (scaleGaussianData c x)).det =
      (sampleCorrelationMatrix x).det := by
  rw [sampleCorrelationMatrix_scaleGaussianData_of_pos c hc x]

end

end LogdetLean

