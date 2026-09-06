import LogdetLean.GaussianScatter
import LogdetLean.SequentialBeta
/-!
# Sample correlation matrices in the general covariance model

This file connects the row-based Gaussian scatter model to the normalized-Gram
definition used throughout the null-case development.  The `j`th variable is
viewed as a vector in `EuclideanSpace ℝ (Fin m)`; normalizing those vectors and
taking their Gram matrix is exactly the ordinary sample correlation matrix.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace

/-- The `j`th variable column of a row-indexed data set. -/
def dataColumn {m p : ℕ} (x : GaussianData m p) (j : Fin p) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun k ↦ x k j)

@[simp]
theorem dataColumn_apply {m p : ℕ} (x : GaussianData m p)
    (j : Fin p) (k : Fin m) : dataColumn x j k = x k j := rfl

/-- Package all variable columns as one finite family. -/
def dataColumns {m p : ℕ} (x : GaussianData m p) :
    Fin p → EuclideanSpace ℝ (Fin m) :=
  fun j ↦ dataColumn x j

theorem measurable_dataColumns {m p : ℕ} :
    Measurable (dataColumns : GaussianData m p →
      Fin p → EuclideanSpace ℝ (Fin m)) := by
  unfold dataColumns dataColumn
  fun_prop

/-- The scatter matrix is the Gram matrix of the variable columns. -/
theorem scatterMatrix_eq_gram_dataColumns {m p : ℕ} (x : GaussianData m p) :
    scatterMatrix x = Matrix.gram ℝ (dataColumns x) := by
  ext i j
  simp [scatterMatrix_apply, dataColumns, dataColumn, PiLp.inner_apply,
    RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The sample correlation matrix obtained by normalizing every variable
column. -/
def sampleCorrelationMatrix {m p : ℕ} (x : GaussianData m p) :
    Matrix (Fin p) (Fin p) ℝ :=
  normalizedGram (dataColumns x)

/-- Entrywise formula for the sample correlation matrix, with Mathlib's
totalized inverse convention at a zero column. -/
@[simp]
theorem sampleCorrelationMatrix_apply {m p : ℕ} (x : GaussianData m p)
    (i j : Fin p) :
    sampleCorrelationMatrix x i j =
      ‖dataColumn x i‖⁻¹ * ‖dataColumn x j‖⁻¹ * scatterMatrix x i j := by
  have hinner : ⟪dataColumn x i, dataColumn x j⟫ = scatterMatrix x i j := by
    change (Matrix.gram ℝ (dataColumns x)) i j = scatterMatrix x i j
    rw [← scatterMatrix_eq_gram_dataColumns]
  simp only [sampleCorrelationMatrix, normalizedGram, Matrix.gram_apply,
    normalizeVector, real_inner_smul_left, real_inner_smul_right,
    dataColumns, hinner]
  ring

/-- If a variable column is nonzero, the corresponding sample-correlation
diagonal entry is one. -/
theorem sampleCorrelationMatrix_apply_self {m p : ℕ} (x : GaussianData m p)
    (i : Fin p) (hi : dataColumn x i ≠ 0) :
    sampleCorrelationMatrix x i i = 1 := by
  exact normalizedGram_apply_self (dataColumns x) i hi

/-- Exact determinant normalization in terms of the scatter determinant and
column sums of squares. -/
theorem det_sampleCorrelationMatrix {m p : ℕ} (x : GaussianData m p) :
    (sampleCorrelationMatrix x).det =
      (scatterMatrix x).det / ∏ i, ‖dataColumn x i‖ ^ 2 := by
  rw [sampleCorrelationMatrix, det_normalizedGram,
    scatterMatrix_eq_gram_dataColumns]
  rfl

/-- The determinant of the general-covariance sample correlation matrix is
measurable. -/
theorem measurable_det_sampleCorrelationMatrix {m p : ℕ} :
    Measurable (fun x : GaussianData m p ↦ (sampleCorrelationMatrix x).det) := by
  exact (measurable_det_normalizedGram (E := EuclideanSpace ℝ (Fin m)) p).comp
    measurable_dataColumns

/-- The general-covariance sample-correlation determinant law. -/
def gaussianSampleCorrelationDetLaw {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : Measure ℝ :=
  Measure.map (fun x : GaussianData m p ↦ (sampleCorrelationMatrix x).det)
    (correlatedGaussianDataMeasure m R)

instance gaussianSampleCorrelationDetLaw_isProbabilityMeasure {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) :
    IsProbabilityMeasure (gaussianSampleCorrelationDetLaw m R) := by
  unfold gaussianSampleCorrelationDetLaw
  exact Measure.isProbabilityMeasure_map
    measurable_det_sampleCorrelationMatrix.aemeasurable

/-- Canonical exact-law statement for the general-covariance sample-
correlation determinant. -/
theorem hasLaw_sampleCorrelationDet {m p : ℕ} (R : CorrelationMatrix p) :
    HasLaw (fun x : GaussianData m p ↦ (sampleCorrelationMatrix x).det)
      (gaussianSampleCorrelationDetLaw m R)
      (correlatedGaussianDataMeasure m R) where
  aemeasurable := measurable_det_sampleCorrelationMatrix.aemeasurable
  map_eq := rfl

end

end LogdetLean
