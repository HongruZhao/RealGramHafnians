import LogdetLean.GaussianColumnProduct
import LogdetLean.CorrelationEigenvalues
import LogdetLean.GeneralRDecomposition
import Mathlib.Tactic
/-!
# Spectral rotation of a standard Gaussian scatter matrix

This file diagonalizes the deterministic correlation matrix while preserving
the law of the standard Gaussian data.  It is the finite-dimensional
orthogonal-invariance step in Zhao (2026), Lemma 5.4 and equation (5.20).
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace

namespace CorrelationMatrix

variable {m p : ℕ} (R : CorrelationMatrix p)

/-- Coordinates of an observation in an orthonormal eigenbasis of `R-I`. -/
def spectralRotateObservation : Observation p ≃ₗᵢ[ℝ] Observation p :=
  R.deviation_isHermitian.eigenvectorBasis.repr

/-- Rotate every row into the eigenbasis of `R-I`. -/
def spectralRotateRows : GaussianData m p → GaussianData m p :=
  fun z k ↦ R.spectralRotateObservation (z k)

theorem measurable_spectralRotateRows :
    Measurable (R.spectralRotateRows (m := m)) := by
  unfold spectralRotateRows
  fun_prop

/-- Orthogonal invariance of the standard Gaussian row-product law. -/
theorem map_spectralRotateRows_standardGaussianDataMeasure :
    Measure.map (R.spectralRotateRows (m := m))
        (standardGaussianDataMeasure m p) =
      standardGaussianDataMeasure m p := by
  let _ (k : Fin m) : IsProbabilityMeasure
      ((stdGaussian (Observation p)).map R.spectralRotateObservation) :=
    Measure.isProbabilityMeasure_map
      R.spectralRotateObservation.continuous.measurable.aemeasurable
  unfold standardGaussianDataMeasure spectralRotateRows
  rw [Measure.pi_map_pi (fun _ ↦
    R.spectralRotateObservation.continuous.measurable.aemeasurable)]
  congr 1
  funext k
  exact stdGaussian_map R.spectralRotateObservation

/-- Rotating rows is right multiplication of the data matrix by the unitary
eigenvector matrix. -/
theorem dataMatrix_spectralRotateRows (z : GaussianData m p) :
    dataMatrix (R.spectralRotateRows z) =
      dataMatrix z *
        (R.deviation_isHermitian.eigenvectorUnitary :
          Matrix (Fin p) (Fin p) ℝ) := by
  ext k i
  simp only [dataMatrix_apply, spectralRotateRows,
    spectralRotateObservation, Matrix.mul_apply]
  rw [OrthonormalBasis.repr_apply_apply]
  simp [PiLp.inner_apply, RCLike.inner_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]

/-- The rotated scatter is unitary conjugation of the original scatter. -/
theorem scatterMatrix_spectralRotateRows (z : GaussianData m p) :
    scatterMatrix (R.spectralRotateRows z) =
      star (R.deviation_isHermitian.eigenvectorUnitary :
        Matrix (Fin p) (Fin p) ℝ) * scatterMatrix z *
          (R.deviation_isHermitian.eigenvectorUnitary :
            Matrix (Fin p) (Fin p) ℝ) := by
  rw [scatterMatrix, dataMatrix_spectralRotateRows,
    Matrix.conjTranspose_mul, scatterMatrix]
  rw [← Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- An orthogonal spectral rotation preserves the Gram determinant. -/
theorem det_scatterMatrix_spectralRotateRows (z : GaussianData m p) :
    (scatterMatrix (R.spectralRotateRows z)).det =
      (scatterMatrix z).det := by
  rw [scatterMatrix_spectralRotateRows, Matrix.det_mul, Matrix.det_mul]
  have hdet :
      (star (R.deviation_isHermitian.eigenvectorUnitary :
          Matrix (Fin p) (Fin p) ℝ)).det *
        (R.deviation_isHermitian.eigenvectorUnitary :
          Matrix (Fin p) (Fin p) ℝ).det = 1 := by
    rw [← Matrix.det_mul, Unitary.coe_star_mul_self, Matrix.det_one]
  calc
    (star (R.deviation_isHermitian.eigenvectorUnitary :
          Matrix (Fin p) (Fin p) ℝ)).det *
          (scatterMatrix z).det *
        (R.deviation_isHermitian.eigenvectorUnitary :
          Matrix (Fin p) (Fin p) ℝ).det =
      ((star (R.deviation_isHermitian.eigenvectorUnitary :
          Matrix (Fin p) (Fin p) ℝ)).det *
        (R.deviation_isHermitian.eigenvectorUnitary :
          Matrix (Fin p) (Fin p) ℝ).det) *
          (scatterMatrix z).det := by ring
    _ = (scatterMatrix z).det := by rw [hdet, one_mul]

/-- Spectral theorem for the correlation matrix itself, with eigenvalues
`1 + lambda_i(R-I)`. -/
theorem val_eq_eigenvectorUnitary_mul_diagonal :
    R.val =
      (R.deviation_isHermitian.eigenvectorUnitary :
          Matrix (Fin p) (Fin p) ℝ) *
        Matrix.diagonal (fun i ↦ 1 + R.deviationEigenvalues i) *
          star (R.deviation_isHermitian.eigenvectorUnitary :
            Matrix (Fin p) (Fin p) ℝ) := by
  let U : Matrix (Fin p) (Fin p) ℝ :=
    R.deviation_isHermitian.eigenvectorUnitary
  let D : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.diagonal R.deviationEigenvalues
  have hA : R.deviation = U * D * star U := by
    simpa [U, D, CorrelationMatrix.deviationEigenvalues,
      Unitary.conjStarAlgAut_apply] using
        R.deviation_isHermitian.spectral_theorem
  have hU : U * star U = 1 := by
    dsimp [U]
    rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hI : (1 : Matrix (Fin p) (Fin p) ℝ) = U * 1 * star U := by
    rw [mul_one, hU]
  have hdiag :
      Matrix.diagonal (fun i ↦ 1 + R.deviationEigenvalues i) = 1 + D := by
    ext i j
    by_cases h : i = j <;> simp [D, h]
  calc
    R.val = 1 + R.deviation := R.one_add_deviation.symm
    _ = 1 + U * D * star U := by rw [hA]
    _ = U * 1 * star U + U * D * star U := by rw [← hI]
    _ = U * (1 + D) * star U := by
      rw [Matrix.mul_add, Matrix.add_mul]
    _ = U * Matrix.diagonal
        (fun i ↦ 1 + R.deviationEigenvalues i) * star U := by rw [hdiag]

/-- The trace tilt is a weighted sum of squared norms of the independent
rotated columns. -/
theorem trace_val_mul_scatterMatrix_eq_sum_rotatedColumnNormSq
    (z : GaussianData m p) :
    Matrix.trace (R.val * scatterMatrix z) =
      ∑ i : Fin p, (1 + R.deviationEigenvalues i) *
        ‖dataColumn (R.spectralRotateRows z) i‖ ^ 2 := by
  let U : Matrix (Fin p) (Fin p) ℝ :=
    R.deviation_isHermitian.eigenvectorUnitary
  let D : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.diagonal (fun i ↦ 1 + R.deviationEigenvalues i)
  have hR : R.val = U * D * star U := by
    simpa [U, D] using R.val_eq_eigenvectorUnitary_mul_diagonal
  have hS : scatterMatrix (R.spectralRotateRows z) =
      star U * scatterMatrix z * U := by
    simpa [U] using R.scatterMatrix_spectralRotateRows z
  rw [hR]
  calc
    Matrix.trace ((U * D * star U) * scatterMatrix z) =
        Matrix.trace (D * (star U * scatterMatrix z * U)) := by
      rw [show (U * D * star U) * scatterMatrix z =
          U * (D * (star U * scatterMatrix z)) by
        simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (D * scatterMatrix (R.spectralRotateRows z)) := by
      rw [hS]
    _ = ∑ i : Fin p, (1 + R.deviationEigenvalues i) *
        ‖dataColumn (R.spectralRotateRows z) i‖ ^ 2 := by
      simp only [Matrix.trace, Matrix.diag_apply, D, Matrix.mul_apply,
        Matrix.diagonal_apply, scatterMatrix_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [pow_two]

/-! The two preceding identities are pointwise; combining them with
`map_spectralRotateRows_standardGaussianDataMeasure` gives the exact law
reduction from the paper's row-based Wishart statistic to independent
Gaussian columns. -/

end CorrelationMatrix

open GeneralRDecomposition

/-- The diagonal spectral version of the paper's leading random variable.
Its input is a family of mutually independent standard Gaussian columns. -/
def wishartDiagonalLeadingStatistic {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p)
    (v : Fin p → EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.log (Matrix.gram ℝ v).det - W0LogDetMean m p -
    ((∑ i : Fin p,
        (1 + R.deviationEigenvalues i) * ‖v i‖ ^ 2) -
      (m : ℝ) * (p : ℝ)) / (m : ℝ)

theorem measurable_wishartDiagonalLeadingStatistic {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) :
    Measurable (wishartDiagonalLeadingStatistic m R) := by
  have hdet : Measurable (fun v :
      Fin p → EuclideanSpace ℝ (Fin m) ↦ (Matrix.gram ℝ v).det) := by
    simp_rw [Matrix.det_apply', Matrix.gram_apply]
    fun_prop
  have hsum : Measurable (fun v :
      Fin p → EuclideanSpace ℝ (Fin m) ↦
        ∑ i : Fin p, (1 + R.deviationEigenvalues i) * ‖v i‖ ^ 2) :=
    Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).norm.pow_const 2).const_mul
        (1 + R.deviationEigenvalues i)
  unfold wishartDiagonalLeadingStatistic
  exact (hdet.log.sub measurable_const).sub
    ((hsum.sub_const _).div_const _)

/-- Pointwise diagonalization of `M_R`. -/
theorem M_R_eq_wishartDiagonalLeadingStatistic_spectralRotate
    {m p : ℕ} (R : CorrelationMatrix p) (z : GaussianData m p) :
    M_R m R z =
      wishartDiagonalLeadingStatistic m R
        (dataColumns (R.spectralRotateRows z)) := by
  rw [M_R_eq_trace_formula]
  unfold wishartDiagonalLeadingStatistic W0
  rw [← scatterMatrix_eq_gram_dataColumns]
  rw [R.det_scatterMatrix_spectralRotateRows]
  rw [R.trace_val_mul_scatterMatrix_eq_sum_rotatedColumnNormSq]
  rfl

/-- Exact law reduction for the actual row-based `M_R`: it is the diagonal
statistic of independent standard Gaussian columns. -/
theorem map_M_R_eq_map_wishartDiagonalLeadingStatistic
    {m p : ℕ} (R : CorrelationMatrix p) :
    Measure.map (M_R m R) (standardGaussianDataMeasure m p) =
      Measure.map (wishartDiagonalLeadingStatistic m R)
        (Measure.pi fun _ : Fin p ↦
          stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  let rot := R.spectralRotateRows (m := m)
  let diag := wishartDiagonalLeadingStatistic m R
  have hrot : Measure.map rot (standardGaussianDataMeasure m p) =
      standardGaussianDataMeasure m p := by
    exact R.map_spectralRotateRows_standardGaussianDataMeasure
  have hcols : Measure.map dataColumns
      (standardGaussianDataMeasure m p) =
      Measure.pi fun _ : Fin p ↦
        stdGaussian (EuclideanSpace ℝ (Fin m)) :=
    map_dataColumns_standardGaussianDataMeasure m p
  calc
    Measure.map (M_R m R) (standardGaussianDataMeasure m p) =
      Measure.map ((diag ∘ dataColumns) ∘ rot)
        (standardGaussianDataMeasure m p) := by
      congr 1
      funext z
      exact M_R_eq_wishartDiagonalLeadingStatistic_spectralRotate R z
    _ = Measure.map (diag ∘ dataColumns)
        (Measure.map rot (standardGaussianDataMeasure m p)) := by
      rw [Measure.map_map]
      · exact (measurable_wishartDiagonalLeadingStatistic m R).comp
          measurable_dataColumns
      · exact R.measurable_spectralRotateRows
    _ = Measure.map (diag ∘ dataColumns)
        (standardGaussianDataMeasure m p) := by rw [hrot]
    _ = Measure.map diag
        (Measure.map dataColumns (standardGaussianDataMeasure m p)) := by
      rw [Measure.map_map]
      · exact measurable_wishartDiagonalLeadingStatistic m R
      · exact measurable_dataColumns
    _ = Measure.map diag
        (Measure.pi fun _ : Fin p ↦
          stdGaussian (EuclideanSpace ℝ (Fin m))) := by rw [hcols]

/-- Right-nested-column form of the exact law reduction.  This is the exact
interface consumed by the sequential Bartlett Beta--Gamma theorem in
`WishartBetaGammaFactors`. -/
theorem map_M_R_eq_map_nestedWishartDiagonalLeadingStatistic
    {m p : ℕ} (R : CorrelationMatrix p) :
    Measure.map (M_R m R) (standardGaussianDataMeasure m p) =
      Measure.map
        (wishartDiagonalLeadingStatistic m R ∘
          nestedTupleToFin (n := p))
        (nestedProductMeasure
          (stdGaussian (EuclideanSpace ℝ (Fin m))) p) := by
  rw [map_M_R_eq_map_wishartDiagonalLeadingStatistic]
  rw [← map_nestedTupleToFin_nestedProductMeasure
    (stdGaussian (EuclideanSpace ℝ (Fin m))) p]
  rw [Measure.map_map]
  · exact measurable_wishartDiagonalLeadingStatistic m R
  · exact measurable_nestedTupleToFin p

end

end LogdetLean
