import LogdetLean.GaussianColumnProduct
import Mathlib.Tactic
/-!
# A prescribed orthogonal column rotation for Gaussian data

This module packages the finite-dimensional orthogonal-invariance step used
to compare a Wishart log determinant with one prescribed linear combination
of its columns.  An orthonormal basis `b` rotates each standard Gaussian row
to its `b`-coordinates.  The row-product law and the scatter determinant are
unchanged, while rotated coordinate `i` is the inner product with `b i`.

The construction is elementary finite-dimensional Hilbert-space algebra.
The Gaussian invariance input is Mathlib's `stdGaussian_map` theorem.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace

/-- Coordinates of an observation in a prescribed orthonormal basis. -/
def rotateObservationByBasis {p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p)) :
    CorrelationMatrix.Observation p ≃ₗᵢ[ℝ]
      CorrelationMatrix.Observation p :=
  b.repr

/-- Apply a prescribed orthonormal coordinate rotation to every data row. -/
def rotateRowsByBasis {m p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p)) :
    GaussianData m p → GaussianData m p :=
  fun z k ↦ rotateObservationByBasis b (z k)

theorem measurable_rotateRowsByBasis {m p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p)) :
    Measurable (rotateRowsByBasis (m := m) b) := by
  unfold rotateRowsByBasis
  fun_prop

/-- Standard Gaussian row data are invariant under the prescribed rotation. -/
theorem map_rotateRowsByBasis_standardGaussianDataMeasure {m p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p)) :
    Measure.map (rotateRowsByBasis (m := m) b)
        (standardGaussianDataMeasure m p) =
      standardGaussianDataMeasure m p := by
  let _ (k : Fin m) : IsProbabilityMeasure
      ((stdGaussian (CorrelationMatrix.Observation p)).map
        (rotateObservationByBasis b)) :=
    Measure.isProbabilityMeasure_map
      (rotateObservationByBasis b).continuous.measurable.aemeasurable
  unfold standardGaussianDataMeasure rotateRowsByBasis
  rw [Measure.pi_map_pi (fun _ ↦
    (rotateObservationByBasis b).continuous.measurable.aemeasurable)]
  congr 1
  funext k
  exact stdGaussian_map (rotateObservationByBasis b)

/-- The orthogonal matrix whose columns are the prescribed basis vectors. -/
def basisColumnUnitary {p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p)) :
    Matrix.unitaryGroup (Fin p) ℝ :=
  ⟨(EuclideanSpace.basisFun (Fin p) ℝ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin p) ℝ).toMatrix_orthonormalBasis_mem_unitary b⟩

@[simp]
theorem basisColumnUnitary_apply {p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p))
    (i j : Fin p) :
    (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ) i j = b j i :=
  rfl

/-- Rotating rows is right multiplication by the basis-column unitary. -/
theorem dataMatrix_rotateRowsByBasis {m p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p))
    (z : GaussianData m p) :
    dataMatrix (rotateRowsByBasis b z) =
      dataMatrix z * (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ) := by
  ext k i
  simp only [dataMatrix_apply, rotateRowsByBasis,
    rotateObservationByBasis, Matrix.mul_apply]
  rw [OrthonormalBasis.repr_apply_apply]
  simp [PiLp.inner_apply, RCLike.inner_apply, basisColumnUnitary_apply]

/-- The scatter matrix is conjugated by the basis-column unitary. -/
theorem scatterMatrix_rotateRowsByBasis {m p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p))
    (z : GaussianData m p) :
    scatterMatrix (rotateRowsByBasis b z) =
      star (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ) *
        scatterMatrix z *
          (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ) := by
  rw [scatterMatrix, dataMatrix_rotateRowsByBasis,
    Matrix.conjTranspose_mul, scatterMatrix]
  rw [← Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- A prescribed orthonormal row rotation preserves the scatter determinant. -/
theorem det_scatterMatrix_rotateRowsByBasis {m p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p))
    (z : GaussianData m p) :
    (scatterMatrix (rotateRowsByBasis b z)).det =
      (scatterMatrix z).det := by
  rw [scatterMatrix_rotateRowsByBasis, Matrix.det_mul, Matrix.det_mul]
  have hdet :
      (star (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ)).det *
        (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ).det = 1 := by
    rw [← Matrix.det_mul, Unitary.coe_star_mul_self, Matrix.det_one]
  calc
    (star (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ)).det *
          (scatterMatrix z).det *
        (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ).det =
      ((star (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ)).det *
        (basisColumnUnitary b : Matrix (Fin p) (Fin p) ℝ).det) *
          (scatterMatrix z).det := by ring
    _ = (scatterMatrix z).det := by rw [hdet, one_mul]

/-- Rotated column `i` is the vector of rowwise inner products with `b i`. -/
theorem dataColumn_rotateRowsByBasis {m p : ℕ}
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p))
    (z : GaussianData m p) (i : Fin p) :
    dataColumn (rotateRowsByBasis b z) i =
      WithLp.toLp 2 (fun k : Fin m ↦ inner ℝ (b i) (z k)) := by
  ext k
  simp only [dataColumn_apply, rotateRowsByBasis, rotateObservationByBasis]
  rw [OrthonormalBasis.repr_apply_apply]

end

end LogdetLean
