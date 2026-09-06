import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.CofactorPreservedCoordinate
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RealMatrixSplit
/-!
# Realification of the literal past-column model

The real Wishart score is stated for a matrix whose columns are the real and
imaginary parts of the literal complex Gaussian columns.  This file records
that identification entry by entry and shows that its preserved `S`
coordinate is exactly the transpose Gram from which the hafnian cofactors are
formed.
-/

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*} [Fintype k] [Fintype m]
  [DecidableEq k] [DecidableEq m]

@[simp] theorem realGramBlock11_realWishartGram
    (R : Matrix k (m ⊕ m) ℝ) :
    realGramBlock11 (realWishartGram R) =
      (realMatrixLeft R).transpose * realMatrixLeft R := by
  ext i j
  simp [realGramBlock11, realWishartGram, realMatrixLeft,
    Matrix.mul_apply]

@[simp] theorem realGramBlock12_realWishartGram
    (R : Matrix k (m ⊕ m) ℝ) :
    realGramBlock12 (realWishartGram R) =
      (realMatrixLeft R).transpose * realMatrixRight R := by
  ext i j
  simp [realGramBlock12, realWishartGram, realMatrixLeft,
    realMatrixRight, Matrix.mul_apply]

@[simp] theorem realGramBlock22_realWishartGram
    (R : Matrix k (m ⊕ m) ℝ) :
    realGramBlock22 (realWishartGram R) =
      (realMatrixRight R).transpose * realMatrixRight R := by
  ext i j
  simp [realGramBlock22, realWishartGram, realMatrixRight,
    Matrix.mul_apply]

/-- The preserved complex-symmetric coordinate extracted from the real Gram
is the literal transpose Gram of the associated complex matrix. -/
theorem sCoordinateOfRealGram_realWishartGram
    (R : Matrix k (m ⊕ m) ℝ) :
    sCoordinateOfRealGram (realWishartGram R) =
      transposeGramMatrix (complexOfRealMatrix R) := by
  rw [complexOfRealMatrix,
    transposeGramMatrix_complexOfRealPair]
  simp [sCoordinateOfRealGram]

/-- Concatenate the real and imaginary parts of the literal past columns. -/
def pastRealifiedMatrix {r n : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin n → ℂ)) :
    Matrix (Fin n)
      (OddCofactorIndex r hr ⊕ OddCofactorIndex r hr) ℝ :=
  fun a ↦ Sum.elim (fun j ↦ (A j a).re) (fun j ↦ (A j a).im)

@[simp] theorem realMatrixLeft_pastRealifiedMatrix
    {r n : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin n → ℂ)) :
    realMatrixLeft (pastRealifiedMatrix hr A) =
      fun a j ↦ (A j a).re := by
  rfl

@[simp] theorem realMatrixRight_pastRealifiedMatrix
    {r n : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin n → ℂ)) :
    realMatrixRight (pastRealifiedMatrix hr A) =
      fun a j ↦ (A j a).im := by
  rfl

/-- Complexifying the realified literal matrix recovers the original column
matrix exactly. -/
@[simp] theorem complexOfRealMatrix_pastRealifiedMatrix
    {r n : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin n → ℂ)) :
    complexOfRealMatrix (pastRealifiedMatrix hr A) =
      pastComplexColumnMatrix hr A := by
  ext a j
  apply Complex.ext <;>
    simp [complexOfRealMatrix, complexOfRealPair,
      pastComplexColumnMatrix]

/-- On literal columns, the preserved score coordinate is exactly the
transpose Gram used to define every hafnian cofactor. -/
theorem sCoordinateOfRealGram_pastRealifiedMatrix
    {r n : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin n → ℂ)) :
    sCoordinateOfRealGram
        (realWishartGram (pastRealifiedMatrix hr A)) =
      transposeGramMatrix (pastComplexColumnMatrix hr A) := by
  rw [sCoordinateOfRealGram_realWishartGram,
    complexOfRealMatrix_pastRealifiedMatrix]

/-- The literal cofactor vector is a function of the preserved coordinate of
the realified Wishart matrix. -/
theorem pastHafnianCofactorVector_eq_preservedRealGram
    {r n : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin n → ℂ)) :
    pastHafnianCofactorVector hr A =
      transposeGramCofactorVector
        (sCoordinateOfRealGram
          (realWishartGram (pastRealifiedMatrix hr A))) := by
  rw [pastHafnianCofactorVector_eq_transposeGramCofactorVector,
    sCoordinateOfRealGram_pastRealifiedMatrix]

/-- The literal cofactor energy is likewise a function of the preserved
coordinate of the realified Wishart matrix. -/
theorem pastCofactorW_eq_preservedRealGram
    {r n : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin n → ℂ)) :
    pastCofactorW hr A =
      transposeGramCofactorW
        (sCoordinateOfRealGram
          (realWishartGram (pastRealifiedMatrix hr A))) := by
  rw [pastCofactorW_eq_transposeGramCofactorW,
    sCoordinateOfRealGram_pastRealifiedMatrix]

end Wishart

end

end LogdetLean.GramHafnian
