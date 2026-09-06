import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseLiteral
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.PastCofactorBridge
/-!
# Hafnian cofactors as functions of the preserved transpose Gram

The conditional-Wishart score changes the Hermitian Gram while fixing the
transpose Gram.  This file records that the literal past cofactor vector and
its squared norm factor exactly through that preserved coordinate.
-/

open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Hafnian cofactor vector formed directly from a symmetric matrix.  The
definition makes sense for an arbitrary square matrix; symmetry is only a
property of the transpose-Gram inputs used below. -/
def transposeGramCofactorVector
    {m : Type*} [Fintype m] [LinearOrder m]
    (S : Matrix m m ℂ) (j : m) : ℂ :=
  typeHafnian (fun i l : {i : m // i ≠ j} ↦ S i.1 l.1)

/-- The usual finite Gram cofactor is the preceding function evaluated at
the column transpose Gram. -/
theorem finiteGramCofactorVector_eq_transposeGramCofactorVector
    {m : Type*} [Fintype m] [LinearOrder m] {k : ℕ}
    (A : m → (Fin k → ℂ)) (j : m) :
    finiteGramCofactorVector A j =
      transposeGramCofactorVector (columnTransposeGram A) j := by
  rfl

/-- The matrix transpose Gram of the literal column matrix is exactly the
column-family transpose Gram. -/
theorem transposeGramMatrix_pastComplexColumnMatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    transposeGramMatrix (pastComplexColumnMatrix hr A) =
      columnTransposeGram A := by
  ext i j
  simp [transposeGramMatrix, pastComplexColumnMatrix,
    columnTransposeGram, Matrix.mul_apply]

/-- The literal past hafnian-cofactor vector depends only on the preserved
transpose-Gram coordinate. -/
theorem pastHafnianCofactorVector_eq_transposeGramCofactorVector
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    pastHafnianCofactorVector hr A =
      transposeGramCofactorVector
        (transposeGramMatrix (pastComplexColumnMatrix hr A)) := by
  funext j
  rw [show pastHafnianCofactorVector hr A j =
      oddHafnianCofactorVector hr (pastCofactorMatrix hr A) j by rfl,
    oddHafnianCofactorVector_pastCofactorMatrix,
    finiteGramCofactorVector_eq_transposeGramCofactorVector,
    transposeGramMatrix_pastComplexColumnMatrix]

/-- Squared cofactor norm formed directly from a transpose Gram matrix. -/
def transposeGramCofactorW
    {m : Type*} [Fintype m] [LinearOrder m]
    (S : Matrix m m ℂ) : ℝ :=
  ∑ j, Complex.normSq (transposeGramCofactorVector S j)

/-- The literal `W_r` also factors exactly through the preserved coordinate. -/
theorem pastCofactorW_eq_transposeGramCofactorW
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    pastCofactorW hr A =
      transposeGramCofactorW
        (transposeGramMatrix (pastComplexColumnMatrix hr A)) := by
  rw [pastCofactorW_eq_sum_normSq]
  unfold transposeGramCofactorW
  congr 1
  funext j
  rw [pastHafnianCofactorVector_eq_transposeGramCofactorVector]

theorem transposeGramCofactorW_nonneg
    {m : Type*} [Fintype m] [LinearOrder m]
    (S : Matrix m m ℂ) :
    0 ≤ transposeGramCofactorW S := by
  unfold transposeGramCofactorW
  exact Finset.sum_nonneg fun j _ ↦ Complex.normSq_nonneg _

end Wishart

end

end LogdetLean.GramHafnian
