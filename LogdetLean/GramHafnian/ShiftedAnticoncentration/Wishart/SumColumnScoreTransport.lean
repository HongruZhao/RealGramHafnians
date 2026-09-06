import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralGaussianRealification
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedScore
import Mathlib.LinearAlgebra.Matrix.Reindex
/-!
# Transporting Wishart score algebra across split-column reindexing

The analytic Gaussian-IBP layer is phrased for numeric columns
`Fin (2*m)`, while the complex realification algebra naturally has split
columns `Fin m ⊕ Fin m`.  This file records the exact permutation
congruences needed to transport fixed-direction score identities between
the two presentations.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Canonical equivalence from real/imaginary split columns to numeric
columns.  This is the equivalence used by `sumColumnsToFinMeasurableEquiv`. -/
def splitColumnEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (Nat.two_mul m)).symm

/-- Reindex a rectangular split-column matrix by numeric columns. -/
def reindexSplitColumns (k m : ℕ) :
    Matrix (Fin k) (Fin m ⊕ Fin m) ℝ →
      Matrix (Fin k) (Fin (2 * m)) ℝ :=
  Matrix.reindex (Equiv.refl (Fin k)) (splitColumnEquiv m)

/-- Reindex a square split-column direction by numeric columns. -/
def reindexSplitSquare (m : ℕ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ →
      Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.reindex (splitColumnEquiv m) (splitColumnEquiv m)

@[simp] theorem reindexSplitColumns_apply
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ)
    (a : Fin k) (j : Fin (2 * m)) :
    reindexSplitColumns k m R a j =
      R a ((splitColumnEquiv m).symm j) := by
  rfl

@[simp] theorem reindexSplitSquare_apply
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (i j : Fin (2 * m)) :
    reindexSplitSquare m D i j =
      D ((splitColumnEquiv m).symm i)
        ((splitColumnEquiv m).symm j) := by
  rfl

theorem reindexSplitColumns_eq_sumColumnsToFin
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    reindexSplitColumns k m R =
      sumColumnsToFinMeasurableEquiv k m R := by
  rfl

/-- Column permutation carries the real Gram matrix by square congruence. -/
theorem realWishartGram_reindexSplitColumns
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    realWishartGram (reindexSplitColumns k m R) =
      reindexSplitSquare m (realWishartGram R) := by
  ext i j
  simp [realWishartGram, Matrix.mul_apply, reindexSplitColumns,
    reindexSplitSquare, Matrix.reindex_apply]

/-- Square reindexing commutes with the nonsingular inverse. -/
theorem inv_reindexSplitSquare
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    (reindexSplitSquare m D)⁻¹ = reindexSplitSquare m D⁻¹ := by
  exact Matrix.inv_reindex (splitColumnEquiv m) (splitColumnEquiv m) D

/-- Rectangular/square multiplication is equivariant under the same column
permutation. -/
theorem reindexSplitColumns_mul
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ)
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    reindexSplitColumns k m (R * D) =
      reindexSplitColumns k m R * reindexSplitSquare m D := by
  exact (Matrix.reindexLinearEquiv_mul
    (R := ℝ) (A := ℝ)
    (Equiv.refl (Fin k)) (splitColumnEquiv m) (splitColumnEquiv m)
    R D).symm

/-- Square multiplication is preserved by the column permutation. -/
theorem reindexSplitSquare_mul
    (D E : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    reindexSplitSquare m (D * E) =
      reindexSplitSquare m D * reindexSplitSquare m E := by
  exact Matrix.reindexAlgEquiv_mul (R := ℝ) (A := ℝ)
    (splitColumnEquiv m) D E

/-- Trace is invariant under simultaneous row/column reindexing. -/
theorem trace_reindexSplitSquare
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    Matrix.trace (reindexSplitSquare m D) = Matrix.trace D := by
  unfold Matrix.trace reindexSplitSquare
  exact (splitColumnEquiv m).symm.sum_comp (fun i ↦ D i i)

/-- Determinant is invariant under simultaneous row/column reindexing. -/
theorem det_reindexSplitSquare
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    (reindexSplitSquare m D).det = D.det := by
  exact Matrix.det_reindex_self (splitColumnEquiv m) D

/-- Invertibility of the real Gram matrix is unchanged by split-column
reindexing. -/
theorem isUnit_det_realWishartGram_reindexSplitColumns_iff
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    IsUnit (realWishartGram (reindexSplitColumns k m R)).det ↔
      IsUnit (realWishartGram R).det := by
  rw [realWishartGram_reindexSplitColumns,
    det_reindexSplitSquare]

/-- The inverse-Gram trace pairing is invariant under split-column
reindexing. -/
theorem trace_inverseGram_mul_reindexSplitSquare
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ)
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    Matrix.trace
        ((realWishartGram (reindexSplitColumns k m R))⁻¹ *
          reindexSplitSquare m D) =
      Matrix.trace ((realWishartGram R)⁻¹ * D) := by
  rw [realWishartGram_reindexSplitColumns, inv_reindexSplitSquare,
    ← reindexSplitSquare_mul, trace_reindexSplitSquare]

theorem trace_inverseGram_mul_sumColumnsToFin
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ)
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    Matrix.trace
        ((realWishartGram (sumColumnsToFinMeasurableEquiv k m R))⁻¹ *
          reindexSplitSquare m D) =
      Matrix.trace ((realWishartGram R)⁻¹ * D) := by
  simpa [reindexSplitColumns_eq_sumColumnsToFin] using
    trace_inverseGram_mul_reindexSplitSquare R D

/-- The dimension coefficient is independent of whether the `2*m` columns
are presented numerically or as two split blocks. -/
theorem inverseGramScoreCoefficient_fin_twoMul_eq_sum (k m : ℕ) :
    inverseGramScoreCoefficient (Fin k) (Fin (2 * m)) =
      inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) := by
  simp only [inverseGramScoreCoefficient, Fintype.card_fin,
    Fintype.card_sum]
  push_cast
  ring

/-- Transport a fixed-direction inverse-Gram score identity from numeric
columns back to the split-column Gaussian law.  All analytic content stays
in `hscore`; this theorem is exact measure and matrix reindexing. -/
theorem integral_inverseGram_score_halfGaussianMatrixSum_of_fin
    (k m : ℕ)
    (g : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ)
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (a : ℝ)
    (hscore :
      (∫ X, g ((sumColumnsToFinMeasurableEquiv k m).symm X) *
          (a * Matrix.trace
            ((realWishartGram X)⁻¹ * reindexSplitSquare m D))
          ∂halfGaussianMatrix k (2 * m)) =
        ∫ X, g ((sumColumnsToFinMeasurableEquiv k m).symm X) *
          Matrix.trace (reindexSplitSquare m D)
          ∂halfGaussianMatrix k (2 * m)) :
    (∫ R, g R *
        (a * Matrix.trace ((realWishartGram R)⁻¹ * D))
        ∂halfGaussianMatrixSum k (Fin m)) =
      ∫ R, g R * Matrix.trace D
        ∂halfGaussianMatrixSum k (Fin m) := by
  let e := sumColumnsToFinMeasurableEquiv k m
  let f : Matrix (Fin k) (Fin (2 * m)) ℝ → ℝ := fun X ↦
    g (e.symm X) *
      (a * Matrix.trace
        ((realWishartGram X)⁻¹ * reindexSplitSquare m D))
  let h : Matrix (Fin k) (Fin (2 * m)) ℝ → ℝ := fun X ↦
    g (e.symm X) * Matrix.trace (reindexSplitSquare m D)
  have hmap := measurePreserving_sumColumnsToFin_halfGaussianMatrixSum k m
  calc
    (∫ R, g R *
        (a * Matrix.trace ((realWishartGram R)⁻¹ * D))
        ∂halfGaussianMatrixSum k (Fin m)) =
        ∫ R, f (e R) ∂halfGaussianMatrixSum k (Fin m) := by
      apply integral_congr_ae
      filter_upwards [] with R
      dsimp [f, e]
      rw [MeasurableEquiv.symm_apply_apply,
        trace_inverseGram_mul_sumColumnsToFin]
    _ = ∫ X, f X ∂halfGaussianMatrix k (2 * m) :=
      hmap.integral_comp' f
    _ = ∫ X, h X ∂halfGaussianMatrix k (2 * m) := by
      exact hscore
    _ = ∫ R, h (e R) ∂halfGaussianMatrixSum k (Fin m) :=
      (hmap.integral_comp' h).symm
    _ = ∫ R, g R * Matrix.trace D
        ∂halfGaussianMatrixSum k (Fin m) := by
      apply integral_congr_ae
      filter_upwards [] with R
      dsimp [h, e]
      rw [MeasurableEquiv.symm_apply_apply,
        trace_reindexSplitSquare]

/-- The lifted Stein vector field is equivariant under split-column
reindexing. -/
theorem steinVectorFieldValue_reindexSplitColumns
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ)
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    steinVectorFieldValue (reindexSplitColumns k m R)
        (reindexSplitSquare m D) =
      reindexSplitColumns k m (steinVectorFieldValue R D) := by
  unfold steinVectorFieldValue
  rw [realWishartGram_reindexSplitColumns, inv_reindexSplitSquare]
  ext a j
  simp only [Matrix.smul_apply]
  rw [show reindexSplitColumns k m R * reindexSplitSquare m (realWishartGram R)⁻¹ =
      reindexSplitColumns k m (R * (realWishartGram R)⁻¹) by
        exact (reindexSplitColumns_mul R (realWishartGram R)⁻¹).symm]
  rw [show reindexSplitColumns k m (R * (realWishartGram R)⁻¹) *
        reindexSplitSquare m D =
      reindexSplitColumns k m (R * (realWishartGram R)⁻¹ * D) by
        exact (reindexSplitColumns_mul (R * (realWishartGram R)⁻¹) D).symm]
  rfl

end Wishart

end

end LogdetLean.GramHafnian
