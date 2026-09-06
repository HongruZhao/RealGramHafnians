import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FixedHPreservedSScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralGaussianRealification
/-!
# Full rank for an arbitrary finite split-column index

The numeric full-rank theorem is stated for `Fin m ⊕ Fin m`.  This module
transports it through the canonical finite-type reindexing used by the
literal Gaussian realification.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Canonical simultaneous reindexing of a square matrix from `I ⊕ I` to
the split numeric model. -/
def reindexGenericSplitSquare (I : Type*) [Fintype I] :
    Matrix (I ⊕ I) (I ⊕ I) ℝ →
      Matrix (Fin (Fintype.card I) ⊕ Fin (Fintype.card I))
        (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) ℝ :=
  Matrix.reindex
    ((Fintype.equivFin I).sumCongr (Fintype.equivFin I))
    ((Fintype.equivFin I).sumCongr (Fintype.equivFin I))

@[simp] theorem sumColumnIndexToFinMeasurableEquiv_apply_generic
    (k : ℕ) (I : Type*) [Fintype I]
    (R : Matrix (Fin k) (I ⊕ I) ℝ) (a : Fin k)
    (j : Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) :
    sumColumnIndexToFinMeasurableEquiv k I R a j =
      R a (((Fintype.equivFin I).sumCongr
        (Fintype.equivFin I)).symm j) := by
  rfl

/-- Reindexing the columns of a rectangular matrix reindexes its Gram
matrix simultaneously in both square coordinates. -/
theorem realWishartGram_sumColumnIndexToFin
    (k : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
    (R : Matrix (Fin k) (I ⊕ I) ℝ) :
    realWishartGram (sumColumnIndexToFinMeasurableEquiv k I R) =
      reindexGenericSplitSquare I (realWishartGram R) := by
  ext i j
  simp [realWishartGram, Matrix.mul_apply,
    reindexGenericSplitSquare, Matrix.reindex_apply]

/-- Determinant is invariant under the canonical simultaneous reindexing. -/
theorem det_reindexGenericSplitSquare
    (I : Type*) [Fintype I] [DecidableEq I]
    (D : Matrix (I ⊕ I) (I ⊕ I) ℝ) :
    (reindexGenericSplitSquare I D).det = D.det := by
  exact Matrix.det_reindex_self
    ((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) D

/-- Invertibility of a Gram determinant is unchanged by the canonical
finite-type column reindexing. -/
theorem isUnit_det_realWishartGram_sumColumnIndexToFin_iff
    (k : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
    (R : Matrix (Fin k) (I ⊕ I) ℝ) :
    IsUnit
        (realWishartGram
          (sumColumnIndexToFinMeasurableEquiv k I R)).det ↔
      IsUnit (realWishartGram R).det := by
  rw [realWishartGram_sumColumnIndexToFin,
    det_reindexGenericSplitSquare]

/-- An iid split half-Gaussian matrix indexed by an arbitrary finite type
has full column rank almost surely whenever its real column count does not
exceed its row count. -/
theorem ae_isUnit_det_realWishartGram_halfGaussianMatrixSum_generic
    (k : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
    (h : Fintype.card (I ⊕ I) ≤ k) :
    ∀ᵐ R ∂halfGaussianMatrixSum k I,
      IsUnit (realWishartGram R).det := by
  have hnum :
      ∀ᵐ R ∂halfGaussianMatrixSum k (Fin (Fintype.card I)),
        IsUnit (realWishartGram R).det :=
    ae_isUnit_det_realWishartGram_halfGaussianMatrixSum
      k (Fintype.card I) (by
        simpa [Fintype.card_sum, two_mul] using h)
  have hpull :=
    (measurePreserving_sumColumnIndexToFin_halfGaussianMatrixSum k I).quasiMeasurePreserving.ae
      hnum
  filter_upwards [hpull] with R hR
  exact
    (isUnit_det_realWishartGram_sumColumnIndexToFin_iff k I R).mp hR

end Wishart

end

end LogdetLean.GramHafnian
