import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericHalfGaussianFullRank
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SumColumnScoreTransport
/-!
# Reindexing preserved-`S` score data over an arbitrary finite type

The analytic Gaussian integration-by-parts theorem is proved with numeric
column indices.  This file contains only deterministic and
measure-preserving transport from an arbitrary finite complex-column type
`I` to its canonical `Fin (card I)` model.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Canonical simultaneous reindexing of a complex square matrix from an
arbitrary finite type to its numeric model. -/
def reindexGenericComplexSquare (I : Type*) [Fintype I] :
    Matrix I I ℂ →
      Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ :=
  Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I)

/-- The inverse canonical reindexing of a numeric complex square matrix. -/
def unreindexGenericComplexSquare (I : Type*) [Fintype I] :
    Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ →
      Matrix I I ℂ :=
  Matrix.reindex (Fintype.equivFin I).symm (Fintype.equivFin I).symm

@[simp] theorem unreindexGenericComplexSquare_reindex
    (I : Type*) [Fintype I] (H : Matrix I I ℂ) :
    unreindexGenericComplexSquare I (reindexGenericComplexSquare I H) = H := by
  ext i j
  simp [unreindexGenericComplexSquare, reindexGenericComplexSquare,
    Matrix.reindex_apply]

@[simp] theorem reindexGenericComplexSquare_unreindex
    (I : Type*) [Fintype I]
    (H : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ) :
    reindexGenericComplexSquare I (unreindexGenericComplexSquare I H) = H := by
  ext i j
  simp [unreindexGenericComplexSquare, reindexGenericComplexSquare,
    Matrix.reindex_apply]

/-- Hermitianity is invariant under canonical finite-type reindexing. -/
theorem reindexGenericComplexSquare_isHermitian
    (I : Type*) [Fintype I]
    {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    (reindexGenericComplexSquare I H).IsHermitian := by
  exact hH.reindex (Fintype.equivFin I)

/-- The real score direction commutes with simultaneous reindexing of its
complex column type. -/
theorem scoreDeltaM_reindexGenericComplexSquare
    (I : Type*) [Fintype I]
    (H : Matrix I I ℂ) :
    scoreDeltaM (reindexGenericComplexSquare I H) =
      reindexGenericSplitSquare I (scoreDeltaM H) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scoreDeltaM, realBlockMatrix, scoreDeltaU, scoreDeltaC,
      scoreDeltaV, recoverU, recoverC, recoverV,
      reindexGenericComplexSquare, reindexGenericSplitSquare,
      Matrix.reindex_apply]

/-- The preserved complex coordinate commutes with simultaneous reindexing
of the two real column blocks. -/
theorem sCoordinateOfRealGram_reindexGenericSplitSquare
    (I : Type*) [Fintype I]
    (M : Matrix (I ⊕ I) (I ⊕ I) ℝ) :
    sCoordinateOfRealGram (reindexGenericSplitSquare I M) =
      reindexGenericComplexSquare I (sCoordinateOfRealGram M) := by
  ext i j
  simp [sCoordinateOfRealGram, sOfRealBlocks, realGramBlock11,
    realGramBlock12, realGramBlock22, reindexGenericSplitSquare,
    reindexGenericComplexSquare, Matrix.reindex_apply]

/-- Reindexing the rectangular matrix reindexes its preserved `S`
coordinate by the corresponding complex square equivalence. -/
theorem preservedSCoordinate_sumColumnIndexToFin
    (k : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
    (R : Matrix (Fin k) (I ⊕ I) ℝ) :
    preservedSCoordinate (sumColumnIndexToFinMeasurableEquiv k I R) =
      reindexGenericComplexSquare I (preservedSCoordinate R) := by
  rw [preservedSCoordinate, preservedSCoordinate,
    realWishartGram_sumColumnIndexToFin,
    sCoordinateOfRealGram_reindexGenericSplitSquare]

/-- The inverse of a simultaneously reindexed real square matrix is the
reindexing of its inverse. -/
theorem inv_reindexGenericSplitSquare
    (I : Type*) [Fintype I] [DecidableEq I]
    (M : Matrix (I ⊕ I) (I ⊕ I) ℝ) :
    (reindexGenericSplitSquare I M)⁻¹ =
      reindexGenericSplitSquare I M⁻¹ := by
  exact Matrix.inv_reindex
    ((Fintype.equivFin I).sumCongr (Fintype.equivFin I))
    ((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) M

/-- Simultaneous generic reindexing preserves square multiplication. -/
theorem reindexGenericSplitSquare_mul
    (I : Type*) [Fintype I] [DecidableEq I]
    (M N : Matrix (I ⊕ I) (I ⊕ I) ℝ) :
    reindexGenericSplitSquare I (M * N) =
      reindexGenericSplitSquare I M * reindexGenericSplitSquare I N := by
  exact Matrix.reindexAlgEquiv_mul (R := ℝ) (A := ℝ)
    ((Fintype.equivFin I).sumCongr (Fintype.equivFin I)) M N

/-- Trace is invariant under canonical simultaneous reindexing. -/
theorem trace_reindexGenericSplitSquare
    (I : Type*) [Fintype I]
    (M : Matrix (I ⊕ I) (I ⊕ I) ℝ) :
    Matrix.trace (reindexGenericSplitSquare I M) = Matrix.trace M := by
  unfold Matrix.trace reindexGenericSplitSquare
  exact (((Fintype.equivFin I).sumCongr
    (Fintype.equivFin I)).symm.sum_comp (fun i ↦ M i i))

/-- The inverse-Gram trace pairing is unchanged by canonical finite-type
column reindexing. -/
theorem trace_inverseGram_mul_sumColumnIndexToFin
    (k : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
    (R : Matrix (Fin k) (I ⊕ I) ℝ)
    (D : Matrix (I ⊕ I) (I ⊕ I) ℝ) :
    Matrix.trace
        ((realWishartGram
          (sumColumnIndexToFinMeasurableEquiv k I R))⁻¹ *
            reindexGenericSplitSquare I D) =
      Matrix.trace ((realWishartGram R)⁻¹ * D) := by
  rw [realWishartGram_sumColumnIndexToFin,
    inv_reindexGenericSplitSquare,
    ← reindexGenericSplitSquare_mul,
    trace_reindexGenericSplitSquare]

/-- The Wishart score dimension coefficient is invariant under the generic
finite-type reindexing. -/
theorem inverseGramScoreCoefficient_generic_sum_eq_fin
    (k : ℕ) (I : Type*) [Fintype I] :
    inverseGramScoreCoefficient (Fin k)
        (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) =
      inverseGramScoreCoefficient (Fin k) (I ⊕ I) := by
  simp [inverseGramScoreCoefficient]

/-- A test function transported to the numeric complex-column model. -/
def reindexGenericComplexTest
    (I : Type*) [Fintype I]
    (psi : Matrix I I ℂ → ℝ) :
    Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ → ℝ :=
  fun S ↦ psi (unreindexGenericComplexSquare I S)

/-- The transported preserved-`S` weight agrees pointwise after rectangular
column reindexing. -/
theorem preservedSWeight_reindexGeneric
    (k : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
    (psi : Matrix I I ℂ → ℝ)
    (R : Matrix (Fin k) (I ⊕ I) ℝ) :
    preservedSWeight (reindexGenericComplexTest I psi)
        (sumColumnIndexToFinMeasurableEquiv k I R) =
      preservedSWeight psi R := by
  simp [preservedSWeight, reindexGenericComplexTest,
    preservedSCoordinate_sumColumnIndexToFin]

/-- The complete fixed-direction preserved-`S` score conclusion transports
from the canonical numeric complex-column type back to an arbitrary finite
type.  This theorem contains no analytic input: `hfin` supplies the numeric
result, and the proof uses only the exact measure-preserving reindexing. -/
theorem preservedS_score_pair_halfGaussianMatrixSum_of_indexToFin
    {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (psi : Matrix I I ℂ → ℝ)
    (H : Matrix I I ℂ)
    (hfin :
      Integrable
          (fun R : Matrix (Fin k)
              (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) ℝ ↦
            preservedSWeight (reindexGenericComplexTest I psi) R *
              (inverseGramScoreCoefficient (Fin k)
                  (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) *
                Matrix.trace
                  ((realWishartGram R)⁻¹ *
                    scoreDeltaM (reindexGenericComplexSquare I H))))
          (halfGaussianMatrixSum k (Fin (Fintype.card I))) ∧
        Integrable
          (fun R : Matrix (Fin k)
              (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) ℝ ↦
            preservedSWeight (reindexGenericComplexTest I psi) R *
              Matrix.trace
                (scoreDeltaM (reindexGenericComplexSquare I H)))
          (halfGaussianMatrixSum k (Fin (Fintype.card I))) ∧
        ((∫ R : Matrix (Fin k)
              (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) ℝ,
            preservedSWeight (reindexGenericComplexTest I psi) R *
              (inverseGramScoreCoefficient (Fin k)
                  (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) *
                Matrix.trace
                  ((realWishartGram R)⁻¹ *
                    scoreDeltaM (reindexGenericComplexSquare I H)))
            ∂halfGaussianMatrixSum k (Fin (Fintype.card I))) =
          ∫ R : Matrix (Fin k)
              (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) ℝ,
            preservedSWeight (reindexGenericComplexTest I psi) R *
              Matrix.trace
                (scoreDeltaM (reindexGenericComplexSquare I H))
            ∂halfGaussianMatrixSum k (Fin (Fintype.card I)))) :
    Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          preservedSWeight psi R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace
                ((realWishartGram R)⁻¹ * scoreDeltaM H)))
        (halfGaussianMatrixSum k I) ∧
      Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          preservedSWeight psi R * Matrix.trace (scoreDeltaM H))
        (halfGaussianMatrixSum k I) ∧
      ((∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          preservedSWeight psi R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace
                ((realWishartGram R)⁻¹ * scoreDeltaM H))
          ∂halfGaussianMatrixSum k I) =
        ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          preservedSWeight psi R * Matrix.trace (scoreDeltaM H)
          ∂halfGaussianMatrixSum k I) := by
  let e := sumColumnIndexToFinMeasurableEquiv k I
  let μ := halfGaussianMatrixSum k I
  let ν := halfGaussianMatrixSum k (Fin (Fintype.card I))
  let fFin : Matrix (Fin k)
      (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) ℝ → ℝ := fun R ↦
    preservedSWeight (reindexGenericComplexTest I psi) R *
      (inverseGramScoreCoefficient (Fin k)
          (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) *
        Matrix.trace
          ((realWishartGram R)⁻¹ *
            scoreDeltaM (reindexGenericComplexSquare I H)))
  let hFin : Matrix (Fin k)
      (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) ℝ → ℝ := fun R ↦
    preservedSWeight (reindexGenericComplexTest I psi) R *
      Matrix.trace (scoreDeltaM (reindexGenericComplexSquare I H))
  let f : Matrix (Fin k) (I ⊕ I) ℝ → ℝ := fun R ↦
    preservedSWeight psi R *
      (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
        Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
  let h : Matrix (Fin k) (I ⊕ I) ℝ → ℝ := fun R ↦
    preservedSWeight psi R * Matrix.trace (scoreDeltaM H)
  have hmp := measurePreserving_sumColumnIndexToFin_halfGaussianMatrixSum k I
  have hfPoint : ∀ R, fFin (e R) = f R := by
    intro R
    dsimp [fFin, f, e]
    rw [preservedSWeight_reindexGeneric,
      scoreDeltaM_reindexGenericComplexSquare,
      trace_inverseGram_mul_sumColumnIndexToFin,
      inverseGramScoreCoefficient_generic_sum_eq_fin]
  have hhPoint : ∀ R, hFin (e R) = h R := by
    intro R
    dsimp [hFin, h, e]
    rw [preservedSWeight_reindexGeneric,
      scoreDeltaM_reindexGenericComplexSquare,
      trace_reindexGenericSplitSquare]
  have hf : Integrable f μ := by
    have hcomp := hmp.integrable_comp_of_integrable hfin.1
    exact hcomp.congr (Filter.Eventually.of_forall fun R ↦ by
      simpa [Function.comp_def] using hfPoint R)
  have hh : Integrable h μ := by
    have hcomp := hmp.integrable_comp_of_integrable hfin.2.1
    exact hcomp.congr (Filter.Eventually.of_forall fun R ↦ by
      simpa [Function.comp_def] using hhPoint R)
  have heq : (∫ R, f R ∂μ) = ∫ R, h R ∂μ := by
    calc
      (∫ R, f R ∂μ) = ∫ R, fFin (e R) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with R
        exact (hfPoint R).symm
      _ = ∫ R, fFin R ∂ν := hmp.integral_comp' fFin
      _ = ∫ R, hFin R ∂ν := hfin.2.2
      _ = ∫ R, hFin (e R) ∂μ := (hmp.integral_comp' hFin).symm
      _ = ∫ R, h R ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with R
        exact hhPoint R
  simpa [f, h, μ] using And.intro hf (And.intro hh heq)

/-- Degenerate empty-column case of the complete preserved-`S` score
conclusion.  It is recorded separately because flattened coordinates are
naturally indexed by `Fin (k*p)`, while there is no predecessor dimension
when `p = 0`. -/
theorem preservedS_score_pair_halfGaussianMatrixSum_of_card_eq_zero
    {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (hcard : Fintype.card I = 0)
    (psi : Matrix I I ℂ → ℝ)
    (H : Matrix I I ℂ) :
    Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          preservedSWeight psi R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace
                ((realWishartGram R)⁻¹ * scoreDeltaM H)))
        (halfGaussianMatrixSum k I) ∧
      Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          preservedSWeight psi R * Matrix.trace (scoreDeltaM H))
        (halfGaussianMatrixSum k I) ∧
      ((∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          preservedSWeight psi R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace
                ((realWishartGram R)⁻¹ * scoreDeltaM H))
          ∂halfGaussianMatrixSum k I) =
        ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          preservedSWeight psi R * Matrix.trace (scoreDeltaM H)
          ∂halfGaussianMatrixSum k I) := by
  letI : IsEmpty I := Fintype.card_eq_zero_iff.mp hcard
  have hleft : Integrable
      (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        preservedSWeight psi R *
          (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
            Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)))
      (halfGaussianMatrixSum k I) := by
    simpa [Matrix.trace] using
      (integrable_zero : Integrable
        (fun _R : Matrix (Fin k) (I ⊕ I) ℝ ↦ (0 : ℝ))
        (halfGaussianMatrixSum k I))
  have hright : Integrable
      (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        preservedSWeight psi R * Matrix.trace (scoreDeltaM H))
      (halfGaussianMatrixSum k I) := by
    simpa [Matrix.trace] using
      (integrable_zero : Integrable
        (fun _R : Matrix (Fin k) (I ⊕ I) ℝ ↦ (0 : ℝ))
        (halfGaussianMatrixSum k I))
  refine ⟨hleft, hright, ?_⟩
  simp [Matrix.trace]

end Wishart

end

end LogdetLean.GramHafnian
