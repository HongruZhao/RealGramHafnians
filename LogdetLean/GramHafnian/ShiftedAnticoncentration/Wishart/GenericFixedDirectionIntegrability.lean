import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericPreservedSReindex
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FixedHScoreIntegrability
/-!
# Fixed-direction score integrability for arbitrary finite split indices

The sharp first inverse-Wishart moment was proved for canonical numeric
columns.  This file transports that conclusion through the exact
measure-preserving finite-type reindexing.  It supplies the unweighted
integrability input used by the smooth-to-Borel preserved-`S` extension,
without invoking any Stein--Haff identity.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Under the split half-Gaussian law, the fixed inverse-Gram score and its
constant companion are integrable for every finite complex-column index.
This is purely an integrability statement; no integration-by-parts identity
is used. -/
theorem integrable_fixedDirection_score_pair_halfGaussianMatrixSum_internal
    {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (hgap : Fintype.card (I ⊕ I) + 1 < k) :
    Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
            Matrix.trace ((realWishartGram R)⁻¹ * D))
        (halfGaussianMatrixSum k I) ∧
      Integrable
        (fun _R : Matrix (Fin k) (I ⊕ I) ℝ ↦ Matrix.trace D)
        (halfGaussianMatrixSum k I) := by
  let m := Fintype.card I
  let e := sumColumnIndexToFinMeasurableEquiv k I
  let μ := halfGaussianMatrixSum k I
  let ν := halfGaussianMatrixSum k (Fin m)
  let Dfin : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
    reindexGenericSplitSquare I D
  let ffin : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ := fun R ↦
    inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
      Matrix.trace ((realWishartGram R)⁻¹ * Dfin)
  let f : Matrix (Fin k) (I ⊕ I) ℝ → ℝ := fun R ↦
    inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
      Matrix.trace ((realWishartGram R)⁻¹ * D)
  let hfin : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ := fun _ ↦
    Matrix.trace Dfin
  let h : Matrix (Fin k) (I ⊕ I) ℝ → ℝ := fun _ ↦ Matrix.trace D
  have hgapfin : 2 * m + 1 < k := by
    dsimp [m]
    simp only [Fintype.card_sum] at hgap
    omega
  have hffin : Integrable ffin ν := by
    have htrace :=
      integrable_trace_nonsingInv_realWishartGram_mul_const_halfGaussianMatrixSum
        hgapfin Dfin
    exact htrace.const_mul
      (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m))
  have hhfin : Integrable hfin ν := integrable_const _
  have hmp := measurePreserving_sumColumnIndexToFin_halfGaussianMatrixSum k I
  have hfPoint : ∀ R, ffin (e R) = f R := by
    intro R
    dsimp [ffin, f, e, Dfin]
    rw [trace_inverseGram_mul_sumColumnIndexToFin,
      inverseGramScoreCoefficient_generic_sum_eq_fin]
  have hhPoint : ∀ R, hfin (e R) = h R := by
    intro R
    dsimp [hfin, h, e, Dfin]
    exact trace_reindexGenericSplitSquare I D
  constructor
  · have hcomp := hmp.integrable_comp_of_integrable hffin
    exact hcomp.congr (Filter.Eventually.of_forall fun R ↦ by
      simpa [Function.comp_def] using hfPoint R)
  · have hcomp := hmp.integrable_comp_of_integrable hhfin
    exact hcomp.congr (Filter.Eventually.of_forall fun R ↦ by
      simpa [Function.comp_def] using hhPoint R)

end Wishart

end

end LogdetLean.GramHafnian
