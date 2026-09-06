import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LineInvariantBoundedDerivativeSteinHaff
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.NumericPreservedSScoreBridge
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericSmoothTestReindex
/-!
# Internal smooth preserved-`S` score identity

This module composes the numeric, axiom-free Stein--Haff theorem with the
exact real/complex and finite-index reindexing bridges.  The result is the
smooth compact-support score identity needed by the existing
smooth-to-bounded-Borel measure extension, on an arbitrary finite complex
column index type.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/- Use the same concrete finite-product matrix topology as the numeric
preserved-`S` bridge.  This also keeps the dependent `fderiv` types
definitionally aligned across the numeric Stein--Haff theorem and the
split-column transport. -/
attribute [local instance]
  numericBridgeMatrixNormedAddCommGroup numericBridgeMatrixNormedSpace
  numericBridgeMatrixAddCommGroup numericBridgeMatrixModule
  numericBridgeMatrixPseudoMetricSpace numericBridgeMatrixUniformSpace
  numericBridgeMatrixTopologicalSpace

/-- Every smooth compactly supported test of the preserved complex
covariance coordinate satisfies the fixed-H score identity.  Both densities
are integrable.  The proof uses only scalar half-Gaussian integration by
parts and exact measure-preserving reindexing. -/
theorem internal_smooth_preservedS_score_pair_halfGaussianMatrixSum
    {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (psi : Matrix I I ℂ → ℝ)
    (hpsi : ContDiff ℝ 1 psi) (hpsiSupport : HasCompactSupport psi)
    {H : Matrix I I ℂ} (hH : H.IsHermitian)
    (hgap : Fintype.card (I ⊕ I) + 1 < k) :
    Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          preservedSWeight psi R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)))
        (halfGaussianMatrixSum k I) ∧
      Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          preservedSWeight psi R * Matrix.trace (scoreDeltaM H))
        (halfGaussianMatrixSum k I) ∧
      ((∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          preservedSWeight psi R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
          ∂halfGaussianMatrixSum k I) =
        ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          preservedSWeight psi R * Matrix.trace (scoreDeltaM H)
          ∂halfGaussianMatrixSum k I) := by
  let m := Fintype.card I
  let psiFin : Matrix (Fin m) (Fin m) ℂ → ℝ :=
    reindexGenericComplexTest I psi
  let HFin : Matrix (Fin m) (Fin m) ℂ :=
    reindexGenericComplexSquare I H
  have hpsiFin : ContDiff ℝ 1 psiFin := by
    exact contDiff_reindexGenericComplexTest I psi hpsi
  have hpsiFinSupport : HasCompactSupport psiFin := by
    exact hasCompactSupport_reindexGenericComplexTest I psi hpsiSupport
  have hHFin : HFin.IsHermitian := by
    exact reindexGenericComplexSquare_isHermitian I hH
  obtain ⟨C₀, C₁, hC₀, hC₁⟩ :=
    exists_bounds_numericPreservedSGramTest
      m psiFin hpsiFin hpsiFinSupport
  have hgapNum : 2 * m + 1 < k := by
    dsimp [m]
    simp only [Fintype.card_sum] at hgap
    omega
  let Dnum : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
    reindexSplitSquare m (scoreDeltaM HFin)
  have hDnum : Dnum.IsSymm := by
    exact (scoreDeltaM_isSymm hHFin).reindex (splitColumnEquiv m)
  have hsimple :=
    steinHaff_halfGaussianMatrix_of_bounded_fderiv_of_lineInvariant
    hgapNum (numericPreservedSGramTest m psiFin)
    (contDiff_numericPreservedSGramTest m psiFin hpsiFin)
    C₀ hC₀ C₁ hC₁ Dnum hDnum (by
      intro M t
      simpa [Dnum] using
        numericPreservedSGramTest_add_smul_scoreDelta
          m psiFin hHFin M t)
  have hzero : ∀ M,
      fderiv ℝ (numericPreservedSGramTest m psiFin) M Dnum = 0 := by
    intro M
    simpa [Dnum] using
      fderiv_numericPreservedSGramTest_scoreDelta
        m psiFin hpsiFin hHFin M
  have hright : Integrable
      (fun X : Matrix (Fin k) (Fin (2 * m)) ℝ ↦
        numericPreservedSGramTest m psiFin (realWishartGram X) *
            Matrix.trace Dnum -
          fderiv ℝ (numericPreservedSGramTest m psiFin)
            (realWishartGram X) Dnum)
      (halfGaussianMatrix k (2 * m)) := by
    exact hsimple.2.1.congr <| Filter.Eventually.of_forall fun X ↦ by
      change
        numericPreservedSGramTest m psiFin (realWishartGram X) *
            Matrix.trace Dnum =
          numericPreservedSGramTest m psiFin (realWishartGram X) *
              Matrix.trace Dnum -
            fderiv ℝ (numericPreservedSGramTest m psiFin)
              (realWishartGram X) Dnum
      rw [hzero (realWishartGram X), sub_zero]
  have heq :
      (∫ X : Matrix (Fin k) (Fin (2 * m)) ℝ,
        numericPreservedSGramTest m psiFin (realWishartGram X) *
          (inverseGramScoreCoefficient (Fin k) (Fin (2 * m)) *
            Matrix.trace ((realWishartGram X)⁻¹ * Dnum))
        ∂halfGaussianMatrix k (2 * m)) =
        ∫ X : Matrix (Fin k) (Fin (2 * m)) ℝ,
          numericPreservedSGramTest m psiFin (realWishartGram X) *
              Matrix.trace Dnum -
            fderiv ℝ (numericPreservedSGramTest m psiFin)
              (realWishartGram X) Dnum
          ∂halfGaussianMatrix k (2 * m) := by
    calc
      _ = ∫ X : Matrix (Fin k) (Fin (2 * m)) ℝ,
          numericPreservedSGramTest m psiFin (realWishartGram X) *
            Matrix.trace Dnum
          ∂halfGaussianMatrix k (2 * m) := hsimple.2.2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with X
        rw [hzero (realWishartGram X), sub_zero]
  have hnum := And.intro hsimple.1 (And.intro hright heq)
  have hfin := preservedS_score_pair_halfGaussianMatrixSum_of_numeric
    psiFin hpsiFin hHFin (by
      simpa [Dnum] using hnum)
  exact preservedS_score_pair_halfGaussianMatrixSum_of_indexToFin
    psi H (by
      simpa [m, psiFin, HFin] using hfin)

end Wishart

end

end LogdetLean.GramHafnian
