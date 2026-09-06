import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericPreservedSReindex
import Mathlib.Analysis.Calculus.FDeriv.Const
/-!
# Numeric-to-split bridge for preserved-`S` Stein--Haff scores

The analytic integration-by-parts layer works on numeric matrices with
columns `Fin (2*m)`.  The conditional hafnian algebra uses split columns
`Fin m ⊕ Fin m`.  This file constructs the numeric Gram test, proves its
uniform derivative bound from compact support, proves that its derivative
vanishes in the score direction, and transports the complete score
conclusion to the split law.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/- Keep every Frechet derivative in this file on the same finite matrix
topology. -/
local instance numericBridgeMatrixNormedAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : NormedAddCommGroup (Matrix a b 𝕜) :=
  Matrix.normedAddCommGroup

local instance numericBridgeMatrixNormedSpace
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    NormedSpace 𝔽 (Matrix a b 𝕜) :=
  Matrix.normedSpace

local instance numericBridgeMatrixAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : AddCommGroup (Matrix a b 𝕜) :=
  numericBridgeMatrixNormedAddCommGroup.toAddCommGroup

local instance numericBridgeMatrixModule
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    Module 𝔽 (Matrix a b 𝕜) :=
  numericBridgeMatrixNormedSpace.toModule

local instance numericBridgeMatrixPseudoMetricSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : PseudoMetricSpace (Matrix a b 𝕜) :=
  numericBridgeMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance numericBridgeMatrixUniformSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : UniformSpace (Matrix a b 𝕜) :=
  numericBridgeMatrixPseudoMetricSpace.toUniformSpace

local instance numericBridgeMatrixTopologicalSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : TopologicalSpace (Matrix a b 𝕜) :=
  numericBridgeMatrixUniformSpace.toTopologicalSpace

/-- Inverse square-column reindexing as a real linear map. -/
def unreindexSplitSquareLinearMap (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ →ₗ[ℝ]
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  (Matrix.reindexLinearEquiv ℝ ℝ
    (splitColumnEquiv m) (splitColumnEquiv m)).symm.toLinearMap

/-- Continuous version of inverse square-column reindexing. -/
def unreindexSplitSquareCLM (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ →L[ℝ]
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  (unreindexSplitSquareLinearMap m).toContinuousLinearMap

@[simp] theorem unreindexSplitSquareCLM_reindexSplitSquare
    (m : ℕ) (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    unreindexSplitSquareCLM m (reindexSplitSquare m M) = M := by
  ext i j
  simp [unreindexSplitSquareCLM, unreindexSplitSquareLinearMap,
    reindexSplitSquare, Matrix.reindex_apply]

/-- Numeric linear extraction of the preserved complex `S` coordinate. -/
def numericPreservedSGramCLM (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ →L[ℝ]
      Matrix (Fin m) (Fin m) ℂ :=
  sCoordinateOfRealGramCLM.comp (unreindexSplitSquareCLM m)

@[simp] theorem numericPreservedSGramCLM_apply
    (m : ℕ) (M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
    numericPreservedSGramCLM m M =
      sCoordinateOfRealGram (unreindexSplitSquareCLM m M) := by
  rfl

/-- A split-complex preserved-`S` test viewed on numeric real Gram
matrices. -/
def numericPreservedSGramTest (m : ℕ)
    (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  psi (numericPreservedSGramCLM m M)

theorem contDiff_numericPreservedSGramTest
    (m : ℕ) (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (hpsi : ContDiff ℝ 1 psi) :
    ContDiff ℝ 1 (numericPreservedSGramTest m psi) := by
  exact hpsi.comp (numericPreservedSGramCLM m).contDiff

/-- Exact Frechet derivative of the numeric preserved-`S` Gram test. -/
theorem fderiv_numericPreservedSGramTest
    (m : ℕ) (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (hpsi : ContDiff ℝ 1 psi)
    (M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
    fderiv ℝ (numericPreservedSGramTest m psi) M =
      (fderiv ℝ psi (numericPreservedSGramCLM m M)).comp
        (numericPreservedSGramCLM m) := by
  have hdiff : Differentiable ℝ psi := hpsi.differentiable (by simp)
  have hcomp := hdiff.differentiableAt.hasFDerivAt.comp M
    (numericPreservedSGramCLM m).hasFDerivAt
  exact hcomp.fderiv

/-- Compact support of `psi` supplies global bounds for the numeric Gram
test and for its full Frechet derivative. -/
theorem exists_bounds_numericPreservedSGramTest
    (m : ℕ) (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (hpsi : ContDiff ℝ 1 psi) (hsupp : HasCompactSupport psi) :
    ∃ C₀ C₁ : ℝ,
      (∀ M, |numericPreservedSGramTest m psi M| ≤ C₀) ∧
      (∀ M, ‖fderiv ℝ (numericPreservedSGramTest m psi) M‖ ≤ C₁) := by
  obtain ⟨C₀, hC₀⟩ :=
    hpsi.continuous.bounded_above_of_compact_support hsupp
  obtain ⟨Cpsi, hCpsi⟩ :=
    (hpsi.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (hsupp.fderiv (𝕜 := ℝ))
  refine ⟨C₀, Cpsi * ‖numericPreservedSGramCLM m‖, ?_, ?_⟩
  · intro M
    simpa [numericPreservedSGramTest, Real.norm_eq_abs] using
      hC₀ (numericPreservedSGramCLM m M)
  · intro M
    rw [fderiv_numericPreservedSGramTest m psi hpsi M]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (hCpsi (numericPreservedSGramCLM m M)) (norm_nonneg _))

/-- The numeric test agrees with the literal preserved-`S` weight after
split-column reindexing. -/
theorem numericPreservedSGramTest_realWishartGram_sumColumnsToFin
    (k m : ℕ) (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    numericPreservedSGramTest m psi
        (realWishartGram (sumColumnsToFinMeasurableEquiv k m R)) =
      preservedSWeight psi R := by
  change numericPreservedSGramTest m psi
      (realWishartGram (reindexSplitColumns k m R)) =
    preservedSWeight psi R
  rw [realWishartGram_reindexSplitColumns]
  simp [numericPreservedSGramTest, preservedSWeight, preservedSCoordinate]

/-- The Frechet derivative of the numeric Gram test vanishes in the
reindexed conditional-Wishart score direction. -/
theorem fderiv_numericPreservedSGramTest_scoreDelta
    (m : ℕ) (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (hpsi : ContDiff ℝ 1 psi)
    {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :
    fderiv ℝ (numericPreservedSGramTest m psi) M
        (reindexSplitSquare m (scoreDeltaM H)) = 0 := by
  rw [fderiv_numericPreservedSGramTest m psi hpsi M]
  change fderiv ℝ psi (numericPreservedSGramCLM m M)
    (numericPreservedSGramCLM m
      (reindexSplitSquare m (scoreDeltaM H))) = 0
  have hS : sCoordinateOfRealGram (scoreDeltaM H) = 0 := by
    simpa [scoreDeltaM] using sOf_scoreDelta hH
  have hL : numericPreservedSGramCLM m
      (reindexSplitSquare m (scoreDeltaM H)) = 0 := by
    change sCoordinateOfRealGram
      (unreindexSplitSquareCLM m
        (reindexSplitSquare m (scoreDeltaM H))) = 0
    rw [unreindexSplitSquareCLM_reindexSplitSquare, hS]
  rw [hL, map_zero]

/-- The transported preserved-`S` Gram test is literally constant on every
line in a transported Hermitian score direction.  This algebraic form has no
`fderiv` in its statement, so it can be passed across modules with different
but equivalent finite-matrix topology instances. -/
theorem numericPreservedSGramTest_add_smul_scoreDelta
    (m : ℕ) (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (t : ℝ) :
    numericPreservedSGramTest m psi
        (M + t • reindexSplitSquare m (scoreDeltaM H)) =
      numericPreservedSGramTest m psi M := by
  have hS : sCoordinateOfRealGram (scoreDeltaM H) = 0 := by
    simpa [scoreDeltaM] using sOf_scoreDelta hH
  have hL : numericPreservedSGramCLM m
      (reindexSplitSquare m (scoreDeltaM H)) = 0 := by
    change sCoordinateOfRealGram
      (unreindexSplitSquareCLM m
        (reindexSplitSquare m (scoreDeltaM H))) = 0
    rw [unreindexSplitSquareCLM_reindexSplitSquare, hS]
  change psi (numericPreservedSGramCLM m
      (M + t • reindexSplitSquare m (scoreDeltaM H))) =
    psi (numericPreservedSGramCLM m M)
  rw [map_add, map_smul, hL, smul_zero, add_zero]

/-- A complete numeric Stein--Haff conclusion for the transported test and
direction yields the complete split-column preserved-`S` score conclusion.
All singular analysis remains isolated in `hnum`. -/
theorem preservedS_score_pair_halfGaussianMatrixSum_of_numeric
    {k m : ℕ}
    (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (hpsi : ContDiff ℝ 1 psi)
    {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (hnum :
      Integrable
          (fun X : Matrix (Fin k) (Fin (2 * m)) ℝ ↦
            numericPreservedSGramTest m psi (realWishartGram X) *
              (inverseGramScoreCoefficient (Fin k) (Fin (2 * m)) *
                Matrix.trace ((realWishartGram X)⁻¹ *
                  reindexSplitSquare m (scoreDeltaM H))))
          (halfGaussianMatrix k (2 * m)) ∧
        Integrable
          (fun X : Matrix (Fin k) (Fin (2 * m)) ℝ ↦
            numericPreservedSGramTest m psi (realWishartGram X) *
                Matrix.trace (reindexSplitSquare m (scoreDeltaM H)) -
              fderiv ℝ (numericPreservedSGramTest m psi)
                (realWishartGram X)
                (reindexSplitSquare m (scoreDeltaM H)))
          (halfGaussianMatrix k (2 * m)) ∧
        ((∫ X : Matrix (Fin k) (Fin (2 * m)) ℝ,
            numericPreservedSGramTest m psi (realWishartGram X) *
              (inverseGramScoreCoefficient (Fin k) (Fin (2 * m)) *
                Matrix.trace ((realWishartGram X)⁻¹ *
                  reindexSplitSquare m (scoreDeltaM H)))
            ∂halfGaussianMatrix k (2 * m)) =
          ∫ X : Matrix (Fin k) (Fin (2 * m)) ℝ,
            numericPreservedSGramTest m psi (realWishartGram X) *
                Matrix.trace (reindexSplitSquare m (scoreDeltaM H)) -
              fderiv ℝ (numericPreservedSGramTest m psi)
                (realWishartGram X)
                (reindexSplitSquare m (scoreDeltaM H))
            ∂halfGaussianMatrix k (2 * m))) :
    Integrable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          preservedSWeight psi R *
            (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)))
        (halfGaussianMatrixSum k (Fin m)) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          preservedSWeight psi R * Matrix.trace (scoreDeltaM H))
        (halfGaussianMatrixSum k (Fin m)) ∧
      ((∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
          preservedSWeight psi R *
            (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
          ∂halfGaussianMatrixSum k (Fin m)) =
        ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
          preservedSWeight psi R * Matrix.trace (scoreDeltaM H)
          ∂halfGaussianMatrixSum k (Fin m)) := by
  let e := sumColumnsToFinMeasurableEquiv k m
  let μ := halfGaussianMatrixSum k (Fin m)
  let ν := halfGaussianMatrix k (2 * m)
  let fNum : Matrix (Fin k) (Fin (2 * m)) ℝ → ℝ := fun X ↦
    numericPreservedSGramTest m psi (realWishartGram X) *
      (inverseGramScoreCoefficient (Fin k) (Fin (2 * m)) *
        Matrix.trace ((realWishartGram X)⁻¹ *
          reindexSplitSquare m (scoreDeltaM H)))
  let hNum : Matrix (Fin k) (Fin (2 * m)) ℝ → ℝ := fun X ↦
    numericPreservedSGramTest m psi (realWishartGram X) *
        Matrix.trace (reindexSplitSquare m (scoreDeltaM H)) -
      fderiv ℝ (numericPreservedSGramTest m psi) (realWishartGram X)
        (reindexSplitSquare m (scoreDeltaM H))
  let f : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ := fun R ↦
    preservedSWeight psi R *
      (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
        Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
  let h : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ := fun R ↦
    preservedSWeight psi R * Matrix.trace (scoreDeltaM H)
  have hmp := measurePreserving_sumColumnsToFin_halfGaussianMatrixSum k m
  have hfPoint : ∀ R, fNum (e R) = f R := by
    intro R
    dsimp [fNum, f, e]
    rw [numericPreservedSGramTest_realWishartGram_sumColumnsToFin,
      trace_inverseGram_mul_sumColumnsToFin,
      inverseGramScoreCoefficient_fin_twoMul_eq_sum]
  have hhPoint : ∀ R, hNum (e R) = h R := by
    intro R
    dsimp [hNum, h, e]
    rw [numericPreservedSGramTest_realWishartGram_sumColumnsToFin,
      trace_reindexSplitSquare,
      fderiv_numericPreservedSGramTest_scoreDelta m psi hpsi hH,
      sub_zero]
  have hf : Integrable f μ := by
    have hcomp := hmp.integrable_comp_of_integrable hnum.1
    exact hcomp.congr (Filter.Eventually.of_forall fun R ↦ by
      simpa [Function.comp_def] using hfPoint R)
  have hh : Integrable h μ := by
    have hcomp := hmp.integrable_comp_of_integrable hnum.2.1
    exact hcomp.congr (Filter.Eventually.of_forall fun R ↦ by
      simpa [Function.comp_def] using hhPoint R)
  have heq : (∫ R, f R ∂μ) = ∫ R, h R ∂μ := by
    calc
      (∫ R, f R ∂μ) = ∫ R, fNum (e R) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with R
        exact (hfPoint R).symm
      _ = ∫ X, fNum X ∂ν := hmp.integral_comp' fNum
      _ = ∫ X, hNum X ∂ν := hnum.2.2
      _ = ∫ R, hNum (e R) ∂μ := (hmp.integral_comp' hNum).symm
      _ = ∫ R, h R ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with R
        exact hhPoint R
  simpa [f, h, μ] using And.intro hf (And.intro hh heq)

end Wishart

end

end LogdetLean.GramHafnian
