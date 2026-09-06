import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericPreservedSReindex
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Smooth compact-support transport for finite complex matrix indices

This file packages the elementary fact that canonical finite-type matrix
reindexing is a continuous linear equivalence.  Consequently `C¹` regularity
and compact support of preserved-`S` tests survive transport from an arbitrary
finite index type to its `Fin (card I)` model.
-/

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

local instance genericSmoothMatrixNormedAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : NormedAddCommGroup (Matrix a b 𝕜) :=
  Matrix.normedAddCommGroup

local instance genericSmoothMatrixNormedSpace
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    NormedSpace 𝔽 (Matrix a b 𝕜) :=
  Matrix.normedSpace

local instance genericSmoothMatrixAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : AddCommGroup (Matrix a b 𝕜) :=
  genericSmoothMatrixNormedAddCommGroup.toAddCommGroup

local instance genericSmoothMatrixModule
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    Module 𝔽 (Matrix a b 𝕜) :=
  genericSmoothMatrixNormedSpace.toModule

local instance genericSmoothMatrixPseudoMetricSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : PseudoMetricSpace (Matrix a b 𝕜) :=
  genericSmoothMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance genericSmoothMatrixUniformSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : UniformSpace (Matrix a b 𝕜) :=
  genericSmoothMatrixPseudoMetricSpace.toUniformSpace

local instance genericSmoothMatrixTopologicalSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : TopologicalSpace (Matrix a b 𝕜) :=
  genericSmoothMatrixUniformSpace.toTopologicalSpace

/-- Canonical complex square reindexing as a continuous real-linear
equivalence. -/
def reindexGenericComplexSquareCLE (I : Type*) [Fintype I] :
    Matrix I I ℂ ≃L[ℝ]
      Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ :=
  (Matrix.reindexLinearEquiv ℝ ℂ
    (Fintype.equivFin I) (Fintype.equivFin I)).toContinuousLinearEquiv

@[simp] theorem reindexGenericComplexSquareCLE_apply
    (I : Type*) [Fintype I] (S : Matrix I I ℂ) :
    reindexGenericComplexSquareCLE I S = reindexGenericComplexSquare I S := by
  rfl

@[simp] theorem reindexGenericComplexSquareCLE_symm_apply
    (I : Type*) [Fintype I]
    (S : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ) :
    (reindexGenericComplexSquareCLE I).symm S =
      unreindexGenericComplexSquare I S := by
  rfl

/-- Canonical test reindexing preserves `C¹` regularity. -/
theorem contDiff_reindexGenericComplexTest
    (I : Type*) [Fintype I]
    (psi : Matrix I I ℂ → ℝ) (hpsi : ContDiff ℝ 1 psi) :
    ContDiff ℝ 1 (reindexGenericComplexTest I psi) := by
  change ContDiff ℝ 1
    (fun S ↦ psi (unreindexGenericComplexSquare I S))
  have heq : (psi ∘ (reindexGenericComplexSquareCLE I).symm) =
      fun S ↦ psi (unreindexGenericComplexSquare I S) := by
    funext S
    rw [Function.comp_apply,
      reindexGenericComplexSquareCLE_symm_apply]
  rw [← heq]
  exact hpsi.comp (reindexGenericComplexSquareCLE I).symm.contDiff

/-- Canonical test reindexing preserves compact support. -/
theorem hasCompactSupport_reindexGenericComplexTest
    (I : Type*) [Fintype I]
    (psi : Matrix I I ℂ → ℝ) (hsupp : HasCompactSupport psi) :
    HasCompactSupport (reindexGenericComplexTest I psi) := by
  change HasCompactSupport
    (fun S ↦ psi (unreindexGenericComplexSquare I S))
  have heq :
      (psi ∘ (reindexGenericComplexSquareCLE I).symm.toHomeomorph) =
        fun S ↦ psi (unreindexGenericComplexSquare I S) := by
    funext S
    change psi ((reindexGenericComplexSquareCLE I).symm S) =
      psi (unreindexGenericComplexSquare I S)
    rw [reindexGenericComplexSquareCLE_symm_apply]
  rw [← heq]
  exact hsupp.comp_homeomorph
    (reindexGenericComplexSquareCLE I).symm.toHomeomorph

end Wishart

end

end LogdetLean.GramHafnian
