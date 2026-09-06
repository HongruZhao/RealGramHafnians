import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericFixedDirectionIntegrability
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.InternalPreservedSScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.PreservedSSmoothMeasureExtension
/-!
# Bounded measurable preserved-S Wishart score

This file derives the exact conditional score identity needed downstream
from the internal scalar-Gaussian integration-by-parts theorem.  All steps
are kernel checked:

* a smooth test is composed with the linear `S` coordinate of the real Gram
  matrix;
* its directional derivative in `scoreDeltaM H` is proved to be exactly
  zero from the deterministic preserved-coordinate algebra;
* smooth compactly supported tests are extended to arbitrary bounded Borel
  tests by the axiom-free measure-extension theorem;
* both weighted densities are proved integrable.

The main theorem is polymorphic in the complex-column index type, so it can
be applied directly to `OddCofactorIndex` without an additional hafnian
reindexing argument.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/- Keep the finite matrix norm topology coherent with the coordinatewise
Borel measurable space. -/
local instance boundedScoreMatrixNormedAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : NormedAddCommGroup (Matrix a b 𝕜) :=
  Matrix.normedAddCommGroup

local instance boundedScoreMatrixNormedSpace
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    NormedSpace 𝔽 (Matrix a b 𝕜) :=
  Matrix.normedSpace

local instance boundedScoreMatrixAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : AddCommGroup (Matrix a b 𝕜) :=
  boundedScoreMatrixNormedAddCommGroup.toAddCommGroup

local instance boundedScoreMatrixModule
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    Module 𝔽 (Matrix a b 𝕜) :=
  boundedScoreMatrixNormedSpace.toModule

local instance boundedScoreMatrixPseudoMetricSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : PseudoMetricSpace (Matrix a b 𝕜) :=
  boundedScoreMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance boundedScoreMatrixUniformSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : UniformSpace (Matrix a b 𝕜) :=
  boundedScoreMatrixPseudoMetricSpace.toUniformSpace

local instance boundedScoreMatrixTopologicalSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : TopologicalSpace (Matrix a b 𝕜) :=
  boundedScoreMatrixUniformSpace.toTopologicalSpace

local instance boundedScoreComplexMatrixBorelSpace
    (a b : Type*) [Fintype a] [Fintype b] :
    BorelSpace (Matrix a b ℂ) := by
  change BorelSpace (a → b → ℂ)
  infer_instance

/-- The linear extraction of the complex `S` coordinate is measurable for
the explicit coordinatewise matrix measurable spaces. -/
theorem measurable_sCoordinateOfRealGram
    {I : Type*} :
    Measurable (sCoordinateOfRealGram :
      Matrix (I ⊕ I) (I ⊕ I) ℝ → Matrix I I ℂ) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [sCoordinateOfRealGram, sOfRealBlocks, realGramBlock11,
    realGramBlock12, realGramBlock22]
  fun_prop

/-- A scalar test of the linear `S` coordinate, viewed as a function of a
real square Gram matrix. -/
def gramPreservedSWeight
    {I : Type*} (psi : Matrix I I ℂ → ℝ)
    (M : Matrix (I ⊕ I) (I ⊕ I) ℝ) : ℝ :=
  psi (sCoordinateOfRealGram M)

/-- A score-direction line leaves every test of the preserved `S`
coordinate literally constant. -/
theorem gramPreservedSWeight_add_smul_scoreDelta
    {I : Type*} [Fintype I] [DecidableEq I]
    (psi : Matrix I I ℂ → ℝ)
    (M : Matrix (I ⊕ I) (I ⊕ I) ℝ) (t : ℝ)
    {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    gramPreservedSWeight psi (M + t • scoreDeltaM H) =
      gramPreservedSWeight psi M := by
  have hS : sCoordinateOfRealGram (scoreDeltaM H) = 0 := by
    simpa [scoreDeltaM] using sOf_scoreDelta hH
  change psi (sCoordinateOfRealGram (M + t • scoreDeltaM H)) =
    psi (sCoordinateOfRealGram M)
  change psi (sCoordinateOfRealGramCLM (M + t • scoreDeltaM H)) =
    psi (sCoordinateOfRealGramCLM M)
  rw [map_add, map_smul]
  simp [hS]

/-- Smooth compactly supported preserved-`S` tests satisfy the fixed-H score
identity.  This is the arbitrary-index projection of the internally proved
numeric Stein--Haff identity. -/
theorem integral_smooth_preservedSWeight_fixedH_score_halfGaussianMatrixSum
    {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (psi : Matrix I I ℂ → ℝ)
    (hpsi : ContDiff ℝ 1 psi) (hpsiSupport : HasCompactSupport psi)
    {H : Matrix I I ℂ} (hH : H.IsHermitian)
    (hgap : Fintype.card (I ⊕ I) + 1 < k) :
    (∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
        preservedSWeight psi R *
          (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
            Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
        ∂halfGaussianMatrixSum k I) =
      ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
        preservedSWeight psi R * Matrix.trace (scoreDeltaM H)
        ∂halfGaussianMatrixSum k I := by
  exact (internal_smooth_preservedS_score_pair_halfGaussianMatrixSum
    psi hpsi hpsiSupport hH hgap).2.2

/-- Unweighted fixed-direction score and constant densities are integrable
for an arbitrary finite split column index. -/
theorem integrable_fixedDirection_score_pair_halfGaussianMatrixSum
    {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix (I ⊕ I) (I ⊕ I) ℝ) (hD : D.IsSymm)
    (hgap : Fintype.card (I ⊕ I) + 1 < k) :
    Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
            Matrix.trace ((realWishartGram R)⁻¹ * D))
        (halfGaussianMatrixSum k I) ∧
      Integrable
        (fun _R : Matrix (Fin k) (I ⊕ I) ℝ ↦ Matrix.trace D)
        (halfGaussianMatrixSum k I) := by
  exact
    integrable_fixedDirection_score_pair_halfGaussianMatrixSum_internal D hgap

/-- Main generic endpoint: every bounded Borel function of the preserved
`S` coordinate satisfies the fixed-H score identity, and both displayed
densities are integrable. -/
theorem bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
    {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (u : Matrix I I ℂ → ℝ) (hu : Measurable u)
    (C : ℝ) (huC : ∀ S, |u S| ≤ C)
    {H : Matrix I I ℂ} (hH : H.IsHermitian)
    (hgap : Fintype.card (I ⊕ I) + 1 < k) :
    Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          preservedSWeight u R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)))
        (halfGaussianMatrixSum k I) ∧
      Integrable
        (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
          preservedSWeight u R * Matrix.trace (scoreDeltaM H))
        (halfGaussianMatrixSum k I) ∧
      ((∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          preservedSWeight u R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
          ∂halfGaussianMatrixSum k I) =
        ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          preservedSWeight u R * Matrix.trace (scoreDeltaM H)
          ∂halfGaussianMatrixSum k I) := by
  let μ : Measure (Matrix (Fin k) (I ⊕ I) ℝ) :=
    halfGaussianMatrixSum k I
  let S : Matrix (Fin k) (I ⊕ I) ℝ → Matrix I I ℂ :=
    preservedSCoordinate
  let f : Matrix (Fin k) (I ⊕ I) ℝ → ℝ := fun R ↦
    inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
      Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)
  let h : Matrix (Fin k) (I ⊕ I) ℝ → ℝ := fun _ ↦
    Matrix.trace (scoreDeltaM H)
  obtain ⟨hf, hh⟩ :=
    integrable_fixedDirection_score_pair_halfGaussianMatrixSum
      (scoreDeltaM H) (scoreDeltaM_isSymm hH) hgap
  have hS : Measurable S := by
    exact measurable_preservedSCoordinate
  have hfmeas : Measurable f := by
    exact measurable_const.mul
      (measurable_trace_nonsingInv_realWishartGram_mul_const
        (scoreDeltaM H))
  have hhmeas : Measurable h := measurable_const
  have hucomp : AEStronglyMeasurable (fun R ↦ u (S R)) μ :=
    (hu.comp hS).aestronglyMeasurable
  have hubound : ∀ᵐ R ∂μ, ‖u (S R)‖ ≤ C :=
    Filter.Eventually.of_forall fun R ↦ by
      simpa [Real.norm_eq_abs] using huC (S R)
  have huf : Integrable (fun R ↦ u (S R) * f R) μ :=
    hf.bdd_mul hucomp hubound
  have huh : Integrable (fun R ↦ u (S R) * h R) μ :=
    hh.bdd_mul hucomp hubound
  have heq : (∫ R, u (S R) * f R ∂μ) =
      ∫ R, u (S R) * h R ∂μ := by
    have hsmooth : ∀ (g : Matrix I I ℂ → ℝ),
        ContDiff ℝ 1 g → HasCompactSupport g →
          ((∫ R, g (S R) * f R ∂μ) =
            ∫ R, g (S R) * h R ∂μ) := by
      intro g hg hsupp
      simpa [μ, S, f, h, preservedSWeight] using
        (integral_smooth_preservedSWeight_fixedH_score_halfGaussianMatrixSum
          g hg hsupp hH hgap)
    exact integral_comp_mul_eq_of_contDiff_compactSupport
      μ S f h hS hfmeas hhmeas hf hh hsmooth u hu C huC
  simpa [μ, S, f, h, preservedSWeight] using
    And.intro huf (And.intro huh heq)

end Wishart

end

end LogdetLean.GramHafnian
