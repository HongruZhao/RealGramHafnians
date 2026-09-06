import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.BoundedDerivativeSteinHaff
import Mathlib.Analysis.Calculus.LineDeriv.Basic
/-!
# Derivative-free Stein--Haff interface for line-invariant tests

The value of a Frechet derivative carries the chosen topology instances of
its matrix domain.  That makes it a poor interface between modules which use
definitionally equivalent finite-dimensional matrix norms.  Literal line
invariance is topology-free.  This module derives the vanishing directional
derivative internally and exports the Stein--Haff identity with no derivative
term in its statement.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

local instance lineInvariantMatrixFunctionalNorm
    {p : Type*} [Fintype p] :
    Norm (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

local instance lineInvariantMatrixFunctionalSeminormedAddCommGroup
    {p : Type*} [Fintype p] :
    SeminormedAddCommGroup (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- A differentiable function which is constant on every affine line in
direction `D` has zero Frechet derivative in that direction. -/
theorem fderiv_apply_eq_zero_of_add_smul_invariant
    {p : Type*} [Fintype p]
    (phi : Matrix p p ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (D : Matrix p p ℝ)
    (hinv : ∀ M (t : ℝ), phi (M + t • D) = phi M)
    (M : Matrix p p ℝ) :
    fderiv ℝ phi M D = 0 := by
  have hline :
      HasLineDerivAt ℝ phi (fderiv ℝ phi M D) M D :=
    (hphi.differentiable (by simp)).differentiableAt.hasFDerivAt.hasLineDerivAt D
  have hzero : HasLineDerivAt ℝ phi 0 M D := by
    change HasDerivAt (fun t : ℝ ↦ phi (M + t • D)) 0 0
    simpa only [hinv] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := phi M))
  exact hline.unique hzero

/-- A line-invariant bounded `C¹` test satisfies the exact numeric
Stein--Haff identity with a derivative-free right side.  This conclusion is
safe to transport across equivalent finite-dimensional matrix topologies. -/
theorem steinHaff_halfGaussianMatrix_of_bounded_fderiv_of_lineInvariant
    {k p : ℕ} (hgap : p + 1 < k)
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (hphi : ContDiff ℝ 1 phi)
    (C₀ : ℝ) (hphiBound : ∀ M, |phi M| ≤ C₀)
    (C₁ : ℝ) (hphiDerivBound : ∀ M, ‖fderiv ℝ phi M‖ ≤ C₁)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm)
    (hinv : ∀ M (t : ℝ), phi (M + t • D) = phi M) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          phi (realWishartGram R) *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          phi (realWishartGram R) * Matrix.trace D)
        (halfGaussianMatrix k p) ∧
      ((∫ R, phi (realWishartGram R) *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, phi (realWishartGram R) * Matrix.trace D
          ∂halfGaussianMatrix k p) := by
  have h := steinHaff_halfGaussianMatrix_of_bounded_fderiv
    hgap phi hphi C₀ hphiBound C₁ hphiDerivBound D hD
  have hzero : ∀ M, fderiv ℝ phi M D = 0 :=
    fderiv_apply_eq_zero_of_add_smul_invariant phi hphi D hinv
  simpa only [hzero, sub_zero] using h

end Wishart

end

end LogdetLean.GramHafnian
