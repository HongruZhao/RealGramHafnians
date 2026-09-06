import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SteinHaffCutoff
/-!
# Stein--Haff from a uniformly bounded full derivative

This module gives an entirely internal numeric Stein--Haff theorem under the
stronger regularity assumption that both a Gram test and its full Frechet
derivative are uniformly bounded.  `SteinHaffCutoff` supplies the genuine
coordinatewise `L¹` estimates; this file packages them through
`MatrixSteinHaffClosure` and exposes the literal `fderiv` formula.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

local instance boundedDerivativeMatrixFunctionalNorm
    {p : Type*} [Fintype p] :
    Norm (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

local instance boundedDerivativeMatrixFunctionalSeminormedAddCommGroup
    {p : Type*} [Fintype p] :
    SeminormedAddCommGroup (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The derivative of a pulled-back Gram test, evaluated on the Stein field,
is exactly the chosen symmetric Gram direction. -/
theorem gramTestWeightDerivative_fderiv_steinVectorFieldValue
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (phi : Matrix p p ℝ → ℝ)
    {D : Matrix p p ℝ} (hD : D.IsSymm)
    (R : Matrix k p ℝ) (hfull : IsUnit (realWishartGram R).det) :
    gramTestWeightDerivative (fun M ↦ fderiv ℝ phi M) R
        (steinVectorFieldValue R D) =
      fderiv ℝ phi (realWishartGram R) D := by
  exact gramTestWeightDerivative_steinVectorFieldValue
    (fun M ↦ fderiv ℝ phi M) R D hD hfull

/-- A `C¹` scalar Gram test pulls back differentiably through `R ↦ RᵀR`,
with the literal Frechet derivative. -/
theorem hasFDerivAt_gramTestWeight_fderiv
    {k p : Type*} [Fintype k] [Fintype p]
    (phi : Matrix p p ℝ → ℝ) (hphi : ContDiff ℝ 1 phi)
    (R : Matrix k p ℝ) :
    HasFDerivAt (gramTestWeight phi)
      (gramTestWeightDerivative (fun M ↦ fderiv ℝ phi M) R) R := by
  apply hasFDerivAt_gramTestWeight phi (fun M ↦ fderiv ℝ phi M)
  intro M
  exact (hphi.differentiable (by simp)).differentiableAt.hasFDerivAt

/-- A uniformly bounded full derivative makes every fixed directional
derivative along the random Gram matrix integrable. -/
theorem integrable_fderiv_realWishartGram_apply_halfGaussianMatrix
    {k p : ℕ}
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (hphi : ContDiff ℝ 1 phi)
    (C₁ : ℝ) (hphiDerivBound : ∀ M, ‖fderiv ℝ phi M‖ ≤ C₁)
    (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        fderiv ℝ phi (realWishartGram R) D)
      (halfGaussianMatrix k p) := by
  have hcont : Continuous
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        fderiv ℝ phi (realWishartGram R) D) :=
    ((hphi.continuous_fderiv (by simp)).comp
      continuous_realWishartGram_genericSteinHaff).clm_apply continuous_const
  refine (integrable_const (C₁ * ‖D‖)).mono'
    ((measurable_of_continuous_matrix_real_genericSteinHaff _ hcont).aestronglyMeasurable)
    ?_
  filter_upwards [] with R
  calc
    ‖fderiv ℝ phi (realWishartGram R) D‖ ≤
        ‖fderiv ℝ phi (realWishartGram R)‖ * ‖D‖ :=
      (fderiv ℝ phi (realWishartGram R)).le_opNorm D
    _ ≤ C₁ * ‖D‖ :=
      mul_le_mul_of_nonneg_right
        (hphiDerivBound (realWishartGram R)) (norm_nonneg D)

/-- Numeric Stein--Haff identity proved solely from scalar Gaussian
integration by parts.  Uniform bounds on the test and on its full Frechet
derivative ensure all singular coordinate fields are integrable at the sharp
first inverse-Wishart threshold `p + 1 < k`. -/
theorem steinHaff_halfGaussianMatrix_of_bounded_fderiv
    {k p : ℕ} (hgap : p + 1 < k)
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (hphi : ContDiff ℝ 1 phi)
    (C₀ : ℝ) (hphiBound : ∀ M, |phi M| ≤ C₀)
    (C₁ : ℝ) (hphiDerivBound : ∀ M, ‖fderiv ℝ phi M‖ ≤ C₁)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          phi (realWishartGram R) *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          phi (realWishartGram R) * Matrix.trace D -
            fderiv ℝ phi (realWishartGram R) D)
        (halfGaussianMatrix k p) ∧
      ((∫ R, phi (realWishartGram R) *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, phi (realWishartGram R) * Matrix.trace D -
          fderiv ℝ phi (realWishartGram R) D
          ∂halfGaussianMatrix k p) := by
  by_cases hp0 : p = 0
  · subst p
    have hDzero : D = 0 := Subsingleton.elim _ _
    subst D
    simp
  · let n := k * p - 1
    have hp : 0 < p := Nat.pos_of_ne_zero hp0
    have hk : 0 < k := by omega
    have hprod : 0 < k * p := Nat.mul_pos hk hp
    have hdim : n + 1 = k * p := by
      dsimp [n]
      omega
    have hphi'Cont : Continuous
        (fun M : Matrix (Fin p) (Fin p) ℝ ↦ fderiv ℝ phi M) :=
      hphi.continuous_fderiv (by simp)
    obtain ⟨hvalue, hderiv, hradial⟩ :=
      integrable_flattenedGramTestSteinComponent_families
        hdim hgap phi hphi.continuous
          (fun M ↦ fderiv ℝ phi M) hphi'Cont
          C₀ hphiBound C₁ hphiDerivBound D
    have hclose := steinHaff_halfGaussianMatrix_of_flattenedSteinFamilies
      hdim (by omega)
      (gramTestWeight phi)
      (fun R ↦ gramTestWeightDerivative (fun M ↦ fderiv ℝ phi M) R)
      D
      (fun R ↦ fderiv ℝ phi (realWishartGram R) D)
      (hasFDerivAt_gramTestWeight_fderiv phi hphi)
      (fun R hR ↦
        gramTestWeightDerivative_fderiv_steinVectorFieldValue
          phi hD R hR)
      (integrable_fderiv_realWishartGram_apply_halfGaussianMatrix
        phi hphi C₁ hphiDerivBound D)
      hvalue hderiv hradial
    simpa [gramTestWeight] using hclose

end Wishart

end

end LogdetLean.GramHafnian
