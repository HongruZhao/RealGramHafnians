import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.PreservedCoordinate
/-!
# Integrated conditional-Wishart score identity

This module separates the finite-dimensional Gaussian integration-by-parts
step from the algebraic simplification of its two sides.  Once the displayed
divergence equality is supplied (for example by `integral_halfGaussianPi_divergence`
after flattening matrix coordinates and checking its integrability hypotheses),
the exact weighted inverse-Gram score identity follows.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*} [Fintype k] [Fintype m]
  [DecidableEq k] [DecidableEq m]

/-- The real-Wishart inverse-score coefficient. -/
def inverseGramScoreCoefficient (k m : Type*) [Fintype k] [Fintype m] : ℝ :=
  ((Fintype.card k : ℝ) - (Fintype.card m : ℝ) - 1) / 2

/-- Abstract integrated score identity.  Its single analytic premise `hIBP`
is exactly the Gaussian divergence theorem for the scalar-weighted lifted
field.  Everything after that premise is pointwise kernel-checked algebra. -/
theorem integral_weighted_inverseGram_score_eq
    [MeasurableSpace (Matrix k m ℝ)]
    (μ : Measure (Matrix k m ℝ))
    (g : Matrix k m ℝ → ℝ)
    (g' : Matrix k m ℝ → Matrix k m ℝ →L[ℝ] ℝ)
    (D : Matrix m m ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (hgzero : ∀ R, IsUnit (realWishartGram R).det →
      g' R (steinVectorFieldValue R D) = 0)
    (hfull : ∀ᵐ R ∂μ, IsUnit (realWishartGram R).det)
    (hIBP :
      (∫ R, weightedSteinCoordinateDivergence g R D ∂μ) =
        ∫ R, 2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D) ∂μ) :
    (∫ R, g R *
        (inverseGramScoreCoefficient k m *
          Matrix.trace ((realWishartGram R)⁻¹ * D)) ∂μ) =
      ∫ R, g R * Matrix.trace D ∂μ := by
  calc
    (∫ R, g R *
        (inverseGramScoreCoefficient k m *
          Matrix.trace ((realWishartGram R)⁻¹ * D)) ∂μ) =
        ∫ R, weightedSteinCoordinateDivergence g R D ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfull] with R hR
      rw [weightedSteinCoordinateDivergence_eq_mul g (g' R) R D
        (hg R) (hgzero R hR) hR,
        steinVectorFieldCoordinateDivergence_eq R D hR]
      rfl
    _ = ∫ R, 2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D) ∂μ := hIBP
    _ = ∫ R, g R * Matrix.trace D ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfull] with R hR
      exact two_mul_weighted_frobenius_steinVectorFieldValue g R D hR

/-- Solve the integrated score identity for the inverse-Gram trace pairing
when the dimension coefficient is nonzero. -/
theorem integral_inverseGram_trace_eq_of_score_identity
    [MeasurableSpace (Matrix k m ℝ)]
    (μ : Measure (Matrix k m ℝ))
    (g : Matrix k m ℝ → ℝ) (D : Matrix m m ℝ)
    (hcoeff : inverseGramScoreCoefficient k m ≠ 0)
    (hscore :
      (∫ R, g R *
          (inverseGramScoreCoefficient k m *
            Matrix.trace ((realWishartGram R)⁻¹ * D)) ∂μ) =
        ∫ R, g R * Matrix.trace D ∂μ) :
    (∫ R, g R * Matrix.trace ((realWishartGram R)⁻¹ * D) ∂μ) =
      (inverseGramScoreCoefficient k m)⁻¹ *
        ∫ R, g R * Matrix.trace D ∂μ := by
  have hleft :
      (∫ R, g R *
          (inverseGramScoreCoefficient k m *
            Matrix.trace ((realWishartGram R)⁻¹ * D)) ∂μ) =
        inverseGramScoreCoefficient k m *
          ∫ R, g R * Matrix.trace ((realWishartGram R)⁻¹ * D) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with R
    ring
  rw [hleft] at hscore
  calc
    (∫ R, g R * Matrix.trace ((realWishartGram R)⁻¹ * D) ∂μ) =
        (inverseGramScoreCoefficient k m)⁻¹ *
          (inverseGramScoreCoefficient k m *
            ∫ R, g R * Matrix.trace ((realWishartGram R)⁻¹ * D) ∂μ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hcoeff, one_mul]
    _ = (inverseGramScoreCoefficient k m)⁻¹ *
          ∫ R, g R * Matrix.trace D ∂μ := by
      rw [hscore]

/-- Integrated score identity specialized to tests whose differentials
factor through the preserved transpose-Gram coordinate `S`. -/
theorem integral_preservedS_inverseGram_scoreDelta_eq
    [MeasurableSpace (Matrix k (m ⊕ m) ℝ)]
    (μ : Measure (Matrix k (m ⊕ m) ℝ))
    (g : Matrix k (m ⊕ m) ℝ → ℝ)
    (g' : Matrix k (m ⊕ m) ℝ →
      Matrix k (m ⊕ m) ℝ →L[ℝ] ℝ)
    (psi' : Matrix k (m ⊕ m) ℝ → Matrix m m ℂ →L[ℝ] ℝ)
    {H : Matrix m m ℂ} (hH : H.IsHermitian)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (hfactor : ∀ R F,
      g' R F = psi' R (sCoordinateFirstVariation R F))
    (hfull : ∀ᵐ R ∂μ, IsUnit (realWishartGram R).det)
    (hIBP :
      (∫ R, weightedSteinCoordinateDivergence g R (scoreDeltaM H) ∂μ) =
        ∫ R, 2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R (scoreDeltaM H)) ∂μ) :
    (∫ R, g R *
        (inverseGramScoreCoefficient k (m ⊕ m) *
          Matrix.trace
            ((realWishartGram R)⁻¹ * scoreDeltaM H)) ∂μ) =
      ∫ R, g R * Matrix.trace (scoreDeltaM H) ∂μ := by
  apply integral_weighted_inverseGram_score_eq μ g g'
    (scoreDeltaM H) hg
  · intro R hR
    exact differential_stein_scoreDelta_eq_zero
      (g' R) (psi' R) R hH (hfactor R) hR
  · exact hfull
  · exact hIBP

end Wishart

end

end LogdetLean.GramHafnian
