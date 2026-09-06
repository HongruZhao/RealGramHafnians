import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedRankOneScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RealMatrixSplit
/-!
# Converting the real rank-one score into the coupled complex quadratic form
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*} [Fintype k] [Fintype m]
  [DecidableEq k] [DecidableEq m]

/-- The factor two from realification converts a variable rank-one score
identity into the coupled-complex inverse quadratic-form identity. -/
theorem integral_coupledQuadratic_eq_of_variable_rankOne_score
    [MeasurableSpace (Matrix k (m ⊕ m) ℝ)]
    (μ : Measure (Matrix k (m ⊕ m) ℝ))
    (u : Matrix k (m ⊕ m) ℝ → ℝ)
    (c : Matrix k (m ⊕ m) ℝ → m → ℂ)
    (a : ℝ)
    (hfull : ∀ᵐ R ∂μ, IsUnit (realWishartGram R).det)
    (hscore :
      (∫ R, u R *
          (a * Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianRankOne (c R)))) ∂μ) =
        ∫ R, u R *
          Matrix.trace (scoreDeltaM (hermitianRankOne (c R))) ∂μ) :
    (∫ R, u R *
        ((2 * a) * quadraticFormReal
          (Matrix.toBlocks₁₁
            (coupledGramKernel (complexOfRealMatrix R))⁻¹) (c R)) ∂μ) =
      ∫ R, u R * vectorNormSq (c R) ∂μ := by
  calc
    (∫ R, u R *
        ((2 * a) * quadraticFormReal
          (Matrix.toBlocks₁₁
            (coupledGramKernel (complexOfRealMatrix R))⁻¹) (c R)) ∂μ) =
        ∫ R, u R *
          (a * Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianRankOne (c R)))) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfull] with R hR
      rw [realWishartGram_inverse_rankOne_score_trace_eq_coupled R (c R) hR]
      ring
    _ = ∫ R, u R *
          Matrix.trace (scoreDeltaM (hermitianRankOne (c R))) ∂μ := hscore
    _ = ∫ R, u R * vectorNormSq (c R) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_scoreDeltaM_hermitianRankOne_eq_vectorNormSq]

end Wishart

end

end LogdetLean.GramHafnian
