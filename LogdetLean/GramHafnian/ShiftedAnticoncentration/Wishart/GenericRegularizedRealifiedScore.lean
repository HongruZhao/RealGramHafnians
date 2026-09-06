import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RegularizedRealifiedScore
/-!
# Regularized realified score for an arbitrary finite column index

The literal hafnian recurrence is indexed by `OddCofactorIndex`, rather than
by a numeric `Fin` type.  This file packages the finite coordinate assembly
without reindexing: all statements are polymorphic in the complex-column
index, and the only analytic input left explicit is almost-sure full rank.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- The real coordinate weight on the realified matrix is definitionally a
test of the preserved `S` coordinate, for any finite index type. -/
@[simp] theorem rankOneRealCoordinateWeight_realified_fintype
    {k I : Type*} [Fintype k] [Fintype I] [LinearOrder I]
    (δ : ℝ) (i j : I) (R : Matrix k (I ⊕ I) ℝ) :
    rankOneRealCoordinateWeight
        (realifiedRegularizedCofactorWeight δ)
        realifiedCofactorVector i j R =
      preservedSWeight
        (regularizedCofactorRealCoordinateWeight δ i j) R := by
  rfl

/-- The imaginary coordinate weight on the realified matrix is
definitionally a test of the preserved `S` coordinate. -/
@[simp] theorem rankOneImagCoordinateWeight_realified_fintype
    {k I : Type*} [Fintype k] [Fintype I] [LinearOrder I]
    (δ : ℝ) (i j : I) (R : Matrix k (I ⊕ I) ℝ) :
    rankOneImagCoordinateWeight
        (realifiedRegularizedCofactorWeight δ)
        realifiedCofactorVector i j R =
      preservedSWeight
        (regularizedCofactorImagCoordinateWeight δ i j) R := by
  rfl

/-- Twice the inverse-Gram score coefficient for two real copies of an
arbitrary finite complex-column index. -/
theorem two_mul_inverseGramScoreCoefficient_fintype_sum
    (k : ℕ) (I : Type*) [Fintype I] :
    2 * inverseGramScoreCoefficient (Fin k) (I ⊕ I) =
      (k : ℝ) - 2 * Fintype.card I - 1 := by
  simp only [inverseGramScoreCoefficient, Fintype.card_fin,
    Fintype.card_sum]
  push_cast
  ring

/-- Coordinate score identities assemble into the coupled score identity
for an arbitrary finite complex-column index. -/
theorem regularized_coupled_score_of_coordinate_scores_fintype
    {k : ℕ} {I : Type*} [Fintype I] [LinearOrder I]
    (δ : ℝ)
    (hfull : ∀ᵐ R ∂halfGaussianMatrixSum k I,
      IsUnit (realWishartGram R).det)
    (hLRe : ∀ i j : I, Integrable (fun R ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
          Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianRealCoordinateDirection i j))))
      (halfGaussianMatrixSum k I))
    (hLIm : ∀ i j : I, Integrable (fun R ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
          Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianImagCoordinateDirection i j))))
      (halfGaussianMatrixSum k I))
    (hRRe : ∀ i j : I, Integrable (fun R ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)))
      (halfGaussianMatrixSum k I))
    (hRIm : ∀ i j : I, Integrable (fun R ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)))
      (halfGaussianMatrixSum k I))
    (hscoreRe : ∀ i j : I,
      (∫ R, rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianRealCoordinateDirection i j)))
        ∂halfGaussianMatrixSum k I) =
      ∫ R, rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j))
        ∂halfGaussianMatrixSum k I)
    (hscoreIm : ∀ i j : I,
      (∫ R, rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianImagCoordinateDirection i j)))
        ∂halfGaussianMatrixSum k I) =
      ∫ R, rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j))
        ∂halfGaussianMatrixSum k I) :
    (∫ R, realifiedRegularizedCofactorWeight δ R *
        (((k : ℝ) - 2 * Fintype.card I - 1) *
          realifiedCoupledCofactorQuadratic R)
        ∂halfGaussianMatrixSum k I) =
      ∫ R, realifiedRegularizedCofactorWeight δ R *
        realifiedCofactorW R
        ∂halfGaussianMatrixSum k I := by
  let μ := halfGaussianMatrixSum k I
  let a := inverseGramScoreCoefficient (Fin k) (I ⊕ I)
  have hrank :
      (∫ R, realifiedRegularizedCofactorWeight δ R *
          (a * Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM
                (hermitianRankOne (realifiedCofactorVector R)))) ∂μ) =
        ∫ R, realifiedRegularizedCofactorWeight δ R *
          Matrix.trace
            (scoreDeltaM
              (hermitianRankOne (realifiedCofactorVector R))) ∂μ := by
    exact integral_variable_rankOne_score_eq_of_coordinate_scores
      μ (fun R ↦ (realWishartGram R)⁻¹)
      (realifiedRegularizedCofactorWeight δ)
      realifiedCofactorVector a
      hLRe hLIm hRRe hRIm hscoreRe hscoreIm
  have hcoupled := integral_coupledQuadratic_eq_of_variable_rankOne_score
    μ (realifiedRegularizedCofactorWeight δ)
      realifiedCofactorVector a hfull hrank
  simpa [μ, a, realifiedCoupledCofactorQuadratic,
    two_mul_inverseGramScoreCoefficient_fintype_sum,
    vectorNormSq_realifiedCofactorVector] using hcoupled

/-- Left coordinate integrability implies integrability of the regularized
coupled inverse quadratic. -/
theorem integrable_regularized_realifiedCoupledCofactorQuadratic_fintype
    {k : ℕ} {I : Type*} [Fintype I] [LinearOrder I]
    (δ : ℝ)
    (hcoeff : (k : ℝ) - 2 * Fintype.card I - 1 ≠ 0)
    (hfull : ∀ᵐ R ∂halfGaussianMatrixSum k I,
      IsUnit (realWishartGram R).det)
    (hLRe : ∀ i j : I, Integrable (fun R ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianRealCoordinateDirection i j))))
      (halfGaussianMatrixSum k I))
    (hLIm : ∀ i j : I, Integrable (fun R ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianImagCoordinateDirection i j))))
      (halfGaussianMatrixSum k I)) :
    Integrable (fun R ↦ realifiedCoupledCofactorQuadratic R /
      (realifiedCofactorW R + δ) ^ 2)
      (halfGaussianMatrixSum k I) := by
  let μ := halfGaussianMatrixSum k I
  let a := inverseGramScoreCoefficient (Fin k) (I ⊕ I)
  let b : ℝ := (k : ℝ) - 2 * Fintype.card I - 1
  have hrank := integrable_variable_rankOne_score_left_of_coordinates
    μ (fun R ↦ (realWishartGram R)⁻¹)
      (realifiedRegularizedCofactorWeight δ)
      realifiedCofactorVector a hLRe hLIm
  have hscaled : Integrable (fun R ↦
      realifiedRegularizedCofactorWeight δ R *
        (b * realifiedCoupledCofactorQuadratic R)) μ := by
    apply hrank.congr
    filter_upwards [hfull] with R hR
    rw [realWishartGram_inverse_rankOne_score_trace_eq_coupled
      R (realifiedCofactorVector R) hR]
    have hab : 2 * a = b := by
      simpa [a, b] using
        two_mul_inverseGramScoreCoefficient_fintype_sum k I
    rw [← hab]
    unfold realifiedCoupledCofactorQuadratic
    ring
  have hunscaled := hscaled.const_mul b⁻¹
  apply hunscaled.congr
  filter_upwards [] with R
  calc
    b⁻¹ * (realifiedRegularizedCofactorWeight δ R *
        (b * realifiedCoupledCofactorQuadratic R)) =
        realifiedRegularizedCofactorWeight δ R *
          realifiedCoupledCofactorQuadratic R := by
      field_simp [show b ≠ 0 by simpa [b] using hcoeff]
    _ = realifiedCoupledCofactorQuadratic R /
        (realifiedCofactorW R + δ) ^ 2 :=
      realifiedRegularizedWeight_mul_quadratic δ R

/-- Right coordinate integrability implies integrability of the regularized
cofactor energy. -/
theorem integrable_regularized_realifiedCofactorW_fintype
    {k : ℕ} {I : Type*} [Fintype I] [LinearOrder I]
    (δ : ℝ)
    (hRRe : ∀ i j : I, Integrable (fun R ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)))
      (halfGaussianMatrixSum k I))
    (hRIm : ∀ i j : I, Integrable (fun R ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)))
      (halfGaussianMatrixSum k I)) :
    Integrable (fun R ↦ realifiedCofactorW R /
      (realifiedCofactorW R + δ) ^ 2)
      (halfGaussianMatrixSum k I) := by
  let μ := halfGaussianMatrixSum k I
  have hrank := integrable_variable_rankOne_score_right_of_coordinates
    μ (realifiedRegularizedCofactorWeight δ)
      realifiedCofactorVector hRRe hRIm
  apply hrank.congr
  filter_upwards [] with R
  rw [trace_scoreDeltaM_hermitianRankOne_eq_vectorNormSq,
    vectorNormSq_realifiedCofactorVector,
    realifiedRegularizedWeight_mul_W]

/-- Pure scalar extraction of the regularized inverse-quadratic identity on
an arbitrary finite split-column law. -/
theorem regularized_realified_integral_identity_fintype
    {k : ℕ} {I : Type*} [Fintype I] [LinearOrder I]
    (δ : ℝ)
    (hcoeff : (k : ℝ) - 2 * Fintype.card I - 1 ≠ 0)
    (hscore :
      (∫ R, realifiedRegularizedCofactorWeight δ R *
          (((k : ℝ) - 2 * Fintype.card I - 1) *
            realifiedCoupledCofactorQuadratic R)
          ∂halfGaussianMatrixSum k I) =
        ∫ R, realifiedRegularizedCofactorWeight δ R *
          realifiedCofactorW R
          ∂halfGaussianMatrixSum k I) :
    (∫ R, realifiedCoupledCofactorQuadratic R /
        (realifiedCofactorW R + δ) ^ 2
        ∂halfGaussianMatrixSum k I) =
      (((k : ℝ) - 2 * Fintype.card I - 1)⁻¹) *
        ∫ R, realifiedCofactorW R /
          (realifiedCofactorW R + δ) ^ 2
          ∂halfGaussianMatrixSum k I := by
  let b : ℝ := (k : ℝ) - 2 * Fintype.card I - 1
  let f : Matrix (Fin k) (I ⊕ I) ℝ → ℝ := fun R ↦
    realifiedCoupledCofactorQuadratic R /
      (realifiedCofactorW R + δ) ^ 2
  let h : Matrix (Fin k) (I ⊕ I) ℝ → ℝ := fun R ↦
    realifiedCofactorW R / (realifiedCofactorW R + δ) ^ 2
  have hbf : (∫ R, realifiedRegularizedCofactorWeight δ R *
        (b * realifiedCoupledCofactorQuadratic R)
        ∂halfGaussianMatrixSum k I) =
      b * ∫ R, f R ∂halfGaussianMatrixSum k I := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with R
    dsimp [f, b]
    rw [← realifiedRegularizedWeight_mul_quadratic]
    ring
  have hright :
      (∫ R, realifiedRegularizedCofactorWeight δ R *
          realifiedCofactorW R ∂halfGaussianMatrixSum k I) =
        ∫ R, h R ∂halfGaussianMatrixSum k I := by
    apply integral_congr_ae
    filter_upwards [] with R
    exact realifiedRegularizedWeight_mul_W δ R
  have hmain : b * ∫ R, f R ∂halfGaussianMatrixSum k I =
      ∫ R, h R ∂halfGaussianMatrixSum k I := by
    rw [← hbf, ← hright]
    exact hscore
  change (∫ R, f R ∂halfGaussianMatrixSum k I) =
    b⁻¹ * ∫ R, h R ∂halfGaussianMatrixSum k I
  calc
    (∫ R, f R ∂halfGaussianMatrixSum k I) =
        b⁻¹ * (b * ∫ R, f R ∂halfGaussianMatrixSum k I) := by
      rw [← mul_assoc, inv_mul_cancel₀ (by simpa [b] using hcoeff), one_mul]
    _ = b⁻¹ * ∫ R, h R ∂halfGaussianMatrixSum k I := by
      rw [hmain]

end Wishart

end

end LogdetLean.GramHafnian
