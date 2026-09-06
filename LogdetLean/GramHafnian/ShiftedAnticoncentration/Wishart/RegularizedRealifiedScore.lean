import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RegularizedCofactorWeights
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedCoupledScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FixedHPreservedSScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FixedHScoreIntegrability
/-!
# Regularized cofactor score on the realified matrix model

This module names the three quantities that occur in the bounded score test
and performs the exact scalar algebra which solves the coupled score identity
for the regularized inverse quadratic form.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Cofactor vector read from the preserved `S` coordinate of a split real
matrix. -/
def realifiedCofactorVector {k m : Type*} [Fintype k] [Fintype m]
    [LinearOrder m]
    (R : Matrix k (m ⊕ m) ℝ) : m → ℂ :=
  preservedCofactorVector (preservedSCoordinate R)

/-- Cofactor energy read from the preserved coordinate. -/
def realifiedCofactorW {k m : Type*} [Fintype k] [Fintype m]
    [LinearOrder m]
    (R : Matrix k (m ⊕ m) ℝ) : ℝ :=
  transposeGramCofactorW (preservedSCoordinate R)

/-- Upper-left coupled-inverse quadratic form paired with the cofactor
vector.  This is the exact quantity produced by the factor-two score
identity. -/
def realifiedCoupledCofactorQuadratic {k m : Type*}
    [Fintype k] [Fintype m] [LinearOrder m]
    (R : Matrix k (m ⊕ m) ℝ) : ℝ :=
  quadraticFormReal
    (Matrix.toBlocks₁₁
      (coupledGramKernel (complexOfRealMatrix R))⁻¹)
    (realifiedCofactorVector R)

/-- The regularized inverse-square cofactor-energy weight on real matrices. -/
def realifiedRegularizedCofactorWeight {k m : Type*}
    [Fintype k] [Fintype m] [LinearOrder m] (δ : ℝ)
    (R : Matrix k (m ⊕ m) ℝ) : ℝ :=
  regularizedCofactorWeight δ (preservedSCoordinate R)

@[simp] theorem vectorNormSq_realifiedCofactorVector
    {k m : Type*} [Fintype k] [Fintype m]
    [LinearOrder m]
    (R : Matrix k (m ⊕ m) ℝ) :
    vectorNormSq (realifiedCofactorVector R) = realifiedCofactorW R := by
  exact vectorNormSq_preservedCofactorVector (preservedSCoordinate R)

theorem realifiedRegularizedWeight_mul_W
    {k m : Type*} [Fintype k] [Fintype m]
    [LinearOrder m]
    (δ : ℝ) (R : Matrix k (m ⊕ m) ℝ) :
    realifiedRegularizedCofactorWeight δ R * realifiedCofactorW R =
      realifiedCofactorW R / (realifiedCofactorW R + δ) ^ 2 := by
  simpa [realifiedRegularizedCofactorWeight, realifiedCofactorW,
    vectorNormSq_preservedCofactorVector] using
    regularized_weight_mul_vectorNormSq δ (preservedSCoordinate R)

theorem realifiedRegularizedWeight_mul_quadratic
    {k m : Type*} [Fintype k] [Fintype m]
    [LinearOrder m]
    (δ : ℝ) (R : Matrix k (m ⊕ m) ℝ) :
    realifiedRegularizedCofactorWeight δ R *
        realifiedCoupledCofactorQuadratic R =
      realifiedCoupledCofactorQuadratic R /
        (realifiedCofactorW R + δ) ^ 2 := by
  unfold realifiedRegularizedCofactorWeight regularizedCofactorWeight
    realifiedCofactorW
  rw [inv_pow, div_eq_mul_inv]
  ring

/-- Twice the real-Wishart score coefficient is the literal residual
degrees-of-freedom factor. -/
theorem two_mul_inverseGramScoreCoefficient_fin_sum (k m : ℕ) :
    2 * inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) =
      (k : ℝ) - 2 * m - 1 := by
  simp only [inverseGramScoreCoefficient, Fintype.card_fin,
    Fintype.card_sum]
  push_cast
  ring

@[simp] theorem rankOneRealCoordinateWeight_realified
    (δ : ℝ) (i j : Fin m)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    rankOneRealCoordinateWeight
        (realifiedRegularizedCofactorWeight δ)
        realifiedCofactorVector i j R =
      preservedSWeight
        (regularizedCofactorRealCoordinateWeight δ i j) R := by
  rfl

@[simp] theorem rankOneImagCoordinateWeight_realified
    (δ : ℝ) (i j : Fin m)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    rankOneImagCoordinateWeight
        (realifiedRegularizedCofactorWeight δ)
        realifiedCofactorVector i j R =
      preservedSWeight
        (regularizedCofactorImagCoordinateWeight δ i j) R := by
  rfl

/-- Both fixed-score integrability facts for a regularized real coordinate
weight. -/
theorem integrable_regularized_realCoordinate_score_pair
    {k m : ℕ} {δ : ℝ} (hδ : 0 < δ) (hgap : 2 * m + 1 < k)
    (i j : Fin m) :
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianRealCoordinateDirection i j))))
      (halfGaussianMatrixSum k (Fin m)) ∧
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)))
      (halfGaussianMatrixSum k (Fin m)) := by
  simpa only [rankOneRealCoordinateWeight_realified] using
    (integrable_bounded_preservedSWeight_fixedH_score_pair
      (regularizedCofactorRealCoordinateWeight δ i j)
      (measurable_regularizedCofactorRealCoordinateWeight hδ i j)
      δ⁻¹ (abs_regularizedCofactorRealCoordinateWeight_le hδ i j)
      (H := hermitianRealCoordinateDirection i j) hgap)

/-- Both fixed-score integrability facts for a regularized imaginary
coordinate weight. -/
theorem integrable_regularized_imagCoordinate_score_pair
    {k m : ℕ} {δ : ℝ} (hδ : 0 < δ) (hgap : 2 * m + 1 < k)
    (i j : Fin m) :
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianImagCoordinateDirection i j))))
      (halfGaussianMatrixSum k (Fin m)) ∧
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)))
      (halfGaussianMatrixSum k (Fin m)) := by
  simpa only [rankOneImagCoordinateWeight_realified] using
    (integrable_bounded_preservedSWeight_fixedH_score_pair
      (regularizedCofactorImagCoordinateWeight δ i j)
      (measurable_regularizedCofactorImagCoordinateWeight hδ i j)
      δ⁻¹ (abs_regularizedCofactorImagCoordinateWeight_le hδ i j)
      (H := hermitianImagCoordinateDirection i j) hgap)

/-- Assemble fixed real/imaginary matrix-unit score identities into the
regularized variable-rank-one coupled score.  The hypotheses are kept in
the exact generic form produced by the bounded fixed-H theorem. -/
theorem regularized_coupled_score_of_coordinate_scores
    {k m : ℕ} (δ : ℝ) (hgap : 2 * m < k)
    (hLRe : ∀ i j : Fin m, Integrable (fun R ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianRealCoordinateDirection i j))))
      (halfGaussianMatrixSum k (Fin m)))
    (hLIm : ∀ i j : Fin m, Integrable (fun R ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianImagCoordinateDirection i j))))
      (halfGaussianMatrixSum k (Fin m)))
    (hRRe : ∀ i j : Fin m, Integrable (fun R ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)))
      (halfGaussianMatrixSum k (Fin m)))
    (hRIm : ∀ i j : Fin m, Integrable (fun R ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)))
      (halfGaussianMatrixSum k (Fin m)))
    (hscoreRe : ∀ i j : Fin m,
      (∫ R, rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianRealCoordinateDirection i j)))
        ∂halfGaussianMatrixSum k (Fin m)) =
      ∫ R, rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j))
        ∂halfGaussianMatrixSum k (Fin m))
    (hscoreIm : ∀ i j : Fin m,
      (∫ R, rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianImagCoordinateDirection i j)))
        ∂halfGaussianMatrixSum k (Fin m)) =
      ∫ R, rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j))
        ∂halfGaussianMatrixSum k (Fin m)) :
    (∫ R, realifiedRegularizedCofactorWeight δ R *
        (((k : ℝ) - 2 * m - 1) *
          realifiedCoupledCofactorQuadratic R)
        ∂halfGaussianMatrixSum k (Fin m)) =
      ∫ R, realifiedRegularizedCofactorWeight δ R *
        realifiedCofactorW R
        ∂halfGaussianMatrixSum k (Fin m) := by
  let μ := halfGaussianMatrixSum k (Fin m)
  let a := inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m)
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
      realifiedCofactorVector a
      (ae_isUnit_det_realWishartGram_halfGaussianMatrixSum
        k m (by omega)) hrank
  simpa [μ, a, realifiedCoupledCofactorQuadratic,
    two_mul_inverseGramScoreCoefficient_fin_sum,
    vectorNormSq_realifiedCofactorVector] using hcoupled

/-- The same left coordinate hypotheses give integrability of the
regularized coupled quadratic required by the scalar limit theorem. -/
theorem integrable_regularized_realifiedCoupledCofactorQuadratic_of_coordinates
    {k m : ℕ} (δ : ℝ) (hgap : 2 * m + 1 < k)
    (hLRe : ∀ i j : Fin m, Integrable (fun R ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianRealCoordinateDirection i j))))
      (halfGaussianMatrixSum k (Fin m)))
    (hLIm : ∀ i j : Fin m, Integrable (fun R ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace
            ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianImagCoordinateDirection i j))))
      (halfGaussianMatrixSum k (Fin m))) :
    Integrable (fun R ↦ realifiedCoupledCofactorQuadratic R /
      (realifiedCofactorW R + δ) ^ 2)
      (halfGaussianMatrixSum k (Fin m)) := by
  let μ := halfGaussianMatrixSum k (Fin m)
  let a := inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m)
  let b : ℝ := (k : ℝ) - 2 * m - 1
  have hrank := integrable_variable_rankOne_score_left_of_coordinates
    μ (fun R ↦ (realWishartGram R)⁻¹)
      (realifiedRegularizedCofactorWeight δ)
      realifiedCofactorVector a hLRe hLIm
  have hfull := ae_isUnit_det_realWishartGram_halfGaussianMatrixSum
    k m (by omega)
  have hscaled : Integrable (fun R ↦
      realifiedRegularizedCofactorWeight δ R *
        (b * realifiedCoupledCofactorQuadratic R)) μ := by
    apply hrank.congr
    filter_upwards [hfull] with R hR
    rw [realWishartGram_inverse_rankOne_score_trace_eq_coupled
      R (realifiedCofactorVector R) hR]
    have hab : 2 * a = b := by
      simpa [a, b] using two_mul_inverseGramScoreCoefficient_fin_sum k m
    rw [← hab]
    unfold realifiedCoupledCofactorQuadratic
    ring
  have hb : b ≠ 0 := by
    have hkR : ((2 * m + 1 : ℕ) : ℝ) < (k : ℝ) := by
      exact_mod_cast hgap
    dsimp [b]
    push_cast at hkR
    linarith
  have hunscaled := hscaled.const_mul b⁻¹
  apply hunscaled.congr
  filter_upwards [] with R
  calc
    b⁻¹ * (realifiedRegularizedCofactorWeight δ R *
        (b * realifiedCoupledCofactorQuadratic R)) =
        realifiedRegularizedCofactorWeight δ R *
          realifiedCoupledCofactorQuadratic R := by
      field_simp [hb]
    _ = realifiedCoupledCofactorQuadratic R /
        (realifiedCofactorW R + δ) ^ 2 :=
      realifiedRegularizedWeight_mul_quadratic δ R

/-- The right coordinate hypotheses give integrability of the regularized
cofactor energy. -/
theorem integrable_regularized_realifiedCofactorW_of_coordinates
    {k m : ℕ} (δ : ℝ)
    (hRRe : ∀ i j : Fin m, Integrable (fun R ↦
      rankOneRealCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)))
      (halfGaussianMatrixSum k (Fin m)))
    (hRIm : ∀ i j : Fin m, Integrable (fun R ↦
      rankOneImagCoordinateWeight
          (realifiedRegularizedCofactorWeight δ)
          realifiedCofactorVector i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)))
      (halfGaussianMatrixSum k (Fin m))) :
    Integrable (fun R ↦ realifiedCofactorW R /
      (realifiedCofactorW R + δ) ^ 2)
      (halfGaussianMatrixSum k (Fin m)) := by
  let μ := halfGaussianMatrixSum k (Fin m)
  have hrank := integrable_variable_rankOne_score_right_of_coordinates
    μ (realifiedRegularizedCofactorWeight δ)
      realifiedCofactorVector hRRe hRIm
  apply hrank.congr
  filter_upwards [] with R
  rw [trace_scoreDeltaM_hermitianRankOne_eq_vectorNormSq,
    vectorNormSq_realifiedCofactorVector,
    realifiedRegularizedWeight_mul_W]

/-- Solve the already-assembled coupled score identity for the regularized
quadratic integral.  This step is purely scalar and measure-theoretic. -/
theorem regularized_realified_integral_identity_of_coupled_score
    {k m : ℕ} (δ : ℝ)
    (hcoeff : (k : ℝ) - 2 * m - 1 ≠ 0)
    (hscore :
      (∫ R, realifiedRegularizedCofactorWeight δ R *
          (((k : ℝ) - 2 * m - 1) *
            realifiedCoupledCofactorQuadratic R)
          ∂halfGaussianMatrixSum k (Fin m)) =
        ∫ R, realifiedRegularizedCofactorWeight δ R *
          realifiedCofactorW R
          ∂halfGaussianMatrixSum k (Fin m)) :
    (∫ R, realifiedCoupledCofactorQuadratic R /
        (realifiedCofactorW R + δ) ^ 2
        ∂halfGaussianMatrixSum k (Fin m)) =
      (((k : ℝ) - 2 * m - 1)⁻¹) *
        ∫ R, realifiedCofactorW R /
          (realifiedCofactorW R + δ) ^ 2
          ∂halfGaussianMatrixSum k (Fin m) := by
  let b : ℝ := (k : ℝ) - 2 * m - 1
  let f : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ := fun R ↦
    realifiedCoupledCofactorQuadratic R /
      (realifiedCofactorW R + δ) ^ 2
  let h : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ := fun R ↦
    realifiedCofactorW R / (realifiedCofactorW R + δ) ^ 2
  have hbf : (∫ R, realifiedRegularizedCofactorWeight δ R *
        (b * realifiedCoupledCofactorQuadratic R)
        ∂halfGaussianMatrixSum k (Fin m)) =
      b * ∫ R, f R ∂halfGaussianMatrixSum k (Fin m) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with R
    dsimp [f, b]
    rw [← realifiedRegularizedWeight_mul_quadratic]
    ring
  have hright :
      (∫ R, realifiedRegularizedCofactorWeight δ R *
          realifiedCofactorW R
          ∂halfGaussianMatrixSum k (Fin m)) =
        ∫ R, h R ∂halfGaussianMatrixSum k (Fin m) := by
    apply integral_congr_ae
    filter_upwards [] with R
    exact realifiedRegularizedWeight_mul_W δ R
  have hmain : b * ∫ R, f R ∂halfGaussianMatrixSum k (Fin m) =
      ∫ R, h R ∂halfGaussianMatrixSum k (Fin m) := by
    rw [← hbf, ← hright]
    exact hscore
  change (∫ R, f R ∂halfGaussianMatrixSum k (Fin m)) =
    b⁻¹ * ∫ R, h R ∂halfGaussianMatrixSum k (Fin m)
  calc
    (∫ R, f R ∂halfGaussianMatrixSum k (Fin m)) =
        b⁻¹ * (b * ∫ R, f R ∂halfGaussianMatrixSum k (Fin m)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hcoeff, one_mul]
    _ = b⁻¹ * ∫ R, h R ∂halfGaussianMatrixSum k (Fin m) := by
      rw [hmain]

end Wishart

end

end LogdetLean.GramHafnian
