import LogdetLean.GeneralRNonlinearRemainder
import LogdetLean.GaussianPairLaplace
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic
namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Module WithLp
open scoped BigOperators MatrixOrder RealInnerProductSpace

namespace CorrelationMatrix

variable {p : ℕ}

def pairProjectionCLM (i j : Fin p) :
    Observation p →L[ℝ] Observation 2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun b : Fin 2 ↦
      if b = 0 then EuclideanSpace.proj i else EuclideanSpace.proj j))

@[simp] lemma pairProjectionCLM_apply_zero (i j : Fin p) (x : Observation p) :
    pairProjectionCLM i j x 0 = x i := by
  simp [pairProjectionCLM]

@[simp] lemma pairProjectionCLM_apply_one (i j : Fin p) (x : Observation p) :
    pairProjectionCLM i j x 1 = x j := by
  simp [pairProjectionCLM]

def pairCorrelationMatrix (rho : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, rho; rho, 1]

lemma pairCorrelationMatrix_posSemidef {rho : ℝ} (hrho : |rho| ≤ 1) :
    (pairCorrelationMatrix rho).PosSemidef := by
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    !![1, 0; rho, Real.sqrt (1 - rho ^ 2)]
  have hrho2 : rho ^ 2 ≤ 1 := by
    rw [abs_le] at hrho
    nlinarith [sq_nonneg (rho - 1), sq_nonneg (rho + 1)]
  rw [show pairCorrelationMatrix rho = A * Aᴴ by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [pairCorrelationMatrix, A, Matrix.mul_apply] ;
      nlinarith [Real.sq_sqrt (sub_nonneg.mpr hrho2)]]
  exact Matrix.posSemidef_self_mul_conjTranspose A

local instance isGaussian_gaussianMeasure (R : CorrelationMatrix p) :
    IsGaussian R.gaussianMeasure := by
  unfold gaussianMeasure
  infer_instance

lemma map_pairProjection_gaussianMeasure (R : CorrelationMatrix p)
    (i j : Fin p) :
    Measure.map (pairProjectionCLM i j) R.gaussianMeasure =
      multivariateGaussian 0 (pairCorrelationMatrix (R.val i j)) := by
  have hproj : (pairProjectionCLM i j : Observation p → Observation 2) =
      fun x ↦ WithLp.toLp 2
        (fun c : Fin 2 ↦ if c = 0 then x i else x j) := by
    funext x
    ext c
    fin_cases c <;> simp
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map]
    · simp
    · exact IsGaussian.integrable_id
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis fun a b ↦ ?_
    rw [ContinuousLinearMap.toBilinForm_apply,
      ContinuousLinearMap.toBilinForm_apply]
    rw [hproj]
    let X : Fin 2 → Observation p → ℝ := fun c x ↦
      if c = 0 then x i else x j
    have hmem : ∀ c, MemLp (X c) 2 R.gaussianMeasure := by
      intro c
      fin_cases c
      · simpa [X] using IsGaussian.memLp_two_id.continuousLinearMap_comp
          (EuclideanSpace.proj (𝕜 := ℝ) i)
      · simpa [X] using IsGaussian.memLp_two_id.continuousLinearMap_comp
          (EuclideanSpace.proj (𝕜 := ℝ) j)
    have hleft := covarianceBilin_apply_basisFun hmem a b
    have hsymm : R.val j i = R.val i j := by
      have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A i j)
        R.transpose_eq
      simpa using h
    calc
      covarianceBilin
          (R.gaussianMeasure.map (fun x ↦ WithLp.toLp 2
            (fun c : Fin 2 ↦ if c = 0 then x i else x j)))
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis a)
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis b) =
          cov[X a, X b; R.gaussianMeasure] := by
            simpa [X] using hleft
      _ = pairCorrelationMatrix (R.val i j) a b := by
        fin_cases a <;> fin_cases b <;>
          simp [X, pairCorrelationMatrix,
            CorrelationMatrix.covariance_eval, hsymm]
      _ = covarianceBilin
          (multivariateGaussian 0 (pairCorrelationMatrix (R.val i j)))
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis a)
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis b) := by
        rw [covarianceBilin_multivariateGaussian
          (pairCorrelationMatrix_posSemidef (R.abs_apply_le_one i j))]
        simp [dotProduct, Matrix.mulVec]

end CorrelationMatrix

theorem map_toEuclideanCLM_stdGaussian (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Measure.map (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
        (stdGaussian (EuclideanSpace ℝ (Fin 2))) =
      multivariateGaussian 0 (A * Aᴴ) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map]
    · simp
    · exact IsGaussian.integrable_id
  · ext x y
    have hadj :
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A).adjoint =
          Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ := by
      calc
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A).adjoint =
            star (Matrix.toEuclideanCLM (𝕜 := ℝ) A) :=
          (ContinuousLinearMap.star_eq_adjoint _).symm
        _ = Matrix.toEuclideanCLM (𝕜 := ℝ) (star A) :=
          (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ)) A).symm
        _ = Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ := rfl
    rw [covarianceBilin_map, covarianceBilin_stdGaussian,
      innerSL_apply_apply,
      covarianceBilin_multivariateGaussian
        (Matrix.posSemidef_self_mul_conjTranspose A),
      ContinuousLinearMap.adjoint_inner_left,
      hadj,
      ← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.mul_def, ← map_mul,
      Matrix.inner_toEuclideanCLM]
    exact IsGaussian.memLp_two_id

def canonicalCorrelationFactor (rho : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; rho, Real.sqrt (1 - rho ^ 2)]

def canonicalCorrelationCLM (rho : ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (canonicalCorrelationFactor rho)

@[simp] lemma canonicalCorrelationCLM_apply_zero (rho : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    canonicalCorrelationCLM rho x 0 = x 0 := by
  unfold canonicalCorrelationCLM
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [canonicalCorrelationFactor, Matrix.mulVec]
  rfl

@[simp] lemma canonicalCorrelationCLM_apply_one (rho : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    canonicalCorrelationCLM rho x 1 =
      rho * x 0 + Real.sqrt (1 - rho ^ 2) * x 1 := by
  unfold canonicalCorrelationCLM
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [canonicalCorrelationFactor, Matrix.mulVec]
  rfl

lemma map_canonicalCorrelation_stdGaussian {rho : ℝ} (hrho : |rho| ≤ 1) :
    Measure.map (canonicalCorrelationCLM rho)
        (stdGaussian (EuclideanSpace ℝ (Fin 2))) =
      multivariateGaussian 0 (CorrelationMatrix.pairCorrelationMatrix rho) := by
  rw [canonicalCorrelationCLM, map_toEuclideanCLM_stdGaussian]
  congr 1
  have hrho2 : rho ^ 2 ≤ 1 := by
    rw [abs_le] at hrho
    nlinarith [sq_nonneg (rho - 1), sq_nonneg (rho + 1)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [canonicalCorrelationFactor,
      CorrelationMatrix.pairCorrelationMatrix, Matrix.mul_apply] ;
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr hrho2)]

theorem integral_exp_pair_gaussianMeasure {p : ℕ}
    (R : CorrelationMatrix p) (i j : Fin p)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ x, Real.exp (-s * (x i) ^ 2 - t * (x j) ^ 2) ∂R.gaussianMeasure =
      (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * (R.val i j) ^ 2 * s * t))⁻¹ := by
  let rho := R.val i j
  let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun y ↦
    Real.exp (-s * (y 0) ^ 2 - t * (y 1) ^ 2)
  let h : ℝ × ℝ → ℝ := fun w ↦
    Real.exp (-s * w.1 ^ 2 -
      t * (rho * w.1 + Real.sqrt (1 - rho ^ 2) * w.2) ^ 2)
  have hrho : |rho| ≤ 1 := R.abs_apply_le_one i j
  have hproj : (fun x : CorrelationMatrix.Observation p ↦
      f (CorrelationMatrix.pairProjectionCLM i j x)) =
      (fun x ↦ Real.exp (-s * (x i) ^ 2 - t * (x j) ^ 2)) := by
    funext x
    simp [f]
  rw [← hproj]
  calc
    (∫ x, f (CorrelationMatrix.pairProjectionCLM i j x)
        ∂R.gaussianMeasure) =
        ∫ y, f y ∂multivariateGaussian 0
          (CorrelationMatrix.pairCorrelationMatrix rho) := by
      rw [← CorrelationMatrix.map_pairProjection_gaussianMeasure R i j]
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x, f (canonicalCorrelationCLM rho x)
        ∂stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
      rw [← map_canonicalCorrelation_stdGaussian hrho]
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ v : Fin 2 → ℝ,
        f (canonicalCorrelationCLM rho (WithLp.toLp 2 v))
        ∂Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1) := by
      rw [← map_pi_eq_stdGaussian]
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ w : ℝ × ℝ, h w
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have hmp := MeasureTheory.measurePreserving_finTwoArrow
        (gaussianReal 0 1)
      have hi := hmp.integral_comp' h
      rw [← hi]
      apply integral_congr_ae
      filter_upwards [] with v
      simp [f, h, rho]
    _ = (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * rho ^ 2 * s * t))⁻¹ := by
      exact integral_bivariate_correlated_sq_laplace_sqrt
        s t rho hs ht hrho

theorem integral_exp_pairNormSq_correlatedGaussianDataMeasure
    {m p : ℕ} (R : CorrelationMatrix p) (i j : Fin p)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ x : GaussianData m p,
        Real.exp (-s * (∑ k, (x k i) ^ 2) -
          t * (∑ k, (x k j) ^ 2))
        ∂correlatedGaussianDataMeasure m R =
      ((Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * (R.val i j) ^ 2 * s * t))⁻¹) ^ m := by
  have hpoint (x : GaussianData m p) :
      Real.exp (-s * (∑ k, (x k i) ^ 2) -
          t * (∑ k, (x k j) ^ 2)) =
        ∏ k, Real.exp (-s * (x k i) ^ 2 - t * (x k j) ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  unfold correlatedGaussianDataMeasure
  calc
    (∫ x : GaussianData m p,
        ∏ k, Real.exp (-s * (x k i) ^ 2 - t * (x k j) ^ 2)
        ∂Measure.pi (fun _ : Fin m ↦ R.gaussianMeasure)) =
      (∫ x : CorrelationMatrix.Observation p,
        Real.exp (-s * (x i) ^ 2 - t * (x j) ^ 2)
        ∂R.gaussianMeasure) ^ m := by
      simpa only [Fintype.card_fin] using
        (MeasureTheory.integral_fintype_prod_eq_pow (ι := Fin m)
          (μ := R.gaussianMeasure)
          (f := fun x : CorrelationMatrix.Observation p ↦
            Real.exp (-s * (x i) ^ 2 - t * (x j) ^ 2)))
    _ = ((Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * (R.val i j) ^ 2 * s * t))⁻¹) ^ m := by
      rw [integral_exp_pair_gaussianMeasure R i j s t hs ht]

namespace GeneralRDecomposition

theorem integral_exp_Q_pair_laplace {m p : ℕ}
    (R : CorrelationMatrix p) (i j : Fin p)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ z : GaussianData m p,
        Real.exp (-s * Q R z i - t * Q R z j)
        ∂standardGaussianDataMeasure m p =
      ((Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * (R.val i j) ^ 2 * s * t))⁻¹) ^ m := by
  let F : GaussianData m p → ℝ := fun x ↦
    Real.exp (-s * (∑ k, (x k i) ^ 2) -
      t * (∑ k, (x k j) ^ 2))
  have hQ (z : GaussianData m p) (a : Fin p) :
      Q R z a = ∑ k, (correlateRows R z k a) ^ 2 := by
    rw [Q, EuclideanSpace.real_norm_sq_eq]
    rfl
  calc
    (∫ z : GaussianData m p,
        Real.exp (-s * Q R z i - t * Q R z j)
        ∂standardGaussianDataMeasure m p) =
      ∫ z, F (correlateRows R z)
        ∂standardGaussianDataMeasure m p := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [F, hQ]
    _ = ∫ x, F x ∂correlatedGaussianDataMeasure m R := by
      rw [← map_correlateRows_standardGaussianDataMeasure R]
      rw [integral_map (measurable_correlateRows R).aemeasurable
        (by fun_prop)]
    _ = ((Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * (R.val i j) ^ 2 * s * t))⁻¹) ^ m := by
      exact integral_exp_pairNormSq_correlatedGaussianDataMeasure
        R i j s t hs ht

end GeneralRDecomposition

end
end LogdetLean
