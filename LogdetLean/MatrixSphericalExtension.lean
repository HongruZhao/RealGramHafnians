import LogdetLean.CenteredGaussianSample
import LogdetLean.GaussianColumnProduct
import LogdetLean.GaussianSampleCorrelation
import LogdetLean.GaussianSphereDirection
import LogdetLean.NormalizedGramScaling
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
/-!
# Matrix-spherical extension of the Gaussian Pearson law

This file formalizes Corollary 3.4 of Hongru Zhao,
"On the Log Determinant of Sample Correlation Matrices under Gaussianity",
arXiv:2608.00565v1 (2026), printed p. 8.

The paper uses the Gaussian polar decomposition `G = rho U`: `U` is uniform
on the Frobenius unit sphere and independent of the positive radial variable
`rho`.  For the Pearson matrix, the radial distribution is immaterial.  We
therefore use the equivalent canonical construction of the uniform direction
as the pushforward of an iid Gaussian matrix by Frobenius normalization, and
prove directly that every common positive radius and every location vector
cancel after empirical centering and Pearson normalization.

No spherical-distribution theorem is postulated.  `GaussianSphereDirection`
derives from Mathlib's polar decomposition that the finite Gaussian
pushforward used below is literally normalized Haar surface measure on the
Frobenius unit sphere.  All measurability statements and cancellation
arguments are proved below.  The comparison with the usual `n-1`
residual-coordinate Gaussian model is proved in the second half of the file.
-/

namespace LogdetLean

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set WithLp Matrix
open scoped BigOperators MatrixOrder RealInnerProductSpace

/-! ## Raw observations, Frobenius radius, and direction -/

theorem measurable_scaleGaussianData {n p : ℕ} (c : ℝ) :
    Measurable (scaleGaussianData c : GaussianData n p → GaussianData n p) := by
  unfold scaleGaussianData
  fun_prop

/-- The Frobenius squared norm of a finite data matrix. -/
def frobeniusNormSqData {n p : ℕ} (x : GaussianData n p) : ℝ :=
  ∑ k, ‖x k‖ ^ 2

/-- The Frobenius norm of a finite data matrix. -/
def frobeniusNormData {n p : ℕ} (x : GaussianData n p) : ℝ :=
  Real.sqrt (frobeniusNormSqData x)

theorem measurable_frobeniusNormSqData {n p : ℕ} :
    Measurable (frobeniusNormSqData : GaussianData n p → ℝ) := by
  unfold frobeniusNormSqData
  exact Finset.measurable_sum _ fun k _ ↦
    ((measurable_pi_apply k).norm.pow_const 2)

theorem measurable_frobeniusNormData {n p : ℕ} :
    Measurable (frobeniusNormData : GaussianData n p → ℝ) := by
  exact measurable_frobeniusNormSqData.sqrt

theorem frobeniusNormSqData_nonneg {n p : ℕ} (x : GaussianData n p) :
    0 ≤ frobeniusNormSqData x := by
  unfold frobeniusNormSqData
  positivity

theorem frobeniusNormData_nonneg {n p : ℕ} (x : GaussianData n p) :
    0 ≤ frobeniusNormData x := by
  exact Real.sqrt_nonneg _

/-- Frobenius direction, totalized at radius zero.  The zero-radius branch is
kept unchanged; it is a null event under the Gaussian law and, more
importantly, makes every scale-invariance identity pointwise rather than only
almost sure. -/
def frobeniusDirectionData {n p : ℕ} (x : GaussianData n p) :
    GaussianData n p :=
  if frobeniusNormData x = 0 then x
  else scaleGaussianData (frobeniusNormData x)⁻¹ x

theorem measurable_frobeniusDirectionData {n p : ℕ} :
    Measurable (frobeniusDirectionData : GaussianData n p → GaussianData n p) := by
  unfold frobeniusDirectionData
  apply Measurable.ite
  · exact measurable_frobeniusNormData (measurableSet_singleton 0)
  · exact measurable_id
  · unfold scaleGaussianData
    refine measurable_pi_lambda _ fun k ↦ ?_
    exact measurable_frobeniusNormData.inv.smul (measurable_pi_apply k)

/-- Canonical uniform law on the Frobenius sphere: normalize a finite iid
standard Gaussian matrix by its common Frobenius radius.  This is the usual
Gaussian polar construction of surface-uniform direction. -/
def frobeniusUniformDirectionLaw (n p : ℕ) : Measure (GaussianData n p) :=
  Measure.map frobeniusDirectionData (standardGaussianDataMeasure n p)

instance frobeniusUniformDirectionLaw_isProbability (n p : ℕ) :
    IsProbabilityMeasure (frobeniusUniformDirectionLaw n p) := by
  unfold frobeniusUniformDirectionLaw
  exact Measure.isProbabilityMeasure_map
    measurable_frobeniusDirectionData.aemeasurable

/-- The elementary row-wise definition of Frobenius direction agrees
pointwise with normalization in the genuine Euclidean space of all matrix
entries. -/
theorem frobeniusDirectionData_eq_frobeniusSurfaceDirection
    (n p : ℕ) (x : GaussianData n p) :
    frobeniusDirectionData x = frobeniusSurfaceDirection n p x := by
  have hnorm : frobeniusNormData x = ‖flattenGaussianData n p x‖ := by
    unfold frobeniusNormData frobeniusNormSqData
    rw [← norm_sq_flattenGaussianData]
    exact Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg (norm_nonneg _))
  unfold frobeniusDirectionData frobeniusSurfaceDirection unitDirection
  by_cases hx : flattenGaussianData n p x = 0
  · have hx' : x = 0 := by
      ext k i
      have hentry := congrArg
        (fun y : EuclideanSpace ℝ (Fin n × Fin p) ↦ y (k, i)) hx
      exact hentry
    have hfnorm : frobeniusNormData x = 0 := by
      rw [hnorm, norm_eq_zero.mpr hx]
    rw [if_pos hfnorm, if_pos hx, hx']
    ext k i
    rfl
  · have hnorm_ne : ‖flattenGaussianData n p x‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hx
    have hfnorm : frobeniusNormData x ≠ 0 := by simpa [hnorm]
    rw [if_neg hfnorm, if_neg hx, hnorm]
    ext k i
    rfl

/-- The Gaussian-normalized direction law used in the cancellation proof is
exactly the literal normalized Haar surface law, not merely an invariant-law
surrogate. -/
theorem frobeniusUniformDirectionLaw_eq_surfaceLaw
    (n p : ℕ) [Nonempty (Fin n × Fin p)] :
    frobeniusUniformDirectionLaw n p = frobeniusSurfaceDirectionLaw n p := by
  unfold frobeniusUniformDirectionLaw
  rw [show (@frobeniusDirectionData n p) =
      frobeniusSurfaceDirection n p by
    funext x
    exact frobeniusDirectionData_eq_frobeniusSurfaceDirection n p x]
  exact map_frobeniusSurfaceDirection_eq_surfaceLaw n p

/-! ## Empirical centering and the raw Pearson matrix -/

/-- Empirically center every variable column of a raw `n`-observation data
matrix. -/
def centerGaussianData {n p : ℕ} (x : GaussianData n p) : GaussianData n p :=
  fun k ↦ WithLp.toLp 2 (fun i ↦ centerVector (dataColumn x i) k)

@[simp]
theorem centerGaussianData_apply {n p : ℕ} (x : GaussianData n p)
    (k : Fin n) (i : Fin p) :
    centerGaussianData x k i = centerVector (dataColumn x i) k := rfl

theorem measurable_centerGaussianData {n p : ℕ} :
    Measurable (centerGaussianData : GaussianData n p → GaussianData n p) := by
  unfold centerGaussianData centerVector sampleMean dataColumn
  fun_prop

@[simp]
theorem dataColumn_centerGaussianData {n p : ℕ} (x : GaussianData n p)
    (i : Fin p) :
    dataColumn (centerGaussianData x) i = centerVector (dataColumn x i) := by
  ext k
  rfl

/-- Pearson sample correlation matrix formed from raw observations by
empirical centering and column normalization. -/
def rawPearsonMatrix {n p : ℕ} (x : GaussianData n p) :
    Matrix (Fin p) (Fin p) ℝ :=
  sampleCorrelationMatrix (centerGaussianData x)

theorem measurable_rawPearsonMatrix {n p : ℕ} :
    Measurable (rawPearsonMatrix : GaussianData n p →
      Matrix (Fin p) (Fin p) ℝ) := by
  unfold rawPearsonMatrix sampleCorrelationMatrix normalizedGram Matrix.gram
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  have hcols : Measurable (fun x : GaussianData n p ↦
      dataColumns (centerGaussianData x)) :=
    measurable_dataColumns.comp measurable_centerGaussianData
  have hi : Measurable (fun x : GaussianData n p ↦
      dataColumns (centerGaussianData x) i) :=
    (measurable_pi_apply i).comp hcols
  have hj : Measurable (fun x : GaussianData n p ↦
      dataColumns (centerGaussianData x) j) :=
    (measurable_pi_apply j).comp hcols
  unfold normalizeVector
  exact Measurable.inner (hi.norm.inv.smul hi) (hj.norm.inv.smul hj)

theorem rawPearsonMatrix_eq_normalizedGram_centeredColumns
    {n p : ℕ} (x : GaussianData n p) :
    rawPearsonMatrix x =
      normalizedGram (fun i ↦ centerVector (dataColumn x i)) := by
  unfold rawPearsonMatrix sampleCorrelationMatrix dataColumns
  congr 1

/-- Add the same deterministic population-location vector to every
observation row. -/
def addLocationData {n p : ℕ} (mu : CorrelationMatrix.Observation p)
    (x : GaussianData n p) : GaussianData n p :=
  fun k ↦ mu + x k

@[simp]
theorem addLocationData_apply {n p : ℕ}
    (mu : CorrelationMatrix.Observation p) (x : GaussianData n p)
    (k : Fin n) (i : Fin p) :
    addLocationData mu x k i = mu i + x k i := rfl

theorem measurable_addLocationData {n p : ℕ}
    (mu : CorrelationMatrix.Observation p) :
    Measurable (addLocationData mu : GaussianData n p → GaussianData n p) := by
  unfold addLocationData
  fun_prop

theorem sampleMean_dataColumn_addLocationData {n p : ℕ} (hn : 0 < n)
    (mu : CorrelationMatrix.Observation p) (x : GaussianData n p)
    (i : Fin p) :
    sampleMean (dataColumn (addLocationData mu x) i) =
      mu i + sampleMean (dataColumn x i) := by
  unfold sampleMean
  simp only [dataColumn_apply, addLocationData_apply, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]

theorem centerGaussianData_addLocationData {n p : ℕ} (hn : 0 < n)
    (mu : CorrelationMatrix.Observation p) (x : GaussianData n p) :
    centerGaussianData (addLocationData mu x) = centerGaussianData x := by
  ext k i
  simp only [centerGaussianData_apply, centerVector_apply,
    dataColumn_apply, addLocationData_apply,
    sampleMean_dataColumn_addLocationData hn mu x i]
  ring

theorem rawPearsonMatrix_addLocationData {n p : ℕ} (hn : 0 < n)
    (mu : CorrelationMatrix.Observation p) (x : GaussianData n p) :
    rawPearsonMatrix (addLocationData mu x) = rawPearsonMatrix x := by
  unfold rawPearsonMatrix
  rw [centerGaussianData_addLocationData hn mu x]

/-- Empirical centering commutes with a common scalar. -/
theorem centerGaussianData_scaleGaussianData {n p : ℕ}
    (c : ℝ) (x : GaussianData n p) :
    centerGaussianData (scaleGaussianData c x) =
      scaleGaussianData c (centerGaussianData x) := by
  ext k i
  have hmean :
      sampleMean (dataColumn (scaleGaussianData c x) i) =
        c * sampleMean (dataColumn x i) := by
    rw [dataColumn_scaleGaussianData]
    unfold sampleMean
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  simp only [centerGaussianData_apply, centerVector_apply,
    dataColumn_apply, scaleGaussianData_apply, hmean]
  ring

/-- The covariance square-root map commutes with a common scalar. -/
theorem correlateRows_scaleGaussianData {n p : ℕ}
    (R : CorrelationMatrix p) (c : ℝ) (x : GaussianData n p) :
    correlateRows R (scaleGaussianData c x) =
      scaleGaussianData c (correlateRows R x) := by
  ext k i
  unfold correlateRows CorrelationMatrix.correlateObservation
  change (toEuclideanCLM (𝕜 := ℝ) R.covarianceSqrt (c • x k)) i =
    (c • toEuclideanCLM (𝕜 := ℝ) R.covarianceSqrt (x k)) i
  rw [map_smul]

/-- A raw Pearson matrix is invariant under a common positive scale. -/
theorem rawPearsonMatrix_scaleGaussianData_of_pos {n p : ℕ}
    (c : ℝ) (hc : 0 < c) (x : GaussianData n p) :
    rawPearsonMatrix (scaleGaussianData c x) = rawPearsonMatrix x := by
  unfold rawPearsonMatrix
  rw [centerGaussianData_scaleGaussianData,
    sampleCorrelationMatrix_scaleGaussianData_of_pos c hc]

/-! ## Cancellation of positive variablewise population scales -/

/-- Multiply variable `i` by its own deterministic scale `s i`. -/
def scaleVariableData {n p : ℕ} (s : Fin p → ℝ)
    (x : GaussianData n p) : GaussianData n p :=
  fun k ↦ WithLp.toLp 2 (fun i ↦ s i * x k i)

@[simp]
theorem scaleVariableData_apply {n p : ℕ} (s : Fin p → ℝ)
    (x : GaussianData n p) (k : Fin n) (i : Fin p) :
    scaleVariableData s x k i = s i * x k i := rfl

theorem measurable_scaleVariableData {n p : ℕ} (s : Fin p → ℝ) :
    Measurable (scaleVariableData s : GaussianData n p → GaussianData n p) := by
  unfold scaleVariableData
  fun_prop

theorem dataColumn_scaleVariableData {n p : ℕ} (s : Fin p → ℝ)
    (x : GaussianData n p) (i : Fin p) :
    dataColumn (scaleVariableData s x) i = s i • dataColumn x i := by
  ext k
  rfl

theorem centerVector_smul (n : ℕ) (c : ℝ) (v : ObservationSpace n) :
    centerVector (c • v) = c • centerVector v := by
  ext k
  unfold centerVector sampleMean
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem centerGaussianData_scaleVariableData {n p : ℕ}
    (s : Fin p → ℝ) (x : GaussianData n p) :
    centerGaussianData (scaleVariableData s x) =
      scaleVariableData s (centerGaussianData x) := by
  ext k i
  change centerVector (dataColumn (scaleVariableData s x) i) k =
    s i * centerVector (dataColumn x i) k
  rw [dataColumn_scaleVariableData, centerVector_smul]
  rfl

/-- Normalized Gram matrices cancel a separate positive scale in every
column. -/
theorem normalizedGram_variable_smul_of_pos
    {p : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (v : Fin p → E) :
    normalizedGram (fun i ↦ s i • v i) = normalizedGram v := by
  unfold normalizedGram
  congr 1
  funext i
  exact normalizeVector_smul_of_pos (s i) (hs i) (v i)

/-- Pearson correlation is invariant under arbitrary positive marginal
standard deviations. -/
theorem rawPearsonMatrix_scaleVariableData_of_pos {n p : ℕ}
    (s : Fin p → ℝ) (hs : ∀ i, 0 < s i) (x : GaussianData n p) :
    rawPearsonMatrix (scaleVariableData s x) = rawPearsonMatrix x := by
  unfold rawPearsonMatrix sampleCorrelationMatrix dataColumns
  rw [centerGaussianData_scaleVariableData]
  rw [show (fun i ↦ dataColumn (scaleVariableData s (centerGaussianData x)) i) =
      fun i ↦ s i • dataColumn (centerGaussianData x) i by
    funext i
    exact dataColumn_scaleVariableData s (centerGaussianData x) i]
  exact normalizedGram_variable_smul_of_pos
    (E := ObservationSpace n) s hs
      (fun i ↦ dataColumn (centerGaussianData x) i)

/-! ## Arbitrary positive-definite population covariance -/

/-- A positive-definite covariance matrix, without the unit-diagonal
restriction imposed by `CorrelationMatrix`. -/
structure CovarianceMatrix (p : ℕ) where
  val : Matrix (Fin p) (Fin p) ℝ
  posDef : val.PosDef

namespace CovarianceMatrix

variable {p : ℕ} (Sigma : CovarianceMatrix p)

/-- Population marginal standard deviations. -/
def stdDev (i : Fin p) : ℝ := Real.sqrt (Sigma.val i i)

theorem diag_pos (i : Fin p) : 0 < Sigma.val i i := by
  simpa using Sigma.posDef.2
    (x := Finsupp.single i 1) (by simp)

theorem stdDev_pos (i : Fin p) : 0 < Sigma.stdDev i := by
  exact Real.sqrt_pos.2 (Sigma.diag_pos i)

/-- The population correlation obtained by standardizing every marginal. -/
def correlation : CorrelationMatrix p where
  val := Matrix.diagonal (fun i ↦ (Sigma.stdDev i)⁻¹) * Sigma.val *
    Matrix.diagonal (fun i ↦ (Sigma.stdDev i)⁻¹)
  posDef := by
    let D : Matrix (Fin p) (Fin p) ℝ :=
      Matrix.diagonal (fun i ↦ (Sigma.stdDev i)⁻¹)
    have hD : IsUnit D := Matrix.isUnit_diagonal.mpr
      (Pi.isUnit_iff.mpr fun i ↦
        isUnit_iff_ne_zero.mpr (inv_ne_zero (Sigma.stdDev_pos i).ne'))
    have hpd : (star D * Sigma.val * D).PosDef :=
      hD.posDef_star_left_conjugate_iff.mpr Sigma.posDef
    have hstar : star D = D := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D]
      · simp [D, hij, Ne.symm hij]
    simpa [D, hstar] using hpd
  diag_one := by
    intro i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hsquare : (Sigma.stdDev i) ^ 2 = Sigma.val i i := by
      unfold stdDev
      exact Real.sq_sqrt (Sigma.diag_pos i).le
    have hsne : Sigma.stdDev i ≠ 0 := (Sigma.stdDev_pos i).ne'
    rw [← hsquare]
    field_simp [hsne]

@[simp]
theorem correlation_val : Sigma.correlation.val =
    Matrix.diagonal (fun i ↦ (Sigma.stdDev i)⁻¹) * Sigma.val *
      Matrix.diagonal (fun i ↦ (Sigma.stdDev i)⁻¹) := rfl

/-- Centered Gaussian law with arbitrary covariance `Sigma`. -/
def gaussianMeasure : Measure (ObservationSpace p) :=
  multivariateGaussian 0 Sigma.val

instance gaussianMeasure_isProbability : IsProbabilityMeasure Sigma.gaussianMeasure := by
  unfold gaussianMeasure
  infer_instance

instance gaussianMeasure_isGaussian : IsGaussian Sigma.gaussianMeasure := by
  unfold gaussianMeasure
  infer_instance

/-- Positive symmetric covariance square root. -/
def covarianceSqrt : Matrix (Fin p) (Fin p) ℝ := CFC.sqrt Sigma.val

/-- Apply the symmetric covariance square root to a standard observation. -/
def correlateObservation (z : ObservationSpace p) : ObservationSpace p :=
  toEuclideanCLM (𝕜 := ℝ) Sigma.covarianceSqrt z

theorem measurable_correlateObservation :
    Measurable Sigma.correlateObservation := by
  unfold correlateObservation
  fun_prop

theorem map_correlateObservation_stdGaussian :
    Measure.map Sigma.correlateObservation
        (stdGaussian (ObservationSpace p)) = Sigma.gaussianMeasure := by
  unfold correlateObservation covarianceSqrt gaussianMeasure
  simp [multivariateGaussian]

/-- Population standardization as a continuous diagonal linear map. -/
def standardizeObservation : ObservationSpace p →L[ℝ] ObservationSpace p :=
  toEuclideanCLM (𝕜 := ℝ)
    (Matrix.diagonal fun i ↦ (Sigma.stdDev i)⁻¹)

@[simp]
theorem standardizeObservation_apply (x : ObservationSpace p) (i : Fin p) :
    Sigma.standardizeObservation x i = (Sigma.stdDev i)⁻¹ * x i := by
  unfold standardizeObservation
  change (∑ j, Matrix.diagonal (fun i ↦ (Sigma.stdDev i)⁻¹) i j * x j) = _
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Standardizing a Gaussian vector with covariance `Sigma` gives exactly
the Gaussian law with population correlation `correlation Sigma`. -/
theorem map_standardizeObservation_gaussianMeasure :
    Measure.map Sigma.standardizeObservation Sigma.gaussianMeasure =
      Sigma.correlation.gaussianMeasure := by
  let D : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.diagonal (fun i ↦ (Sigma.stdDev i)⁻¹)
  let L : ObservationSpace p →L[ℝ] ObservationSpace p :=
    toEuclideanCLM (𝕜 := ℝ) D
  letI : IsGaussian Sigma.correlation.gaussianMeasure := by
    unfold CorrelationMatrix.gaussianMeasure
    infer_instance
  letI : IsGaussian (Measure.map L Sigma.gaussianMeasure) :=
    ProbabilityTheory.isGaussian_map L
  have hDself : IsSelfAdjoint D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij, Ne.symm hij]
  have hLself : IsSelfAdjoint L := hDself.map _
  have hmean :
      (∫ x, id x ∂Measure.map L Sigma.gaussianMeasure) =
        ∫ x, id x ∂Sigma.correlation.gaussianMeasure := by
    rw [integral_map L.continuous.aemeasurable
      IsGaussian.integrable_id.aestronglyMeasurable]
    change (∫ x, L x ∂Sigma.gaussianMeasure) = _
    have hInt := L.integral_comp_comm
      (φ := id) (IsGaussian.integrable_id (μ := Sigma.gaussianMeasure))
    change (∫ x, L x ∂Sigma.gaussianMeasure) =
      L (∫ x, x ∂Sigma.gaussianMeasure) at hInt
    rw [hInt]
    simp [CovarianceMatrix.gaussianMeasure, CorrelationMatrix.gaussianMeasure]
  have hcov :
      covarianceBilin (Measure.map L Sigma.gaussianMeasure) =
        covarianceBilin Sigma.correlation.gaussianMeasure := by
    ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id]
    rw [hLself.adjoint_eq]
    unfold CovarianceMatrix.gaussianMeasure
    rw [covarianceBilin_multivariateGaussian Sigma.posDef.posSemidef]
    change (L u).ofLp ⬝ᵥ Sigma.val *ᵥ (L v).ofLp =
      ((covarianceBilin
        (multivariateGaussian 0 Sigma.correlation.val)) u) v
    rw [covarianceBilin_multivariateGaussian
      Sigma.correlation.posSemidef]
    change (D *ᵥ u) ⬝ᵥ Sigma.val *ᵥ (D *ᵥ v) =
      u ⬝ᵥ Sigma.correlation.val *ᵥ v
    rw [Sigma.correlation_val]
    simp only [← Matrix.mulVec_mulVec]
    have hDmulVec (w : Fin p → ℝ) : D *ᵥ w =
        fun i ↦ (Sigma.stdDev i)⁻¹ * w i := by
      funext i
      simp [D, Matrix.mulVec]
    rw [hDmulVec u, hDmulVec v,
      hDmulVec (Sigma.val *ᵥ fun i ↦ (Sigma.stdDev i)⁻¹ * v i)]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change Measure.map L Sigma.gaussianMeasure =
    Sigma.correlation.gaussianMeasure
  exact IsGaussian.ext hmean hcov

end CovarianceMatrix

/-- Apply an arbitrary covariance square root independently to every row. -/
def correlateRowsCovariance {n p : ℕ} (Sigma : CovarianceMatrix p)
    (z : GaussianData n p) : GaussianData n p :=
  fun k ↦ Sigma.correlateObservation (z k)

theorem measurable_correlateRowsCovariance {n p : ℕ}
    (Sigma : CovarianceMatrix p) :
    Measurable (correlateRowsCovariance (n := n) Sigma) := by
  unfold correlateRowsCovariance
  refine measurable_pi_lambda _ fun k ↦ ?_
  exact Sigma.measurable_correlateObservation.comp (measurable_pi_apply k)

theorem correlateRowsCovariance_scaleGaussianData {n p : ℕ}
    (Sigma : CovarianceMatrix p) (c : ℝ) (x : GaussianData n p) :
    correlateRowsCovariance Sigma (scaleGaussianData c x) =
      scaleGaussianData c (correlateRowsCovariance Sigma x) := by
  ext k i
  unfold correlateRowsCovariance CovarianceMatrix.correlateObservation
  change (toEuclideanCLM (𝕜 := ℝ) Sigma.covarianceSqrt (c • x k)) i =
    (c • toEuclideanCLM (𝕜 := ℝ) Sigma.covarianceSqrt (x k)) i
  rw [map_smul]

/-- Product Gaussian data law with arbitrary covariance. -/
def covarianceGaussianDataMeasure {p : ℕ} (n : ℕ)
    (Sigma : CovarianceMatrix p) : Measure (GaussianData n p) :=
  Measure.pi fun _ : Fin n ↦ Sigma.gaussianMeasure

instance covarianceGaussianDataMeasure_isProbability {p : ℕ} (n : ℕ)
    (Sigma : CovarianceMatrix p) :
    IsProbabilityMeasure (covarianceGaussianDataMeasure n Sigma) := by
  unfold covarianceGaussianDataMeasure
  infer_instance

theorem map_correlateRowsCovariance_standardGaussianDataMeasure
    {n p : ℕ} (Sigma : CovarianceMatrix p) :
    Measure.map (correlateRowsCovariance (n := n) Sigma)
        (standardGaussianDataMeasure n p) =
      covarianceGaussianDataMeasure n Sigma := by
  let _ (k : Fin n) : IsProbabilityMeasure
      ((stdGaussian (ObservationSpace p)).map Sigma.correlateObservation) :=
    Measure.isProbabilityMeasure_map
      Sigma.measurable_correlateObservation.aemeasurable
  change Measure.map
      (fun z : GaussianData n p ↦ fun k ↦ Sigma.correlateObservation (z k))
      (Measure.pi fun _ : Fin n ↦ stdGaussian (ObservationSpace p)) =
    Measure.pi fun _ : Fin n ↦ Sigma.gaussianMeasure
  rw [Measure.pi_map_pi
    (fun _ ↦ Sigma.measurable_correlateObservation.aemeasurable)]
  congr 1
  funext k
  exact Sigma.map_correlateObservation_stdGaussian

theorem scaleVariableData_invStdDev_eq_standardizeRows
    {n p : ℕ} (Sigma : CovarianceMatrix p) (x : GaussianData n p) :
    scaleVariableData (fun i ↦ (Sigma.stdDev i)⁻¹) x =
      fun k ↦ Sigma.standardizeObservation (x k) := by
  ext k i
  exact Sigma.standardizeObservation_apply (x k) i |>.symm

/-- At the product-data level, population standardization changes arbitrary
covariance `Sigma` into its population correlation matrix. -/
theorem map_scaleVariableData_invStdDev_covarianceGaussianDataMeasure
    {n p : ℕ} (Sigma : CovarianceMatrix p) :
    Measure.map (scaleVariableData (n := n)
        (fun i ↦ (Sigma.stdDev i)⁻¹))
        (covarianceGaussianDataMeasure n Sigma) =
      correlatedGaussianDataMeasure n Sigma.correlation := by
  let _ (k : Fin n) : IsProbabilityMeasure
      (Measure.map Sigma.standardizeObservation Sigma.gaussianMeasure) :=
    Measure.isProbabilityMeasure_map
      Sigma.standardizeObservation.continuous.measurable.aemeasurable
  rw [show scaleVariableData (n := n) (fun i ↦ (Sigma.stdDev i)⁻¹) =
      (fun x : GaussianData n p ↦
        fun k ↦ Sigma.standardizeObservation (x k)) by
    funext x
    exact scaleVariableData_invStdDev_eq_standardizeRows Sigma x]
  unfold covarianceGaussianDataMeasure correlatedGaussianDataMeasure
  rw [Measure.pi_map_pi (fun _ ↦
    Sigma.standardizeObservation.continuous.measurable.aemeasurable)]
  congr 1
  funext k
  exact Sigma.map_standardizeObservation_gaussianMeasure

/-- Exact Pearson-law reduction from arbitrary covariance to its correlation
matrix.  This proves, rather than assumes, that marginal standard deviations
are irrelevant. -/
theorem map_rawPearson_covarianceGaussianDataMeasure_eq_correlation
    {n p : ℕ} (Sigma : CovarianceMatrix p) :
    Measure.map rawPearsonMatrix (covarianceGaussianDataMeasure n Sigma) =
      Measure.map rawPearsonMatrix
        (correlatedGaussianDataMeasure n Sigma.correlation) := by
  let s : Fin p → ℝ := fun i ↦ (Sigma.stdDev i)⁻¹
  have hs : ∀ i, 0 < s i := fun i ↦ inv_pos.mpr (Sigma.stdDev_pos i)
  calc
    Measure.map rawPearsonMatrix (covarianceGaussianDataMeasure n Sigma) =
        Measure.map (rawPearsonMatrix ∘ scaleVariableData s)
          (covarianceGaussianDataMeasure n Sigma) := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact (rawPearsonMatrix_scaleVariableData_of_pos s hs x).symm
    _ = Measure.map rawPearsonMatrix
        (Measure.map (scaleVariableData s)
          (covarianceGaussianDataMeasure n Sigma)) := by
      rw [Measure.map_map measurable_rawPearsonMatrix
        (measurable_scaleVariableData s)]
    _ = Measure.map rawPearsonMatrix
        (correlatedGaussianDataMeasure n Sigma.correlation) := by
      rw [map_scaleVariableData_invStdDev_covarianceGaussianDataMeasure]

/-! ## Matrix-spherical data with an arbitrary independent positive radius -/

/-- Raw matrix-spherical observations
`Y = mu 1^T + T R^(1/2) U`, in row orientation.  The radius is represented by
the subtype `Ioi 0`, so positivity is part of its type. -/
def matrixSphericalData {n p : ℕ}
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p)
    (q : Ioi (0 : ℝ) × GaussianData n p) : GaussianData n p :=
  addLocationData mu
    (scaleGaussianData q.1.1 (correlateRows R q.2))

theorem measurable_matrixSphericalData {n p : ℕ}
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    Measurable (matrixSphericalData mu R :
      Ioi (0 : ℝ) × GaussianData n p → GaussianData n p) := by
  unfold matrixSphericalData
  apply (measurable_addLocationData mu).comp
  unfold scaleGaussianData
  refine measurable_pi_lambda _ fun k ↦ ?_
  have hradius : Measurable (fun q : Ioi (0 : ℝ) × GaussianData n p ↦
      (q.1.1 : ℝ)) := measurable_subtype_coe.comp measurable_fst
  have hcorr : Measurable (fun q : Ioi (0 : ℝ) × GaussianData n p ↦
      correlateRows R q.2 k) :=
    (R.measurable_correlateObservation.comp
      ((measurable_pi_apply k).comp measurable_snd))
  exact hradius.smul hcorr

/-- The exact Pearson-matrix law of the matrix-spherical model. -/
def matrixSphericalPearsonLaw {p : ℕ} (n : ℕ)
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p)
    (radiusLaw : Measure (Ioi (0 : ℝ))) :
    Measure (Matrix (Fin p) (Fin p) ℝ) :=
  Measure.map (rawPearsonMatrix ∘ matrixSphericalData mu R)
    (radiusLaw.prod (frobeniusUniformDirectionLaw n p))

instance matrixSphericalPearsonLaw_isProbability {p : ℕ} (n : ℕ)
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p)
    (radiusLaw : Measure (Ioi (0 : ℝ))) [IsProbabilityMeasure radiusLaw] :
    IsProbabilityMeasure
      (matrixSphericalPearsonLaw n mu R radiusLaw) := by
  unfold matrixSphericalPearsonLaw
  exact Measure.isProbabilityMeasure_map
    ((measurable_rawPearsonMatrix.comp
      (measurable_matrixSphericalData mu R)).aemeasurable)

/-! ## Exact cancellation of the polar radius -/

/-- Pointwise cancellation behind the matrix-spherical extension.  The
outer radius `t` and the Gaussian Frobenius radius both disappear from the
Pearson matrix. -/
theorem rawPearsonMatrix_matrixSphericalData_direction
    {n p : ℕ} (hn : 0 < n)
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p)
    (q : Ioi (0 : ℝ) × GaussianData n p) :
    rawPearsonMatrix
        (matrixSphericalData mu R (q.1, frobeniusDirectionData q.2)) =
      rawPearsonMatrix (correlateRows R q.2) := by
  unfold matrixSphericalData
  rw [rawPearsonMatrix_addLocationData hn]
  rw [rawPearsonMatrix_scaleGaussianData_of_pos q.1.1 q.1.2]
  unfold frobeniusDirectionData
  split_ifs with hzero
  · rfl
  · rw [correlateRows_scaleGaussianData]
    apply rawPearsonMatrix_scaleGaussianData_of_pos
    exact inv_pos.mpr (lt_of_le_of_ne
      (frobeniusNormData_nonneg q.2) (Ne.symm hzero))

/-- Exact matrix-level law in Corollary 3.4: for every independent positive
radius law and every location vector, the Pearson matrix has exactly the same
law as the Pearson matrix built from correlated iid standard Gaussian raw
observations. -/
theorem matrixSphericalPearsonLaw_eq_gaussianRawPearsonLaw
    {n p : ℕ} (hn : 0 < n)
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p)
    (radiusLaw : Measure (Ioi (0 : ℝ))) [IsProbabilityMeasure radiusLaw] :
    matrixSphericalPearsonLaw n mu R radiusLaw =
      Measure.map (rawPearsonMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure n p) := by
  unfold matrixSphericalPearsonLaw frobeniusUniformDirectionLaw
  have hid : Measure.map (id : Ioi (0 : ℝ) → Ioi (0 : ℝ)) radiusLaw =
      radiusLaw := Measure.map_id
  rw [← hid]
  rw [Measure.map_prod_map radiusLaw (standardGaussianDataMeasure n p)
    measurable_id measurable_frobeniusDirectionData]
  rw [Measure.map_map
    (measurable_rawPearsonMatrix.comp
      (measurable_matrixSphericalData mu R))
    (measurable_id.prodMap measurable_frobeniusDirectionData)]
  have hfun :
      ((@rawPearsonMatrix n p ∘ matrixSphericalData mu R) ∘
          Prod.map id (@frobeniusDirectionData n p)) =
        ((@rawPearsonMatrix n p ∘ correlateRows (m := n) R) ∘
          (Prod.snd : Ioi (0 : ℝ) × GaussianData n p → GaussianData n p)) := by
    funext q
    exact rawPearsonMatrix_matrixSphericalData_direction hn mu R q
  rw [hfun, ← Measure.map_map
    (measurable_rawPearsonMatrix.comp (measurable_correlateRows R))
    measurable_snd]
  rw [measurePreserving_snd.map_eq]

/-! ## The paper's arbitrary-covariance matrix-spherical model -/

/-- Raw matrix-spherical observations with an arbitrary positive-definite
population covariance:
`Y = mu 1^T + T Sigma^(1/2) U`, in row orientation. -/
def matrixSphericalCovarianceData {n p : ℕ}
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p)
    (q : Ioi (0 : ℝ) × GaussianData n p) : GaussianData n p :=
  addLocationData mu
    (scaleGaussianData q.1.1 (correlateRowsCovariance Sigma q.2))

theorem measurable_matrixSphericalCovarianceData {n p : ℕ}
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    Measurable (matrixSphericalCovarianceData mu Sigma :
      Ioi (0 : ℝ) × GaussianData n p → GaussianData n p) := by
  unfold matrixSphericalCovarianceData
  apply (measurable_addLocationData mu).comp
  unfold scaleGaussianData
  refine measurable_pi_lambda _ fun k ↦ ?_
  have hradius : Measurable (fun q : Ioi (0 : ℝ) × GaussianData n p ↦
      (q.1.1 : ℝ)) := measurable_subtype_coe.comp measurable_fst
  have hcorr : Measurable (fun q : Ioi (0 : ℝ) × GaussianData n p ↦
      correlateRowsCovariance Sigma q.2 k) :=
    (Sigma.measurable_correlateObservation.comp
      ((measurable_pi_apply k).comp measurable_snd))
  exact hradius.smul hcorr

/-- The Pearson-matrix law in Corollary 3.4 before reducing the covariance
matrix to its population correlation matrix. -/
def matrixSphericalCovariancePearsonLaw {p : ℕ} (n : ℕ)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p)
    (radiusLaw : Measure (Ioi (0 : ℝ))) :
    Measure (Matrix (Fin p) (Fin p) ℝ) :=
  Measure.map (rawPearsonMatrix ∘ matrixSphericalCovarianceData mu Sigma)
    (radiusLaw.prod (frobeniusUniformDirectionLaw n p))

instance matrixSphericalCovariancePearsonLaw_isProbability {p : ℕ} (n : ℕ)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p)
    (radiusLaw : Measure (Ioi (0 : ℝ))) [IsProbabilityMeasure radiusLaw] :
    IsProbabilityMeasure
      (matrixSphericalCovariancePearsonLaw n mu Sigma radiusLaw) := by
  unfold matrixSphericalCovariancePearsonLaw
  exact Measure.isProbabilityMeasure_map
    ((measurable_rawPearsonMatrix.comp
      (measurable_matrixSphericalCovarianceData mu Sigma)).aemeasurable)

/-- Pointwise cancellation of location and of both positive radial factors in
the arbitrary-covariance model. -/
theorem rawPearsonMatrix_matrixSphericalCovarianceData_direction
    {n p : ℕ} (hn : 0 < n)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p)
    (q : Ioi (0 : ℝ) × GaussianData n p) :
    rawPearsonMatrix
        (matrixSphericalCovarianceData mu Sigma
          (q.1, frobeniusDirectionData q.2)) =
      rawPearsonMatrix (correlateRowsCovariance Sigma q.2) := by
  unfold matrixSphericalCovarianceData
  rw [rawPearsonMatrix_addLocationData hn]
  rw [rawPearsonMatrix_scaleGaussianData_of_pos q.1.1 q.1.2]
  unfold frobeniusDirectionData
  split_ifs with hzero
  · rfl
  · rw [correlateRowsCovariance_scaleGaussianData]
    apply rawPearsonMatrix_scaleGaussianData_of_pos
    exact inv_pos.mpr (lt_of_le_of_ne
      (frobeniusNormData_nonneg q.2) (Ne.symm hzero))

/-- Exact covariance-level law: an arbitrary independent positive radius and
arbitrary location disappear, leaving iid Gaussian observations with
covariance `Sigma`. -/
theorem matrixSphericalCovariancePearsonLaw_eq_gaussianRawPearsonLaw
    {n p : ℕ} (hn : 0 < n)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p)
    (radiusLaw : Measure (Ioi (0 : ℝ))) [IsProbabilityMeasure radiusLaw] :
    matrixSphericalCovariancePearsonLaw n mu Sigma radiusLaw =
      Measure.map rawPearsonMatrix
        (covarianceGaussianDataMeasure n Sigma) := by
  unfold matrixSphericalCovariancePearsonLaw frobeniusUniformDirectionLaw
  have hid : Measure.map (id : Ioi (0 : ℝ) → Ioi (0 : ℝ)) radiusLaw =
      radiusLaw := Measure.map_id
  rw [← hid]
  rw [Measure.map_prod_map radiusLaw (standardGaussianDataMeasure n p)
    measurable_id measurable_frobeniusDirectionData]
  rw [Measure.map_map
    (measurable_rawPearsonMatrix.comp
      (measurable_matrixSphericalCovarianceData mu Sigma))
    (measurable_id.prodMap measurable_frobeniusDirectionData)]
  have hfun :
      ((@rawPearsonMatrix n p ∘ matrixSphericalCovarianceData mu Sigma) ∘
          Prod.map id (@frobeniusDirectionData n p)) =
        ((@rawPearsonMatrix n p ∘ correlateRowsCovariance Sigma) ∘
          (Prod.snd : Ioi (0 : ℝ) × GaussianData n p → GaussianData n p)) := by
    funext q
    exact rawPearsonMatrix_matrixSphericalCovarianceData_direction
      hn mu Sigma q
  rw [hfun, ← Measure.map_map
    (measurable_rawPearsonMatrix.comp
      (measurable_correlateRowsCovariance Sigma)) measurable_snd]
  rw [measurePreserving_snd.map_eq]
  rw [← Measure.map_map measurable_rawPearsonMatrix
    (measurable_correlateRowsCovariance Sigma)]
  rw [map_correlateRowsCovariance_standardGaussianDataMeasure]

/-- A Gaussian Pearson law written as a product covariance law is identical
to the square-root realization used by the residual-coordinate theorem. -/
theorem map_rawPearson_correlatedGaussianDataMeasure_eq_squareRoot
    {n p : ℕ} (R : CorrelationMatrix p) :
    Measure.map rawPearsonMatrix (correlatedGaussianDataMeasure n R) =
      Measure.map (rawPearsonMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure n p) := by
  rw [← map_correlateRows_standardGaussianDataMeasure R]
  exact Measure.map_map measurable_rawPearsonMatrix
    (measurable_correlateRows R)

/-! ## From `n` raw observations to `n - 1` Gaussian residual coordinates -/

/-- Mix a family of variable columns by the population covariance square
root.  This definition works in every real inner-product observation space. -/
def mixColumns {p : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (R : CorrelationMatrix p)
    (v : Fin p → E) : Fin p → E :=
  fun i ↦ ∑ j, R.covarianceSqrt i j • v j

theorem measurable_mixColumns {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (R : CorrelationMatrix p) :
    Measurable (mixColumns (E := E) R) := by
  unfold mixColumns
  refine measurable_pi_lambda _ fun i ↦
    Finset.measurable_sum _ fun j _ ↦ ?_
  exact measurable_const.smul (measurable_pi_apply j)

/-- Pearson matrix written purely in terms of independent variable columns. -/
def correlatedColumnPearson {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : CorrelationMatrix p) (v : Fin p → E) :
    Matrix (Fin p) (Fin p) ℝ :=
  normalizedGram (mixColumns R v)

theorem measurable_normalizedGramFamily {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] :
    Measurable (normalizedGram : (Fin p → E) →
      Matrix (Fin p) (Fin p) ℝ) := by
  unfold normalizedGram Matrix.gram normalizeVector
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  have hi : Measurable (fun v : Fin p → E ↦ v i) := measurable_pi_apply i
  have hj : Measurable (fun v : Fin p → E ↦ v j) := measurable_pi_apply j
  exact Measurable.inner (hi.norm.inv.smul hi) (hj.norm.inv.smul hj)

theorem measurable_correlatedColumnPearson {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (R : CorrelationMatrix p) :
    Measurable (correlatedColumnPearson (E := E) R) := by
  exact measurable_normalizedGramFamily.comp (measurable_mixColumns R)

theorem dataColumns_correlateRows {n p : ℕ}
    (R : CorrelationMatrix p) (x : GaussianData n p) :
    dataColumns (correlateRows R x) = mixColumns R (dataColumns x) := by
  ext i k
  simp only [dataColumns, dataColumn_apply, mixColumns, correlateRows,
    CorrelationMatrix.correlateObservation, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem sampleCorrelationMatrix_correlateRows_eq_columnPearson
    {n p : ℕ} (R : CorrelationMatrix p) (x : GaussianData n p) :
    sampleCorrelationMatrix (correlateRows R x) =
      correlatedColumnPearson R (dataColumns x) := by
  unfold sampleCorrelationMatrix correlatedColumnPearson
  rw [dataColumns_correlateRows]

theorem mixColumns_linearIsometry {p : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (R : CorrelationMatrix p) (v : Fin p → E) :
    mixColumns R (fun j ↦ T (v j)) = fun i ↦ T (mixColumns R v i) := by
  funext i
  simp [mixColumns, map_sum, map_smul]

theorem correlatedColumnPearson_linearIsometry {p : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (R : CorrelationMatrix p) (v : Fin p → E) :
    correlatedColumnPearson R (fun j ↦ T (v j)) =
      correlatedColumnPearson R v := by
  unfold correlatedColumnPearson
  rw [mixColumns_linearIsometry]
  exact normalizedGram_linearIsometry T (mixColumns R v)

/-- A fixed orthonormal-coordinate identification of the centered subspace
of `m+1` raw observations with `m` residual coordinates. -/
def centeredCoordinateIsometry (m : ℕ) :
    centeredSubspace (m + 1) ≃ₗᵢ[ℝ] ObservationSpace m :=
  ((stdOrthonormalBasis ℝ (centeredSubspace (m + 1))).reindex
    (finCongr (by
      simpa using finrank_centeredSubspace (N := m + 1)
        (Nat.zero_lt_succ m)))).repr

/-- Apply an isometry independently to all variable columns. -/
def mapColumnIsometry {p : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (v : Fin p → E) : Fin p → F :=
  fun j ↦ T (v j)

theorem measurable_mapColumnIsometry {p : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (T : E →ₗᵢ[ℝ] F) : Measurable (mapColumnIsometry (p := p) T) := by
  unfold mapColumnIsometry
  fun_prop

theorem map_mapColumnIsometry_pi_stdGaussian {p : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (T : E ≃ₗᵢ[ℝ] F) :
    Measure.map (mapColumnIsometry (p := p) T.toLinearIsometry)
        (Measure.pi fun _ : Fin p ↦ stdGaussian E) =
      Measure.pi fun _ : Fin p ↦ stdGaussian F := by
  let _ (j : Fin p) : IsProbabilityMeasure ((stdGaussian E).map T) :=
    Measure.isProbabilityMeasure_map T.continuous.measurable.aemeasurable
  change Measure.map (fun v : Fin p → E ↦ fun j ↦ T (v j))
      (Measure.pi fun _ : Fin p ↦ stdGaussian E) =
    Measure.pi fun _ : Fin p ↦ stdGaussian F
  rw [Measure.pi_map_pi (fun _ ↦ T.continuous.measurable.aemeasurable)]
  congr 1
  funext j
  exact stdGaussian_map T

/-- Centering after covariance mixing is the same as mixing the
subtype-valued centered columns. -/
theorem centeredColumns_correlateRows_eq_mixColumns
    {n p : ℕ} (hn : 0 < n) (R : CorrelationMatrix p)
    (x : GaussianData n p) :
    (fun i ↦ centerVector (dataColumn (correlateRows R x) i)) =
      (fun i ↦ ((mixColumns R (centerColumns n p (dataColumns x)) i :
        centeredSubspace n) : ObservationSpace n)) := by
  funext i
  rw [show dataColumn (correlateRows R x) i =
      mixColumns R (dataColumns x) i by
    exact congrFun (dataColumns_correlateRows R x) i]
  rw [← coe_orthogonalProjectionOnto_centeredSubspace hn]
  change (((centeredSubspace n).orthogonalProjectionOnto
      (mixColumns R (dataColumns x) i) : centeredSubspace n) :
        ObservationSpace n) = _
  congr 1
  simp [mixColumns, centerColumns, map_sum, map_smul]

/-- Raw centering plus correlation equals the column-space statistic in the
`n-1`-dimensional centered subspace. -/
theorem rawPearsonMatrix_correlateRows_eq_centeredColumnPearson
    {n p : ℕ} (hn : 0 < n) (R : CorrelationMatrix p)
    (x : GaussianData n p) :
    rawPearsonMatrix (correlateRows R x) =
      correlatedColumnPearson R (centerColumns n p (dataColumns x)) := by
  rw [rawPearsonMatrix_eq_normalizedGram_centeredColumns]
  unfold correlatedColumnPearson
  rw [centeredColumns_correlateRows_eq_mixColumns hn R x]
  exact normalizedGram_subtype_coe (centeredSubspace n)
    (mixColumns R (centerColumns n p (dataColumns x)))

/-- Exact equality of Pearson-matrix pushforward laws: centering `m+1`
Gaussian raw observations is distributionally the same as using `m`
independent Gaussian residual coordinates. -/
theorem map_rawPearson_correlated_standard_succ_eq_residual
    (m p : ℕ) (R : CorrelationMatrix p) :
    Measure.map (rawPearsonMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure (m + 1) p) =
      Measure.map (sampleCorrelationMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure m p) := by
  let T := centeredCoordinateIsometry m
  let FC : (Fin p → centeredSubspace (m + 1)) →
      Matrix (Fin p) (Fin p) ℝ := correlatedColumnPearson R
  let FE : (Fin p → ObservationSpace m) →
      Matrix (Fin p) (Fin p) ℝ := correlatedColumnPearson R
  have hFC : Measurable FC := measurable_correlatedColumnPearson R
  have hFE : Measurable FE := measurable_correlatedColumnPearson R
  have hT : Measurable (mapColumnIsometry (p := p) T.toLinearIsometry) :=
    measurable_mapColumnIsometry T.toLinearIsometry
  calc
    Measure.map (rawPearsonMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure (m + 1) p) =
      Measure.map (FC ∘ centerColumns (m + 1) p ∘ dataColumns)
        (standardGaussianDataMeasure (m + 1) p) := by
          apply Measure.map_congr
          exact Filter.Eventually.of_forall fun x ↦
            rawPearsonMatrix_correlateRows_eq_centeredColumnPearson
              (Nat.zero_lt_succ m) R x
    _ = Measure.map (FC ∘ centerColumns (m + 1) p)
        (Measure.map dataColumns
          (standardGaussianDataMeasure (m + 1) p)) := by
          change Measure.map
              ((FC ∘ centerColumns (m + 1) p) ∘ dataColumns)
              (standardGaussianDataMeasure (m + 1) p) = _
          rw [Measure.map_map
            (hFC.comp (measurable_centerColumns (m + 1) p))
            measurable_dataColumns]
    _ = Measure.map (FC ∘ centerColumns (m + 1) p)
        (Measure.pi fun _ : Fin p ↦ stdGaussian (ObservationSpace (m + 1))) := by
          rw [map_dataColumns_standardGaussianDataMeasure]
    _ = Measure.map FC
        (Measure.map (centerColumns (m + 1) p)
          (Measure.pi fun _ : Fin p ↦
            stdGaussian (ObservationSpace (m + 1)))) := by
          rw [Measure.map_map hFC (measurable_centerColumns (m + 1) p)]
    _ = Measure.map FC
        (Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace (m + 1))) := by
          rw [map_centerColumns_pi_stdGaussian]
    _ = Measure.map (FE ∘ mapColumnIsometry (p := p) T.toLinearIsometry)
        (Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace (m + 1))) := by
          apply Measure.map_congr
          exact Filter.Eventually.of_forall fun v ↦
            (correlatedColumnPearson_linearIsometry
              T.toLinearIsometry R v).symm
    _ = Measure.map FE
        (Measure.map (mapColumnIsometry (p := p) T.toLinearIsometry)
          (Measure.pi fun _ : Fin p ↦
            stdGaussian (centeredSubspace (m + 1)))) := by
          rw [Measure.map_map hFE hT]
    _ = Measure.map FE
        (Measure.pi fun _ : Fin p ↦ stdGaussian (ObservationSpace m)) := by
          rw [map_mapColumnIsometry_pi_stdGaussian T]
    _ = Measure.map FE
        (Measure.map dataColumns (standardGaussianDataMeasure m p)) := by
          rw [map_dataColumns_standardGaussianDataMeasure]
    _ = Measure.map (FE ∘ dataColumns)
        (standardGaussianDataMeasure m p) := by
          rw [Measure.map_map hFE measurable_dataColumns]
    _ = Measure.map (sampleCorrelationMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure m p) := by
          apply Measure.map_congr
          exact Filter.Eventually.of_forall fun x ↦
            (sampleCorrelationMatrix_correlateRows_eq_columnPearson R x).symm

/-- Corollary 3.4 in the residual-coordinate form used by the rest of the
formalization. -/
theorem matrixSphericalPearsonLaw_eq_gaussianResidualPearsonLaw
    {m p : ℕ}
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p)
    (radiusLaw : Measure (Ioi (0 : ℝ))) [IsProbabilityMeasure radiusLaw] :
    matrixSphericalPearsonLaw (m + 1) mu R radiusLaw =
      Measure.map (sampleCorrelationMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure m p) := by
  rw [matrixSphericalPearsonLaw_eq_gaussianRawPearsonLaw
    (Nat.zero_lt_succ m)]
  exact map_rawPearson_correlated_standard_succ_eq_residual m p R

/-- Corollary 3.4 exactly as stated for an arbitrary positive-definite
population covariance `Sigma`.  Its marginal standard deviations cancel,
and the remaining law is the Gaussian residual-coordinate Pearson law with
population correlation `Sigma.correlation`. -/
theorem matrixSphericalCovariancePearsonLaw_eq_gaussianResidualPearsonLaw
    {m p : ℕ}
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p)
    (radiusLaw : Measure (Ioi (0 : ℝ))) [IsProbabilityMeasure radiusLaw] :
    matrixSphericalCovariancePearsonLaw (m + 1) mu Sigma radiusLaw =
      Measure.map
        (sampleCorrelationMatrix ∘ correlateRows Sigma.correlation)
        (standardGaussianDataMeasure m p) := by
  rw [matrixSphericalCovariancePearsonLaw_eq_gaussianRawPearsonLaw
    (Nat.zero_lt_succ m)]
  rw [map_rawPearson_covarianceGaussianDataMeasure_eq_correlation]
  rw [map_rawPearson_correlatedGaussianDataMeasure_eq_squareRoot]
  exact map_rawPearson_correlated_standard_succ_eq_residual
    m p Sigma.correlation

end

end LogdetLean
