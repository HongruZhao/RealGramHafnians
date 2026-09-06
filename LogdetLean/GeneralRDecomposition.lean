import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.HasLaw
import LogdetLean.FixedSubspaceGaussian
import LogdetLean.GaussianLinearIndependence
import LogdetLean.GaussianSampleCorrelation
import LogdetLean.GeneralRLogdetAlgebra
/-!
# Exact common-space decomposition for the general-correlation statistic

This file formalizes the exact algebra behind the general-`R` reduction in
Zhao, *On the Log Determinant of Sample Correlation Matrices under
Gaussianity*, arXiv:2608.00565v1:

* Lemma 5.1 and equations (5.1)--(5.2), printed p. 10;
* Lemma 5.2, printed p. 11, for the definitions of `h_m`, `u_m`, and `e_m`.
  Its numbered conclusions (5.3)--(5.4) are the later variance/covariance
  estimates and are not asserted here;
* the subsection “Reduction to a linear correlation-matrix term,” equations
  `reduction-expanded`, `MR`, and `M-minus-E` in the manuscript source.

All random variables below live on one canonical probability space: `m`
independent standard Gaussian rows.  Correlated observations are produced by
the already verified covariance-square-root map.  Since `Real.log 0 = 0` in
Lean, every definition is total.  Log-determinant identities are proved on
the full-rank event, and that event is then proved to have probability one
when `p ≤ m`; no positivity assumption is hidden in a definition.
-/

namespace LogdetLean
namespace GeneralRDecomposition

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Module WithLp
open scoped BigOperators MatrixOrder RealInnerProductSpace

variable {m p : ℕ}

/-- The identity-covariance scatter `W₀ = Zᵀ Z` on the canonical standard
Gaussian data space. -/
def W0 (z : GaussianData m p) : Matrix (Fin p) (Fin p) ℝ :=
  scatterMatrix z

/-- The correlated scatter `W_R = R^(1/2) W₀ R^(1/2)`, realized on the same
standard Gaussian data space. -/
def WR (R : CorrelationMatrix p) (z : GaussianData m p) :
    Matrix (Fin p) (Fin p) ℝ :=
  scatterMatrix (correlateRows R z)

theorem WR_eq_covarianceSqrt_mul (R : CorrelationMatrix p)
    (z : GaussianData m p) :
    WR R z = R.covarianceSqrt * W0 z * R.covarianceSqrt := by
  exact scatterMatrix_correlateRows R z

/-- The `i`th correlated Gaussian variable-column `G_i ∈ ℝ^m`.  Its squared
norm is the paper's `Q_i`. -/
def G (R : CorrelationMatrix p) (z : GaussianData m p) (i : Fin p) :
    EuclideanSpace ℝ (Fin m) :=
  dataColumn (correlateRows R z) i

/-- `Q_i = ||G_i||² = (W_R)_{ii}`. -/
def Q (R : CorrelationMatrix p) (z : GaussianData m p) (i : Fin p) : ℝ :=
  ‖G R z i‖ ^ 2

@[simp]
theorem Q_eq_WR_diagonal (R : CorrelationMatrix p)
    (z : GaussianData m p) (i : Fin p) :
    Q R z i = WR R z i i := by
  rw [WR, scatterMatrix_eq_gram_dataColumns]
  simp [Q, G, dataColumns, Matrix.gram_apply]

/-- The scalar linear fluctuation `g_i = (Q_i-m)/m` requested in the
quantitative manuscript.  It is `u_m(G_i)` in arXiv:2608.00565v1. -/
def g (m : ℕ) (R : CorrelationMatrix p) (z : GaussianData m p)
    (i : Fin p) : ℝ :=
  (Q R z i - (m : ℝ)) / (m : ℝ)

/-- Exact log-chi-square mean, kept as an integral so this definition does not
presuppose a not-yet-formalized differentiation formula for the Gamma law. -/
def chiSquareLogMean (m : ℕ) : ℝ :=
  ∫ q, Real.log q ∂gammaMeasure ((m : ℝ) / 2) (1 / 2)

/-- `h_m(G)=log(||G||²)-E log(χ²_m)`, Lemma 5.2, p. 11. -/
def h_m (m : ℕ) (Gv : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.log (‖Gv‖ ^ 2) - chiSquareLogMean m

/-- `u_m(G)=(||G||²-m)/m`, Lemma 5.2, p. 11. -/
def u_m (m : ℕ) (Gv : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (‖Gv‖ ^ 2 - (m : ℝ)) / (m : ℝ)

/-- Nonlinear residual `e_m=h_m-u_m`, Lemma 5.2, p. 11. -/
def e_m (m : ℕ) (Gv : EuclideanSpace ℝ (Fin m)) : ℝ :=
  h_m m Gv - u_m m Gv

@[simp]
theorem u_m_G_eq_g (m : ℕ) (R : CorrelationMatrix p)
    (z : GaussianData m p) (i : Fin p) :
    u_m m (G R z i) = g m R z i := rfl

theorem h_m_eq_u_m_add_e_m (m : ℕ) (Gv : EuclideanSpace ℝ (Fin m)) :
    h_m m Gv = u_m m Gv + e_m m Gv := by
  simp [e_m]

/-- Mean of the standard log-scatter determinant. -/
def W0LogDetMean (m p : ℕ) : ℝ :=
  ∫ z, Real.log (W0 z).det ∂standardGaussianDataMeasure m p

/-- Leading term
`M_R = log|W₀|-E log|W₀| - Σ_i (Q_i-m)/m`. -/
def M_R (m : ℕ) (R : CorrelationMatrix p) (z : GaussianData m p) : ℝ :=
  Real.log (W0 z).det - W0LogDetMean m p - ∑ i, g m R z i

/-- Nonlinear remainder `E_R = Σ_i e_m(G_i)`. -/
def E_R (m : ℕ) (R : CorrelationMatrix p) (z : GaussianData m p) : ℝ :=
  ∑ i, e_m m (G R z i)

/-- The exact deterministic centering appearing after equation (5.1):
`log|R| + E log|W₀| - p E log(χ²_m)`.  Under log-integrability this is the
actual expectation of the sample log determinant. -/
def logDetCenter (m : ℕ) (R : CorrelationMatrix p) : ℝ :=
  Real.log R.val.det + W0LogDetMean m p -
    (p : ℝ) * chiSquareLogMean m

/-- Sample correlation matrix on the canonical standard Gaussian space. -/
def sampleCorrelation (R : CorrelationMatrix p) (z : GaussianData m p) :
    Matrix (Fin p) (Fin p) ℝ :=
  sampleCorrelationMatrix (correlateRows R z)

/-! ## Measurability -/

theorem measurable_G (R : CorrelationMatrix p) (i : Fin p) :
    Measurable (fun z : GaussianData m p ↦ G R z i) := by
  exact (measurable_pi_apply i).comp
    (measurable_dataColumns.comp (measurable_correlateRows R))

theorem measurable_Q (R : CorrelationMatrix p) (i : Fin p) :
    Measurable (fun z : GaussianData m p ↦ Q R z i) := by
  unfold Q
  exact (measurable_G R i).norm.pow_const 2

theorem measurable_g (m : ℕ) (R : CorrelationMatrix p) (i : Fin p) :
    Measurable (fun z : GaussianData m p ↦ g m R z i) := by
  unfold g
  exact ((measurable_Q R i).sub_const _).div_const _

theorem measurable_h_m (m : ℕ) : Measurable (h_m m) := by
  unfold h_m
  fun_prop

theorem measurable_u_m (m : ℕ) : Measurable (u_m m) := by
  unfold u_m
  fun_prop

theorem measurable_e_m (m : ℕ) : Measurable (e_m m) := by
  unfold e_m
  exact (measurable_h_m m).sub (measurable_u_m m)

private theorem measurable_det_W0 :
    Measurable (fun z : GaussianData m p ↦ (W0 z).det) := by
  have hdet : Measurable
      (fun S : Matrix (Fin p) (Fin p) ℝ ↦ S.det) := by
    simp_rw [Matrix.det_apply']
    fun_prop
  exact hdet.comp measurable_scatterMatrix

theorem measurable_M_R (m : ℕ) (R : CorrelationMatrix p) :
    Measurable (M_R m R) := by
  unfold M_R
  exact ((measurable_det_W0.log.sub measurable_const).sub
    (Finset.measurable_sum _ fun i _ ↦ measurable_g m R i))

theorem measurable_E_R (m : ℕ) (R : CorrelationMatrix p) :
    Measurable (E_R m R) := by
  unfold E_R
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_e_m m).comp (measurable_G R i)

theorem measurable_log_det_sampleCorrelation (R : CorrelationMatrix p) :
    Measurable (fun z : GaussianData m p ↦
      Real.log (sampleCorrelation R z).det) := by
  unfold sampleCorrelation
  exact (measurable_det_sampleCorrelationMatrix.comp
    (measurable_correlateRows R)).log

/-! ## Exact one-column and chi-square laws -/

/-- Under the correlated row-product measure, each variable column is a
standard Gaussian vector in `ℝ^m`.  Correlations occur between different
columns, not within a column. -/
theorem map_dataColumn_correlatedGaussianDataMeasure
    (R : CorrelationMatrix p) (i : Fin p) :
    Measure.map (fun x : GaussianData m p ↦ dataColumn x i)
        (correlatedGaussianDataMeasure m R) =
      stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let rawColumn : GaussianData m p → (Fin m → ℝ) := fun x k ↦ x k i
  have hraw : Measure.map rawColumn (correlatedGaussianDataMeasure m R) =
      Measure.pi (fun _ : Fin m ↦ gaussianReal 0 1) := by
    let _ (k : Fin m) : IsProbabilityMeasure
        (R.gaussianMeasure.map (fun x : CorrelationMatrix.Observation p ↦ x i)) :=
      Measure.isProbabilityMeasure_map
        (R.measurePreserving_eval i).measurable.aemeasurable
    unfold correlatedGaussianDataMeasure
    change Measure.map
        (fun x : GaussianData m p ↦ fun k ↦ (fun y :
          CorrelationMatrix.Observation p ↦ y i) (x k))
        (Measure.pi fun _ : Fin m ↦ R.gaussianMeasure) =
      Measure.pi (fun _ : Fin m ↦ gaussianReal 0 1)
    rw [Measure.pi_map_pi (fun _ ↦
      (R.measurePreserving_eval i).measurable.aemeasurable)]
    congr 1
    funext k
    exact (R.measurePreserving_eval i).map_eq
  calc
    Measure.map (fun x : GaussianData m p ↦ dataColumn x i)
        (correlatedGaussianDataMeasure m R) =
        Measure.map (WithLp.toLp 2)
          (Measure.map rawColumn (correlatedGaussianDataMeasure m R)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.map (WithLp.toLp 2)
          (Measure.pi (fun _ : Fin m ↦ gaussianReal 0 1)) := by rw [hraw]
    _ = stdGaussian (EuclideanSpace ℝ (Fin m)) := map_pi_eq_stdGaussian

/-- On the canonical standard-data probability space, every correlated
column `G_i` has standard Gaussian law. -/
theorem hasLaw_G_stdGaussian (R : CorrelationMatrix p) (i : Fin p) :
    HasLaw (fun z : GaussianData m p ↦ G R z i)
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (standardGaussianDataMeasure m p) := by
  have hrows : HasLaw (correlateRows R)
      (correlatedGaussianDataMeasure m R)
      (standardGaussianDataMeasure m p) := by
    exact ⟨(measurable_correlateRows R).aemeasurable,
      map_correlateRows_standardGaussianDataMeasure R⟩
  have hcol : HasLaw (fun x : GaussianData m p ↦ dataColumn x i)
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (correlatedGaussianDataMeasure m R) := by
    exact ⟨((measurable_pi_apply i).comp
      measurable_dataColumns).aemeasurable,
      map_dataColumn_correlatedGaussianDataMeasure R i⟩
  simpa [G, Function.comp_def] using hcol.fun_comp hrows

/-- Exact `Q_i ~ Gamma(m/2,1/2)`, equivalently `χ²_m`, for `m>0`. -/
theorem hasLaw_Q_gamma (hm : 0 < m) (R : CorrelationMatrix p) (i : Fin p) :
    HasLaw (fun z : GaussianData m p ↦ Q R z i)
      (gammaMeasure ((m : ℝ) / 2) (1 / 2))
      (standardGaussianDataMeasure m p) := by
  let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hnorm := hasLaw_normSq_stdGaussian (EuclideanSpace ℝ (Fin m))
  have hcomp := hnorm.fun_comp (hasLaw_G_stdGaussian R i)
  rw [stdGaussianNormSqMeasure_eq_gamma
    (EuclideanSpace ℝ (Fin m))] at hcomp
  simpa [Q, Function.comp_def] using hcomp

/-- Consequently the integral used in `chiSquareLogMean` is exactly the
expectation of `log Q_i` on the common probability space.  No integrability
hypothesis is needed for this change-of-variables identity. -/
theorem integral_log_Q_eq_chiSquareLogMean (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, Real.log (Q R z i) ∂standardGaussianDataMeasure m p =
      chiSquareLogMean m := by
  exact (hasLaw_Q_gamma hm R i).integral_comp
    (by fun_prop : AEStronglyMeasurable Real.log
      (gammaMeasure ((m : ℝ) / 2) (1 / 2)))

/-! ## Positivity and the full-rank event -/

/-- The positive covariance square root has positive determinant. -/
theorem covarianceSqrt_det_pos (R : CorrelationMatrix p) :
    0 < R.covarianceSqrt.det := by
  change 0 < (CFC.sqrt R.val).det
  rw [Matrix.PosSemidef.det_sqrt R.posSemidef]
  simpa only [RCLike.sqrt_real] using Real.sqrt_pos.2 R.det_pos

/-- Determinant form of `(sqrt R)^2=R`. -/
theorem covarianceSqrt_det_sq (R : CorrelationMatrix p) :
    R.val.det = R.covarianceSqrt.det ^ 2 := by
  change R.val.det = (CFC.sqrt R.val).det ^ 2
  rw [Matrix.PosSemidef.det_sqrt R.posSemidef]
  simpa only [RCLike.sqrt_real] using (Real.sq_sqrt R.det_pos.le).symm

/-- The first `p` rows, available when `p≤m`. -/
def leadingRows (hp : p ≤ m) (z : GaussianData m p) :
    Fin p → CorrelationMatrix.Observation p :=
  fun i ↦ z (Fin.castLEEmb hp i)

/-- Square matrix formed by the first `p` rows. -/
def leadingDataMatrix (hp : p ≤ m) (z : GaussianData m p) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ z (Fin.castLEEmb hp i) j

/-- If the first `p` rows are linearly independent, then the full rectangular
data matrix has injective column action, hence `W₀=XᵀX` is positive definite. -/
theorem W0_posDef_of_leadingRows_linearIndependent (hp : p ≤ m)
    (z : GaussianData m p)
    (hli : LinearIndependent ℝ (leadingRows hp z)) :
    (W0 z).PosDef := by
  let e : EuclideanSpace ℝ (Fin p) ≃L[ℝ] (Fin p → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p ↦ ℝ)
  have hraw0 : LinearIndependent ℝ (e.toLinearMap ∘ leadingRows hp z) :=
    hli.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have hraw : LinearIndependent ℝ (leadingDataMatrix hp z).row := by
    change LinearIndependent ℝ
      (fun i : Fin p ↦ fun j : Fin p ↦ z (Fin.castLEEmb hp i) j)
    simpa [e, leadingRows, Function.comp_def,
      PiLp.coe_continuousLinearEquiv] using hraw0
  have hA : (leadingDataMatrix hp z).Nonsingular :=
    Matrix.Nonsingular.of_linearIndependent_row hraw
  have hAinj : Function.Injective (leadingDataMatrix hp z).mulVec :=
    Matrix.mulVec_injective_iff.mpr hA.linearIndependent_col
  have hXinj : Function.Injective (dataMatrix z).mulVec := by
    intro c d hcd
    apply hAinj
    funext i
    have hi := congrFun hcd (Fin.castLEEmb hp i)
    simpa [leadingDataMatrix, Matrix.mulVec, dotProduct, dataMatrix] using hi
  exact Matrix.PosDef.conjTranspose_mul_self (dataMatrix z) hXinj

theorem W0_det_pos_of_leadingRows_linearIndependent (hp : p ≤ m)
    (z : GaussianData m p)
    (hli : LinearIndependent ℝ (leadingRows hp z)) :
    0 < (W0 z).det :=
  (W0_posDef_of_leadingRows_linearIndependent hp z hli).det_pos

/-- The leading `p` standard Gaussian rows are linearly independent almost
surely. -/
theorem ae_leadingRows_linearIndependent (hp : p ≤ m) :
    ∀ᵐ z ∂standardGaussianDataMeasure m p,
      LinearIndependent ℝ (leadingRows hp z) := by
  let X : Fin m → GaussianData m p → CorrelationMatrix.Observation p :=
    fun k z ↦ z k
  have hAll : iIndepFun X (standardGaussianDataMeasure m p) := by
    exact iIndepFun_pi (μ := fun _ : Fin m ↦
      stdGaussian (CorrelationMatrix.Observation p))
      (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hSub : iIndepFun
      (fun i : Fin p ↦ X (Fin.castLEEmb hp i))
      (standardGaussianDataMeasure m p) :=
    hAll.precomp (Fin.castLEEmb hp).injective
  have hrow (i : Fin p) : HasLaw
      (X (Fin.castLEEmb hp i))
      (stdGaussian (CorrelationMatrix.Observation p))
      (standardGaussianDataMeasure m p) := by
    exact (MeasureTheory.measurePreserving_eval
      (fun _ : Fin m ↦ stdGaussian (CorrelationMatrix.Observation p))
      (Fin.castLEEmb hp i)).hasLaw
  have hlaw : HasLaw (leadingRows hp)
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (CorrelationMatrix.Observation p))
      (standardGaussianDataMeasure m p) := by
    change HasLaw (fun z i ↦ z (Fin.castLEEmb hp i))
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (CorrelationMatrix.Observation p))
      (standardGaussianDataMeasure m p)
    exact hSub.hasLaw_pi hrow
  refine (hlaw.ae_iff
    (p := fun v : Fin p → CorrelationMatrix.Observation p ↦
      LinearIndependent ℝ v) ?_).2 ?_
  · exact measurableSet_setOfPred.mp
      (measurableSet_linearlyIndependentTuples
        (E := CorrelationMatrix.Observation p) p)
  · simpa using ae_linearIndependent_pi_stdGaussian
      (E := CorrelationMatrix.Observation p) p (by simp)

/-- Therefore `W₀` has positive determinant almost surely whenever `p≤m`. -/
theorem ae_W0_det_pos (hp : p ≤ m) :
    ∀ᵐ z ∂standardGaussianDataMeasure m p, 0 < (W0 z).det := by
  filter_upwards [ae_leadingRows_linearIndependent hp] with z hz
  exact W0_det_pos_of_leadingRows_linearIndependent hp z hz

/-- Positive `W₀` implies positive `W_R`; in particular every `Q_i` is
strictly positive. -/
theorem WR_posDef_of_W0_det_pos (R : CorrelationMatrix p)
    (z : GaussianData m p) (hW : 0 < (W0 z).det) :
    (WR R z).PosDef := by
  have hWpd : (W0 z).PosDef :=
    (scatterMatrix_posSemidef z).posDef_iff_det_ne_zero.mpr hW.ne'
  have hBinj : Function.Injective R.covarianceSqrt.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (R.covarianceSqrt.isUnit_iff_isUnit_det.mpr
        (isUnit_iff_ne_zero.mpr (covarianceSqrt_det_pos R).ne'))
  have hcongr := hWpd.conjTranspose_mul_mul_same hBinj
  rw [R.covarianceSqrt_conjTranspose] at hcongr
  simpa [WR_eq_covarianceSqrt_mul] using hcongr

theorem Q_pos_of_W0_det_pos (R : CorrelationMatrix p)
    (z : GaussianData m p) (hW : 0 < (W0 z).det) (i : Fin p) :
    0 < Q R z i := by
  rw [Q_eq_WR_diagonal]
  exact (WR_posDef_of_W0_det_pos R z hW).diag_pos

/-- All diagonal energies are positive almost surely. -/
theorem ae_Q_pos (hp : p ≤ m) (R : CorrelationMatrix p) (i : Fin p) :
    ∀ᵐ z ∂standardGaussianDataMeasure m p, 0 < Q R z i := by
  filter_upwards [ae_W0_det_pos hp] with z hz
  exact Q_pos_of_W0_det_pos R z hz i

/-! ## Exact determinant and fluctuation identities -/

/-- The normalized-Gram definition of sample correlation is exactly diagonal
normalization of the correlated scatter matrix.  This identity is total: the
two sides use the same totalized inverse when a column is zero. -/
theorem sampleCorrelation_eq_correlationNormalize
    (R : CorrelationMatrix p) (z : GaussianData m p) :
    sampleCorrelation R z = correlationNormalizeMatrix (WR R z) := by
  ext i j
  rw [sampleCorrelation, sampleCorrelationMatrix_apply]
  rw [correlationNormalizeMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [← Q_eq_WR_diagonal R z i, ← Q_eq_WR_diagonal R z j]
  simp only [Q, Real.sqrt_sq_eq_abs, abs_norm]
  simp only [G, WR]
  ring

/-- Equation (5.1) on the full-rank event, now specialized to the canonical
common probability space. -/
theorem log_det_sampleCorrelation_eq_population_add
    (R : CorrelationMatrix p) (z : GaussianData m p)
    (hW : 0 < (W0 z).det) :
    Real.log (sampleCorrelation R z).det =
      Real.log R.val.det + Real.log (W0 z).det -
        ∑ i, Real.log (Q R z i) := by
  rw [sampleCorrelation_eq_correlationNormalize R z,
    WR_eq_covarianceSqrt_mul]
  have hdiag : ∀ i, 0 <
      (R.covarianceSqrt * W0 z * R.covarianceSqrt) i i := by
    intro i
    rw [← WR_eq_covarianceSqrt_mul R z, ← Q_eq_WR_diagonal]
    exact Q_pos_of_W0_det_pos R z hW i
  simpa only [← WR_eq_covarianceSqrt_mul R z,
    ← Q_eq_WR_diagonal R z] using
    (log_det_correlationNormalize_eq_population_add
      R.covarianceSqrt R.val (W0 z)
      (covarianceSqrt_det_pos R) R.det_pos hW
      (covarianceSqrt_det_sq R) hdiag)

/-- The sum of the column energies is the trace of the correlated scatter. -/
theorem sum_Q_eq_trace_WR (R : CorrelationMatrix p)
    (z : GaussianData m p) :
    ∑ i, Q R z i = Matrix.trace (WR R z) := by
  simp only [Matrix.trace, Matrix.diag_apply, Q_eq_WR_diagonal]

/-- Cyclicity of trace turns the correlated scatter trace into
`tr(R W₀)`. -/
theorem trace_WR_eq_trace_R_mul_W0 (R : CorrelationMatrix p)
    (z : GaussianData m p) :
    Matrix.trace (WR R z) = Matrix.trace (R.val * W0 z) := by
  rw [WR_eq_covarianceSqrt_mul, Matrix.trace_mul_cycle,
    R.covarianceSqrt_mul_self]

/-- The finite sum of scalar fluctuations is the trace fluctuation used in
the manuscript definition of `M_R`. -/
theorem sum_g_eq_trace (m : ℕ) (R : CorrelationMatrix p)
    (z : GaussianData m p) :
    ∑ i, g m R z i =
      (Matrix.trace (R.val * W0 z) - (m : ℝ) * (p : ℝ)) /
        (m : ℝ) := by
  calc
    ∑ i, g m R z i =
        ((∑ i, Q R z i) - (m : ℝ) * (p : ℝ)) / (m : ℝ) := by
      unfold g
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    _ = (Matrix.trace (R.val * W0 z) -
        (m : ℝ) * (p : ℝ)) / (m : ℝ) := by
      congr 2
      rw [sum_Q_eq_trace_WR R z, trace_WR_eq_trace_R_mul_W0 R z]

/-- The trace form of `M_R` displayed in the manuscript. -/
theorem M_R_eq_trace_formula (m : ℕ) (R : CorrelationMatrix p)
    (z : GaussianData m p) :
    M_R m R z = Real.log (W0 z).det - W0LogDetMean m p -
      (Matrix.trace (R.val * W0 z) - (m : ℝ) * (p : ℝ)) /
        (m : ℝ) := by
  rw [M_R, sum_g_eq_trace]

/-- Exact pointwise `M_R-E_R` decomposition on the full-rank event.  This is
the identity labelled `M-minus-E` in the manuscript source. -/
theorem centered_log_det_eq_M_R_sub_E_R
    (R : CorrelationMatrix p) (z : GaussianData m p)
    (hW : 0 < (W0 z).det) :
    Real.log (sampleCorrelation R z).det - logDetCenter m R =
      M_R m R z - E_R m R z := by
  rw [log_det_sampleCorrelation_eq_population_add R z hW]
  unfold logDetCenter M_R E_R e_m h_m u_m g Q
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The exact decomposition holds almost surely whenever `p≤m`. -/
theorem ae_centered_log_det_eq_M_R_sub_E_R (hp : p ≤ m)
    (R : CorrelationMatrix p) :
    ∀ᵐ z ∂standardGaussianDataMeasure m p,
      Real.log (sampleCorrelation R z).det - logDetCenter m R =
        M_R m R z - E_R m R z := by
  filter_upwards [ae_W0_det_pos hp] with z hz
  exact centered_log_det_eq_M_R_sub_E_R R z hz

/-! ## Exact first moments available from the Gaussian library -/

/-- The squared norm of a standard Gaussian vector is integrable and has
mean equal to the dimension.  We prove this from the already verified
one-dimensional Gaussian second moment, rather than postulating a Gamma
moment formula. -/
theorem integrable_normSq_stdGaussian_and_integral_eq (m : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦ ‖x‖ ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin m))) ∧
      ∫ x, ‖x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin m)) =
        (m : ℝ) := by
  let ν := stdGaussian (EuclideanSpace ℝ (Fin m))
  have heval (k : Fin m) : MeasurePreserving
      (fun x : EuclideanSpace ℝ (Fin m) ↦ x k) ν
      (gaussianReal 0 1) := by
    change MeasurePreserving
      (fun x : EuclideanSpace ℝ (Fin m) ↦ x k)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) (gaussianReal 0 1)
    rw [← multivariateGaussian_zero_one]
    convert (measurePreserving_eval_multivariateGaussian
      (Matrix.PosSemidef.one :
        (1 : Matrix (Fin m) (Fin m) ℝ).PosSemidef) (i := k)) using 1
    all_goals simp
  have hid2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
    exact (memLp_two_iff_integrable_sq
      measurable_id'.aestronglyMeasurable).mp
      (memLp_id_gaussianReal (2 : NNReal))
  have hcoord (k : Fin m) : Integrable
      (fun x : EuclideanSpace ℝ (Fin m) ↦ (x k) ^ 2) ν := by
    simpa [Function.comp_def] using
      (heval k).integrable_comp_of_integrable hid2
  have hcoordIntegral (k : Fin m) :
      ∫ x : EuclideanSpace ℝ (Fin m), (x k) ^ 2 ∂ν = 1 := by
    have hstrong : AEStronglyMeasurable (fun x : ℝ ↦ x ^ 2)
        (Measure.map (fun x : EuclideanSpace ℝ (Fin m) ↦ x k) ν) := by
      rw [(heval k).map_eq]
      exact hid2.aestronglyMeasurable
    have hmap := integral_map (heval k).measurable.aemeasurable hstrong
    rw [(heval k).map_eq] at hmap
    have hsecond : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
      have hv := variance_id_gaussianReal (μ := 0) (v := 1)
      change Var[(fun x : ℝ ↦ x); gaussianReal 0 1] = 1 at hv
      rw [variance_eq_integral (X := fun x : ℝ ↦ x)
        measurable_id'.aemeasurable] at hv
      simpa only [integral_id_gaussianReal, sub_zero] using hv
    exact hmap.symm.trans hsecond
  constructor
  · simpa only [EuclideanSpace.real_norm_sq_eq] using
      (integrable_finsetSum Finset.univ fun k _ ↦ hcoord k)
  · simp_rw [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finsetSum Finset.univ fun k _ ↦ hcoord k]
    simp only [hcoordIntegral, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Every `Q_i` is integrable. -/
theorem integrable_Q (R : CorrelationMatrix p) (i : Fin p) :
    Integrable (fun z : GaussianData m p ↦ Q R z i)
      (standardGaussianDataMeasure m p) := by
  have hpres := (hasLaw_G_stdGaussian (m := m) R i).measurePreserving
    (measurable_G (m := m) R i)
  simpa [Q, Function.comp_def] using
    hpres.integrable_comp_of_integrable
      (integrable_normSq_stdGaussian_and_integral_eq m).1

/-- Exact first moment `E Q_i=m`. -/
theorem integral_Q_eq_m (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, Q R z i ∂standardGaussianDataMeasure m p = (m : ℝ) := by
  simpa [Q, Function.comp_def] using
    (hasLaw_G_stdGaussian (m := m) R i).integral_comp
      (integrable_normSq_stdGaussian_and_integral_eq m).1.aestronglyMeasurable
      |>.trans (integrable_normSq_stdGaussian_and_integral_eq m).2

/-- The linear fluctuation `g_i` is integrable. -/
theorem integrable_g (R : CorrelationMatrix p) (i : Fin p) :
    Integrable (fun z : GaussianData m p ↦ g m R z i)
      (standardGaussianDataMeasure m p) := by
  exact ((integrable_Q R i).sub (integrable_const _)).div_const _

/-- Exact centering `E g_i=0`.  This remains true for the degenerate `m=0`
definition because division is totalized in Lean. -/
theorem integral_g_eq_zero (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, g m R z i ∂standardGaussianDataMeasure m p = 0 := by
  unfold g
  rw [integral_div]
  rw [integral_sub (integrable_Q R i) (integrable_const _)]
  rw [integral_Q_eq_m]
  simp

/-- Integrability of the exactly centered log energy, conditional only on
the corresponding log-energy integrability. -/
theorem integrable_h_m_G (R : CorrelationMatrix p) (i : Fin p)
    (hlog : Integrable (fun z : GaussianData m p ↦ Real.log (Q R z i))
      (standardGaussianDataMeasure m p)) :
    Integrable (fun z : GaussianData m p ↦ h_m m (G R z i))
      (standardGaussianDataMeasure m p) := by
  change Integrable (fun z : GaussianData m p ↦
    Real.log (Q R z i) - chiSquareLogMean m) _
  exact hlog.sub (integrable_const _)

/-- Exact centering `E h_m(G_i)=0`, using the exact Gamma law. -/
theorem integral_h_m_G_eq_zero (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p)
    (hlog : Integrable (fun z : GaussianData m p ↦ Real.log (Q R z i))
      (standardGaussianDataMeasure m p)) :
    ∫ z, h_m m (G R z i) ∂standardGaussianDataMeasure m p = 0 := by
  change ∫ z, Real.log (Q R z i) - chiSquareLogMean m
    ∂standardGaussianDataMeasure m p = 0
  rw [integral_sub hlog (integrable_const _)]
  rw [integral_log_Q_eq_chiSquareLogMean hm]
  simp

theorem integrable_u_m_G (R : CorrelationMatrix p) (i : Fin p) :
    Integrable (fun z : GaussianData m p ↦ u_m m (G R z i))
      (standardGaussianDataMeasure m p) := by
  simpa only [u_m_G_eq_g] using integrable_g (m := m) R i

theorem integral_u_m_G_eq_zero (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, u_m m (G R z i) ∂standardGaussianDataMeasure m p = 0 := by
  simpa only [u_m_G_eq_g] using integral_g_eq_zero (m := m) R i

theorem integrable_e_m_G (R : CorrelationMatrix p) (i : Fin p)
    (hlog : Integrable (fun z : GaussianData m p ↦ Real.log (Q R z i))
      (standardGaussianDataMeasure m p)) :
    Integrable (fun z : GaussianData m p ↦ e_m m (G R z i))
      (standardGaussianDataMeasure m p) := by
  exact (integrable_h_m_G R i hlog).sub (integrable_u_m_G R i)

/-- Each nonlinear residual is exactly centered, under the minimal
log-integrability hypothesis needed to interpret its expectation. -/
theorem integral_e_m_G_eq_zero (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p)
    (hlog : Integrable (fun z : GaussianData m p ↦ Real.log (Q R z i))
      (standardGaussianDataMeasure m p)) :
    ∫ z, e_m m (G R z i) ∂standardGaussianDataMeasure m p = 0 := by
  change ∫ z, h_m m (G R z i) - u_m m (G R z i)
    ∂standardGaussianDataMeasure m p = 0
  rw [integral_sub (integrable_h_m_G R i hlog)
    (integrable_u_m_G R i)]
  rw [integral_h_m_G_eq_zero hm R i hlog,
    integral_u_m_G_eq_zero]
  simp

/-- The finite nonlinear remainder is integrable if every log energy is. -/
theorem integrable_E_R (R : CorrelationMatrix p)
    (hlog : ∀ i : Fin p,
      Integrable (fun z : GaussianData m p ↦ Real.log (Q R z i))
        (standardGaussianDataMeasure m p)) :
    Integrable (E_R m R) (standardGaussianDataMeasure m p) := by
  unfold E_R
  exact integrable_finsetSum Finset.univ fun i _ ↦
    integrable_e_m_G R i (hlog i)

/-- Exact centering `E E_R=0`. -/
theorem integral_E_R_eq_zero (hm : 0 < m)
    (R : CorrelationMatrix p)
    (hlog : ∀ i : Fin p,
      Integrable (fun z : GaussianData m p ↦ Real.log (Q R z i))
        (standardGaussianDataMeasure m p)) :
    ∫ z, E_R m R z ∂standardGaussianDataMeasure m p = 0 := by
  unfold E_R
  rw [integral_finsetSum Finset.univ fun i _ ↦
    integrable_e_m_G R i (hlog i)]
  simp only [integral_e_m_G_eq_zero hm R _ (hlog _),
    Finset.sum_const_zero]

/-- `M_R` is integrable once the standard log-scatter determinant is. -/
theorem integrable_M_R (R : CorrelationMatrix p)
    (hWint : Integrable (fun z : GaussianData m p ↦ Real.log (W0 z).det)
      (standardGaussianDataMeasure m p)) :
    Integrable (M_R m R) (standardGaussianDataMeasure m p) := by
  unfold M_R
  exact (hWint.sub (integrable_const _)).sub
    (integrable_finsetSum Finset.univ fun i _ ↦ integrable_g R i)

/-- Exact centering `E M_R=0`. -/
theorem integral_M_R_eq_zero (R : CorrelationMatrix p)
    (hWint : Integrable (fun z : GaussianData m p ↦ Real.log (W0 z).det)
      (standardGaussianDataMeasure m p)) :
    ∫ z, M_R m R z ∂standardGaussianDataMeasure m p = 0 := by
  have hsum : Integrable (fun z : GaussianData m p ↦ ∑ i, g m R z i)
      (standardGaussianDataMeasure m p) :=
    integrable_finsetSum Finset.univ fun i _ ↦ integrable_g R i
  unfold M_R
  rw [integral_sub
    (f := fun z : GaussianData m p ↦
      Real.log (W0 z).det - W0LogDetMean m p)
    (g := fun z ↦ ∑ i, g m R z i)
    (hWint.sub (integrable_const _)) hsum]
  rw [integral_sub
    (f := fun z : GaussianData m p ↦ Real.log (W0 z).det)
    (g := fun _ ↦ W0LogDetMean m p)
    hWint (integrable_const _)]
  rw [integral_finsetSum Finset.univ fun i _ ↦ integrable_g R i]
  simp only [integral_g_eq_zero, Finset.sum_const_zero, sub_zero]
  simp [W0LogDetMean]

/-! ## The deterministic center is the actual expectation when integrable -/

/-- Under the explicitly stated log-integrability hypotheses, the sample
log determinant is integrable and its expectation is `logDetCenter`.  These
hypotheses are kept visible because Mathlib currently does not package the
needed Wishart log-determinant or Gamma log-moment integrability theorems. -/
theorem integrable_log_det_sampleCorrelation_and_integral_eq_center
    (hm : 0 < m) (hp : p ≤ m) (R : CorrelationMatrix p)
    (hWint : Integrable (fun z : GaussianData m p ↦
      Real.log (W0 z).det) (standardGaussianDataMeasure m p))
    (hQint : ∀ i : Fin p, Integrable (fun z : GaussianData m p ↦
      Real.log (Q R z i)) (standardGaussianDataMeasure m p)) :
    Integrable (fun z : GaussianData m p ↦
      Real.log (sampleCorrelation R z).det)
      (standardGaussianDataMeasure m p) ∧
    ∫ z, Real.log (sampleCorrelation R z).det
        ∂standardGaussianDataMeasure m p = logDetCenter m R := by
  let μ := standardGaussianDataMeasure m p
  have hsum : Integrable (fun z : GaussianData m p ↦
      ∑ i, Real.log (Q R z i)) μ := by
    exact integrable_finsetSum Finset.univ fun i _ ↦ hQint i
  have hrhs : Integrable (fun z : GaussianData m p ↦
      Real.log R.val.det + Real.log (W0 z).det -
        ∑ i, Real.log (Q R z i)) μ := by
    exact ((integrable_const _).add hWint).sub hsum
  have hae : (fun z : GaussianData m p ↦
      Real.log (sampleCorrelation R z).det) =ᵐ[μ]
      (fun z ↦ Real.log R.val.det + Real.log (W0 z).det -
        ∑ i, Real.log (Q R z i)) := by
    filter_upwards [ae_W0_det_pos hp] with z hz
    exact log_det_sampleCorrelation_eq_population_add R z hz
  have hsamp : Integrable (fun z : GaussianData m p ↦
      Real.log (sampleCorrelation R z).det) μ :=
    hrhs.congr hae.symm
  refine ⟨hsamp, ?_⟩
  rw [integral_congr_ae hae]
  rw [integral_sub
    (f := fun z : GaussianData m p ↦
      Real.log R.val.det + Real.log (W0 z).det)
    (g := fun z ↦ ∑ i, Real.log (Q R z i))
    ((integrable_const _).add hWint) hsum]
  rw [integral_add (integrable_const _) hWint]
  rw [integral_finsetSum Finset.univ fun i _ ↦ hQint i]
  simp only [integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul, integral_log_Q_eq_chiSquareLogMean hm]
  simp [logDetCenter, W0LogDetMean]

/-- Hence the paper's `M_R-E_R` decomposition is literally centered by the
expectation, not merely by a named deterministic constant, whenever the
displayed integrability hypotheses hold. -/
theorem ae_log_det_sub_expectation_eq_M_R_sub_E_R
    (hm : 0 < m) (hp : p ≤ m) (R : CorrelationMatrix p)
    (hWint : Integrable (fun z : GaussianData m p ↦
      Real.log (W0 z).det) (standardGaussianDataMeasure m p))
    (hQint : ∀ i : Fin p, Integrable (fun z : GaussianData m p ↦
      Real.log (Q R z i)) (standardGaussianDataMeasure m p)) :
    ∀ᵐ z ∂standardGaussianDataMeasure m p,
      Real.log (sampleCorrelation R z).det -
        (∫ y, Real.log (sampleCorrelation R y).det
          ∂standardGaussianDataMeasure m p) =
        M_R m R z - E_R m R z := by
  have hcenter :=
    (integrable_log_det_sampleCorrelation_and_integral_eq_center
      hm hp R hWint hQint).2
  filter_upwards [ae_centered_log_det_eq_M_R_sub_E_R hp R] with z hz
  rw [hcenter]
  exact hz



end

end GeneralRDecomposition
end LogdetLean
