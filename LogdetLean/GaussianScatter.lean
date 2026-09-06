import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic
import LogdetLean.GeneralRModel
/-!
# Gaussian data and scatter matrices

Mathlib presently has multivariate Gaussian measures but no native Wishart
distribution.  We therefore define the Gaussian scatter law canonically as a
pushforward: take `m` independent centered Gaussian rows with covariance `R`
and map the data matrix `X` to `Xᴴ X`.

The main result is an exact square-root realization.  If `Z` has independent
standard Gaussian rows and `A = sqrt R`, then `Z A` has independent Gaussian
rows with covariance `R`, and its scatter matrix is exactly

`A * scatter(Z) * A`.

Thus the pushforward law defined here is precisely the classical central
Wishart law, without assuming any unformalized Wishart API.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators MatrixOrder RealInnerProductSpace

/-- Matrices inherit the coordinatewise product measurable space.  Mathlib's
`Matrix` is a reducible-by-theorem synonym rather than an abbreviation, so the
Pi-space instance is made explicit here. -/
instance realMatrixMeasurableSpace (ι κ : Type*) :
    MeasurableSpace (Matrix ι κ ℝ) := by
  unfold Matrix
  infer_instance

namespace CorrelationMatrix

variable {m p : ℕ} (R : CorrelationMatrix p)

/-- The positive square root of a correlation matrix. -/
def covarianceSqrt : Matrix (Fin p) (Fin p) ℝ := CFC.sqrt R.val

/-- The covariance square root is self-adjoint. -/
theorem covarianceSqrt_isSelfAdjoint : IsSelfAdjoint R.covarianceSqrt :=
  (CFC.sqrt_nonneg R.val).isSelfAdjoint

@[simp]
theorem covarianceSqrt_conjTranspose : R.covarianceSqrtᴴ = R.covarianceSqrt :=
  R.covarianceSqrt_isSelfAdjoint

theorem covarianceSqrt_apply_symm (i j : Fin p) :
    R.covarianceSqrt i j = R.covarianceSqrt j i := by
  have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A j i)
    R.covarianceSqrt_conjTranspose
  simpa using h

/-- Squaring the positive square root recovers the covariance matrix. -/
theorem covarianceSqrt_mul_self :
    R.covarianceSqrt * R.covarianceSqrt = R.val := by
  exact CFC.sqrt_mul_sqrt_self R.val R.posSemidef.nonneg

/-- Apply the covariance square root to one standard Gaussian vector. -/
def correlateObservation (z : Observation p) : Observation p :=
  toEuclideanCLM (𝕜 := ℝ) R.covarianceSqrt z

theorem measurable_correlateObservation : Measurable R.correlateObservation := by
  unfold correlateObservation
  fun_prop

/-- A covariance-square-root image of a standard Gaussian has exactly the
multivariate Gaussian law with covariance `R`. -/
theorem map_correlateObservation_stdGaussian :
    Measure.map R.correlateObservation (stdGaussian (Observation p)) =
      R.gaussianMeasure := by
  change Measure.map (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R.val))
      (stdGaussian (Observation p)) =
    Measure.map (fun x ↦ (0 : Observation p) +
      toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R.val) x)
      (stdGaussian (Observation p))
  simp

end CorrelationMatrix

/-- Space of `m` observations in dimension `p`, represented by rows. -/
abbrev GaussianData (m p : ℕ) := Fin m → CorrelationMatrix.Observation p

/-- Product law of `m` independent standard Gaussian rows. -/
def standardGaussianDataMeasure (m p : ℕ) : Measure (GaussianData m p) :=
  Measure.pi fun _ : Fin m ↦ stdGaussian (CorrelationMatrix.Observation p)

instance standardGaussianDataMeasure_isProbabilityMeasure (m p : ℕ) :
    IsProbabilityMeasure (standardGaussianDataMeasure m p) := by
  unfold standardGaussianDataMeasure
  infer_instance

/-- Product law of `m` independent Gaussian rows with covariance `R`. -/
def correlatedGaussianDataMeasure {p : ℕ} (m : ℕ) (R : CorrelationMatrix p) :
    Measure (GaussianData m p) :=
  Measure.pi fun _ : Fin m ↦ R.gaussianMeasure

instance correlatedGaussianDataMeasure_isProbabilityMeasure {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) :
    IsProbabilityMeasure (correlatedGaussianDataMeasure m R) := by
  unfold correlatedGaussianDataMeasure
  infer_instance

/-- Each row projection has exactly the prescribed multivariate Gaussian law. -/
theorem measurePreserving_correlatedGaussianData_row {m p : ℕ}
    (R : CorrelationMatrix p) (k : Fin m) :
    MeasurePreserving (fun x : GaussianData m p ↦ x k)
      (correlatedGaussianDataMeasure m R) R.gaussianMeasure := by
  unfold correlatedGaussianDataMeasure
  exact MeasureTheory.measurePreserving_eval (fun _ : Fin m ↦ R.gaussianMeasure) k

/-- Each scalar data entry has a standard real Gaussian marginal. -/
theorem measurePreserving_correlatedGaussianData_entry {m p : ℕ}
    (R : CorrelationMatrix p) (k : Fin m) (i : Fin p) :
    MeasurePreserving (fun x : GaussianData m p ↦ x k i)
      (correlatedGaussianDataMeasure m R) (gaussianReal 0 1) := by
  exact (R.measurePreserving_eval i).comp
    (measurePreserving_correlatedGaussianData_row R k)

/-- Within each row, coordinate covariance is exactly `R`. -/
theorem covariance_correlatedGaussianData_entry {m p : ℕ}
    (R : CorrelationMatrix p) (k : Fin m) (i j : Fin p) :
    cov[fun x : GaussianData m p ↦ x k i, fun x ↦ x k j;
      correlatedGaussianDataMeasure m R] = R.val i j := by
  have hrow := (measurePreserving_correlatedGaussianData_row R k).hasLaw
  simpa [Function.comp_def] using
    (hrow.covariance_fun_comp
      (show AEMeasurable (fun x : CorrelationMatrix.Observation p ↦ x i)
        R.gaussianMeasure by fun_prop)
      (show AEMeasurable (fun x : CorrelationMatrix.Observation p ↦ x j)
        R.gaussianMeasure by fun_prop)).trans (R.covariance_eval i j)

/-- Apply the covariance square root independently to each data row. -/
def correlateRows {m p : ℕ} (R : CorrelationMatrix p) :
    GaussianData m p → GaussianData m p :=
  fun z k ↦ R.correlateObservation (z k)

theorem measurable_correlateRows {m p : ℕ} (R : CorrelationMatrix p) :
    Measurable (correlateRows (m := m) R) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  exact R.measurable_correlateObservation.comp (measurable_pi_apply k)

/-- Exact product-law realization of correlated Gaussian data from standard
Gaussian data. -/
theorem map_correlateRows_standardGaussianDataMeasure {m p : ℕ}
    (R : CorrelationMatrix p) :
    Measure.map (correlateRows (m := m) R) (standardGaussianDataMeasure m p) =
      correlatedGaussianDataMeasure m R := by
  let _ (k : Fin m) : IsProbabilityMeasure
      ((stdGaussian (CorrelationMatrix.Observation p)).map R.correlateObservation) :=
    Measure.isProbabilityMeasure_map R.measurable_correlateObservation.aemeasurable
  change Measure.map
      (fun z : GaussianData m p ↦ fun k ↦ R.correlateObservation (z k))
      (Measure.pi fun _ : Fin m ↦ stdGaussian (CorrelationMatrix.Observation p)) =
    Measure.pi fun _ : Fin m ↦ R.gaussianMeasure
  rw [Measure.pi_map_pi
    (fun _ ↦ R.measurable_correlateObservation.aemeasurable)]
  congr 1
  funext k
  exact R.map_correlateObservation_stdGaussian

/-- The ordinary rectangular data matrix, with observations in rows. -/
def dataMatrix {m p : ℕ} (x : GaussianData m p) :
    Matrix (Fin m) (Fin p) ℝ :=
  fun k i ↦ x k i

@[simp]
theorem dataMatrix_apply {m p : ℕ} (x : GaussianData m p)
    (k : Fin m) (i : Fin p) : dataMatrix x k i = x k i := rfl

theorem measurable_dataMatrix {m p : ℕ} :
    Measurable (dataMatrix : GaussianData m p → Matrix (Fin m) (Fin p) ℝ) := by
  unfold dataMatrix
  fun_prop

/-- The unnormalized scatter matrix `Xᴴ X`. -/
def scatterMatrix {m p : ℕ} (x : GaussianData m p) :
    Matrix (Fin p) (Fin p) ℝ :=
  (dataMatrix x)ᴴ * dataMatrix x

@[simp]
theorem scatterMatrix_apply {m p : ℕ} (x : GaussianData m p)
    (i j : Fin p) :
    scatterMatrix x i j = ∑ k, x k i * x k j := by
  simp [scatterMatrix, Matrix.mul_apply]

theorem measurable_scatterMatrix {m p : ℕ} :
    Measurable (scatterMatrix : GaussianData m p → Matrix (Fin p) (Fin p) ℝ) := by
  refine measurable_pi_iff.mpr fun i ↦ measurable_pi_iff.mpr fun j ↦ ?_
  simp only [scatterMatrix_apply]
  exact Finset.measurable_sum _ fun k _ ↦ by fun_prop

/-- Every realized scatter matrix is positive semidefinite. -/
theorem scatterMatrix_posSemidef {m p : ℕ} (x : GaussianData m p) :
    (scatterMatrix x).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self (dataMatrix x)

/-- The scatter matrix is symmetric. -/
theorem scatterMatrix_isHermitian {m p : ℕ} (x : GaussianData m p) :
    (scatterMatrix x).IsHermitian :=
  (scatterMatrix_posSemidef x).isHermitian

/-- Correlating rows is right multiplication of the rectangular standard-data
matrix by the self-adjoint covariance square root. -/
theorem dataMatrix_correlateRows {m p : ℕ} (R : CorrelationMatrix p)
    (z : GaussianData m p) :
    dataMatrix (correlateRows R z) = dataMatrix z * R.covarianceSqrt := by
  ext k i
  simp only [dataMatrix_apply, correlateRows,
    CorrelationMatrix.correlateObservation, ofLp_toEuclideanCLM,
    Matrix.mul_apply]
  rw [show R.covarianceSqrt *ᵥ (z k) =
      fun i ↦ ∑ j, R.covarianceSqrt i j * z k j by rfl]
  simp only
  apply Finset.sum_congr rfl
  intro j hj
  rw [R.covarianceSqrt_apply_symm i j, mul_comm]

/-- Deterministic square-root factorization of every correlated scatter
realization. -/
theorem scatterMatrix_correlateRows {m p : ℕ} (R : CorrelationMatrix p)
    (z : GaussianData m p) :
    scatterMatrix (correlateRows R z) =
      R.covarianceSqrt * scatterMatrix z * R.covarianceSqrt := by
  rw [scatterMatrix, dataMatrix_correlateRows, Matrix.conjTranspose_mul,
    R.covarianceSqrt_conjTranspose, scatterMatrix]
  calc
    (R.covarianceSqrt * (dataMatrix z)ᴴ) *
        (dataMatrix z * R.covarianceSqrt) =
        ((R.covarianceSqrt * (dataMatrix z)ᴴ) * dataMatrix z) *
          R.covarianceSqrt :=
      (Matrix.mul_assoc (R.covarianceSqrt * (dataMatrix z)ᴴ)
        (dataMatrix z) R.covarianceSqrt).symm
    _ = (R.covarianceSqrt * ((dataMatrix z)ᴴ * dataMatrix z)) *
          R.covarianceSqrt := by
      exact congrArg (fun S ↦ S * R.covarianceSqrt)
        (Matrix.mul_assoc R.covarianceSqrt (dataMatrix z)ᴴ (dataMatrix z))

/-- The central Gaussian scatter (Wishart) law, defined without a primitive
Wishart distribution as the pushforward of independent Gaussian rows. -/
def gaussianScatterLaw {p : ℕ} (m : ℕ) (R : CorrelationMatrix p) :
    Measure (Matrix (Fin p) (Fin p) ℝ) :=
  Measure.map scatterMatrix (correlatedGaussianDataMeasure m R)

instance gaussianScatterLaw_isProbabilityMeasure {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) :
    IsProbabilityMeasure (gaussianScatterLaw m R) := by
  unfold gaussianScatterLaw
  exact Measure.isProbabilityMeasure_map measurable_scatterMatrix.aemeasurable

/-- Canonical exact-law statement for the scatter statistic. -/
theorem hasLaw_scatterMatrix {m p : ℕ} (R : CorrelationMatrix p) :
    HasLaw (scatterMatrix : GaussianData m p → Matrix (Fin p) (Fin p) ℝ)
      (gaussianScatterLaw m R) (correlatedGaussianDataMeasure m R) where
  aemeasurable := measurable_scatterMatrix.aemeasurable
  map_eq := rfl

/-- Standard (identity-covariance) scatter law. -/
def standardGaussianScatterLaw (m p : ℕ) :
    Measure (Matrix (Fin p) (Fin p) ℝ) :=
  gaussianScatterLaw m (CorrelationMatrix.identity p)

/-- The identity-covariance definition agrees with the direct pushforward of
independent standard Gaussian rows. -/
theorem standardGaussianScatterLaw_eq_map (m p : ℕ) :
    standardGaussianScatterLaw m p =
      Measure.map scatterMatrix (standardGaussianDataMeasure m p) := by
  unfold standardGaussianScatterLaw gaussianScatterLaw
  congr 1
  unfold correlatedGaussianDataMeasure standardGaussianDataMeasure
  congr 1
  funext k
  simp [CorrelationMatrix.gaussianMeasure]

/-- Congruence transform on square matrices by the positive covariance square
root. -/
def scatterCongruence {p : ℕ} (R : CorrelationMatrix p)
    (S : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  R.covarianceSqrt * S * R.covarianceSqrt

theorem measurable_scatterCongruence {p : ℕ} (R : CorrelationMatrix p) :
    Measurable (scatterCongruence R) := by
  refine measurable_pi_iff.mpr fun i ↦ measurable_pi_iff.mpr fun j ↦ ?_
  change Measurable (fun S : Matrix (Fin p) (Fin p) ℝ ↦
    (scatterCongruence R S) i j)
  simp only [scatterCongruence, Matrix.mul_apply]
  have hcoord (a b : Fin p) :
      Measurable (fun S : Matrix (Fin p) (Fin p) ℝ ↦ S a b) :=
    (measurable_pi_apply b).comp (measurable_pi_apply a)
  exact Finset.measurable_sum _ fun k _ ↦
    (Finset.measurable_sum _ fun a _ ↦
      (hcoord a k).const_mul (R.covarianceSqrt i a)).mul_const
        (R.covarianceSqrt k j)

/-- Exact square-root realization of the central Gaussian scatter law.  This
is the usual representation `Wishart_p(m,R) = sqrt(R) * Wishart_p(m,I) *
sqrt(R)`, stated entirely in terms of measures already available in Mathlib. -/
theorem gaussianScatterLaw_eq_map_standard {m p : ℕ}
    (R : CorrelationMatrix p) :
    gaussianScatterLaw m R =
      Measure.map (scatterCongruence R) (standardGaussianScatterLaw m p) := by
  rw [standardGaussianScatterLaw_eq_map]
  unfold gaussianScatterLaw
  rw [← map_correlateRows_standardGaussianDataMeasure R]
  rw [Measure.map_map measurable_scatterMatrix (measurable_correlateRows R)]
  rw [Measure.map_map (measurable_scatterCongruence R) measurable_scatterMatrix]
  apply Measure.map_congr
  filter_upwards [] with z
  exact scatterMatrix_correlateRows R z

end

end LogdetLean
