import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
/-!
# Correlation matrices and Gaussian observations

This file introduces the finite-dimensional parameter and probability model
used by the general-correlation part of the log-determinant problem.  A
`CorrelationMatrix p` is a real positive-definite `p x p` matrix with unit
diagonal.  The associated observation law is Mathlib's multivariate Gaussian
measure with mean zero and that covariance matrix.

No Wishart distribution is assumed here.  The later scatter module defines the
relevant pushforward law directly from independent Gaussian observations.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators MatrixOrder RealInnerProductSpace

/-- A real positive-definite correlation matrix of size `p`.  Positive
definiteness already includes Hermitian symmetry in Mathlib's definition. -/
structure CorrelationMatrix (p : ℕ) where
  /-- The underlying matrix. -/
  val : Matrix (Fin p) (Fin p) ℝ
  /-- Strict positive definiteness. -/
  posDef : val.PosDef
  /-- Every marginal variance is one. -/
  diag_one : ∀ i, val i i = 1

namespace CorrelationMatrix

variable {p : ℕ} (R : CorrelationMatrix p)

instance : Coe (CorrelationMatrix p) (Matrix (Fin p) (Fin p) ℝ) := ⟨val⟩

@[ext]
theorem ext {R S : CorrelationMatrix p} (h : R.val = S.val) : R = S := by
  cases R
  cases S
  cases h
  rfl

/-- A correlation matrix is positive semidefinite. -/
theorem posSemidef : R.val.PosSemidef := R.posDef.posSemidef

/-- A real correlation matrix is symmetric. -/
theorem isHermitian : R.val.IsHermitian := R.posDef.isHermitian

theorem transpose_eq : R.valᵀ = R.val := by
  simpa [Matrix.IsHermitian] using R.isHermitian

/-- A correlation matrix has strictly positive determinant. -/
theorem det_pos : 0 < R.val.det := R.posDef.det_pos

/-- In particular, a correlation matrix is invertible. -/
theorem isUnit : IsUnit R.val := R.posDef.isUnit

@[simp]
theorem apply_self (i : Fin p) : R.val i i = 1 := R.diag_one i

/-- The identity matrix is a correlation matrix. -/
def identity (p : ℕ) : CorrelationMatrix p where
  val := 1
  posDef := Matrix.PosDef.one
  diag_one := by simp

@[simp]
theorem identity_val (p : ℕ) : (identity p).val = 1 := rfl

/-- Euclidean coordinate space for one `p`-variate observation. -/
abbrev Observation (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- The centered multivariate Gaussian law with correlation matrix `R`. -/
def gaussianMeasure : Measure (Observation p) :=
  multivariateGaussian 0 R.val

instance gaussianMeasure_isProbabilityMeasure : IsProbabilityMeasure R.gaussianMeasure :=
  by
    change IsProbabilityMeasure (multivariateGaussian (0 : Observation p) R.val)
    infer_instance

/-- The Gaussian law has mean zero. -/
@[simp]
theorem integral_id_gaussianMeasure :
    ∫ x, x ∂R.gaussianMeasure = 0 := by
  simp [gaussianMeasure]

/-- Coordinate covariance is exactly the specified correlation matrix. -/
theorem covariance_eval (i j : Fin p) :
    cov[fun x : Observation p ↦ x i, fun x ↦ x j; R.gaussianMeasure] = R.val i j := by
  exact covariance_eval_multivariateGaussian R.posSemidef i j

/-- Every coordinate has variance one. -/
@[simp]
theorem variance_eval (i : Fin p) :
    Var[fun x : Observation p ↦ x i; R.gaussianMeasure] = 1 := by
  unfold gaussianMeasure
  rw [variance_eval_multivariateGaussian R.posSemidef, R.apply_self]

/-- Every coordinate marginal is a standard real Gaussian. -/
theorem measurePreserving_eval (i : Fin p) :
    MeasurePreserving (fun x : Observation p ↦ x i) R.gaussianMeasure
      (gaussianReal 0 1) := by
  simpa [gaussianMeasure, R.apply_self] using
    (measurePreserving_eval_multivariateGaussian R.posSemidef
      (i := i) (μ := (0 : Observation p)))

/-- Exact characteristic function of one correlated Gaussian observation. -/
theorem charFun_gaussianMeasure (t : Observation p) :
    charFun R.gaussianMeasure t = Complex.exp (-(t ⬝ᵥ R.val *ᵥ t) / 2) := by
  rw [gaussianMeasure,
    charFun_multivariateGaussian (μ := (0 : Observation p)) R.posSemidef]
  congr 1
  simp
  ring

end CorrelationMatrix

end

end LogdetLean
