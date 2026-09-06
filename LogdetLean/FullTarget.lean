import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LogdetLean.EdgeworthTransfer
import LogdetLean.KolmogorovDistance
/-!
# Formal statement of the full null Edgeworth target

This file defines the two proposition-valued targets without assuming them as
axioms.  They are now proved in `NullUniformEdgeworthTarget.lean` by
`uniformNullEdgeworthTarget_proved` and
`uniformNullSharpKolmogorovTarget_proved`.

The law is constructed recursively as the additive convolution of the laws of
independent logarithms of beta random variables.  Thus independence is built
into the measure itself, rather than postulated for unnamed random variables.
The centering, variance, and third-cumulant magnitude are defined as exact
moments of this law.  This avoids pretending that mathlib already contains the
polygamma identities used to evaluate those moments.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

/-- First beta shape `(m-j+1)/2` in the Bartlett/Haar decomposition. -/
def betaShapeA (m j : ℕ) : ℝ := ((m : ℝ) - (j : ℝ) + 1) / 2

/-- Second beta shape `(j-1)/2` in the Bartlett/Haar decomposition. -/
def betaShapeB (j : ℕ) : ℝ := ((j : ℝ) - 1) / 2

/-- Parameter range in which every beta factor from `j=2` through `p` has
positive shapes. -/
def Admissible (m p : ℕ) : Prop := 2 ≤ p ∧ p ≤ m

/-- Positivity of the first beta shape throughout the admissible triangular
array. -/
theorem betaShapeA_pos_of_le {m j : ℕ} (hjm : j ≤ m) :
    0 < betaShapeA m j := by
  unfold betaShapeA
  have hcast : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
  linarith

/-- Positivity of the second beta shape for every factor `j ≥ 2`. -/
theorem betaShapeB_pos_of_two_le {j : ℕ} (hj : 2 ≤ j) :
    0 < betaShapeB j := by
  unfold betaShapeB
  have hcast : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  linarith

/-- Law of `log B_j`, where `B_j` has the exact beta law from the paper. -/
def logBetaLaw (m j : ℕ) : Measure ℝ :=
  (betaMeasure (betaShapeA m j) (betaShapeB j)).map Real.log

set_option linter.style.haveILetI false in
/-- Every admissible log-beta factor is a probability measure. -/
theorem isProbabilityMeasure_logBetaLaw {m j : ℕ}
    (hjm : j ≤ m) (hj : 2 ≤ j) :
    IsProbabilityMeasure (logBetaLaw m j) := by
  haveI : IsProbabilityMeasure
      (betaMeasure (betaShapeA m j) (betaShapeB j)) :=
    isProbabilityMeasureBeta (betaShapeA_pos_of_le hjm)
      (betaShapeB_pos_of_two_le hj)
  unfold logBetaLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Exact law of `∑_{j=2}^p log B_j`, built by additive convolution.
The values at `p=0,1` are harmless base cases for the recursion. -/
def logBetaSumLaw (m : ℕ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | p + 1 =>
      if 2 ≤ p + 1 then logBetaSumLaw m p ∗ logBetaLaw m (p + 1)
      else Measure.dirac 0

set_option linter.style.haveILetI false in
/-- The recursively convolved exact null law is a probability measure whenever
`p ≤ m`. -/
theorem isProbabilityMeasure_logBetaSumLaw {m p : ℕ} (hpm : p ≤ m) :
    IsProbabilityMeasure (logBetaSumLaw m p) := by
  induction p with
  | zero =>
      simpa [logBetaSumLaw] using
        (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | succ p ih =>
      by_cases hp2 : 2 ≤ p + 1
      · haveI : IsProbabilityMeasure (logBetaSumLaw m p) :=
          ih (by omega)
        haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm hp2
        rw [logBetaSumLaw, if_pos hp2]
        infer_instance
      · rw [logBetaSumLaw, if_neg hp2]
        infer_instance

/-- Exact centering `b_{m,p}` represented as the first moment. -/
def nullCenter (m p : ℕ) : ℝ :=
  ∫ x, x ∂(logBetaSumLaw m p)

/-- Exact variance `V_{m,p}` represented as the centered second moment. -/
def nullVariance (m p : ℕ) : ℝ :=
  ∫ x, (x - nullCenter m p) ^ 2 ∂(logBetaSumLaw m p)

/-- The positive quantity `A_{m,p}` is minus the centered third moment. -/
def nullThirdMagnitude (m p : ℕ) : ℝ :=
  -∫ x, (x - nullCenter m p) ^ 3 ∂(logBetaSumLaw m p)

/-- Law of the exactly centered and variance-normalized null statistic. -/
def standardizedNullLaw (m p : ℕ) : Measure ℝ :=
  (logBetaSumLaw m p).map
    (fun x ↦ (x - nullCenter m p) / Real.sqrt (nullVariance m p))

set_option linter.style.haveILetI false in
/-- Standardization preserves probability mass. -/
theorem isProbabilityMeasure_standardizedNullLaw {m p : ℕ} (hpm : p ≤ m) :
    IsProbabilityMeasure (standardizedNullLaw m p) := by
  haveI : IsProbabilityMeasure (logBetaSumLaw m p) :=
    isProbabilityMeasure_logBetaSumLaw hpm
  unfold standardizedNullLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Standard normal distribution function. -/
def standardNormalCDF (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf (gaussianReal 0 1) x

/-- The signed first Edgeworth correction in the paper. -/
def nullEdgeworthCorrection (m p : ℕ) (x : ℝ) : ℝ :=
  nullThirdMagnitude m p /
      (6 * nullVariance m p ^ (3 / 2 : ℝ)) *
    (1 - x ^ 2) * gaussianPDFReal 0 1 x

/-- Uniform-in-`x` error in the first Edgeworth approximation. -/
def nullEdgeworthError (m p : ℕ) : ℝ :=
  supDistance
    (ProbabilityTheory.cdf (standardizedNullLaw m p))
    (fun x ↦ standardNormalCDF x - nullEdgeworthCorrection m p x)

/-- The standardized third-cumulant scale `λ_{m,p}`. -/
def nullSkewScale (m p : ℕ) : ℝ :=
  nullThirdMagnitude m p / nullVariance m p ^ (3 / 2 : ℝ)

/-- Sequential formulation of the paper's uniform null Edgeworth theorem.

For every sequence `m(p) ≥ p`, the uniform remainder divided by
`λ_{m(p),p}` tends to zero.  The proposition is discharged in
`NullUniformEdgeworthTarget.lean`. -/
def UniformNullEdgeworthTarget : Prop :=
  ∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      Tendsto
        (fun p ↦ nullEdgeworthError (mseq p) p /
          nullSkewScale (mseq p) p)
        atTop (nhds 0)

/-- Sequential formulation of the sharp Kolmogorov equivalent that follows
from the target above once the normal-correction maximizer is established. -/
def UniformNullSharpKolmogorovTarget : Prop :=
  ∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      Tendsto
        (fun p ↦
          kolmogorovDistance
              (standardizedNullLaw (mseq p) p)
              (gaussianReal 0 1) /
            (nullThirdMagnitude (mseq p) p /
              (6 * Real.sqrt (2 * Real.pi) *
                nullVariance (mseq p) p ^ (3 / 2 : ℝ))))
        atTop (nhds 1)

end

end LogdetLean
