import LogdetLean.Coherence.BetaTailTarget
/-!
# Quantitative joint normal--Gumbel targets and deterministic transfer

This module records the finite-`(m,p)` Poisson intensity and separates two
logically different quantitative problems:

1. approximate the joint lower-tail probability by the product of the normal
   CDF and the *exact* finite beta-tail Poisson void probability;
2. replace that finite intensity by the limiting, dimension-free intensity.

The triangle inequality below proves the deterministic assembly.  It does not
postulate either probabilistic estimate and therefore does not turn the
existing qualitative limit into a Berry--Esseen theorem.
-/

namespace LogdetLean.Coherence

noncomputable section

open ProbabilityTheory

/-- Exact expected number of classical-threshold edge exceedances. -/
def finiteCoherenceIntensity (m p : ℕ) (x : ℝ) : ℝ :=
  ((p.choose 2 : ℕ) : ℝ) * betaCorrelationTailProbability m p x

/-- Dimension-free limiting Gumbel-type CDF for the coherence statistic. -/
def limitingCoherenceCDF (x : ℝ) : ℝ :=
  Real.exp (-classicalCoherenceIntensity x)

/-- Product approximation retaining the exact finite beta-tail intensity. -/
def exactIntensityJointApproximation (m p : ℕ) (z x : ℝ) : ℝ :=
  standardNormalCDF z * Real.exp (-finiteCoherenceIntensity m p x)

/-- Product approximation using the dimension-free limiting intensity. -/
def limitingJointApproximation (z x : ℝ) : ℝ :=
  standardNormalCDF z * limitingCoherenceCDF x

/-- Pointwise joint error relative to the exact finite intensity. -/
def exactIntensityJointError (m p : ℕ) (z x : ℝ) : ℝ :=
  |gaussianCoherenceJointLowerProbability m p z x -
    exactIntensityJointApproximation m p z x|

/-- Pointwise joint error relative to the fixed normal--Gumbel product. -/
def limitingJointError (m p : ℕ) (z x : ℝ) : ℝ :=
  |gaussianCoherenceJointLowerProbability m p z x -
    limitingJointApproximation z x|

/-- Sharp signed-cumulant scale of the marginal log-determinant normal
approximation.  The absolute value makes the quantitative envelope total at
all finite indices; on admissible indices the underlying quantity is
nonnegative. -/
def sharpLogdetBerryEsseenScale (m p : ℕ) : ℝ :=
  |nullSkewScale m p / (6 * Real.sqrt (2 * Real.pi))|

/-- Candidate compact-threshold error before replacing the finite Poisson
intensity.  The three summands correspond to the marginal log-determinant
normal error, the conditioned finite-prefix perturbation, and the local
Poisson/overlap error. -/
def exactIntensityJointRateEnvelope (m p : ℕ) : ℝ :=
  sharpLogdetBerryEsseenScale m p +
    |Real.log (p : ℝ) /
      ((m : ℝ) * Real.sqrt (nullVariance m p))| +
    |1 / (p : ℝ)|

/-- Candidate cost of replacing the exact finite intensity by the fixed
Gumbel intensity on a compact `x`-set. -/
def intensityReplacementRateEnvelope (m p : ℕ) : ℝ :=
  |(1 + |Real.log (Real.log (p : ℝ))|) / Real.log (p : ℝ)| +
    |Real.log (p : ℝ) ^ 2 / (m : ℝ)| +
    |1 / (p : ℝ)|

/-- Full candidate compact-threshold normal--Gumbel rate, retaining the exact
dependence on both dimensions. -/
def fixedGumbelJointRateEnvelope (m p : ℕ) : ℝ :=
  exactIntensityJointRateEnvelope m p +
    intensityReplacementRateEnvelope m p

theorem exactIntensityJointRateEnvelope_nonneg (m p : ℕ) :
    0 ≤ exactIntensityJointRateEnvelope m p := by
  unfold exactIntensityJointRateEnvelope sharpLogdetBerryEsseenScale
  positivity

theorem intensityReplacementRateEnvelope_nonneg (m p : ℕ) :
    0 ≤ intensityReplacementRateEnvelope m p := by
  unfold intensityReplacementRateEnvelope
  positivity

/-- Quantitative exact-intensity target on every fixed compact set of maximum
thresholds.  This definition is a proof obligation, not an axiom. -/
def CompactExactIntensityJointBerryEsseenTarget : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (m p : ℕ) (z x : ℝ), 41 ≤ p → p ≤ m → |x| ≤ M →
      exactIntensityJointError m p z x ≤
        C * exactIntensityJointRateEnvelope m p

/-- Quantitative finite-intensity-to-Gumbel target on compact threshold sets.
This definition is a proof obligation, not an axiom. -/
def CompactIntensityReplacementBerryEsseenTarget : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (m p : ℕ) (x : ℝ), 41 ≤ p → p ≤ m → |x| ≤ M →
      |Real.exp (-finiteCoherenceIntensity m p x) -
        Real.exp (-classicalCoherenceIntensity x)| ≤
          C * intensityReplacementRateEnvelope m p

/-- Final compact-threshold joint Berry--Esseen target with the dimension-free
normal--Gumbel product.  This definition is a proof obligation, not an axiom.
-/
def CompactFixedGumbelJointBerryEsseenTarget : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (m p : ℕ) (z x : ℝ), 41 ≤ p → p ≤ m → |x| ≤ M →
      limitingJointError m p z x ≤
        C * fixedGumbelJointRateEnvelope m p

/-- Replacing the finite intensity costs at most the scalar exponential
difference.  This is the deterministic bridge from an exact-intensity joint
bound to the final dimension-free normal--Gumbel bound. -/
theorem limitingJointError_le_exactIntensity_add_expDifference
    (m p : ℕ) (z x : ℝ) :
    limitingJointError m p z x ≤
      exactIntensityJointError m p z x +
        |Real.exp (-finiteCoherenceIntensity m p x) -
          Real.exp (-classicalCoherenceIntensity x)| := by
  have hPhi_nonneg : 0 ≤ standardNormalCDF z := by
    exact ProbabilityTheory.cdf_nonneg _ _
  have hPhi_le : standardNormalCDF z ≤ 1 := by
    exact ProbabilityTheory.cdf_le_one _ _
  calc
    limitingJointError m p z x
        ≤ exactIntensityJointError m p z x +
            |exactIntensityJointApproximation m p z x -
              limitingJointApproximation z x| := by
          unfold limitingJointError exactIntensityJointError
          exact abs_sub_le _ _ _
    _ = exactIntensityJointError m p z x +
          standardNormalCDF z *
            |Real.exp (-finiteCoherenceIntensity m p x) -
              Real.exp (-classicalCoherenceIntensity x)| := by
          rw [show
            exactIntensityJointApproximation m p z x -
                limitingJointApproximation z x =
              standardNormalCDF z *
                (Real.exp (-finiteCoherenceIntensity m p x) -
                  Real.exp (-classicalCoherenceIntensity x)) by
              simp [exactIntensityJointApproximation,
                limitingJointApproximation, limitingCoherenceCDF,
                mul_sub]]
          rw [abs_mul, abs_of_nonneg hPhi_nonneg]
    _ ≤ exactIntensityJointError m p z x +
          |Real.exp (-finiteCoherenceIntensity m p x) -
            Real.exp (-classicalCoherenceIntensity x)| := by
          have habs : 0 ≤
              |Real.exp (-finiteCoherenceIntensity m p x) -
                Real.exp (-classicalCoherenceIntensity x)| := abs_nonneg _
          nlinarith

/-- Abstract quantitative assembly: any exact-intensity joint error bound and
any finite-to-limiting intensity bound add to a final fixed-Gumbel bound. -/
theorem limitingJointError_le_of_two_bounds
    {m p : ℕ} {z x exactErr intensityErr : ℝ}
    (hexact : exactIntensityJointError m p z x ≤ exactErr)
    (hintensity :
      |Real.exp (-finiteCoherenceIntensity m p x) -
        Real.exp (-classicalCoherenceIntensity x)| ≤ intensityErr) :
    limitingJointError m p z x ≤ exactErr + intensityErr := by
  exact (limitingJointError_le_exactIntensity_add_expDifference m p z x).trans
    (add_le_add hexact hintensity)

/-- The two compact quantitative targets assemble into the final fixed-Gumbel
target with no additional probabilistic input. -/
theorem compactFixedGumbelJointBerryEsseen_of_components
    (hexact : CompactExactIntensityJointBerryEsseenTarget)
    (hintensity : CompactIntensityReplacementBerryEsseenTarget) :
    CompactFixedGumbelJointBerryEsseenTarget := by
  intro M hM
  obtain ⟨C₁, hC₁, hbound₁⟩ := hexact M hM
  obtain ⟨C₂, hC₂, hbound₂⟩ := hintensity M hM
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro m p z x hp hpm hx
  have h₁ := hbound₁ m p z x hp hpm hx
  have h₂ := hbound₂ m p x hp hpm hx
  have htransfer := limitingJointError_le_of_two_bounds h₁ h₂
  have hE₁ := exactIntensityJointRateEnvelope_nonneg m p
  have hE₂ := intensityReplacementRateEnvelope_nonneg m p
  unfold fixedGumbelJointRateEnvelope
  calc
    limitingJointError m p z x
        ≤ C₁ * exactIntensityJointRateEnvelope m p +
            C₂ * intensityReplacementRateEnvelope m p := htransfer
    _ ≤ (C₁ + C₂) *
          (exactIntensityJointRateEnvelope m p +
            intensityReplacementRateEnvelope m p) := by
          nlinarith [mul_nonneg hC₁ hE₂, mul_nonneg hC₂ hE₁]

end

end LogdetLean.Coherence
