import LogdetLean.Coherence.MixedMomentZero
import LogdetLean.Coherence.MixedMomentToJoint
/-!
# Reduction of the all-gap target to positive factorial orders

The model-specific rare-event argument naturally treats `k ≥ 1`, whereas
the order-zero case is exactly the marginal log-determinant CLT.  This file
combines those two pieces and then invokes the already proved Bonferroni
assembly.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter

/-- To prove all mixed factorial moments, it is enough to prove the
model-specific statement at every fixed positive order. -/
theorem allGapGaussianMixedFactorialTarget_of_positive
    (hpos : ∀ (mseq : ℕ → ℕ),
      (∀ᶠ p in atTop, Admissible (mseq p) p) →
      ∀ (z x : ℝ) (k : ℕ), 1 ≤ k →
        Tendsto
          (fun p ↦ gaussianCoherenceMixedFactorialMoment
            (mseq p) p k z x)
          atTop
          (nhds (standardNormalCDF z *
            classicalCoherenceIntensity x ^ k))) :
    AllGapGaussianMixedFactorialTarget := by
  intro mseq hadm z x k
  cases k with
  | zero =>
      simpa [gaussianCoherenceMixedFactorialMoment] using
        (tendsto_gaussianCoherenceMixedFactorialMoment_zero
          mseq hadm z x)
  | succ k =>
      exact hpos mseq hadm z x (k + 1) (by omega)

/-- A positive-order mixed-moment proof therefore implies the full
all-gap Gaussian asymptotic-independence theorem. -/
theorem allGapGaussianJointIndependence_of_positive_mixedFactorial
    (hpos : ∀ (mseq : ℕ → ℕ),
      (∀ᶠ p in atTop, Admissible (mseq p) p) →
      ∀ (z x : ℝ) (k : ℕ), 1 ≤ k →
        Tendsto
          (fun p ↦ gaussianCoherenceMixedFactorialMoment
            (mseq p) p k z x)
          atTop
          (nhds (standardNormalCDF z *
            classicalCoherenceIntensity x ^ k))) :
    AllGapGaussianJointIndependenceTarget :=
  allGapGaussianJointIndependence_of_mixedFactorial
    (allGapGaussianMixedFactorialTarget_of_positive hpos)

end

end LogdetLean.Coherence
