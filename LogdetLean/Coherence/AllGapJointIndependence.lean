import LogdetLean.Coherence.CanonicalMatchingFactorization
import LogdetLean.Coherence.ConcreteOverlap
import LogdetLean.Coherence.MixedMomentAssembly
import LogdetLean.Coherence.MixedMomentPositiveReduction
/-!
# Completed all-gap Gaussian coherence independence theorem

This module closes the model-specific mixed factorial-moment argument.  For
positive fixed order, every matching summand is factored by the canonical
conditional CLT and the complete nonmatching contribution is negligible.
The order-zero theorem and the Bonferroni/void assembly then give the exact
joint lower-tail limit.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory

/-- The central mixed factorial-moment limit at every positive fixed order. -/
theorem tendsto_gaussianCoherenceMixedFactorialMoment_positive
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (z x : ℝ) :
    Tendsto
      (fun p ↦ gaussianCoherenceMixedFactorialMoment
        (mseq p) p k z x)
      atTop
      (nhds (standardNormalCDF z *
        classicalCoherenceIntensity x ^ k)) := by
  apply tendsto_gaussianCoherenceMixedFactorialMoment_of_matching_overlap
    k hadm z x
    (fun p ↦ canonicalConditionedZ0mpCDFOrGaussian
      k (mseq p) p x z)
  · exact tendsto_canonicalConditionedZ0mpCDFOrGaussian k hk hadm x z
  · have hs0 := eventually_canonicalCenteredGaussianMatchingEvent_ne_zero
      k hadm x
    filter_upwards [hadm, hs0] with p hp hs0p
    intro edges hedges
    exact orderedMatchingJointEvent_probability_factorization_of_mem
      (mseq p) p k (hp.1.trans hp.2) hp.2 z x edges hedges
      (by simpa [canonicalCenteredMatchingPrefixEvent] using hs0p)
  · exact tendsto_gaussianOrderedTupleJoint_overlap_zero
      k hk hadm z x

/-- The full all-gap mixed factorial target, including order zero. -/
theorem allGapGaussianMixedFactorialTarget :
    AllGapGaussianMixedFactorialTarget := by
  apply allGapGaussianMixedFactorialTarget_of_positive
  intro mseq hadm z x k hk
  exact tendsto_gaussianCoherenceMixedFactorialMoment_positive
    k hk hadm z x

/-- **All-gap Gaussian asymptotic independence.**  Along every sequence
`p → ∞` with eventually `2 ≤ p ≤ m(p)`, the standardized sample-correlation
log determinant and the classically normalized maximum squared sample
correlation have the product lower-tail limit. -/
theorem allGapGaussianJointIndependence :
    AllGapGaussianJointIndependenceTarget :=
  allGapGaussianJointIndependence_of_positive_mixedFactorial (by
    intro mseq hadm z x k hk
    exact tendsto_gaussianCoherenceMixedFactorialMoment_positive
      k hk hadm z x)

end

end LogdetLean.Coherence
