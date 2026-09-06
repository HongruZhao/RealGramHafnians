import LogdetLean.Coherence.ModelBonferroniTransfer
/-!
# From mixed factorial moments to the Gaussian coherence joint limit

This module closes the deterministic probability-theory part of the argument.
It identifies the zero-exceedance event with the lower-tail event for the
maximum and then instantiates the abstract factorial Bonferroni transfer.

The remaining statistical obligation is exactly
`AllGapGaussianMixedFactorialTarget`; no independence conclusion is assumed.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- For `p ≥ 2`, the integrated zero-exceedance indicator is exactly the
joint lower-tail probability of the standardized log determinant and the
classical coherence extreme. -/
theorem classical_thresholdJointVoidProbability_eq_jointLowerProbability
    (m p : ℕ) (hp : 2 ≤ p) (z x : ℝ) :
    thresholdJointVoidProbability classicalCoherenceThreshold m p z x =
      gaussianCoherenceJointLowerProbability m p z x := by
  let μ := nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p
  let A : Set (NestedTuple (ObservationSpace (m + 1)) p) :=
    {data | Z0mpStatistic m p data ≤ z ∧ coherenceExtreme m p data ≤ x}
  have hA : MeasurableSet A := by
    exact (measurableSet_le (measurable_Z0mpStatistic m p) measurable_const).inter
      (measurableSet_le (measurable_coherenceExtreme m p) measurable_const)
  change (∫ data, if Z0mpStatistic m p data ≤ z ∧
      coherenceExceedanceCount m p x data = 0 then (1 : ℝ) else 0 ∂μ) =
    μ.real A
  rw [← integral_indicator_one hA]
  apply integral_congr_ae
  filter_upwards [] with data
  by_cases hbulk : Z0mpStatistic m p data ≤ z
  · by_cases hextreme : coherenceExtreme m p data ≤ x
    · have hcount : coherenceExceedanceCount m p x data = 0 :=
        (coherenceExtreme_le_iff_exceedanceCount_eq_zero hp data x).mp hextreme
      simp [A, Set.indicator, hbulk, hextreme, hcount]
    · have hcount : coherenceExceedanceCount m p x data ≠ 0 := by
        intro hzero
        exact hextreme
          ((coherenceExtreme_le_iff_exceedanceCount_eq_zero hp data x).mpr hzero)
      simp [A, Set.indicator, hbulk, hextreme, hcount]
  · simp [A, Set.indicator, hbulk]

/-- The exact mixed factorial-moment target implies the exact all-gap joint
lower-tail factorization target.  This theorem contains the complete
Bonferroni/void-event assembly; its only hypothesis is the still-open
model-specific mixed factorial asymptotic. -/
theorem allGapGaussianJointIndependence_of_mixedFactorial
    (hmixed : AllGapGaussianMixedFactorialTarget) :
    AllGapGaussianJointIndependenceTarget := by
  intro mseq hadm z x
  have hvoid := threshold_joint_void_limit_of_mixed_factorial_limits
    classicalCoherenceThreshold classicalCoherenceIntensity mseq z x
    (fun k ↦ hmixed mseq hadm z x k)
  apply hvoid.congr'
  filter_upwards [hadm] with p hp
  exact classical_thresholdJointVoidProbability_eq_jointLowerProbability
    (mseq p) p hp.1 z x

end

end LogdetLean.Coherence
