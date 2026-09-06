import LogdetLean.Coherence.ModelAndTargets
import LogdetLean.Coherence.FactorialVoidLimit
/-!
# Model Bonferroni bounds and the abstract threshold transfer theorem

This module instantiates the finite Bonferroni inequalities on the exact
Gaussian data space.  Consequently, the only hypothesis of the final transfer
theorem is the model-specific mixed factorial-moment limit.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

/-- Probability of the bulk event together with no threshold exceedance,
written as an integral of its indicator. -/
def thresholdJointVoidProbability
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p : ℕ) (z x : ℝ) : ℝ :=
  ∫ data : NestedTuple (ObservationSpace (m + 1)) p,
    if Z0mpStatistic m p data ≤ z ∧
        thresholdExceedanceCount threshold m p x data = 0 then 1 else 0
  ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p

/-- The void-event integrand is measurable. -/
theorem measurable_thresholdJointVoidIntegrand
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p : ℕ) (z x : ℝ) :
    Measurable (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      if Z0mpStatistic m p data ≤ z ∧
          thresholdExceedanceCount threshold m p x data = 0 then
        (1 : ℝ) else 0) := by
  apply Measurable.ite
  · exact (measurableSet_le (measurable_Z0mpStatistic m p) measurable_const).inter
      (measurable_thresholdExceedanceCount threshold m p x
        (measurableSet_singleton 0))
  · exact measurable_const
  · exact measurable_const

/-- The void-event integrand is integrable. -/
theorem integrable_thresholdJointVoidIntegrand
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p : ℕ) (z x : ℝ) :
    Integrable (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      if Z0mpStatistic m p data ≤ z ∧
          thresholdExceedanceCount threshold m p x data = 0 then
        (1 : ℝ) else 0)
      (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) := by
  apply Integrable.of_bound
    (measurable_thresholdJointVoidIntegrand threshold m p z x).aestronglyMeasurable 1
  filter_upwards [] with data
  split <;> simp

/-- Integral form of a fixed factorial partial sum. -/
theorem mixedFactorialPartialSum_eq_integral
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p : ℕ) (z x : ℝ) (J n : ℕ) :
    mixedFactorialPartialSum
        (fun _ k ↦ thresholdMixedFactorialMoment threshold m p k z x)
        n J =
      ∫ data : NestedTuple (ObservationSpace (m + 1)) p,
        if Z0mpStatistic m p data ≤ z then
          alternatingFactorialSum
            (thresholdExceedanceCount threshold m p x data) J
        else 0
      ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p := by
  let μ := nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p
  let f : ℕ → NestedTuple (ObservationSpace (m + 1)) p → ℝ :=
    fun k data ↦ if Z0mpStatistic m p data ≤ z then
      ((thresholdExceedanceCount threshold m p x data).descFactorial k : ℝ)
      else 0
  have hf (k : ℕ) : Integrable (f k) μ := by
    exact integrable_thresholdMixedFactorialIntegrand threshold m p k z x
  unfold mixedFactorialPartialSum thresholdMixedFactorialMoment
  change (∑ k ∈ Finset.range (J + 1),
      (-1 : ℝ) ^ k / ↑k.factorial * ∫ data, f k data ∂μ) = _
  calc
    (∑ k ∈ Finset.range (J + 1),
        (-1 : ℝ) ^ k / ↑k.factorial * ∫ data, f k data ∂μ) =
        ∑ k ∈ Finset.range (J + 1),
          ∫ data, ((-1 : ℝ) ^ k / ↑k.factorial) * f k data ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul]
    _ = ∫ data, ∑ k ∈ Finset.range (J + 1),
          ((-1 : ℝ) ^ k / ↑k.factorial) * f k data ∂μ := by
      rw [integral_finsetSum]
      intro k hk
      exact (hf k).const_mul _
    _ = ∫ data,
          if Z0mpStatistic m p data ≤ z then
            alternatingFactorialSum
              (thresholdExceedanceCount threshold m p x data) J
          else 0 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with data
      by_cases hbulk : Z0mpStatistic m p data ≤ z
      · simp [f, hbulk, alternatingFactorialSum]
      · simp [f, hbulk]

/-- Exact odd/even Bonferroni bounds for the Gaussian mixed moments. -/
theorem thresholdMixedFactorial_bonferroni
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p : ℕ) (z x : ℝ) (K n : ℕ) :
    mixedFactorialPartialSum
        (fun _ k ↦ thresholdMixedFactorialMoment threshold m p k z x)
        n (2 * K + 1) ≤
      thresholdJointVoidProbability threshold m p z x ∧
    thresholdJointVoidProbability threshold m p z x ≤
      mixedFactorialPartialSum
        (fun _ k ↦ thresholdMixedFactorialMoment threshold m p k z x)
        n (2 * K) := by
  let μ := nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p
  let partialSum : ℕ → NestedTuple (ObservationSpace (m + 1)) p → ℝ :=
    fun J data ↦ if Z0mpStatistic m p data ≤ z then
      alternatingFactorialSum
        (thresholdExceedanceCount threshold m p x data) J
      else 0
  let void : NestedTuple (ObservationSpace (m + 1)) p → ℝ :=
    fun data ↦ if Z0mpStatistic m p data ≤ z ∧
        thresholdExceedanceCount threshold m p x data = 0 then 1 else 0
  have hpartial (J : ℕ) : Integrable (partialSum J) μ := by
    have hsum : Integrable (fun data ↦
        ∑ k ∈ Finset.range (J + 1),
          ((-1 : ℝ) ^ k / ↑k.factorial) *
            (if Z0mpStatistic m p data ≤ z then
              ((thresholdExceedanceCount threshold m p x data).descFactorial k : ℝ)
             else 0)) μ := by
      apply integrable_finsetSum
      intro k hk
      exact (integrable_thresholdMixedFactorialIntegrand
        threshold m p k z x).const_mul _
    apply hsum.congr
    filter_upwards [] with data
    by_cases hbulk : Z0mpStatistic m p data ≤ z
    · simp [partialSum, alternatingFactorialSum, hbulk]
    · simp [partialSum, hbulk]
  have hvoid : Integrable void μ :=
    integrable_thresholdJointVoidIntegrand threshold m p z x
  have hpoint (data : NestedTuple (ObservationSpace (m + 1)) p) :
      partialSum (2 * K + 1) data ≤ void data ∧
        void data ≤ partialSum (2 * K) data := by
    by_cases hbulk : Z0mpStatistic m p data ≤ z
    · simpa [partialSum, void, hbulk] using
        alternatingFactorialSum_bonferroni
          (thresholdExceedanceCount threshold m p x data) K
    · simp [partialSum, void, hbulk]
  rw [mixedFactorialPartialSum_eq_integral,
    mixedFactorialPartialSum_eq_integral]
  change (∫ data, partialSum (2 * K + 1) data ∂μ) ≤
      (∫ data, void data ∂μ) ∧
    (∫ data, void data ∂μ) ≤ (∫ data, partialSum (2 * K) data ∂μ)
  exact ⟨integral_mono (hpartial _) hvoid (fun data ↦ (hpoint data).1),
    integral_mono hvoid (hpartial _) (fun data ↦ (hpoint data).2)⟩

/-- **Abstract threshold transfer theorem.**  For an arbitrary maximum
normalization, the model-specific mixed factorial-moment limits imply the
joint Gaussian-times-Poisson-void limit. -/
theorem threshold_joint_void_limit_of_mixed_factorial_limits
    (threshold : ℕ → ℕ → ℝ → ℝ) (intensity : ℝ → ℝ)
    (mseq : ℕ → ℕ) (z x : ℝ)
    (hmom : ∀ k,
      Tendsto
        (fun p ↦ thresholdMixedFactorialMoment threshold
          (mseq p) p k z x)
        atTop (nhds (standardNormalCDF z * intensity x ^ k))) :
    Tendsto
      (fun p ↦ thresholdJointVoidProbability threshold (mseq p) p z x)
      atTop
      (nhds (standardNormalCDF z * Real.exp (-intensity x))) := by
  apply tendsto_void_of_mixed_factorial_limits
    (fun p k ↦ thresholdMixedFactorialMoment threshold (mseq p) p k z x)
    (fun p ↦ thresholdJointVoidProbability threshold (mseq p) p z x)
    (standardNormalCDF z) (intensity x) hmom
  intro p K
  exact thresholdMixedFactorial_bonferroni threshold
    (mseq p) p z x K p

end

end LogdetLean.Coherence
