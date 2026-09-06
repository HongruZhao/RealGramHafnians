import LogdetLean.NullWeakCLT
import LogdetLean.MatrixSphericalExtension
import LogdetLean.Coherence.PairBeta
/-!
# Gaussian coherence model and exact formalization targets

This file freezes the model-specific statements before the remaining proof is
attempted.  The asymptotic index is the number of variables `p`.  An arbitrary
sequence `m p` gives the residual sample dimension, and the only dimensional
assumption in the all-gap target is eventual `Admissible (m p) p`, i.e.
`2 ≤ p ≤ m p`.

Two levels are recorded:

* `ThresholdMixedFactorialTarget` allows an arbitrary threshold normalization
  and limiting rare-event intensity;
* `AllGapGaussianMixedFactorialTarget` and
  `AllGapGaussianJointIndependenceTarget` specialize to the classical
  coherence threshold `4 log p - log log p + x`.

These proposition-valued definitions are goals, not axioms and not theorems.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Module
open scoped BigOperators RealInnerProductSpace

/-- An iterated product of probability measures is again a probability
measure.  The upstream sequential package only needed the weaker `SFinite`
instance, so we record the stronger fact here. -/
instance nestedProductMeasure_isProbability
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (nestedProductMeasure μ n) := by
  induction n with
  | zero =>
      simp only [nestedProductMeasure]
      infer_instance
  | succ n ih =>
      simp only [nestedProductMeasure]
      infer_instance

/-- The centered sample-correlation matrix from `N` raw observations and `p`
independent Gaussian columns, represented through the centered subspace. -/
def centeredCorrelationMatrix (N p : ℕ)
    (z : NestedTuple (ObservationSpace N) p) : Matrix (Fin p) (Fin p) ℝ :=
  normalizedGram (nestedTupleToFin p (centerNested N p z))

/-- The centered sample-correlation matrix is measurable. -/
theorem measurable_centeredCorrelationMatrix (N p : ℕ) :
    Measurable (centeredCorrelationMatrix N p) := by
  exact measurable_normalizedGramFamily.comp
    ((measurable_nestedTupleToFin (α := centeredSubspace N) p).comp
      (measurable_centerNested N p))

/-- Unordered off-diagonal index pairs. -/
def correlationEdges (p : ℕ) : Finset (Fin p × Fin p) :=
  Finset.univ.filter fun e ↦ e.1 < e.2

/-- There is at least one off-diagonal pair when `2 ≤ p`. -/
theorem correlationEdges_nonempty {p : ℕ} (hp : 2 ≤ p) :
    (correlationEdges p).Nonempty := by
  let i : Fin p := ⟨0, by omega⟩
  let j : Fin p := ⟨1, by omega⟩
  refine ⟨(i, j), ?_⟩
  simp [correlationEdges, i, j]

/-- The classical scaled squared-correlation score `m r_ij^2`. -/
def scaledSquaredCorrelationScore (m p : ℕ)
    (z : NestedTuple (ObservationSpace (m + 1)) p)
    (e : Fin p × Fin p) : ℝ :=
  (m : ℝ) * (centeredCorrelationMatrix (m + 1) p z e.1 e.2) ^ 2

/-- Every fixed edge score is measurable. -/
theorem measurable_scaledSquaredCorrelationScore (m p : ℕ)
    (e : Fin p × Fin p) :
    Measurable (fun z ↦ scaledSquaredCorrelationScore m p z e) := by
  unfold scaledSquaredCorrelationScore
  have hentry : Measurable (fun z ↦
      centeredCorrelationMatrix (m + 1) p z e.1 e.2) :=
    (measurable_pi_apply e.2).comp
      ((measurable_pi_apply e.1).comp
        (measurable_centeredCorrelationMatrix (m + 1) p))
  exact measurable_const.mul (hentry.pow_const 2)

/-- Count strict exceedances of an arbitrary deterministic threshold. -/
def thresholdExceedanceCount
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p : ℕ) (x : ℝ)
    (z : NestedTuple (ObservationSpace (m + 1)) p) : ℕ :=
  ∑ e ∈ correlationEdges p,
    if threshold m p x < scaledSquaredCorrelationScore m p z e then 1 else 0

/-- The exceedance count is measurable for every deterministic threshold. -/
theorem measurable_thresholdExceedanceCount
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p : ℕ) (x : ℝ) :
    Measurable (thresholdExceedanceCount threshold m p x) := by
  unfold thresholdExceedanceCount
  apply Finset.measurable_sum
  intro e he
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      (measurable_scaledSquaredCorrelationScore m p e)
  · exact measurable_const
  · exact measurable_const

/-- A void exceedance count means that every edge lies below threshold. -/
theorem thresholdExceedanceCount_eq_zero_iff
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p : ℕ) (x : ℝ)
    (z : NestedTuple (ObservationSpace (m + 1)) p) :
    thresholdExceedanceCount threshold m p x z = 0 ↔
      ∀ e ∈ correlationEdges p,
        scaledSquaredCorrelationScore m p z e ≤ threshold m p x := by
  classical
  simp [thresholdExceedanceCount, not_lt]

/-- Classical coherence threshold for the statistic `m max r_ij^2`. -/
def classicalCoherenceThreshold (_m p : ℕ) (x : ℝ) : ℝ :=
  4 * Real.log (p : ℝ) - Real.log (Real.log (p : ℝ)) + x

/-- The number `N_p(x)` of classical coherence-threshold exceedances. -/
def coherenceExceedanceCount (m p : ℕ) (x : ℝ)
    (z : NestedTuple (ObservationSpace (m + 1)) p) : ℕ :=
  thresholdExceedanceCount classicalCoherenceThreshold m p x z

/-- The maximum scaled squared correlation, totalized to zero when `p < 2`.
For the asymptotic targets `p ≥ 2` eventually. -/
def maximumScaledSquaredCorrelation (m p : ℕ)
    (z : NestedTuple (ObservationSpace (m + 1)) p) : ℝ := by
  classical
  exact if hp : 2 ≤ p then
    (correlationEdges p).sup' (correlationEdges_nonempty hp)
      (scaledSquaredCorrelationScore m p z)
  else 0

/-- Characterization of the finite maximum in the nonempty-edge range. -/
theorem maximumScaledSquaredCorrelation_le_iff
    {m p : ℕ} (hp : 2 ≤ p)
    (z : NestedTuple (ObservationSpace (m + 1)) p) (t : ℝ) :
    maximumScaledSquaredCorrelation m p z ≤ t ↔
      ∀ e ∈ correlationEdges p,
        scaledSquaredCorrelationScore m p z e ≤ t := by
  classical
  unfold maximumScaledSquaredCorrelation
  rw [dif_pos hp, Finset.sup'_le_iff]

/-- The finite maximum is measurable. -/
theorem measurable_maximumScaledSquaredCorrelation (m p : ℕ) :
    Measurable (maximumScaledSquaredCorrelation m p) := by
  classical
  by_cases hp : 2 ≤ p
  · unfold maximumScaledSquaredCorrelation
    simp only [hp, dif_pos, if_pos]
    have hsup : Measurable
        ((correlationEdges p).sup' (correlationEdges_nonempty hp)
          (fun e z ↦ scaledSquaredCorrelationScore m p z e)) := by
      apply Finset.sup'_induction (correlationEdges_nonempty hp)
      · intro f hf g hg
        exact hf.max hg
      · intro e he
        exact measurable_scaledSquaredCorrelationScore m p e
    convert hsup using 1
    funext z
    exact (Finset.sup'_apply (correlationEdges_nonempty hp)
      (fun e z ↦ scaledSquaredCorrelationScore m p z e) z).symm
  · unfold maximumScaledSquaredCorrelation
    simp only [hp, dif_neg, if_neg]
    exact measurable_const

/-- The classical centered coherence extreme statistic. -/
def coherenceExtreme (m p : ℕ)
    (z : NestedTuple (ObservationSpace (m + 1)) p) : ℝ :=
  maximumScaledSquaredCorrelation m p z - 4 * Real.log (p : ℝ) +
    Real.log (Real.log (p : ℝ))

/-- The centered coherence extreme statistic is measurable. -/
theorem measurable_coherenceExtreme (m p : ℕ) :
    Measurable (coherenceExtreme m p) := by
  unfold coherenceExtreme
  exact ((measurable_maximumScaledSquaredCorrelation m p).sub
    measurable_const).add measurable_const

/-- The maximum event is exactly the void event for the classical threshold
whenever off-diagonal edges exist. -/
theorem coherenceExtreme_le_iff_exceedanceCount_eq_zero
    {m p : ℕ} (hp : 2 ≤ p)
    (z : NestedTuple (ObservationSpace (m + 1)) p) (x : ℝ) :
    coherenceExtreme m p z ≤ x ↔
      coherenceExceedanceCount m p x z = 0 := by
  unfold coherenceExceedanceCount
  rw [thresholdExceedanceCount_eq_zero_iff]
  rw [← maximumScaledSquaredCorrelation_le_iff hp]
  unfold coherenceExtreme classicalCoherenceThreshold
  constructor <;> intro h <;> linarith

/-- Limiting Poisson intensity at the classical Gaussian coherence
normalization. -/
def classicalCoherenceIntensity (x : ℝ) : ℝ :=
  (1 / Real.sqrt (8 * Real.pi)) * Real.exp (-x / 2)

/-- The exact mixed factorial moment at an arbitrary threshold family. -/
def thresholdMixedFactorialMoment
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p k : ℕ) (z x : ℝ) : ℝ :=
  ∫ data : NestedTuple (ObservationSpace (m + 1)) p,
    if Z0mpStatistic m p data ≤ z then
      ((thresholdExceedanceCount threshold m p x data).descFactorial k : ℝ)
    else 0
  ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p

/-- The integrand in the mixed factorial moment is measurable. -/
theorem measurable_thresholdMixedFactorialIntegrand
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p k : ℕ) (z x : ℝ) :
    Measurable (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      if Z0mpStatistic m p data ≤ z then
        ((thresholdExceedanceCount threshold m p x data).descFactorial k : ℝ)
      else 0) := by
  have hcount := measurable_thresholdExceedanceCount threshold m p x
  have hfall : Measurable (fun data :
      NestedTuple (ObservationSpace (m + 1)) p ↦
        ((thresholdExceedanceCount threshold m p x data).descFactorial k : ℝ)) :=
    (measurable_of_countable
      (fun n : ℕ ↦ ((n.descFactorial k : ℕ) : ℝ))).comp hcount
  exact hfall.ite
    (measurableSet_le (measurable_Z0mpStatistic m p) measurable_const)
    measurable_const

/-- The exceedance count is bounded by the finite number of edges. -/
theorem thresholdExceedanceCount_le_card_edges
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p : ℕ) (x : ℝ)
    (z : NestedTuple (ObservationSpace (m + 1)) p) :
    thresholdExceedanceCount threshold m p x z ≤ (correlationEdges p).card := by
  simpa [thresholdExceedanceCount] using
    Finset.card_le_card
      (Finset.filter_subset
        (p := fun e ↦ threshold m p x <
          scaledSquaredCorrelationScore m p z e)
        (correlationEdges p))

/-- The mixed factorial integrand is integrable.  This discharges the
expectation well-definedness obligation without adding an assumption. -/
theorem integrable_thresholdMixedFactorialIntegrand
    (threshold : ℕ → ℕ → ℝ → ℝ)
    (m p k : ℕ) (z x : ℝ) :
    Integrable (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
      if Z0mpStatistic m p data ≤ z then
        ((thresholdExceedanceCount threshold m p x data).descFactorial k : ℝ)
      else 0)
      (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) := by
  let C : ℝ := ((correlationEdges p).card : ℝ) ^ k
  apply Integrable.of_bound
    (measurable_thresholdMixedFactorialIntegrand threshold m p k z x).aestronglyMeasurable C
  filter_upwards [] with data
  by_cases hz : Z0mpStatistic m p data ≤ z
  · rw [if_pos hz, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp [C]
    exact_mod_cast (Nat.descFactorial_le_pow
      (thresholdExceedanceCount threshold m p x data) k |>.trans
        (Nat.pow_le_pow_left
          (thresholdExceedanceCount_le_card_edges threshold m p x data) k))
  · rw [if_neg hz, norm_zero]
    positivity

/-- Mixed factorial moment for the classical maximum-correlation
normalization. -/
def gaussianCoherenceMixedFactorialMoment
    (m p k : ℕ) (z x : ℝ) : ℝ :=
  thresholdMixedFactorialMoment classicalCoherenceThreshold m p k z x

/-- Abstract normalization target.  `threshold` may encode a different
maximum normalization and `intensity` its limiting Poisson intensity.  The
normal limit is kept fixed because the bulk statistic is `Z0mpStatistic`.

Quantification over `k`, `z`, and `x` is pointwise: each is fixed before
`p → ∞`. -/
def ThresholdMixedFactorialTarget
    (threshold : ℕ → ℕ → ℝ → ℝ) (intensity : ℝ → ℝ) : Prop :=
  ∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      ∀ (z x : ℝ) (k : ℕ),
        Tendsto
          (fun p ↦ thresholdMixedFactorialMoment threshold
            (mseq p) p k z x)
          atTop (nhds (standardNormalCDF z * intensity x ^ k))

/-- All-nonsingular-gap mixed factorial-moment target, discharged downstream
by `allGapGaussianMixedFactorialTarget`. -/
def AllGapGaussianMixedFactorialTarget : Prop :=
  ThresholdMixedFactorialTarget
    classicalCoherenceThreshold classicalCoherenceIntensity

/-- Exact joint lower-tail probability for the two standardized statistics. -/
def gaussianCoherenceJointLowerProbability
    (m p : ℕ) (z x : ℝ) : ℝ :=
  (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p
    {data | Z0mpStatistic m p data ≤ z ∧
      coherenceExtreme m p data ≤ x}).toReal

/-- All-nonsingular-gap asymptotic-independence target, discharged downstream
by `allGapGaussianJointIndependence`. -/
def AllGapGaussianJointIndependenceTarget : Prop :=
  ∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      ∀ z x : ℝ,
        Tendsto
          (fun p ↦ gaussianCoherenceJointLowerProbability (mseq p) p z x)
          atTop
          (nhds (standardNormalCDF z *
            Real.exp (-classicalCoherenceIntensity x)))

end

end LogdetLean.Coherence
