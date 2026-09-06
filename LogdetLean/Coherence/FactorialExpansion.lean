import LogdetLean.Coherence.MatchingAndOverlap
import LogdetLean.Coherence.ModelAndTargets
/-!
# Exact expansion of an exceedance-count falling factorial

For a finite active edge set `S`, `(card S)_k` counts ordered embeddings of
`Fin k` into `S`.  Equivalently it is the sum, over ordered distinct edge
tuples, of the indicator that every selected edge is active.  This is the
finite identity underneath the mixed factorial-moment argument.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Embeddings into a finite subtype are equivalent to ambient embeddings
whose entire range lies in the finite set. -/
def embeddingsIntoFinsetEquiv
    {α : Type*} [DecidableEq α] (s : Finset α) (k : ℕ) :
    (Fin k ↪ {x : α // x ∈ s}) ≃
      {f : Fin k ↪ α // ∀ i, f i ∈ s} where
  toFun f :=
    ⟨f.trans ⟨Subtype.val, Subtype.val_injective⟩,
      fun i ↦ (f i).property⟩
  invFun f :=
    ⟨fun i ↦ ⟨f.1 i, f.2 i⟩,
      fun _i _j hij ↦ f.1.injective (congrArg Subtype.val hij)⟩
  left_inv f := by ext i; rfl
  right_inv f := by ext i; rfl

/-- Pure counting form of the falling-factorial expansion. -/
theorem descFactorial_card_eq_sum_embeddings_indicator
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (k : ℕ) :
    s.card.descFactorial k =
      ∑ f : Fin k ↪ α, if (∀ i, f i ∈ s) then 1 else 0 := by
  calc
    s.card.descFactorial k = Fintype.card (Fin k ↪ {x : α // x ∈ s}) :=
      descFactorial_card_eq_card_orderedSelections s k
    _ = Fintype.card {f : Fin k ↪ α // ∀ i, f i ∈ s} :=
      Fintype.card_congr (embeddingsIntoFinsetEquiv s k)
    _ = ∑ f : Fin k ↪ α, if (∀ i, f i ∈ s) then 1 else 0 := by
      rw [Fintype.card_subtype]
      rw [Finset.card_filter]

/-- Active unordered correlation edges at a deterministic threshold. -/
def activeCorrelationEdges
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p : ℕ) (x : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) p) :
    Finset (CorrelationEdge p) :=
  Finset.univ.filter fun e ↦
    threshold m p x < scaledSquaredCorrelationScore m p data e.1

/-- The original sum-of-indicators definition of the exceedance count is
exactly the cardinality of the active edge subtype. -/
theorem thresholdExceedanceCount_eq_card_activeCorrelationEdges
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p : ℕ) (x : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) p) :
    thresholdExceedanceCount threshold m p x data =
      (activeCorrelationEdges threshold m p x data).card := by
  classical
  unfold thresholdExceedanceCount activeCorrelationEdges
  rw [Finset.card_filter]
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (correlationEdges p)
      (by simp [correlationEdges])
      (fun e : Fin p × Fin p ↦
        if threshold m p x < scaledSquaredCorrelationScore m p data e
        then 1 else 0))

/-- Pointwise factorial expansion over ordered tuples of distinct unordered
edges. -/
theorem thresholdExceedanceCount_descFactorial_eq_sum_orderedDistinct
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (x : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) p) :
    (thresholdExceedanceCount threshold m p x data).descFactorial k =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        if (∀ i, threshold m p x <
            scaledSquaredCorrelationScore m p data (edges i).1)
        then 1 else 0 := by
  classical
  rw [thresholdExceedanceCount_eq_card_activeCorrelationEdges]
  simpa [activeCorrelationEdges] using
    descFactorial_card_eq_sum_embeddings_indicator
      (activeCorrelationEdges threshold m p x data) k

/-- Joint bulk-and-edge indicator associated with one ordered distinct edge
tuple. -/
def orderedTupleJointIndicator
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k)
    (data : NestedTuple (ObservationSpace (m + 1)) p) : ℝ :=
  if Z0mpStatistic m p data ≤ z ∧
      ∀ i, threshold m p x <
        scaledSquaredCorrelationScore m p data (edges i).1
  then 1 else 0

/-- Event whose indicator is `orderedTupleJointIndicator`. -/
def orderedTupleJointEvent
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    Set (NestedTuple (ObservationSpace (m + 1)) p) :=
  {data | Z0mpStatistic m p data ≤ z ∧
      ∀ i, threshold m p x <
        scaledSquaredCorrelationScore m p data (edges i).1}

/-- Every ordered-tuple joint indicator is measurable. -/
theorem measurable_orderedTupleJointIndicator
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    Measurable (orderedTupleJointIndicator threshold m p k z x edges) := by
  have hbulk : MeasurableSet
      {data : NestedTuple (ObservationSpace (m + 1)) p |
        Z0mpStatistic m p data ≤ z} :=
    measurableSet_le (measurable_Z0mpStatistic m p) measurable_const
  have hedge : MeasurableSet
      {data : NestedTuple (ObservationSpace (m + 1)) p |
        ∀ i, threshold m p x <
          scaledSquaredCorrelationScore m p data (edges i).1} := by
    have hi := MeasurableSet.iInter fun i ↦
      measurableSet_lt
        (measurable_const : Measurable
          (fun _data : NestedTuple (ObservationSpace (m + 1)) p ↦
            threshold m p x))
        (measurable_scaledSquaredCorrelationScore m p (edges i).1)
    convert hi using 1
    ext data
    simp
  exact measurable_const.ite (hbulk.inter hedge) measurable_const

/-- The joint event is measurable. -/
theorem measurableSet_orderedTupleJointEvent
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    MeasurableSet (orderedTupleJointEvent threshold m p k z x edges) := by
  have h := measurable_orderedTupleJointIndicator threshold m p k z x edges
  have hone : MeasurableSet
      (orderedTupleJointIndicator threshold m p k z x edges ⁻¹' ({1} : Set ℝ)) :=
    h (MeasurableSet.singleton 1)
  convert hone using 1
  ext data
  simp [orderedTupleJointEvent, orderedTupleJointIndicator]

/-- Indicator presentation of the tuple event. -/
theorem orderedTupleJointIndicator_eq_setIndicator
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    orderedTupleJointIndicator threshold m p k z x edges =
      (orderedTupleJointEvent threshold m p k z x edges).indicator
        (fun _ ↦ (1 : ℝ)) := by
  funext data
  by_cases hcond : Z0mpStatistic m p data ≤ z ∧
      ∀ i, threshold m p x <
        scaledSquaredCorrelationScore m p data (edges i).1
  · simp [orderedTupleJointIndicator, orderedTupleJointEvent, hcond]
  · simp [orderedTupleJointIndicator, orderedTupleJointEvent, hcond]

/-- Every ordered-tuple joint indicator is integrable under any finite
measure; in particular, under the Gaussian product probability measure. -/
theorem integrable_orderedTupleJointIndicator
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    Integrable (orderedTupleJointIndicator threshold m p k z x edges)
      (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) := by
  apply Integrable.of_bound
    (measurable_orderedTupleJointIndicator threshold m p k z x edges).aestronglyMeasurable 1
  filter_upwards [] with data
  unfold orderedTupleJointIndicator
  split_ifs <;> norm_num

/-- The mixed factorial integrand is pointwise the finite sum of its ordered
distinct-edge joint indicators. -/
theorem thresholdMixedFactorialIntegrand_eq_sum_orderedTupleJointIndicator
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) p) :
    (if Z0mpStatistic m p data ≤ z then
        ((thresholdExceedanceCount threshold m p x data).descFactorial k : ℝ)
      else 0) =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        orderedTupleJointIndicator threshold m p k z x edges data := by
  classical
  rw [thresholdExceedanceCount_descFactorial_eq_sum_orderedDistinct]
  by_cases hbulk : Z0mpStatistic m p data ≤ z
  · simp only [hbulk, if_true, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro edges _hedges
    by_cases hall : ∀ i, threshold m p x <
        scaledSquaredCorrelationScore m p data (edges i).1
    · simp [orderedTupleJointIndicator, hbulk, hall]
    · simp [orderedTupleJointIndicator, hbulk, hall]
  · simp [orderedTupleJointIndicator, hbulk]

/-- Exact integral expansion of the mixed factorial moment.  No asymptotics
or independence assumption enters this identity. -/
theorem thresholdMixedFactorialMoment_eq_sum_orderedTupleIntegrals
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ) :
    thresholdMixedFactorialMoment threshold m p k z x =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        ∫ data : NestedTuple (ObservationSpace (m + 1)) p,
          orderedTupleJointIndicator threshold m p k z x edges data
        ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p := by
  unfold thresholdMixedFactorialMoment
  calc
    (∫ data : NestedTuple (ObservationSpace (m + 1)) p,
        if Z0mpStatistic m p data ≤ z then
          ((thresholdExceedanceCount threshold m p x data).descFactorial k : ℝ)
        else 0
      ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) =
        ∫ data : NestedTuple (ObservationSpace (m + 1)) p,
          ∑ edges : OrderedDistinctEdgeTuple p k,
            orderedTupleJointIndicator threshold m p k z x edges data
        ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p := by
      apply integral_congr_ae
      filter_upwards [] with data
      exact thresholdMixedFactorialIntegrand_eq_sum_orderedTupleJointIndicator
        threshold m p k z x data
    _ = ∑ edges : OrderedDistinctEdgeTuple p k,
        ∫ data : NestedTuple (ObservationSpace (m + 1)) p,
          orderedTupleJointIndicator threshold m p k z x edges data
        ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p := by
      simpa using integral_finsetSum
        (μ := nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p)
        (Finset.univ : Finset (OrderedDistinctEdgeTuple p k))
        (fun edges _hedges ↦
          integrable_orderedTupleJointIndicator threshold m p k z x edges)

/-- Each tuple integral is exactly the real-valued probability of its joint
event. -/
theorem integral_orderedTupleJointIndicator_eq_measureReal
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    (∫ data : NestedTuple (ObservationSpace (m + 1)) p,
        orderedTupleJointIndicator threshold m p k z x edges data
      ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) =
      (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleJointEvent threshold m p k z x edges) := by
  rw [orderedTupleJointIndicator_eq_setIndicator]
  exact integral_indicator_one
    (measurableSet_orderedTupleJointEvent threshold m p k z x edges)

/-- The exact matching/overlap partition of the mixed factorial moment. -/
theorem thresholdMixedFactorialMoment_eq_matching_add_overlap
    (threshold : ℕ → ℕ → ℝ → ℝ) (m p k : ℕ) (z x : ℝ) :
    thresholdMixedFactorialMoment threshold m p k z x =
      (∑ edges ∈ orderedMatchingTuples p k,
        (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p).real
          (orderedTupleJointEvent threshold m p k z x edges)) +
      ∑ edges ∈ orderedOverlapTuples p k,
        (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p).real
          (orderedTupleJointEvent threshold m p k z x edges) := by
  rw [thresholdMixedFactorialMoment_eq_sum_orderedTupleIntegrals]
  simp_rw [integral_orderedTupleJointIndicator_eq_measureReal]
  simpa [orderedDistinctEdgeTuples] using
    sum_orderedDistinct_eq_matching_add_overlap p k
      (fun edges ↦
        (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p).real
          (orderedTupleJointEvent threshold m p k z x edges))

end

end LogdetLean.Coherence
