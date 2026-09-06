import LogdetLean.Coherence.FiniteUnionScoreWindow
import LogdetLean.Coherence.FactorialExpansion
/-!
# Exact factorial expansion for a finite union of score windows

For a fixed `FiniteScoreWindowFamily`, this module defines the number of
normalized coherence scores in the union, expands its falling factorial over
ordered distinct edge tuples, and partitions the resulting mixed moment into
matching and overlapping tuples.  Everything is finite-sample and exact.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

-- Membership in a finite union is propositionally decidable; the definitions
-- below are noncomputable and use the standard classical decision procedure.
attribute [local instance] Classical.propDecidable

/-- Number of unordered coherence edges whose normalized scores lie in the
finite disjoint window union. -/
def coherenceFiniteUnionWindowCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (data : GaussianCorrelationSample m p) : ℕ :=
  ∑ e : CorrelationEdge p,
    if coherencePointScore m p data e ∈ finiteScoreWindowUnion W
    then 1 else 0

/-- The finite-union count is measurable. -/
theorem measurable_coherenceFiniteUnionWindowCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) :
    Measurable (coherenceFiniteUnionWindowCount W m p) := by
  unfold coherenceFiniteUnionWindowCount
  apply Finset.measurable_sum
  intro e _he
  exact Measurable.ite
    (measurableSet_finiteScoreWindowUnion W |>.preimage
      (measurable_coherencePointScore m p e))
    measurable_const measurable_const

/-- A finite-union count cannot exceed the number of unordered edges. -/
theorem coherenceFiniteUnionWindowCount_le_card_edges
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (data : GaussianCorrelationSample m p) :
    coherenceFiniteUnionWindowCount W m p data ≤ p.choose 2 := by
  unfold coherenceFiniteUnionWindowCount
  calc
    (∑ e : CorrelationEdge p,
        if coherencePointScore m p data e ∈ finiteScoreWindowUnion W
        then 1 else 0) ≤
        ∑ _e : CorrelationEdge p, 1 := by
          apply Finset.sum_le_sum
          intro e _he
          split_ifs <;> omega
    _ = Fintype.card (CorrelationEdge p) := by simp
    _ = p.choose 2 := card_correlationEdge p

/-- Active unordered edges in the finite score-window union. -/
def activeCoherenceFiniteUnionWindowEdges
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (data : GaussianCorrelationSample m p) :
    Finset (CorrelationEdge p) :=
  Finset.univ.filter fun e ↦
    coherencePointScore m p data e ∈ finiteScoreWindowUnion W

/-- The sum-of-indicators definition is the active-edge cardinality. -/
theorem coherenceFiniteUnionWindowCount_eq_card_active
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (data : GaussianCorrelationSample m p) :
    coherenceFiniteUnionWindowCount W m p data =
      (activeCoherenceFiniteUnionWindowEdges W m p data).card := by
  classical
  unfold coherenceFiniteUnionWindowCount
    activeCoherenceFiniteUnionWindowEdges
  rw [Finset.card_filter]

/-- Pointwise falling-factorial expansion of the finite-union count. -/
theorem coherenceFiniteUnionWindowCount_descFactorial_eq_sum_orderedDistinct
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (data : GaussianCorrelationSample m p) :
    (coherenceFiniteUnionWindowCount W m p data).descFactorial k =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        if (∀ i, coherencePointScore m p data (edges i) ∈
            finiteScoreWindowUnion W)
        then 1 else 0 := by
  classical
  rw [coherenceFiniteUnionWindowCount_eq_card_active]
  simpa [activeCoherenceFiniteUnionWindowEdges] using
    descFactorial_card_eq_sum_embeddings_indicator
      (activeCoherenceFiniteUnionWindowEdges W m p data) k

/-- Joint lower-tail and finite-union tuple event. -/
def orderedTupleFiniteUnionWindowJointEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    Set (GaussianCorrelationSample m p) :=
  {data | Z0mpStatistic m p data ≤ z ∧
    ∀ i, coherencePointScore m p data (edges i) ∈
      finiteScoreWindowUnion W}

/-- Indicator of the joint lower-tail and finite-union tuple event. -/
def orderedTupleFiniteUnionWindowJointIndicator
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k)
    (data : GaussianCorrelationSample m p) : ℝ :=
  if Z0mpStatistic m p data ≤ z ∧
      ∀ i, coherencePointScore m p data (edges i) ∈
        finiteScoreWindowUnion W
  then 1 else 0

theorem measurableSet_orderedTupleFiniteUnionWindowJointEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    MeasurableSet
      (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) := by
  have hbulk : MeasurableSet
      {data : GaussianCorrelationSample m p | Z0mpStatistic m p data ≤ z} :=
    measurableSet_le (measurable_Z0mpStatistic m p) measurable_const
  have hedge : MeasurableSet
      {data : GaussianCorrelationSample m p |
        ∀ i, coherencePointScore m p data (edges i) ∈
          finiteScoreWindowUnion W} := by
    have hi : MeasurableSet
        (⋂ i : Fin k,
          coherencePointScore m p (e := edges i) ⁻¹'
            finiteScoreWindowUnion W) :=
      MeasurableSet.iInter fun i ↦
        (measurableSet_finiteScoreWindowUnion W).preimage
          (measurable_coherencePointScore m p (edges i))
    convert hi using 1
    ext data
    simp
  exact hbulk.inter hedge

theorem measurable_orderedTupleFiniteUnionWindowJointIndicator
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    Measurable
      (orderedTupleFiniteUnionWindowJointIndicator W m p k z edges) := by
  exact Measurable.ite
    (measurableSet_orderedTupleFiniteUnionWindowJointEvent
      W m p k z edges)
    measurable_const measurable_const

theorem orderedTupleFiniteUnionWindowJointIndicator_eq_setIndicator
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    orderedTupleFiniteUnionWindowJointIndicator W m p k z edges =
      (orderedTupleFiniteUnionWindowJointEvent W m p k z edges).indicator
        (fun _ ↦ (1 : ℝ)) := by
  funext data
  by_cases h : Z0mpStatistic m p data ≤ z ∧
      ∀ i, coherencePointScore m p data (edges i) ∈
        finiteScoreWindowUnion W
  · rw [Set.indicator_of_mem]
    · unfold orderedTupleFiniteUnionWindowJointIndicator
      rw [if_pos h]
    · exact h
  · rw [Set.indicator_of_notMem]
    · unfold orderedTupleFiniteUnionWindowJointIndicator
      rw [if_neg h]
    · exact h

theorem integrable_orderedTupleFiniteUnionWindowJointIndicator
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    Integrable
      (orderedTupleFiniteUnionWindowJointIndicator W m p k z edges)
      (gaussianCorrelationMeasure m p) := by
  let _ : IsProbabilityMeasure (gaussianCorrelationMeasure m p) := by
    unfold gaussianCorrelationMeasure
    infer_instance
  apply Integrable.of_bound
    (measurable_orderedTupleFiniteUnionWindowJointIndicator
      W m p k z edges).aestronglyMeasurable 1
  filter_upwards [] with data
  unfold orderedTupleFiniteUnionWindowJointIndicator
  split_ifs <;> norm_num

/-- Mixed log-determinant/falling-factorial moment for the finite union. -/
def gaussianCoherenceFiniteUnionMixedFactorialMoment
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) : ℝ :=
  ∫ data : GaussianCorrelationSample m p,
    if Z0mpStatistic m p data ≤ z then
      ((coherenceFiniteUnionWindowCount W m p data).descFactorial k : ℝ)
    else 0
  ∂gaussianCorrelationMeasure m p

/-- Pointwise expansion of the finite-union mixed factorial integrand. -/
theorem finiteUnionMixedFactorialIntegrand_eq_sum_orderedTuple
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) (data : GaussianCorrelationSample m p) :
    (if Z0mpStatistic m p data ≤ z then
        ((coherenceFiniteUnionWindowCount W m p data).descFactorial k : ℝ)
      else 0) =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        orderedTupleFiniteUnionWindowJointIndicator W m p k z edges data := by
  classical
  rw [coherenceFiniteUnionWindowCount_descFactorial_eq_sum_orderedDistinct]
  by_cases hbulk : Z0mpStatistic m p data ≤ z
  · simp only [hbulk, if_true, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro edges _hedges
    by_cases hall : ∀ i,
        coherencePointScore m p data (edges i) ∈ finiteScoreWindowUnion W
    · simp [orderedTupleFiniteUnionWindowJointIndicator, hbulk, hall]
    · simp [orderedTupleFiniteUnionWindowJointIndicator, hbulk, hall]
  · simp [orderedTupleFiniteUnionWindowJointIndicator, hbulk]

/-- Exact expansion of the finite-union mixed factorial moment into joint
event probabilities. -/
theorem gaussianCoherenceFiniteUnionMixedFactorialMoment_eq_sum_probabilities
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) :
    gaussianCoherenceFiniteUnionMixedFactorialMoment W m p k z =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        (gaussianCorrelationMeasure m p).real
          (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) := by
  unfold gaussianCoherenceFiniteUnionMixedFactorialMoment
  calc
    (∫ data : GaussianCorrelationSample m p,
        if Z0mpStatistic m p data ≤ z then
          ((coherenceFiniteUnionWindowCount W m p data).descFactorial k : ℝ)
        else 0 ∂gaussianCorrelationMeasure m p) =
        ∫ data : GaussianCorrelationSample m p,
          ∑ edges : OrderedDistinctEdgeTuple p k,
            orderedTupleFiniteUnionWindowJointIndicator
              W m p k z edges data
        ∂gaussianCorrelationMeasure m p := by
      apply integral_congr_ae
      filter_upwards [] with data
      exact finiteUnionMixedFactorialIntegrand_eq_sum_orderedTuple
        W m p k z data
    _ = ∑ edges : OrderedDistinctEdgeTuple p k,
          ∫ data : GaussianCorrelationSample m p,
            orderedTupleFiniteUnionWindowJointIndicator
              W m p k z edges data
          ∂gaussianCorrelationMeasure m p := by
      simpa using integral_finsetSum
        (μ := gaussianCorrelationMeasure m p)
        (Finset.univ : Finset (OrderedDistinctEdgeTuple p k))
        (fun edges _ ↦
          integrable_orderedTupleFiniteUnionWindowJointIndicator
            W m p k z edges)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro edges _
      rw [orderedTupleFiniteUnionWindowJointIndicator_eq_setIndicator]
      exact integral_indicator_one
        (measurableSet_orderedTupleFiniteUnionWindowJointEvent
          W m p k z edges)

/-- Exact matching/overlap partition for the finite-union mixed moment. -/
theorem gaussianCoherenceFiniteUnionMixedFactorialMoment_eq_matching_add_overlap
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z : ℝ) :
    gaussianCoherenceFiniteUnionMixedFactorialMoment W m p k z =
      (∑ edges ∈ orderedMatchingTuples p k,
        (gaussianCorrelationMeasure m p).real
          (orderedTupleFiniteUnionWindowJointEvent W m p k z edges)) +
      ∑ edges ∈ orderedOverlapTuples p k,
        (gaussianCorrelationMeasure m p).real
          (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) := by
  rw [gaussianCoherenceFiniteUnionMixedFactorialMoment_eq_sum_probabilities]
  simpa [orderedDistinctEdgeTuples] using
    sum_orderedDistinct_eq_matching_add_overlap p k
      (fun edges ↦ (gaussianCorrelationMeasure m p).real
        (orderedTupleFiniteUnionWindowJointEvent W m p k z edges))

end

end LogdetLean.Coherence
