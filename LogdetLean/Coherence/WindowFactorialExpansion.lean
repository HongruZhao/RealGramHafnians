import LogdetLean.Coherence.ScoreWindow
import LogdetLean.Coherence.FactorialExpansion
/-!
# Exact factorial expansion for a bounded coherence-score window

This module is the bounded-window counterpart of `FactorialExpansion`.  It
contains no limiting argument: it rewrites the falling factorial of the
number of normalized squared-correlation scores in `(a,b]` as a finite sum
over ordered tuples of distinct correlation edges, and then rewrites the
corresponding mixed log-determinant moment as a sum of joint-event
probabilities.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- Active unordered correlation edges whose normalized scores lie in
`(a,b]`. -/
def activeCoherenceScoreWindowEdges
    (m p : ℕ) (a b : ℝ) (data : GaussianCorrelationSample m p) :
    Finset (CorrelationEdge p) :=
  Finset.univ.filter fun e ↦ coherencePointScore m p data e ∈ Ioc a b

/-- The sum-of-indicators definition of the window count is exactly the
cardinality of the active-edge set. -/
theorem coherenceScoreWindowCount_eq_card_active
    (m p : ℕ) (a b : ℝ) (data : GaussianCorrelationSample m p) :
    coherenceScoreWindowCount m p a b data =
      (activeCoherenceScoreWindowEdges m p a b data).card := by
  classical
  unfold coherenceScoreWindowCount activeCoherenceScoreWindowEdges
  rw [Finset.card_filter]

/-- Pointwise falling-factorial expansion of a bounded-window count. -/
theorem coherenceScoreWindowCount_descFactorial_eq_sum_orderedDistinct
    (m p k : ℕ) (a b : ℝ) (data : GaussianCorrelationSample m p) :
    (coherenceScoreWindowCount m p a b data).descFactorial k =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        if (∀ i, coherencePointScore m p data (edges i) ∈ Ioc a b)
        then 1 else 0 := by
  classical
  rw [coherenceScoreWindowCount_eq_card_active]
  simpa [activeCoherenceScoreWindowEdges] using
    descFactorial_card_eq_sum_embeddings_indicator
      (activeCoherenceScoreWindowEdges m p a b data) k

/-- Joint indicator of the standardized log-determinant lower tail and a
fixed ordered tuple of bounded-window edge events. -/
def orderedTupleWindowJointIndicator
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k)
    (data : GaussianCorrelationSample m p) : ℝ :=
  if Z0mpStatistic m p data ≤ z ∧
      ∀ i, coherencePointScore m p data (edges i) ∈ Ioc a b
  then 1 else 0

/-- The event represented by `orderedTupleWindowJointIndicator`. -/
def orderedTupleWindowJointEvent
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    Set (GaussianCorrelationSample m p) :=
  {data | Z0mpStatistic m p data ≤ z ∧
      ∀ i, coherencePointScore m p data (edges i) ∈ Ioc a b}

theorem measurableSet_orderedTupleWindowJointEvent
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    MeasurableSet (orderedTupleWindowJointEvent m p k z a b edges) := by
  have hbulk : MeasurableSet
      {data : GaussianCorrelationSample m p | Z0mpStatistic m p data ≤ z} :=
    measurableSet_le (measurable_Z0mpStatistic m p) measurable_const
  have hedge : MeasurableSet
      {data : GaussianCorrelationSample m p |
        ∀ i, coherencePointScore m p data (edges i) ∈ Ioc a b} := by
    have hi : MeasurableSet
        (⋂ i : Fin k,
          coherencePointScore m p (e := edges i) ⁻¹' Ioc a b) :=
      MeasurableSet.iInter fun i ↦
        measurableSet_Ioc.preimage
          (measurable_coherencePointScore m p (edges i))
    convert hi using 1
    ext data
    simp
  exact hbulk.inter hedge

theorem measurable_orderedTupleWindowJointIndicator
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    Measurable (orderedTupleWindowJointIndicator m p k z a b edges) := by
  exact Measurable.ite
    (measurableSet_orderedTupleWindowJointEvent m p k z a b edges)
    measurable_const measurable_const

theorem orderedTupleWindowJointIndicator_eq_setIndicator
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    orderedTupleWindowJointIndicator m p k z a b edges =
      (orderedTupleWindowJointEvent m p k z a b edges).indicator
        (fun _ ↦ (1 : ℝ)) := by
  funext data
  by_cases h : Z0mpStatistic m p data ≤ z ∧
      ∀ i, coherencePointScore m p data (edges i) ∈ Ioc a b
  · rw [Set.indicator_of_mem]
    · unfold orderedTupleWindowJointIndicator
      rw [if_pos h]
    · exact h
  · rw [Set.indicator_of_notMem]
    · unfold orderedTupleWindowJointIndicator
      rw [if_neg h]
    · exact h

theorem integrable_orderedTupleWindowJointIndicator
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    Integrable (orderedTupleWindowJointIndicator m p k z a b edges)
      (gaussianCorrelationMeasure m p) := by
  let _ : IsProbabilityMeasure (gaussianCorrelationMeasure m p) := by
    unfold gaussianCorrelationMeasure
    infer_instance
  apply Integrable.of_bound
    (measurable_orderedTupleWindowJointIndicator m p k z a b edges).aestronglyMeasurable 1
  filter_upwards [] with data
  unfold orderedTupleWindowJointIndicator
  split_ifs <;> norm_num

/-- Mixed factorial moment for a bounded normalized score window. -/
def gaussianCoherenceWindowMixedFactorialMoment
    (m p k : ℕ) (z a b : ℝ) : ℝ :=
  ∫ data : GaussianCorrelationSample m p,
    if Z0mpStatistic m p data ≤ z then
      ((coherenceScoreWindowCount m p a b data).descFactorial k : ℝ)
    else 0
  ∂gaussianCorrelationMeasure m p

/-- The mixed window factorial integrand is pointwise the sum over ordered
distinct edge tuples. -/
theorem windowMixedFactorialIntegrand_eq_sum_orderedTupleWindowJointIndicator
    (m p k : ℕ) (z a b : ℝ) (data : GaussianCorrelationSample m p) :
    (if Z0mpStatistic m p data ≤ z then
        ((coherenceScoreWindowCount m p a b data).descFactorial k : ℝ)
      else 0) =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        orderedTupleWindowJointIndicator m p k z a b edges data := by
  classical
  rw [coherenceScoreWindowCount_descFactorial_eq_sum_orderedDistinct]
  by_cases hbulk : Z0mpStatistic m p data ≤ z
  · simp only [hbulk, if_true, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro edges _hedges
    by_cases hall : ∀ i,
        coherencePointScore m p data (edges i) ∈ Ioc a b
    · simp [orderedTupleWindowJointIndicator, hbulk, hall]
    · simp [orderedTupleWindowJointIndicator, hbulk, hall]
  · simp [orderedTupleWindowJointIndicator, hbulk]

/-- Exact finite expansion of the bounded-window mixed factorial moment. -/
theorem gaussianCoherenceWindowMixedFactorialMoment_eq_sum_integrals
    (m p k : ℕ) (z a b : ℝ) :
    gaussianCoherenceWindowMixedFactorialMoment m p k z a b =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        ∫ data : GaussianCorrelationSample m p,
          orderedTupleWindowJointIndicator m p k z a b edges data
        ∂gaussianCorrelationMeasure m p := by
  unfold gaussianCoherenceWindowMixedFactorialMoment
  calc
    (∫ data : GaussianCorrelationSample m p,
        if Z0mpStatistic m p data ≤ z then
          ((coherenceScoreWindowCount m p a b data).descFactorial k : ℝ)
        else 0 ∂gaussianCorrelationMeasure m p) =
        ∫ data : GaussianCorrelationSample m p,
          ∑ edges : OrderedDistinctEdgeTuple p k,
            orderedTupleWindowJointIndicator m p k z a b edges data
        ∂gaussianCorrelationMeasure m p := by
          apply integral_congr_ae
          filter_upwards [] with data
          exact windowMixedFactorialIntegrand_eq_sum_orderedTupleWindowJointIndicator
            m p k z a b data
    _ = _ := by
      simpa using integral_finsetSum
        (μ := gaussianCorrelationMeasure m p)
        (Finset.univ : Finset (OrderedDistinctEdgeTuple p k))
        (fun edges _ ↦
          integrable_orderedTupleWindowJointIndicator m p k z a b edges)

/-- Each summand is the real-valued probability of its joint event. -/
theorem integral_orderedTupleWindowJointIndicator_eq_measureReal
    (m p k : ℕ) (z a b : ℝ) (edges : OrderedDistinctEdgeTuple p k) :
    (∫ data : GaussianCorrelationSample m p,
        orderedTupleWindowJointIndicator m p k z a b edges data
      ∂gaussianCorrelationMeasure m p) =
      (gaussianCorrelationMeasure m p).real
        (orderedTupleWindowJointEvent m p k z a b edges) := by
  rw [orderedTupleWindowJointIndicator_eq_setIndicator]
  exact integral_indicator_one
    (measurableSet_orderedTupleWindowJointEvent m p k z a b edges)

/-- Probability-sum version of the exact factorial expansion. -/
theorem gaussianCoherenceWindowMixedFactorialMoment_eq_sum_probabilities
    (m p k : ℕ) (z a b : ℝ) :
    gaussianCoherenceWindowMixedFactorialMoment m p k z a b =
      ∑ edges : OrderedDistinctEdgeTuple p k,
        (gaussianCorrelationMeasure m p).real
          (orderedTupleWindowJointEvent m p k z a b edges) := by
  rw [gaussianCoherenceWindowMixedFactorialMoment_eq_sum_integrals]
  apply Finset.sum_congr rfl
  intro edges _
  exact integral_orderedTupleWindowJointIndicator_eq_measureReal
    m p k z a b edges

/-- Exact matching/overlap partition of the bounded-window mixed factorial
moment. -/
theorem gaussianCoherenceWindowMixedFactorialMoment_eq_matching_add_overlap
    (m p k : ℕ) (z a b : ℝ) :
    gaussianCoherenceWindowMixedFactorialMoment m p k z a b =
      (∑ edges ∈ orderedMatchingTuples p k,
        (gaussianCorrelationMeasure m p).real
          (orderedTupleWindowJointEvent m p k z a b edges)) +
      ∑ edges ∈ orderedOverlapTuples p k,
        (gaussianCorrelationMeasure m p).real
          (orderedTupleWindowJointEvent m p k z a b edges) := by
  rw [gaussianCoherenceWindowMixedFactorialMoment_eq_sum_probabilities]
  simpa [orderedDistinctEdgeTuples] using
    sum_orderedDistinct_eq_matching_add_overlap p k
      (fun edges ↦ (gaussianCorrelationMeasure m p).real
        (orderedTupleWindowJointEvent m p k z a b edges))

end

end LogdetLean.Coherence
