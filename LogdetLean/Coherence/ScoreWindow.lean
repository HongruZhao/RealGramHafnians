import LogdetLean.Coherence.GaussianMarkedJointAdapter
import LogdetLean.Coherence.BetaEndpointAsymptotic
/-!
# Normalized coherence scores and bounded score windows

This file introduces the finite point locations

`m * r_ij^2 - 4 * log p + log (log p)`

without yet constructing a random point-measure space.  It defines the count
in a bounded half-open window `(a,b]`, proves its basic measurability and
cardinality properties, identifies the exact one-edge window probability as
the difference of two Beta tails, and proves the corresponding all-gap
intensity limit.

No point-process convergence is asserted here.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

/-- The normalized extreme-correlation location attached to one unordered
sample-correlation edge. -/
def coherencePointScore (m p : ℕ)
    (data : GaussianCorrelationSample m p) (e : CorrelationEdge p) : ℝ :=
  scaledSquaredCorrelationScore m p data e.1 -
    4 * Real.log (p : ℝ) + Real.log (Real.log (p : ℝ))

/-- Every fixed normalized edge score is measurable on the raw centered
Gaussian sample space. -/
theorem measurable_coherencePointScore
    (m p : ℕ) (e : CorrelationEdge p) :
    Measurable (fun data : GaussianCorrelationSample m p ↦
      coherencePointScore m p data e) := by
  unfold coherencePointScore
  exact ((measurable_scaledSquaredCorrelationScore m p e.1).sub
    measurable_const).add measurable_const

/-- A normalized score lies above `x` exactly when the uncentered squared
correlation score exceeds the classical coherence threshold at `x`. -/
theorem coherencePointScore_gt_iff
    (m p : ℕ) (data : GaussianCorrelationSample m p)
    (e : CorrelationEdge p) (x : ℝ) :
    x < coherencePointScore m p data e ↔
      classicalCoherenceThreshold m p x <
        scaledSquaredCorrelationScore m p data e.1 := by
  unfold coherencePointScore classicalCoherenceThreshold
  constructor <;> intro h <;> linarith

/-- The event that one normalized score belongs to the bounded half-open
window `(a,b]`. -/
def coherenceScoreWindowEvent (m p : ℕ) (a b : ℝ)
    (e : CorrelationEdge p) : Set (GaussianCorrelationSample m p) :=
  coherencePointScore m p (e := e) ⁻¹' Ioc a b

/-- Every one-edge score-window event is measurable. -/
theorem measurableSet_coherenceScoreWindowEvent
    (m p : ℕ) (a b : ℝ) (e : CorrelationEdge p) :
    MeasurableSet (coherenceScoreWindowEvent m p a b e) := by
  exact measurableSet_Ioc.preimage (measurable_coherencePointScore m p e)

/-- The upper tail at a larger normalized threshold is contained in the
upper tail at a smaller threshold. -/
theorem coherenceEdgeExceedanceEvent_mono_threshold
    {m p : ℕ} {a b : ℝ} (hab : a ≤ b) (e : CorrelationEdge p) :
    coherenceEdgeExceedanceEvent m p b e ⊆
      coherenceEdgeExceedanceEvent m p a e := by
  intro data hdata
  change classicalCoherenceThreshold m p b <
    scaledSquaredCorrelationScore m p data e.1 at hdata
  change classicalCoherenceThreshold m p a <
    scaledSquaredCorrelationScore m p data e.1
  unfold classicalCoherenceThreshold at hdata ⊢
  linarith

/-- A bounded score window is exactly the lower-threshold tail with the
upper-threshold tail removed.  This set identity itself does not require an
ordering assumption on the endpoints. -/
theorem coherenceScoreWindowEvent_eq_sdiff
    (m p : ℕ) (a b : ℝ) (e : CorrelationEdge p) :
    coherenceScoreWindowEvent m p a b e =
      coherenceEdgeExceedanceEvent m p a e \
        coherenceEdgeExceedanceEvent m p b e := by
  ext data
  change
    (a < coherencePointScore m p data e ∧
      coherencePointScore m p data e ≤ b) ↔
    (classicalCoherenceThreshold m p a <
        scaledSquaredCorrelationScore m p data e.1 ∧
      ¬ classicalCoherenceThreshold m p b <
        scaledSquaredCorrelationScore m p data e.1)
  rw [← coherencePointScore_gt_iff m p data e a,
    ← coherencePointScore_gt_iff m p data e b]
  simp only [not_lt]

/-- Number of unordered sample-correlation edges whose normalized locations
belong to `(a,b]`. -/
def coherenceScoreWindowCount (m p : ℕ) (a b : ℝ)
    (data : GaussianCorrelationSample m p) : ℕ :=
  ∑ e : CorrelationEdge p,
    if coherencePointScore m p data e ∈ Ioc a b then 1 else 0

/-- The bounded-window count is measurable. -/
theorem measurable_coherenceScoreWindowCount
    (m p : ℕ) (a b : ℝ) :
    Measurable (coherenceScoreWindowCount m p a b) := by
  unfold coherenceScoreWindowCount
  apply Finset.measurable_sum
  intro e _he
  exact Measurable.ite
    (measurableSet_coherenceScoreWindowEvent m p a b e)
    measurable_const measurable_const

/-- A bounded-window count cannot exceed the total number of unordered
edges. -/
theorem coherenceScoreWindowCount_le_card_edges
    (m p : ℕ) (a b : ℝ) (data : GaussianCorrelationSample m p) :
    coherenceScoreWindowCount m p a b data ≤ p.choose 2 := by
  unfold coherenceScoreWindowCount
  calc
    (∑ e : CorrelationEdge p,
        if coherencePointScore m p data e ∈ Ioc a b then 1 else 0) ≤
        ∑ _e : CorrelationEdge p, 1 := by
          apply Finset.sum_le_sum
          intro e _he
          split_ifs <;> omega
    _ = Fintype.card (CorrelationEdge p) := by simp
    _ = p.choose 2 := card_correlationEdge p

/-- Exact one-edge Beta probability assigned to the bounded normalized score
window `(a,b]`. -/
def betaCorrelationWindowProbability
    (m p : ℕ) (a b : ℝ) : ℝ :=
  betaCorrelationTailProbability m p a -
    betaCorrelationTailProbability m p b

/-- For ordered endpoints, the probability of a fixed edge falling in
`(a,b]` is exactly the difference of the two Beta upper tails. -/
theorem coherenceScoreWindowEvent_probability_eq_betaWindow
    {m p : ℕ} (hm : 2 ≤ m) {a b : ℝ} (hab : a ≤ b)
    (e : CorrelationEdge p) :
    (gaussianCorrelationMeasure m p).real
        (coherenceScoreWindowEvent m p a b e) =
      betaCorrelationWindowProbability m p a b := by
  let _ : IsProbabilityMeasure (gaussianCorrelationMeasure m p) := by
    unfold gaussianCorrelationMeasure
    infer_instance
  rw [coherenceScoreWindowEvent_eq_sdiff]
  rw [measureReal_sdiff
    (coherenceEdgeExceedanceEvent_mono_threshold hab e)
    (measurableSet_coherenceEdgeExceedanceEvent m p b e)]
  rw [coherenceEdgeExceedanceEvent_probability_eq_betaTail hm a e,
    coherenceEdgeExceedanceEvent_probability_eq_betaTail hm b e]
  rfl

/-- The finite expected intensity of a bounded normalized score window. -/
def finiteCoherenceWindowIntensity
    (m p : ℕ) (a b : ℝ) : ℝ :=
  ((p.choose 2 : ℕ) : ℝ) * betaCorrelationWindowProbability m p a b

/-- All-gap bounded-window intensity limit.  Along every eventually
admissible sequence `2 ≤ p ≤ m(p)`, the total one-edge weight in `(a,b]`
converges to `lambda(a)-lambda(b)`. -/
theorem tendsto_finiteCoherenceWindowIntensity
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (a b : ℝ) :
    Tendsto
      (fun p : ℕ ↦ finiteCoherenceWindowIntensity (mseq p) p a b)
      atTop
      (nhds (classicalCoherenceIntensity a -
        classicalCoherenceIntensity b)) := by
  have ha := allGapBetaTailIntensity mseq hadm a
  have hb := allGapBetaTailIntensity mseq hadm b
  simpa [finiteCoherenceWindowIntensity,
    betaCorrelationWindowProbability, mul_sub] using ha.sub hb

end

end LogdetLean.Coherence
