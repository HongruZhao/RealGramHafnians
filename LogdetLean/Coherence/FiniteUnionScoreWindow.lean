import LogdetLean.Coherence.ScoreWindow
import Mathlib.MeasureTheory.Measure.Real
/-!
# Finite unions of disjoint normalized score windows

This module packages a finite indexed family of pairwise-disjoint half-open
intervals `(a_i,b_i]`.  It proves exact one-edge probability and finite
intensity sum identities, together with the all-gap limit of that finite
intensity.  These are finite-union ingredients relevant to a Kallenberg-style
criterion; no multibin or point-process convergence is asserted.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

/-- A finite-type-indexed family of ordered, pairwise-disjoint half-open
normalized score intervals.  Finiteness is supplied by `[Fintype ι]` at use
sites. -/
structure FiniteScoreWindowFamily (ι : Type*) where
  lower : ι → ℝ
  upper : ι → ℝ
  ordered : ∀ i, lower i ≤ upper i
  pairwiseDisjoint : Pairwise fun i j ↦
    Disjoint (Set.Ioc (lower i) (upper i))
      (Set.Ioc (lower j) (upper j))

/-- Union of all normalized score intervals in the family. -/
def finiteScoreWindowUnion {ι : Type*} (W : FiniteScoreWindowFamily ι) :
    Set ℝ :=
  ⋃ i, Set.Ioc (W.lower i) (W.upper i)

theorem measurableSet_finiteScoreWindowUnion
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι) :
    MeasurableSet (finiteScoreWindowUnion W) := by
  exact MeasurableSet.iUnion fun i ↦ measurableSet_Ioc

/-- Any common lower bound for all interval endpoints is a strict lower-tail
bound for their union. -/
theorem finiteScoreWindowUnion_subset_Ioi
    {ι : Type*} (W : FiniteScoreWindowFamily ι) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) :
    finiteScoreWindowUnion W ⊆ Set.Ioi c := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
  exact (hc i).trans_lt hi.1

/-- Event that one fixed Pearson edge has normalized score in the finite
union of windows. -/
def coherenceFiniteUnionWindowEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (e : CorrelationEdge p) :
    Set (GaussianCorrelationSample m p) :=
  ⋃ i, coherenceScoreWindowEvent m p (W.lower i) (W.upper i) e

theorem coherenceFiniteUnionWindowEvent_eq_preimage
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (e : CorrelationEdge p) :
    coherenceFiniteUnionWindowEvent W m p e =
      coherencePointScore m p (e := e) ⁻¹' finiteScoreWindowUnion W := by
  ext data
  simp [coherenceFiniteUnionWindowEvent, coherenceScoreWindowEvent,
    finiteScoreWindowUnion]

theorem measurableSet_coherenceFiniteUnionWindowEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (e : CorrelationEdge p) :
    MeasurableSet (coherenceFiniteUnionWindowEvent W m p e) := by
  rw [coherenceFiniteUnionWindowEvent_eq_preimage]
  exact (measurableSet_finiteScoreWindowUnion W).preimage
    (measurable_coherencePointScore m p e)

/-- The one-edge window events inherit pairwise disjointness from their score
intervals. -/
theorem pairwise_disjoint_coherenceScoreWindowEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (e : CorrelationEdge p) :
    Pairwise fun i j ↦ Disjoint
      (coherenceScoreWindowEvent m p (W.lower i) (W.upper i) e)
      (coherenceScoreWindowEvent m p (W.lower j) (W.upper j) e) := by
  intro i j hij
  simpa [coherenceScoreWindowEvent] using
    (W.pairwiseDisjoint hij).preimage
      (fun data : GaussianCorrelationSample m p ↦
        coherencePointScore m p data e)

/-- Sum of exact one-edge Beta masses over the disjoint windows. -/
def finiteUnionBetaProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) : ℝ :=
  ∑ i, betaCorrelationWindowProbability m p (W.lower i) (W.upper i)

/-- Exact one-edge probability of the finite disjoint union. -/
theorem coherenceFiniteUnionWindowEvent_probability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p : ℕ} (hm : 2 ≤ m) (e : CorrelationEdge p) :
    (gaussianCorrelationMeasure m p).real
        (coherenceFiniteUnionWindowEvent W m p e) =
      finiteUnionBetaProbability W m p := by
  let _ : IsProbabilityMeasure (gaussianCorrelationMeasure m p) := by
    unfold gaussianCorrelationMeasure
    infer_instance
  unfold coherenceFiniteUnionWindowEvent finiteUnionBetaProbability
  rw [measureReal_iUnion_fintype
    (pairwise_disjoint_coherenceScoreWindowEvent W m p e)
    (fun i ↦ measurableSet_coherenceScoreWindowEvent
      m p (W.lower i) (W.upper i) e)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact coherenceScoreWindowEvent_probability_eq_betaWindow
    hm (W.ordered i) e

/-- Finite choose-two intensity of the score-set union. -/
def finiteUnionCoherenceIntensity
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) : ℝ :=
  ((p.choose 2 : ℕ) : ℝ) * finiteUnionBetaProbability W m p

/-- Exact decomposition of finite-union intensity into its window
intensities. -/
theorem finiteUnionCoherenceIntensity_eq_sum
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) :
    finiteUnionCoherenceIntensity W m p =
      ∑ i, finiteCoherenceWindowIntensity
        m p (W.lower i) (W.upper i) := by
  simp [finiteUnionCoherenceIntensity, finiteUnionBetaProbability,
    finiteCoherenceWindowIntensity, Finset.mul_sum]

/-- Limiting intensity assigned to the finite union. -/
def finiteUnionClassicalCoherenceIntensity
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι) : ℝ :=
  ∑ i, (classicalCoherenceIntensity (W.lower i) -
    classicalCoherenceIntensity (W.upper i))

/-- All-gap finite-union intensity limit, obtained by a finite sum of the
already verified single-window limits. -/
theorem tendsto_finiteUnionCoherenceIntensity
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto
      (fun p : ℕ ↦ finiteUnionCoherenceIntensity W (mseq p) p)
      atTop (nhds (finiteUnionClassicalCoherenceIntensity W)) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun i _hi ↦ tendsto_finiteCoherenceWindowIntensity
      hadm (W.lower i) (W.upper i))
  simpa [finiteUnionCoherenceIntensity_eq_sum,
    finiteUnionClassicalCoherenceIntensity] using hsum

/-- The finite-union one-edge event is dominated by the exceedance event at
any common lower endpoint. -/
theorem coherenceFiniteUnionWindowEvent_subset_lowerExceedance
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (e : CorrelationEdge p) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) :
    coherenceFiniteUnionWindowEvent W m p e ⊆
      coherenceEdgeExceedanceEvent m p c e := by
  intro data hdata
  rw [coherenceFiniteUnionWindowEvent_eq_preimage] at hdata
  have hcscore : c < coherencePointScore m p data e :=
    finiteScoreWindowUnion_subset_Ioi W c hc hdata
  exact (coherencePointScore_gt_iff m p data e c).mp hcscore

end

end LogdetLean.Coherence
