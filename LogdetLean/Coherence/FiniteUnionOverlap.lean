import LogdetLean.Coherence.FiniteUnionFactorialExpansion
import LogdetLean.Coherence.ConcreteOverlap
/-!
# Overlap negligibility for a finite union of score windows

If `c` is a common lower bound for every window's lower endpoint, every
finite-union tuple event is contained in the ordinary upper-tail tuple event
at `c`.  This transfers the already verified all-gap overlap estimate to the
entire finite union.  No matching factorization or conditional CLT is used.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators

/-- Tuplewise containment in the ordinary lower-endpoint exceedance event. -/
theorem orderedTupleFiniteUnionWindowJointEvent_subset_lowerTail
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z c : ℝ) (hc : ∀ i, c ≤ W.lower i)
    (edges : OrderedDistinctEdgeTuple p k) :
    orderedTupleFiniteUnionWindowJointEvent W m p k z edges ⊆
      orderedTupleJointEvent classicalCoherenceThreshold
        m p k z c edges := by
  intro data hdata
  refine ⟨hdata.1, fun i ↦ ?_⟩
  have hmem : data ∈ coherenceFiniteUnionWindowEvent W m p (edges i) := by
    rw [coherenceFiniteUnionWindowEvent_eq_preimage]
    exact hdata.2 i
  exact coherenceFiniteUnionWindowEvent_subset_lowerExceedance
    W m p (edges i) c hc hmem

/-- Each finite-union tuple probability is dominated by the ordinary
lower-endpoint tail-tuple probability. -/
theorem orderedTupleFiniteUnionWindowJoint_probability_le_lowerTail
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (z c : ℝ) (hc : ∀ i, c ≤ W.lower i)
    (edges : OrderedDistinctEdgeTuple p k) :
    (gaussianCorrelationMeasure m p).real
        (orderedTupleFiniteUnionWindowJointEvent W m p k z edges) ≤
      (gaussianCorrelationMeasure m p).real
        (orderedTupleJointEvent classicalCoherenceThreshold
          m p k z c edges) := by
  let _ : IsProbabilityMeasure (gaussianCorrelationMeasure m p) := by
    unfold gaussianCorrelationMeasure
    infer_instance
  exact measureReal_mono
    (orderedTupleFiniteUnionWindowJointEvent_subset_lowerTail
      W m p k z c hc edges)

/-- The complete ordered-overlap contribution for a fixed finite window
union vanishes along every admissible all-gap sequence. -/
theorem tendsto_gaussianOrderedTupleFiniteUnionWindowJoint_overlap_zero
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) (hk : 0 < k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (z c : ℝ) (hc : ∀ i, c ≤ W.lower i) :
    Tendsto
      (fun p : ℕ ↦
        ∑ edges ∈ orderedOverlapTuples p k,
          (gaussianCorrelationMeasure (mseq p) p).real
            (orderedTupleFiniteUnionWindowJointEvent
              W (mseq p) p k z edges))
      atTop (nhds 0) := by
  classical
  have hupper := tendsto_gaussianOrderedTupleJoint_overlap_zero
    k hk hadm z c
  apply squeeze_zero'
    (g := fun p : ℕ ↦
      ∑ edges ∈ orderedOverlapTuples p k,
        (gaussianCorrelationMeasure (mseq p) p).real
          (orderedTupleJointEvent classicalCoherenceThreshold
            (mseq p) p k z c edges))
  · exact Eventually.of_forall fun p ↦ Finset.sum_nonneg fun _ _ ↦
      measureReal_nonneg
  · exact Eventually.of_forall fun p ↦ by
      apply Finset.sum_le_sum
      intro edges _
      exact orderedTupleFiniteUnionWindowJoint_probability_le_lowerTail
        W (mseq p) p k z c hc edges
  · simpa [gaussianCorrelationMeasure] using hupper

end

end LogdetLean.Coherence
