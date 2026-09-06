import LogdetLean.Coherence.FiniteUnionFactorialExpansion
import LogdetLean.Coherence.FiniteUnionMatchingIntensity
/-!
# Assembly of finite-union matching and overlap contributions

An exact common matching factor, the finite-union matching-intensity limit,
and a vanishing overlap sum imply the decorated mixed factorial-moment limit.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory Topology
open scoped BigOperators

theorem tendsto_gaussianCoherenceFiniteUnionMixedFactorialMoment_of_matching_overlap
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (z : ℝ) (bulkFactor : ℕ → ℝ)
    (hbulk : Tendsto bulkFactor atTop (nhds (standardNormalCDF z)))
    (hmatching : ∀ᶠ p in atTop,
      ∀ edges ∈ orderedMatchingTuples p k,
        (gaussianCorrelationMeasure (mseq p) p).real
            (orderedTupleFiniteUnionWindowJointEvent
              W (mseq p) p k z edges) =
          finiteUnionBetaProbability W (mseq p) p ^ k * bulkFactor p)
    (hoverlap : Tendsto
      (fun p : ℕ ↦
        ∑ edges ∈ orderedOverlapTuples p k,
          (gaussianCorrelationMeasure (mseq p) p).real
            (orderedTupleFiniteUnionWindowJointEvent
              W (mseq p) p k z edges))
      atTop (nhds 0)) :
    Tendsto
      (fun p : ℕ ↦ gaussianCoherenceFiniteUnionMixedFactorialMoment
        W (mseq p) p k z)
      atTop
      (nhds (standardNormalCDF z *
        (finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
  have hweight := tendsto_orderedMatching_finiteUnionTotalProbabilityWeight
    W k hadm
  have hmatchingLimit : Tendsto
      (fun p : ℕ ↦
        ((orderedMatchingTuples p k).card : ℝ) *
          finiteUnionBetaProbability W (mseq p) p ^ k * bulkFactor p)
      atTop
      (nhds (standardNormalCDF z *
        (finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hweight.mul hbulk
  have hmatchSum : Tendsto
      (fun p : ℕ ↦
        ∑ edges ∈ orderedMatchingTuples p k,
          (gaussianCorrelationMeasure (mseq p) p).real
            (orderedTupleFiniteUnionWindowJointEvent
              W (mseq p) p k z edges))
      atTop
      (nhds (standardNormalCDF z *
        (finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
    apply hmatchingLimit.congr'
    filter_upwards [hmatching] with p hp
    have hsumEq :
      (∑ edges ∈ orderedMatchingTuples p k,
          (gaussianCorrelationMeasure (mseq p) p).real
            (orderedTupleFiniteUnionWindowJointEvent
              W (mseq p) p k z edges)) =
          ((orderedMatchingTuples p k).card : ℝ) *
            finiteUnionBetaProbability W (mseq p) p ^ k * bulkFactor p := by
      calc
        (∑ edges ∈ orderedMatchingTuples p k,
            (gaussianCorrelationMeasure (mseq p) p).real
              (orderedTupleFiniteUnionWindowJointEvent
                W (mseq p) p k z edges)) =
            ∑ _edges ∈ orderedMatchingTuples p k,
              finiteUnionBetaProbability W (mseq p) p ^ k *
                bulkFactor p := by
                  apply Finset.sum_congr rfl
                  intro edges hedges
                  exact hp edges hedges
        _ = ((orderedMatchingTuples p k).card : ℝ) *
              (finiteUnionBetaProbability W (mseq p) p ^ k *
                bulkFactor p) := by simp
        _ = ((orderedMatchingTuples p k).card : ℝ) *
              finiteUnionBetaProbability W (mseq p) p ^ k *
                bulkFactor p := by ring
    exact hsumEq.symm
  have hsum : Tendsto
      (fun p : ℕ ↦
        (∑ edges ∈ orderedMatchingTuples p k,
          (gaussianCorrelationMeasure (mseq p) p).real
            (orderedTupleFiniteUnionWindowJointEvent
              W (mseq p) p k z edges)) +
        ∑ edges ∈ orderedOverlapTuples p k,
          (gaussianCorrelationMeasure (mseq p) p).real
            (orderedTupleFiniteUnionWindowJointEvent
              W (mseq p) p k z edges))
      atTop
      (nhds (standardNormalCDF z *
        (finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
    simpa using hmatchSum.add hoverlap
  apply hsum.congr'
  filter_upwards [] with p
  exact (gaussianCoherenceFiniteUnionMixedFactorialMoment_eq_matching_add_overlap
    W (mseq p) p k z).symm

end

end LogdetLean.Coherence
