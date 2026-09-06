import LogdetLean.Coherence.FactorialExpansion
import LogdetLean.Coherence.MatchingIntensity
/-!
# Assembly of matching and overlap contributions

This module isolates the last algebraic step of the mixed factorial-moment
proof.  Once every matching has one common conditional bulk factor, the
matching count/intensity theorem and a vanishing overlap sum imply the desired
mixed moment limit.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Model-specific mixed-moment assembly for a fixed `k,z,x`.  The hypothesis
`hmatching` is an exact finite identity: every ordered matching joint event
has probability `q^k * bulkFactor`.  Permutation invariance is what supplies
this identity in the Gaussian model. -/
theorem tendsto_gaussianCoherenceMixedFactorialMoment_of_matching_overlap
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (z x : ℝ) (bulkFactor : ℕ → ℝ)
    (hbulk : Tendsto bulkFactor atTop (nhds (standardNormalCDF z)))
    (hmatching : ∀ᶠ p in atTop,
      ∀ edges ∈ orderedMatchingTuples p k,
        (nestedProductMeasure
            (stdGaussian (ObservationSpace (mseq p + 1))) p).real
            (orderedTupleJointEvent classicalCoherenceThreshold
              (mseq p) p k z x edges) =
          betaCorrelationTailProbability (mseq p) p x ^ k *
            bulkFactor p)
    (hoverlap : Tendsto
      (fun p : ℕ ↦
        ∑ edges ∈ orderedOverlapTuples p k,
          (nestedProductMeasure
              (stdGaussian (ObservationSpace (mseq p + 1))) p).real
              (orderedTupleJointEvent classicalCoherenceThreshold
                (mseq p) p k z x edges))
      atTop (nhds 0)) :
    Tendsto
      (fun p : ℕ ↦ gaussianCoherenceMixedFactorialMoment
        (mseq p) p k z x)
      atTop
      (nhds (standardNormalCDF z * classicalCoherenceIntensity x ^ k)) := by
  have hweight :=
    tendsto_orderedMatching_totalProbabilityWeight k hadm x
  have hmatchingLimit : Tendsto
      (fun p : ℕ ↦
        ((orderedMatchingTuples p k).card : ℝ) *
          betaCorrelationTailProbability (mseq p) p x ^ k *
          bulkFactor p)
      atTop
      (nhds (standardNormalCDF z * classicalCoherenceIntensity x ^ k)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hweight.mul hbulk
  have hsum : Tendsto
      (fun p : ℕ ↦
        (∑ edges ∈ orderedMatchingTuples p k,
          (nestedProductMeasure
              (stdGaussian (ObservationSpace (mseq p + 1))) p).real
              (orderedTupleJointEvent classicalCoherenceThreshold
                (mseq p) p k z x edges)) +
        ∑ edges ∈ orderedOverlapTuples p k,
          (nestedProductMeasure
              (stdGaussian (ObservationSpace (mseq p + 1))) p).real
              (orderedTupleJointEvent classicalCoherenceThreshold
                (mseq p) p k z x edges))
      atTop
      (nhds (standardNormalCDF z * classicalCoherenceIntensity x ^ k)) := by
    have hmatchSum : Tendsto
        (fun p : ℕ ↦
          ∑ edges ∈ orderedMatchingTuples p k,
            (nestedProductMeasure
                (stdGaussian (ObservationSpace (mseq p + 1))) p).real
                (orderedTupleJointEvent classicalCoherenceThreshold
                  (mseq p) p k z x edges))
        atTop
        (nhds (standardNormalCDF z * classicalCoherenceIntensity x ^ k)) := by
      apply hmatchingLimit.congr'
      filter_upwards [hmatching] with p hp
      have hsumEq :
        (∑ edges ∈ orderedMatchingTuples p k,
            (nestedProductMeasure
                (stdGaussian (ObservationSpace (mseq p + 1))) p).real
                (orderedTupleJointEvent classicalCoherenceThreshold
                  (mseq p) p k z x edges)) =
            ((orderedMatchingTuples p k).card : ℝ) *
              betaCorrelationTailProbability (mseq p) p x ^ k *
                bulkFactor p := by
        calc
          (∑ edges ∈ orderedMatchingTuples p k,
              (nestedProductMeasure
                  (stdGaussian (ObservationSpace (mseq p + 1))) p).real
                  (orderedTupleJointEvent classicalCoherenceThreshold
                    (mseq p) p k z x edges)) =
              ∑ _edges ∈ orderedMatchingTuples p k,
                betaCorrelationTailProbability (mseq p) p x ^ k *
                  bulkFactor p := by
                    apply Finset.sum_congr rfl
                    intro edges hedges
                    exact hp edges hedges
          _ = ((orderedMatchingTuples p k).card : ℝ) *
                (betaCorrelationTailProbability (mseq p) p x ^ k *
                  bulkFactor p) := by simp
          _ = ((orderedMatchingTuples p k).card : ℝ) *
                betaCorrelationTailProbability (mseq p) p x ^ k *
                  bulkFactor p := by ring
      exact hsumEq.symm
    simpa using hmatchSum.add hoverlap
  apply hsum.congr'
  filter_upwards [] with p
  exact (thresholdMixedFactorialMoment_eq_matching_add_overlap
    classicalCoherenceThreshold (mseq p) p k z x).symm

end

end LogdetLean.Coherence
