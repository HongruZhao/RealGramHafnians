import LogdetLean.Coherence.AcyclicOrdering
import LogdetLean.Coherence.OverlapAsymptotic
import LogdetLean.Coherence.MatchingPermutation
import Mathlib.Tactic
/-!
# Concrete Gaussian overlap negligibility

This file instantiates the abstract overlap summation theorem.  The raw
joint event is first transported to centered Gaussian columns, its bulk
condition is discarded, and the remaining edge event is bounded by the
ordered spanning-forest certificate constructed in `AcyclicOrdering`.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Module Set Topology
open scoped BigOperators

/-- Squared normalized Gram entries equal squared normalized inner products,
including at zero vectors under Lean's totalized inverse convention. -/
theorem normalizedGram_apply_sq_eq_squaredNormalizedInner_total
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (i j : ι) :
    (normalizedGram v i j) ^ 2 =
      squaredNormalizedInner (v i) (v j) := by
  by_cases hi : v i = 0
  · simp [hi, normalizedGram, normalizeVector, Matrix.gram,
      squaredNormalizedInner]
  by_cases hj : v j = 0
  · simp [hj, normalizedGram, normalizeVector, Matrix.gram,
      squaredNormalizedInner]
  have hni : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
  have hnj : ‖v j‖ ≠ 0 := norm_ne_zero_iff.mpr hj
  unfold normalizedGram normalizeVector squaredNormalizedInner
  simp only [Matrix.gram, real_inner_smul_left, real_inner_smul_right]
  change (‖v j‖⁻¹ * (‖v i‖⁻¹ * inner ℝ (v i) (v j))) ^ 2 =
    (inner ℝ (v i) (v j)) ^ 2 / (‖v i‖ ^ 2 * ‖v j‖ ^ 2)
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [hni, hnj]

/-- Dropping the bulk log-determinant restriction from the centered family
event leaves exactly the tuple's common squared-inner-product exceedances. -/
theorem familyOrderedTupleJointEvent_subset_edgeExceedance
    (m p k : ℕ) (hm : 0 < m) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) :
    familyOrderedTupleJointEvent classicalCoherenceThreshold
        m p k z x edges ⊆
      orderedEdgeTupleFamilyExceedanceEvent
        (E := centeredSubspace (m + 1)) edges
        (classicalCoherenceThreshold m p x / (m : ℝ)) := by
  intro v hv
  rcases hv with ⟨_hbulk, hedge⟩
  intro j
  have hj := hedge j
  have hscaled : classicalCoherenceThreshold m p x <
      (m : ℝ) * squaredNormalizedInner
        (v (edges j).1.1) (v (edges j).1.2) := by
    simpa [orderedEdgeEndpointMap, correlationEdgeEndpoint,
      normalizedGram_apply_sq_eq_squaredNormalizedInner_total] using hj
  exact (scaledSquaredInner_exceedance_iff hm
    (classicalCoherenceThreshold m p x)
    (v (edges j).1.1, v (edges j).1.2)).mp hscaled

/-- Every nonmatching raw Gaussian tuple obeys the concrete forest-power
bound at the classical coherence threshold. -/
theorem gaussianOrderedTupleJoint_le_forestPower_of_not_matching
    (m p k : ℕ) (hm : 2 ≤ m) (z x : ℝ)
    (edges : OrderedDistinctEdgeTuple p k) (hoverlap : ¬edges.IsMatching) :
    (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p).real
        (orderedTupleJointEvent classicalCoherenceThreshold
          m p k z x edges) ≤
      betaCorrelationTailProbability m p x ^
        ((orderedEdgeVertexSet edges).card / 2 + 1) := by
  rw [orderedTupleJointEvent_probability_eq_family]
  let μ : Measure (Fin p → centeredSubspace (m + 1)) :=
    Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace (m + 1))
  let edgeEvent : Set (Fin p → centeredSubspace (m + 1)) :=
    orderedEdgeTupleFamilyExceedanceEvent edges
      (classicalCoherenceThreshold m p x / (m : ℝ))
  have hsubset :
      familyOrderedTupleJointEvent classicalCoherenceThreshold
          m p k z x edges ⊆ edgeEvent :=
    familyOrderedTupleJointEvent_subset_edgeExceedance
      m p k (by omega) z x edges
  have hdim : finrank ℝ (centeredSubspace (m + 1)) = m := by
    simpa using finrank_centeredSubspace (N := m + 1)
  calc
    μ.real
        (familyOrderedTupleJointEvent classicalCoherenceThreshold
          m p k z x edges) ≤ μ.real edgeEvent :=
      measureReal_mono hsubset
    _ ≤ (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Set.Ioi
            (classicalCoherenceThreshold m p x / (m : ℝ)))).toReal ^
        ((orderedEdgeVertexSet edges).card / 2 + 1) := by
      exact gaussianTuple_jointExceedanceReal_le_betaTail_pow_of_not_matching
        edges hoverlap m hdim hm
          (classicalCoherenceThreshold m p x / (m : ℝ))
    _ = betaCorrelationTailProbability m p x ^
        ((orderedEdgeVertexSet edges).card / 2 + 1) := by
      rfl

/-- The complete ordered-overlap contribution tends to zero along every
eventually admissible dimension sequence.  This is the concrete theorem
needed by the mixed factorial-moment decomposition; it has no remaining
configurationwise forest hypothesis. -/
theorem tendsto_gaussianOrderedTupleJoint_overlap_zero
    (k : ℕ) (hk : 0 < k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (z x : ℝ) :
    Tendsto
      (fun p : ℕ ↦
        ∑ edges ∈ orderedOverlapTuples p k,
          (nestedProductMeasure
              (stdGaussian (ObservationSpace (mseq p + 1))) p).real
              (orderedTupleJointEvent classicalCoherenceThreshold
                (mseq p) p k z x edges))
      atTop (nhds 0) := by
  classical
  apply tendsto_gaussianOrderedTupleJoint_overlap_zero_of_forestPower
    k hk hadm z x
  filter_upwards [hadm] with p hp
  intro edges hedges
  have hoverlap : ¬edges.IsMatching :=
    (Finset.mem_filter.mp hedges).2
  exact gaussianOrderedTupleJoint_le_forestPower_of_not_matching
    (mseq p) p k (hp.1.trans hp.2) z x edges hoverlap

end

end LogdetLean.Coherence
