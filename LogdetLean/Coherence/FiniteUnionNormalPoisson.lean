import LogdetLean.Coherence.MatchingFiniteUnionWindowFactorization
import LogdetLean.Coherence.FiniteUnionMixedMomentAssembly
import LogdetLean.Coherence.FiniteUnionOverlap
import LogdetLean.Coherence.MixedMomentZero
import LogdetLean.Coherence.ExactCountFactorialLimit
/-!
# Finite disjoint score unions: mixed moments and the Normal--Poisson void law

For a fixed finite disjoint union of normalized coherence-score windows with
positive limiting intensity, this module proves all fixed mixed factorial
moments and the exact joint log-determinant/void limit.  These are the scalar
mean/void ingredients used by a Kallenberg criterion.  No random point-measure
space or vague-topology convergence theorem is asserted here.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## All fixed mixed factorial moments -/

/-- Positive-order finite-union mixed factorial-moment limit. -/
theorem tendsto_gaussianCoherenceFiniteUnionMixedFactorialMoment_positive
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) (z : ℝ) :
    Tendsto
      (fun p ↦ gaussianCoherenceFiniteUnionMixedFactorialMoment
        W (mseq p) p k z)
      atTop
      (nhds (standardNormalCDF z *
        (finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
  apply
    tendsto_gaussianCoherenceFiniteUnionMixedFactorialMoment_of_matching_overlap
      W k hadm z
      (fun p ↦ canonicalFiniteUnionConditionedZ0mpCDFOrGaussian
        W k (mseq p) p z)
  · exact tendsto_canonicalFiniteUnionConditionedZ0mpCDFOrGaussian
      W k hk c hc hadm hnu z
  · have hs0 :=
      eventually_canonicalCenteredMatchingFiniteUnionPrefixEvent_ne_zero
        W k hadm hnu
    filter_upwards [hadm, hs0] with p hp hs0p
    intro edges hedges
    exact
      orderedMatchingFiniteUnionWindowJointEvent_probability_factorization_of_mem
        W (mseq p) p k (hp.1.trans hp.2) hp.2 z edges hedges hs0p
  · exact
      tendsto_gaussianOrderedTupleFiniteUnionWindowJoint_overlap_zero
        W k (by omega) hadm z c hc

/-- At order zero, the finite-union count disappears and the mixed moment is
the ordinary order-zero Gaussian log-determinant mixed moment. -/
theorem gaussianCoherenceFiniteUnionMixedFactorialMoment_zero_eq
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (z x : ℝ) :
    gaussianCoherenceFiniteUnionMixedFactorialMoment W m p 0 z =
      gaussianCoherenceMixedFactorialMoment m p 0 z x := by
  unfold gaussianCoherenceFiniteUnionMixedFactorialMoment
    gaussianCoherenceMixedFactorialMoment thresholdMixedFactorialMoment
  simp [gaussianCorrelationMeasure]

/-- The order-zero finite-union mixed moment has the Gaussian CDF limit. -/
theorem tendsto_gaussianCoherenceFiniteUnionMixedFactorialMoment_zero
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (z : ℝ) :
    Tendsto
      (fun p ↦ gaussianCoherenceFiniteUnionMixedFactorialMoment
        W (mseq p) p 0 z)
      atTop (nhds (standardNormalCDF z)) := by
  apply (tendsto_gaussianCoherenceMixedFactorialMoment_zero
    mseq hadm z z).congr'
  filter_upwards [] with p
  exact gaussianCoherenceFiniteUnionMixedFactorialMoment_zero_eq
    W (mseq p) p z z

/-- Complete finite-union mixed factorial-moment limit for every fixed order,
including zero. -/
theorem tendsto_gaussianCoherenceFiniteUnionMixedFactorialMoment
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) (c : ℝ) (hc : ∀ i, c ≤ W.lower i)
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) (z : ℝ) :
    Tendsto
      (fun p ↦ gaussianCoherenceFiniteUnionMixedFactorialMoment
        W (mseq p) p k z)
      atTop
      (nhds (standardNormalCDF z *
        (finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
  cases k with
  | zero =>
      simpa using
        tendsto_gaussianCoherenceFiniteUnionMixedFactorialMoment_zero
          W mseq hadm z
  | succ k =>
      exact tendsto_gaussianCoherenceFiniteUnionMixedFactorialMoment_positive
        W (k + 1) (by omega) c hc hadm hnu z

/-! ## Exact count probabilities and finite count algebra -/

/-- Actual joint probability of the standardized log determinant lower-tail
event and exactly `r` scores in the finite window union. -/
def gaussianCoherenceFiniteUnionJointExactCountProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) (z : ℝ) : ℝ :=
  ∫ data : GaussianCorrelationSample m p,
    if Z0mpStatistic m p data ≤ z ∧
        coherenceFiniteUnionWindowCount W m p data = r then 1 else 0
  ∂gaussianCorrelationMeasure m p

theorem measurable_gaussianCoherenceFiniteUnionJointExactCountIntegrand
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) (z : ℝ) :
    Measurable (fun data : GaussianCorrelationSample m p ↦
      if Z0mpStatistic m p data ≤ z ∧
          coherenceFiniteUnionWindowCount W m p data = r then
        (1 : ℝ) else 0) := by
  apply Measurable.ite
  · exact (measurableSet_le (measurable_Z0mpStatistic m p)
      measurable_const).inter
      (measurable_coherenceFiniteUnionWindowCount W m p
        (measurableSet_singleton r))
  · exact measurable_const
  · exact measurable_const

theorem integrable_gaussianCoherenceFiniteUnionJointExactCountIntegrand
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) (z : ℝ) :
    Integrable (fun data : GaussianCorrelationSample m p ↦
      if Z0mpStatistic m p data ≤ z ∧
          coherenceFiniteUnionWindowCount W m p data = r then
        (1 : ℝ) else 0)
      (gaussianCorrelationMeasure m p) := by
  let _ : IsProbabilityMeasure (gaussianCorrelationMeasure m p) := by
    unfold gaussianCorrelationMeasure
    infer_instance
  apply Integrable.of_bound
    (measurable_gaussianCoherenceFiniteUnionJointExactCountIntegrand
      W m p r z).aestronglyMeasurable 1
  filter_upwards [] with data
  split <;> simp

/-- The integral is exactly the real-valued probability of the measurable
joint exact-count event. -/
theorem gaussianCoherenceFiniteUnionJointExactCountProbability_eq_measureReal
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) (z : ℝ) :
    gaussianCoherenceFiniteUnionJointExactCountProbability W m p r z =
      (gaussianCorrelationMeasure m p).real
        {data | Z0mpStatistic m p data ≤ z ∧
          coherenceFiniteUnionWindowCount W m p data = r} := by
  let A : Set (GaussianCorrelationSample m p) :=
    {data | Z0mpStatistic m p data ≤ z ∧
      coherenceFiniteUnionWindowCount W m p data = r}
  have hA : MeasurableSet A :=
    (measurableSet_le (measurable_Z0mpStatistic m p)
      measurable_const).inter
      (measurable_coherenceFiniteUnionWindowCount W m p
        (measurableSet_singleton r))
  unfold gaussianCoherenceFiniteUnionJointExactCountProbability
  have hindicator :
      (fun data : GaussianCorrelationSample m p ↦
        if Z0mpStatistic m p data ≤ z ∧
            coherenceFiniteUnionWindowCount W m p data = r then
          (1 : ℝ) else 0) =
        A.indicator (fun _ ↦ (1 : ℝ)) := by
    funext data
    by_cases h : Z0mpStatistic m p data ≤ z ∧
        coherenceFiniteUnionWindowCount W m p data = r
    · simp [A, h]
    · simp [A, h]
  rw [hindicator]
  exact integral_indicator_one hA

theorem gaussianCoherenceFiniteUnionJointExactCountProbability_nonneg
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) (z : ℝ) :
    0 ≤ gaussianCoherenceFiniteUnionJointExactCountProbability
      W m p r z := by
  rw [gaussianCoherenceFiniteUnionJointExactCountProbability_eq_measureReal]
  exact measureReal_nonneg

/-- Exact identification of the finite array's factorial moments with the
model-specific mixed factorial moments.  `extra` is a harmless support
enlargement used to ensure any fixed requested count belongs to the cap. -/
theorem finiteCountWeightedFactorialMoment_finiteUnionJointExactCount_eq
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (mseq : ℕ → ℕ) (extra p k : ℕ) (z : ℝ) :
    finiteCountWeightedFactorialMoment
        (fun n ↦ n.choose 2 + extra)
        (fun n r ↦ gaussianCoherenceFiniteUnionJointExactCountProbability
          W (mseq n) n r z)
        p k =
      gaussianCoherenceFiniteUnionMixedFactorialMoment
        W (mseq p) p k z := by
  let μ := gaussianCorrelationMeasure (mseq p) p
  let f : ℕ → GaussianCorrelationSample (mseq p) p → ℝ :=
    fun r data ↦
      if Z0mpStatistic (mseq p) p data ≤ z ∧
          coherenceFiniteUnionWindowCount W (mseq p) p data = r then
        (1 : ℝ) else 0
  have hf (r : ℕ) : Integrable (f r) μ := by
    exact integrable_gaussianCoherenceFiniteUnionJointExactCountIntegrand
      W (mseq p) p r z
  unfold finiteCountWeightedFactorialMoment
    gaussianCoherenceFiniteUnionJointExactCountProbability
  change
    (∑ r ∈ Finset.range (p.choose 2 + extra + 1),
      (∫ data, f r data ∂μ) * (r.descFactorial k : ℝ)) = _
  calc
    (∑ r ∈ Finset.range (p.choose 2 + extra + 1),
        (∫ data, f r data ∂μ) * (r.descFactorial k : ℝ)) =
        ∑ r ∈ Finset.range (p.choose 2 + extra + 1),
          ∫ data, f r data * (r.descFactorial k : ℝ) ∂μ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [integral_mul_const]
    _ = ∫ data, ∑ r ∈ Finset.range (p.choose 2 + extra + 1),
          f r data * (r.descFactorial k : ℝ) ∂μ := by
      rw [integral_finsetSum]
      intro r _
      exact (hf r).mul_const _
    _ = ∫ data,
          if Z0mpStatistic (mseq p) p data ≤ z then
            ((coherenceFiniteUnionWindowCount
              W (mseq p) p data).descFactorial k : ℝ)
          else 0 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with data
      let C := coherenceFiniteUnionWindowCount W (mseq p) p data
      have hC : C ∈ Finset.range (p.choose 2 + extra + 1) := by
        simp only [Finset.mem_range]
        have hle := coherenceFiniteUnionWindowCount_le_card_edges
          W (mseq p) p data
        dsimp [C]
        omega
      by_cases hbulk : Z0mpStatistic (mseq p) p data ≤ z
      · have hsum :
            (∑ r ∈ Finset.range (p.choose 2 + extra + 1),
              f r data * (r.descFactorial k : ℝ)) =
              f C data * (C.descFactorial k : ℝ) := by
          apply Finset.sum_eq_single C
          · intro r _ hne
            have hcount :
                coherenceFiniteUnionWindowCount W (mseq p) p data ≠ r := by
              intro heq
              apply hne
              simpa [C] using heq.symm
            simp [f, hbulk, hcount]
          · intro hnot
            exact (hnot hC).elim
        rw [hsum]
        simp [f, C, hbulk]
      · simp [f, hbulk]
    _ = gaussianCoherenceFiniteUnionMixedFactorialMoment
          W (mseq p) p k z := by
      rfl

/-! ## Exact and limiting mean count -/

/-- The expected number of normalized coherence scores in the finite union is
exactly its finite one-edge intensity. -/
theorem integral_coherenceFiniteUnionWindowCount_eq_intensity
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p : ℕ} (hm : 2 ≤ m) :
    (∫ data : GaussianCorrelationSample m p,
        (coherenceFiniteUnionWindowCount W m p data : ℝ)
      ∂gaussianCorrelationMeasure m p) =
      finiteUnionCoherenceIntensity W m p := by
  let μ := gaussianCorrelationMeasure m p
  let f : CorrelationEdge p → GaussianCorrelationSample m p → ℝ :=
    fun e data ↦
      if data ∈ coherenceFiniteUnionWindowEvent W m p e then 1 else 0
  let _ : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold gaussianCorrelationMeasure
    infer_instance
  have hf (e : CorrelationEdge p) : Integrable (f e) μ := by
    apply Integrable.of_bound
      ((Measurable.ite
        (measurableSet_coherenceFiniteUnionWindowEvent W m p e)
        measurable_const measurable_const).aestronglyMeasurable) 1
    filter_upwards [] with data
    dsimp [f]
    split_ifs <;> simp_all
  have hint (e : CorrelationEdge p) :
      (∫ data, f e data ∂μ) =
        μ.real (coherenceFiniteUnionWindowEvent W m p e) := by
    have heq : f e =
        (coherenceFiniteUnionWindowEvent W m p e).indicator
          (fun _ ↦ (1 : ℝ)) := by
      funext data
      by_cases h : data ∈ coherenceFiniteUnionWindowEvent W m p e
      · simp [f, h]
      · simp [f, h]
    rw [heq]
    exact integral_indicator_one
      (measurableSet_coherenceFiniteUnionWindowEvent W m p e)
  calc
    (∫ data : GaussianCorrelationSample m p,
        (coherenceFiniteUnionWindowCount W m p data : ℝ) ∂μ) =
        ∫ data, ∑ e : CorrelationEdge p, f e data ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with data
      simp [coherenceFiniteUnionWindowCount, f,
        coherenceFiniteUnionWindowEvent_eq_preimage]
    _ = ∑ e : CorrelationEdge p, ∫ data, f e data ∂μ := by
      exact integral_finsetSum
        (Finset.univ : Finset (CorrelationEdge p))
        (fun e _ ↦ hf e)
    _ = ∑ e : CorrelationEdge p,
          μ.real (coherenceFiniteUnionWindowEvent W m p e) := by
      apply Finset.sum_congr rfl
      intro e _
      exact hint e
    _ = ∑ _e : CorrelationEdge p,
          finiteUnionBetaProbability W m p := by
      apply Finset.sum_congr rfl
      intro e _
      exact coherenceFiniteUnionWindowEvent_probability W hm e
    _ = finiteUnionCoherenceIntensity W m p := by
      simp [finiteUnionCoherenceIntensity, card_correlationEdge]

/-- Consequently, the actual expected finite-union count converges to the
limiting finite-union intensity along every admissible all-gap sequence. -/
theorem tendsto_integral_coherenceFiniteUnionWindowCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto
      (fun p ↦ ∫ data : GaussianCorrelationSample (mseq p) p,
        (coherenceFiniteUnionWindowCount W (mseq p) p data : ℝ)
        ∂gaussianCorrelationMeasure (mseq p) p)
      atTop (nhds (finiteUnionClassicalCoherenceIntensity W)) := by
  apply (tendsto_finiteUnionCoherenceIntensity W hadm).congr'
  filter_upwards [hadm] with p hp
  exact (integral_coherenceFiniteUnionWindowCount_eq_intensity
    W (hp.1.trans hp.2)).symm

/-! ## Normal--Poisson exact counts and the void criterion -/

/-- Every fixed finite-union count has the joint Normal--Poisson product
mass limit. -/
theorem tendsto_gaussianCoherenceFiniteUnionJointExactCountProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (r : ℕ) (c : ℝ) (hc : ∀ i, c ≤ W.lower i)
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) (z : ℝ) :
    Tendsto
      (fun p ↦ gaussianCoherenceFiniteUnionJointExactCountProbability
        W (mseq p) p r z)
      atTop
      (nhds (standardNormalCDF z *
        poissonExactMass (finiteUnionClassicalCoherenceIntensity W) r)) := by
  let cap : ℕ → ℕ := fun p ↦ p.choose 2 + r
  let mass : ℕ → ℕ → ℝ := fun p s ↦
    gaussianCoherenceFiniteUnionJointExactCountProbability
      W (mseq p) p s z
  have hmass : ∀ p s, 0 ≤ mass p s := by
    intro p s
    exact gaussianCoherenceFiniteUnionJointExactCountProbability_nonneg
      W (mseq p) p s z
  have hcap : ∀ᶠ p in atTop, r ≤ cap p :=
    Eventually.of_forall fun p ↦ by simp [cap]
  have hmom (k : ℕ) :
      Tendsto
        (fun p ↦ finiteCountWeightedFactorialMoment cap mass p k)
        atTop
        (nhds (standardNormalCDF z *
          (finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
    apply (tendsto_gaussianCoherenceFiniteUnionMixedFactorialMoment
      W k c hc hadm hnu z).congr'
    filter_upwards [] with p
    exact
      (finiteCountWeightedFactorialMoment_finiteUnionJointExactCount_eq
        W mseq r p k z).symm
  exact tendsto_finiteCountCoefficient_of_factorialMoments
    cap mass (standardNormalCDF z)
      (finiteUnionClassicalCoherenceIntensity W) r hmass hcap hmom

/-- The actual joint log-determinant/finite-union void probability. -/
def gaussianCoherenceFiniteUnionJointVoidProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (z : ℝ) : ℝ :=
  gaussianCoherenceFiniteUnionJointExactCountProbability W m p 0 z

/-- **Finite-union Normal--Poisson void criterion.**  The joint probability
of the standardized log determinant lying below `z` and no normalized
coherence score lying in the fixed finite disjoint union converges to
`Phi(z) * exp (-nu(W))`. -/
theorem tendsto_gaussianCoherenceFiniteUnionJointVoidProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (c : ℝ) (hc : ∀ i, c ≤ W.lower i) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) (z : ℝ) :
    Tendsto
      (fun p ↦ gaussianCoherenceFiniteUnionJointVoidProbability
        W (mseq p) p z)
      atTop
      (nhds (standardNormalCDF z *
        Real.exp (-finiteUnionClassicalCoherenceIntensity W))) := by
  simpa [gaussianCoherenceFiniteUnionJointVoidProbability,
    poissonExactMass] using
    tendsto_gaussianCoherenceFiniteUnionJointExactCountProbability
      W 0 c hc hadm hnu z

/-- Bundled scalar mean/void criterion: the exact finite-union one-edge
intensity converges to `nu(W)`, while the decorated void probability has the
Normal--Poisson product limit.  This statement is not itself a theorem about
vague convergence of random point measures. -/
theorem finiteUnionMeanJointVoidCriterion
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (c : ℝ) (hc : ∀ i, c ≤ W.lower i) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) (z : ℝ) :
    Tendsto
        (fun p ↦ ∫ data : GaussianCorrelationSample (mseq p) p,
          (coherenceFiniteUnionWindowCount W (mseq p) p data : ℝ)
          ∂gaussianCorrelationMeasure (mseq p) p)
        atTop (nhds (finiteUnionClassicalCoherenceIntensity W)) ∧
      Tendsto
        (fun p ↦ gaussianCoherenceFiniteUnionJointVoidProbability
          W (mseq p) p z)
        atTop
        (nhds (standardNormalCDF z *
          Real.exp (-finiteUnionClassicalCoherenceIntensity W))) := by
  exact ⟨tendsto_integral_coherenceFiniteUnionWindowCount W hadm,
    tendsto_gaussianCoherenceFiniteUnionJointVoidProbability
      W c hc hadm hnu z⟩

end

end LogdetLean.Coherence
