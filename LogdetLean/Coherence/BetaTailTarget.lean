import LogdetLean.Coherence.ModelAndTargets
/-!
# The analytic single-edge Beta-tail target

The exact pair law reduces the extreme-value marginal to one deterministic
Beta-tail asymptotic.  This file records that remaining analytic target and
proves the exact event/probability reduction feeding it.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Module Set

/-- Tail probability of `Beta(1/2,(m-1)/2)` above the classical squared
correlation threshold. -/
def betaCorrelationTailProbability (m p : ℕ) (x : ℝ) : ℝ :=
  (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
    (Ioi (classicalCoherenceThreshold m p x / (m : ℝ)))).toReal

/-- The exact analytic statement needed for the one-edge Poisson intensity,
uniformly over all nonsingular gap regimes.  This is a target, not an axiom. -/
def AllGapBetaTailIntensityTarget : Prop :=
  ∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      ∀ x : ℝ,
        Tendsto
          (fun p ↦ ((p.choose 2 : ℕ) : ℝ) *
            betaCorrelationTailProbability (mseq p) p x)
          atTop (nhds (classicalCoherenceIntensity x))

/-- Both Beta parameters in the one-edge law are positive in dimension
`m ≥ 2`. -/
theorem pairBeta_shapes_pos {m : ℕ} (hm : 2 ≤ m) :
    (0 : ℝ) < 1 / 2 ∧ (0 : ℝ) < ((m - 1 : ℕ) : ℝ) / 2 := by
  constructor
  · norm_num
  · exact div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num)

/-- Consequently the exact one-edge Beta measure is a probability measure. -/
theorem pairBeta_isProbabilityMeasure {m : ℕ} (hm : 2 ≤ m) :
    IsProbabilityMeasure
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) := by
  exact isProbabilityMeasureBeta (pairBeta_shapes_pos hm).1
    (pairBeta_shapes_pos hm).2

/-- Scaling a squared correlation by a positive dimension converts the
exceedance event to the corresponding Beta-tail event. -/
theorem scaledSquaredInner_exceedance_iff
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (hm : 0 < m) (t : ℝ) (z : E × E) :
    t < (m : ℝ) * squaredNormalizedInner z.1 z.2 ↔
      t / (m : ℝ) < squaredNormalizedInner z.1 z.2 := by
  have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  constructor <;> intro h
  · exact (div_lt_iff₀ hmreal).2 (by simpa [mul_comm] using h)
  · simpa [mul_comm] using (div_lt_iff₀ hmreal).1 h

/-- Exact ENNReal-valued probability identity for a single scaled Gaussian
correlation exceedance. -/
theorem gaussianPair_scaledSquaredInner_exceedance_eq_betaTail
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m) (t : ℝ) :
    ((stdGaussian E).prod (stdGaussian E))
        {z | t < (m : ℝ) * squaredNormalizedInner z.1 z.2} =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
        (Ioi (t / (m : ℝ))) := by
  let score : E × E → ℝ := fun z ↦ squaredNormalizedInner z.1 z.2
  have hscore : Measurable score :=
    measurable_uncurry_squaredNormalizedInner
  have hset : {z : E × E |
      t < (m : ℝ) * squaredNormalizedInner z.1 z.2} =
      score ⁻¹' Ioi (t / (m : ℝ)) := by
    ext z
    exact scaledSquaredInner_exceedance_iff (by omega : 0 < m) t z
  rw [hset, ← Measure.map_apply hscore measurableSet_Ioi]
  exact congrArg (fun μ : Measure ℝ ↦ μ (Ioi (t / (m : ℝ))))
    (map_squaredNormalizedInner_gaussianProduct m hdim hm)

/-- Real-valued specialization at the classical coherence threshold. -/
theorem gaussianPair_classicalExceedanceProbability_eq_betaCorrelationTail
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m p : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m) (x : ℝ) :
    (((stdGaussian E).prod (stdGaussian E))
      {z | classicalCoherenceThreshold m p x <
        (m : ℝ) * squaredNormalizedInner z.1 z.2}).toReal =
      betaCorrelationTailProbability m p x := by
  unfold betaCorrelationTailProbability
  rw [gaussianPair_scaledSquaredInner_exceedance_eq_betaTail
    m hdim hm (classicalCoherenceThreshold m p x)]

end

end LogdetLean.Coherence
