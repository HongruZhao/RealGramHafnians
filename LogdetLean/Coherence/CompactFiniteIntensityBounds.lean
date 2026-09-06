import LogdetLean.Coherence.CompactOneEdgeConditions
/-!
# Positive compact-window bounds for the finite coherence intensity

The marked Poisson Stein equation needs a strictly positive intensity and a
compact upper bound.  Both follow from the already proved Beta Mills
sandwich under the same compact-rate conditions.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real

/-- A convenient dimension-free upper bound for the exact finite intensity
on `|x| ≤ M`. -/
def compactFiniteIntensityUpper (M : ℝ) : ℝ :=
  Real.exp (M / 2) * (√2 / √Real.pi) * (81 + 4 * M)

theorem compactFiniteIntensityUpper_nonneg
    {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ compactFiniteIntensityUpper M := by
  unfold compactFiniteIntensityUpper
  positivity

/-- The exact finite intensity is positive and bounded by a constant
depending only on the fixed compact threshold window. -/
theorem finiteCoherenceIntensity_pos_le_compactUpper
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    0 < finiteCoherenceIntensity m p x ∧
      finiteCoherenceIntensity m p x ≤ compactFiniteIntensityUpper M := by
  have hone := compactBetaRateConditions_oneEdge_bounds hcond hpm hx
  have hf := compactBetaRateConditions_finite_bounds hcond hpm hx
  have hm4 : 4 ≤ m := by omega
  have hlogOne : 1 ≤ Real.log (p : ℝ) := hone.2.2.2.1
  have hp2 : 2 ≤ p := by
    by_contra hp
    have hp_le : p ≤ 1 := by omega
    interval_cases p <;> norm_num at hlogOne
  have hendpoint := betaCorrelationEndpointIntensity_pos
    hp2 hm4 hf.1 hf.2.1
  have hmills := finiteCoherenceIntensity_mills_bounds
    hm4 hf.1 hf.2.1
  have hrateLower := betaCorrelationMillsRate_ge_log hcond hpm hx
  have hlogPos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le zero_lt_one hlogOne
  have hratePos : 0 < betaCorrelationMillsRate m p x :=
    hlogPos.trans_le hrateLower
  have hden : 0 < 1 + 1 / betaCorrelationMillsRate m p x := by positivity
  have hlowerPos : 0 < betaCorrelationEndpointIntensity m p x /
      (1 + 1 / betaCorrelationMillsRate m p x) :=
    div_pos hendpoint hden
  have hupper := betaCorrelationEndpointIntensity_le_compact_constant
    hcond hpm hx
  constructor
  · exact hlowerPos.trans_le hmills.1
  · exact hmills.2.trans (by
      simpa [compactFiniteIntensityUpper] using hupper.2)

/-- Eventual uniform cutoff form. -/
theorem eventually_uniform_finiteCoherenceIntensity_pos_le_compactUpper
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ P : ℕ, ∀ p ≥ P, ∀ m ≥ p, ∀ x : ℝ, |x| ≤ M →
      0 < finiteCoherenceIntensity m p x ∧
        finiteCoherenceIntensity m p x ≤ compactFiniteIntensityUpper M := by
  obtain ⟨P, hP⟩ := eventually_atTop.1
    (eventually_compactBetaRateConditions hM)
  refine ⟨P, ?_⟩
  intro p hp m hpm x hx
  exact finiteCoherenceIntensity_pos_le_compactUpper (hP p hp) hpm hx

end

end LogdetLean.Coherence
