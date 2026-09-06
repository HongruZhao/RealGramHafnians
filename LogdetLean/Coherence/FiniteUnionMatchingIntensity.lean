import LogdetLean.Coherence.FiniteUnionScoreWindow
import LogdetLean.Coherence.MatchingIntensity
/-!
# Matching intensity for a finite disjoint union of score windows

This file combines the exact ordered-matching count with the all-gap
one-edge intensity of a finite disjoint union.  It is the finite-union
counterpart of `WindowMatchingIntensity`.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Topology

/-- Multiplying a finite-union one-edge probability by `p^2/2` has the same
limit as multiplying it by `p.choose 2`. -/
theorem tendsto_half_sq_mul_finiteUnionBetaProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto
      (fun p : ℕ ↦ ((p : ℝ) ^ 2 / 2) *
        finiteUnionBetaProbability W (mseq p) p)
      atTop (nhds (finiteUnionClassicalCoherenceIntensity W)) := by
  have hunion := tendsto_finiteUnionCoherenceIntensity W hadm
  have hedge := tendsto_two_mul_choose_two_div_sq_one
  have hquot := hunion.div hedge (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' : Tendsto
      ((fun p : ℕ ↦ finiteUnionCoherenceIntensity W (mseq p) p) /
        (fun p : ℕ ↦
          2 * ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2))
      atTop (nhds (finiteUnionClassicalCoherenceIntensity W)) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  have hchooseN : 0 < p.choose 2 := Nat.choose_pos hp
  have hchoose : (((p.choose 2 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hchooseN.ne'
  change
    ((((p.choose 2 : ℕ) : ℝ) *
        finiteUnionBetaProbability W (mseq p) p) /
        (2 * ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2)) =
      (p : ℝ) ^ 2 / 2 *
        finiteUnionBetaProbability W (mseq p) p
  field_simp [hp0, hchoose]

/-- Total probability weight of all ordered `k`-edge matchings whose scores
lie in the finite union. -/
theorem tendsto_orderedMatching_finiteUnionTotalProbabilityWeight
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto
      (fun p : ℕ ↦
        ((orderedMatchingTuples p k).card : ℝ) *
          finiteUnionBetaProbability W (mseq p) p ^ k)
      atTop
      (nhds ((finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
  have hcount := tendsto_orderedMatching_count_normalized k
  have hunion := tendsto_half_sq_mul_finiteUnionBetaProbability W hadm
  have hprod : Tendsto
      (fun p : ℕ ↦
        (((orderedMatchingTuples p k).card : ℝ) * (2 : ℝ) ^ k /
            (p : ℝ) ^ (2 * k)) *
          ((((p : ℝ) ^ 2 / 2) *
            finiteUnionBetaProbability W (mseq p) p) ^ k))
      atTop
      (nhds ((finiteUnionClassicalCoherenceIntensity W) ^ k)) := by
    simpa using hcount.mul (hunion.pow k)
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  rw [mul_pow, div_pow, pow_mul]
  field_simp [hp0]

end

end LogdetLean.Coherence
