import LogdetLean.Coherence.BetaEndpointAsymptotic
import LogdetLean.Coherence.MatchingCount
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic
/-!
# The fixed-order matching contribution

For a fixed number `k` of disjoint edges, every matching event has probability
equal to the `k`th power of the one-edge beta tail.  This file proves that the
total weight of all ordered matchings converges to the `k`th power of the
classical coherence intensity.

The deterministic normalization is kept explicit.  First,

`(p)_{n} / p^n → 1`

for every fixed `n`.  The exact matching count then yields

`#matchings * 2^k / p^(2k) → 1`.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Topology

/-- Removing a fixed natural number from `p` is asymptotically negligible. -/
theorem tendsto_natCast_sub_div_natCast_one (r : ℕ) :
    Tendsto (fun p : ℕ ↦ (((p - r : ℕ) : ℝ) / (p : ℝ)))
      atTop (nhds 1) := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun p : ℕ ↦ (r : ℝ) / (p : ℝ))
      atTop (nhds 0) := hpR.const_div_atTop (r : ℝ)
  have hlim : Tendsto (fun p : ℕ ↦ 1 - (r : ℝ) / (p : ℝ))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds :
      Tendsto (fun _p : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub hsmall
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop r, eventually_ge_atTop 1] with p hpr hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [Nat.cast_sub hpr]
  field_simp [hp0]

/-- Fixed-order falling-factorial normalization. -/
theorem tendsto_descFactorial_div_pow_one (n : ℕ) :
    Tendsto
      (fun p : ℕ ↦ ((p.descFactorial n : ℕ) : ℝ) / (p : ℝ) ^ n)
      atTop (nhds 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfactor := tendsto_natCast_sub_div_natCast_one n
      have hprod : Tendsto
          (fun p : ℕ ↦ (((p - n : ℕ) : ℝ) / (p : ℝ)) *
            (((p.descFactorial n : ℕ) : ℝ) / (p : ℝ) ^ n))
          atTop (nhds 1) := by
        simpa using hfactor.mul ih
      apply hprod.congr'
      filter_upwards [eventually_ge_atTop 1] with p hp
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
      rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      field_simp [hp0]

/-- The number of unordered edges is asymptotic to `p²/2`. -/
theorem tendsto_two_mul_choose_two_div_sq_one :
    Tendsto
      (fun p : ℕ ↦
        2 * ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2)
      atTop (nhds 1) := by
  have hpred := tendsto_natCast_sub_div_natCast_one 1
  apply hpred.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [Nat.cast_choose_two, Nat.cast_sub hp, Nat.cast_one]
  field_simp [hp0]

/-- Exact matching enumeration plus the fixed falling-factorial limit gives
the normalized ordered-matching count. -/
theorem tendsto_orderedMatching_count_normalized (k : ℕ) :
    Tendsto
      (fun p : ℕ ↦
        ((orderedMatchingTuples p k).card : ℝ) * (2 : ℝ) ^ k /
          (p : ℝ) ^ (2 * k))
      atTop (nhds 1) := by
  have hdesc := tendsto_descFactorial_div_pow_one (2 * k)
  apply hdesc.congr'
  filter_upwards [] with p
  have hcountR :
      ((orderedMatchingTuples p k).card : ℝ) * (2 : ℝ) ^ k =
        (p.descFactorial (2 * k) : ℝ) := by
    exact_mod_cast card_orderedMatchingTuples_mul_pow_two p k
  rw [hcountR]

/-- Rescaling the one-edge beta tail by `p²/2` instead of `p.choose 2`
does not change its limiting intensity. -/
theorem tendsto_half_sq_mul_betaCorrelationTailProbability
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto
      (fun p : ℕ ↦
        ((p : ℝ) ^ 2 / 2) *
          betaCorrelationTailProbability (mseq p) p x)
      atTop (nhds (classicalCoherenceIntensity x)) := by
  have hone : Tendsto
      (fun p : ℕ ↦ ((p.choose 2 : ℕ) : ℝ) *
        betaCorrelationTailProbability (mseq p) p x)
      atTop (nhds (classicalCoherenceIntensity x)) :=
    allGapBetaTailIntensity mseq hadm x
  have hedge := tendsto_two_mul_choose_two_div_sq_one
  have hquot := hone.div hedge (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' : Tendsto
      ((fun p : ℕ ↦ ((p.choose 2 : ℕ) : ℝ) *
          betaCorrelationTailProbability (mseq p) p x) /
        (fun p : ℕ ↦
          2 * ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2))
      atTop (nhds (classicalCoherenceIntensity x)) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hchooseN : 0 < p.choose 2 := Nat.choose_pos hp
  have hchoose : (((p.choose 2 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hchooseN.ne'
  change
    (((p.choose 2 : ℕ) : ℝ) *
        betaCorrelationTailProbability (mseq p) p x) /
        (2 * ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2) =
      (p : ℝ) ^ 2 / 2 *
        betaCorrelationTailProbability (mseq p) p x
  field_simp [hp0, hchoose]

/-- For every fixed `k`, the total probability weight of all ordered
`k`-edge matchings has the expected Poisson factorial-moment limit. -/
theorem tendsto_orderedMatching_totalProbabilityWeight
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto
      (fun p : ℕ ↦
        ((orderedMatchingTuples p k).card : ℝ) *
          betaCorrelationTailProbability (mseq p) p x ^ k)
      atTop (nhds (classicalCoherenceIntensity x ^ k)) := by
  have hcount := tendsto_orderedMatching_count_normalized k
  have htail := tendsto_half_sq_mul_betaCorrelationTailProbability hadm x
  have hprod : Tendsto
      (fun p : ℕ ↦
        (((orderedMatchingTuples p k).card : ℝ) * (2 : ℝ) ^ k /
            (p : ℝ) ^ (2 * k)) *
          ((((p : ℝ) ^ 2 / 2) *
            betaCorrelationTailProbability (mseq p) p x) ^ k))
      atTop (nhds (classicalCoherenceIntensity x ^ k)) := by
    simpa using hcount.mul (htail.pow k)
  have hfinal : Tendsto
      (fun p : ℕ ↦
        ((orderedMatchingTuples p k).card : ℝ) *
          betaCorrelationTailProbability (mseq p) p x ^ k)
      atTop (nhds (classicalCoherenceIntensity x ^ k)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 1] with p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    rw [mul_pow, div_pow, pow_mul]
    field_simp [hp0]
  simpa using hfinal

end

end LogdetLean.Coherence
