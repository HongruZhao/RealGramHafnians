import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralGramTail
/-!
# A uniform finite-level bound for the literal real Gram error

For `r ≤ n`, both the polynomial prefactor and the exponential factor in
the elementary level envelope increase when `2r-1` is replaced by `2n`.
This yields a direct bound on the full literal bad-event sum by a single
explicit real expression.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The real-valued uniform level envelope obtained by replacing `2r-1`
with `2n`. -/
def pastRealCofactorGramUniformLevelEnvelopeReal
    (n k : ℕ) (delta : ℝ) : ℝ :=
  2 * (2 * (n : ℝ)) ^ 2 *
    Real.exp (-((k : ℝ) * (delta / (2 * (n : ℝ))) ^ 2 / 8))

/-- The full real-valued uniform error, allowing at most `n` recursion
levels. -/
def pastRealCofactorGramUniformErrorReal
    (n k : ℕ) (delta : ℝ) : ℝ :=
  (n : ℝ) * pastRealCofactorGramUniformLevelEnvelopeReal n k delta

private theorem real_gram_envelope_mono_dimension
    {m M k delta : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hk : 0 ≤ k) (hdelta : 0 ≤ delta) :
    2 * m ^ 2 * Real.exp (-(k * (delta / m) ^ 2 / 8)) ≤
      2 * M ^ 2 * Real.exp (-(k * (delta / M) ^ 2 / 8)) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hdiv : delta / M ≤ delta / m :=
    div_le_div_of_nonneg_left hdelta hm hmM
  have hdiv0 : 0 ≤ delta / M := div_nonneg hdelta hM.le
  have hsq : (delta / M) ^ 2 ≤ (delta / m) ^ 2 := by nlinarith
  have hexparg : -(k * (delta / m) ^ 2 / 8) ≤
      -(k * (delta / M) ^ 2 / 8) := by nlinarith
  have hexp := Real.exp_le_exp.mpr hexparg
  have hmsq : m ^ 2 ≤ M ^ 2 := by nlinarith
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmsq (by norm_num)) hexp
    (Real.exp_pos _).le (mul_nonneg (by norm_num) (sq_nonneg _))

/-- Tight uniform level envelope, using the actual largest cofactor
dimension `M = 2n-1`. -/
def pastRealCofactorGramTightLevelEnvelopeReal
    (n k : ℕ) (delta : ℝ) : ℝ :=
  2 * (((2 * n - 1 : ℕ) : ℝ)) ^ 2 *
    Real.exp (-((k : ℝ) *
      (delta / (((2 * n - 1 : ℕ) : ℝ))) ^ 2 / 8))

/-- Tight total finite error.  There are exactly `n-1` non-base levels. -/
def pastRealCofactorGramTightErrorReal
    (n k : ℕ) (delta : ℝ) : ℝ :=
  ((n - 1 : ℕ) : ℝ) *
    pastRealCofactorGramTightLevelEnvelopeReal n k delta

/-- A level `r ≤ n` is controlled by the actual maximal dimension
`2n-1`. -/
theorem pastRealCofactorGramBadEnvelope_le_tightLevel
    {r n k : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) {delta : ℝ}
    (hdelta : 0 ≤ delta) :
    pastRealCofactorGramBadEnvelope r k delta ≤
      ENNReal.ofReal
        (pastRealCofactorGramTightLevelEnvelopeReal n k delta) := by
  have hmNat : 0 < 2 * r - 1 := by omega
  have hm : (0 : ℝ) < ((2 * r - 1 : ℕ) : ℝ) := by exact_mod_cast hmNat
  have hmMNat : 2 * r - 1 ≤ 2 * n - 1 := by omega
  have hmM : ((2 * r - 1 : ℕ) : ℝ) ≤
      ((2 * n - 1 : ℕ) : ℝ) := by exact_mod_cast hmMNat
  apply ENNReal.ofReal_le_ofReal
  exact real_gram_envelope_mono_dimension hm hmM (by positivity) hdelta

/-- Exact finite aggregation of the elementary literal Gram tail:

`2 (n-1) (2n-1)² exp(-k delta² / (8 (2n-1)²))`.

This is the sharp finite interface matching the paper. -/
theorem pastRealCofactorGramBadProbabilitySum_le_tightError
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    pastRealCofactorGramBadProbabilitySum n k delta ≤
      ENNReal.ofReal
        (2 * ((n - 1 : ℕ) : ℝ) *
          (((2 * n - 1 : ℕ) : ℝ)) ^ 2 *
          Real.exp (-((k : ℝ) *
            (delta / (((2 * n - 1 : ℕ) : ℝ))) ^ 2 / 8))) := by
  let U : ENNReal := ENNReal.ofReal
    (pastRealCofactorGramTightLevelEnvelopeReal n k delta)
  have hsum := pastRealCofactorGramBadProbabilitySum_le_sum_envelopes
    (n := n) hk hdelta0 hdelta1
  calc
    pastRealCofactorGramBadProbabilitySum n k delta ≤
        ∑ r ∈ Finset.Icc 2 n,
          pastRealCofactorGramBadEnvelope r k delta := hsum
    _ ≤ (Finset.Icc 2 n).card • U := by
      apply Finset.sum_le_card_nsmul
      intro r hrmem
      exact pastRealCofactorGramBadEnvelope_le_tightLevel
        (le_trans (by norm_num : 1 ≤ 2) (Finset.mem_Icc.mp hrmem).1)
        (Finset.mem_Icc.mp hrmem).2 hdelta0
    _ = (n - 1) • U := by
      congr 1
      rw [Nat.card_Icc]
      omega
    _ = ENNReal.ofReal (pastRealCofactorGramTightErrorReal n k delta) := by
      unfold U pastRealCofactorGramTightErrorReal
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast]
      exact (ENNReal.ofReal_mul
        (by positivity : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ))).symm
    _ = ENNReal.ofReal
        (2 * ((n - 1 : ℕ) : ℝ) *
          (((2 * n - 1 : ℕ) : ℝ)) ^ 2 *
          Real.exp (-((k : ℝ) *
            (delta / (((2 * n - 1 : ℕ) : ℝ))) ^ 2 / 8))) := by
      unfold pastRealCofactorGramTightErrorReal
        pastRealCofactorGramTightLevelEnvelopeReal
      congr 1
      ring

/-- Every literal level envelope below `n` is bounded by the coarser `2n`
uniform level envelope.  This form is convenient only for asymptotics; use
`pastRealCofactorGramBadProbabilitySum_le_tightError` for finite constants. -/
theorem pastRealCofactorGramBadEnvelope_le_uniformLevel
    {r n k : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) {delta : ℝ}
    (hdelta : 0 ≤ delta) :
    pastRealCofactorGramBadEnvelope r k delta ≤
      ENNReal.ofReal
        (pastRealCofactorGramUniformLevelEnvelopeReal n k delta) := by
  have hmNat : 0 < 2 * r - 1 := by omega
  have hm : (0 : ℝ) < ((2 * r - 1 : ℕ) : ℝ) := by exact_mod_cast hmNat
  have hmM : ((2 * r - 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show 2 * r - 1 ≤ 2 * n by omega)
  apply ENNReal.ofReal_le_ofReal
  exact real_gram_envelope_mono_dimension hm hmM (by positivity) hdelta

/-- The literal accumulated bad-event probability has one explicit finite
upper bound.  This is the interface used by the polynomial specialization. -/
theorem pastRealCofactorGramBadProbabilitySum_le_uniformError
    {n k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    pastRealCofactorGramBadProbabilitySum n k delta ≤
      ENNReal.ofReal (pastRealCofactorGramUniformErrorReal n k delta) := by
  let U : ENNReal := ENNReal.ofReal
    (pastRealCofactorGramUniformLevelEnvelopeReal n k delta)
  have hsum := pastRealCofactorGramBadProbabilitySum_le_sum_envelopes
    (n := n) hk hdelta0 hdelta1
  calc
    pastRealCofactorGramBadProbabilitySum n k delta ≤
        ∑ r ∈ Finset.Icc 2 n,
          pastRealCofactorGramBadEnvelope r k delta := hsum
    _ ≤ (Finset.Icc 2 n).card • U := by
      apply Finset.sum_le_card_nsmul
      intro r hr
      exact pastRealCofactorGramBadEnvelope_le_uniformLevel
        (le_trans (by norm_num : 1 ≤ 2) (Finset.mem_Icc.mp hr).1)
        (Finset.mem_Icc.mp hr).2 hdelta0
    _ ≤ n • U := by
      apply nsmul_le_nsmul le_rfl bot_le
      rw [Nat.card_Icc]
      omega
    _ = ENNReal.ofReal
        (pastRealCofactorGramUniformErrorReal n k delta) := by
      unfold U pastRealCofactorGramUniformErrorReal
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast]
      exact (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ))).symm

end

end LogdetLean.GramHafnian
