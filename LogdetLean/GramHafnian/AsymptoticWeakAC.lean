import LogdetLean.GramHafnian.AsymptoticBounds
import Mathlib.Data.Nat.Choose.Central
/-!
# Weak anti-concentration at and above the quadratic boundary

The paper's weak anti-concentration requirement only asks for an inverse
polynomial lower bound.  The sharp Wallis constant is therefore unnecessary:
the elementary central-binomial inequality

`4^n ≤ 2 n * choose (2n) n`

already gives a `1/(2n)` lower bound for the baseline.  Combining it with the
finite exponential correction bound proves weak anti-concentration whenever
`k` is bounded below by a positive multiple of `n²`.
-/

open scoped Topology
open Filter Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- A sequence has weak anti-concentration if it is eventually bounded below
by some inverse polynomial. -/
def HasWeakAntiConcentration (q : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
    ∀ᶠ n : ℕ in atTop, C / (n : ℝ) ^ d ≤ q n

/-- The elementary central-binomial estimate is already strong enough for
weak anti-concentration. -/
theorem one_div_two_mul_le_centralBaseline (n : ℕ) (hn : 0 < n) :
    1 / (2 * (n : ℝ)) ≤ centralBaseline n := by
  have hnat := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hreal :
      (4 : ℝ) ^ n ≤
        2 * (n : ℝ) * ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfour : 0 < (4 : ℝ) ^ n := by positivity
  rw [centralBaseline]
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ)) hfour]
  nlinarith

/-- Pointwise weak-AC lower bound at the quadratic scale. -/
theorem exp_neg_two_div_c_div_two_mul_le_gramSecondMomentRatio
    (k n : ℕ) {c : ℝ} (hn : 0 < n) (hk : 0 < k) (hc : 0 < c)
    (hscale : c * (n : ℝ) ^ 2 ≤ (k : ℝ)) :
    Real.exp (-(2 / c)) / (2 * (n : ℝ)) ≤
      gramSecondMomentRatio k n := by
  have hbase := one_div_two_mul_le_centralBaseline n hn
  have hcorr := finiteCorrection_le_exp_of_quadratic_lower k n hk hc hscale
  have hdiv :
      (1 / (2 * (n : ℝ))) / Real.exp (2 / c) ≤
        centralBaseline n / finiteCorrection k n := by
    exact div_le_div₀ (centralBaseline_nonneg n) hbase
      (finiteCorrection_pos k n) hcorr
  rw [gramSecondMomentRatio]
  calc
    Real.exp (-(2 / c)) / (2 * (n : ℝ)) =
        (1 / (2 * (n : ℝ))) / Real.exp (2 / c) := by
      rw [Real.exp_neg]
      field_simp
    _ ≤ centralBaseline n / finiteCorrection k n := hdiv

/-- A positive quadratic lower envelope for the row dimension proves the
paper's weak anti-concentration condition with polynomial exponent one. -/
theorem hasWeakAntiConcentration_of_eventually_quadratic_lower
    (kseq : ℕ → ℕ) {c : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ 2 ≤ (kseq n : ℝ)) :
    HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio (kseq n) n) := by
  refine ⟨Real.exp (-(2 / c)) / 2, by positivity, 1, ?_⟩
  filter_upwards [hscale, eventually_ge_atTop 1] with n hnscale hn
  have hnpos : 0 < n := by omega
  have hkpos : 0 < kseq n := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hkR : 0 < (kseq n : ℝ) :=
      lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos hnR)) hnscale
    exact_mod_cast hkR
  simpa [pow_one, div_div] using
    exp_neg_two_div_c_div_two_mul_le_gramSecondMomentRatio
      (kseq n) n hnpos hkpos hc hnscale

end

end LogdetLean.GramHafnian
