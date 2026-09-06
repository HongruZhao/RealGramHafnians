import LogdetLean.GramHafnian.AsymptoticWeakAC
import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-!
# The logarithmic weak-anticoncentration boundary

The quadratic scale `k ≍ n²` controls convergence to the independent-Gaussian
baseline.  Weak anticoncentration asks only for an inverse-polynomial lower
bound and therefore persists farther down, to the logarithmic scale
`k ≍ n² / log n`.

This file proves the rigorous sufficient half directly from the exact finite
exponential bound.  Its assumption is written in the equivalent and Lean-
friendly form `2 n²/k ≤ d log n` for one fixed natural exponent `d`.
-/

open scoped Topology
open Filter Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- A logarithmic upper bound on the correction exponent gives an explicit
inverse-polynomial lower bound for the normalized second moment. -/
theorem one_div_two_mul_pow_le_gramSecondMomentRatio_of_log_scale
    (k n d : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hscale : 2 * (n : ℝ) ^ 2 / (k : ℝ) ≤ (d : ℝ) * Real.log n) :
    1 / (2 * (n : ℝ) ^ (d + 1)) ≤ gramSecondMomentRatio k n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hFexp := finiteCorrection_le_exp k n hk
  have hexp :
      Real.exp (2 * (n : ℝ) ^ 2 / (k : ℝ)) ≤ (n : ℝ) ^ d := by
    calc
      Real.exp (2 * (n : ℝ) ^ 2 / (k : ℝ)) ≤
          Real.exp ((d : ℝ) * Real.log n) := Real.exp_le_exp.mpr hscale
      _ = (n : ℝ) ^ d := by
        calc
          Real.exp ((d : ℝ) * Real.log n) =
              Real.exp (Real.log n) ^ d := by
            simpa [mul_comm] using Real.exp_nat_mul (Real.log n) d
          _ = (n : ℝ) ^ d := by rw [Real.exp_log hnR]
  have hF : finiteCorrection k n ≤ (n : ℝ) ^ d := hFexp.trans hexp
  have hbase := one_div_two_mul_le_centralBaseline n hn
  have hdiv :
      (1 / (2 * (n : ℝ))) / ((n : ℝ) ^ d) ≤
        centralBaseline n / finiteCorrection k n :=
    div_le_div₀ (centralBaseline_nonneg n) hbase
      (finiteCorrection_pos k n) hF
  rw [gramSecondMomentRatio]
  calc
    1 / (2 * (n : ℝ) ^ (d + 1)) =
        (1 / (2 * (n : ℝ))) / ((n : ℝ) ^ d) := by
      rw [pow_succ]
      field_simp [ne_of_gt hnR]
    _ ≤ centralBaseline n / finiteCorrection k n := hdiv

/-- Sequence form: the scale `2 n²/k_n ≤ d log n` implies weak
anticoncentration with the explicit polynomial exponent `d+1`. -/
theorem hasWeakAntiConcentration_of_eventually_log_scale
    (kseq : ℕ → ℕ) (d : ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ 2 / (kseq n : ℝ) ≤
        (d : ℝ) * Real.log n) :
    HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio (kseq n) n) := by
  refine ⟨1 / 2, by norm_num, d + 1, ?_⟩
  filter_upwards [hk, hscale, eventually_ge_atTop 1]
    with n hkn hs hn
  have hnpos : 0 < n := by omega
  have h := one_div_two_mul_pow_le_gramSecondMomentRatio_of_log_scale
    (kseq n) n d hnpos hkn hs
  simpa [div_eq_mul_inv, mul_assoc, mul_comm] using h

/-- At the exact rank-one endpoint `k=1`, the normalized moment is
exponentially small and therefore fails every inverse-polynomial weak-
anticoncentration bound. -/
theorem not_hasWeakAntiConcentration_rank_one :
    ¬ HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio 1 n) := by
  rintro ⟨C, hC, d, hweak⟩
  have hpoly : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ d / (4 : ℝ) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ d / (4 : ℝ) ^ n < C :=
    hpoly.eventually (Iio_mem_nhds hC)
  obtain ⟨n, hnweak, hnsmall, hn⟩ :=
    (hweak.and (hsmall.and (eventually_ge_atTop 1))).exists
  change C / (n : ℝ) ^ d ≤ gramSecondMomentRatio 1 n at hnweak
  rw [gramSecondMomentRatio_one] at hnweak
  have hnR : (0 : ℝ) < n := by positivity
  have hpow : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  rw [div_le_iff₀ hpow] at hnweak
  have hrewrite :
      1 / (4 : ℝ) ^ n * (n : ℝ) ^ d =
        (n : ℝ) ^ d / (4 : ℝ) ^ n := by ring
  rw [hrewrite] at hnweak
  linarith

end

end LogdetLean.GramHafnian
