import LogdetLean.GramHafnian.FiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
/-!
# A simple all-regime exponential bound

This file proves the useful coarse estimate

`finiteCorrection k n ≤ exp (2 n² / k)`

for every positive integral `k`.  It is weaker than the refined Bessel
comparison, but it is completely nonasymptotic and already gives the correct
exponential scale in the sparse-row regime.
-/

open scoped BigOperators
open Finset

namespace LogdetLean.GramHafnian

theorem pochhammerRatio_le_factorial_mul
    (k j : ℕ) (hk : 0 < k) :
    pochhammerRatio k j ≤
      (j.factorial : ℝ) * ((2 : ℝ) / k) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pochhammerRatio_succ]
      have hfactor :
          (((2 * j + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) ≤
            ((j + 1 : ℕ) : ℝ) * ((2 : ℝ) / k) := by
        have hkR : (0 : ℝ) < k := by positivity
        have hden : (0 : ℝ) < ((k + 2 * j : ℕ) : ℝ) := by positivity
        apply (div_le_iff₀ hden).2
        field_simp [ne_of_gt hkR]
        push_cast
        nlinarith [show (0 : ℝ) ≤ j by positivity, show (0 : ℝ) ≤ k by positivity]
      calc
        pochhammerRatio k j *
              (((2 * j + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) ≤
            ((j.factorial : ℝ) * ((2 : ℝ) / k) ^ j) *
              (((j + 1 : ℕ) : ℝ) * ((2 : ℝ) / k)) := by
          exact mul_le_mul ih hfactor (by positivity) (by positivity)
        _ = ((j + 1).factorial : ℝ) * ((2 : ℝ) / k) ^ (j + 1) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
          ring

theorem finiteTerm_le_exponential_series_term
    (k n j : ℕ) (hk : 0 < k) :
    finiteTerm k n j ≤
      ((2 : ℝ) * (n : ℝ) ^ 2 / k) ^ j / (j.factorial : ℝ) := by
  have hchoose :
      ((n.choose j : ℕ) : ℝ) ≤ (n : ℝ) ^ j / (j.factorial : ℝ) :=
    Nat.choose_le_pow_div j n
  have hchoose0 : (0 : ℝ) ≤ ((n.choose j : ℕ) : ℝ) := by positivity
  have hupper0 : (0 : ℝ) ≤ (n : ℝ) ^ j / (j.factorial : ℝ) := by positivity
  have hchooseSq :
      ((n.choose j : ℕ) : ℝ) ^ 2 ≤
        ((n : ℝ) ^ j / (j.factorial : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hchoose) (add_nonneg hupper0 hchoose0)]
  rw [finiteTerm]
  calc
    ((n.choose j : ℕ) : ℝ) ^ 2 * pochhammerRatio k j ≤
        ((n : ℝ) ^ j / (j.factorial : ℝ)) ^ 2 *
          ((j.factorial : ℝ) * ((2 : ℝ) / k) ^ j) := by
      exact mul_le_mul hchooseSq (pochhammerRatio_le_factorial_mul k j hk)
        (pochhammerRatio_nonneg k j) (by positivity)
    _ = ((2 : ℝ) * (n : ℝ) ^ 2 / k) ^ j / (j.factorial : ℝ) := by
      have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
      have hkR : (k : ℝ) ≠ 0 := by positivity
      field_simp [hfac, hkR]
      ring

/-- The finite Taylor polynomial with nonnegative argument lies below the
corresponding real exponential. -/
theorem partial_exp_series_le_exp (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (∑ j ∈ range (N + 1), x ^ j / (j.factorial : ℝ)) ≤ Real.exp x := by
  have hs : Summable (fun j : ℕ ↦ x ^ j / (j.factorial : ℝ)) :=
    Real.summable_pow_div_factorial x
  calc
    (∑ j ∈ range (N + 1), x ^ j / (j.factorial : ℝ))
        ≤ ∑' j : ℕ, x ^ j / (j.factorial : ℝ) :=
          hs.sum_le_tsum (range (N + 1)) (fun j hj ↦ by positivity)
    _ = Real.exp x := by
      rw [Real.exp_eq_exp_ℝ]
      exact (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

/-- Uniform nonasymptotic exponential majorant. -/
theorem finiteCorrection_le_exp_series (k n : ℕ) (hk : 0 < k) :
    finiteCorrection k n ≤ Real.exp ((2 : ℝ) * (n : ℝ) ^ 2 / k) := by
  rw [finiteCorrection]
  calc
    (∑ j ∈ range (n + 1), finiteTerm k n j) ≤
        ∑ j ∈ range (n + 1),
          ((2 : ℝ) * (n : ℝ) ^ 2 / k) ^ j / (j.factorial : ℝ) := by
      exact Finset.sum_le_sum fun j _ ↦ finiteTerm_le_exponential_series_term k n j hk
    _ ≤ Real.exp ((2 : ℝ) * (n : ℝ) ^ 2 / k) :=
      partial_exp_series_le_exp _ (by positivity) n

/-- Corresponding explicit lower bound on the normalized second moment. -/
theorem baseline_mul_exp_neg_le_gramSecondMomentRatio
    (k n : ℕ) (hk : 0 < k) :
    centralBaseline n * Real.exp (-((2 : ℝ) * (n : ℝ) ^ 2 / k)) ≤
      gramSecondMomentRatio k n := by
  rw [gramSecondMomentRatio]
  have hF := finiteCorrection_pos k n
  have hq := centralBaseline_nonneg n
  have hexp : 0 < Real.exp ((2 : ℝ) * (n : ℝ) ^ 2 / k) := Real.exp_pos _
  rw [Real.exp_neg]
  change centralBaseline n / Real.exp ((2 : ℝ) * (n : ℝ) ^ 2 / k) ≤
    centralBaseline n / finiteCorrection k n
  exact div_le_div_of_nonneg_left hq hF (finiteCorrection_le_exp_series k n hk)

end LogdetLean.GramHafnian
