import LogdetLean.GramHafnian.FiniteSum
import Mathlib.Analysis.Complex.Exponential
/-!
# Deterministic asymptotic bounds for the Gram--hafnian correction

This file isolates the finite algebra needed at the quadratic aspect-ratio
boundary.  It deliberately does not postulate an infinite-series or special-
function limit.  Instead, it bounds every exact finite summand and then uses
the already formalized exponential series.
-/

open scoped BigOperators Topology
open Finset Filter Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- A convenient exponential majorant for one finite correction summand. -/
noncomputable def exponentialEnvelopeTerm (k n j : ℕ) : ℝ :=
  (2 * (n : ℝ) ^ 2 / (k : ℝ)) ^ j / (j.factorial : ℝ)

/-- The Pochhammer quotient is bounded by a factorial envelope.  This is the
key estimate that keeps the critical scale at `k` of order `n²`. -/
theorem pochhammerRatio_le_factorial_envelope
    (k j : ℕ) (hk : 0 < k) :
    pochhammerRatio k j ≤
      (2 : ℝ) ^ j * (j.factorial : ℝ) / (k : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pochhammerRatio_succ]
      have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
      have hden : 0 < ((k + 2 * j : ℕ) : ℝ) := by positivity
      have hfactor :
          (((2 * j + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) ≤
            2 * ((j + 1 : ℕ) : ℝ) / (k : ℝ) := by
        rw [div_le_div_iff₀ hden hkR]
        push_cast
        nlinarith
      calc
        pochhammerRatio k j *
              (((2 * j + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) ≤
            pochhammerRatio k j *
              (2 * ((j + 1 : ℕ) : ℝ) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hfactor (pochhammerRatio_nonneg k j)
        _ ≤ ((2 : ℝ) ^ j * (j.factorial : ℝ) / (k : ℝ) ^ j) *
              (2 * ((j + 1 : ℕ) : ℝ) / (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_right ih (by positivity)
        _ = (2 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) /
              (k : ℝ) ^ (j + 1) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp
          ring

/-- Each exact correction summand is dominated by the corresponding term of
an exponential series with parameter `2 n² / k`. -/
theorem finiteTerm_le_exponentialEnvelopeTerm
    (k n j : ℕ) (hk : 0 < k) :
    finiteTerm k n j ≤ exponentialEnvelopeTerm k n j := by
  have hchoose :
      ((n.choose j : ℕ) : ℝ) ≤
        (n : ℝ) ^ j / (j.factorial : ℝ) := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) j n)
  have hchoose0 : 0 ≤ ((n.choose j : ℕ) : ℝ) := by positivity
  have hpowdiv0 : 0 ≤ (n : ℝ) ^ j / (j.factorial : ℝ) := by positivity
  have hchooseSq :
      ((n.choose j : ℕ) : ℝ) ^ 2 ≤
        ((n : ℝ) ^ j / (j.factorial : ℝ)) ^ 2 := by
    nlinarith
  have hpoch := pochhammerRatio_le_factorial_envelope k j hk
  have henv0 :
      0 ≤ (2 : ℝ) ^ j * (j.factorial : ℝ) / (k : ℝ) ^ j := by
    positivity
  rw [finiteTerm, exponentialEnvelopeTerm]
  calc
    ((n.choose j : ℕ) : ℝ) ^ 2 * pochhammerRatio k j ≤
        ((n.choose j : ℕ) : ℝ) ^ 2 *
          ((2 : ℝ) ^ j * (j.factorial : ℝ) / (k : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left hpoch (sq_nonneg _)
    _ ≤ ((n : ℝ) ^ j / (j.factorial : ℝ)) ^ 2 *
          ((2 : ℝ) ^ j * (j.factorial : ℝ) / (k : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_right hchooseSq henv0
    _ = (2 * (n : ℝ) ^ 2 / (k : ℝ)) ^ j /
          (j.factorial : ℝ) := by
      have hkR : (k : ℝ) ≠ 0 := by positivity
      have hjR : (j.factorial : ℝ) ≠ 0 := by positivity
      simp_rw [div_pow]
      field_simp
      ring

/-- The complete finite correction is bounded by an exponential. -/
theorem finiteCorrection_le_exp (k n : ℕ) (hk : 0 < k) :
    finiteCorrection k n ≤ Real.exp (2 * (n : ℝ) ^ 2 / (k : ℝ)) := by
  rw [finiteCorrection]
  calc
    (∑ j ∈ range (n + 1), finiteTerm k n j) ≤
        ∑ j ∈ range (n + 1), exponentialEnvelopeTerm k n j := by
      exact Finset.sum_le_sum fun j _ ↦ finiteTerm_le_exponentialEnvelopeTerm k n j hk
    _ ≤ Real.exp (2 * (n : ℝ) ^ 2 / (k : ℝ)) := by
      simpa [exponentialEnvelopeTerm] using
        Real.sum_le_exp_of_nonneg
          (by positivity : 0 ≤ 2 * (n : ℝ) ^ 2 / (k : ℝ)) (n + 1)

/-- A pointwise quadratic lower bound on `k` gives a uniform correction
bound.  No limiting argument is hidden in this theorem. -/
theorem finiteCorrection_le_exp_of_quadratic_lower
    (k n : ℕ) {c : ℝ} (hk : 0 < k) (hc : 0 < c)
    (hscale : c * (n : ℝ) ^ 2 ≤ (k : ℝ)) :
    finiteCorrection k n ≤ Real.exp (2 / c) := by
  refine (finiteCorrection_le_exp k n hk).trans ?_
  apply Real.exp_le_exp.mpr
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [div_le_div_iff₀ hkR hc]
  nlinarith [sq_nonneg (n : ℝ)]

/-- The first nonconstant correction summand is exactly `n²/k`. -/
@[simp] theorem finiteTerm_one (k n : ℕ) :
    finiteTerm k n 1 = (n : ℝ) ^ 2 / (k : ℝ) := by
  simp [finiteTerm, pochhammerRatio, div_eq_mul_inv]

/-- Keeping only the zeroth and first summands gives the matching lower
envelope. -/
theorem one_add_quadratic_div_le_finiteCorrection
    (k n : ℕ) (hn : 0 < n) :
    1 + (n : ℝ) ^ 2 / (k : ℝ) ≤ finiteCorrection k n := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ range (n + 1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    simp only [mem_range]
    rcases hi with rfl | rfl <;> omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j ↦ finiteTerm k n j) hsub
    (fun i _ _ ↦ finiteTerm_nonneg k n i)
  simpa [finiteCorrection] using hsum

/-- At or below a fixed quadratic envelope, the correction stays a definite
distance above one. -/
theorem one_add_inv_le_finiteCorrection_of_quadratic_upper
    (k n : ℕ) {c : ℝ} (hn : 0 < n) (hk : 0 < k) (hc : 0 < c)
    (hscale : (k : ℝ) ≤ c * (n : ℝ) ^ 2) :
    1 + 1 / c ≤ finiteCorrection k n := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratio : 1 / c ≤ (n : ℝ) ^ 2 / (k : ℝ) := by
    rw [div_le_div_iff₀ hc hkR]
    simpa [mul_comm] using hscale
  calc
    1 + 1 / c ≤ 1 + (n : ℝ) ^ 2 / (k : ℝ) := by linarith
    _ ≤ finiteCorrection k n :=
      one_add_quadratic_div_le_finiteCorrection k n hn

/-- In the superquadratic regime `n²/k → 0`, the exact finite correction
converges to one.  This is a complete squeeze proof, not a formal asymptotic
certificate. -/
theorem tendsto_finiteCorrection_one_of_quadratic_ratio_zero
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hratio : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ finiteCorrection (kseq n) n)
      atTop (nhds 1) := by
  have hupperT : Tendsto
      (fun n : ℕ ↦ Real.exp (2 * (n : ℝ) ^ 2 / (kseq n : ℝ)))
      atTop (nhds 1) := by
    have htwo := Real.continuous_exp.continuousAt.tendsto.comp
      (Tendsto.const_mul 2 hratio)
    simpa [Function.comp_def, mul_div_assoc] using htwo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperT
  · exact Filter.Eventually.of_forall fun n ↦
      one_le_finiteCorrection (kseq n) n
  · filter_upwards [hk] with n hn
    exact finiteCorrection_le_exp (kseq n) n hn

/-- Conversely, an eventual positive quadratic upper envelope prevents the
correction from converging to one.  This cleanly locates the boundary without
asserting an unproved critical special-function limit. -/
theorem not_tendsto_finiteCorrection_one_of_eventually_quadratic_upper
    (kseq : ℕ → ℕ) {c : ℝ} (hc : 0 < c)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (kseq n : ℝ) ≤ c * (n : ℝ) ^ 2) :
    ¬ Tendsto (fun n : ℕ ↦ finiteCorrection (kseq n) n)
        atTop (nhds 1) := by
  intro hlim
  have hlower : ∀ᶠ n : ℕ in atTop,
      1 + 1 / c ≤ finiteCorrection (kseq n) n := by
    filter_upwards [hk, hscale, eventually_ge_atTop 1]
      with n hnK hnScale hn
    exact one_add_inv_le_finiteCorrection_of_quadratic_upper
      (kseq n) n (by omega) hnK hc hnScale
  have hbad : 1 + 1 / c ≤ (1 : ℝ) := ge_of_tendsto hlim hlower
  have : 0 < 1 / c := one_div_pos.mpr hc
  linarith

/-- Consequently, in the superquadratic regime the exact second-moment ratio
is asymptotic to its central-binomial baseline. -/
theorem tendsto_gramSecondMomentRatio_div_baseline_one
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hratio : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      gramSecondMomentRatio (kseq n) n / centralBaseline n)
      atTop (nhds 1) := by
  have hcorr :=
    tendsto_finiteCorrection_one_of_quadratic_ratio_zero kseq hk hratio
  have hinv := hcorr.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have heq :
      (fun n : ℕ ↦ (finiteCorrection (kseq n) n)⁻¹) =ᶠ[atTop]
        (fun n : ℕ ↦
          gramSecondMomentRatio (kseq n) n / centralBaseline n) :=
    Filter.Eventually.of_forall fun n ↦ by
      change (finiteCorrection (kseq n) n)⁻¹ =
        (centralBaseline n / finiteCorrection (kseq n) n) /
          centralBaseline n
      field_simp [ne_of_gt (centralBaseline_pos n)]
  simpa using hinv.congr' heq

end

end LogdetLean.GramHafnian
