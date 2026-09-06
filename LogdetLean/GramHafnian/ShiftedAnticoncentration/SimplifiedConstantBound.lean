import LogdetLean.GramHafnian.ShiftedAnticoncentration.Definitions
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Exp
/-!
# Simplified finite anticoncentration constant

This file proves the elementary estimate used to pass from the exact finite
coefficient to the compact bound displayed in the paper.  The only inputs
are a finite central-binomial estimate and `1 + x ≤ exp x`; no probabilistic
or analytic bridge theorem is used here.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-! ## A finite central-binomial bound -/

/-- A convenient Wallis-strength finite estimate.  It is slightly stronger
than the `1 / sqrt n` estimate needed below:

`(3n+1) * binom(2n,n)^2 ≤ 16^n`.

The proof is the exact central-binomial recurrence together with the
one-line polynomial inequality at the induction step. -/
theorem centralBinom_sq_mul_three_mul_add_one_le_sixteen_pow (n : ℕ) :
    (((Nat.centralBinom n : ℕ) : ℝ) ^ 2) * (3 * (n : ℝ) + 1) ≤
      (16 : ℝ) ^ n := by
  induction n with
  | zero => norm_num [Nat.centralBinom]
  | succ n ih =>
      have hrec :
          ((n : ℝ) + 1) * (((Nat.centralBinom (n + 1) : ℕ) : ℝ)) =
            2 * (2 * (n : ℝ) + 1) *
              (((Nat.centralBinom n : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ n
      have halg :
          (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 4) ≤
            4 * ((n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1) := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      have hn1sq : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
      rw [← mul_le_mul_iff_of_pos_left hn1sq]
      calc
        ((n : ℝ) + 1) ^ 2 *
              ((((Nat.centralBinom (n + 1) : ℕ) : ℝ) ^ 2) *
                (3 * ((n + 1 : ℕ) : ℝ) + 1)) =
            ((((n : ℝ) + 1) *
                (((Nat.centralBinom (n + 1) : ℕ) : ℝ))) ^ 2) *
              (3 * (n : ℝ) + 4) := by
                push_cast
                ring
        _ = (2 * (2 * (n : ℝ) + 1) *
                (((Nat.centralBinom n : ℕ) : ℝ))) ^ 2 *
              (3 * (n : ℝ) + 4) := by rw [hrec]
        _ = 4 * (((Nat.centralBinom n : ℕ) : ℝ) ^ 2) *
              ((2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 4)) := by ring
        _ ≤ 4 * (((Nat.centralBinom n : ℕ) : ℝ) ^ 2) *
              (4 * ((n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 1)) := by
                exact mul_le_mul_of_nonneg_left halg (by positivity)
        _ = 16 * ((n : ℝ) + 1) ^ 2 *
              ((((Nat.centralBinom n : ℕ) : ℝ) ^ 2) *
                (3 * (n : ℝ) + 1)) := by ring
        _ ≤ 16 * ((n : ℝ) + 1) ^ 2 * (16 : ℝ) ^ n := by
                exact mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((n : ℝ) + 1) ^ 2 * (16 : ℝ) ^ (n + 1) := by
                rw [pow_succ]
                ring

/-- The sharp-enough finite central-binomial estimate in the form used by
the paper's prefactor: `sqrt(n) * binom(2n,n) ≤ 4^n`. -/
theorem sqrt_mul_centralBinom_le_four_pow (n : ℕ) :
    Real.sqrt (n : ℝ) * (((Nat.centralBinom n : ℕ) : ℝ)) ≤
      (4 : ℝ) ^ n := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  calc
    (Real.sqrt (n : ℝ) * (((Nat.centralBinom n : ℕ) : ℝ))) ^ 2 =
        (((Nat.centralBinom n : ℕ) : ℝ) ^ 2) * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      ring
    _ ≤ (((Nat.centralBinom n : ℕ) : ℝ) ^ 2) *
        (3 * (n : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left (by
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) (sq_nonneg _)
    _ ≤ (16 : ℝ) ^ n :=
      centralBinom_sq_mul_three_mul_add_one_le_sixteen_pow n
    _ = ((4 : ℝ) ^ n) ^ 2 := by
      calc
        (16 : ℝ) ^ n = ((4 : ℝ) ^ 2) ^ n := by norm_num
        _ = (4 : ℝ) ^ (2 * n) := by rw [pow_mul]
        _ = (4 : ℝ) ^ (n * 2) := by congr 1 <;> omega
        _ = ((4 : ℝ) ^ n) ^ 2 := by rw [pow_mul]

/-- The exact central-binomial factor in the finite coefficient is bounded
by `2 sqrt n`. -/
theorem centralBinomial_prefactor_le_two_sqrt (n : ℕ) :
    (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n ≤
      2 * Real.sqrt (n : ℝ) := by
  have hroot := sqrt_mul_centralBinom_le_four_pow n
  change (2 * (n : ℝ)) * (((Nat.centralBinom n : ℕ) : ℝ)) /
      (4 : ℝ) ^ n ≤ 2 * Real.sqrt (n : ℝ)
  have hpow : 0 < (4 : ℝ) ^ n := by positivity
  rw [div_le_iff₀ hpow]
  calc
    (2 * (n : ℝ)) * (((Nat.centralBinom n : ℕ) : ℝ)) =
        2 * (Real.sqrt (n : ℝ)) ^ 2 *
          (Nat.centralBinom n : ℝ) := by
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = 2 * Real.sqrt (n : ℝ) *
          (Real.sqrt (n : ℝ) * (Nat.centralBinom n : ℝ)) := by ring
    _ ≤ 2 * Real.sqrt (n : ℝ) * (4 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = 2 * Real.sqrt (n : ℝ) * (4 : ℝ) ^ n := rfl

/-! ## Exponential bounds for the rational correction -/

/-- Every recurrence denominator is positive in the paper's regime. -/
theorem shiftedDenominator_pos
    {k n r : ℕ} (hk : 4 * n ≤ k) (hr : r ≤ n) :
    0 < (k : ℝ) - 4 * (r : ℝ) + 1 := by
  have hkR : (4 : ℝ) * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hrR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
  linarith

/-- Exact `1+x` form of one shifted-ratio factor. -/
theorem shiftedRatio_eq_one_add
    {k r : ℕ} (hden : 0 < (k : ℝ) - 4 * (r : ℝ) + 1) :
    ((k : ℝ) + 2 * (r : ℝ) - 2) /
        ((k : ℝ) - 4 * (r : ℝ) + 1) =
      1 + (6 * (r : ℝ) - 3) /
        ((k : ℝ) - 4 * (r : ℝ) + 1) := by
  have hsplit :
      (k : ℝ) + 2 * (r : ℝ) - 2 =
        ((k : ℝ) - 4 * (r : ℝ) + 1) + (6 * (r : ℝ) - 3) := by
    ring
  rw [hsplit, add_div, div_self hden.ne']

/-- Exact sum of the numerator losses from levels `2,...,n`. -/
theorem sum_Icc_two_six_mul_sub_three (n : ℕ) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.Icc 2 n, (6 * (r : ℝ) - 3)) =
      3 * (n : ℝ) ^ 2 - 3 := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    (∑ r ∈ Finset.Icc 2 j, (6 * (r : ℝ) - 3)) =
      3 * (j : ℝ) ^ 2 - 3
  apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
  · norm_num [P]
  · intro j hj ih
    change (∑ r ∈ Finset.Icc 2 j, (6 * (r : ℝ) - 3)) =
      3 * (j : ℝ) ^ 2 - 3 at ih
    change (∑ r ∈ Finset.Icc 2 (j + 1), (6 * (r : ℝ) - 3)) =
      3 * ((j + 1 : ℕ) : ℝ) ^ 2 - 3
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- The complete product over recurrence levels is bounded by the second
exponential term displayed in the paper. -/
theorem shiftedRatioProduct_le_exp
    {k n : ℕ} (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    (∏ r ∈ Finset.Icc 2 n,
        (((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
      Real.exp
        ((3 * (n : ℝ) ^ 2 - 3) /
          ((k : ℝ) - 4 * (n : ℝ) + 1)) := by
  let f : ℕ → ℝ := fun r ↦
    (6 * (r : ℝ) - 3) / ((k : ℝ) - 4 * (r : ℝ) + 1)
  have hdmin : 0 < (k : ℝ) - 4 * (n : ℝ) + 1 :=
    shiftedDenominator_pos hk le_rfl
  have hf_nonneg : ∀ r ∈ Finset.Icc 2 n, 0 ≤ f r := by
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hden := shiftedDenominator_pos hk hrn
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    unfold f
    exact div_nonneg (by linarith) hden.le
  have hrewrite :
      (∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) =
        ∏ r ∈ Finset.Icc 2 n, (1 + f r) := by
    apply Finset.prod_congr rfl
    intro r hr
    have hrn := (Finset.mem_Icc.mp hr).2
    exact shiftedRatio_eq_one_add (shiftedDenominator_pos hk hrn)
  rw [hrewrite]
  calc
    (∏ r ∈ Finset.Icc 2 n, (1 + f r)) ≤
        Real.exp (∑ r ∈ Finset.Icc 2 n, f r) := by
      calc
        (∏ r ∈ Finset.Icc 2 n, (1 + f r)) ≤
            ∏ r ∈ Finset.Icc 2 n, Real.exp (f r) := by
          apply Finset.prod_le_prod
          · intro r hr
            exact add_nonneg zero_le_one (hf_nonneg r hr)
          · intro r hr
            exact (add_comm 1 (f r)).le.trans (Real.add_one_le_exp (f r))
        _ = Real.exp (∑ r ∈ Finset.Icc 2 n, f r) := by
          rw [Real.exp_sum]
    _ ≤ Real.exp
        ((3 * (n : ℝ) ^ 2 - 3) /
          ((k : ℝ) - 4 * (n : ℝ) + 1)) := by
      apply Real.exp_le_exp.mpr
      calc
        (∑ r ∈ Finset.Icc 2 n, f r) ≤
            ∑ r ∈ Finset.Icc 2 n,
              (6 * (r : ℝ) - 3) /
                ((k : ℝ) - 4 * (n : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro r hr
          have hr2 := (Finset.mem_Icc.mp hr).1
          have hrn := (Finset.mem_Icc.mp hr).2
          have hnum : 0 ≤ 6 * (r : ℝ) - 3 := by
            have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
            linarith
          have horder :
              (k : ℝ) - 4 * (n : ℝ) + 1 ≤
                (k : ℝ) - 4 * (r : ℝ) + 1 := by
            have hrnR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
            linarith
          exact div_le_div_of_nonneg_left hnum hdmin horder
        _ = (∑ r ∈ Finset.Icc 2 n, (6 * (r : ℝ) - 3)) /
              ((k : ℝ) - 4 * (n : ℝ) + 1) := by
          rw [Finset.sum_div]
        _ = (3 * (n : ℝ) ^ 2 - 3) /
              ((k : ℝ) - 4 * (n : ℝ) + 1) := by
          rw [sum_Icc_two_six_mul_sub_three n hn]

/-- The head correction is bounded by its exponential envelope. -/
theorem shiftedHeadRatio_le_exp
    {k n : ℕ} (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    (k : ℝ) / ((k : ℝ) - 1) ≤
      Real.exp (1 / ((k : ℝ) - 1)) := by
  have hk4 : 4 ≤ k := by omega
  have hkR : (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast (show 1 < k by omega)
  have hden : 0 < (k : ℝ) - 1 := by linarith
  calc
    (k : ℝ) / ((k : ℝ) - 1) =
        1 + 1 / ((k : ℝ) - 1) := by
      field_simp [hden.ne']
      ring
    _ ≤ Real.exp (1 / ((k : ℝ) - 1)) := by
      simpa [add_comm] using
        Real.add_one_le_exp (1 / ((k : ℝ) - 1))

/-! ## Displayed simplified coefficient -/

/-- The exact finite shifted-anticoncentration coefficient is bounded by the
simplified expression displayed in the manuscript. -/
theorem shiftedAnticoncentrationConstant_le_simplified
    {k n : ℕ} (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    shiftedAnticoncentrationConstant k n ≤
      2 * Real.sqrt (n : ℝ) *
        Real.exp
          (1 / ((k : ℝ) - 1) +
            (3 * (n : ℝ) ^ 2 - 3) /
              ((k : ℝ) - 4 * (n : ℝ) + 1)) := by
  let A : ℝ :=
    (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n
  let H : ℝ := (k : ℝ) / ((k : ℝ) - 1)
  let P : ℝ :=
    ∏ r ∈ Finset.Icc 2 n,
      (((k : ℝ) + 2 * (r : ℝ) - 2) /
        ((k : ℝ) - 4 * (r : ℝ) + 1))
  let H' : ℝ := Real.exp (1 / ((k : ℝ) - 1))
  let P' : ℝ := Real.exp
    ((3 * (n : ℝ) ^ 2 - 3) /
      ((k : ℝ) - 4 * (n : ℝ) + 1))
  have hA : A ≤ 2 * Real.sqrt (n : ℝ) := by
    exact centralBinomial_prefactor_le_two_sqrt n
  have hH : H ≤ H' := by
    exact shiftedHeadRatio_le_exp hn hk
  have hP : P ≤ P' := by
    exact shiftedRatioProduct_le_exp hn hk
  have hH0 : 0 ≤ H := by
    have hk4 : 4 ≤ k := by omega
    have hkR : (1 : ℝ) < (k : ℝ) := by
      exact_mod_cast (show 1 < k by omega)
    have hden : 0 < (k : ℝ) - 1 := by
      linarith
    exact div_nonneg (Nat.cast_nonneg k) hden.le
  have hP0 : 0 ≤ P := by
    unfold P
    apply Finset.prod_nonneg
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hden := shiftedDenominator_pos hk hrn
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    exact div_nonneg (by linarith) hden.le
  have hAmax0 : 0 ≤ 2 * Real.sqrt (n : ℝ) := by positivity
  have hH'0 : 0 ≤ H' := Real.exp_nonneg _
  have hAH : A * H ≤ (2 * Real.sqrt (n : ℝ)) * H' :=
    mul_le_mul hA hH hH0 hAmax0
  have hAHP : A * H * P ≤
      (2 * Real.sqrt (n : ℝ)) * H' * P' :=
    mul_le_mul hAH hP hP0 (mul_nonneg hAmax0 hH'0)
  change A * H * P ≤ _
  calc
    A * H * P ≤ (2 * Real.sqrt (n : ℝ)) * H' * P' := hAHP
    _ = 2 * Real.sqrt (n : ℝ) *
        Real.exp
          (1 / ((k : ℝ) - 1) +
            (3 * (n : ℝ) ^ 2 - 3) /
              ((k : ℝ) - 4 * (n : ℝ) + 1)) := by
      unfold H' P'
      rw [mul_assoc, ← Real.exp_add]

end

end LogdetLean.GramHafnian
