import LogdetLean.GramHafnian.FiniteBesselMajorant
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Central
/-!
# The finite coefficient identity behind the Bessel crossover

This file proves the exact finite convolution identity needed to identify
`besselMajorant y` with the product of the exponential series and the
standard power series for `I₀(y)`.  The combinatorial proof extracts the
middle coefficient in

`(1 + 2 X + X²)^n = (1 + X)^(2n)`.

Everything in this file is finite; no rearrangement of infinite sums is used.
-/

open scoped BigOperators
open Finset Polynomial

namespace LogdetLean.GramHafnian

noncomputable section

/-- Coefficient of `(1 + 2X)^m`. -/
theorem coeff_one_add_twoX_pow (m d : ℕ) :
    ((1 + Polynomial.C (2 : ℝ) * Polynomial.X) ^ m).coeff d =
      ((m.choose d : ℕ) : ℝ) * (2 : ℝ) ^ d := by
  have hp :
      (1 + Polynomial.C (2 : ℝ) * Polynomial.X : ℝ[X]) =
        Polynomial.C 2 * (Polynomial.X + Polynomial.C (1 / 2 : ℝ)) := by
    calc
      1 + Polynomial.C 2 * Polynomial.X =
          Polynomial.C 2 * Polynomial.X + 1 := add_comm _ _
      _ = Polynomial.C 2 * Polynomial.X +
          Polynomial.C 2 * Polynomial.C (1 / 2 : ℝ) := by
            rw [← Polynomial.C_mul]
            norm_num
      _ = Polynomial.C 2 *
          (Polynomial.X + Polynomial.C (1 / 2 : ℝ)) := by rw [mul_add]
  rw [hp, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  by_cases hd : d ≤ m
  · have hm : m = (m - d) + d := by omega
    have htwo :
        (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m - d) = (2 : ℝ) ^ d := by
      have hpowm :
          (2 : ℝ) ^ m = (2 : ℝ) ^ (m - d) * (2 : ℝ) ^ d := by
        conv_lhs => rw [hm, pow_add]
      calc
        (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m - d) =
            ((2 : ℝ) ^ (m - d) * (2 : ℝ) ^ d) *
              (1 / 2 : ℝ) ^ (m - d) := by rw [hpowm]
        _ = (2 : ℝ) ^ d *
            (((2 : ℝ) * (1 / 2 : ℝ)) ^ (m - d)) := by
              rw [mul_pow]
              ring
        _ = (2 : ℝ) ^ d := by norm_num
    calc
      (2 : ℝ) ^ m *
          ((1 / 2 : ℝ) ^ (m - d) * ((m.choose d : ℕ) : ℝ)) =
          ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m - d)) *
            ((m.choose d : ℕ) : ℝ) := by ring
      _ = ((m.choose d : ℕ) : ℝ) * (2 : ℝ) ^ d := by
        rw [htwo]
        ring
  · have hdm : m < d := Nat.lt_of_not_ge hd
    rw [Nat.choose_eq_zero_of_lt hdm]
    simp

/-- The contribution to the middle coefficient from choosing `r` copies of
`X²`, `r` copies of `1`, and `n-2r` copies of `2X`. -/
def besselPairStateTerm (n r : ℕ) : ℝ :=
  if 2 * r ≤ n then
    ((n.choose r : ℕ) : ℝ) *
      (((n - r).choose (n - 2 * r) : ℕ) : ℝ) *
      (2 : ℝ) ^ (n - 2 * r)
  else 0

/-- Extracting the middle coefficient in
`(1+2X+X²)^n=(1+X)^(2n)` gives the central binomial coefficient. -/
theorem sum_besselPairStateTerm_eq_centralBinom (n : ℕ) :
    (∑ r ∈ Finset.range (n + 1), besselPairStateTerm n r) =
      ((Nat.centralBinom n : ℕ) : ℝ) := by
  let P : ℝ[X] := 1 + Polynomial.C (2 : ℝ) * Polynomial.X
  have hpoly :
      ((1 + Polynomial.X) ^ (2 * n) : ℝ[X]) =
        (Polynomial.X ^ 2 + P) ^ n := by
    calc
      ((1 + Polynomial.X) ^ (2 * n) : ℝ[X]) =
          ((1 + Polynomial.X) ^ 2) ^ n := by rw [pow_mul]
      _ = (Polynomial.X ^ 2 + P) ^ n := by
        congr 1
        dsimp [P]
        simp only [Polynomial.C_ofNat]
        ring
  have hcoeff := congrArg (fun q : ℝ[X] ↦ q.coeff n) hpoly
  rw [Polynomial.coeff_one_add_X_pow] at hcoeff
  rw [add_pow] at hcoeff
  rw [Nat.centralBinom_eq_two_mul_choose]
  rw [hcoeff]
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro r hr
  symm
  rw [besselPairStateTerm]
  have hrle : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  change
    ((Polynomial.X ^ 2) ^ r * P ^ (n - r) *
        ((n.choose r : ℕ) : ℝ[X])).coeff n = _
  rw [show ((n.choose r : ℕ) : ℝ[X]) =
      Polynomial.C (((n.choose r : ℕ) : ℝ)) by norm_num]
  rw [Polynomial.coeff_mul_C]
  rw [← pow_mul, Polynomial.coeff_X_pow_mul']
  by_cases h2r : 2 * r ≤ n
  · rw [if_pos h2r, if_pos h2r]
    rw [coeff_one_add_twoX_pow]
    ring
  · rw [if_neg h2r, if_neg h2r]
    simp

/-- Terms with `r > n/2` vanish, so the coefficient sum may be truncated at
its natural endpoint. -/
theorem sum_besselPairStateTerm_range_half (n : ℕ) :
    (∑ r ∈ Finset.range (n / 2 + 1), besselPairStateTerm n r) =
      ((Nat.centralBinom n : ℕ) : ℝ) := by
  rw [← sum_besselPairStateTerm_eq_centralBinom n]
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_succ (Nat.div_le_self n 2))
  · intro r hrBig hrSmall
    simp only [Finset.mem_range, not_lt] at hrSmall
    have hrLower : n / 2 < r := by
      omega
    rw [besselPairStateTerm, if_neg (by omega)]

/-- The three-state coefficient is the corresponding multinomial count. -/
theorem besselPairState_factorial_identity
    (n r : ℕ) (h2r : 2 * r ≤ n) :
    n.choose r * (n - r).choose (n - 2 * r) *
        (r.factorial ^ 2 * (n - 2 * r).factorial) = n.factorial := by
  have hrn : r ≤ n := by omega
  have hinner : n - 2 * r ≤ n - r := by omega
  have hsub : (n - r) - (n - 2 * r) = r := by omega
  have houter := Nat.choose_mul_factorial_mul_factorial hrn
  have hinside := Nat.choose_mul_factorial_mul_factorial hinner
  rw [hsub] at hinside
  calc
    n.choose r * (n - r).choose (n - 2 * r) *
          (r.factorial ^ 2 * (n - 2 * r).factorial) =
        n.choose r * r.factorial *
          ((n - r).choose (n - 2 * r) *
            (n - 2 * r).factorial * r.factorial) := by ring
    _ = n.choose r * r.factorial * (n - r).factorial := by rw [hinside]
    _ = n.factorial := houter

/-- The middle-coefficient summand, divided by the natural scale
`n! 2^n`, is exactly the reciprocal-factorial convolution summand. -/
theorem reciprocalFactorialTerm_eq_besselPairStateTerm_div
    (n r : ℕ) (h2r : 2 * r ≤ n) :
    1 /
        (((n - 2 * r).factorial : ℝ) * (4 : ℝ) ^ r *
          ((r.factorial : ℝ) ^ 2)) =
      besselPairStateTerm n r /
        ((n.factorial : ℝ) * (2 : ℝ) ^ n) := by
  have hfactorial :
      ((n.choose r : ℕ) : ℝ) *
          (((n - r).choose (n - 2 * r) : ℕ) : ℝ) *
          (((r.factorial : ℝ) ^ 2) *
            ((n - 2 * r).factorial : ℝ)) =
        (n.factorial : ℝ) := by
    exact_mod_cast besselPairState_factorial_identity n r h2r
  have hn : n = 2 * r + (n - 2 * r) := by omega
  have hpowTwo : (2 : ℝ) ^ (2 * r) = (4 : ℝ) ^ r := by
    rw [pow_mul]
    norm_num
  have hpower :
      (2 : ℝ) ^ n = (4 : ℝ) ^ r * (2 : ℝ) ^ (n - 2 * r) := by
    conv_lhs => rw [hn, pow_add]
    rw [hpowTwo]
  rw [besselPairStateTerm, if_pos h2r]
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hrfac : (r.factorial : ℝ) ≠ 0 := by positivity
  have hsubfac : ((n - 2 * r).factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ r ≠ 0 := by positivity
  field_simp [hnfac, hrfac, hsubfac, htwo, hfour]
  calc
    (n.factorial : ℝ) * (2 : ℝ) ^ n =
        (((n.choose r : ℕ) : ℝ) *
            (((n - r).choose (n - 2 * r) : ℕ) : ℝ) *
            (((r.factorial : ℝ) ^ 2) *
              ((n - 2 * r).factorial : ℝ))) *
          ((4 : ℝ) ^ r * (2 : ℝ) ^ (n - 2 * r)) := by
            rw [hfactorial, hpower]
    _ = ((n - 2 * r).factorial : ℝ) * (4 : ℝ) ^ r *
          (r.factorial : ℝ) ^ 2 * ((n.choose r : ℕ) : ℝ) *
          (((n - r).choose (n - 2 * r) : ℕ) : ℝ) *
          (2 : ℝ) ^ (n - 2 * r) := by ring

/-- Exact finite coefficient convolution in central-binomial form. -/
theorem sum_reciprocalFactorialTerm_eq_centralBinom (n : ℕ) :
    (∑ r ∈ Finset.range (n / 2 + 1),
        1 /
          (((n - 2 * r).factorial : ℝ) * (4 : ℝ) ^ r *
            ((r.factorial : ℝ) ^ 2))) =
      ((Nat.centralBinom n : ℕ) : ℝ) /
        ((n.factorial : ℝ) * (2 : ℝ) ^ n) := by
  calc
    (∑ r ∈ Finset.range (n / 2 + 1),
        1 /
          (((n - 2 * r).factorial : ℝ) * (4 : ℝ) ^ r *
            ((r.factorial : ℝ) ^ 2))) =
        ∑ r ∈ Finset.range (n / 2 + 1),
          besselPairStateTerm n r /
            ((n.factorial : ℝ) * (2 : ℝ) ^ n) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply reciprocalFactorialTerm_eq_besselPairStateTerm_div
      have hrlt : r < n / 2 + 1 := Finset.mem_range.mp hr
      omega
    _ = (∑ r ∈ Finset.range (n / 2 + 1), besselPairStateTerm n r) /
          ((n.factorial : ℝ) * (2 : ℝ) ^ n) := by
      rw [Finset.sum_div]
    _ = ((Nat.centralBinom n : ℕ) : ℝ) /
          ((n.factorial : ℝ) * (2 : ℝ) ^ n) := by
      rw [sum_besselPairStateTerm_range_half]

/-- Duplication identity for the half-integer rising factorial, proved from
the central-binomial recurrence. -/
theorem rising_half_mul_four_pow_eq_centralBinom_mul_factorial (n : ℕ) :
    rising (1 / 2 : ℝ) n * (4 : ℝ) ^ n =
      ((Nat.centralBinom n : ℕ) : ℝ) * (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hcentralNat := Nat.succ_mul_centralBinom_succ n
      have hcentral :
          ((n + 1 : ℕ) : ℝ) * ((Nat.centralBinom (n + 1) : ℕ) : ℝ) =
            2 * ((2 * n + 1 : ℕ) : ℝ) *
              ((Nat.centralBinom n : ℕ) : ℝ) := by
        exact_mod_cast hcentralNat
      rw [rising_succ, pow_succ, Nat.factorial_succ]
      push_cast
      calc
        rising (1 / 2 : ℝ) n * (1 / 2 + (n : ℝ)) *
              ((4 : ℝ) ^ n * 4) =
            (rising (1 / 2 : ℝ) n * (4 : ℝ) ^ n) *
              (2 * ((2 * n + 1 : ℕ) : ℝ)) := by
          push_cast
          ring
        _ = (((Nat.centralBinom n : ℕ) : ℝ) * (n.factorial : ℝ)) *
              (2 * ((2 * n + 1 : ℕ) : ℝ)) := by rw [ih]
        _ = ((Nat.centralBinom (n + 1) : ℕ) : ℝ) *
              (((n : ℝ) + 1) * (n.factorial : ℝ)) := by
          have hcentral' :
              2 * ((2 * n + 1 : ℕ) : ℝ) *
                  ((Nat.centralBinom n : ℕ) : ℝ) =
                ((Nat.centralBinom (n + 1) : ℕ) : ℝ) *
                  ((n : ℝ) + 1) := by
            rw [← hcentral]
            push_cast
            ring
          rw [show ((Nat.centralBinom n : ℕ) : ℝ) *
                (n.factorial : ℝ) *
                (2 * ((2 * n + 1 : ℕ) : ℝ)) =
              (2 * ((2 * n + 1 : ℕ) : ℝ) *
                ((Nat.centralBinom n : ℕ) : ℝ)) *
                (n.factorial : ℝ) by ring,
            hcentral']
          ring

/-- The exact reciprocal-factorial coefficient required by the exponential
times `I₀` Cauchy product. -/
theorem sum_reciprocalFactorialTerm_eq_rising_half (n : ℕ) :
    (∑ r ∈ Finset.range (n / 2 + 1),
        1 /
          (((n - 2 * r).factorial : ℝ) * (4 : ℝ) ^ r *
            ((r.factorial : ℝ) ^ 2))) =
      rising (1 / 2 : ℝ) n * (2 : ℝ) ^ n /
        ((n.factorial : ℝ) ^ 2) := by
  rw [sum_reciprocalFactorialTerm_eq_centralBinom]
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hpow : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  field_simp [hnfac, htwo]
  have hdup := rising_half_mul_four_pow_eq_centralBinom_mul_factorial n
  rw [hpow] at hdup
  nlinarith

end

end LogdetLean.GramHafnian
