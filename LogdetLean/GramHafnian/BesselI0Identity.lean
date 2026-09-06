import LogdetLean.GramHafnian.BesselI0Series
import LogdetLean.GramHafnian.BesselI0Coefficient
/-!
# Identification of the Gram--hafnian crossover with `exp(y) I₀(y)`

This module proves the classical identity

`besselMajorant y = exp(y) * I₀(y)`

using only the literal series definitions.  The proof is a genuine absolutely
convergent Cauchy product.  Its finite coefficient calculation is supplied by
`BesselI0Coefficient`, where it is proved by extracting the middle coefficient
of `(1 + 2X + X²)^n = (1 + X)^(2n)`.
-/

open scoped BigOperators
open Finset

namespace LogdetLean.GramHafnian

noncomputable section

/-- The `n`-th Cauchy coefficient of the exponential series and the
zero-padded `I₀` power series is exactly the `n`-th coefficient defining
`besselMajorant`. -/
theorem besselI0_cauchyCoefficient_eq_besselMajorantTerm
    (y : ℝ) (n : ℕ) :
    (∑ k ∈ range (n + 1),
      modifiedBesselI0PowerTerm y k *
        (y ^ (n - k) / ((n - k).factorial : ℝ))) =
      rising (1 / 2 : ℝ) n * (2 * y) ^ n /
        ((n.factorial : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun r ↦
    modifiedBesselI0Term y r *
      (y ^ (n - 2 * r) / ((n - 2 * r).factorial : ℝ))
  have hpad :
      (∑ k ∈ range (n + 1),
        modifiedBesselI0PowerTerm y k *
          (y ^ (n - k) / ((n - k).factorial : ℝ))) =
        ∑ k ∈ range (n + 1), evenPadded f k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [modifiedBesselI0PowerTerm, evenPadded]
    by_cases heven : k % 2 = 0
    · rw [if_pos heven, if_pos heven]
      have hkTwo : k = 2 * (k / 2) := by omega
      dsimp [f]
      rw [hkTwo]
      simp [modifiedBesselI0Term]
    · rw [if_neg heven, if_neg heven]
      simp
  rw [hpad, sum_evenPadded]
  have hf :
      (∑ r ∈ range (n / 2 + 1), f r) =
        y ^ n *
          ∑ r ∈ range (n / 2 + 1),
            1 /
              (((n - 2 * r).factorial : ℝ) * (4 : ℝ) ^ r *
                ((r.factorial : ℝ) ^ 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrle : r ≤ n / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have h2r : 2 * r ≤ n := by omega
    dsimp [f]
    rw [modifiedBesselI0Term]
    have hpow : y ^ (2 * r) * y ^ (n - 2 * r) = y ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have h4 : (4 : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
    have hrfac : (r.factorial : ℝ) ≠ 0 := by positivity
    have hnfac : ((n - 2 * r).factorial : ℝ) ≠ 0 := by positivity
    field_simp [h4, hrfac, hnfac]
    nlinarith
  rw [hf, sum_reciprocalFactorialTerm_eq_rising_half]
  rw [mul_pow]
  ring

/-- **Literal special-function identification.**  With `I₀` defined by its
standard everywhere-convergent real series, the exact Gram--hafnian critical
crossover is `exp(y) I₀(y)`.  The statement holds for every real `y`; no
sign restriction is needed. -/
theorem besselMajorant_eq_exp_mul_modifiedBesselI0Series (y : ℝ) :
    besselMajorant y =
      Real.exp y * modifiedBesselI0Series y := by
  rw [besselMajorant]
  symm
  calc
    Real.exp y * modifiedBesselI0Series y =
        modifiedBesselI0Series y * Real.exp y := mul_comm _ _
    _ = (∑' k : ℕ, modifiedBesselI0PowerTerm y k) *
          ∑' k : ℕ, y ^ k / (k.factorial : ℝ) := by
            rw [tsum_modifiedBesselI0PowerTerm,
              ← exp_eq_tsum_pow_div_factorial]
    _ = ∑' n : ℕ, ∑ k ∈ range (n + 1),
          modifiedBesselI0PowerTerm y k *
            (y ^ (n - k) / ((n - k).factorial : ℝ)) :=
      tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
        (summable_norm_modifiedBesselI0PowerTerm y)
        (summable_norm_expPowerTerm y)
    _ = ∑' n : ℕ,
          rising (1 / 2 : ℝ) n * (2 * y) ^ n /
            ((n.factorial : ℝ) ^ 2) := by
      apply tsum_congr
      exact besselI0_cauchyCoefficient_eq_besselMajorantTerm y

end

end LogdetLean.GramHafnian
