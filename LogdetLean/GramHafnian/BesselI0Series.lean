import LogdetLean.GramHafnian.FiniteBesselMajorant
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
/-!
# A literal modified-Bessel `I₀` series

Mathlib does not currently expose a modified-Bessel special function.  This
module therefore defines the exact real series used in the Gram--hafnian
critical crossover, proves absolute summability, and relates its natural
indexing by `r` to a power series padded by zero in odd degrees.

No special-function identity is assumed here.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- The `r`-th term of the standard modified-Bessel `I₀(y)` series. -/
def modifiedBesselI0Term (y : ℝ) (r : ℕ) : ℝ :=
  y ^ (2 * r) / ((4 : ℝ) ^ r * ((r.factorial : ℝ) ^ 2))

/-- A literal series definition of the modified-Bessel function `I₀` on the
real line. -/
noncomputable def modifiedBesselI0Series (y : ℝ) : ℝ :=
  ∑' r : ℕ, modifiedBesselI0Term y r

/-- The same coefficients, padded by zero in odd power-series degrees. -/
def modifiedBesselI0PowerTerm (y : ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then
    y ^ n /
      ((4 : ℝ) ^ (n / 2) * (((n / 2).factorial : ℝ) ^ 2))
  else 0

/-- Pad a sequence by zero in odd indices.  This small finite-sum adapter is
used when the I0 series participates in a Cauchy product. -/
def evenPadded (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then f (k / 2) else 0

theorem sum_evenPadded_two_mul (f : ℕ → ℝ) (q : ℕ) :
    (∑ k ∈ Finset.range (2 * q + 1), evenPadded f k) =
      ∑ r ∈ Finset.range (q + 1), f r := by
  induction q with
  | zero => simp [evenPadded]
  | succ q ih =>
      calc
        (∑ k ∈ Finset.range (2 * (q + 1) + 1), evenPadded f k) =
            (∑ k ∈ Finset.range (2 * q + 1), evenPadded f k) +
              evenPadded f (2 * q + 1) + evenPadded f (2 * q + 2) := by
                rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by omega,
                  Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (∑ r ∈ Finset.range (q + 1), f r) + f (q + 1) := by
              rw [ih]
              simp [evenPadded]
        _ = ∑ r ∈ Finset.range (q + 1 + 1), f r := by
              exact (Finset.sum_range_succ f (q + 1)).symm

theorem sum_evenPadded (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), evenPadded f k) =
      ∑ r ∈ Finset.range (n / 2 + 1), f r := by
  by_cases hn : n % 2 = 0
  · have heq : n = 2 * (n / 2) := by omega
    conv_lhs => rw [heq]
    exact sum_evenPadded_two_mul f (n / 2)
  · have heq : n = 2 * (n / 2) + 1 := by omega
    conv_lhs => rw [heq]
    rw [show 2 * (n / 2) + 1 + 1 = (2 * (n / 2) + 1) + 1 by rfl,
      Finset.sum_range_succ]
    rw [sum_evenPadded_two_mul f (n / 2)]
    simp [evenPadded]

theorem modifiedBesselI0Term_eq (y : ℝ) (r : ℕ) :
    modifiedBesselI0Term y r =
      ((y ^ 2 / 4) ^ r) / ((r.factorial : ℝ) ^ 2) := by
  rw [modifiedBesselI0Term, pow_mul, div_pow]
  have h4 : (4 : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp [h4, hfac]

theorem modifiedBesselI0Term_nonneg (y : ℝ) (r : ℕ) :
    0 ≤ modifiedBesselI0Term y r := by
  rw [modifiedBesselI0Term]
  exact div_nonneg ((even_two_mul r).pow_nonneg y) (by positivity)

theorem summable_modifiedBesselI0Term (y : ℝ) :
    Summable (modifiedBesselI0Term y) := by
  let x : ℝ := y ^ 2 / 4
  have hx : 0 ≤ x := by dsimp [x]; positivity
  apply Summable.of_nonneg_of_le
      (fun r ↦ modifiedBesselI0Term_nonneg y r)
      (fun r ↦ ?_)
      (Real.summable_pow_div_factorial x)
  rw [modifiedBesselI0Term_eq]
  have hfac : (0 : ℝ) < (r.factorial : ℝ) := by positivity
  have hfacOne : (1 : ℝ) ≤ (r.factorial : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r))
  have hfacSq :
      (r.factorial : ℝ) ≤ (r.factorial : ℝ) ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_left (pow_nonneg hx r) hfac hfacSq

@[simp] theorem modifiedBesselI0PowerTerm_even (y : ℝ) (r : ℕ) :
    modifiedBesselI0PowerTerm y (2 * r) =
      modifiedBesselI0Term y r := by
  simp [modifiedBesselI0PowerTerm, modifiedBesselI0Term]

@[simp] theorem modifiedBesselI0PowerTerm_odd (y : ℝ) (r : ℕ) :
    modifiedBesselI0PowerTerm y (2 * r + 1) = 0 := by
  simp [modifiedBesselI0PowerTerm]

theorem modifiedBesselI0PowerTerm_nonneg (y : ℝ) (n : ℕ) :
    0 ≤ modifiedBesselI0PowerTerm y n := by
  rw [modifiedBesselI0PowerTerm]
  split_ifs with hn
  · exact div_nonneg ((Nat.even_iff.mpr hn).pow_nonneg y) (by positivity)
  · exact le_rfl

theorem summable_modifiedBesselI0PowerTerm (y : ℝ) :
    Summable (modifiedBesselI0PowerTerm y) := by
  apply Summable.even_add_odd
  · simpa only [modifiedBesselI0PowerTerm_even] using
      summable_modifiedBesselI0Term y
  · simpa only [modifiedBesselI0PowerTerm_odd] using
      (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))

theorem summable_norm_modifiedBesselI0PowerTerm (y : ℝ) :
    Summable (fun n ↦ ‖modifiedBesselI0PowerTerm y n‖) := by
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (modifiedBesselI0PowerTerm_nonneg y _)] using
      summable_modifiedBesselI0PowerTerm y

theorem tsum_modifiedBesselI0PowerTerm (y : ℝ) :
    (∑' n : ℕ, modifiedBesselI0PowerTerm y n) =
      modifiedBesselI0Series y := by
  have h := tsum_even_add_odd
    (show Summable (fun r ↦ modifiedBesselI0PowerTerm y (2 * r)) by
      simpa only [modifiedBesselI0PowerTerm_even] using
        summable_modifiedBesselI0Term y)
    (show Summable (fun r ↦ modifiedBesselI0PowerTerm y (2 * r + 1)) by
      simpa only [modifiedBesselI0PowerTerm_odd] using
        (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ))))
  simpa only [modifiedBesselI0PowerTerm_even,
    modifiedBesselI0PowerTerm_odd, tsum_zero, add_zero,
    modifiedBesselI0Series] using h.symm

theorem exp_eq_tsum_pow_div_factorial (y : ℝ) :
    Real.exp y = ∑' n : ℕ, y ^ n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

theorem summable_norm_expPowerTerm (y : ℝ) :
    Summable (fun n : ℕ ↦ ‖y ^ n / (n.factorial : ℝ)‖) :=
  NormedSpace.norm_expSeries_div_summable y

end

end LogdetLean.GramHafnian
