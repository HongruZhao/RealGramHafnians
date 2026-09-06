import LogdetLean.GramHafnian.FiniteHypergeometric
import LogdetLean.GramHafnian.FiniteExponentialBound
/-!
# The confluent-hypergeometric (Bessel) majorant

The refined all-regime comparison uses the entire series

`sum_j (1/2)_j (2y)^j / (j!)²`.

Classically this is `₁F₁(1/2;1;2y) = exp(y) I₀(y)`.  The present file proves
the model-specific finite-sum inequality directly from the series definition;
the special-function naming identity is not needed by any downstream theorem.
-/

open scoped BigOperators
open Finset

namespace LogdetLean.GramHafnian

/-- Entire-series form of the Bessel crossover function. -/
noncomputable def besselMajorant (y : ℝ) : ℝ :=
  ∑' j : ℕ,
    rising (1 / 2 : ℝ) j * (2 * y) ^ j / ((j.factorial : ℝ) ^ 2)

theorem rising_half_nonneg (j : ℕ) : 0 ≤ rising (1 / 2 : ℝ) j :=
  (rising_pos (by norm_num) j).le

theorem rising_half_le_factorial (j : ℕ) :
    rising (1 / 2 : ℝ) j ≤ (j.factorial : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [rising_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have hfactor : (1 / 2 : ℝ) + j ≤ j + 1 := by linarith
      calc
        rising (1 / 2 : ℝ) j * ((1 / 2 : ℝ) + j) ≤
            (j.factorial : ℝ) * ((j : ℝ) + 1) := by
          exact mul_le_mul ih hfactor (by positivity) (by positivity)
        _ = ((j : ℝ) + 1) * (j.factorial : ℝ) := by ring

theorem pochhammerRatio_le_half_rising_mul
    (k j : ℕ) (hk : 0 < k) :
    pochhammerRatio k j ≤
      rising (1 / 2 : ℝ) j * ((2 : ℝ) / k) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pochhammerRatio_succ, rising_succ, pow_succ]
      have hfactor :
          (((2 * j + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) ≤
            ((1 / 2 : ℝ) + j) * ((2 : ℝ) / k) := by
        have hkR : (0 : ℝ) < k := by positivity
        have hden : (0 : ℝ) < ((k + 2 * j : ℕ) : ℝ) := by positivity
        apply (div_le_iff₀ hden).2
        field_simp [ne_of_gt hkR]
        push_cast
        nlinarith [show (0 : ℝ) ≤ j by positivity, show (0 : ℝ) ≤ k by positivity]
      calc
        pochhammerRatio k j *
              (((2 * j + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) ≤
            (rising (1 / 2 : ℝ) j * ((2 : ℝ) / k) ^ j) *
              (((1 / 2 : ℝ) + j) * ((2 : ℝ) / k)) := by
          exact mul_le_mul ih hfactor (by positivity)
            (mul_nonneg (rising_half_nonneg j) (by positivity))
        _ = rising (1 / 2 : ℝ) j * ((1 / 2 : ℝ) + j) *
              (((2 : ℝ) / k) ^ j * ((2 : ℝ) / k)) := by ring

theorem finiteTerm_le_bessel_series_term
    (k n j : ℕ) (hk : 0 < k) :
    finiteTerm k n j ≤
      rising (1 / 2 : ℝ) j *
          ((2 : ℝ) * (n : ℝ) ^ 2 / k) ^ j /
        ((j.factorial : ℝ) ^ 2) := by
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
          (rising (1 / 2 : ℝ) j * ((2 : ℝ) / k) ^ j) := by
      exact mul_le_mul hchooseSq (pochhammerRatio_le_half_rising_mul k j hk)
        (pochhammerRatio_nonneg k j) (by positivity)
    _ = rising (1 / 2 : ℝ) j *
          ((2 : ℝ) * (n : ℝ) ^ 2 / k) ^ j /
        ((j.factorial : ℝ) ^ 2) := by
      have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
      have hkR : (k : ℝ) ≠ 0 := by positivity
      field_simp [hfac, hkR]
      ring

theorem besselMajorant_summable (y : ℝ) (hy : 0 ≤ y) :
    Summable (fun j : ℕ ↦
      rising (1 / 2 : ℝ) j * (2 * y) ^ j / ((j.factorial : ℝ) ^ 2)) := by
  apply Summable.of_nonneg_of_le
      (fun j ↦ div_nonneg
        (mul_nonneg (rising_half_nonneg j) (pow_nonneg (by positivity) j))
        (sq_nonneg _))
      (fun j ↦ ?_)
      (Real.summable_pow_div_factorial (2 * y))
  have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hpow : 0 ≤ (2 * y) ^ j := by positivity
  calc
    rising (1 / 2 : ℝ) j * (2 * y) ^ j / ((j.factorial : ℝ) ^ 2)
        ≤ (j.factorial : ℝ) * (2 * y) ^ j / ((j.factorial : ℝ) ^ 2) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (rising_half_le_factorial j) hpow)
            (by positivity)
    _ = (2 * y) ^ j / (j.factorial : ℝ) := by field_simp [hfac]

/-- Exact finite-sum upper comparison with the Bessel crossover series. -/
theorem finiteCorrection_le_besselMajorant
    (k n : ℕ) (hk : 0 < k) :
    finiteCorrection k n ≤ besselMajorant ((n : ℝ) ^ 2 / k) := by
  let y : ℝ := (n : ℝ) ^ 2 / k
  have hy : 0 ≤ y := by dsimp [y]; positivity
  rw [finiteCorrection, besselMajorant]
  calc
    (∑ j ∈ range (n + 1), finiteTerm k n j) ≤
        ∑ j ∈ range (n + 1),
          rising (1 / 2 : ℝ) j * (2 * y) ^ j /
            ((j.factorial : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [y, mul_div_assoc, mul_assoc] using
        finiteTerm_le_bessel_series_term k n j hk
    _ ≤ ∑' j : ℕ,
          rising (1 / 2 : ℝ) j * (2 * y) ^ j /
            ((j.factorial : ℝ) ^ 2) :=
      (besselMajorant_summable y hy).sum_le_tsum (range (n + 1))
        (fun j hj ↦ div_nonneg
          (mul_nonneg (rising_half_nonneg j) (pow_nonneg (by positivity) j))
          (sq_nonneg _))

/-- Bessel-series lower bound on the normalized second moment. -/
theorem baseline_div_besselMajorant_le_gramSecondMomentRatio
    (k n : ℕ) (hk : 0 < k) :
    centralBaseline n / besselMajorant ((n : ℝ) ^ 2 / k) ≤
      gramSecondMomentRatio k n := by
  rw [gramSecondMomentRatio]
  have hy : 0 ≤ (n : ℝ) ^ 2 / k := by positivity
  have hBpos : 0 < besselMajorant ((n : ℝ) ^ 2 / k) := by
    rw [besselMajorant]
    have hs := besselMajorant_summable ((n : ℝ) ^ 2 / k) hy
    have hzero :
        (0 : ℝ) < rising (1 / 2 : ℝ) 0 *
          (2 * ((n : ℝ) ^ 2 / k)) ^ 0 / ((Nat.factorial 0 : ℝ) ^ 2) := by simp
    have hle :
        rising (1 / 2 : ℝ) 0 *
            (2 * ((n : ℝ) ^ 2 / k)) ^ 0 / ((Nat.factorial 0 : ℝ) ^ 2) ≤
          ∑' j : ℕ, rising (1 / 2 : ℝ) j *
            (2 * ((n : ℝ) ^ 2 / k)) ^ j / ((j.factorial : ℝ) ^ 2) := by
      simpa using hs.sum_le_tsum ({0} : Finset ℕ) (fun j hj ↦ div_nonneg
        (mul_nonneg (rising_half_nonneg j) (pow_nonneg (by positivity) j))
        (sq_nonneg _))
    exact lt_of_lt_of_le hzero hle
  exact div_le_div_of_nonneg_left (centralBaseline_nonneg n)
    (finiteCorrection_pos k n) (finiteCorrection_le_besselMajorant k n hk)

/-- Unified finite bracket combining the maximum-summand and Bessel-series
lower bounds. -/
theorem combined_max_bessel_ratio_bracket
    (k n jStar : ℕ) (hk : 0 < k) (hjStar : jStar ≤ n)
    (hmax : ∀ j, j ≤ n → finiteTerm k n j ≤ finiteTerm k n jStar) :
    max
        (centralBaseline n / besselMajorant ((n : ℝ) ^ 2 / k))
        (centralBaseline n / ((n + 1 : ℝ) * finiteTerm k n jStar)) ≤
        gramSecondMomentRatio k n ∧
      gramSecondMomentRatio k n ≤
        centralBaseline n / finiteTerm k n jStar := by
  have hmaxBracket := max_summand_ratio_bracket k n jStar hk hjStar hmax
  constructor
  · exact max_le
      (baseline_div_besselMajorant_le_gramSecondMomentRatio k n hk)
      hmaxBracket.1
  · exact hmaxBracket.2

end LogdetLean.GramHafnian
