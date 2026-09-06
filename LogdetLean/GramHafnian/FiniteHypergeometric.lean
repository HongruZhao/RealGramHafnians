import LogdetLean.GramHafnian.FiniteSum
import Mathlib.RingTheory.Polynomial.Pochhammer
/-!
# Hypergeometric form of the finite Gram--hafnian correction

The generalized hypergeometric function is not currently a primitive Mathlib
object.  For a terminating upper parameter `-n`, its value is just a finite
sum.  We therefore define the terminating `₃F₂` polynomial directly and prove
that the Gram--hafnian correction factor is exactly its specialization at one.
-/

open scoped BigOperators
open Finset Polynomial

namespace LogdetLean.GramHafnian

/-- The rising Pochhammer symbol `(a)_j`. -/
noncomputable def rising (a : ℝ) (j : ℕ) : ℝ :=
  (ascPochhammer ℝ j).eval a

@[simp] theorem rising_zero (a : ℝ) : rising a 0 = 1 := by
  simp [rising]

theorem rising_succ (a : ℝ) (j : ℕ) :
    rising a (j + 1) = rising a j * (a + j) := by
  exact ascPochhammer_succ_eval j a

theorem rising_pos {a : ℝ} (ha : 0 < a) (j : ℕ) : 0 < rising a j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [rising_succ]
      exact mul_pos ih (by positivity)

@[simp] theorem rising_one (j : ℕ) : rising 1 j = (j.factorial : ℝ) := by
  exact (Nat.cast_factorial ℝ j).symm

/-- Evaluation of `(-n)_j` as a signed descending factorial. -/
theorem rising_neg_nat (n j : ℕ) :
    rising (-(n : ℝ)) j = (-1 : ℝ) ^ j * (n.descFactorial j : ℕ) := by
  rw [rising, ascPochhammer_eval_neg_eq_descPochhammer]
  rw [descPochhammer_eval_eq_descFactorial]

/-- When `j ≤ n`, division by `j!` turns `(-n)_j` into a signed binomial
coefficient. -/
theorem rising_neg_nat_div_factorial (n j : ℕ) :
    rising (-(n : ℝ)) j / (j.factorial : ℝ) =
      (-1 : ℝ) ^ j * (n.choose j : ℕ) := by
  rw [rising_neg_nat]
  rw [Nat.descFactorial_eq_factorial_mul_choose n j]
  push_cast
  have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfac]

/-- The product representation used by `finiteCorrection` is exactly the
ratio of the two usual Pochhammer symbols. -/
theorem half_rising_div_dimension_rising
    (k j : ℕ) (hk : 0 < k) :
    rising (1 / 2 : ℝ) j / rising ((k : ℝ) / 2) j =
      pochhammerRatio k j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [rising_succ, rising_succ, pochhammerRatio_succ]
      have hprev : rising ((k : ℝ) / 2) j ≠ 0 :=
        ne_of_gt (rising_pos (by positivity) j)
      have hnext : (k : ℝ) / 2 + j ≠ 0 := by positivity
      have hnat : ((k + 2 * j : ℕ) : ℝ) ≠ 0 := by positivity
      have hcross :
          rising (1 / 2 : ℝ) j =
            pochhammerRatio k j * rising ((k : ℝ) / 2) j :=
        (div_eq_iff hprev).mp ih
      field_simp [hprev, hnext, hnat]
      rw [hcross]
      push_cast
      ring

/-- Paper-facing finite-sum form with literal rising Pochhammer symbols. -/
theorem finiteCorrection_eq_pochhammer_sum
    (k n : ℕ) (hk : 0 < k) :
    finiteCorrection k n =
      ∑ j ∈ range (n + 1),
        ((n.choose j : ℕ) : ℝ) ^ 2 *
          (rising (1 / 2 : ℝ) j / rising ((k : ℝ) / 2) j) := by
  rw [finiteCorrection]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteTerm, half_rising_div_dimension_rising k j hk]

/-- A terminating generalized hypergeometric polynomial `₃F₂`.  This is the
standard coefficient definition; termination is enforced by summing only
through degree `n`. -/
noncomputable def terminatingThreeFtwo
    (n : ℕ) (a₁ a₂ a₃ b₁ b₂ z : ℝ) : ℝ :=
  ∑ j ∈ range (n + 1),
    (rising a₁ j * rising a₂ j * rising a₃ j) /
      (rising b₁ j * rising b₂ j * (j.factorial : ℝ)) * z ^ j

/-- Coefficient-by-coefficient identification of the specialized terminating
`₃F₂` with the Gram--hafnian finite summand. -/
theorem terminatingThreeFtwo_term_eq_finiteTerm
    (k n j : ℕ) (hk : 0 < k) :
    (rising (-(n : ℝ)) j * rising (-(n : ℝ)) j * rising (1 / 2 : ℝ) j) /
        (rising 1 j * rising ((k : ℝ) / 2) j * (j.factorial : ℝ)) =
      finiteTerm k n j := by
  rw [finiteTerm, rising_one]
  have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hdim : rising ((k : ℝ) / 2) j ≠ 0 :=
    ne_of_gt (rising_pos (by positivity) j)
  have hneg := rising_neg_nat_div_factorial n j
  have hhalf := half_rising_div_dimension_rising k j hk
  rw [div_eq_iff hfac] at hneg
  rw [div_eq_iff hdim] at hhalf
  rw [hneg, hhalf]
  have hsign : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  field_simp [hfac, hdim]
  ring_nf
  rw [pow_mul, hsign, mul_one]

/-- Exact hypergeometric identity

`F_{k,n} = ₃F₂(-n,-n,1/2; 1,k/2; 1)`.
-/
theorem finiteCorrection_eq_terminatingThreeFtwo
    (k n : ℕ) (hk : 0 < k) :
    finiteCorrection k n =
      terminatingThreeFtwo n (-(n : ℝ)) (-(n : ℝ)) (1 / 2 : ℝ)
        1 ((k : ℝ) / 2) 1 := by
  rw [finiteCorrection, terminatingThreeFtwo]
  apply Finset.sum_congr rfl
  intro j hj
  rw [one_pow, mul_one]
  exact (terminatingThreeFtwo_term_eq_finiteTerm k n j hk).symm

end LogdetLean.GramHafnian
