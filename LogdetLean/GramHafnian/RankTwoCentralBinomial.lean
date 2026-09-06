import LogdetLean.GramHafnian.RankTwoEvenGaussian
import LogdetLean.GramHafnian.FiniteMomentAlgebra
import Mathlib.Data.Nat.Choose.Cast
/-!
# Central-binomial normalization of the rank-two Gaussian moment

The double-factorial moment sum is converted term by term to the convolution
of central binomial coefficients.  This is the exact algebraic form whose
classical quadratic transformation gives the squared-binomial expression.
-/

open scoped BigOperators Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

theorem oddPairingNat_eq_doubleFactorial (j : Nat) :
    oddPairingNat j = (2 * j - 1)‼ := by
  induction j with
  | zero => simp [oddPairingNat]
  | succ j ih =>
      rw [oddPairingNat_succ]
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
        Nat.doubleFactorial_add_one]
      rw [ih]
      ring

/-- Odd double factorial as a factorial quotient, over `Real`; the statement
also covers `j=0` without a side condition. -/
theorem odd_doubleFactorial_cast_eq_factorial_div (j : Nat) :
    (((2 * j - 1)‼ : Nat) : Real) =
      ((2 * j).factorial : Real) /
        ((2 : Real) ^ j * (j.factorial : Real)) := by
  have hnat := factorial_two_mul_eq_even_mul_odd j
  rw [oddPairingNat_eq_doubleFactorial] at hnat
  have hreal :
      ((2 * j).factorial : Real) =
        (2 : Real) ^ j * (j.factorial : Real) *
          (((2 * j - 1)‼ : Nat) : Real) := by
    exact_mod_cast hnat
  have hden : (2 : Real) ^ j * (j.factorial : Real) ≠ 0 := by positivity
  rw [eq_div_iff hden]
  nlinarith

/-- One term of the diagonal double-factorial sum equals its normalized
central-binomial form. -/
theorem even_choose_doubleFactorial_term_eq_central
    (n j : Nat) (hj : j ≤ n) :
    ((2 * n).choose (2 * j) : Real) *
        ((((2 * j - 1)‼ : Nat) : Real) *
          (((2 * (n - j) - 1)‼ : Nat) : Real)) ^ 2 =
      (((2 * n).factorial : Real) / (4 : Real) ^ n) *
        ((2 * j).choose j : Real) *
        ((2 * (n - j)).choose (n - j) : Real) := by
  have h2j : 2 * j ≤ 2 * n := Nat.mul_le_mul_left 2 hj
  have hsub : 2 * n - 2 * j = 2 * (n - j) := by omega
  rw [Nat.cast_choose Real h2j]
  rw [hsub]
  rw [odd_doubleFactorial_cast_eq_factorial_div,
    odd_doubleFactorial_cast_eq_factorial_div]
  rw [Nat.cast_choose Real (show j ≤ 2 * j by omega)]
  rw [Nat.cast_choose Real (show n - j ≤ 2 * (n - j) by omega)]
  have hsubj : 2 * j - j = j := by omega
  have hsubs : 2 * (n-j) - (n-j) = n-j := by omega
  rw [hsubj, hsubs]
  have hfac2n : ((2 * n).factorial : Real) ≠ 0 := by positivity
  have hfac2j : ((2 * j).factorial : Real) ≠ 0 := by positivity
  have hfacs : ((2 * (n-j)).factorial : Real) ≠ 0 := by positivity
  have hfacj : (j.factorial : Real) ≠ 0 := by positivity
  have hfacs' : ((n-j).factorial : Real) ≠ 0 := by positivity
  have hpowj : (2 : Real) ^ j ≠ 0 := by positivity
  have hpows : (2 : Real) ^ (n-j) ≠ 0 := by positivity
  have hpow4 : (4 : Real) ^ n ≠ 0 := by positivity
  field_simp [hfac2n, hfac2j, hfacs, hfacj, hfacs', hpowj, hpows, hpow4]
  rw [show (4 : Real) ^ n = (2 : Real) ^ (2 * n) by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul]]
  rw [show (2 : Real) ^ (2 * n) =
      ((2 : Real) ^ j * (2 : Real) ^ (n-j)) ^ 2 by
    calc
      (2 : Real) ^ (2*n) =
          (2 : Real) ^ (j*2 + (n-j)*2) := by congr 1 <;> omega
      _ = (2 : Real) ^ (j*2) * (2 : Real) ^ ((n-j)*2) := by
        rw [pow_add]
      _ = ((2 : Real)^j * (2 : Real)^(n-j))^2 := by
        rw [pow_mul, pow_mul, mul_pow]]
  ring

/-- Exact central-binomial convolution for the diagonal rank-two moment. -/
theorem integral_diagonalRankTwoBilinear_pow_two_mul_central_sum
    (lambdaPlus lambdaMinus : Real) (n : Nat) :
    (∫ w, diagonalRankTwoBilinear lambdaPlus lambdaMinus w ^ (2 * n)
        ∂twoStandardGaussianPairs) =
      (((2 * n).factorial : Real) / (4 : Real) ^ n) *
        ∑ j ∈ Finset.range (n + 1),
          ((2 * j).choose j : Real) *
            ((2 * (n - j)).choose (n - j) : Real) *
            lambdaPlus ^ (2 * j) * lambdaMinus ^ (2 * (n - j)) := by
  rw [integral_diagonalRankTwoBilinear_pow_two_mul_even_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hjmem
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
  have hterm := even_choose_doubleFactorial_term_eq_central n j hj
  calc
    ((2 * n).choose (2 * j) : Real) * lambdaPlus ^ (2 * j) *
          lambdaMinus ^ (2 * (n - j)) *
          ((((2 * j - 1)‼ : Nat) : Real) *
            (((2 * (n - j) - 1)‼ : Nat) : Real)) ^ 2 =
        (lambdaPlus ^ (2 * j) * lambdaMinus ^ (2 * (n-j))) *
          (((2 * n).choose (2*j) : Real) *
            ((((2*j-1)‼ : Nat) : Real) *
              (((2*(n-j)-1)‼ : Nat) : Real))^2) := by ring
    _ = (lambdaPlus ^ (2 * j) * lambdaMinus ^ (2 * (n-j))) *
          ((((2*n).factorial : Real) / (4 : Real)^n) *
            ((2*j).choose j : Real) *
            ((2*(n-j)).choose (n-j) : Real)) := by rw [hterm]
    _ = ((2 * n).factorial : Real) / (4 : Real) ^ n *
        (((2 * j).choose j : Real) *
          ((2 * (n - j)).choose (n - j) : Real) *
          lambdaPlus ^ (2 * j) * lambdaMinus ^ (2 * (n - j))) := by ring

end

end LogdetLean.GramHafnian
