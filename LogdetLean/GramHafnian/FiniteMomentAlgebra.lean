import LogdetLean.GramHafnian.FiniteSum
import Mathlib.Data.Nat.Choose.Cast
/-!
# Deterministic normalization of the exact Gram--hafnian moments

Assuming the probabilistic calculation supplies the two displayed closed
moments, this file proves by exact finite algebra that their quotient is the
central-binomial baseline divided by `finiteCorrection`.
-/

open scoped BigOperators
open Finset

namespace LogdetLean.GramHafnian

/-- `(2n-1)!!`, with the harmless factor `1` retained at the beginning. -/
def oddPairingNat (n : ℕ) : ℕ :=
  ∏ i ∈ range n, (2 * i + 1)

/-- The row-dimension product `k(k+2)...(k+2n-2)`. -/
noncomputable def dimensionProduct (k n : ℕ) : ℝ :=
  ∏ q ∈ range n, ((k + 2 * q : ℕ) : ℝ)

/-- The closed form for the first absolute-square moment. -/
noncomputable def closedFirstMoment (k n : ℕ) : ℝ :=
  (oddPairingNat n : ℝ) * dimensionProduct k n

/-- The closed form for the fourth absolute moment. -/
noncomputable def closedFourthMoment (k n : ℕ) : ℝ :=
  ((2 * n).factorial : ℝ) * (dimensionProduct k n) ^ 2 * finiteCorrection k n

@[simp] theorem oddPairingNat_zero : oddPairingNat 0 = 1 := by
  simp [oddPairingNat]

theorem oddPairingNat_succ (n : ℕ) :
    oddPairingNat (n + 1) = oddPairingNat n * (2 * n + 1) := by
  simp [oddPairingNat, Finset.prod_range_succ]

/-- Split `(2n)!` into its even and odd factors. -/
theorem factorial_two_mul_eq_even_mul_odd (n : ℕ) :
    (2 * n).factorial = 2 ^ n * n.factorial * oddPairingNat n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [Nat.factorial_succ]
      rw [Nat.factorial_succ]
      rw [oddPairingNat_succ, Nat.factorial_succ, pow_succ, ih]
      ring

/-- The pairing/factorial quotient is exactly the central-binomial baseline. -/
theorem oddPairing_sq_div_factorial_eq_centralBaseline (n : ℕ) :
    ((oddPairingNat n : ℕ) : ℝ) ^ 2 / ((2 * n).factorial : ℝ) =
      centralBaseline n := by
  rw [centralBaseline]
  have hfacNat := factorial_two_mul_eq_even_mul_odd n
  have hfac :
      (((2 * n).factorial : ℕ) : ℝ) =
        (2 : ℝ) ^ n * (n.factorial : ℝ) * (oddPairingNat n : ℝ) := by
    exact_mod_cast hfacNat
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial
    (show n ≤ 2 * n by omega)
  have hchoose :
      ((Nat.choose (2 * n) n : ℕ) : ℝ) * (n.factorial : ℝ) *
          ((2 * n - n).factorial : ℝ) = ((2 * n).factorial : ℝ) := by
    exact_mod_cast hchooseNat
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hchoose
  have hodd : ((oddPairingNat n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      omega : ∀ i ∈ range n, 2 * i + 1 ≠ 0))
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ n ≠ 0 := by positivity
  have htotal : (((2 * n).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [htotal, hfour]
  rw [hfac] at hchoose ⊢
  field_simp [hodd, hnfac, htwo] at hchoose ⊢
  have hfourtwo : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  rw [hfourtwo, hchoose]
  ring

theorem dimensionProduct_pos (k n : ℕ) (hk : 0 < k) :
    0 < dimensionProduct k n := by
  unfold dimensionProduct
  apply Finset.prod_pos
  intro i hi
  positivity

/-- Exact algebraic cancellation of the common dimension product in the two
closed moments. -/
theorem closed_moment_ratio_eq_gramSecondMomentRatio
    (k n : ℕ) (hk : 0 < k) :
    closedFirstMoment k n ^ 2 / closedFourthMoment k n =
      gramSecondMomentRatio k n := by
  rw [closedFirstMoment, closedFourthMoment, gramSecondMomentRatio]
  have hP : dimensionProduct k n ≠ 0 := ne_of_gt (dimensionProduct_pos k n hk)
  have hfac : (((2 * n).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hF : finiteCorrection k n ≠ 0 := ne_of_gt (finiteCorrection_pos k n)
  rw [← oddPairing_sq_div_factorial_eq_centralBaseline n]
  field_simp [hP, hfac, hF]

/-- Paper-facing implication: any random variable whose first and fourth
moments equal the two closed forms has the stated exact normalized second
moment. -/
theorem exact_normalized_second_moment_of_closed_forms
    (k n : ℕ) (hk : 0 < k) (M₁ M₂ : ℝ)
    (h₁ : M₁ = closedFirstMoment k n)
    (h₂ : M₂ = closedFourthMoment k n) :
    M₁ ^ 2 / M₂ = gramSecondMomentRatio k n := by
  rw [h₁, h₂]
  exact closed_moment_ratio_eq_gramSecondMomentRatio k n hk

end LogdetLean.GramHafnian
