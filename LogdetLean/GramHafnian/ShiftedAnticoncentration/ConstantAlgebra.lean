import LogdetLean.GramHafnian.ShiftedAnticoncentration.InverseMomentRecurrence
import LogdetLean.GramHafnian.RankTwoCentralBinomial
import LogdetLean.GramHafnian.RankOneGaussianBilinear
/-!
# Exact normalization algebra

The probabilistic proof produces `closedFirstMoment k n *
inverseVarianceBound k n`.  This file verifies that this expression is
exactly the coefficient displayed in the finite anticoncentration theorem.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- The even gap product in the inverse-moment recursion. -/
def evenRecurrenceProduct (n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n, ((2 : ℝ) * r - 2)

theorem evenRecurrenceProduct_eq (n : ℕ) (hn : 1 ≤ n) :
    evenRecurrenceProduct n =
      (2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ =>
    evenRecurrenceProduct j =
      (2 : ℝ) ^ (j - 1) * ((j - 1).factorial : ℝ)
  apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
  · simp [P, evenRecurrenceProduct]
  · intro j hj ih
    change evenRecurrenceProduct j =
      (2 : ℝ) ^ (j - 1) * ((j - 1).factorial : ℝ) at ih
    change evenRecurrenceProduct (j + 1) =
      (2 : ℝ) ^ (j + 1 - 1) * ((j + 1 - 1).factorial : ℝ)
    unfold evenRecurrenceProduct at ih ⊢
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have hjsub : j + 1 - 1 = j := by omega
    have hjpos : j - 1 + 1 = j := by omega
    rw [hjsub, ← hjpos, Nat.factorial_succ, pow_succ]
    push_cast
    ring

/-- Split the dimension product into its first factor and the factors indexed
by the inverse-moment levels. -/
theorem dimensionProduct_eq_head_mul_Icc (k n : ℕ) (hn : 1 ≤ n) :
    dimensionProduct k n =
      (k : ℝ) * ∏ r ∈ Finset.Icc 2 n,
        ((k : ℝ) + 2 * (r : ℝ) - 2) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ =>
    dimensionProduct k j =
      (k : ℝ) * ∏ r ∈ Finset.Icc 2 j,
        ((k : ℝ) + 2 * (r : ℝ) - 2)
  apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
  · simp [P, dimensionProduct]
  · intro j hj ih
    change dimensionProduct k j =
      (k : ℝ) * ∏ r ∈ Finset.Icc 2 j,
        ((k : ℝ) + 2 * (r : ℝ) - 2) at ih
    change dimensionProduct k (j + 1) =
      (k : ℝ) * ∏ r ∈ Finset.Icc 2 (j + 1),
        ((k : ℝ) + 2 * (r : ℝ) - 2)
    rw [dimensionProduct_succ, ih,
      Finset.prod_Icc_succ_top (by omega)]
    push_cast
    ring

/-- The double-factorial/even-factor quotient in the normalization is the
central-binomial coefficient appearing in the paper. -/
theorem oddPairing_mul_evenRecurrenceProduct_inv
    (n : ℕ) (hn : 1 ≤ n) :
    (oddPairingNat n : ℝ) * (evenRecurrenceProduct n)⁻¹ =
      (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n := by
  rw [evenRecurrenceProduct_eq n hn]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hle : m + 1 ≤ 2 * (m + 1) := by omega
  have hchoose := Nat.cast_choose ℝ hle
  have hsub : 2 * (m + 1) - (m + 1) = m + 1 := by omega
  rw [hsub] at hchoose
  have hfacNat := factorial_two_mul_eq_even_mul_odd (m + 1)
  have hfac :
      (((2 * (m + 1)).factorial : ℕ) : ℝ) =
        (2 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) *
          (oddPairingNat (m + 1) : ℝ) := by
    exact_mod_cast hfacNat
  rw [hchoose, hfac]
  have hmfac : (m.factorial : ℝ) ≠ 0 := by positivity
  have hsmfac : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ m ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ m ≠ 0 := by positivity
  rw [show m + 1 - 1 = m by omega, Nat.factorial_succ, pow_succ,
    show (4 : ℝ) ^ (m + 1) = 4 ^ m * 4 by rw [pow_succ]]
  push_cast
  field_simp [hmfac, hsmfac, htwo, hfour]
  have hpow : (4 : ℝ) ^ m = (2 : ℝ) ^ (m * 2) := by
    calc
      (4 : ℝ) ^ m = ((2 : ℝ) ^ 2) ^ m := by norm_num
      _ = (2 : ℝ) ^ (2 * m) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (m * 2) := by congr 1 <;> omega
  rw [hpow]
  rw [← pow_mul]
  norm_num

/-- The second denominator product in the inverse-moment recursion. -/
def wishartRecurrenceProduct (k n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n, ((k : ℝ) - 4 * (r : ℝ) + 1)

theorem prod_inverseVarianceStep_split (k n : ℕ) :
    (∏ r ∈ Finset.Icc 2 n, inverseVarianceStep k r) =
      (evenRecurrenceProduct n)⁻¹ * (wishartRecurrenceProduct k n)⁻¹ := by
  unfold inverseVarianceStep evenRecurrenceProduct wishartRecurrenceProduct
  simp_rw [mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_inv_distrib]

/-- The numerator product in the displayed finite theorem coefficient. -/
def shiftedNumeratorProduct (k n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n, ((k : ℝ) + 2 * (r : ℝ) - 2)

theorem prod_shifted_ratio_split (k n : ℕ) :
    (∏ r ∈ Finset.Icc 2 n,
        (((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1))) =
      shiftedNumeratorProduct k n / wishartRecurrenceProduct k n := by
  exact Finset.prod_div_distrib _ _

/-- Exact identification of the probabilistic normalization with the
coefficient printed in the main theorem. -/
theorem closedFirstMoment_mul_inverseVarianceBound
    (k n : ℕ) (hn : 1 ≤ n) :
    closedFirstMoment k n * inverseVarianceBound k n =
      shiftedAnticoncentrationConstant k n := by
  have hdim := dimensionProduct_eq_head_mul_Icc k n hn
  change dimensionProduct k n = (k : ℝ) * shiftedNumeratorProduct k n at hdim
  have hodd := oddPairing_mul_evenRecurrenceProduct_inv n hn
  rw [closedFirstMoment, inverseVarianceBound,
    prod_inverseVarianceStep_split, shiftedAnticoncentrationConstant,
    prod_shifted_ratio_split, hdim]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    ((oddPairingNat n : ℝ) * ((k : ℝ) * shiftedNumeratorProduct k n)) *
          (((k : ℝ) - 1)⁻¹ *
            ((evenRecurrenceProduct n)⁻¹ *
              (wishartRecurrenceProduct k n)⁻¹)) =
        ((oddPairingNat n : ℝ) * (evenRecurrenceProduct n)⁻¹) *
          ((k : ℝ) * shiftedNumeratorProduct k n) *
          ((k : ℝ) - 1)⁻¹ * (wishartRecurrenceProduct k n)⁻¹ := by ring
    _ = ((2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) *
          ((4 : ℝ) ^ n)⁻¹) *
          ((k : ℝ) * shiftedNumeratorProduct k n) *
          ((k : ℝ) - 1)⁻¹ * (wishartRecurrenceProduct k n)⁻¹ := by
      rw [hodd]
      ring
    _ = (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) *
          ((4 : ℝ) ^ n)⁻¹ *
          ((k : ℝ) * ((k : ℝ) - 1)⁻¹) *
          (shiftedNumeratorProduct k n *
            (wishartRecurrenceProduct k n)⁻¹) := by ring

end

end LogdetLean.GramHafnian
