import LogdetLean.GramHafnian.ShiftedAnticoncentration.PolynomialSmallBall
import LogdetLean.Coherence.BetaHalfNormalization
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
/-!
# Gamma form and sharp asymptotics of the finite coefficient

This module gives the exact Gamma representation of the finite shifted
anticoncentration coefficient and isolates its dimension dependent correction.
The quantitative logarithmic remainder is the input for the improved
polynomial small ball corollary.
-/

open Filter
open scoped BigOperators Nat

namespace LogdetLean.GramHafnian.CurrentPRL

noncomputable section

/-- The limiting normalized coefficient, written in Gamma form. -/
def limitingAnticoncentrationConstant (n : ℕ) : ℝ :=
  2 * Real.Gamma ((n : ℝ) + 1 / 2) /
    (Real.sqrt Real.pi * Real.Gamma (n : ℝ))

/-- The finite coefficient, written entirely with Gamma quotients. -/
def gammaAnticoncentrationConstant (k n : ℕ) : ℝ :=
  limitingAnticoncentrationConstant n *
    ((k : ℝ) / ((k : ℝ) - 1)) *
    ((2 : ℝ) ^ (n - 1) / (4 : ℝ) ^ (n - 1)) *
    (Real.Gamma ((k : ℝ) / 2 + (n : ℝ)) /
      Real.Gamma ((k : ℝ) / 2 + 1)) *
    (Real.Gamma (((k : ℝ) - 4 * (n : ℝ) + 1) / 4) /
      Real.Gamma (((k : ℝ) - 3) / 4))

/-- The Gamma definition of the limiting coefficient agrees with the
central binomial expression used by the finite theorem. -/
theorem limitingAnticoncentrationConstant_eq_centralBinomial
    (n : ℕ) (hn : 1 ≤ n) :
    limitingAnticoncentrationConstant n =
      (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [limitingAnticoncentrationConstant]
  rw [show (((1 + m : ℕ) : ℝ) + 1 / 2) = (m + 1 : ℕ) + 1 / 2 by
    push_cast; ring]
  rw [Real.Gamma_nat_add_half (m + 1)]
  rw [show (((1 + m : ℕ) : ℝ)) = (m : ℝ) + 1 by push_cast; ring]
  rw [Real.Gamma_nat_eq_factorial m]
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
  calc
    2 * ((↑(2 * m + 1)‼ : ℝ) * Real.sqrt Real.pi /
          2 ^ (m + 1)) /
        (Real.sqrt Real.pi * ↑m.factorial) =
        (oddPairingNat (m + 1) : ℝ) *
          ((2 : ℝ) ^ m * (m.factorial : ℝ))⁻¹ := by
      have hdf : 2 * m + 1 = 2 * (m + 1) - 1 := by omega
      rw [oddPairingNat_eq_doubleFactorial]
      rw [hdf]
      have htwo : (2 : ℝ) ^ m ≠ 0 := by positivity
      have hfac : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp [hsqrt, htwo, hfac, pow_succ]
      ring
    _ = (2 * ((m + 1 : ℕ) : ℝ)) *
          (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) /
          (4 : ℝ) ^ (m + 1) := by
      have h := oddPairing_mul_evenRecurrenceProduct_inv (m + 1) (by omega)
      rw [evenRecurrenceProduct_eq (m + 1) (by omega)] at h
      simpa using h
    _ = (2 * (((1 + m : ℕ) : ℝ))) *
          (Nat.choose (2 * (1 + m)) (1 + m) : ℝ) /
          (4 : ℝ) ^ (1 + m) := by
      simp only [add_comm]
  push_cast
  ring

/-- Numerator product in the finite correction, as a Gamma quotient. -/
theorem shiftedNumeratorProduct_eq_gamma
    (k n : ℕ) (hn : 1 ≤ n) (hk : 0 < k) :
    (∏ r ∈ Finset.Icc 2 n,
        ((k : ℝ) + 2 * (r : ℝ) - 2)) =
      (2 : ℝ) ^ (n - 1) *
        (Real.Gamma ((k : ℝ) / 2 + (n : ℝ)) /
          Real.Gamma ((k : ℝ) / 2 + 1)) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    (∏ r ∈ Finset.Icc 2 j,
        ((k : ℝ) + 2 * (r : ℝ) - 2)) =
      (2 : ℝ) ^ (j - 1) *
        (Real.Gamma ((k : ℝ) / 2 + (j : ℝ)) /
          Real.Gamma ((k : ℝ) / 2 + 1))
  apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
  · dsimp [P]
    have hG : Real.Gamma ((k : ℝ) / 2 + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    simp [hG]
  · intro j hj ih
    dsimp [P] at ih ⊢
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have harg : (k : ℝ) / 2 + (j : ℝ) ≠ 0 := by positivity
    rw [show (k : ℝ) / 2 + ((j + 1 : ℕ) : ℝ) =
      ((k : ℝ) / 2 + (j : ℝ)) + 1 by push_cast; ring]
    rw [Real.Gamma_add_one harg]
    have hpow : (2 : ℝ) ^ j = (2 : ℝ) ^ (j - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    push_cast
    ring

/-- Denominator product in the finite correction, as a Gamma quotient. -/
theorem shiftedDenominatorProduct_eq_gamma
    (k n : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    (∏ r ∈ Finset.Icc 2 n,
        ((k : ℝ) - 4 * (r : ℝ) + 1)) =
      (4 : ℝ) ^ (n - 1) *
        (Real.Gamma (((k : ℝ) - 3) / 4) /
          Real.Gamma (((k : ℝ) - 4 * (n : ℝ) + 1) / 4)) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    4 * j ≤ k →
      (∏ r ∈ Finset.Icc 2 j,
          ((k : ℝ) - 4 * (r : ℝ) + 1)) =
        (4 : ℝ) ^ (j - 1) *
          (Real.Gamma (((k : ℝ) - 3) / 4) /
            Real.Gamma (((k : ℝ) - 4 * (j : ℝ) + 1) / 4))
  have hP : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · intro hk1
      dsimp [P]
      have harg : 0 < ((k : ℝ) - 3) / 4 := by
        have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        linarith
      have hG : Real.Gamma (((k : ℝ) - 3) / 4) ≠ 0 :=
        (Real.Gamma_pos_of_pos harg).ne'
      have heq : ((k : ℝ) - 4 + 1) / 4 = ((k : ℝ) - 3) / 4 := by ring
      simp [heq, hG]
    · intro j hj ih hkj
      dsimp [P] at ih ⊢
      have hprev : 4 * j ≤ k := by omega
      rw [Finset.prod_Icc_succ_top (by omega), ih hprev]
      let a : ℝ := ((k : ℝ) - 4 * ((j + 1 : ℕ) : ℝ) + 1) / 4
      have ha : 0 < a := by
        dsimp [a]
        have hkR : (4 * (j + 1) : ℕ) ≤ k := hkj
        have hkR' : (4 : ℝ) * ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast hkR
        linarith
      have hold : ((k : ℝ) - 4 * (j : ℝ) + 1) / 4 = a + 1 := by
        dsimp [a]
        push_cast
        ring
      rw [hold, Real.Gamma_add_one ha.ne']
      have hpow : (4 : ℝ) ^ j = (4 : ℝ) ^ (j - 1) * 4 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      have hfac :
          (k : ℝ) - 4 * ((j + 1 : ℕ) : ℝ) + 1 = 4 * a := by
        dsimp [a]
        ring
      rw [hfac]
      have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
      field_simp [ha.ne', hGa, mul_ne_zero ha.ne' hGa]
  exact hP hkn

/-- Exact Gamma representation of the finite shifted coefficient. -/
theorem shiftedAnticoncentrationConstant_eq_gamma
    (k n : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    shiftedAnticoncentrationConstant k n =
      gammaAnticoncentrationConstant k n := by
  have hk : 0 < k := by omega
  rw [shiftedAnticoncentrationConstant, gammaAnticoncentrationConstant]
  rw [limitingAnticoncentrationConstant_eq_centralBinomial n hn]
  rw [Finset.prod_div_distrib]
  rw [shiftedNumeratorProduct_eq_gamma k n hn hk]
  rw [shiftedDenominatorProduct_eq_gamma k n hn hkn]
  have hlow : 0 < ((k : ℝ) - 4 * (n : ℝ) + 1) / 4 := by
    have hkR : (4 : ℝ) * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkn
    linarith
  have hhigh : 0 < ((k : ℝ) - 3) / 4 := by
    have hk4 : 4 ≤ k := by omega
    have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
    linarith
  have hGlo : Real.Gamma (((k : ℝ) - 4 * (n : ℝ) + 1) / 4) ≠ 0 :=
    (Real.Gamma_pos_of_pos hlow).ne'
  have hGhi : Real.Gamma (((k : ℝ) - 3) / 4) ≠ 0 :=
    (Real.Gamma_pos_of_pos hhigh).ne'
  have hGnum : Real.Gamma ((k : ℝ) / 2 + (n : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hGden : Real.Gamma ((k : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have htwo : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ (n - 1) ≠ 0 := by positivity
  field_simp [hGlo, hGhi, hGnum, hGden, htwo, hfour]

/-- Exact cubic sum controlling the second order denominator correction. -/
theorem sum_Icc_two_shifted_numerator_mul_denominator_loss
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.Icc 2 n,
        (6 * (r : ℝ) - 3) * (4 * (r : ℝ) - 1)) =
      8 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2 - 2 * (n : ℝ) - 9 := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    (∑ r ∈ Finset.Icc 2 j,
        (6 * (r : ℝ) - 3) * (4 * (r : ℝ) - 1)) =
      8 * (j : ℝ) ^ 3 + 3 * (j : ℝ) ^ 2 - 2 * (j : ℝ) - 9
  apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
  · norm_num [P]
  · intro j hj ih
    dsimp [P] at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- The exact cubic numerator is bounded by the clean `9n³` envelope. -/
theorem one_add_shifted_cubic_sum_le_nine_cube
    (n : ℕ) (hn : 1 ≤ n) :
    1 + (8 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2 -
      2 * (n : ℝ) - 9) ≤ 9 * (n : ℝ) ^ 3 := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) + 8 := by
    by_cases htwo : (n : ℝ) ≤ 2
    · have hn2 : n ≤ 2 := by exact_mod_cast htwo
      interval_cases n <;> norm_num
    · have : 0 ≤ (n : ℝ) - 2 := by linarith
      positivity
  nlinarith

/-- Sharpened exponent used in the finite coefficient bound. -/
def sharpAnticoncentrationExponent (k n : ℕ) : ℝ :=
  (3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) +
    9 * (n : ℝ) ^ 3 /
      ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1))

/-- The sum of the first order logarithmic losses is bounded by the sharp
leading exponent and a uniform cubic remainder. -/
theorem linearizedAnticoncentrationExponent_le_sharp
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    1 / ((k : ℝ) - 1) +
        ∑ r ∈ Finset.Icc 2 n,
          (6 * (r : ℝ) - 3) /
            ((k : ℝ) - 4 * (r : ℝ) + 1) ≤
      sharpAnticoncentrationExponent k n := by
  have hkposNat : 0 < k := by omega
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkposNat
  have hdmin : 0 < (k : ℝ) - 4 * (n : ℝ) + 1 :=
    shiftedDenominator_pos hkn le_rfl
  have hkm1 : 0 < (k : ℝ) - 1 := by
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
    linarith
  have hheadEq :
      1 / ((k : ℝ) - 1) =
        1 / (k : ℝ) + 1 /
          ((k : ℝ) * ((k : ℝ) - 1)) := by
    field_simp [hkpos.ne', hkm1.ne']
    ring
  have hdmin_le_km1 :
      (k : ℝ) - 4 * (n : ℝ) + 1 ≤ (k : ℝ) - 1 := by
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hhead :
      1 / ((k : ℝ) - 1) ≤
        1 / (k : ℝ) + 1 /
          ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) := by
    rw [hheadEq]
    gcongr
  have hterm : ∀ r ∈ Finset.Icc 2 n,
      (6 * (r : ℝ) - 3) /
          ((k : ℝ) - 4 * (r : ℝ) + 1) ≤
        (6 * (r : ℝ) - 3) / (k : ℝ) +
          ((6 * (r : ℝ) - 3) * (4 * (r : ℝ) - 1)) /
            ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) := by
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hden : 0 < (k : ℝ) - 4 * (r : ℝ) + 1 :=
      shiftedDenominator_pos hkn hrn
    have hnum : 0 ≤ 6 * (r : ℝ) - 3 := by
      have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
      linarith
    have hloss : 0 ≤ 4 * (r : ℝ) - 1 := by
      have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
      linarith
    have hdecomp :
        (6 * (r : ℝ) - 3) /
            ((k : ℝ) - 4 * (r : ℝ) + 1) =
          (6 * (r : ℝ) - 3) / (k : ℝ) +
            ((6 * (r : ℝ) - 3) * (4 * (r : ℝ) - 1)) /
              ((k : ℝ) * ((k : ℝ) - 4 * (r : ℝ) + 1)) := by
      let a : ℝ := 6 * (r : ℝ) - 3
      let b : ℝ := 4 * (r : ℝ) - 1
      let d : ℝ := (k : ℝ) - 4 * (r : ℝ) + 1
      have hd : d ≠ 0 := by exact (by simpa [d] using hden.ne')
      have hsum : (k : ℝ) = d + b := by
        dsimp [d, b]
        ring
      change a / d = a / (k : ℝ) + a * b / ((k : ℝ) * d)
      field_simp [hd, hkpos.ne']
      nlinarith
    rw [hdecomp]
    gcongr
  calc
    1 / ((k : ℝ) - 1) +
          ∑ r ∈ Finset.Icc 2 n,
            (6 * (r : ℝ) - 3) /
              ((k : ℝ) - 4 * (r : ℝ) + 1) ≤
        (1 / (k : ℝ) + 1 /
            ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1))) +
          ∑ r ∈ Finset.Icc 2 n,
            ((6 * (r : ℝ) - 3) / (k : ℝ) +
              ((6 * (r : ℝ) - 3) * (4 * (r : ℝ) - 1)) /
                ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1))) := by
      exact add_le_add hhead (Finset.sum_le_sum hterm)
    _ = (3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) +
        (1 + (8 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2 -
          2 * (n : ℝ) - 9)) /
          ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
      rw [sum_Icc_two_six_mul_sub_three n hn]
      rw [sum_Icc_two_shifted_numerator_mul_denominator_loss n hn]
      ring
    _ ≤ sharpAnticoncentrationExponent k n := by
      unfold sharpAnticoncentrationExponent
      gcongr
      exact one_add_shifted_cubic_sum_le_nine_cube n hn

/-- The complete rational correction is bounded by the sharpened exponential
envelope. -/
theorem shiftedCorrectionProduct_le_exp_sharp
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    ((k : ℝ) / ((k : ℝ) - 1)) *
        (∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
      Real.exp (sharpAnticoncentrationExponent k n) := by
  let f : ℕ → ℝ := fun r ↦
    (6 * (r : ℝ) - 3) / ((k : ℝ) - 4 * (r : ℝ) + 1)
  have hf_nonneg : ∀ r ∈ Finset.Icc 2 n, 0 ≤ f r := by
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hden := shiftedDenominator_pos hkn hrn
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    exact div_nonneg (by linarith) hden.le
  have hrewrite :
      (∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) =
        ∏ r ∈ Finset.Icc 2 n, (1 + f r) := by
    apply Finset.prod_congr rfl
    intro r hr
    have hrn := (Finset.mem_Icc.mp hr).2
    exact shiftedRatio_eq_one_add (shiftedDenominator_pos hkn hrn)
  have hprod :
      (∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
        Real.exp (∑ r ∈ Finset.Icc 2 n, f r) := by
    rw [hrewrite]
    calc
      (∏ r ∈ Finset.Icc 2 n, (1 + f r)) ≤
          ∏ r ∈ Finset.Icc 2 n, Real.exp (f r) := by
        apply Finset.prod_le_prod
        · intro r hr
          exact add_nonneg zero_le_one (hf_nonneg r hr)
        · intro r hr
          simpa [add_comm] using Real.add_one_le_exp (f r)
      _ = Real.exp (∑ r ∈ Finset.Icc 2 n, f r) := by
        rw [Real.exp_sum]
  have hhead := shiftedHeadRatio_le_exp hn hkn
  have hhead0 : 0 ≤ (k : ℝ) / ((k : ℝ) - 1) := by
    have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
    exact div_nonneg (Nat.cast_nonneg k) (by linarith)
  have hprod0 : 0 ≤
      ∏ r ∈ Finset.Icc 2 n,
        (((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1)) := by
    apply Finset.prod_nonneg
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hden := shiftedDenominator_pos hkn hrn
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    have hnum : 0 ≤ (k : ℝ) + 2 * (r : ℝ) - 2 := by
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact div_nonneg hnum hden.le
  calc
    ((k : ℝ) / ((k : ℝ) - 1)) *
          (∏ r ∈ Finset.Icc 2 n,
            (((k : ℝ) + 2 * (r : ℝ) - 2) /
              ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
        Real.exp (1 / ((k : ℝ) - 1)) *
          Real.exp (∑ r ∈ Finset.Icc 2 n, f r) := by
      exact mul_le_mul hhead hprod hprod0 (Real.exp_nonneg _)
    _ = Real.exp
        (1 / ((k : ℝ) - 1) +
          ∑ r ∈ Finset.Icc 2 n, f r) := by
      rw [Real.exp_add]
    _ ≤ Real.exp (sharpAnticoncentrationExponent k n) := by
      apply Real.exp_le_exp.mpr
      exact linearizedAnticoncentrationExponent_le_sharp hn hkn

/-- Sharpened finite coefficient bound with exact limiting prefactor. -/
theorem shiftedAnticoncentrationConstant_le_gamma_sharp
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    shiftedAnticoncentrationConstant k n ≤
      limitingAnticoncentrationConstant n *
        Real.exp (sharpAnticoncentrationExponent k n) := by
  have hb : 0 ≤ limitingAnticoncentrationConstant n := by
    unfold limitingAnticoncentrationConstant
    positivity
  rw [shiftedAnticoncentrationConstant]
  rw [← limitingAnticoncentrationConstant_eq_centralBinomial n hn]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (shiftedCorrectionProduct_le_exp_sharp hn hkn) hb

/-- Quadratic remainder for `log (1+x)` on the nonnegative half line. -/
theorem abs_log_one_add_sub_self_le_half_sq
    {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (1 + x) - x| ≤ x ^ 2 / 2 := by
  have hpos : 0 < 1 + x := by linarith
  have hupp : Real.log (1 + x) ≤ x := by
    simpa using Real.log_le_sub_one_of_pos hpos
  have hlow := Real.le_log_one_add_of_nonneg hx
  have hden : 0 < x + 2 := by linarith
  have hgap : x - 2 * x / (x + 2) = x ^ 2 / (x + 2) := by
    field_simp [hden.ne']
    ring
  have hgapLe : x ^ 2 / (x + 2) ≤ x ^ 2 / 2 := by
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hupp)]
  rw [neg_sub]
  linarith

theorem log_one_add_le_self {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x := by
  simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)

theorem self_sub_half_sq_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have h := abs_log_one_add_sub_self_le_half_sq hx
  rw [abs_le] at h
  linarith

/-- Logarithm of the finite rational correction. -/
def finiteCoefficientLogCorrection (k n : ℕ) : ℝ :=
  Real.log ((k : ℝ) / ((k : ℝ) - 1)) +
    ∑ r ∈ Finset.Icc 2 n,
      Real.log
        (((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1))

/-- Remainder after extracting the universal leading exponent `3n²/k`. -/
def finiteCoefficientLogRemainder (k n : ℕ) : ℝ :=
  finiteCoefficientLogCorrection k n -
    3 * (n : ℝ) ^ 2 / (k : ℝ)

def finiteCoefficientLinearizedCorrection (k n : ℕ) : ℝ :=
  1 / ((k : ℝ) - 1) +
    ∑ r ∈ Finset.Icc 2 n,
      (6 * (r : ℝ) - 3) /
        ((k : ℝ) - 4 * (r : ℝ) + 1)

def finiteCoefficientQuadraticLogError (k n : ℕ) : ℝ :=
  (1 / ((k : ℝ) - 1)) ^ 2 / 2 +
    ∑ r ∈ Finset.Icc 2 n,
      (((6 * (r : ℝ) - 3) /
        ((k : ℝ) - 4 * (r : ℝ) + 1)) ^ 2 / 2)

/-- The exact log correction is trapped between its linearization and the
same linearization minus a quadratic error. -/
theorem finiteCoefficientLogCorrection_bounds
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    finiteCoefficientLinearizedCorrection k n -
        finiteCoefficientQuadraticLogError k n ≤
      finiteCoefficientLogCorrection k n ∧
    finiteCoefficientLogCorrection k n ≤
      finiteCoefficientLinearizedCorrection k n := by
  let y : ℝ := 1 / ((k : ℝ) - 1)
  let f : ℕ → ℝ := fun r ↦
    (6 * (r : ℝ) - 3) /
      ((k : ℝ) - 4 * (r : ℝ) + 1)
  have hy : 0 ≤ y := by
    dsimp [y]
    have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
    positivity
  have hf : ∀ r ∈ Finset.Icc 2 n, 0 ≤ f r := by
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    exact div_nonneg (by linarith) (shiftedDenominator_pos hkn hrn).le
  have hheadRewrite :
      (k : ℝ) / ((k : ℝ) - 1) = 1 + y := by
    dsimp [y]
    have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
    field_simp [ne_of_gt (by linarith : 0 < (k : ℝ) - 1)]
    ring
  have hfactorRewrite : ∀ r ∈ Finset.Icc 2 n,
      ((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1) = 1 + f r := by
    intro r hr
    have hrn := (Finset.mem_Icc.mp hr).2
    exact shiftedRatio_eq_one_add (shiftedDenominator_pos hkn hrn)
  have hlowerTerms :
      ∑ r ∈ Finset.Icc 2 n, (f r - (f r) ^ 2 / 2) ≤
        ∑ r ∈ Finset.Icc 2 n, Real.log (1 + f r) := by
    exact Finset.sum_le_sum fun r hr ↦ self_sub_half_sq_le_log_one_add (hf r hr)
  have hupperTerms :
      ∑ r ∈ Finset.Icc 2 n, Real.log (1 + f r) ≤
        ∑ r ∈ Finset.Icc 2 n, f r := by
    exact Finset.sum_le_sum fun r hr ↦ log_one_add_le_self (hf r hr)
  have hsumRewrite :
      (∑ r ∈ Finset.Icc 2 n,
        Real.log
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) =
        ∑ r ∈ Finset.Icc 2 n, Real.log (1 + f r) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [hfactorRewrite r hr]
  unfold finiteCoefficientLogCorrection finiteCoefficientLinearizedCorrection
    finiteCoefficientQuadraticLogError
  rw [hheadRewrite]
  rw [hsumRewrite]
  constructor
  · have h := add_le_add (self_sub_half_sq_le_log_one_add hy) hlowerTerms
    dsimp [y, f] at h
    rw [Finset.sum_sub_distrib] at h
    linarith
  · have h := add_le_add (log_one_add_le_self hy) hupperTerms
    dsimp [y, f] at h
    exact h

/-- Uniform cubic bound on the quadratic logarithmic error. -/
theorem finiteCoefficientQuadraticLogError_le
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    finiteCoefficientQuadraticLogError k n ≤
      19 * (n : ℝ) ^ 3 /
        (((k : ℝ) - 4 * (n : ℝ) + 1) ^ 2) := by
  let d : ℝ := (k : ℝ) - 4 * (n : ℝ) + 1
  have hd : 0 < d := by
    dsimp [d]
    exact shiftedDenominator_pos hkn le_rfl
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hy :
      0 ≤ 1 / ((k : ℝ) - 1) ∧
      1 / ((k : ℝ) - 1) ≤ 1 / d := by
    have hkm1 : 0 < (k : ℝ) - 1 := by
      have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
      linarith
    have horder : d ≤ (k : ℝ) - 1 := by
      dsimp [d]
      linarith
    exact ⟨by positivity, div_le_div_of_nonneg_left zero_le_one hd horder⟩
  have hterm : ∀ r ∈ Finset.Icc 2 n,
      (((6 * (r : ℝ) - 3) /
        ((k : ℝ) - 4 * (r : ℝ) + 1)) ^ 2 / 2) ≤
        18 * (n : ℝ) ^ 2 / d ^ 2 := by
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    have hrnR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
    have hden : 0 < (k : ℝ) - 4 * (r : ℝ) + 1 :=
      shiftedDenominator_pos hkn hrn
    have hnum : 0 ≤ 6 * (r : ℝ) - 3 := by linarith
    have hnumle : 6 * (r : ℝ) - 3 ≤ 6 * (n : ℝ) := by linarith
    have hdle : d ≤ (k : ℝ) - 4 * (r : ℝ) + 1 := by
      dsimp [d]
      linarith
    have hratio :
        (6 * (r : ℝ) - 3) /
            ((k : ℝ) - 4 * (r : ℝ) + 1) ≤
          6 * (n : ℝ) / d := by
      exact div_le_div₀ (by positivity) hnumle hd hdle
    have hratio0 : 0 ≤
        (6 * (r : ℝ) - 3) /
          ((k : ℝ) - 4 * (r : ℝ) + 1) :=
      div_nonneg hnum hden.le
    have hsq := sq_le_sq₀ hratio0 (by positivity) |>.mpr hratio
    calc
      (((6 * (r : ℝ) - 3) /
          ((k : ℝ) - 4 * (r : ℝ) + 1)) ^ 2 / 2) ≤
          (6 * (n : ℝ) / d) ^ 2 / 2 := by gcongr
      _ = 18 * (n : ℝ) ^ 2 / d ^ 2 := by ring
  have hcard : ((Finset.Icc 2 n).card : ℝ) ≤ (n : ℝ) := by
    rw [Nat.card_Icc]
    norm_num
  have hheadSq :
      (1 / ((k : ℝ) - 1)) ^ 2 / 2 ≤ (1 / d) ^ 2 / 2 := by
    have hs := (sq_le_sq₀ hy.1 (by positivity)).2 hy.2
    linarith
  unfold finiteCoefficientQuadraticLogError
  calc
    (1 / ((k : ℝ) - 1)) ^ 2 / 2 +
          ∑ r ∈ Finset.Icc 2 n,
            (((6 * (r : ℝ) - 3) /
              ((k : ℝ) - 4 * (r : ℝ) + 1)) ^ 2 / 2) ≤
        (1 / d) ^ 2 / 2 +
          ∑ _r ∈ Finset.Icc 2 n, 18 * (n : ℝ) ^ 2 / d ^ 2 := by
      exact add_le_add hheadSq (Finset.sum_le_sum hterm)
    _ = (1 / d) ^ 2 / 2 +
        ((Finset.Icc 2 n).card : ℝ) * (18 * (n : ℝ) ^ 2 / d ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / d) ^ 2 / 2 +
        (n : ℝ) * (18 * (n : ℝ) ^ 2 / d ^ 2) := by
      gcongr
    _ ≤ 19 * (n : ℝ) ^ 3 / d ^ 2 := by
      have hfac :
          0 ≤ ((n : ℝ) - 1) *
            ((n : ℝ) ^ 2 + (n : ℝ) + 1) := by positivity
      have hn3 : 1 ≤ (n : ℝ) ^ 3 := by
        nlinarith [hfac]
      field_simp [hd.ne']
      nlinarith

/-- The leading term `(3n²-2)/k` is below the exact linearized correction. -/
theorem leadingAnticoncentrationExponent_le_linearized
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    (3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) ≤
      finiteCoefficientLinearizedCorrection k n := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hhead : 1 / (k : ℝ) ≤ 1 / ((k : ℝ) - 1) := by
    have hkm1 : 0 < (k : ℝ) - 1 := by
      have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
      linarith
    exact div_le_div_of_nonneg_left zero_le_one hkm1 (by linarith)
  have hterm : ∀ r ∈ Finset.Icc 2 n,
      (6 * (r : ℝ) - 3) / (k : ℝ) ≤
        (6 * (r : ℝ) - 3) /
          ((k : ℝ) - 4 * (r : ℝ) + 1) := by
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    have hnum : 0 ≤ 6 * (r : ℝ) - 3 := by linarith
    have hden := shiftedDenominator_pos hkn hrn
    exact div_le_div_of_nonneg_left hnum hden (by linarith)
  unfold finiteCoefficientLinearizedCorrection
  calc
    (3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) =
        1 / (k : ℝ) +
          ∑ r ∈ Finset.Icc 2 n,
            (6 * (r : ℝ) - 3) / (k : ℝ) := by
      rw [← Finset.sum_div, sum_Icc_two_six_mul_sub_three n hn]
      ring
    _ ≤ 1 / ((k : ℝ) - 1) +
          ∑ r ∈ Finset.Icc 2 n,
            (6 * (r : ℝ) - 3) /
              ((k : ℝ) - 4 * (r : ℝ) + 1) :=
      add_le_add hhead (Finset.sum_le_sum hterm)

/-- Explicit envelope for the logarithmic remainder. -/
def finiteCoefficientRemainderEnvelope (k n : ℕ) : ℝ :=
  2 / (k : ℝ) +
    9 * (n : ℝ) ^ 3 /
      ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) +
    19 * (n : ℝ) ^ 3 /
      (((k : ℝ) - 4 * (n : ℝ) + 1) ^ 2)

/-- Quantitative two-sided bound behind the manuscript's `o_D(1)`. -/
theorem abs_finiteCoefficientLogRemainder_le
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    |finiteCoefficientLogRemainder k n| ≤
      finiteCoefficientRemainderEnvelope k n := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hd : 0 < (k : ℝ) - 4 * (n : ℝ) + 1 :=
    shiftedDenominator_pos hkn le_rfl
  obtain ⟨hlogLower, hlogUpper⟩ :=
    finiteCoefficientLogCorrection_bounds hn hkn
  have hlinearLower := leadingAnticoncentrationExponent_le_linearized hn hkn
  have hlinearUpper := linearizedAnticoncentrationExponent_le_sharp hn hkn
  change finiteCoefficientLinearizedCorrection k n ≤
    (3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) +
      9 * (n : ℝ) ^ 3 /
        ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) at hlinearUpper
  have hleadEq :
      (3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) =
        3 * (n : ℝ) ^ 2 / (k : ℝ) - 2 / (k : ℝ) := by
    field_simp [hkpos.ne']
  rw [hleadEq] at hlinearLower hlinearUpper
  have hquad := finiteCoefficientQuadraticLogError_le hn hkn
  have hfiniteCorr :
      0 ≤ 9 * (n : ℝ) ^ 3 /
        ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) := by positivity
  have hquadEnvelope :
      0 ≤ 19 * (n : ℝ) ^ 3 /
        (((k : ℝ) - 4 * (n : ℝ) + 1) ^ 2) := by positivity
  have htwoOverK : 0 ≤ 2 / (k : ℝ) := by positivity
  have hRnonneg : 0 ≤ finiteCoefficientRemainderEnvelope k n := by
    unfold finiteCoefficientRemainderEnvelope
    positivity
  rw [abs_le]
  constructor
  · unfold finiteCoefficientLogRemainder
      finiteCoefficientRemainderEnvelope at *
    linarith
  · unfold finiteCoefficientLogRemainder
      finiteCoefficientRemainderEnvelope at *
    linarith

/-- Coarse large dimension form of the explicit envelope. -/
theorem finiteCoefficientRemainderEnvelope_le_largeDimension
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 8 * n ≤ k) :
    finiteCoefficientRemainderEnvelope k n ≤
      2 / (k : ℝ) + 94 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkR : 8 * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkn
  have hd : 0 < (k : ℝ) - 4 * (n : ℝ) + 1 := by nlinarith
  have hdhalf : (k : ℝ) / 2 ≤ (k : ℝ) - 4 * (n : ℝ) + 1 := by nlinarith
  have hsecond :
      9 * (n : ℝ) ^ 3 /
          ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) ≤
        18 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
    have hden : (k : ℝ) ^ 2 / 2 ≤
        (k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1) := by
      nlinarith
    have hdenpos : 0 < (k : ℝ) ^ 2 / 2 := by positivity
    calc
      9 * (n : ℝ) ^ 3 /
            ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) ≤
          9 * (n : ℝ) ^ 3 / ((k : ℝ) ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hden
      _ = 18 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2 := by ring
  have hthird :
      19 * (n : ℝ) ^ 3 /
          (((k : ℝ) - 4 * (n : ℝ) + 1) ^ 2) ≤
        76 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2 := by
    have hsquares : (k : ℝ) ^ 2 / 4 ≤
        ((k : ℝ) - 4 * (n : ℝ) + 1) ^ 2 := by
      have hs := (sq_le_sq₀ (by positivity) hd.le).2 hdhalf
      nlinarith
    have hdenpos : 0 < (k : ℝ) ^ 2 / 4 := by positivity
    calc
      19 * (n : ℝ) ^ 3 /
            (((k : ℝ) - 4 * (n : ℝ) + 1) ^ 2) ≤
          19 * (n : ℝ) ^ 3 / ((k : ℝ) ^ 2 / 4) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hsquares
      _ = 76 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2 := by ring
  unfold finiteCoefficientRemainderEnvelope
  calc
    2 / (k : ℝ) +
          9 * (n : ℝ) ^ 3 /
            ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)) +
          19 * (n : ℝ) ^ 3 /
            (((k : ℝ) - 4 * (n : ℝ) + 1) ^ 2) ≤
        2 / (k : ℝ) + 18 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2 +
          76 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2 := by linarith
    _ = 2 / (k : ℝ) + 94 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2 := by ring

/-- The explicit remainder tends to zero whenever `k→∞` and `n³/k²→0`. -/
theorem tendsto_finiteCoefficientLogRemainder_of_growth
    (kseq : ℕ → ℕ)
    (hk8 : ∀ᶠ n : ℕ in atTop, 8 * n ≤ kseq n)
    (hkTop : Tendsto kseq atTop atTop)
    (hcubic : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 3 / (kseq n : ℝ) ^ 2)
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ finiteCoefficientLogRemainder (kseq n) n)
      atTop (nhds 0) := by
  have hkCast : Tendsto (fun n : ℕ ↦ (kseq n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hkTop
  have hinv : Tendsto (fun n : ℕ ↦ 2 / (kseq n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hkCast
  have henv : Tendsto
      (fun n : ℕ ↦ 2 / (kseq n : ℝ) +
        94 * (n : ℝ) ^ 3 / (kseq n : ℝ) ^ 2)
      atTop (nhds 0) := by
    simpa [mul_div_assoc] using hinv.add (tendsto_const_nhds.mul hcubic)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · filter_upwards [hk8] with n hkn
    exact abs_nonneg _
  · filter_upwards [hk8, eventually_ge_atTop 1] with n hkn hn
    calc
      ‖finiteCoefficientLogRemainder (kseq n) n‖ =
          |finiteCoefficientLogRemainder (kseq n) n| := Real.norm_eq_abs _
      _ ≤ finiteCoefficientRemainderEnvelope (kseq n) n :=
        abs_finiteCoefficientLogRemainder_le hn (by omega)
      _ ≤ 2 / (kseq n : ℝ) +
          94 * (n : ℝ) ^ 3 / (kseq n : ℝ) ^ 2 :=
        finiteCoefficientRemainderEnvelope_le_largeDimension hn hkn
  · exact henv

/-- The manuscript's logarithmic dimension regime forces the cubic error
scale `n³/k_n²` to vanish. -/
theorem tendsto_cubic_dimension_ratio_of_log_scale
    (kseq : ℕ → ℕ) {D : ℝ} (hD : 0 < D)
    (hkpos : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 3 / (kseq n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ (1 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (show 0 < (1 : ℝ) by norm_num)).tendsto_div_nhds_zero
  have hlogsq : Tendsto
      (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
    convert hreal.comp tendsto_natCast_atTop_atTop using 1
    ext n
    simp only [Function.comp_apply, Real.rpow_two, Real.rpow_one]
  have hmajor : Tendsto
      (fun n : ℕ ↦ D ^ 2 *
        ((Real.log (n : ℝ)) ^ 2 / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlogsq
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [hkpos, hscale, eventually_ge_atTop 2]
      with n hkn hs hn
    have hkR : 0 < (kseq n : ℝ) := by exact_mod_cast hkn
    have hnR : 0 < (n : ℝ) := by positivity
    have hleft : 0 ≤ (n : ℝ) ^ 2 / (kseq n : ℝ) := by positivity
    have hright : 0 ≤ D * Real.log (n : ℝ) := hleft.trans hs
    have hsq :
        ((n : ℝ) ^ 2 / (kseq n : ℝ)) ^ 2 ≤
          (D * Real.log (n : ℝ)) ^ 2 :=
      (sq_le_sq₀ hleft hright).2 hs
    calc
      ‖(n : ℝ) ^ 3 / (kseq n : ℝ) ^ 2‖ =
          (n : ℝ) ^ 3 / (kseq n : ℝ) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ = (((n : ℝ) ^ 2 / (kseq n : ℝ)) ^ 2) / (n : ℝ) := by
        field_simp [hkR.ne', hnR.ne']
      _ ≤ (D * Real.log (n : ℝ)) ^ 2 / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hsq hnR.le
      _ = D ^ 2 * ((Real.log (n : ℝ)) ^ 2 / (n : ℝ)) := by ring
  · exact hmajor

/-- In the logarithmic regime, the exact logarithmic remainder is `o(1)`. -/
theorem tendsto_finiteCoefficientLogRemainder_of_log_scale
    (kseq : ℕ → ℕ) {D : ℝ} (hD : 0 < D)
    (hkpos : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    Tendsto
      (fun n : ℕ ↦ finiteCoefficientLogRemainder (kseq n) n)
      atTop (nhds 0) := by
  have hk8 := eventually_eight_mul_le_of_log_scale kseq hD hkpos hscale
  have hkTop : Tendsto kseq atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hk8, eventually_ge_atTop b] with n hkn hnb
    omega
  exact tendsto_finiteCoefficientLogRemainder_of_growth kseq hk8 hkTop
    (tendsto_cubic_dimension_ratio_of_log_scale kseq hD hkpos hscale)

/-- The Gamma prefactor has its expected square root asymptotic. -/
theorem limitingAnticoncentrationConstant_ratio_tendsto_one :
    Tendsto
      (fun n : ℕ ↦ limitingAnticoncentrationConstant n /
        (2 * Real.sqrt (n : ℝ) / Real.sqrt Real.pi))
      atTop (nhds 1) := by
  have htwoTop : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hscale : Tendsto
      (fun n : ℕ ↦ LogdetLean.Coherence.gammaHalfRatioScale (n : ℝ))
      atTop (nhds 1) := by
    have h := LogdetLean.Coherence.tendsto_gammaHalfRatioScale_nat_half.comp htwoTop
    convert h using 1
    ext n
    simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat]
    congr 1
    ring
  have hinv : Tendsto
      (fun n : ℕ ↦
        (LogdetLean.Coherence.gammaHalfRatioScale (n : ℝ))⁻¹)
      atTop (nhds 1) := by
    simpa using hscale.inv₀ one_ne_zero
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold limitingAnticoncentrationConstant
    LogdetLean.Coherence.gammaHalfRatioScale
  have hnR : 0 < (n : ℝ) := by positivity
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hGn : Real.Gamma (n : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos hnR).ne'
  have hGhalf : Real.Gamma ((n : ℝ) + 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp [hsqrtn, hsqrtpi, hGn, hGhalf]

theorem limitingAnticoncentrationConstant_le_two_sqrt (n : ℕ) (hn : 1 ≤ n) :
    limitingAnticoncentrationConstant n ≤ 2 * Real.sqrt (n : ℝ) := by
  rw [limitingAnticoncentrationConstant_eq_centralBinomial n hn]
  exact centralBinomial_prefactor_le_two_sqrt n

/-- Exact coefficient bridge: the finite coefficient is its limiting Gamma
prefactor times the exponential of the leading term and an explicit
logarithmic remainder. -/
theorem shiftedAnticoncentrationConstant_eq_limit_mul_exp
    {k n : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    shiftedAnticoncentrationConstant k n =
      limitingAnticoncentrationConstant n *
        Real.exp
          (3 * (n : ℝ) ^ 2 / (k : ℝ) +
            finiteCoefficientLogRemainder k n) := by
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hhead : 0 < (k : ℝ) / ((k : ℝ) - 1) :=
    div_pos (by positivity) (by linarith)
  have hfactor : ∀ r ∈ Finset.Icc 2 n,
      0 < ((k : ℝ) + 2 * (r : ℝ) - 2) /
        ((k : ℝ) - 4 * (r : ℝ) + 1) := by
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    have hrn := (Finset.mem_Icc.mp hr).2
    have hden := shiftedDenominator_pos hkn hrn
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    have hnum : 0 < (k : ℝ) + 2 * (r : ℝ) - 2 := by
      have hkpos : 0 < (k : ℝ) := by positivity
      linarith
    exact div_pos hnum hden
  have hexp :
      Real.exp (finiteCoefficientLogCorrection k n) =
        ((k : ℝ) / ((k : ℝ) - 1)) *
          ∏ r ∈ Finset.Icc 2 n,
            (((k : ℝ) + 2 * (r : ℝ) - 2) /
              ((k : ℝ) - 4 * (r : ℝ) + 1)) := by
    unfold finiteCoefficientLogCorrection
    rw [Real.exp_add, Real.exp_log hhead, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro r hr
    rw [Real.exp_log (hfactor r hr)]
  rw [shiftedAnticoncentrationConstant]
  rw [← limitingAnticoncentrationConstant_eq_centralBinomial n hn]
  rw [mul_assoc]
  rw [← hexp]
  unfold finiteCoefficientLogRemainder
  congr 1
  congr 1
  ring

/-- Finite sharp polynomial form, parameterized by the already small
logarithmic remainder. -/
theorem gaussianGramHafnianShiftedAnticoncentration_polynomial_sharp_finite
    {n k : ℕ} {A D beta : ℝ}
    (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (hscale : (n : ℝ) ^ 2 / (k : ℝ) ≤ D * Real.log (n : ℝ))
    (hremainder : finiteCoefficientLogRemainder k n ≤ 1)
    (hconstant :
      2 * Real.exp 1 ≤
        (n : ℝ) ^ (2 * beta - A - 3 * D - (1 / 2 : ℝ))) :
    ∀ z : ℂ,
      gramHafnianShiftedSmallBallProbability k n z
          ((n : ℝ) ^ (-beta)) ≤
        (n : ℝ) ^ (-A) := by
  intro z
  have hnpos : 0 < (n : ℝ) := by positivity
  have heps : 0 ≤ (n : ℝ) ^ (-beta) := Real.rpow_nonneg hnpos.le _
  have hexponent :
      3 * (n : ℝ) ^ 2 / (k : ℝ) +
          finiteCoefficientLogRemainder k n ≤
        3 * D * Real.log (n : ℝ) + 1 := by
    have hthree := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 3)
    calc
      3 * (n : ℝ) ^ 2 / (k : ℝ) +
            finiteCoefficientLogRemainder k n =
          3 * ((n : ℝ) ^ 2 / (k : ℝ)) +
            finiteCoefficientLogRemainder k n := by ring
      _ ≤ 3 * (D * Real.log (n : ℝ)) + 1 :=
        add_le_add hthree hremainder
      _ = 3 * D * Real.log (n : ℝ) + 1 := by ring
  have hepssq :
      ((n : ℝ) ^ (-beta)) ^ 2 = (n : ℝ) ^ (-2 * beta) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hnpos.le]
    congr 1
    ring
  have hexplog :
      Real.exp (3 * D * Real.log (n : ℝ)) =
        (n : ℝ) ^ (3 * D) := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hsimplify :
      (2 * Real.sqrt (n : ℝ) *
          Real.exp (3 * D * Real.log (n : ℝ) + 1)) *
          ((n : ℝ) ^ (-beta)) ^ 2 =
        (2 * Real.exp 1) *
          (n : ℝ) ^ ((1 / 2 : ℝ) + 3 * D - 2 * beta) := by
    rw [Real.sqrt_eq_rpow, Real.exp_add, hexplog, hepssq]
    calc
      2 * (n : ℝ) ^ (1 / 2 : ℝ) *
            ((n : ℝ) ^ (3 * D) * Real.exp 1) *
            (n : ℝ) ^ (-2 * beta) =
          (2 * Real.exp 1) *
            (((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 * D)) *
              (n : ℝ) ^ (-2 * beta)) := by ring
      _ = (2 * Real.exp 1) *
            ((n : ℝ) ^ ((1 / 2 : ℝ) + 3 * D) *
              (n : ℝ) ^ (-2 * beta)) := by
        rw [Real.rpow_add hnpos]
      _ = (2 * Real.exp 1) *
            (n : ℝ) ^ ((1 / 2 : ℝ) + 3 * D - 2 * beta) := by
        rw [← Real.rpow_add hnpos]
        congr 2
        ring
  have hmarginNonneg :
      0 ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + 3 * D - 2 * beta) :=
    Real.rpow_nonneg hnpos.le _
  have habsorb := mul_le_mul_of_nonneg_right hconstant hmarginNonneg
  have habsorb' :
      (2 * Real.exp 1) *
          (n : ℝ) ^ ((1 / 2 : ℝ) + 3 * D - 2 * beta) ≤
        (n : ℝ) ^ (-A) := by
    calc
      (2 * Real.exp 1) *
            (n : ℝ) ^ ((1 / 2 : ℝ) + 3 * D - 2 * beta) ≤
          (n : ℝ) ^ (2 * beta - A - 3 * D - (1 / 2 : ℝ)) *
            (n : ℝ) ^ ((1 / 2 : ℝ) + 3 * D - 2 * beta) := habsorb
      _ = (n : ℝ) ^
          ((2 * beta - A - 3 * D - (1 / 2 : ℝ)) +
            ((1 / 2 : ℝ) + 3 * D - 2 * beta)) := by
        rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (-A) := by congr 1 <;> ring
  calc
    gramHafnianShiftedSmallBallProbability k n z
          ((n : ℝ) ^ (-beta)) ≤
        shiftedAnticoncentrationConstant k n *
          ((n : ℝ) ^ (-beta)) ^ 2 :=
      gaussianGramHafnianShiftedAnticoncentration
        n k hn hkn z ((n : ℝ) ^ (-beta)) heps
    _ = (limitingAnticoncentrationConstant n *
          Real.exp
            (3 * (n : ℝ) ^ 2 / (k : ℝ) +
              finiteCoefficientLogRemainder k n)) *
          ((n : ℝ) ^ (-beta)) ^ 2 := by
      rw [shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hkn]
    _ ≤ (2 * Real.sqrt (n : ℝ) *
          Real.exp (3 * D * Real.log (n : ℝ) + 1)) *
          ((n : ℝ) ^ (-beta)) ^ 2 := by
      gcongr
      exact limitingAnticoncentrationConstant_le_two_sqrt n hn
    _ = (2 * Real.exp 1) *
          (n : ℝ) ^ ((1 / 2 : ℝ) + 3 * D - 2 * beta) := hsimplify
    _ ≤ (n : ℝ) ^ (-A) := habsorb'

/-- Improved polynomial small ball theorem with the sharp leading `3D`
loss. -/
theorem gaussianGramHafnianShiftedAnticoncentration_polynomial_sharp
    (kseq : ℕ → ℕ) {A D beta : ℝ}
    (_hA : 0 < A) (hD : 0 < D)
    (hbeta : (A + 3 * D + (1 / 2 : ℝ)) / 2 < beta)
    (hkpos : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ,
      gramHafnianShiftedSmallBallProbability (kseq n) n z
          ((n : ℝ) ^ (-beta)) ≤
        (n : ℝ) ^ (-A) := by
  have hmargin : 0 < 2 * beta - A - 3 * D - (1 / 2 : ℝ) := by linarith
  have hconstant : ∀ᶠ n : ℕ in atTop,
      2 * Real.exp 1 ≤
        (n : ℝ) ^ (2 * beta - A - 3 * D - (1 / 2 : ℝ)) :=
    ((tendsto_rpow_atTop hmargin).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 * Real.exp 1))
  have hk8 := eventually_eight_mul_le_of_log_scale kseq hD hkpos hscale
  have hremT := tendsto_finiteCoefficientLogRemainder_of_log_scale
    kseq hD hkpos hscale
  have hrem : ∀ᶠ n : ℕ in atTop,
      finiteCoefficientLogRemainder (kseq n) n ≤ 1 :=
    hremT.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hscale, hk8, hconstant, hrem, eventually_ge_atTop 1]
    with n hs hk hc hr hn
  exact gaussianGramHafnianShiftedAnticoncentration_polynomial_sharp_finite
    hn (by omega) hs hr hc

/-- At every fixed hafnian degree, the finite coefficient converges to the
Gamma prefactor `b_n` as the Gram dimension tends to infinity. -/
theorem tendsto_shiftedAnticoncentrationConstant_fixed_degree
    (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun k : ℕ ↦ shiftedAnticoncentrationConstant k n)
      atTop (nhds (limitingAnticoncentrationConstant n)) := by
  have hhead : Tendsto
      (fun k : ℕ ↦ (k : ℝ) / ((k : ℝ) - 1))
      atTop (nhds 1) := by
    convert tendsto_add_mul_div_add_mul_atTop_nhds
      (0 : ℝ) (-1 : ℝ) (1 : ℝ) one_ne_zero using 1
    · ext k
      push_cast
      ring
    · norm_num
  have hfactor : ∀ r : ℕ, Tendsto
      (fun k : ℕ ↦
        ((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1))
      atTop (nhds 1) := by
    intro r
    convert tendsto_add_mul_div_add_mul_atTop_nhds
      (2 * (r : ℝ) - 2) (1 - 4 * (r : ℝ)) (1 : ℝ) one_ne_zero using 1
    · ext k
      push_cast
      ring
    · norm_num
  have hprod : Tendsto
      (fun k : ℕ ↦ ∏ r ∈ Finset.Icc 2 n,
        (((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1)))
      atTop (nhds 1) := by
    simpa using tendsto_finsetProd (Finset.Icc 2 n)
      (fun r _ ↦ hfactor r)
  have hall : Tendsto
      (fun k : ℕ ↦ limitingAnticoncentrationConstant n *
        (((k : ℝ) / ((k : ℝ) - 1)) *
          ∏ r ∈ Finset.Icc 2 n,
            (((k : ℝ) + 2 * (r : ℝ) - 2) /
              ((k : ℝ) - 4 * (r : ℝ) + 1))))
      atTop (nhds (limitingAnticoncentrationConstant n * (1 * 1))) :=
    tendsto_const_nhds.mul (hhead.mul hprod)
  simp only [mul_one] at hall
  apply hall.congr'
  filter_upwards [eventually_ge_atTop (4 * n)] with k hk
  rw [shiftedAnticoncentrationConstant]
  rw [← limitingAnticoncentrationConstant_eq_centralBinomial n hn]
  ring

end

end LogdetLean.GramHafnian.CurrentPRL
