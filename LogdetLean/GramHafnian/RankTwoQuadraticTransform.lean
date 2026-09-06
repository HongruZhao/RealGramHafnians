import LogdetLean.GramHafnian.RankTwoCentralBinomial
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Vandermonde
/-!
# The quadratic transform behind the rank-two Gaussian moment

This file proves, by finite polynomial algebra, the classical quadratic
transformation which converts the central-binomial eigenvalue convolution
into the squared-binomial invariant formula.  No analytic generating
function or special-function identity is assumed.
-/

open scoped BigOperators
open Finset Polynomial

namespace LogdetLean.GramHafnian

noncomputable section

/-- The homogeneous squared-binomial polynomial, represented as a polynomial
in its first variable. -/
def squaredChooseHomPolynomial (n : Nat) (v : Real) : Real[X] :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (((n.choose j : Nat) : Real) ^ 2 * v ^ (n - j)) *
      Polynomial.X ^ j

theorem coeff_squaredChooseHomPolynomial (n j : Nat) (v : Real) :
    (squaredChooseHomPolynomial n v).coeff j =
      ((n.choose j : Nat) : Real) ^ 2 * v ^ (n - j) := by
  rw [squaredChooseHomPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hj : j ≤ n
  · rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro b hb hbj
      simp [Ne.symm hbj]
    · simp [hj]
  · have hjlt : n < j := Nat.lt_of_not_ge hj
    have hchoose : n.choose j = 0 := Nat.choose_eq_zero_of_lt hjlt
    have hrhs :
        ((n.choose j : Nat) : Real) ^ 2 * v ^ (n - j) = 0 := by
      rw [hchoose]
      norm_num
    rw [hrhs]
    apply Finset.sum_eq_zero
    intro b hb
    have hbj : j ≠ b := by
      intro h
      subst b
      exact hj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
    rw [if_neg hbj]

theorem eval_squaredChooseHomPolynomial (n : Nat) (u v : Real) :
    (squaredChooseHomPolynomial n v).eval u =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : Nat) : Real) ^ 2 * u ^ j * v ^ (n - j) := by
  rw [squaredChooseHomPolynomial, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- The interior coefficient identity underlying the three-term recurrence
of the squared-binomial polynomials. -/
theorem squared_choose_coefficient_recurrence_interior
    (N j : Nat) (hj2 : 2 ≤ j) (hjtop : j ≤ N + 1) :
    ((N + 2 : Nat) : Real) * (((N + 2).choose j : Nat) : Real) ^ 2 =
      ((2 * N + 3 : Nat) : Real) *
          ((((N + 1).choose j : Nat) : Real) ^ 2 +
            (((N + 1).choose (j - 1) : Nat) : Real) ^ 2) -
        ((N + 1 : Nat) : Real) *
          ((((N.choose j : Nat) : Real) ^ 2 -
              2 * ((N.choose (j - 1) : Nat) : Real) ^ 2) +
            ((N.choose (j - 2) : Nat) : Real) ^ 2) := by
  let a : Real := ((N.choose j : Nat) : Real)
  let b : Real := ((N.choose (j - 1) : Nat) : Real)
  let c : Real := ((N.choose (j - 2) : Nat) : Real)
  have hj1 : 1 ≤ j := by omega
  have hjm1 : j - 1 + 1 = j := by omega
  have hjm2 : j - 2 + 1 = j - 1 := by omega
  have hpascal1Nat :
      (N + 1).choose j = N.choose (j - 1) + N.choose j := by
    have h := Nat.choose_succ_succ' N (j - 1)
    rw [hjm1] at h
    exact h
  have hpascal0Nat :
      (N + 1).choose (j - 1) =
        N.choose (j - 2) + N.choose (j - 1) := by
    have h := Nat.choose_succ_succ' N (j - 2)
    rw [hjm2] at h
    exact h
  have hpascal2Nat :
      (N + 2).choose j =
        (N + 1).choose (j - 1) + (N + 1).choose j := by
    have h := Nat.choose_succ_succ' (N + 1) (j - 1)
    rw [hjm1] at h
    simpa only [Nat.add_assoc] using h
  have hpascal1 :
      (((N + 1).choose j : Nat) : Real) = b + a := by
    dsimp [a, b]
    exact_mod_cast hpascal1Nat
  have hpascal0 :
      (((N + 1).choose (j - 1) : Nat) : Real) = c + b := by
    dsimp [b, c]
    exact_mod_cast hpascal0Nat
  have hpascal2 :
      (((N + 2).choose j : Nat) : Real) = c + 2 * b + a := by
    have h :
        (((N + 2).choose j : Nat) : Real) =
          (((N + 1).choose (j - 1) : Nat) : Real) +
            (((N + 1).choose j : Nat) : Real) := by
      exact_mod_cast hpascal2Nat
    rw [h, hpascal0, hpascal1]
    ring
  have haNat :
      N.choose j * j = N.choose (j - 1) * (N + 1 - j) := by
    have h := Nat.choose_succ_right_eq N (j - 1)
    rw [hjm1, show N - (j - 1) = N + 1 - j by omega] at h
    exact h
  have hcNat :
      N.choose (j - 2) * (N + 2 - j) =
        N.choose (j - 1) * (j - 1) := by
    have h := Nat.choose_succ_right_eq N (j - 2)
    rw [hjm2, show N - (j - 2) = N + 2 - j by omega] at h
    exact h.symm
  have ha : (j : Real) * a = ((N + 1 - j : Nat) : Real) * b := by
    have h : a * (j : Real) = b * ((N + 1 - j : Nat) : Real) := by
      dsimp [a, b]
      exact_mod_cast haNat
    simpa [mul_comm] using h
  have hc : ((N + 2 - j : Nat) : Real) * c =
      ((j - 1 : Nat) : Real) * b := by
    have h :
        (((N.choose (j - 2) * (N + 2 - j) : Nat) : Real)) =
          (((N.choose (j - 1) * (j - 1) : Nat) : Real)) := by
      exact_mod_cast hcNat
    dsimp [b, c]
    simpa only [Nat.cast_mul, mul_comm] using h
  have hscalePos :
      0 < (j : Real) * ((N + 2 - j : Nat) : Real) := by
    have hdiff : 0 < N + 2 - j := by omega
    exact mul_pos (by positivity) (by exact_mod_cast hdiff)
  have hrelation : a * b + b * c + (N + 2 : Real) * a * c =
      (N : Real) * b ^ 2 := by
    have hmul :
        ((j : Real) * ((N + 2 - j : Nat) : Real)) *
            (a * b + b * c + (N + 2 : Real) * a * c -
              (N : Real) * b ^ 2) = 0 := by
      calc
        ((j : Real) * ((N + 2 - j : Nat) : Real)) *
              (a * b + b * c + (N + 2 : Real) * a * c -
                (N : Real) * b ^ 2) =
            ((j : Real) * a) * ((N + 2 - j : Nat) : Real) * b +
              (j : Real) * b * (((N + 2 - j : Nat) : Real) * c) +
              (N + 2 : Real) * ((j : Real) * a) *
                (((N + 2 - j : Nat) : Real) * c) -
              (N : Real) * b ^ 2 * (j : Real) *
                ((N + 2 - j : Nat) : Real) := by ring
        _ = (((N + 1 - j : Nat) : Real) * b) *
                ((N + 2 - j : Nat) : Real) * b +
              (j : Real) * b * (((j - 1 : Nat) : Real) * b) +
              (N + 2 : Real) * (((N + 1 - j : Nat) : Real) * b) *
                (((j - 1 : Nat) : Real) * b) -
              (N : Real) * b ^ 2 * (j : Real) *
                ((N + 2 - j : Nat) : Real) := by rw [ha, hc]
        _ = 0 := by
          rw [Nat.cast_sub hjtop, Nat.cast_sub (by omega : j ≤ N + 2),
            Nat.cast_sub hj1]
          push_cast
          ring
    have hzero := (mul_eq_zero.mp hmul).resolve_left hscalePos.ne'
    linarith
  rw [hpascal2, hpascal1, hpascal0]
  dsimp [a, b, c] at hrelation ⊢
  push_cast at hrelation ⊢
  linear_combination 2 * hrelation

theorem coeff_X_add_C_mul_squaredChooseHomPolynomial
    (n j : Nat) (v : Real) :
    ((Polynomial.X + Polynomial.C v) *
        squaredChooseHomPolynomial n v).coeff j =
      (if 1 ≤ j then
          ((n.choose (j - 1) : Nat) : Real) ^ 2 *
            v ^ (n - (j - 1))
        else 0) +
        v * (((n.choose j : Nat) : Real) ^ 2 * v ^ (n - j)) := by
  rw [add_mul, coeff_add, show Polynomial.X = Polynomial.X ^ 1 by simp,
    coeff_X_pow_mul', coeff_C_mul, coeff_squaredChooseHomPolynomial,
    coeff_squaredChooseHomPolynomial]

theorem coeff_X_sub_C_sq_mul_squaredChooseHomPolynomial
    (n j : Nat) (v : Real) :
    (((Polynomial.X - Polynomial.C v) ^ 2) *
        squaredChooseHomPolynomial n v).coeff j =
      (if 2 ≤ j then
          ((n.choose (j - 2) : Nat) : Real) ^ 2 *
            v ^ (n - (j - 2))
        else 0) -
        2 * v *
          (if 1 ≤ j then
              ((n.choose (j - 1) : Nat) : Real) ^ 2 *
                v ^ (n - (j - 1))
            else 0) +
        v ^ 2 * (((n.choose j : Nat) : Real) ^ 2 * v ^ (n - j)) := by
  have hexpand :
      (Polynomial.X - Polynomial.C v : Real[X]) ^ 2 =
        Polynomial.X ^ 2 - Polynomial.C (2 * v) * Polynomial.X +
          Polynomial.C (v ^ 2) := by
    rw [C_mul, C_pow]
    rw [C_ofNat]
    ring
  have hX :
      (Polynomial.X * squaredChooseHomPolynomial n v).coeff j =
        if 1 ≤ j then
          (squaredChooseHomPolynomial n v).coeff (j - 1) else 0 := by
    simpa only [pow_one] using
      (Polynomial.coeff_X_pow_mul' (squaredChooseHomPolynomial n v) 1 j)
  rw [hexpand, add_mul, sub_mul, coeff_add, coeff_sub, mul_assoc,
    coeff_C_mul, coeff_X_pow_mul', hX, coeff_C_mul,
    coeff_squaredChooseHomPolynomial, coeff_squaredChooseHomPolynomial,
    coeff_squaredChooseHomPolynomial]

/-- Three-term recurrence for the homogeneous squared-binomial polynomial. -/
theorem squaredChooseHomPolynomial_recurrence (N : Nat) (v : Real) :
    Polynomial.C ((N + 2 : Nat) : Real) *
        squaredChooseHomPolynomial (N + 2) v =
      Polynomial.C ((2 * N + 3 : Nat) : Real) *
          (Polynomial.X + Polynomial.C v) *
            squaredChooseHomPolynomial (N + 1) v -
        Polynomial.C ((N + 1 : Nat) : Real) *
          (Polynomial.X - Polynomial.C v) ^ 2 *
            squaredChooseHomPolynomial N v := by
  ext j
  rw [coeff_C_mul, coeff_sub, mul_assoc, coeff_C_mul,
    coeff_X_add_C_mul_squaredChooseHomPolynomial, mul_assoc,
    coeff_C_mul, coeff_X_sub_C_sq_mul_squaredChooseHomPolynomial,
    coeff_squaredChooseHomPolynomial]
  by_cases hjtop : j ≤ N + 2
  · cases j with
    | zero =>
        simp only [Nat.choose_zero_right, Nat.cast_one, one_pow, Nat.sub_zero,
          if_false, zero_add, one_mul]
        push_cast
        simp only [pow_succ]
        ring
    | succ j0 =>
      cases j0 with
      | zero =>
          cases N with
          | zero => norm_num <;> ring
          | succ N =>
              simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one,
                Nat.add_sub_cancel, Nat.reduceLeDiff, if_true, Nat.sub_zero,
                Nat.cast_mul]
              simp only [pow_succ]
              push_cast
              simp_rw [Nat.choose_one_right, Nat.choose_zero_right]
              push_cast
              ring
      | succ j0 =>
        set j : Nat := j0 + 2 with hjdef
        have hj2 : 2 ≤ j := by omega
        simp only [if_pos hj2, if_pos (by omega : 1 ≤ j)]
        by_cases hjN : j ≤ N
        · have hrec := squared_choose_coefficient_recurrence_interior
              N j hj2 (by omega : j ≤ N + 1)
          rw [show N + 2 - j = (N - j) + 2 by omega,
            show N + 1 - (j - 1) = (N - j) + 2 by omega,
            show N + 1 - j = (N - j) + 1 by omega,
            show N - (j - 2) = (N - j) + 2 by omega,
            show N - (j - 1) = (N - j) + 1 by omega]
          simp only [pow_add, pow_one, pow_two]
          push_cast at hrec ⊢
          linear_combination (v ^ (N - j) * v ^ 2) * hrec
        · have hjCases : j = N + 1 ∨ j = N + 2 := by omega
          rcases hjCases with hjEq | hjEq
          · have hrec := squared_choose_coefficient_recurrence_interior
                N j hj2 (by omega : j ≤ N + 1)
            have hqzero : N.choose j = 0 :=
              Nat.choose_eq_zero_of_lt (by omega)
            rw [hqzero] at hrec ⊢
            norm_num only [Nat.cast_zero, zero_pow, OfNat.ofNat_ne_zero,
              pow_eq_zero_iff, or_false, zero_mul, add_zero] at hrec ⊢
            rw [show N + 2 - j = 1 by omega,
              show N + 1 - (j - 1) = 1 by omega,
              show N + 1 - j = 0 by omega,
              show N - (j - 2) = 1 by omega,
              show N - (j - 1) = 0 by omega]
            simp only [pow_one, pow_zero, mul_one]
            push_cast at hrec ⊢
            linear_combination v * hrec
          · have hj0Eq : j0 = N := by omega
            subst j0
            simp [hjdef, Nat.choose_eq_zero_of_lt, pow_succ]
            ring
  · have hjlt : N + 2 < j := Nat.lt_of_not_ge hjtop
    have h0 : (N + 2).choose j = 0 := Nat.choose_eq_zero_of_lt hjlt
    have h1 : (N + 1).choose j = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have h1' : (N + 1).choose (j - 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have h2 : N.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2' : N.choose (j - 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have h2'' : N.choose (j - 2) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [h0, h1, h1', h2, h2', h2'']
    norm_num

/-- The raw central-binomial convolution, homogeneous in two variables and
represented as a polynomial in the first one. -/
def centralBinomialHomPolynomial (n : Nat) (v : Real) : Real[X] :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.C
        (((Nat.centralBinom j : Nat) : Real) *
          ((Nat.centralBinom (n - j) : Nat) : Real) * v ^ (n - j)) *
      Polynomial.X ^ j

theorem coeff_centralBinomialHomPolynomial (n j : Nat) (v : Real) :
    (centralBinomialHomPolynomial n v).coeff j =
      if j ≤ n then
        ((Nat.centralBinom j : Nat) : Real) *
          ((Nat.centralBinom (n - j) : Nat) : Real) * v ^ (n - j)
      else 0 := by
  rw [centralBinomialHomPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hj : j ≤ n
  · rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, if_pos hj]
    · intro b hb hbj
      rw [if_neg (Ne.symm hbj)]
    · intro hjnot
      exact (hjnot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))).elim
  · have hjlt : n < j := Nat.lt_of_not_ge hj
    have hsum :
        (∑ b ∈ Finset.range (n + 1),
          if j = b then
            ((Nat.centralBinom b : Nat) : Real) *
              ((Nat.centralBinom (n - b) : Nat) : Real) * v ^ (n - b)
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg]
      intro h
      subst b
      exact hj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
    rw [hsum, if_neg hj]

theorem eval_centralBinomialHomPolynomial (n : Nat) (u v : Real) :
    (centralBinomialHomPolynomial n v).eval u =
      ∑ j ∈ Finset.range (n + 1),
        ((Nat.centralBinom j : Nat) : Real) *
          ((Nat.centralBinom (n - j) : Nat) : Real) *
            u ^ j * v ^ (n - j) := by
  rw [centralBinomialHomPolynomial, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- Interior coefficient recurrence for the raw central-binomial
convolution. -/
theorem centralBinomial_coefficient_recurrence_interior
    (N j : Nat) (hj1 : 1 ≤ j) (hjtop : j ≤ N + 1) :
    ((N + 2 : Nat) : Real) *
        ((Nat.centralBinom j : Nat) : Real) *
          ((Nat.centralBinom (N + 2 - j) : Nat) : Real) =
      2 * ((2 * N + 3 : Nat) : Real) *
          (((Nat.centralBinom (j - 1) : Nat) : Real) *
              ((Nat.centralBinom (N + 2 - j) : Nat) : Real) +
            ((Nat.centralBinom j : Nat) : Real) *
              ((Nat.centralBinom (N + 1 - j) : Nat) : Real)) -
        16 * ((N + 1 : Nat) : Real) *
          ((Nat.centralBinom (j - 1) : Nat) : Real) *
            ((Nat.centralBinom (N + 1 - j) : Nat) : Real) := by
  let bNat := N + 2 - j
  let A : Real := ((Nat.centralBinom j : Nat) : Real)
  let P : Real := ((Nat.centralBinom (j - 1) : Nat) : Real)
  let B : Real := ((Nat.centralBinom bNat : Nat) : Real)
  let Q : Real := ((Nat.centralBinom (bNat - 1) : Nat) : Real)
  have hbpos : 0 < bNat := by dsimp [bNat]; omega
  have hjpred : j - 1 + 1 = j := by omega
  have hbpred : bNat - 1 + 1 = bNat := by omega
  have hsum : j + bNat = N + 2 := by dsimp [bNat]; omega
  have hqIndex : bNat - 1 = N + 1 - j := by dsimp [bNat]; omega
  have hAjNat :
      j * Nat.centralBinom j =
        2 * (2 * (j - 1) + 1) * Nat.centralBinom (j - 1) := by
    have h := Nat.succ_mul_centralBinom_succ (j - 1)
    rw [hjpred] at h
    exact h
  have hBbNat :
      bNat * Nat.centralBinom bNat =
        2 * (2 * (bNat - 1) + 1) * Nat.centralBinom (bNat - 1) := by
    have h := Nat.succ_mul_centralBinom_succ (bNat - 1)
    rw [hbpred] at h
    exact h
  have hAj : (j : Real) * A = (4 * (j : Real) - 2) * P := by
    dsimp [A, P]
    have h :
        (((j * Nat.centralBinom j : Nat) : Real)) =
          (((2 * (2 * (j - 1) + 1) *
              Nat.centralBinom (j - 1) : Nat) : Real)) := by
      exact_mod_cast hAjNat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at h
    have hidx : (((2 * (j - 1) + 1 : Nat) : Real)) =
        2 * (j : Real) - 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hj1]
      push_cast
      ring
    rw [hidx] at h
    calc
      (j : Real) * ((Nat.centralBinom j : Nat) : Real) =
          2 * (2 * (j : Real) - 1) *
            ((Nat.centralBinom (j - 1) : Nat) : Real) := by simpa using h
      _ = (4 * (j : Real) - 2) *
            ((Nat.centralBinom (j - 1) : Nat) : Real) := by ring
  have hBb : (bNat : Real) * B = (4 * (bNat : Real) - 2) * Q := by
    dsimp [B, Q]
    have h :
        (((bNat * Nat.centralBinom bNat : Nat) : Real)) =
          (((2 * (2 * (bNat - 1) + 1) *
              Nat.centralBinom (bNat - 1) : Nat) : Real)) := by
      exact_mod_cast hBbNat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at h
    have hidx : (((2 * (bNat - 1) + 1 : Nat) : Real)) =
        2 * (bNat : Real) - 1 := by
      rw [Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub (by omega : 1 ≤ bNat)]
      push_cast
      ring
    rw [hidx] at h
    calc
      (bNat : Real) * ((Nat.centralBinom bNat : Nat) : Real) =
          2 * (2 * (bNat : Real) - 1) *
            ((Nat.centralBinom (bNat - 1) : Nat) : Real) := by simpa using h
      _ = (4 * (bNat : Real) - 2) *
            ((Nat.centralBinom (bNat - 1) : Nat) : Real) := by ring
  have hscalePos : 0 < (j : Real) * (bNat : Real) := by positivity
  have hzero :
      ((N + 2 : Real) * A * B -
          2 * (2 * N + 3 : Real) * (P * B + A * Q) +
          16 * (N + 1 : Real) * P * Q) = 0 := by
    have hmul :
        ((j : Real) * (bNat : Real)) *
            ((N + 2 : Real) * A * B -
              2 * (2 * N + 3 : Real) * (P * B + A * Q) +
              16 * (N + 1 : Real) * P * Q) = 0 := by
      calc
        ((j : Real) * (bNat : Real)) *
              ((N + 2 : Real) * A * B -
                2 * (2 * N + 3 : Real) * (P * B + A * Q) +
                16 * (N + 1 : Real) * P * Q) =
            (N + 2 : Real) * ((j : Real) * A) *
                ((bNat : Real) * B) -
              2 * (2 * N + 3 : Real) *
                ((j : Real) * P * ((bNat : Real) * B) +
                  (bNat : Real) * Q * ((j : Real) * A)) +
              16 * (N + 1 : Real) * (j : Real) *
                (bNat : Real) * P * Q := by ring
        _ = (N + 2 : Real) * ((4 * (j : Real) - 2) * P) *
                ((4 * (bNat : Real) - 2) * Q) -
              2 * (2 * N + 3 : Real) *
                ((j : Real) * P * ((4 * (bNat : Real) - 2) * Q) +
                  (bNat : Real) * Q * ((4 * (j : Real) - 2) * P)) +
              16 * (N + 1 : Real) * (j : Real) *
                (bNat : Real) * P * Q := by rw [hAj, hBb]
        _ = 0 := by
          have hsumR : (j : Real) + (bNat : Real) = (N : Real) + 2 := by
            exact_mod_cast hsum
          have hN : (N : Real) = (j : Real) + (bNat : Real) - 2 := by
            linarith
          rw [hN]
          ring
    exact (mul_eq_zero.mp hmul).resolve_left hscalePos.ne'
  rw [← hqIndex]
  dsimp [A, P, B, Q, bNat] at hzero ⊢
  push_cast at hzero ⊢
  linarith

theorem coeff_X_add_C_mul_centralBinomialHomPolynomial
    (n j : Nat) (v : Real) :
    ((Polynomial.X + Polynomial.C v) *
        centralBinomialHomPolynomial n v).coeff j =
      (if 1 ≤ j then
          if j - 1 ≤ n then
            ((Nat.centralBinom (j - 1) : Nat) : Real) *
              ((Nat.centralBinom (n - (j - 1)) : Nat) : Real) *
                v ^ (n - (j - 1))
          else 0
        else 0) +
        v *
          (if j ≤ n then
            ((Nat.centralBinom j : Nat) : Real) *
              ((Nat.centralBinom (n - j) : Nat) : Real) * v ^ (n - j)
          else 0) := by
  have hX :
      (Polynomial.X * centralBinomialHomPolynomial n v).coeff j =
        if 1 ≤ j then
          (centralBinomialHomPolynomial n v).coeff (j - 1) else 0 := by
    simpa only [pow_one] using
      (Polynomial.coeff_X_pow_mul' (centralBinomialHomPolynomial n v) 1 j)
  rw [add_mul, coeff_add, hX, coeff_C_mul,
    coeff_centralBinomialHomPolynomial,
    coeff_centralBinomialHomPolynomial]

/-- Three-term recurrence for the raw central-binomial convolution. -/
theorem centralBinomialHomPolynomial_recurrence (N : Nat) (v : Real) :
    Polynomial.C ((N + 2 : Nat) : Real) *
        centralBinomialHomPolynomial (N + 2) v =
      Polynomial.C (2 * ((2 * N + 3 : Nat) : Real)) *
          (Polynomial.X + Polynomial.C v) *
            centralBinomialHomPolynomial (N + 1) v -
        Polynomial.C (16 * ((N + 1 : Nat) : Real) * v) *
          (Polynomial.X * centralBinomialHomPolynomial N v) := by
  ext j
  rw [coeff_C_mul, coeff_sub, mul_assoc, coeff_C_mul,
    coeff_X_add_C_mul_centralBinomialHomPolynomial, mul_assoc, mul_assoc,
    coeff_C_mul]
  have hX :
      (Polynomial.X * centralBinomialHomPolynomial N v).coeff j =
        if 1 ≤ j then
          (centralBinomialHomPolynomial N v).coeff (j - 1) else 0 := by
    simpa only [pow_one] using
      (Polynomial.coeff_X_pow_mul' (centralBinomialHomPolynomial N v) 1 j)
  rw [hX, coeff_centralBinomialHomPolynomial,
    coeff_centralBinomialHomPolynomial]
  cases j with
  | zero =>
      simp only [Nat.reduceLeDiff, if_false, zero_add, Nat.zero_le, if_true,
        Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
      have hcbNat := Nat.succ_mul_centralBinom_succ (N + 1)
      have hcb :
          ((N + 2 : Nat) : Real) *
              ((Nat.centralBinom (N + 2) : Nat) : Real) =
            2 * ((2 * N + 3 : Nat) : Real) *
              ((Nat.centralBinom (N + 1) : Nat) : Real) := by
        exact_mod_cast hcbNat
      simp only [Nat.centralBinom_zero, Nat.cast_one, one_mul, mul_zero,
        sub_zero]
      rw [show v *
          (((Nat.centralBinom (N + 1) : Nat) : Real) * v ^ (N + 1)) =
            ((Nat.centralBinom (N + 1) : Nat) : Real) * v ^ (N + 2) by
        rw [pow_succ']
        ring]
      linear_combination v ^ (N + 2) * hcb
  | succ j0 =>
      set j : Nat := j0 + 1 with hjdef
      have hj1 : 1 ≤ j := by omega
      simp only [if_pos hj1]
      by_cases hjmid : j ≤ N + 1
      · have hjm1 : j - 1 ≤ N := by omega
        simp only [if_pos (by omega : j - 1 ≤ N + 1), if_pos hjmid,
          if_pos hjm1]
        have hrec := centralBinomial_coefficient_recurrence_interior
          N j hj1 hjmid
        simp only [if_pos (by omega : j ≤ N + 2)]
        rw [show N + 1 - (j - 1) = N + 2 - j by omega,
          show N - (j - 1) = N + 1 - j by omega]
        rw [show v ^ (N + 2 - j) = v * v ^ (N + 1 - j) by
          rw [show N + 2 - j = (N + 1 - j) + 1 by omega, pow_succ']]
        push_cast at hrec ⊢
        linear_combination v ^ (N + 1 - j) * v * hrec
      · by_cases hjtop : j = N + 2
        · have hcbNat := Nat.succ_mul_centralBinom_succ (N + 1)
          have hcb :
              ((N + 2 : Nat) : Real) *
                  ((Nat.centralBinom (N + 2) : Nat) : Real) =
                2 * ((2 * N + 3 : Nat) : Real) *
                  ((Nat.centralBinom (N + 1) : Nat) : Real) := by
            exact_mod_cast hcbNat
          simp [hjtop, Nat.centralBinom]
          simpa [Nat.centralBinom, mul_assoc] using hcb
        · have hjlarge : N + 2 < j := by omega
          simp only [if_neg (by omega : ¬j ≤ N + 2),
            if_neg (by omega : ¬j - 1 ≤ N + 1),
            if_neg (by omega : ¬j ≤ N + 1),
            if_neg (by omega : ¬j - 1 ≤ N), mul_zero, add_zero,
            zero_mul, sub_zero]

/-- The squared-binomial invariant evaluated at `(C²,D²)`. -/
def squaredChooseQuadraticValue (n : Nat) (C D : Real) : Real :=
  (squaredChooseHomPolynomial n (D ^ 2)).eval (C ^ 2)

/-- The raw central-binomial convolution evaluated at the two eigenvalue
squares `(C+D)²,(C-D)²`. -/
def centralBinomialQuadraticValue (n : Nat) (C D : Real) : Real :=
  (centralBinomialHomPolynomial n ((C - D) ^ 2)).eval ((C + D) ^ 2)

theorem squaredChooseQuadraticValue_recurrence
    (N : Nat) (C D : Real) :
    ((N + 2 : Nat) : Real) * squaredChooseQuadraticValue (N + 2) C D =
      ((2 * N + 3 : Nat) : Real) * (C ^ 2 + D ^ 2) *
          squaredChooseQuadraticValue (N + 1) C D -
        ((N + 1 : Nat) : Real) * (C ^ 2 - D ^ 2) ^ 2 *
          squaredChooseQuadraticValue N C D := by
  have h := congrArg (fun p : Real[X] ↦ p.eval (C ^ 2))
    (squaredChooseHomPolynomial_recurrence N (D ^ 2))
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_X, eval_pow] at h
  simpa only [squaredChooseQuadraticValue, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_mul] using h

theorem centralBinomialQuadraticValue_recurrence
    (N : Nat) (C D : Real) :
    ((N + 2 : Nat) : Real) * centralBinomialQuadraticValue (N + 2) C D =
      4 * ((2 * N + 3 : Nat) : Real) * (C ^ 2 + D ^ 2) *
          centralBinomialQuadraticValue (N + 1) C D -
        16 * ((N + 1 : Nat) : Real) * (C ^ 2 - D ^ 2) ^ 2 *
          centralBinomialQuadraticValue N C D := by
  have h := congrArg (fun p : Real[X] ↦ p.eval ((C + D) ^ 2))
    (centralBinomialHomPolynomial_recurrence N ((C - D) ^ 2))
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_X, eval_pow] at h
  change ((N + 2 : Nat) : Real) * centralBinomialQuadraticValue (N + 2) C D = _
  change _ =
    4 * ((2 * N + 3 : Nat) : Real) * (C ^ 2 + D ^ 2) *
        centralBinomialQuadraticValue (N + 1) C D -
      16 * ((N + 1 : Nat) : Real) * (C ^ 2 - D ^ 2) ^ 2 *
        centralBinomialQuadraticValue N C D
  dsimp [centralBinomialQuadraticValue]
  push_cast at h ⊢
  nlinarith [sq_nonneg (C + D), sq_nonneg (C - D)]

@[simp] theorem squaredChooseQuadraticValue_zero (C D : Real) :
    squaredChooseQuadraticValue 0 C D = 1 := by
  rw [squaredChooseQuadraticValue, eval_squaredChooseHomPolynomial]
  norm_num

@[simp] theorem squaredChooseQuadraticValue_one (C D : Real) :
    squaredChooseQuadraticValue 1 C D = C ^ 2 + D ^ 2 := by
  rw [squaredChooseQuadraticValue, eval_squaredChooseHomPolynomial]
  norm_num [Finset.sum_range_succ]
  ring

@[simp] theorem centralBinomialQuadraticValue_zero (C D : Real) :
    centralBinomialQuadraticValue 0 C D = 1 := by
  rw [centralBinomialQuadraticValue, eval_centralBinomialHomPolynomial]
  norm_num [Nat.centralBinom]

@[simp] theorem centralBinomialQuadraticValue_one (C D : Real) :
    centralBinomialQuadraticValue 1 C D = 4 * (C ^ 2 + D ^ 2) := by
  rw [centralBinomialQuadraticValue, eval_centralBinomialHomPolynomial]
  norm_num [Finset.sum_range_succ, Nat.centralBinom]
  ring

/-- **Classical quadratic transformation, proved finitely.**  The raw
central-binomial eigenvalue convolution is `4ⁿ` times the homogeneous
squared-binomial invariant. -/
theorem centralBinomialQuadraticValue_eq_four_pow_mul_squaredChoose
    (n : Nat) (C D : Real) :
    centralBinomialQuadraticValue n C D =
      (4 : Real) ^ n * squaredChooseQuadraticValue n C D := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more N ihN ihN1 =>
      have hc := centralBinomialQuadraticValue_recurrence N C D
      have hs := squaredChooseQuadraticValue_recurrence N C D
      rw [ihN1, ihN] at hc
      have hmul :
          ((N + 2 : Nat) : Real) *
              (centralBinomialQuadraticValue (N + 2) C D -
                (4 : Real) ^ (N + 2) *
                  squaredChooseQuadraticValue (N + 2) C D) = 0 := by
        calc
          ((N + 2 : Nat) : Real) *
                (centralBinomialQuadraticValue (N + 2) C D -
                  (4 : Real) ^ (N + 2) *
                    squaredChooseQuadraticValue (N + 2) C D) =
              ((N + 2 : Nat) : Real) *
                  centralBinomialQuadraticValue (N + 2) C D -
                (4 : Real) ^ (N + 2) *
                  (((N + 2 : Nat) : Real) *
                    squaredChooseQuadraticValue (N + 2) C D) := by ring
          _ = (4 : Real) * ((2 * N + 3 : Nat) : Real) *
                  (C ^ 2 + D ^ 2) *
                    ((4 : Real) ^ (N + 1) *
                      squaredChooseQuadraticValue (N + 1) C D) -
                16 * ((N + 1 : Nat) : Real) *
                  (C ^ 2 - D ^ 2) ^ 2 *
                    ((4 : Real) ^ N * squaredChooseQuadraticValue N C D) -
                (4 : Real) ^ (N + 2) *
                  (((2 * N + 3 : Nat) : Real) * (C ^ 2 + D ^ 2) *
                      squaredChooseQuadraticValue (N + 1) C D -
                    ((N + 1 : Nat) : Real) * (C ^ 2 - D ^ 2) ^ 2 *
                      squaredChooseQuadraticValue N C D) := by rw [hc, hs]
          _ = 0 := by
            rw [show (4 : Real) ^ (N + 1) = 4 ^ N * 4 by rw [pow_succ],
              show (4 : Real) ^ (N + 2) = 4 ^ N * 16 by
                rw [show N + 2 = N + 2 by rfl, pow_add]
                norm_num]
            ring
      have hfactor : (((N + 2 : Nat) : Real)) ≠ 0 := by positivity
      have hz := (mul_eq_zero.mp hmul).resolve_left hfactor
      linarith

/-- The quadratic transform in its homogeneous finite-sum form.  This is the
exact algebraic bridge from the eigenvalue expansion of the Gaussian moment
to the squared-binomial invariant expansion. -/
theorem centralBinomial_quadratic_transform_sq
    (n : Nat) (C D : Real) :
    (∑ j ∈ Finset.range (n + 1),
        ((Nat.centralBinom j : Nat) : Real) *
          ((Nat.centralBinom (n - j) : Nat) : Real) *
          ((C + D) ^ 2) ^ j * ((C - D) ^ 2) ^ (n - j)) =
      (4 : Real) ^ n *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : Nat) : Real) ^ 2 *
            (C ^ 2) ^ j * (D ^ 2) ^ (n - j) := by
  simpa only [centralBinomialQuadraticValue,
      squaredChooseQuadraticValue,
      eval_centralBinomialHomPolynomial,
      eval_squaredChooseHomPolynomial] using
    centralBinomialQuadraticValue_eq_four_pow_mul_squaredChoose n C D

/-- The same quadratic transform with ordinary even powers. -/
theorem centralBinomial_quadratic_transform
    (n : Nat) (C D : Real) :
    (∑ j ∈ Finset.range (n + 1),
        ((2 * j).choose j : Real) *
          ((2 * (n - j)).choose (n - j) : Real) *
          (C + D) ^ (2 * j) * (C - D) ^ (2 * (n - j))) =
      (4 : Real) ^ n *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : Nat) : Real) ^ 2 *
            C ^ (2 * j) * D ^ (2 * (n - j)) := by
  simpa only [Nat.centralBinom, pow_mul] using
    centralBinomial_quadratic_transform_sq n C D

/-- Exact even moment of a diagonal rank-two Gaussian bilinear form, written
only through the two invariant parameters `C` and `D`. -/
theorem integral_diagonalRankTwoBilinear_add_sub_pow_two_mul
    (C D : Real) (n : Nat) :
    (∫ w, diagonalRankTwoBilinear (C + D) (C - D) w ^ (2 * n)
        ∂twoStandardGaussianPairs) =
      ((2 * n).factorial : Real) *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : Nat) : Real) ^ 2 *
            C ^ (2 * j) * D ^ (2 * (n - j)) := by
  rw [integral_diagonalRankTwoBilinear_pow_two_mul_central_sum,
    centralBinomial_quadratic_transform]
  have hfour : (4 : Real) ^ n ≠ 0 := by positivity
  field_simp

end

end LogdetLean.GramHafnian
