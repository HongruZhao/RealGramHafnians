import LogdetLean.NullCenterStandardization
import LogdetLean.Paper2608Computations
import LogdetLean.GeneralRResidualMoments
import LogdetLean.NullRegimeAsymptotics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic
/-!
# Elementary centering and scaling

This file formalizes the analytic comparison in Lemma E.1 and Corollary 3.5
of Hongru Zhao, arXiv:2608.00565v1 (2026), Appendix E, printed pp. 28--30.

The first ingredient is proved here rather than assumed: a second-order
remainder bound for harmonic numbers, and hence for the digamma function at
the integer and half-integer arguments occurring in the exact null center.
The proof uses only the Gamma recurrence/duplication identities already in
mathlib, the project's proved identification of `digammaSeries` with
`(log Gamma)'`, and elementary logarithm inequalities proved below.
-/

namespace LogdetLean

noncomputable section

open Filter Real Set
open scoped BigOperators Topology

/-! ## Two elementary logarithm inequalities -/

private def lowerLogRemainder (x : ℝ) : ℝ :=
  Real.log (1 + x) - x + x ^ 2 / 2

private theorem hasDerivAt_lowerLogRemainder {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt lowerLogRemainder (x ^ 2 / (1 + x)) x := by
  unfold lowerLogRemainder
  have hne : 1 + x ≠ 0 := by linarith
  have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y)) (1 / (1 + x)) x := by
    simpa only [Function.comp_def, zero_add, mul_one, one_div] using
      (Real.hasDerivAt_log hne).comp x
      ((hasDerivAt_const x 1).add (hasDerivAt_id x))
  have h := ((hlog.sub (hasDerivAt_id x)).add
    (((hasDerivAt_pow 2 x).div_const 2)))
  have hder : 1 / (1 + x) - 1 + (2 : ℝ) * x ^ (2 - 1) / 2 =
      x ^ 2 / (1 + x) := by
    field_simp [hne]
    ring
  refine (h.congr_deriv hder).congr_of_eventuallyEq ?_
  filter_upwards [] with y
  rfl

/-- The alternating quadratic truncation is a lower bound for
`log(1+x)` on the nonnegative half-line. -/
theorem sub_half_sq_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have hcont : ContinuousOn lowerLogRemainder (Ici 0) := by
    intro y hy
    exact (hasDerivAt_lowerLogRemainder hy).continuousAt.continuousWithinAt
  have hmono : MonotoneOn lowerLogRemainder (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) hcont
      (f' := fun y ↦ y ^ 2 / (1 + y))
    · intro y hy
      have hy0 : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
      exact (hasDerivAt_lowerLogRemainder hy0.le).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
      positivity
  have h := hmono (show 0 ∈ Ici (0 : ℝ) by simp)
    (show x ∈ Ici (0 : ℝ) by exact hx) hx
  dsimp [lowerLogRemainder] at h
  norm_num at h
  linarith

private def upperLogRemainder (x : ℝ) : ℝ :=
  x * (2 + x) / (2 * (1 + x)) - Real.log (1 + x)

private theorem hasDerivAt_upperLogRemainder {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt upperLogRemainder
      (x ^ 2 / (2 * (1 + x) ^ 2)) x := by
  unfold upperLogRemainder
  have hne : 1 + x ≠ 0 := by linarith
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hnum : HasDerivAt (fun y : ℝ ↦ y * (2 + y)) (2 + 2 * x) x := by
    have h := (hasDerivAt_id x).mul
      ((hasDerivAt_const x 2).add (hasDerivAt_id x))
    have h' : HasDerivAt (id * ((fun _ : ℝ ↦ (2 : ℝ)) + id))
        (2 + 2 * x) x := h.congr_deriv (by simp; ring)
    refine h'.congr_of_eventuallyEq ?_
    filter_upwards [] with y
    rfl
  have hden : HasDerivAt (fun y : ℝ ↦ 2 * (1 + y)) 2 x := by
    have h := (hasDerivAt_const x 2).mul
      ((hasDerivAt_const x 1).add (hasDerivAt_id x))
    have h' : HasDerivAt
        ((fun _ : ℝ ↦ (2 : ℝ)) * ((fun _ : ℝ ↦ (1 : ℝ)) + id))
        2 x := h.congr_deriv (by simp)
    refine h'.congr_of_eventuallyEq ?_
    filter_upwards [] with y
    rfl
  have hfrac := hnum.div hden (mul_ne_zero htwo hne)
  have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y))
      (1 / (1 + x)) x := by
    simpa only [Function.comp_def, zero_add, mul_one, one_div] using
      (Real.hasDerivAt_log hne).comp x
      ((hasDerivAt_const x 1).add (hasDerivAt_id x))
  have h := hfrac.sub hlog
  have hder :
      ((2 + 2 * x) * (2 * (1 + x)) - x * (2 + x) * 2) /
          (2 * (1 + x)) ^ 2 - 1 / (1 + x) =
        x ^ 2 / (2 * (1 + x) ^ 2) := by
    field_simp [hne]
    ring
  refine (h.congr_deriv hder).congr_of_eventuallyEq ?_
  filter_upwards [] with y
  rfl

/-- A rational upper bound for `log(1+x)`.  This is the precise bound that
makes the harmonic second-order remainder monotone. -/
theorem log_one_add_le_rational {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) := by
  have hcont : ContinuousOn upperLogRemainder (Ici 0) := by
    intro y hy
    exact (hasDerivAt_upperLogRemainder hy).continuousAt.continuousWithinAt
  have hmono : MonotoneOn upperLogRemainder (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) hcont
      (f' := fun y ↦ y ^ 2 / (2 * (1 + y) ^ 2))
    · intro y hy
      have hy0 : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
      exact (hasDerivAt_upperLogRemainder hy0.le).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
      positivity
  have h := hmono (show 0 ∈ Ici (0 : ℝ) by simp)
    (show x ∈ Ici (0 : ℝ) by exact hx) hx
  simpa [upperLogRemainder] using h

/-! ## A verified second-order harmonic remainder -/

/-- Positive second-order error in the harmonic-number expansion
`H_n = log n + gamma + 1/(2n) - q_n`. -/
def harmonicSecondOrderError (n : ℕ) : ℝ :=
  Real.log (n : ℝ) + Real.eulerMascheroniConstant +
    1 / (2 * (n : ℝ)) - (harmonic n : ℝ)

theorem harmonicSecondOrderError_succ_sub {n : ℕ} (hn : 0 < n) :
    harmonicSecondOrderError (n + 1) - harmonicSecondOrderError n =
      Real.log (1 + 1 / (n : ℝ)) -
        ((1 / (n : ℝ)) * (2 + 1 / (n : ℝ)) /
          (2 * (1 + 1 / (n : ℝ)))) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsuccR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold harmonicSecondOrderError
  rw [harmonic_succ, Rat.cast_add, Rat.cast_inv,
    Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  have hlog : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) =
      Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_div (by positivity : (n : ℝ) + 1 ≠ 0) hnR]
    congr 1
    field_simp [hnR]
  have hlog' : Real.log ((n : ℝ) + 1) = Real.log (n : ℝ) +
      Real.log (1 + 1 / (n : ℝ)) := by linarith
  rw [hlog']
  field_simp [hnR, hsuccR]
  ring

theorem harmonicSecondOrderError_antitone_step {n : ℕ} (hn : 0 < n) :
    harmonicSecondOrderError (n + 1) ≤ harmonicSecondOrderError n := by
  rw [← sub_nonpos, harmonicSecondOrderError_succ_sub hn]
  exact sub_nonpos.mpr (log_one_add_le_rational (by positivity))

theorem harmonicSecondOrderError_step_abs_le {n : ℕ} (hn : 0 < n) :
    0 ≤ harmonicSecondOrderError n - harmonicSecondOrderError (n + 1) ∧
      harmonicSecondOrderError n - harmonicSecondOrderError (n + 1) ≤
        1 / (2 * (n : ℝ) ^ 3) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiff := harmonicSecondOrderError_succ_sub hn
  have hupper := log_one_add_le_rational
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  have hlower := sub_half_sq_le_log_one_add
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  constructor
  · rw [← neg_sub, hdiff, neg_sub]
    exact sub_nonneg.mpr hupper
  · rw [← neg_sub, hdiff, neg_sub]
    calc
      (1 / (n : ℝ)) * (2 + 1 / (n : ℝ)) /
            (2 * (1 + 1 / (n : ℝ))) -
          Real.log (1 + 1 / (n : ℝ)) ≤
        (1 / (n : ℝ)) * (2 + 1 / (n : ℝ)) /
            (2 * (1 + 1 / (n : ℝ))) -
          ((1 / (n : ℝ)) - (1 / (n : ℝ)) ^ 2 / 2) := by linarith
      _ ≤ 1 / (2 * (n : ℝ) ^ 3) := by
        field_simp [hnR.ne']
        nlinarith

theorem tendsto_harmonicSecondOrderError_zero :
    Tendsto harmonicSecondOrderError atTop (nhds 0) := by
  have hmain : Tendsto
      (fun n : ℕ ↦ Real.eulerMascheroniConstant -
        ((harmonic n : ℝ) - Real.log (n : ℝ)))
      atTop (nhds 0) := by
    have hc : Tendsto (fun _ : ℕ ↦ Real.eulerMascheroniConstant) atTop
        (nhds Real.eulerMascheroniConstant) := tendsto_const_nhds
    simpa using hc.sub Real.tendsto_harmonic_sub_log
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (2 * (n : ℝ))) atTop (nhds 0) := by
    have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hhalf : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ)) atTop (nhds (1 / 2)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv, mul_comm] using
      hhalf.mul (tendsto_inv_atTop_zero.comp hcast)
  have hsum := hmain.add hinv
  convert hsum using 1
  · funext n
    unfold harmonicSecondOrderError
    ring
  · simp

/-- The second-order harmonic error is nonnegative. -/
theorem harmonicSecondOrderError_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ harmonicSecondOrderError n := by
  let f : ℕ → ℝ := fun k ↦ harmonicSecondOrderError (k + n)
  have hanti : Antitone f := antitone_nat_of_succ_le fun k ↦ by
    dsimp [f]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      harmonicSecondOrderError_antitone_step (show 0 < k + n by omega)
  have hlim : Tendsto f atTop (nhds 0) :=
    tendsto_harmonicSecondOrderError_zero.comp (tendsto_add_atTop_nat n)
  simpa [f] using hanti.le_of_tendsto hlim 0

/-- Explicit second-order upper bound.  The constant one is deliberately
loose; its simple form is convenient when summing digamma remainders. -/
theorem harmonicSecondOrderError_le_inv_sq {n : ℕ} (hn : 0 < n) :
    harmonicSecondOrderError n ≤ 1 / (n : ℝ) ^ 2 := by
  let f : ℕ → ℝ := fun k ↦
    harmonicSecondOrderError (k + n) - 1 / ((k + n : ℕ) : ℝ) ^ 2
  have hmono : Monotone f := monotone_nat_of_le_succ fun k ↦ by
    have hN : 0 < k + n := by omega
    have hNR : 0 < ((k + n : ℕ) : ℝ) := Nat.cast_pos.mpr hN
    have hsuccR : 0 < (((k + n + 1 : ℕ) : ℝ)) := by positivity
    have hstep := (harmonicSecondOrderError_step_abs_le hN).2
    have hsuccEq : (((k + n + 1 : ℕ) : ℝ)) =
        ((k + n : ℕ) : ℝ) + 1 := by norm_num
    have hrecip : 1 / (2 * ((k + n : ℕ) : ℝ) ^ 3) ≤
        1 / ((k + n : ℕ) : ℝ) ^ 2 -
          1 / (((k + n + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [hsuccEq]
      field_simp [hNR.ne', hsuccR.ne']
      nlinarith [show 1 ≤ ((k + n : ℕ) : ℝ) by exact_mod_cast hN,
        sq_nonneg (((k + n : ℕ) : ℝ))]
    dsimp [f]
    have h := hstep.trans hrecip
    rw [show k + 1 + n = k + n + 1 by omega]
    linarith
  have hcast : Tendsto (fun k : ℕ ↦ (((k + n : ℕ) : ℝ))) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n)
  have hinvSq : Tendsto
      (fun k : ℕ ↦ 1 / ((k + n : ℕ) : ℝ) ^ 2) atTop (nhds 0) := by
    have hi : Tendsto (fun k : ℕ ↦ (((k + n : ℕ) : ℝ))⁻¹)
        atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcast
    simpa [one_div, inv_pow] using hi.pow 2
  have herr : Tendsto (fun k : ℕ ↦
      harmonicSecondOrderError (k + n)) atTop (nhds 0) :=
    tendsto_harmonicSecondOrderError_zero.comp (tendsto_add_atTop_nat n)
  have hlim : Tendsto f atTop (nhds 0) := by
    simpa [f] using herr.sub hinvSq
  simpa [f] using hmono.ge_of_tendsto hlim 0

/-! ## Digamma at integer and half-integer arguments -/

theorem hasDerivAt_logGamma_eq_digammaSeries {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Real.log ∘ Real.Gamma) (digammaSeries x) x := by
  have hd : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x :=
    (Real.differentiableAt_Gamma (fun n ↦ by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)).log (Real.Gamma_pos_of_pos hx).ne'
  rw [← deriv_logGamma_eq_digammaSeries hx]
  exact hd.hasDerivAt

/-- Digamma duplication, derived by differentiating mathlib's proved real
Gamma duplication formula. -/
theorem digammaSeries_duplication {x : ℝ} (hx : 0 < x) :
    digammaSeries x + digammaSeries (x + 1 / 2) =
      2 * digammaSeries (2 * x) - 2 * Real.log 2 := by
  let g : ℝ → ℝ := fun y ↦
    Real.log (Real.Gamma y) + Real.log (Real.Gamma (y + 1 / 2))
  let h : ℝ → ℝ := fun y ↦
    Real.log (Real.Gamma (2 * y)) + (1 - 2 * y) * Real.log 2 +
      Real.log (Real.sqrt Real.pi)
  have hleft : HasDerivAt g
      (digammaSeries x + digammaSeries (x + 1 / 2)) x := by
    have h1 := hasDerivAt_logGamma_eq_digammaSeries hx
    have hshift : HasDerivAt (fun y : ℝ ↦ y + 1 / 2) 1 x :=
      (hasDerivAt_id x).add_const _
    have h2 := (hasDerivAt_logGamma_eq_digammaSeries (by linarith :
      0 < x + 1 / 2)).comp x hshift
    have h2' : HasDerivAt
        ((Real.log ∘ Real.Gamma) ∘ fun y : ℝ ↦ y + 1 / 2)
        (digammaSeries (x + 1 / 2)) x :=
      h2.congr_deriv (by ring)
    refine (h1.add h2').congr_of_eventuallyEq ?_
    filter_upwards [] with y
    rfl
  have hright : HasDerivAt h
      (2 * digammaSeries (2 * x) - 2 * Real.log 2) x := by
    have hscale : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
      have hs := (hasDerivAt_const x 2).mul (hasDerivAt_id x)
      have hs' : HasDerivAt ((fun _ : ℝ ↦ (2 : ℝ)) * id) 2 x :=
        hs.congr_deriv (by simp)
      refine hs'.congr_of_eventuallyEq ?_
      filter_upwards [] with y
      rfl
    have hgamma := (hasDerivAt_logGamma_eq_digammaSeries
      (show 0 < 2 * x by positivity)).comp x hscale
    have haff : HasDerivAt (fun y : ℝ ↦ (1 - 2 * y) * Real.log 2)
        (-2 * Real.log 2) x := by
      have ha := ((hasDerivAt_const x 1).sub
        ((hasDerivAt_const x 2).mul (hasDerivAt_id x))).mul_const
          (Real.log 2)
      have ha' := ha.congr_deriv (show
          (0 - (0 * x + 2 * 1)) * Real.log 2 = -2 * Real.log 2 by ring)
      refine ha'.congr_of_eventuallyEq ?_
      filter_upwards [] with y
      rfl
    have hconst := hasDerivAt_const x (Real.log (Real.sqrt Real.pi))
    have hs := (hgamma.add haff).add hconst
    have hs' := hs.congr_deriv (show
        digammaSeries (2 * x) * 2 + (-2 * Real.log 2) + 0 =
          2 * digammaSeries (2 * x) - 2 * Real.log 2 by ring)
    refine hs'.congr_of_eventuallyEq ?_
    filter_upwards [] with y
    rfl
  have heq : g =ᶠ[nhds x] h := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    have hGy : Real.Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy).ne'
    have hGyh : Real.Gamma (y + 1 / 2) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by linarith)).ne'
    have hG2y : Real.Gamma (2 * y) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hpow : (2 : ℝ) ^ (1 - 2 * y) ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num) _).ne'
    have hsqrt : Real.sqrt Real.pi ≠ 0 :=
      (Real.sqrt_pos.2 Real.pi_pos).ne'
    dsimp [g, h]
    calc
      Real.log (Real.Gamma y) + Real.log (Real.Gamma (y + 1 / 2)) =
          Real.log (Real.Gamma y * Real.Gamma (y + 1 / 2)) := by
            rw [Real.log_mul hGy hGyh]
      _ = Real.log (Real.Gamma (2 * y) * (2 : ℝ) ^ (1 - 2 * y) *
          Real.sqrt Real.pi) := by
            rw [Real.Gamma_mul_Gamma_add_half]
      _ = Real.log (Real.Gamma (2 * y)) + (1 - 2 * y) * Real.log 2 +
          Real.log (Real.sqrt Real.pi) := by
            rw [Real.log_mul (mul_ne_zero hG2y hpow) hsqrt,
              Real.log_mul hG2y hpow, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact hleft.unique (heq.hasDerivAt_iff.mpr hright)

@[simp]
theorem digammaSeries_one :
    digammaSeries 1 = -Real.eulerMascheroniConstant := by
  unfold digammaSeries
  have hfun : (fun l : ℕ ↦
      1 / (((l + 1 : ℕ) : ℝ)) - 1 / (1 + (l : ℝ))) = fun _ ↦ 0 := by
    funext l
    norm_num [Nat.cast_add, Nat.cast_one, add_comm]
  rw [hfun, tsum_zero]
  ring

/-- Exact integer values of the digamma series. -/
theorem digammaSeries_nat_succ (n : ℕ) :
    digammaSeries ((n + 1 : ℕ) : ℝ) =
      -Real.eulerMascheroniConstant + (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one,
        digammaSeries_add_one (by positivity), ih,
        harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

/-- Exact half-integer values, obtained from duplication and the integer
formula. -/
theorem digammaSeries_nat_add_half (n : ℕ) :
    digammaSeries ((n : ℝ) + 1 / 2) =
      -Real.eulerMascheroniConstant - 2 * Real.log 2 +
        2 * (harmonic (2 * n) : ℝ) - (harmonic n : ℝ) := by
  have hdup := digammaSeries_duplication
    (show 0 < (n : ℝ) + 1 / 2 by positivity)
  rw [show ((n : ℝ) + 1 / 2) + 1 / 2 = ((n + 1 : ℕ) : ℝ) by
      norm_num only [Nat.cast_add, Nat.cast_one]; ring,
    show 2 * ((n : ℝ) + 1 / 2) = ((2 * n + 1 : ℕ) : ℝ) by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]; ring,
    digammaSeries_nat_succ n, digammaSeries_nat_succ (2 * n)] at hdup
  linarith

theorem digammaSeries_nat_pos {n : ℕ} (hn : 0 < n) :
    digammaSeries (n : ℝ) =
      -Real.eulerMascheroniConstant + (harmonic n : ℝ) - 1 / (n : ℝ) := by
  have hrec := digammaSeries_add_one (show 0 < (n : ℝ) by exact_mod_cast hn)
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num,
    digammaSeries_nat_succ n] at hrec
  linarith

/-- At positive integer arguments, the digamma approximation error is
exactly minus the harmonic second-order error. -/
theorem digammaSeries_nat_sub_log_add_half_inv {n : ℕ} (hn : 0 < n) :
    digammaSeries (n : ℝ) -
        (Real.log (n : ℝ) - 1 / (2 * (n : ℝ))) =
      -harmonicSecondOrderError n := by
  rw [digammaSeries_nat_pos hn]
  unfold harmonicSecondOrderError
  ring

/-- At positive half-integers, duplication reduces the error to two
harmonic second-order errors. -/
theorem digammaSeries_nat_add_half_eq_log_add_errors {n : ℕ} (hn : 0 < n) :
    digammaSeries ((n : ℝ) + 1 / 2) =
      Real.log (n : ℝ) + harmonicSecondOrderError n -
        2 * harmonicSecondOrderError (2 * n) := by
  rw [digammaSeries_nat_add_half]
  unfold harmonicSecondOrderError
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2nR : ((2 * n : ℕ) : ℝ) ≠ 0 := by positivity
  have hlog : Real.log ((2 * n : ℕ) : ℝ) =
      Real.log 2 + Real.log (n : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR]
  rw [hlog]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hnR, h2nR]
  ring

/-- Uniform second-order digamma expansion at every positive half-integer.
The constant `20` is intentionally conservative. -/
theorem abs_digammaSeries_half_nat_sub_log_correction_le
    {k : ℕ} (hk : 0 < k) :
    |digammaSeries ((k : ℝ) / 2) -
        (Real.log ((k : ℝ) / 2) - 1 / (k : ℝ))| ≤
      20 / (k : ℝ) ^ 2 := by
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · have hn : 0 < n := by omega
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have herr := digammaSeries_nat_sub_log_add_half_inv hn
    have hq0 := harmonicSecondOrderError_nonneg hn
    have hq := harmonicSecondOrderError_le_inv_sq hn
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have harg : (2 * (n : ℝ)) / 2 = (n : ℝ) := by ring
    have hcorr : 1 / (2 * (n : ℝ)) = 1 / (2 * (n : ℝ)) := rfl
    rw [harg]
    change |digammaSeries (n : ℝ) -
      (Real.log (n : ℝ) - 1 / (2 * (n : ℝ)))| ≤
        20 / (2 * (n : ℝ)) ^ 2
    rw [herr, abs_neg, abs_of_nonneg hq0]
    calc
      harmonicSecondOrderError n ≤ 1 / (n : ℝ) ^ 2 := hq
      _ ≤ 20 / (2 * (n : ℝ)) ^ 2 := by
        field_simp [hnR.ne']
        nlinarith
  · by_cases hn0 : n = 0
    · subst n
      norm_num only [Nat.cast_one, Nat.cast_zero, zero_add]
      have hpsi0 := digammaSeries_nat_add_half 0
      norm_num only [Nat.cast_zero, harmonic_zero, Rat.cast_zero, mul_zero,
        sub_zero, add_zero] at hpsi0
      rw [hpsi0]
      have hlog2pos : 0 ≤ Real.log 2 :=
        Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      have hlog2le : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hgamma0 : 0 ≤ Real.eulerMascheroniConstant := by
        linarith [Real.one_half_lt_eulerMascheroniConstant]
      have hgammale : Real.eulerMascheroniConstant ≤ 1 :=
        Real.eulerMascheroniConstant_lt_two_thirds.le.trans
          (by norm_num : (2 / 3 : ℝ) ≤ 1)
      rw [show Real.log ((1 : ℝ) / 2) = -Real.log 2 by
        rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by ring, Real.log_inv]]
      rw [abs_le]
      constructor <;> norm_num <;> linarith
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have h2nR : 0 < (2 * (n : ℝ)) := by positivity
      have hkR : 0 < (2 * (n : ℝ) + 1) := by positivity
      have hpsi := digammaSeries_nat_add_half_eq_log_add_errors hn
      have hq1_0 := harmonicSecondOrderError_nonneg hn
      have hq1 := harmonicSecondOrderError_le_inv_sq hn
      have h2npos : 0 < 2 * n := by omega
      have hq2_0 := harmonicSecondOrderError_nonneg h2npos
      have hq2 := harmonicSecondOrderError_le_inv_sq h2npos
      have hlogdiff : Real.log ((n : ℝ) + 1 / 2) - Real.log (n : ℝ) =
          Real.log (1 + 1 / (2 * (n : ℝ))) := by
        rw [← Real.log_div (by positivity : (n : ℝ) + 1 / 2 ≠ 0) hnR.ne']
        congr 1
        field_simp [hnR.ne']
      let delta : ℝ := Real.log ((n : ℝ) + 1 / 2) -
        Real.log (n : ℝ) - 1 / (2 * (n : ℝ) + 1)
      have hdelta0 : 0 ≤ delta := by
        dsimp [delta]
        rw [hlogdiff]
        have hlower := Real.one_sub_inv_le_log_of_pos
          (show 0 < 1 + 1 / (2 * (n : ℝ)) by positivity)
        have hid : 1 - (1 + 1 / (2 * (n : ℝ)))⁻¹ =
            1 / (2 * (n : ℝ) + 1) := by
          field_simp [hnR.ne']
          ring
        rw [hid] at hlower
        linarith
      have hdelta : delta ≤ 1 / (2 * (n : ℝ) *
          (2 * (n : ℝ) + 1)) := by
        dsimp [delta]
        rw [hlogdiff]
        have hu := Real.log_le_sub_one_of_pos
          (show 0 < 1 + 1 / (2 * (n : ℝ)) by positivity)
        have hu' : Real.log (1 + 1 / (2 * (n : ℝ))) ≤
            1 / (2 * (n : ℝ)) := by linarith
        calc
          Real.log (1 + 1 / (2 * (n : ℝ))) -
              1 / (2 * (n : ℝ) + 1) ≤
            1 / (2 * (n : ℝ)) - 1 / (2 * (n : ℝ) + 1) := by linarith
          _ = 1 / (2 * (n : ℝ) * (2 * (n : ℝ) + 1)) := by
            field_simp [hnR.ne']
            ring
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      rw [show (2 * (n : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 by ring,
        hpsi]
      have herr :
          Real.log (n : ℝ) + harmonicSecondOrderError n -
                2 * harmonicSecondOrderError (2 * n) -
              (Real.log ((n : ℝ) + 1 / 2) -
                1 / (2 * (n : ℝ) + 1)) =
            harmonicSecondOrderError n -
              2 * harmonicSecondOrderError (2 * n) - delta := by
        dsimp [delta]
        ring
      rw [herr]
      have habs :
          |harmonicSecondOrderError n -
              2 * harmonicSecondOrderError (2 * n) - delta| ≤
            harmonicSecondOrderError n +
              2 * harmonicSecondOrderError (2 * n) + delta := by
        rw [abs_le]
        constructor <;> linarith
      calc
        |harmonicSecondOrderError n -
            2 * harmonicSecondOrderError (2 * n) - delta| ≤
          harmonicSecondOrderError n +
            2 * harmonicSecondOrderError (2 * n) + delta := habs
        _ ≤ 1 / (n : ℝ) ^ 2 +
            2 * (1 / (2 * (n : ℝ)) ^ 2) +
              1 / (2 * (n : ℝ) * (2 * (n : ℝ) + 1)) := by
          norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hq2
          linarith
        _ ≤ 20 / (2 * (n : ℝ) + 1) ^ 2 := by
          field_simp [hnR.ne']
          nlinarith [show 1 ≤ (n : ℝ) by exact_mod_cast hn,
            sq_nonneg (n : ℝ)]

/-! ## The exact center versus its elementary summand approximation -/

/-- The cancellation-preserving elementary approximation to the exact
digamma center, indexed by the residual degrees of freedom. -/
def nullCenterLeading (m p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico (m - p + 1) m,
    (Real.log (k : ℝ) - Real.log (m : ℝ) - 1 / (k : ℝ) + 1 / (m : ℝ))

private theorem cast_center_shape_index {m j : ℕ} (hjm : j ≤ m) :
    (((m - j + 1 : ℕ) : ℝ) / 2) = betaShapeA m j := by
  unfold betaShapeA
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hjm]

/-- Reindex the exact digamma center by the residual degrees of freedom. -/
theorem nullCenterDigammaSeries_eq_gap_sum {m p : ℕ}
    (h : Admissible m p) :
    nullCenterDigammaSeries m p =
      ∑ k ∈ Finset.Ico (m - p + 1) m,
        (digammaSeries ((k : ℝ) / 2) -
          digammaSeries ((m : ℝ) / 2)) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  unfold nullCenterDigammaSeries betaShapeTotal
  apply Finset.sum_bij (fun j _hj ↦ m - j + 1)
  · intro j hj
    have hjb := Finset.mem_Icc.mp hj
    exact Finset.mem_Ico.mpr (by omega)
  · intro j₁ hj₁ j₂ hj₂ heq
    have h₁ := (Finset.mem_Icc.mp hj₁).2
    have h₂ := (Finset.mem_Icc.mp hj₂).2
    omega
  · intro k hk
    have hkb := Finset.mem_Ico.mp hk
    refine ⟨m - k + 1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr (by omega)
    · omega
  · intro j hj
    have hjm : j ≤ m := le_trans (Finset.mem_Icc.mp hj).2 h.2
    rw [← cast_center_shape_index hjm]

/-- Explicit finite comparison between the exact digamma center and the
cancellation-preserving elementary sum.  Retaining the factor `p-1` is
essential in the dilute regime. -/
theorem abs_nullCenterDigammaSeries_sub_nullCenterLeading_endpoint_le
    {m p : ℕ} (h : Admissible m p) :
    |nullCenterDigammaSeries m p - nullCenterLeading m p| ≤
      20 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 2) +
        20 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  rw [nullCenterDigammaSeries_eq_gap_sum h]
  unfold nullCenterLeading
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hmpos : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
  have hmerr := abs_digammaSeries_half_nat_sub_log_correction_le hmpos
  have hterm : ∀ k ∈ Finset.Ico (m - p + 1) m,
      |(digammaSeries ((k : ℝ) / 2) - digammaSeries ((m : ℝ) / 2)) -
          (Real.log (k : ℝ) - Real.log (m : ℝ) -
            1 / (k : ℝ) + 1 / (m : ℝ))| ≤
        20 / (k : ℝ) ^ 2 + 20 / (m : ℝ) ^ 2 := by
    intro k hk
    have hkpos : 0 < k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hkpos
    have hkerr := abs_digammaSeries_half_nat_sub_log_correction_le hkpos
    have hlogk : Real.log ((k : ℝ) / 2) =
        Real.log (k : ℝ) - Real.log 2 := by
      rw [Real.log_div hkR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have hlogm : Real.log ((m : ℝ) / 2) =
        Real.log (m : ℝ) - Real.log 2 := by
      rw [Real.log_div hmR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    let ek : ℝ := digammaSeries ((k : ℝ) / 2) -
      (Real.log ((k : ℝ) / 2) - 1 / (k : ℝ))
    let em : ℝ := digammaSeries ((m : ℝ) / 2) -
      (Real.log ((m : ℝ) / 2) - 1 / (m : ℝ))
    have hid :
        (digammaSeries ((k : ℝ) / 2) - digammaSeries ((m : ℝ) / 2)) -
            (Real.log (k : ℝ) - Real.log (m : ℝ) -
              1 / (k : ℝ) + 1 / (m : ℝ)) = ek - em := by
      dsimp [ek, em]
      rw [hlogk, hlogm]
      ring
    rw [hid]
    calc
      |ek - em| ≤ |ek| + |em| := abs_sub ek em
      _ ≤ 20 / (k : ℝ) ^ 2 + 20 / (m : ℝ) ^ 2 :=
        add_le_add hkerr hmerr
  calc
    (∑ k ∈ Finset.Ico (m - p + 1) m,
        |(digammaSeries ((k : ℝ) / 2) - digammaSeries ((m : ℝ) / 2)) -
          (Real.log (k : ℝ) - Real.log (m : ℝ) -
            1 / (k : ℝ) + 1 / (m : ℝ))|) ≤
      ∑ _k ∈ Finset.Ico (m - p + 1) m,
        (20 / (((m - p + 1 : ℕ) : ℝ) ^ 2) +
          20 / (m : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        refine (hterm k hk).trans ?_
        have hmk : m - p + 1 ≤ k := (Finset.mem_Ico.mp hk).1
        have hbase : 0 < (((m - p + 1 : ℕ) : ℝ)) := by positivity
        have hkpos : 0 < k := by omega
        have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hkpos
        have hcast : (((m - p + 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
          exact_mod_cast hmk
        have hinv : 20 / (k : ℝ) ^ 2 ≤
            20 / (((m - p + 1 : ℕ) : ℝ) ^ 2) := by gcongr
        linarith
    _ = 20 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 2) +
        20 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
      have hcard : m - (m - p + 1) = p - 1 := by omega
      have hcastp : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      rw [Finset.sum_const, Nat.card_Ico, hcard]
      simp only [nsmul_eq_mul, hcastp]
      ring

private theorem prod_cast_Ico_eq_factorial_div {d m : ℕ}
    (hdm : d + 1 ≤ m) :
    (∏ k ∈ Finset.Ico (d + 1) m, (k : ℝ)) =
      ((m - 1).factorial : ℝ) / (d.factorial : ℝ) := by
  cases m with
  | zero => omega
  | succ r =>
    have hcon := Finset.prod_Ico_consecutive (fun k : ℕ ↦ (k : ℝ))
      (show 1 ≤ d + 1 by omega) hdm
    rw [show (∏ k ∈ Finset.Ico 1 (d + 1), (k : ℝ)) =
          (d.factorial : ℝ) by
          rw [← Nat.cast_prod]
          norm_cast
          exact Finset.prod_Ico_id_eq_factorial d,
        show (∏ k ∈ Finset.Ico 1 (r + 1), (k : ℝ)) =
            (r.factorial : ℝ) by
          rw [← Nat.cast_prod]
          norm_cast
          exact Finset.prod_Ico_id_eq_factorial r] at hcon
    rw [eq_div_iff]
    · simpa [mul_comm] using hcon
    · positivity

private theorem sum_log_cast_Ico_eq_log_factorial_sub {d m : ℕ}
    (hdm : d + 1 ≤ m) :
    (∑ k ∈ Finset.Ico (d + 1) m, Real.log (k : ℝ)) =
      Real.log ((m - 1).factorial : ℝ) -
        Real.log (d.factorial : ℝ) := by
  rw [← Real.log_prod]
  · rw [prod_cast_Ico_eq_factorial_div hdm, Real.log_div]
    · positivity
    · positivity
  · intro k hk
    have hklo := (Finset.mem_Ico.mp hk).1
    have hkpos : 0 < k := by omega
    positivity

/-- Exact logarithmic Stirling decomposition used in Appendix E.  This is a
direct algebraic consequence of Mathlib's proved `log_stirlingSeq_formula`. -/
theorem log_factorial_eq_stirling_decomposition {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) =
      ((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - (n : ℝ) +
        Real.log 2 / 2 + Real.log (Stirling.stirlingSeq n) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := Stirling.log_stirlingSeq_formula n
  have hlog2n : Real.log (2 * (n : ℝ)) =
      Real.log 2 + Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR]
  have hlogdiv : Real.log ((n : ℝ) / Real.exp 1) =
      Real.log (n : ℝ) - 1 := by
    rw [Real.log_div hnR (Real.exp_ne_zero 1), Real.log_exp]
  change Real.log (Stirling.stirlingSeq n) =
    Real.log (n.factorial : ℝ) - 1 / 2 * Real.log (2 * (n : ℝ)) -
      (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) at h
  rw [hlog2n, hlogdiv] at h
  linarith

/-- Exact decomposition of the difference between the elementary summand
center and the closed center in equation (3.7).  The three displayed
remainders are respectively the Stirling, endpoint, and harmonic
second-order remainders from Appendix E. -/
theorem nullCenterLeading_eq_elementary_add_remainders
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    nullCenterLeading m p =
      elementaryNullCenterReal (m : ℝ) (p : ℝ) +
        (Real.log (Stirling.stirlingSeq m) -
          Real.log (Stirling.stirlingSeq (m - p))) +
        (1 / (2 * ((m - p : ℕ) : ℝ)) - 1 / (2 * (m : ℝ))) +
        (harmonicSecondOrderError m -
          harmonicSecondOrderError (m - p)) := by
  let d : ℕ := m - p
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmpos : 0 < m := by omega
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdm : d + 1 ≤ m := by dsimp [d]; omega
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hcard : m - (d + 1) = p - 1 := by dsimp [d]; omega
  have hcastcard : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have hlogsum := sum_log_cast_Ico_eq_log_factorial_sub hdm
  have hrecip :
      (∑ k ∈ Finset.Ico (d + 1) m,
        (1 / (k : ℝ) - 1 / (m : ℝ))) =
      (harmonic (m - 1) : ℝ) - (harmonic d : ℝ) -
        ((p : ℝ) - 1) / (m : ℝ) := by
    have hv := nullVLeading_eq_harmonic_sub h
    unfold nullVLeading nullGapPowerDifference at hv
    change 2 * (∑ k ∈ Finset.Ico (d + 1) m,
        (1 / (k : ℝ) ^ 1 - 1 / (m : ℝ) ^ 1)) =
      2 * ((harmonic (m - 1) : ℝ) - (harmonic d : ℝ) -
        ((p : ℝ) - 1) / (m : ℝ)) at hv
    simpa only [pow_one] using (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hv)
  have hlead : nullCenterLeading m p =
      Real.log ((m - 1).factorial : ℝ) -
        Real.log (d.factorial : ℝ) -
        ((p : ℝ) - 1) * Real.log (m : ℝ) -
        ((harmonic (m - 1) : ℝ) - (harmonic d : ℝ) -
          ((p : ℝ) - 1) / (m : ℝ)) := by
    unfold nullCenterLeading
    change (∑ k ∈ Finset.Ico (d + 1) m,
      (Real.log (k : ℝ) - Real.log (m : ℝ) -
        1 / (k : ℝ) + 1 / (m : ℝ))) = _
    calc
      (∑ k ∈ Finset.Ico (d + 1) m,
        (Real.log (k : ℝ) - Real.log (m : ℝ) -
          1 / (k : ℝ) + 1 / (m : ℝ))) =
        (∑ k ∈ Finset.Ico (d + 1) m,
          ((Real.log (k : ℝ) - Real.log (m : ℝ)) -
            (1 / (k : ℝ) - 1 / (m : ℝ)))) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = (∑ k ∈ Finset.Ico (d + 1) m,
          (Real.log (k : ℝ) - Real.log (m : ℝ))) -
          ∑ k ∈ Finset.Ico (d + 1) m,
            (1 / (k : ℝ) - 1 / (m : ℝ)) := by
              rw [Finset.sum_sub_distrib]
      _ = ((∑ k ∈ Finset.Ico (d + 1) m, Real.log (k : ℝ)) -
          ∑ _k ∈ Finset.Ico (d + 1) m, Real.log (m : ℝ)) -
          ∑ k ∈ Finset.Ico (d + 1) m,
            (1 / (k : ℝ) - 1 / (m : ℝ)) := by
              rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [hlogsum, hrecip, Finset.sum_const, Nat.card_Ico, hcard]
        simp only [nsmul_eq_mul, hcastcard]
  have hmEq : m - 1 + 1 = m := by omega
  have hharmSucc : (harmonic (m - 1) : ℝ) =
      (harmonic m : ℝ) - 1 / (m : ℝ) := by
    have hs := congrArg (fun q : ℚ ↦ (q : ℝ)) (harmonic_succ (m - 1))
    rw [hmEq] at hs
    norm_num only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hs
    rw [one_div]
    linarith
  have hfacSucc : Real.log ((m - 1).factorial : ℝ) =
      Real.log (m.factorial : ℝ) - Real.log (m : ℝ) := by
    have hnat : m.factorial = m * (m - 1).factorial := by
      conv_lhs => rw [← hmEq, Nat.factorial_succ]
      rw [hmEq]
    have hcast : (m.factorial : ℝ) =
        (m : ℝ) * ((m - 1).factorial : ℝ) := by exact_mod_cast hnat
    have hlog := congrArg Real.log hcast
    rw [Real.log_mul hmR.ne' (by positivity :
      ((m - 1).factorial : ℝ) ≠ 0)] at hlog
    linarith
  have hfacm := log_factorial_eq_stirling_decomposition hmpos
  have hfacd := log_factorial_eq_stirling_decomposition hdpos
  have hharM : (harmonic m : ℝ) =
      Real.log (m : ℝ) + Real.eulerMascheroniConstant +
        1 / (2 * (m : ℝ)) - harmonicSecondOrderError m := by
    unfold harmonicSecondOrderError
    ring
  have hharD : (harmonic d : ℝ) =
      Real.log (d : ℝ) + Real.eulerMascheroniConstant +
        1 / (2 * (d : ℝ)) - harmonicSecondOrderError d := by
    unfold harmonicSecondOrderError
    ring
  have hgapcast : (p : ℝ) = (m : ℝ) - (d : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub hpm]
    ring
  have hmu := elementaryNullCenterReal_gap_rewrite
    (m := (m : ℝ)) (p := (p : ℝ)) (d := (d : ℝ))
    hmR hdR hgapcast
  have hgaplog : gapLogReal (m : ℝ) (d : ℝ) =
      Real.log (m : ℝ) - Real.log (d : ℝ) := by
    unfold gapLogReal
    rw [Real.log_div hmR.ne' hdR.ne']
  rw [hlead, hfacSucc, hfacm, hfacd, hharmSucc, hharM, hharD,
    hmu, hgaplog]
  dsimp [d]
  rw [Nat.cast_sub hpm]
  ring

/-- Robbins' stepwise Stirling bound, telescoped over an arbitrary interval.
This is the exact uniform form needed when the residual gap varies with the
dimension. -/
theorem abs_log_stirlingSeq_sub_le_inv_gap
    {d m : ℕ} (hd : 0 < d) (hdm : d ≤ m) :
    |Real.log (Stirling.stirlingSeq m) -
        Real.log (Stirling.stirlingSeq d)| ≤ 1 / (12 * (d : ℝ)) := by
  have hanti : Real.log (Stirling.stirlingSeq m) ≤
      Real.log (Stirling.stirlingSeq d) := by
    cases d with
    | zero => omega
    | succ d₀ =>
      cases m with
      | zero => omega
      | succ m₀ =>
        have hle : d₀ ≤ m₀ := by omega
        simpa only [Function.comp_apply] using
          Stirling.log_stirlingSeq'_antitone hle
  have htel : Real.log (Stirling.stirlingSeq d) -
      Real.log (Stirling.stirlingSeq m) =
      ∑ k ∈ Finset.Ico d m,
        (Real.log (Stirling.stirlingSeq k) -
          Real.log (Stirling.stirlingSeq (k + 1))) := by
    rw [Finset.sum_Ico_eq_sum_range]
    symm
    simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_sub_of_le hdm] using
      (Finset.sum_range_sub'
        (fun i : ℕ ↦ Real.log (Stirling.stirlingSeq (d + i))) (m - d))
  have hsteps :
      (∑ k ∈ Finset.Ico d m,
        (Real.log (Stirling.stirlingSeq k) -
          Real.log (Stirling.stirlingSeq (k + 1)))) ≤
      ∑ k ∈ Finset.Ico d m,
        1 / (12 * (k : ℝ) * ((k : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact Stirling.log_stirlingSeq_sdiff_le k
  have htelRecip :
      (∑ k ∈ Finset.Ico d m,
        1 / (12 * (k : ℝ) * ((k : ℝ) + 1))) ≤
        1 / (12 * (d : ℝ)) := by
    have hsum :
        (∑ k ∈ Finset.Ico d m,
          1 / (12 * (k : ℝ) * ((k : ℝ) + 1))) =
        (1 / 12 : ℝ) *
          ∑ k ∈ Finset.Ico d m,
            (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkpos : 0 < k := by
        have := (Finset.mem_Ico.mp hk).1
        omega
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
      have hksR : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hkR, hksR]
      ring
    rw [hsum]
    have hsumdiff :
        (∑ k ∈ Finset.Ico d m,
          (1 / (k : ℝ) - 1 / ((k : ℝ) + 1))) =
        1 / (d : ℝ) - 1 / (m : ℝ) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have ht := Finset.sum_range_sub'
        (fun i : ℕ ↦ 1 / ((d + i : ℕ) : ℝ)) (m - d)
      have hend : d + (m - d) = m := Nat.add_sub_of_le hdm
      convert ht using 1 <;> simp only [Nat.cast_add, Nat.cast_one, hend]
      · apply Finset.sum_congr rfl
        intro k hk
        congr 2
        ring
      · ring
    rw [hsumdiff]
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    have hmR : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le hd hdm)
    have hinvM : 0 ≤ 1 / (m : ℝ) := by positivity
    calc
      (1 / 12 : ℝ) * (1 / (d : ℝ) - 1 / (m : ℝ)) ≤
          (1 / 12 : ℝ) * (1 / (d : ℝ)) := by nlinarith
      _ = 1 / (12 * (d : ℝ)) := by field_simp
  rw [abs_of_nonpos (sub_nonpos.mpr hanti), neg_sub]
  rw [htel]
  exact hsteps.trans htelRecip

private theorem abs_digamma_center_summand_le
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    |(digammaSeries ((k : ℝ) / 2) - digammaSeries ((m : ℝ) / 2)) -
        (Real.log (k : ℝ) - Real.log (m : ℝ) -
          1 / (k : ℝ) + 1 / (m : ℝ))| ≤
      20 / (k : ℝ) ^ 2 + 20 / (m : ℝ) ^ 2 := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hkerr := abs_digammaSeries_half_nat_sub_log_correction_le hk
  have hmerr := abs_digammaSeries_half_nat_sub_log_correction_le hm
  have hlogk : Real.log ((k : ℝ) / 2) =
      Real.log (k : ℝ) - Real.log 2 := by
    rw [Real.log_div hkR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  have hlogm : Real.log ((m : ℝ) / 2) =
      Real.log (m : ℝ) - Real.log 2 := by
    rw [Real.log_div hmR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  let ek : ℝ := digammaSeries ((k : ℝ) / 2) -
    (Real.log ((k : ℝ) / 2) - 1 / (k : ℝ))
  let em : ℝ := digammaSeries ((m : ℝ) / 2) -
    (Real.log ((m : ℝ) / 2) - 1 / (m : ℝ))
  have hid :
      (digammaSeries ((k : ℝ) / 2) - digammaSeries ((m : ℝ) / 2)) -
          (Real.log (k : ℝ) - Real.log (m : ℝ) -
            1 / (k : ℝ) + 1 / (m : ℝ)) = ek - em := by
    dsimp [ek, em]
    rw [hlogk, hlogm]
    ring
  rw [hid]
  exact (abs_sub ek em).trans (add_le_add hkerr hmerr)

/-- Integral-test bound for the reciprocal-square tail, proved by the
pointwise telescoping majorant `1/k^2 ≤ 1/(k-1)-1/k`. -/
theorem sum_inv_sq_Ico_succ_le_inv
    {d m : ℕ} (hd : 0 < d) (hdm : d + 1 ≤ m) :
    (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2) ≤ 1 / (d : ℝ) := by
  have hpoint : ∀ k ∈ Finset.Ico (d + 1) m,
      1 / (k : ℝ) ^ 2 ≤
        1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
    intro k hk
    have hkNat : d + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkOne : 1 < k := by omega
    have hkR : 1 < (k : ℝ) := by exact_mod_cast hkOne
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hkm0 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have heq : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) =
        1 / (((k : ℝ) - 1) * (k : ℝ)) := by
      field_simp [hk0.ne', hkm0.ne']
      ring
    rw [heq]
    have hden : ((k : ℝ) - 1) * (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      nlinarith
    exact one_div_le_one_div_of_le (mul_pos hkm0 hk0) hden
  calc
    (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2) ≤
        ∑ k ∈ Finset.Ico (d + 1) m,
          (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hpoint k hk
    _ = 1 / (d : ℝ) - 1 / ((m : ℝ) - 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hsumEq :
          (∑ k ∈ Finset.range (m - (d + 1)),
            (1 / ((d : ℝ) + 1 + (k : ℝ) - 1) -
              1 / ((d : ℝ) + 1 + (k : ℝ)))) =
          ∑ k ∈ Finset.range (m - (d + 1)),
            (1 / ((d : ℝ) + (k : ℝ)) -
              1 / ((d : ℝ) + ((k : ℝ) + 1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 2 <;> norm_num only [Nat.cast_add, Nat.cast_one] <;> ring
      rw [hsumEq]
      have ht := Finset.sum_range_sub'
        (fun i : ℕ ↦ 1 / ((d : ℝ) + (i : ℝ))) (m - (d + 1))
      have hendNat : d + (m - (d + 1)) = m - 1 := by omega
      have hend : (d : ℝ) + ((m - (d + 1) : ℕ) : ℝ) =
          (m : ℝ) - 1 := by
        rw [← Nat.cast_add, hendNat, Nat.cast_sub (by omega : 1 ≤ m),
          Nat.cast_one]
      convert ht using 1
      · apply Finset.sum_congr rfl
        intro k hk
        congr 2
        norm_num only [Nat.cast_add, Nat.cast_one]
      · simpa using hend.symm
    _ ≤ 1 / (d : ℝ) := by
      have hmOne : 1 < m := by omega
      have hmCast : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hmOne
      have hmR : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      have : 0 ≤ 1 / ((m : ℝ) - 1) := one_div_nonneg.mpr hmR.le
      linarith

/-- Uniform all-gap comparison for the exact and elementary summand centers.
Unlike the endpoint bound, this remains informative for every fixed positive
gap. -/
theorem abs_nullCenterDigammaSeries_sub_nullCenterLeading_le_inv_gap
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    |nullCenterDigammaSeries m p - nullCenterLeading m p| ≤
      40 / ((m - p : ℕ) : ℝ) := by
  let d : ℕ := m - p
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmpos : 0 < m := by omega
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdm : d + 1 ≤ m := by dsimp [d]; omega
  rw [nullCenterDigammaSeries_eq_gap_sum h]
  unfold nullCenterLeading
  change |(∑ k ∈ Finset.Ico (d + 1) m,
      (digammaSeries ((k : ℝ) / 2) - digammaSeries ((m : ℝ) / 2))) -
    ∑ k ∈ Finset.Ico (d + 1) m,
      (Real.log (k : ℝ) - Real.log (m : ℝ) -
        1 / (k : ℝ) + 1 / (m : ℝ))| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.Ico (d + 1) m,
        ((digammaSeries ((k : ℝ) / 2) - digammaSeries ((m : ℝ) / 2)) -
          (Real.log (k : ℝ) - Real.log (m : ℝ) -
            1 / (k : ℝ) + 1 / (m : ℝ)))| ≤
      ∑ k ∈ Finset.Ico (d + 1) m,
        |(digammaSeries ((k : ℝ) / 2) - digammaSeries ((m : ℝ) / 2)) -
          (Real.log (k : ℝ) - Real.log (m : ℝ) -
            1 / (k : ℝ) + 1 / (m : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico (d + 1) m,
        (20 / (k : ℝ) ^ 2 + 20 / (m : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := by
        have := (Finset.mem_Ico.mp hk).1
        omega
      exact abs_digamma_center_summand_le hkpos hmpos
    _ = 20 * (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2) +
        20 * ((m - (d + 1) : ℕ) : ℝ) / (m : ℝ) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico]
      simp only [nsmul_eq_mul]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      ring
    _ ≤ 20 * (1 / (d : ℝ)) + 20 * (1 / (m : ℝ)) := by
      have htail := sum_inv_sq_Ico_succ_le_inv hdpos hdm
      have hcardle : ((m - (d + 1) : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.sub_le m (d + 1)
      have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
      have hsecond : 20 * ((m - (d + 1) : ℕ) : ℝ) / (m : ℝ) ^ 2 ≤
          20 * (1 / (m : ℝ)) := by
        apply (div_le_iff₀ (sq_pos_of_pos hmR)).2
        field_simp [hmR.ne']
        nlinarith
      nlinarith
    _ ≤ 40 / (d : ℝ) := by
      have hdm' : d ≤ m := le_trans (Nat.le_add_right d 1) hdm
      have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
      have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
      have hinv : 1 / (m : ℝ) ≤ 1 / (d : ℝ) := by gcongr
      calc
        20 * (1 / (d : ℝ)) + 20 * (1 / (m : ℝ)) ≤
            20 * (1 / (d : ℝ)) + 20 * (1 / (d : ℝ)) := by gcongr
        _ = 40 / (d : ℝ) := by ring

/-- The closed elementary center differs from the cancellation-preserving
summand center by at most `2/d`, uniformly over all positive gaps. -/
theorem abs_nullCenterLeading_sub_elementaryNullCenterReal_le_inv_gap
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    |nullCenterLeading m p -
        elementaryNullCenterReal (m : ℝ) (p : ℝ)| ≤
      2 / ((m - p : ℕ) : ℝ) := by
  let d : ℕ := m - p
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmpos : 0 < m := by omega
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdm : d ≤ m := by dsimp [d]; omega
  let rS : ℝ := Real.log (Stirling.stirlingSeq m) -
    Real.log (Stirling.stirlingSeq d)
  let rE : ℝ := 1 / (2 * (d : ℝ)) - 1 / (2 * (m : ℝ))
  let rQ : ℝ := harmonicSecondOrderError m - harmonicSecondOrderError d
  have hdecomp := nullCenterLeading_eq_elementary_add_remainders h hstrict
  have hid : nullCenterLeading m p -
      elementaryNullCenterReal (m : ℝ) (p : ℝ) = rS + rE + rQ := by
    dsimp [rS, rE, rQ, d]
    rw [hdecomp]
    ring
  have hrS : |rS| ≤ 1 / (12 * (d : ℝ)) := by
    dsimp [rS]
    exact abs_log_stirlingSeq_sub_le_inv_gap hdpos hdm
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
  have hcastdm : (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdm
  have hInv : 1 / (m : ℝ) ≤ 1 / (d : ℝ) := by gcongr
  have hrE0 : 0 ≤ rE := by
    dsimp [rE]
    have : 1 / (2 * (m : ℝ)) ≤ 1 / (2 * (d : ℝ)) := by gcongr
    linarith
  have hrE : |rE| ≤ 1 / (2 * (d : ℝ)) := by
    rw [abs_of_nonneg hrE0]
    dsimp [rE]
    have : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
    linarith
  have hantiQ : Antitone harmonicSecondOrderError :=
    antitone_nat_of_succ_le fun n ↦ by
      by_cases hn : n = 0
      · subst n
        have hq1 := harmonicSecondOrderError_nonneg (show 0 < 1 by omega)
        unfold harmonicSecondOrderError
        norm_num at hq1 ⊢
      · simpa [Nat.succ_eq_add_one] using
          harmonicSecondOrderError_antitone_step (Nat.pos_of_ne_zero hn)
  have hqmle : harmonicSecondOrderError m ≤ harmonicSecondOrderError d :=
    hantiQ hdm
  have hqm0 := harmonicSecondOrderError_nonneg hmpos
  have hqd0 := harmonicSecondOrderError_nonneg hdpos
  have hqd := harmonicSecondOrderError_le_inv_sq hdpos
  have hrQ : |rQ| ≤ 1 / (d : ℝ) ^ 2 := by
    dsimp [rQ]
    rw [abs_of_nonpos (sub_nonpos.mpr hqmle), neg_sub]
    linarith
  rw [hid]
  calc
    |rS + rE + rQ| ≤ |rS + rE| + |rQ| := abs_add_le (rS + rE) rQ
    _ ≤ (|rS| + |rE|) + |rQ| := by
      gcongr
      exact abs_add_le rS rE
    _ ≤ 1 / (12 * (d : ℝ)) + 1 / (2 * (d : ℝ)) +
        1 / (d : ℝ) ^ 2 := by linarith
    _ ≤ 2 / (d : ℝ) := by
      have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
      field_simp [hdR.ne']
      nlinarith

/-- Lemma E.1, centering half: a completely explicit finite uniform bound.
It covers fixed gaps as well as all growing-gap and dilute regimes. -/
theorem abs_nullCenterDigammaSeries_sub_elementaryNullCenterReal_le_inv_gap
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    |nullCenterDigammaSeries m p -
        elementaryNullCenterReal (m : ℝ) (p : ℝ)| ≤
      42 / ((m - p : ℕ) : ℝ) := by
  have hfirst :=
    abs_nullCenterDigammaSeries_sub_nullCenterLeading_le_inv_gap h hstrict
  have hsecond :=
    abs_nullCenterLeading_sub_elementaryNullCenterReal_le_inv_gap h hstrict
  calc
    |nullCenterDigammaSeries m p -
        elementaryNullCenterReal (m : ℝ) (p : ℝ)| =
      |(nullCenterDigammaSeries m p - nullCenterLeading m p) +
        (nullCenterLeading m p -
          elementaryNullCenterReal (m : ℝ) (p : ℝ))| := by ring_nf
    _ ≤ |nullCenterDigammaSeries m p - nullCenterLeading m p| +
        |nullCenterLeading m p -
          elementaryNullCenterReal (m : ℝ) (p : ℝ)| := abs_add_le _ _
    _ ≤ 40 / ((m - p : ℕ) : ℝ) +
        2 / ((m - p : ℕ) : ℝ) := add_le_add hfirst hsecond
    _ = 42 / ((m - p : ℕ) : ℝ) := by ring

end

end LogdetLean
