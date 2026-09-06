import LogdetLean.Coherence.MarkedPoissonVoid
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Integration
/-!
# Uniform factors for the Poisson void Stein solution

The recursive solution in `MarkedPoissonVoid` has the integral form

`f_lambda (n + 1) = integral_0^1 exp (-lambda t) t^n dt`.

This representation makes positivity and the sharp elementary uniform bound
`|f_lambda n| <= min 1 (1 / lambda)` transparent.  It also bounds every
discrete increment by the same factor.  The second half of the file uses
these estimates to turn the five-channel marked decomposition into an
Arratia--Goldstein--Gordon-style local-neighborhood estimate.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Interval

/-- Integral factor representing the positive-index Poisson void Stein
solution. -/
def poissonVoidIntegralFactor (lambda : ℝ) (n : ℕ) : ℝ :=
  ∫ t : ℝ in 0..1, Real.exp (-lambda * t) * t ^ n

theorem continuous_poissonVoidIntegralFactor_integrand
    (lambda : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ ↦ Real.exp (-lambda * t) * t ^ n) := by
  fun_prop

theorem intervalIntegrable_poissonVoidIntegralFactor
    (lambda : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (-lambda * t) * t ^ n) volume 0 1 :=
  (continuous_poissonVoidIntegralFactor_integrand lambda n).intervalIntegrable 0 1

theorem poissonVoidIntegralFactor_nonneg
    (lambda : ℝ) (n : ℕ) :
    0 ≤ poissonVoidIntegralFactor lambda n := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.1 n)

theorem poissonVoidIntegralFactor_le_zero
    (lambda : ℝ) (n : ℕ) :
    poissonVoidIntegralFactor lambda n ≤ poissonVoidIntegralFactor lambda 0 := by
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact intervalIntegrable_poissonVoidIntegralFactor lambda n
  · exact intervalIntegrable_poissonVoidIntegralFactor lambda 0
  · intro t ht
    have hpow : t ^ n ≤ (1 : ℝ) := pow_le_one₀ ht.1 ht.2
    simpa using mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le

theorem poissonVoidIntegralFactor_zero
    {lambda : ℝ} (hlambda : lambda ≠ 0) :
    poissonVoidIntegralFactor lambda 0 =
      (1 - Real.exp (-lambda)) / lambda := by
  have hderiv (t : ℝ) :
      HasDerivAt
        (fun s : ℝ ↦ (-1 / lambda) * Real.exp (-lambda * s))
        (Real.exp (-lambda * t)) t := by
    have hlin : HasDerivAt (fun s : ℝ ↦ -lambda * s) (-lambda) t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-lambda)
    have hexp := hlin.exp
    have hcoefficient :
        (-1 / lambda) * (Real.exp (-lambda * t) * -lambda) =
          Real.exp (-lambda * t) := by
      field_simp
    exact (hexp.const_mul (-1 / lambda)).congr_deriv hcoefficient
  have hint := intervalIntegrable_poissonVoidIntegralFactor lambda 0
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ ↦ (-1 / lambda) * Real.exp (-lambda * s))
    (f' := fun s : ℝ ↦ Real.exp (-lambda * s))
    (fun t _ht ↦ hderiv t)
    (by simpa using hint)
  calc
    poissonVoidIntegralFactor lambda 0 =
        ∫ t : ℝ in 0..1, Real.exp (-lambda * t) := by
          simp [poissonVoidIntegralFactor]
    _ = (-1 / lambda) * Real.exp (-lambda * 1) -
        (-1 / lambda) * Real.exp (-lambda * 0) := hFTC
    _ = (1 - Real.exp (-lambda)) / lambda := by
      field_simp
      simp
      ring

/-- Integration-by-parts recurrence for the integral factors. -/
theorem poissonVoidIntegralFactor_succ_recurrence
    (lambda : ℝ) (n : ℕ) :
    lambda * poissonVoidIntegralFactor lambda (n + 1) =
      (n + 1 : ℕ) * poissonVoidIntegralFactor lambda n -
        Real.exp (-lambda) := by
  have hu (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ s ^ (n + 1))
        ((n + 1 : ℕ) * t ^ n) t := by
    simpa using (hasDerivAt_pow (n + 1) t)
  have hv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ Real.exp (-lambda * s))
        (-lambda * Real.exp (-lambda * t)) t := by
    have hlin : HasDerivAt (fun s : ℝ ↦ -lambda * s) (-lambda) t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-lambda)
    have hexp := hlin.exp
    apply hexp.congr_deriv
    ring
  have huInt : IntervalIntegrable
      (fun t : ℝ ↦ (n + 1 : ℕ) * t ^ n) volume 0 1 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ ↦ (n + 1 : ℕ) * t ^ n)).intervalIntegrable 0 1
  have hvInt : IntervalIntegrable
      (fun t : ℝ ↦ -lambda * Real.exp (-lambda * t)) volume 0 1 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ ↦ -lambda * Real.exp (-lambda * t))).intervalIntegrable 0 1
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (u := fun t : ℝ ↦ t ^ (n + 1))
    (u' := fun t : ℝ ↦ (n + 1 : ℕ) * t ^ n)
    (v := fun t : ℝ ↦ Real.exp (-lambda * t))
    (v' := fun t : ℝ ↦ -lambda * Real.exp (-lambda * t))
    (fun t _ht ↦ hu t) (fun t _ht ↦ hv t) huInt hvInt
  have hleft :
      (∫ t : ℝ in 0..1,
        t ^ (n + 1) * (-lambda * Real.exp (-lambda * t))) =
        -lambda * poissonVoidIntegralFactor lambda (n + 1) := by
    rw [show (fun t : ℝ ↦
        t ^ (n + 1) * (-lambda * Real.exp (-lambda * t))) =
        fun t : ℝ ↦ -lambda *
          (Real.exp (-lambda * t) * t ^ (n + 1)) by
            funext t
            ring]
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hright :
      (∫ t : ℝ in 0..1,
        ((n + 1 : ℕ) * t ^ n) * Real.exp (-lambda * t)) =
        (n + 1 : ℕ) * poissonVoidIntegralFactor lambda n := by
    rw [show (fun t : ℝ ↦
        ((n + 1 : ℕ) * t ^ n) * Real.exp (-lambda * t)) =
        fun t : ℝ ↦ (n + 1 : ℕ) *
          (Real.exp (-lambda * t) * t ^ n) by
            funext t
            ring]
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hrec :
      -lambda * poissonVoidIntegralFactor lambda (n + 1) =
        Real.exp (-lambda) -
          (n + 1 : ℕ) * poissonVoidIntegralFactor lambda n := by
    rw [← hleft, ← hright]
    simpa using hparts
  linarith

/-- Integral representation of the recursive Stein solution at every
positive index. -/
theorem poissonVoidStein_succ_eq_integralFactor
    {lambda : ℝ} (hlambda : lambda ≠ 0) (n : ℕ) :
    poissonVoidStein lambda (n + 1) =
      poissonVoidIntegralFactor lambda n := by
  induction n with
  | zero =>
      rw [poissonVoidStein_succ, poissonVoidIntegralFactor_zero hlambda]
      simp [markedVoidIndicator]
  | succ n ih =>
      rw [poissonVoidStein_succ, ih]
      simp only [markedVoidIndicator, Nat.succ_ne_zero, if_false]
      apply (div_eq_iff hlambda).2
      simpa [mul_comm] using
        (poissonVoidIntegralFactor_succ_recurrence lambda n).symm

/-- The void Stein solution is nonnegative for positive intensity. -/
theorem poissonVoidStein_nonneg
    {lambda : ℝ} (hlambda : 0 < lambda) (n : ℕ) :
    0 ≤ poissonVoidStein lambda n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [poissonVoidStein_succ_eq_integralFactor hlambda.ne']
      exact poissonVoidIntegralFactor_nonneg lambda n

/-- Every value is bounded by the first positive value. -/
theorem poissonVoidStein_le_first
    {lambda : ℝ} (hlambda : 0 < lambda) (n : ℕ) :
    poissonVoidStein lambda n ≤ poissonVoidStein lambda 1 := by
  cases n with
  | zero =>
      simpa using poissonVoidStein_nonneg hlambda 1
  | succ n =>
      rw [show 1 = 0 + 1 by omega,
        poissonVoidStein_succ_eq_integralFactor hlambda.ne',
        poissonVoidStein_succ_eq_integralFactor hlambda.ne']
      exact poissonVoidIntegralFactor_le_zero lambda n

/-- The first integral factor is at most one. -/
theorem poissonVoidIntegralFactor_zero_le_one
    {lambda : ℝ} (hlambda : 0 < lambda) :
    poissonVoidIntegralFactor lambda 0 ≤ 1 := by
  rw [poissonVoidIntegralFactor_zero hlambda.ne']
  apply (div_le_one hlambda).2
  have hexp := Real.add_one_le_exp (-lambda)
  linarith

/-- The first integral factor is also at most `1 / lambda`. -/
theorem poissonVoidIntegralFactor_zero_le_inv
    {lambda : ℝ} (hlambda : 0 < lambda) :
    poissonVoidIntegralFactor lambda 0 ≤ 1 / lambda := by
  rw [poissonVoidIntegralFactor_zero hlambda.ne']
  apply (div_le_div_iff_of_pos_right hlambda).2
  linarith [Real.exp_pos (-lambda)]

/-- Sharp elementary uniform factor for the void Stein solution. -/
theorem abs_poissonVoidStein_le_min
    {lambda : ℝ} (hlambda : 0 < lambda) (n : ℕ) :
    |poissonVoidStein lambda n| ≤ min 1 (1 / lambda) := by
  rw [abs_of_nonneg (poissonVoidStein_nonneg hlambda n)]
  apply (poissonVoidStein_le_first hlambda n).trans
  rw [show 1 = 0 + 1 by omega,
    poissonVoidStein_succ_eq_integralFactor hlambda.ne']
  exact le_min
    (poissonVoidIntegralFactor_zero_le_one hlambda)
    (poissonVoidIntegralFactor_zero_le_inv hlambda)

/-- Every discrete increment has the same uniform factor. -/
theorem abs_poissonVoidStein_succ_sub_le_min
    {lambda : ℝ} (hlambda : 0 < lambda) (n : ℕ) :
    |poissonVoidStein lambda (n + 1) - poissonVoidStein lambda n| ≤
      min 1 (1 / lambda) := by
  have hn0 := poissonVoidStein_nonneg hlambda n
  have hs0 := poissonVoidStein_nonneg hlambda (n + 1)
  have hn := abs_poissonVoidStein_le_min hlambda n
  have hs := abs_poissonVoidStein_le_min hlambda (n + 1)
  rw [abs_of_nonneg hn0] at hn
  rw [abs_of_nonneg hs0] at hs
  rw [abs_le]
  constructor <;> linarith

/-- Telescoping a uniform adjacent-increment bound over a finite number of
integer steps. -/
theorem abs_sub_le_nat_mul_of_step
    {f : ℕ → ℝ} {c : ℝ}
    (hstep : ∀ n, |f (n + 1) - f n| ≤ c) (a d : ℕ) :
    |f (a + d) - f a| ≤ (d : ℝ) * c := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show a + (d + 1) = (a + d) + 1 by omega]
      calc
        |f ((a + d) + 1) - f a| =
            |(f ((a + d) + 1) - f (a + d)) +
              (f (a + d) - f a)| := by ring_nf
        _ ≤ |f ((a + d) + 1) - f (a + d)| +
            |f (a + d) - f a| := abs_add_le _ _
        _ ≤ c + (d : ℝ) * c := add_le_add (hstep (a + d)) ih
        _ = ((d + 1 : ℕ) : ℝ) * c := by
          push_cast
          ring

/-- Multi-step Lipschitz estimate for the void Stein solution. -/
theorem abs_poissonVoidStein_add_sub_le
    {lambda : ℝ} (hlambda : 0 < lambda) (a d : ℕ) :
    |poissonVoidStein lambda (a + d) - poissonVoidStein lambda a| ≤
      (d : ℝ) * min 1 (1 / lambda) :=
  abs_sub_le_nat_mul_of_step
    (abs_poissonVoidStein_succ_sub_le_min hlambda) a d

/-- The outside-neighborhood event count is measurable. -/
theorem measurable_markedOutsideNeighborhoodCount
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (i : I) :
    Measurable (markedOutsideNeighborhoodCount A B i) := by
  unfold markedOutsideNeighborhoodCount
  apply Finset.measurable_sum Finset.univ
  intro j _hj
  by_cases hji : j ∈ B i
  · simp [hji]
  · simpa [hji] using measurable_bernoulliEventIndicator (hA j)

/-- The inside-neighborhood count is the direct sum over `B i`. -/
theorem markedNeighborhoodCount_eq_sum
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega) :
    markedNeighborhoodCount A B i omega =
      ∑ j ∈ B i, bernoulliEventIndicator (A j) omega := by
  classical
  simp [markedNeighborhoodCount]

/-- Local count with the distinguished event removed. -/
def markedReducedNeighborhoodCount
    {I Omega : Type*} [DecidableEq I]
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega) : ℕ :=
  ∑ j ∈ (B i).erase i, bernoulliEventIndicator (A j) omega

/-- If `i` belongs to its own neighborhood, the inside count splits into
the `i` indicator and the reduced-neighborhood count. -/
theorem markedNeighborhoodCount_eq_indicator_add_reduced
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega)
    (hiB : i ∈ B i) :
    markedNeighborhoodCount A B i omega =
      bernoulliEventIndicator (A i) omega +
        markedReducedNeighborhoodCount A B i omega := by
  rw [markedNeighborhoodCount_eq_sum]
  unfold markedReducedNeighborhoodCount
  simpa [add_comm] using
    (Finset.sum_erase_add (B i)
      (fun j ↦ bernoulliEventIndicator (A j) omega) hiB).symm

/-- On occurrence of event `i`, the full count is the outside count, one,
and the reduced local count. -/
theorem markedBernoulliCount_eq_outside_add_one_add_reduced
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega)
    (hiB : i ∈ B i) (homega : omega ∈ A i) :
    markedBernoulliCount A omega =
      markedOutsideNeighborhoodCount A B i omega + 1 +
        markedReducedNeighborhoodCount A B i omega := by
  have hpartition := markedOutside_add_neighborhood_eq_count A B i omega
  rw [markedNeighborhoodCount_eq_indicator_add_reduced A B i omega hiB,
    bernoulliEventIndicator_of_mem homega] at hpartition
  omega

/-- Forward total-count replacement costs one Stein increment per local
event. -/
theorem abs_poissonVoidStein_count_succ_sub_outside_succ_le
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    {lambda : ℝ} (hlambda : 0 < lambda)
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega) :
    |poissonVoidStein lambda (markedBernoulliCount A omega + 1) -
        poissonVoidStein lambda
          (markedOutsideNeighborhoodCount A B i omega + 1)| ≤
      (markedNeighborhoodCount A B i omega : ℝ) *
        min 1 (1 / lambda) := by
  have hpartition := markedOutside_add_neighborhood_eq_count A B i omega
  have hindex : markedBernoulliCount A omega + 1 =
      (markedOutsideNeighborhoodCount A B i omega + 1) +
        markedNeighborhoodCount A B i omega := by omega
  rw [hindex]
  exact abs_poissonVoidStein_add_sub_le hlambda
    (markedOutsideNeighborhoodCount A B i omega + 1)
    (markedNeighborhoodCount A B i omega)

/-- Backward count replacement on event `i` costs one increment per other
active event in its neighborhood. -/
theorem abs_poissonVoidStein_outside_succ_sub_count_le
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    {lambda : ℝ} (hlambda : 0 < lambda)
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega)
    (hiB : i ∈ B i) (homega : omega ∈ A i) :
    |poissonVoidStein lambda
          (markedOutsideNeighborhoodCount A B i omega + 1) -
        poissonVoidStein lambda (markedBernoulliCount A omega)| ≤
      (markedReducedNeighborhoodCount A B i omega : ℝ) *
        min 1 (1 / lambda) := by
  have hcount := markedBernoulliCount_eq_outside_add_one_add_reduced
    A B i omega hiB homega
  rw [hcount, abs_sub_comm]
  exact abs_poissonVoidStein_add_sub_le hlambda
    (markedOutsideNeighborhoodCount A B i omega + 1)
    (markedReducedNeighborhoodCount A B i omega)

/-- A real Bernoulli indicator integrates to the event probability. -/
theorem integral_real_bernoulliEventIndicator
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {A : Set Omega} (hA : MeasurableSet A) :
    (∫ omega, (bernoulliEventIndicator A omega : ℝ) ∂mu) = mu.real A := by
  have hfun : (fun omega ↦ (bernoulliEventIndicator A omega : ℝ)) =
      A.indicator (1 : Omega → ℝ) := by
    funext omega
    by_cases homega : omega ∈ A <;>
      simp [bernoulliEventIndicator, homega]
  rw [hfun]
  exact integral_indicator_one (μ := mu) hA

/-- Product of two real Bernoulli indicators integrates to the probability
of their intersection. -/
theorem integral_real_bernoulliEventIndicator_mul
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {A C : Set Omega}
    (hA : MeasurableSet A) (hC : MeasurableSet C) :
    (∫ omega, (bernoulliEventIndicator A omega : ℝ) *
        (bernoulliEventIndicator C omega : ℝ) ∂mu) =
      mu.real (A ∩ C) := by
  have hfun : (fun omega ↦ (bernoulliEventIndicator A omega : ℝ) *
      (bernoulliEventIndicator C omega : ℝ)) =
      (A ∩ C).indicator (1 : Omega → ℝ) := by
    funext omega
    by_cases hAo : omega ∈ A <;> by_cases hCo : omega ∈ C <;>
      simp [bernoulliEventIndicator, hAo, hCo]
  rw [hfun]
  exact integral_indicator_one (μ := mu) (hA.inter hC)

/-- The far-field channel has zero expectation when the Bernoulli indicator
is independent of the evaluated leave-one factor. -/
theorem integral_centeredBernoulli_mul_eq_zero_of_indepFun
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A : Set Omega} (hA : MeasurableSet A)
    (Y : Omega → ℝ) (hY : Integrable Y mu)
    (hindep : IndepFun
      (fun omega ↦ (bernoulliEventIndicator A omega : ℝ)) Y mu) :
    (∫ omega, (mu.real A - (bernoulliEventIndicator A omega : ℝ)) *
        Y omega ∂mu) = 0 := by
  have hxiMeas : AEStronglyMeasurable
      (fun omega ↦ (bernoulliEventIndicator A omega : ℝ)) mu :=
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_bernoulliEventIndicator hA)).aestronglyMeasurable
  have hxiBound : ∀ᵐ omega ∂mu,
      ‖(bernoulliEventIndicator A omega : ℝ)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with omega
    rcases bernoulliEventIndicator_eq_zero_or_one A omega with h | h <;>
      simp [h]
  have hxiY : Integrable
      (fun omega ↦ (bernoulliEventIndicator A omega : ℝ) * Y omega) mu :=
    hY.bdd_mul hxiMeas hxiBound
  have hpY : Integrable (fun omega ↦ mu.real A * Y omega) mu :=
    hY.const_mul _
  calc
    (∫ omega, (mu.real A - (bernoulliEventIndicator A omega : ℝ)) *
        Y omega ∂mu) =
        (∫ omega, mu.real A * Y omega ∂mu) -
          ∫ omega, (bernoulliEventIndicator A omega : ℝ) * Y omega ∂mu := by
            rw [show (fun omega ↦
                (mu.real A - (bernoulliEventIndicator A omega : ℝ)) * Y omega) =
              fun omega ↦ mu.real A * Y omega -
                (bernoulliEventIndicator A omega : ℝ) * Y omega by
                  funext omega
                  ring,
              integral_sub hpY hxiY]
    _ = mu.real A * (∫ omega, Y omega ∂mu) -
        (∫ omega, (bernoulliEventIndicator A omega : ℝ) ∂mu) *
          ∫ omega, Y omega ∂mu := by
            rw [integral_const_mul,
              hindep.integral_fun_mul_eq_mul_integral
                hxiMeas hY.aestronglyMeasurable]
    _ = 0 := by
      rw [integral_real_bernoulliEventIndicator mu hA]
      ring

/-- Pair-valued form of the far-field cancellation.  Independence is assumed
between the Bernoulli indicator and the literal leave-one pair
`(hLeave i, WOutside i)`. -/
theorem integral_centeredBernoulli_leavePair_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A : Set Omega} (hA : MeasurableSet A)
    {lambda : ℝ} (hLeave : Omega → ℝ) (WOutside : Omega → ℕ)
    (hY : Integrable
      (fun omega ↦ hLeave omega *
        poissonVoidStein lambda (WOutside omega + 1)) mu)
    (hindep : IndepFun
      (fun omega ↦ (bernoulliEventIndicator A omega : ℝ))
      (fun omega ↦ (hLeave omega, WOutside omega)) mu) :
    (∫ omega, (mu.real A - (bernoulliEventIndicator A omega : ℝ)) *
        hLeave omega * poissonVoidStein lambda (WOutside omega + 1) ∂mu) = 0 := by
  let psi : ℝ × ℕ → ℝ := fun q ↦
    q.1 * poissonVoidStein lambda (q.2 + 1)
  have hsucc : Measurable (fun n : ℕ ↦ n + 1) :=
    measurable_of_countable _
  have hf : Measurable (poissonVoidStein lambda) :=
    measurable_of_countable _
  have hpsi : Measurable psi := by
    unfold psi
    exact measurable_fst.mul (hf.comp (hsucc.comp measurable_snd))
  have hindepY : IndepFun
      (fun omega ↦ (bernoulliEventIndicator A omega : ℝ))
      (fun omega ↦ hLeave omega *
        poissonVoidStein lambda (WOutside omega + 1)) mu := by
    simpa [psi, Function.comp_def] using hindep.comp measurable_id hpsi
  simpa [mul_assoc] using
    integral_centeredBernoulli_mul_eq_zero_of_indepFun
      hA
      (fun omega ↦ hLeave omega *
        poissonVoidStein lambda (WOutside omega + 1))
      hY hindepY

/-- Forward mark-replacement channel. -/
def markedBernoulliForwardMarkTerm
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (i : I) (omega : Omega) : ℝ :=
  mu.real (A i) * (h omega - hLeave i omega) *
    poissonVoidStein (markedBernoulliIntensity mu A)
      (markedBernoulliCount A omega + 1)

/-- Forward neighborhood-count replacement channel. -/
def markedBernoulliForwardCountTerm
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (hLeave : I → Omega → ℝ) (i : I) (omega : Omega) : ℝ :=
  mu.real (A i) * hLeave i omega *
    (poissonVoidStein (markedBernoulliIntensity mu A)
        (markedBernoulliCount A omega + 1) -
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedOutsideNeighborhoodCount A B i omega + 1))

/-- Centered far-field dependence channel. -/
def markedBernoulliFarTerm
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (hLeave : I → Omega → ℝ) (i : I) (omega : Omega) : ℝ :=
  (mu.real (A i) - (bernoulliEventIndicator (A i) omega : ℝ)) *
    hLeave i omega * poissonVoidStein (markedBernoulliIntensity mu A)
      (markedOutsideNeighborhoodCount A B i omega + 1)

/-- Backward neighborhood-count replacement channel. -/
def markedBernoulliBackwardCountTerm
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (hLeave : I → Omega → ℝ) (i : I) (omega : Omega) : ℝ :=
  (bernoulliEventIndicator (A i) omega : ℝ) * hLeave i omega *
    (poissonVoidStein (markedBernoulliIntensity mu A)
        (markedOutsideNeighborhoodCount A B i omega + 1) -
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedBernoulliCount A omega))

/-- Backward mark-restoration channel. -/
def markedBernoulliBackwardMarkTerm
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (i : I) (omega : Omega) : ℝ :=
  (bernoulliEventIndicator (A i) omega : ℝ) *
    (hLeave i omega - h omega) *
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedBernoulliCount A omega)

/-- The event-specific local error is exactly the sum of its five named
channels. -/
theorem markedBernoulliVoidLocalError_eq_fiveTerms
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (i : I) (omega : Omega) :
    markedBernoulliVoidLocalError mu A B h hLeave i omega =
      markedBernoulliForwardMarkTerm mu A h hLeave i omega +
      markedBernoulliForwardCountTerm mu A B hLeave i omega +
      markedBernoulliFarTerm mu A B hLeave i omega +
      markedBernoulliBackwardCountTerm mu A B hLeave i omega +
      markedBernoulliBackwardMarkTerm mu A h hLeave i omega := by
  rfl

/-- Integrability package for the five named channels.  Concrete bounded-mark
models discharge this routine hypothesis once and then use the AGG corollary
below. -/
def MarkedBernoulliVoidChannelsIntegrable
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ) : Prop :=
  ∀ i,
    Integrable (markedBernoulliForwardMarkTerm mu A h hLeave i) mu ∧
    Integrable (markedBernoulliForwardCountTerm mu A B hLeave i) mu ∧
    Integrable (markedBernoulliFarTerm mu A B hLeave i) mu ∧
    Integrable (markedBernoulliBackwardCountTerm mu A B hLeave i) mu ∧
    Integrable (markedBernoulliBackwardMarkTerm mu A h hLeave i) mu

/-- The `b1` local-neighborhood factor. -/
def markedPoissonBOne
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I) : ℝ :=
  ∑ i, mu.real (A i) * ∑ j ∈ B i, mu.real (A j)

/-- The `b2` local pair-occurrence factor, excluding the distinguished
event itself. -/
def markedPoissonBTwo
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I) : ℝ :=
  ∑ i, ∑ j ∈ (B i).erase i, mu.real (A i ∩ A j)

/-- Two-sided mark-replacement cost. -/
def markedPoissonMarkReplacement
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ) : ℝ :=
  ∑ i, (
    mu.real (A i) * (∫ omega, |h omega - hLeave i omega| ∂mu) +
      (∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
        |h omega - hLeave i omega| ∂mu))

/-- The inside-count expectation is the sum of the local event
probabilities. -/
theorem integral_markedNeighborhoodCount
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (i : I) :
    (∫ omega, (markedNeighborhoodCount A B i omega : ℝ) ∂mu) =
      ∑ j ∈ B i, mu.real (A j) := by
  have hfun : (fun omega ↦ (markedNeighborhoodCount A B i omega : ℝ)) =
      fun omega ↦ ∑ j ∈ B i,
        (bernoulliEventIndicator (A j) omega : ℝ) := by
    funext omega
    rw [markedNeighborhoodCount_eq_sum]
    simp
  rw [hfun, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _hj
    exact integral_real_bernoulliEventIndicator mu (hA j)
  · intro j _hj
    apply Integrable.of_bound
      (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
        (measurable_bernoulliEventIndicator (hA j))).aestronglyMeasurable) 1
    filter_upwards [] with omega
    rcases bernoulliEventIndicator_eq_zero_or_one (A j) omega with h | h <;>
      simp [h]

/-- The indicator times the reduced local count integrates to the sum of
local pair probabilities. -/
theorem integral_indicator_mul_markedReducedNeighborhoodCount
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (i : I) :
    (∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
        (markedReducedNeighborhoodCount A B i omega : ℝ) ∂mu) =
      ∑ j ∈ (B i).erase i, mu.real (A i ∩ A j) := by
  have hfun : (fun omega ↦ (bernoulliEventIndicator (A i) omega : ℝ) *
      (markedReducedNeighborhoodCount A B i omega : ℝ)) =
      fun omega ↦ ∑ j ∈ (B i).erase i,
        (bernoulliEventIndicator (A i) omega : ℝ) *
          (bernoulliEventIndicator (A j) omega : ℝ) := by
    funext omega
    unfold markedReducedNeighborhoodCount
    simp [Finset.mul_sum]
  rw [hfun, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _hj
    exact integral_real_bernoulliEventIndicator_mul mu (hA i) (hA j)
  · intro j _hj
    have hmeas : Measurable (fun omega ↦
        (bernoulliEventIndicator (A i) omega : ℝ) *
          (bernoulliEventIndicator (A j) omega : ℝ)) :=
      ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
        (measurable_bernoulliEventIndicator (hA i))).mul
      ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
        (measurable_bernoulliEventIndicator (hA j)))
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with omega
    rcases bernoulliEventIndicator_eq_zero_or_one (A i) omega with hi | hi <;>
      rcases bernoulliEventIndicator_eq_zero_or_one (A j) omega with hj | hj <;>
        simp [hi, hj]

/-- A real event indicator is integrable under a finite measure. -/
theorem integrable_real_bernoulliEventIndicator
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {A : Set Omega} (hA : MeasurableSet A) :
    Integrable (fun omega ↦ (bernoulliEventIndicator A omega : ℝ)) mu := by
  apply Integrable.of_bound
    (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_bernoulliEventIndicator hA)).aestronglyMeasurable) 1
  filter_upwards [] with omega
  rcases bernoulliEventIndicator_eq_zero_or_one A omega with h | h <;>
    simp [h]

/-- The real local-neighborhood count is integrable. -/
theorem integrable_markedNeighborhoodCount_real
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (i : I) :
    Integrable (fun omega ↦ (markedNeighborhoodCount A B i omega : ℝ)) mu := by
  have hfun : (fun omega ↦ (markedNeighborhoodCount A B i omega : ℝ)) =
      fun omega ↦ ∑ j ∈ B i,
        (bernoulliEventIndicator (A j) omega : ℝ) := by
    funext omega
    rw [markedNeighborhoodCount_eq_sum]
    simp
  rw [hfun]
  exact integrable_finsetSum (B i) fun j _hj ↦
    integrable_real_bernoulliEventIndicator (hA j)

/-- The product of the distinguished indicator and the reduced local count is
integrable. -/
theorem integrable_indicator_mul_markedReducedNeighborhoodCount
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (i : I) :
    Integrable (fun omega ↦ (bernoulliEventIndicator (A i) omega : ℝ) *
      (markedReducedNeighborhoodCount A B i omega : ℝ)) mu := by
  have hfun : (fun omega ↦ (bernoulliEventIndicator (A i) omega : ℝ) *
      (markedReducedNeighborhoodCount A B i omega : ℝ)) =
      fun omega ↦ ∑ j ∈ (B i).erase i,
        (bernoulliEventIndicator (A i) omega : ℝ) *
          (bernoulliEventIndicator (A j) omega : ℝ) := by
    funext omega
    unfold markedReducedNeighborhoodCount
    simp [Finset.mul_sum]
  rw [hfun]
  apply integrable_finsetSum ((B i).erase i)
  intro j _hj
  have hbound : ∀ᵐ omega ∂mu,
      ‖(bernoulliEventIndicator (A j) omega : ℝ)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with omega
    rcases bernoulliEventIndicator_eq_zero_or_one (A j) omega with h | h <;>
      simp [h]
  simpa [Function.comp_def, mul_comm] using
    (integrable_real_bernoulliEventIndicator (hA i)).bdd_mul
      (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
        (measurable_bernoulliEventIndicator (hA j))).aestronglyMeasurable)
      hbound

/-- The uniform Stein factor is nonnegative at positive intensity. -/
theorem poissonVoidSteinFactor_nonneg
    {lambda : ℝ} (hlambda : 0 < lambda) :
    0 ≤ min 1 (1 / lambda) := by
  exact le_min (by norm_num) (by positivity)

/-- Pointwise estimate for the forward mark-replacement channel. -/
theorem abs_markedBernoulliForwardMarkTerm_le
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    (i : I) (omega : Omega) :
    |markedBernoulliForwardMarkTerm mu A h hLeave i omega| ≤
      min 1 (1 / markedBernoulliIntensity mu A) *
        (mu.real (A i) * |h omega - hLeave i omega|) := by
  unfold markedBernoulliForwardMarkTerm
  rw [abs_mul, abs_mul, abs_of_nonneg (measureReal_nonneg)]
  calc
    mu.real (A i) * |h omega - hLeave i omega| *
          |poissonVoidStein (markedBernoulliIntensity mu A)
            (markedBernoulliCount A omega + 1)| ≤
        mu.real (A i) * |h omega - hLeave i omega| *
          min 1 (1 / markedBernoulliIntensity mu A) :=
      mul_le_mul_of_nonneg_left
        (abs_poissonVoidStein_le_min hlambda _)
        (mul_nonneg measureReal_nonneg (abs_nonneg _))
    _ = min 1 (1 / markedBernoulliIntensity mu A) *
        (mu.real (A i) * |h omega - hLeave i omega|) := by ring

/-- Pointwise estimate for the forward local-count replacement channel. -/
theorem abs_markedBernoulliForwardCountTerm_le
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    {H : ℝ} (hH : 0 ≤ H)
    (hLeaveBound : ∀ i omega, |hLeave i omega| ≤ H)
    (i : I) (omega : Omega) :
    |markedBernoulliForwardCountTerm mu A B hLeave i omega| ≤
      min 1 (1 / markedBernoulliIntensity mu A) * H *
        (mu.real (A i) * (markedNeighborhoodCount A B i omega : ℝ)) := by
  unfold markedBernoulliForwardCountTerm
  rw [abs_mul, abs_mul, abs_of_nonneg (measureReal_nonneg)]
  have hcount :=
    abs_poissonVoidStein_count_succ_sub_outside_succ_le
      hlambda A B i omega
  calc
    mu.real (A i) * |hLeave i omega| *
          |poissonVoidStein (markedBernoulliIntensity mu A)
                (markedBernoulliCount A omega + 1) -
            poissonVoidStein (markedBernoulliIntensity mu A)
                (markedOutsideNeighborhoodCount A B i omega + 1)| ≤
        mu.real (A i) * H *
          ((markedNeighborhoodCount A B i omega : ℝ) *
            min 1 (1 / markedBernoulliIntensity mu A)) := by
      gcongr
      exact hLeaveBound i omega
    _ = min 1 (1 / markedBernoulliIntensity mu A) * H *
        (mu.real (A i) * (markedNeighborhoodCount A B i omega : ℝ)) := by
      ring

/-- Pointwise estimate for the backward local-count replacement channel. -/
theorem abs_markedBernoulliBackwardCountTerm_le
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    {H : ℝ} (hH : 0 ≤ H)
    (hLeaveBound : ∀ i omega, |hLeave i omega| ≤ H)
    (hiB : ∀ i, i ∈ B i) (i : I) (omega : Omega) :
    |markedBernoulliBackwardCountTerm mu A B hLeave i omega| ≤
      min 1 (1 / markedBernoulliIntensity mu A) * H *
        ((bernoulliEventIndicator (A i) omega : ℝ) *
          (markedReducedNeighborhoodCount A B i omega : ℝ)) := by
  by_cases homega : omega ∈ A i
  · rw [markedBernoulliBackwardCountTerm,
      bernoulliEventIndicator_of_mem homega]
    norm_num
    have hcount := abs_poissonVoidStein_outside_succ_sub_count_le
      hlambda A B i omega (hiB i) homega
    calc
      |hLeave i omega| *
            |poissonVoidStein (markedBernoulliIntensity mu A)
                  (markedOutsideNeighborhoodCount A B i omega + 1) -
              poissonVoidStein (markedBernoulliIntensity mu A)
                  (markedBernoulliCount A omega)| ≤
          H * ((markedReducedNeighborhoodCount A B i omega : ℝ) *
            min 1 (1 / markedBernoulliIntensity mu A)) := by
        gcongr
        exact hLeaveBound i omega
      _ = min 1 ((markedBernoulliIntensity mu A)⁻¹) * H *
          (markedReducedNeighborhoodCount A B i omega : ℝ) := by
        simp only [one_div]
        ring
  · rw [markedBernoulliBackwardCountTerm,
      bernoulliEventIndicator_of_not_mem homega]
    norm_num

/-- Pointwise estimate for the backward mark-restoration channel. -/
theorem abs_markedBernoulliBackwardMarkTerm_le
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    (i : I) (omega : Omega) :
    |markedBernoulliBackwardMarkTerm mu A h hLeave i omega| ≤
      min 1 (1 / markedBernoulliIntensity mu A) *
        ((bernoulliEventIndicator (A i) omega : ℝ) *
          |h omega - hLeave i omega|) := by
  unfold markedBernoulliBackwardMarkTerm
  rw [abs_mul, abs_mul, abs_sub_comm]
  have hxi : 0 ≤ (bernoulliEventIndicator (A i) omega : ℝ) := by positivity
  rw [abs_of_nonneg hxi]
  calc
    (bernoulliEventIndicator (A i) omega : ℝ) *
          |h omega - hLeave i omega| *
          |poissonVoidStein (markedBernoulliIntensity mu A)
            (markedBernoulliCount A omega)| ≤
        (bernoulliEventIndicator (A i) omega : ℝ) *
          |h omega - hLeave i omega| *
          min 1 (1 / markedBernoulliIntensity mu A) :=
      mul_le_mul_of_nonneg_left
        (abs_poissonVoidStein_le_min hlambda _)
        (mul_nonneg hxi (abs_nonneg _))
    _ = min 1 (1 / markedBernoulliIntensity mu A) *
        ((bernoulliEventIndicator (A i) omega : ℝ) *
          |h omega - hLeave i omega|) := by ring

/-- Integrated forward mark-replacement estimate. -/
theorem abs_integral_markedBernoulliForwardMarkTerm_le
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A : I → Set Omega}
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    (hdiff : ∀ i, Integrable (fun omega ↦ |h omega - hLeave i omega|) mu)
    (i : I) :
    |∫ omega, markedBernoulliForwardMarkTerm mu A h hLeave i omega ∂mu| ≤
      min 1 (1 / markedBernoulliIntensity mu A) *
        (mu.real (A i) *
          ∫ omega, |h omega - hLeave i omega| ∂mu) := by
  let c := min 1 (1 / markedBernoulliIntensity mu A)
  have hrhs : Integrable (fun omega ↦
      c * (mu.real (A i) * |h omega - hLeave i omega|)) mu :=
    ((hdiff i).const_mul (mu.real (A i))).const_mul c
  calc
    |∫ omega, markedBernoulliForwardMarkTerm mu A h hLeave i omega ∂mu| =
        ‖∫ omega, markedBernoulliForwardMarkTerm mu A h hLeave i omega ∂mu‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ omega, c *
          (mu.real (A i) * |h omega - hLeave i omega|) ∂mu := by
      apply norm_integral_le_of_norm_le hrhs
      filter_upwards [] with omega
      rw [Real.norm_eq_abs]
      exact abs_markedBernoulliForwardMarkTerm_le
        mu A h hLeave hlambda i omega
    _ = min 1 (1 / markedBernoulliIntensity mu A) *
        (mu.real (A i) *
          ∫ omega, |h omega - hLeave i omega| ∂mu) := by
      simp only [c, integral_const_mul]

/-- Integrated forward neighborhood-count estimate. -/
theorem abs_integral_markedBernoulliForwardCountTerm_le
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    {H : ℝ} (hH : 0 ≤ H)
    (hLeaveBound : ∀ i omega, |hLeave i omega| ≤ H)
    (i : I) :
    |∫ omega,
        markedBernoulliForwardCountTerm mu A B hLeave i omega ∂mu| ≤
      min 1 (1 / markedBernoulliIntensity mu A) * H *
        (mu.real (A i) * ∑ j ∈ B i, mu.real (A j)) := by
  let c := min 1 (1 / markedBernoulliIntensity mu A)
  have hcount := integrable_markedNeighborhoodCount_real
    (mu := mu) (A := A) hA B i
  have hrhs : Integrable (fun omega ↦
      c * H * (mu.real (A i) *
        (markedNeighborhoodCount A B i omega : ℝ))) mu := by
    fun_prop
  calc
    |∫ omega,
        markedBernoulliForwardCountTerm mu A B hLeave i omega ∂mu| =
        ‖∫ omega,
          markedBernoulliForwardCountTerm mu A B hLeave i omega ∂mu‖ := by
            rw [Real.norm_eq_abs]
    _ ≤ ∫ omega, c * H *
          (mu.real (A i) *
            (markedNeighborhoodCount A B i omega : ℝ)) ∂mu := by
      apply norm_integral_le_of_norm_le hrhs
      filter_upwards [] with omega
      rw [Real.norm_eq_abs]
      exact abs_markedBernoulliForwardCountTerm_le
        mu A B hLeave hlambda hH hLeaveBound i omega
    _ = min 1 (1 / markedBernoulliIntensity mu A) * H *
        (mu.real (A i) * ∑ j ∈ B i, mu.real (A j)) := by
      simp only [c]
      rw [show (fun omega ↦
          min 1 (1 / markedBernoulliIntensity mu A) * H *
            (mu.real (A i) *
              (markedNeighborhoodCount A B i omega : ℝ))) =
          fun omega ↦
            (min 1 (1 / markedBernoulliIntensity mu A) * H *
              mu.real (A i)) *
              (markedNeighborhoodCount A B i omega : ℝ) by
                funext omega
                ring,
        integral_const_mul,
        integral_markedNeighborhoodCount hA B i]
      ring

/-- Integrated backward neighborhood-count estimate. -/
theorem abs_integral_markedBernoulliBackwardCountTerm_le
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    {H : ℝ} (hH : 0 ≤ H)
    (hLeaveBound : ∀ i omega, |hLeave i omega| ≤ H)
    (hiB : ∀ i, i ∈ B i) (i : I) :
    |∫ omega,
        markedBernoulliBackwardCountTerm mu A B hLeave i omega ∂mu| ≤
      min 1 (1 / markedBernoulliIntensity mu A) * H *
        (∑ j ∈ (B i).erase i, mu.real (A i ∩ A j)) := by
  let c := min 1 (1 / markedBernoulliIntensity mu A)
  have hcount :=
    integrable_indicator_mul_markedReducedNeighborhoodCount
      (mu := mu) (A := A) hA B i
  have hrhs : Integrable (fun omega ↦ c * H *
      ((bernoulliEventIndicator (A i) omega : ℝ) *
        (markedReducedNeighborhoodCount A B i omega : ℝ))) mu := by
    fun_prop
  calc
    |∫ omega,
        markedBernoulliBackwardCountTerm mu A B hLeave i omega ∂mu| =
        ‖∫ omega,
          markedBernoulliBackwardCountTerm mu A B hLeave i omega ∂mu‖ := by
            rw [Real.norm_eq_abs]
    _ ≤ ∫ omega, c * H *
          ((bernoulliEventIndicator (A i) omega : ℝ) *
            (markedReducedNeighborhoodCount A B i omega : ℝ)) ∂mu := by
      apply norm_integral_le_of_norm_le hrhs
      filter_upwards [] with omega
      rw [Real.norm_eq_abs]
      exact abs_markedBernoulliBackwardCountTerm_le
        mu A B hLeave hlambda hH hLeaveBound hiB i omega
    _ = min 1 (1 / markedBernoulliIntensity mu A) * H *
        (∑ j ∈ (B i).erase i, mu.real (A i ∩ A j)) := by
      simp only [c]
      rw [show (fun omega ↦
          min 1 (1 / markedBernoulliIntensity mu A) * H *
            ((bernoulliEventIndicator (A i) omega : ℝ) *
              (markedReducedNeighborhoodCount A B i omega : ℝ))) =
          fun omega ↦
            (min 1 (1 / markedBernoulliIntensity mu A) * H) *
              ((bernoulliEventIndicator (A i) omega : ℝ) *
                (markedReducedNeighborhoodCount A B i omega : ℝ)) by
                  funext omega
                  ring,
        integral_const_mul,
        integral_indicator_mul_markedReducedNeighborhoodCount hA B i]

/-- Integrated backward mark-restoration estimate. -/
theorem abs_integral_markedBernoulliBackwardMarkTerm_le
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    (hdiff : ∀ i, Integrable (fun omega ↦ |h omega - hLeave i omega|) mu)
    (i : I) :
    |∫ omega, markedBernoulliBackwardMarkTerm mu A h hLeave i omega ∂mu| ≤
      min 1 (1 / markedBernoulliIntensity mu A) *
        (∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
          |h omega - hLeave i omega| ∂mu) := by
  let c := min 1 (1 / markedBernoulliIntensity mu A)
  have hxiMeas : AEStronglyMeasurable
      (fun omega ↦ (bernoulliEventIndicator (A i) omega : ℝ)) mu :=
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_bernoulliEventIndicator (hA i))).aestronglyMeasurable
  have hxiBound : ∀ᵐ omega ∂mu,
      ‖(bernoulliEventIndicator (A i) omega : ℝ)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with omega
    rcases bernoulliEventIndicator_eq_zero_or_one (A i) omega with hx | hx <;>
      simp [hx]
  have hprod : Integrable (fun omega ↦
      (bernoulliEventIndicator (A i) omega : ℝ) *
        |h omega - hLeave i omega|) mu :=
    (hdiff i).bdd_mul hxiMeas hxiBound
  have hrhs : Integrable (fun omega ↦ c *
      ((bernoulliEventIndicator (A i) omega : ℝ) *
        |h omega - hLeave i omega|)) mu := hprod.const_mul c
  calc
    |∫ omega, markedBernoulliBackwardMarkTerm mu A h hLeave i omega ∂mu| =
        ‖∫ omega, markedBernoulliBackwardMarkTerm mu A h hLeave i omega ∂mu‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ omega, c *
          ((bernoulliEventIndicator (A i) omega : ℝ) *
            |h omega - hLeave i omega|) ∂mu := by
      apply norm_integral_le_of_norm_le hrhs
      filter_upwards [] with omega
      rw [Real.norm_eq_abs]
      exact abs_markedBernoulliBackwardMarkTerm_le
        mu A h hLeave hlambda i omega
    _ = min 1 (1 / markedBernoulliIntensity mu A) *
        (∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
          |h omega - hLeave i omega| ∂mu) := by
      simp only [c, integral_const_mul]

/-- One-index AGG estimate: independence of the distinguished Bernoulli
indicator from the leave-one pair kills the far-field channel, while the four
remaining channels reduce to mark replacement and the local `b1`, `b2`
summands. -/
theorem abs_integral_markedBernoulliVoidLocalError_le_AGG
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (h : Omega → ℝ)
    (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    {H : ℝ} (hH : 0 ≤ H)
    (hLeaveBound : ∀ i omega, |hLeave i omega| ≤ H)
    (hiB : ∀ i, i ∈ B i)
    (hdiff : ∀ i, Integrable (fun omega ↦ |h omega - hLeave i omega|) mu)
    (hchannels : MarkedBernoulliVoidChannelsIntegrable mu A B h hLeave)
    (hY : ∀ i, Integrable (fun omega ↦ hLeave i omega *
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedOutsideNeighborhoodCount A B i omega + 1)) mu)
    (hindep : ∀ i, IndepFun
      (fun omega ↦ (bernoulliEventIndicator (A i) omega : ℝ))
      (fun omega ↦
        (hLeave i omega, markedOutsideNeighborhoodCount A B i omega)) mu)
    (i : I) :
    |∫ omega,
        markedBernoulliVoidLocalError mu A B h hLeave i omega ∂mu| ≤
      min 1 (1 / markedBernoulliIntensity mu A) *
        (mu.real (A i) *
            (∫ omega, |h omega - hLeave i omega| ∂mu) +
          (∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
            |h omega - hLeave i omega| ∂mu) +
          H * (mu.real (A i) * ∑ j ∈ B i, mu.real (A j) +
            ∑ j ∈ (B i).erase i, mu.real (A i ∩ A j))) := by
  rcases hchannels i with ⟨hforwardMark, hforwardCount, hfar,
    hbackwardCount, hbackwardMark⟩
  have hsplit :
      (∫ omega,
        markedBernoulliVoidLocalError mu A B h hLeave i omega ∂mu) =
        (∫ omega, markedBernoulliForwardMarkTerm mu A h hLeave i omega ∂mu) +
        (∫ omega,
          markedBernoulliForwardCountTerm mu A B hLeave i omega ∂mu) +
        (∫ omega, markedBernoulliFarTerm mu A B hLeave i omega ∂mu) +
        (∫ omega,
          markedBernoulliBackwardCountTerm mu A B hLeave i omega ∂mu) +
        (∫ omega,
          markedBernoulliBackwardMarkTerm mu A h hLeave i omega ∂mu) := by
    rw [show (fun omega ↦
        markedBernoulliVoidLocalError mu A B h hLeave i omega) =
      fun omega ↦
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega +
        markedBernoulliFarTerm mu A B hLeave i omega +
        markedBernoulliBackwardCountTerm mu A B hLeave i omega +
        markedBernoulliBackwardMarkTerm mu A h hLeave i omega by
          funext omega
          exact markedBernoulliVoidLocalError_eq_fiveTerms
            mu A B h hLeave i omega]
    have h12 := integral_add hforwardMark hforwardCount
    have h123 := integral_add (hforwardMark.add hforwardCount) hfar
    have h1234 := integral_add
      ((hforwardMark.add hforwardCount).add hfar) hbackwardCount
    have h12345 := integral_add
      (((hforwardMark.add hforwardCount).add hfar).add hbackwardCount)
      hbackwardMark
    rw [show (∫ omega,
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega +
        markedBernoulliFarTerm mu A B hLeave i omega +
        markedBernoulliBackwardCountTerm mu A B hLeave i omega +
        markedBernoulliBackwardMarkTerm mu A h hLeave i omega ∂mu) =
      (∫ omega,
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega +
        markedBernoulliFarTerm mu A B hLeave i omega +
        markedBernoulliBackwardCountTerm mu A B hLeave i omega ∂mu) +
      ∫ omega,
        markedBernoulliBackwardMarkTerm mu A h hLeave i omega ∂mu by
          simpa only [Pi.add_apply] using h12345,
      show (∫ omega,
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega +
        markedBernoulliFarTerm mu A B hLeave i omega +
        markedBernoulliBackwardCountTerm mu A B hLeave i omega ∂mu) =
      (∫ omega,
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega +
        markedBernoulliFarTerm mu A B hLeave i omega ∂mu) +
      ∫ omega,
        markedBernoulliBackwardCountTerm mu A B hLeave i omega ∂mu by
          simpa only [Pi.add_apply] using h1234,
      show (∫ omega,
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega +
        markedBernoulliFarTerm mu A B hLeave i omega ∂mu) =
      (∫ omega,
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega ∂mu) +
      ∫ omega, markedBernoulliFarTerm mu A B hLeave i omega ∂mu by
          simpa only [Pi.add_apply] using h123,
      show (∫ omega,
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega ∂mu) =
      (∫ omega, markedBernoulliForwardMarkTerm mu A h hLeave i omega ∂mu) +
      ∫ omega,
        markedBernoulliForwardCountTerm mu A B hLeave i omega ∂mu by
          simpa only [Pi.add_apply] using h12]
  have hfarzero :
      (∫ omega, markedBernoulliFarTerm mu A B hLeave i omega ∂mu) = 0 := by
    simpa [markedBernoulliFarTerm, mul_assoc] using
      (integral_centeredBernoulli_leavePair_eq_zero
        (mu := mu) (hA i)
        (lambda := markedBernoulliIntensity mu A)
        (hLeave i) (markedOutsideNeighborhoodCount A B i)
        (hY i) (hindep i))
  let a := ∫ omega,
    markedBernoulliForwardMarkTerm mu A h hLeave i omega ∂mu
  let b := ∫ omega,
    markedBernoulliForwardCountTerm mu A B hLeave i omega ∂mu
  let d := ∫ omega,
    markedBernoulliBackwardCountTerm mu A B hLeave i omega ∂mu
  let e := ∫ omega,
    markedBernoulliBackwardMarkTerm mu A h hLeave i omega ∂mu
  have htriangle : |a + b + d + e| ≤ |a| + |b| + |d| + |e| := by
    have hab := abs_add_le a b
    have habd := abs_add_le (a + b) d
    have habde := abs_add_le (a + b + d) e
    linarith
  have ha := abs_integral_markedBernoulliForwardMarkTerm_le
    (mu := mu) (A := A) h hLeave hlambda hdiff i
  have hb := abs_integral_markedBernoulliForwardCountTerm_le
    (mu := mu) (A := A) hA B hLeave hlambda hH hLeaveBound i
  have hd := abs_integral_markedBernoulliBackwardCountTerm_le
    (mu := mu) (A := A) hA B hLeave hlambda hH hLeaveBound hiB i
  have he := abs_integral_markedBernoulliBackwardMarkTerm_le
    (mu := mu) (A := A) hA h hLeave hlambda hdiff i
  rw [hsplit, hfarzero, add_zero]
  change |a + b + d + e| ≤ _
  calc
    |a + b + d + e| ≤ |a| + |b| + |d| + |e| := htriangle
    _ ≤
        min 1 (1 / markedBernoulliIntensity mu A) *
            (mu.real (A i) *
              (∫ omega, |h omega - hLeave i omega| ∂mu)) +
          min 1 (1 / markedBernoulliIntensity mu A) * H *
            (mu.real (A i) * ∑ j ∈ B i, mu.real (A j)) +
          min 1 (1 / markedBernoulliIntensity mu A) * H *
            (∑ j ∈ (B i).erase i, mu.real (A i ∩ A j)) +
          min 1 (1 / markedBernoulliIntensity mu A) *
            (∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
              |h omega - hLeave i omega| ∂mu) := by
      exact add_le_add (add_le_add (add_le_add ha hb) hd) he
    _ = min 1 (1 / markedBernoulliIntensity mu A) *
        (mu.real (A i) *
            (∫ omega, |h omega - hLeave i omega| ∂mu) +
          (∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
            |h omega - hLeave i omega| ∂mu) +
          H * (mu.real (A i) * ∑ j ∈ B i, mu.real (A j) +
            ∑ j ∈ (B i).erase i, mu.real (A i ∩ A j))) := by
      ring

/-- Integrability of the local error follows from integrability of its five
named channels. -/
theorem integrable_markedBernoulliVoidLocalError_of_channels
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} {A : I → Set Omega} {B : I → Finset I}
    {h : Omega → ℝ} {hLeave : I → Omega → ℝ}
    (hchannels : MarkedBernoulliVoidChannelsIntegrable mu A B h hLeave)
    (i : I) :
    Integrable (markedBernoulliVoidLocalError mu A B h hLeave i) mu := by
  rcases hchannels i with ⟨hforwardMark, hforwardCount, hfar,
    hbackwardCount, hbackwardMark⟩
  rw [show markedBernoulliVoidLocalError mu A B h hLeave i =
      fun omega ↦
        markedBernoulliForwardMarkTerm mu A h hLeave i omega +
        markedBernoulliForwardCountTerm mu A B hLeave i omega +
        markedBernoulliFarTerm mu A B hLeave i omega +
        markedBernoulliBackwardCountTerm mu A B hLeave i omega +
        markedBernoulliBackwardMarkTerm mu A h hLeave i omega by
    funext omega
    exact markedBernoulliVoidLocalError_eq_fiveTerms
      mu A B h hLeave i omega]
  exact (((hforwardMark.add hforwardCount).add hfar).add
    hbackwardCount).add hbackwardMark

/-- Finite marked Poisson-void AGG inequality.  Under independence of each
distinguished indicator from its leave-one mark/outside-count pair, all five
channels reduce to two mark-replacement costs and the classical local
`b1 + b2` terms. -/
theorem markedBernoulliVoid_AGG_bound
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (h : Omega → ℝ)
    (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    (hh : Integrable h mu)
    {H : ℝ} (hH : 0 ≤ H)
    (hLeaveBound : ∀ i omega, |hLeave i omega| ≤ H)
    (hiB : ∀ i, i ∈ B i)
    (hdiff : ∀ i, Integrable (fun omega ↦ |h omega - hLeave i omega|) mu)
    (hchannels : MarkedBernoulliVoidChannelsIntegrable mu A B h hLeave)
    (hY : ∀ i, Integrable (fun omega ↦ hLeave i omega *
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedOutsideNeighborhoodCount A B i omega + 1)) mu)
    (hindep : ∀ i, IndepFun
      (fun omega ↦ (bernoulliEventIndicator (A i) omega : ℝ))
      (fun omega ↦
        (hLeave i omega, markedOutsideNeighborhoodCount A B i omega)) mu) :
    |(∫ omega,
        h omega * markedVoidIndicator (markedBernoulliCount A omega) ∂mu) -
      (∫ omega, h omega ∂mu) *
        Real.exp (-markedBernoulliIntensity mu A)| ≤
      min 1 (1 / markedBernoulliIntensity mu A) *
        (markedPoissonMarkReplacement mu A h hLeave +
          H * (markedPoissonBOne mu A B + markedPoissonBTwo mu A B)) := by
  have herror : ∀ i, Integrable
      (markedBernoulliVoidLocalError mu A B h hLeave i) mu :=
    integrable_markedBernoulliVoidLocalError_of_channels hchannels
  refine (markedBernoulliVoid_stein_bound
    A B h hLeave hA hlambda.ne' hh herror).trans ?_
  calc
    ∑ i, |∫ omega,
        markedBernoulliVoidLocalError mu A B h hLeave i omega ∂mu| ≤
      ∑ i, min 1 (1 / markedBernoulliIntensity mu A) *
        (mu.real (A i) *
            (∫ omega, |h omega - hLeave i omega| ∂mu) +
          (∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
            |h omega - hLeave i omega| ∂mu) +
          H * (mu.real (A i) * ∑ j ∈ B i, mu.real (A j) +
            ∑ j ∈ (B i).erase i, mu.real (A i ∩ A j))) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact abs_integral_markedBernoulliVoidLocalError_le_AGG
        hA B h hLeave hlambda hH hLeaveBound hiB hdiff hchannels hY hindep i
    _ = min 1 (1 / markedBernoulliIntensity mu A) *
        (markedPoissonMarkReplacement mu A h hLeave +
          H * (markedPoissonBOne mu A B + markedPoissonBTwo mu A B)) := by
      simp only [markedPoissonMarkReplacement, markedPoissonBOne,
        markedPoissonBTwo, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]

end

end LogdetLean.Coherence
