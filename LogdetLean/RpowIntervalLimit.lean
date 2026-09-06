import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
/-!
# An elementary reciprocal-power interval integral and its expanding-window limit

This is the scalar calculus input used by the Frullani/Laplace proof of the
general-correlation radial covariance bound.  It is isolated here because it
is useful independently of Gaussian probability.
-/

namespace LogdetLean

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

/-- Exact finite-window integral of the reciprocal power appearing in the
linear part of the bivariate radial Laplace kernel. -/
theorem integral_one_div_one_add_two_mul_rpow
    {a eps T : ℝ} (ha : 0 < a) (heps : 0 < eps) (hT : eps ≤ T) :
    (∫ s in eps..T, 1 / (1 + 2 * s) ^ (a + 1)) =
      ((1 + 2 * eps) ^ (-a) - (1 + 2 * T) ^ (-a)) / (2 * a) := by
  let F : ℝ → ℝ := fun s ↦ -(1 + 2 * s) ^ (-a) / (2 * a)
  have hderiv : ∀ s ∈ uIcc eps T,
      HasDerivAt F (1 / (1 + 2 * s) ^ (a + 1)) s := by
    intro s hs
    have hsIcc : s ∈ Icc eps T := by simpa [uIcc_of_le hT] using hs
    have hsge : eps ≤ s := hsIcc.1
    have hbase : 0 < 1 + 2 * s := by linarith
    have hlin : HasDerivAt (fun x : ℝ ↦ 1 + 2 * x) 2 s := by
      simpa using ((hasDerivAt_id s).const_mul 2).const_add 1
    have hp := hlin.rpow_const (p := -a) (Or.inl hbase.ne')
    have hscaled := hp.neg.div_const (2 * a)
    have hvalue : -(2 * -a * (1 + 2 * s) ^ (-a - 1)) / (2 * a) =
        1 / (1 + 2 * s) ^ (a + 1) := by
      rw [show -a - 1 = -(a + 1) by ring,
        Real.rpow_neg hbase.le]
      field_simp [ha.ne']
    simpa [F] using hscaled.congr_deriv hvalue
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ 1 / (1 + 2 * s) ^ (a + 1)) volume eps T := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro s hs
    have hsIcc : s ∈ Icc eps T := by simpa [uIcc_of_le hT] using hs
    have hbase : 0 < 1 + 2 * s := by linarith [hsIcc.1]
    have hc : ContinuousAt (fun x : ℝ ↦ (1 + 2 * x) ^ (a + 1)) s :=
      (by fun_prop : ContinuousAt (fun x : ℝ ↦ 1 + 2 * x) s).rpow_const
        (Or.inl hbase.ne')
    exact continuousAt_const.div hc (Real.rpow_pos_of_pos hbase _).ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp [F] at hFTC
  rw [hFTC]
  field_simp [ha.ne']
  ring

/-- The expanding Frullani window used in the project. -/
def reciprocalPowerWindowIntegral (a : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
    1 / (1 + 2 * s) ^ (a + 1)

/-- The expanding-window integral converges to its improper-integral value. -/
theorem tendsto_reciprocalPowerWindowIntegral
    {a : ℝ} (ha : 0 < a) :
    Tendsto (reciprocalPowerWindowIntegral a) atTop (nhds (1 / (2 * a))) := by
  have hformula : ∀ n : ℕ,
      reciprocalPowerWindowIntegral a n =
        ((1 + 2 * (1 / ((n : ℝ) + 1))) ^ (-a) -
          (1 + 2 * ((n : ℝ) + 1)) ^ (-a)) / (2 * a) := by
    intro n
    unfold reciprocalPowerWindowIntegral
    apply integral_one_div_one_add_two_mul_rpow ha
    · positivity
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hpos : 0 < (n : ℝ) + 1 := by positivity
      exact (div_le_iff₀ hpos).2 (by nlinarith)
  have heq : reciprocalPowerWindowIntegral a = fun n : ℕ ↦
      ((1 + 2 * (1 / ((n : ℝ) + 1))) ^ (-a) -
        (1 + 2 * ((n : ℝ) + 1)) ^ (-a)) / (2 * a) := by
    funext n
    exact hformula n
  rw [heq]
  have hsmall : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have htop : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [one_div] using hone.div_atTop htop
  have hleftbase : Tendsto
      (fun n : ℕ ↦ 1 + 2 * (1 / ((n : ℝ) + 1))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hsmall)
  have hleft : Tendsto
      (fun n : ℕ ↦ (1 + 2 * (1 / ((n : ℝ) + 1))) ^ (-a))
      atTop (nhds 1) := by
    simpa using hleftbase.rpow_const (Or.inl one_ne_zero)
  have hrightbase : Tendsto
      (fun n : ℕ ↦ 1 + 2 * ((n : ℝ) + 1)) atTop atTop := by
    have hinner : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hmul : Tendsto (fun n : ℕ ↦ 2 * ((n : ℝ) + 1)) atTop atTop :=
      Tendsto.const_mul_atTop' (by norm_num) hinner
    simpa [add_comm] using
      (tendsto_atTop_add_const_right atTop 1 hmul)
  have hright : Tendsto
      (fun n : ℕ ↦ (1 + 2 * ((n : ℝ) + 1)) ^ (-a)) atTop (nhds 0) := by
    simpa [Function.comp_def] using (tendsto_rpow_neg_atTop ha).comp hrightbase
  simpa using (hleft.sub hright).div_const (2 * a)

end

end LogdetLean
