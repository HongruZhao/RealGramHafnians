import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Probability.Moments.Variance
import LogdetLean.FullTarget
import LogdetLean.BetaMellin
/-!
# Moments of additive convolutions

This file proves that the mean, variance, and third centered moment of the
additive convolution of two probability measures are the sums of the
corresponding moments.  The third-moment theorem assumes finite third absolute
moments, expressed by `MemLp id 3`.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal

noncomputable section

set_option linter.style.haveILetI false

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The mean of an additive convolution is the sum of the two means. -/
theorem integral_id_conv (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hν : Integrable (fun x : ℝ ↦ x) ν) :
    (∫ z, z ∂(μ ∗ ν)) = (∫ x, x ∂μ) + ∫ y, y ∂ν := by
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  have hfst : Integrable (fun z : ℝ × ℝ ↦ z.1) (μ.prod ν) := hμ.comp_fst ν
  have hsnd : Integrable (fun z : ℝ × ℝ ↦ z.2) (μ.prod ν) := hν.comp_snd μ
  rw [integral_add hfst hsnd]
  have hifst : (∫ z : ℝ × ℝ, z.1 ∂(μ.prod ν)) =
      ν.real Set.univ • ∫ x : ℝ, x ∂μ :=
    integral_fun_fst (μ := μ) (ν := ν) (fun x : ℝ ↦ x)
  have hisnd : (∫ z : ℝ × ℝ, z.2 ∂(μ.prod ν)) =
      μ.real Set.univ • ∫ y : ℝ, y ∂ν :=
    integral_fun_snd (μ := μ) (ν := ν) (fun y : ℝ ↦ y)
  rw [hifst, hisnd]
  simp only [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul]

/-- The variance of an additive convolution is the sum of the two variances. -/
theorem variance_id_conv (hμ : MemLp (fun x : ℝ ↦ x) 2 μ)
    (hν : MemLp (fun x : ℝ ↦ x) 2 ν) :
    Var[(fun z : ℝ ↦ z); μ ∗ ν] =
      Var[(fun x : ℝ ↦ x); μ] + Var[(fun y : ℝ ↦ y); ν] := by
  rw [Measure.conv,
    variance_map (X := fun z : ℝ ↦ z) (Y := fun z : ℝ × ℝ ↦ z.1 + z.2)
      (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def] using
    (variance_add_prod (X := fun x : ℝ ↦ x) (Y := fun y : ℝ ↦ y) hμ hν)

/-- The centered second moment of an additive convolution is the sum of the
two centered second moments. -/
theorem integral_centered_sq_conv (hμ : MemLp (fun x : ℝ ↦ x) 2 μ)
    (hν : MemLp (fun x : ℝ ↦ x) 2 ν) :
    (∫ z, (z - ∫ w, w ∂(μ ∗ ν)) ^ 2 ∂(μ ∗ ν)) =
      (∫ x, (x - ∫ u, u ∂μ) ^ 2 ∂μ) +
        ∫ y, (y - ∫ v, v ∂ν) ^ 2 ∂ν := by
  simpa only [variance_eq_integral (X := fun z : ℝ ↦ z) (μ := μ ∗ ν) (by fun_prop),
    variance_eq_integral (X := fun x : ℝ ↦ x) (μ := μ) (by fun_prop),
    variance_eq_integral (X := fun y : ℝ ↦ y) (μ := ν) (by fun_prop)] using
      variance_id_conv hμ hν

/-- The centered third moment of an additive convolution is the sum of the
two centered third moments. -/
theorem integral_centered_cube_conv (hμ : MemLp (fun x : ℝ ↦ x) 3 μ)
    (hν : MemLp (fun x : ℝ ↦ x) 3 ν) :
    (∫ z, (z - ∫ w, w ∂(μ ∗ ν)) ^ 3 ∂(μ ∗ ν)) =
      (∫ x, (x - ∫ u, u ∂μ) ^ 3 ∂μ) +
        ∫ y, (y - ∫ v, v ∂ν) ^ 3 ∂ν := by
  let a : ℝ := ∫ x, x ∂μ
  let b : ℝ := ∫ y, y ∂ν
  have hμ1 : Integrable (fun x : ℝ ↦ x) μ := hμ.integrable (by norm_num)
  have hν1 : Integrable (fun y : ℝ ↦ y) ν := hν.integrable (by norm_num)
  have hmean : (∫ z, z ∂(μ ∗ ν)) = a + b := by
    simpa [a, b] using integral_id_conv hμ1 hν1
  have hμc3 : MemLp (fun x : ℝ ↦ x - a) 3 μ := hμ.sub (memLp_const a)
  have hνc3 : MemLp (fun y : ℝ ↦ y - b) 3 ν := hν.sub (memLp_const b)
  have hμc2 : MemLp (fun x : ℝ ↦ x - a) 2 μ :=
    hμc3.mono_exponent (by norm_num)
  have hνc2 : MemLp (fun y : ℝ ↦ y - b) 2 ν :=
    hνc3.mono_exponent (by norm_num)
  have hμc1 : Integrable (fun x : ℝ ↦ x - a) μ := hμc3.integrable (by norm_num)
  have hνc1 : Integrable (fun y : ℝ ↦ y - b) ν := hνc3.integrable (by norm_num)
  have hμc_sq : Integrable (fun x : ℝ ↦ (x - a) ^ 2) μ := hμc2.integrable_sq
  have hνc_sq : Integrable (fun y : ℝ ↦ (y - b) ^ 2) ν := hνc2.integrable_sq
  have hμc_cube : Integrable (fun x : ℝ ↦ (x - a) ^ 3) μ := by
    have h := hμc3.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
    apply (integrable_norm_iff (by fun_prop)).mp
    simpa [norm_pow] using h
  have hνc_cube : Integrable (fun y : ℝ ↦ (y - b) ^ 3) ν := by
    have h := hνc3.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
    apply (integrable_norm_iff (by fun_prop)).mp
    simpa [norm_pow] using h
  have hμcenter : (∫ x, x - a ∂μ) = 0 := by
    rw [integral_sub hμ1 (integrable_const a), integral_const]
    simp [a]
  have hνcenter : (∫ y, y - b ∂ν) = 0 := by
    rw [integral_sub hν1 (integrable_const b), integral_const]
    simp [b]
  let f1 : ℝ × ℝ → ℝ := fun z ↦ (z.1 - a) ^ 3
  let f2 : ℝ × ℝ → ℝ := fun z ↦ 3 * ((z.1 - a) ^ 2 * (z.2 - b))
  let f3 : ℝ × ℝ → ℝ := fun z ↦ 3 * ((z.1 - a) * (z.2 - b) ^ 2)
  let f4 : ℝ × ℝ → ℝ := fun z ↦ (z.2 - b) ^ 3
  have hf1 : Integrable f1 (μ.prod ν) := hμc_cube.comp_fst ν
  have hf2 : Integrable f2 (μ.prod ν) :=
    (hμc_sq.mul_prod hνc1).const_mul 3
  have hf3 : Integrable f3 (μ.prod ν) :=
    (hμc1.mul_prod hνc_sq).const_mul 3
  have hf4 : Integrable f4 (μ.prod ν) := hνc_cube.comp_snd μ
  rw [hmean, Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  have hpoly :
      (fun z : ℝ × ℝ ↦ (z.1 + z.2 - (a + b)) ^ 3) =
        f1 + f2 + f3 + f4 := by
    funext z
    simp only [Pi.add_apply, f1, f2, f3, f4]
    ring
  rw [hpoly, integral_add' ((hf1.add hf2).add hf3) hf4,
    integral_add' (hf1.add hf2) hf3, integral_add' hf1 hf2]
  have hi1 : (∫ z, f1 z ∂(μ.prod ν)) = ∫ x, (x - a) ^ 3 ∂μ := by
    calc
      (∫ z, f1 z ∂(μ.prod ν)) =
          ∫ z : ℝ × ℝ, (z.1 - a) ^ 3 ∂(μ.prod ν) := by rfl
      _ = ν.real Set.univ • ∫ x, (x - a) ^ 3 ∂μ :=
        integral_fun_fst (μ := μ) (ν := ν) (fun x : ℝ ↦ (x - a) ^ 3)
      _ = ∫ x, (x - a) ^ 3 ∂μ := by
        simp only [measureReal_def, IsProbabilityMeasure.measure_univ,
          ENNReal.toReal_one, one_smul]
  have hi2 : (∫ z, f2 z ∂(μ.prod ν)) = 0 := by
    have hprod := integral_prod_mul (μ := μ) (ν := ν)
      (fun x : ℝ ↦ (x - a) ^ 2) (fun y : ℝ ↦ y - b)
    calc
      (∫ z, f2 z ∂(μ.prod ν)) =
          3 * ∫ z : ℝ × ℝ, (z.1 - a) ^ 2 * (z.2 - b) ∂(μ.prod ν) := by
        rw [integral_const_mul]
      _ = 3 * ((∫ x, (x - a) ^ 2 ∂μ) * ∫ y, y - b ∂ν) := by rw [hprod]
      _ = 0 := by rw [hνcenter]; ring
  have hi3 : (∫ z, f3 z ∂(μ.prod ν)) = 0 := by
    have hprod := integral_prod_mul (μ := μ) (ν := ν)
      (fun x : ℝ ↦ x - a) (fun y : ℝ ↦ (y - b) ^ 2)
    calc
      (∫ z, f3 z ∂(μ.prod ν)) =
          3 * ∫ z : ℝ × ℝ, (z.1 - a) * (z.2 - b) ^ 2 ∂(μ.prod ν) := by
        rw [integral_const_mul]
      _ = 3 * ((∫ x, x - a ∂μ) * ∫ y, (y - b) ^ 2 ∂ν) := by rw [hprod]
      _ = 0 := by rw [hμcenter]; ring
  have hi4 : (∫ z, f4 z ∂(μ.prod ν)) = ∫ y, (y - b) ^ 3 ∂ν := by
    calc
      (∫ z, f4 z ∂(μ.prod ν)) =
          ∫ z : ℝ × ℝ, (z.2 - b) ^ 3 ∂(μ.prod ν) := by rfl
      _ = μ.real Set.univ • ∫ y, (y - b) ^ 3 ∂ν :=
        integral_fun_snd (μ := μ) (ν := ν) (fun y : ℝ ↦ (y - b) ^ 3)
      _ = ∫ y, (y - b) ^ 3 ∂ν := by
        simp only [measureReal_def, IsProbabilityMeasure.measure_univ,
          ENNReal.toReal_one, one_smul]
  rw [hi1, hi2, hi3, hi4]
  simp [a, b]

/-- Finite third absolute moments are preserved by additive convolution. -/
theorem memLp_id_conv (hμ : MemLp (fun x : ℝ ↦ x) 3 μ)
    (hν : MemLp (fun x : ℝ ↦ x) 3 ν) :
    MemLp (fun z : ℝ ↦ z) 3 (μ ∗ ν) := by
  rw [Measure.conv, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact MemLp.ae_eq (ae_of_all _ fun z ↦ by rfl)
    ((hμ.comp_fst ν).add (hν.comp_snd μ))

/-- Each admissible log-beta factor has a finite third absolute moment. -/
theorem memLp_id_logBetaLaw {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) :
    MemLp (fun x : ℝ ↦ x) 3 (logBetaLaw m j) := by
  have hA : 0 < betaShapeA m j := betaShapeA_pos_of_le hjm
  have hB : 0 < betaShapeB j := betaShapeB_pos_of_two_le hj
  have hpow : Integrable (fun x ↦ Real.log x ^ 3)
      (betaMeasure (betaShapeA m j) (betaShapeB j)) :=
    integrable_pow_log_betaMeasure hA hB 3
  have hnorm : Integrable (fun x ↦ ‖Real.log x‖ ^ 3)
      (betaMeasure (betaShapeA m j) (betaShapeB j)) := by
    simpa [norm_pow] using hpow.norm
  have hlog : MemLp Real.log 3
      (betaMeasure (betaShapeA m j) (betaShapeB j)) := by
    apply (integrable_norm_rpow_iff (by fun_prop) (by norm_num) (by simp)).mp
    simpa using hnorm
  unfold logBetaLaw
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact MemLp.ae_eq (ae_of_all _ fun x ↦ by rfl) hlog

/-- The recursively convolved log-beta law has a finite third absolute moment
throughout the admissible triangular array. -/
theorem memLp_id_logBetaSumLaw {m p : ℕ} (hpm : p ≤ m) :
    MemLp (fun x : ℝ ↦ x) 3 (logBetaSumLaw m p) := by
  induction p with
  | zero =>
      rw [logBetaSumLaw]
      refine MemLp.of_bound (by fun_prop) 0 ?_
      simp
  | succ p ih =>
      by_cases hp2 : 2 ≤ p + 1
      · haveI : IsProbabilityMeasure (logBetaSumLaw m p) :=
          isProbabilityMeasure_logBetaSumLaw (by omega)
        haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm hp2
        rw [logBetaSumLaw, if_pos hp2]
        exact memLp_id_conv (ih (by omega)) (memLp_id_logBetaLaw hpm hp2)
      · rw [logBetaSumLaw, if_neg hp2]
        refine MemLp.of_bound (by fun_prop) 0 ?_
        simp

/-- The exact variance of one log-beta factor. -/
def logBetaVariance (m j : ℕ) : ℝ :=
  ∫ x, (x - ∫ y, y ∂(logBetaLaw m j)) ^ 2 ∂(logBetaLaw m j)

/-- Minus the exact centered third moment of one log-beta factor. -/
def logBetaThirdMagnitude (m j : ℕ) : ℝ :=
  -∫ x, (x - ∫ y, y ∂(logBetaLaw m j)) ^ 3 ∂(logBetaLaw m j)

/-- `nullVariance` is exactly the finite sum of the individual log-beta
variances. -/
theorem nullVariance_eq_sum_logBetaVariance {m p : ℕ} (hpm : p ≤ m) :
    nullVariance m p = ∑ j ∈ Finset.Icc 2 p, logBetaVariance m j := by
  induction p with
  | zero => simp [nullVariance, nullCenter, logBetaSumLaw]
  | succ p ih =>
      by_cases hp2 : 2 ≤ p + 1
      · haveI : IsProbabilityMeasure (logBetaSumLaw m p) :=
          isProbabilityMeasure_logBetaSumLaw (by omega)
        haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm hp2
        have hprev3 := memLp_id_logBetaSumLaw (m := m) (p := p) (by omega)
        have hfactor3 := memLp_id_logBetaLaw (m := m) (j := p + 1) hpm hp2
        have hprev2 : MemLp (fun x : ℝ ↦ x) 2 (logBetaSumLaw m p) :=
          hprev3.mono_exponent (by norm_num)
        have hfactor2 : MemLp (fun x : ℝ ↦ x) 2 (logBetaLaw m (p + 1)) :=
          hfactor3.mono_exponent (by norm_num)
        rw [nullVariance, nullCenter, logBetaSumLaw, if_pos hp2]
        rw [integral_centered_sq_conv hprev2 hfactor2]
        change nullVariance m p + logBetaVariance m (p + 1) = _
        rw [ih (by omega), Finset.sum_Icc_succ_top hp2]
      · have hp0 : p = 0 := by omega
        subst p
        simp [nullVariance, nullCenter, logBetaSumLaw]

/-- `nullThirdMagnitude` is exactly the finite sum of minus the individual
centered third moments. -/
theorem nullThirdMagnitude_eq_sum_logBetaThirdMagnitude {m p : ℕ} (hpm : p ≤ m) :
    nullThirdMagnitude m p =
      ∑ j ∈ Finset.Icc 2 p, logBetaThirdMagnitude m j := by
  induction p with
  | zero => simp [nullThirdMagnitude, nullCenter, logBetaSumLaw]
  | succ p ih =>
      by_cases hp2 : 2 ≤ p + 1
      · haveI : IsProbabilityMeasure (logBetaSumLaw m p) :=
          isProbabilityMeasure_logBetaSumLaw (by omega)
        haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm hp2
        have hprev3 := memLp_id_logBetaSumLaw (m := m) (p := p) (by omega)
        have hfactor3 := memLp_id_logBetaLaw (m := m) (j := p + 1) hpm hp2
        rw [nullThirdMagnitude, nullCenter, logBetaSumLaw, if_pos hp2]
        rw [integral_centered_cube_conv hprev3 hfactor3, neg_add]
        change nullThirdMagnitude m p + logBetaThirdMagnitude m (p + 1) = _
        rw [ih (by omega), Finset.sum_Icc_succ_top hp2]
      · have hp0 : p = 0 := by omega
        subst p
        simp [nullThirdMagnitude, nullCenter, logBetaSumLaw]

end

end LogdetLean
