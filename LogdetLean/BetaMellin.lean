import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic
/-!
# Mellin transform of the beta distribution

This file proves the exact real Mellin transform of `betaMeasure` directly
from mathlib's beta density.  It is the analytic starting point for computing
moments and cumulants of the logarithm of a beta random variable.

Exact mathematical source for the Mellin quotient: Rouault (2007), equation
(2.10), printed p. 189. Related exact log-Beta moment formulas appear in
Heiny--Johnston--Prochno (2022), Lemmas 3.3--3.5, printed pp. 14--16. The
proof here is an independent density-and-differentiation derivation. Full
bibliographic data and the normalization map are in PROVENANCE.md.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology

noncomputable section

set_option linter.style.haveILetI false

/-- The real beta density is nonnegative when both shape parameters are
positive. -/
lemma betaPDFReal_nonneg_of_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  rw [betaPDFReal]
  split_ifs with hx
  · exact mul_nonneg
      (mul_nonneg (one_div_nonneg.mpr (beta_pos hα hβ).le)
        (Real.rpow_nonneg hx.1.le _))
      (Real.rpow_nonneg (by linarith [hx.2]) _)
  · exact le_rfl

/-- Converting the `ℝ≥0∞` beta density back to the reals recovers the real
density. -/
lemma betaPDF_toReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    (betaPDF α β x).toReal = betaPDFReal α β x := by
  rw [betaPDF]
  exact ENNReal.toReal_ofReal (betaPDFReal_nonneg_of_pos hα hβ x)

/-- The real beta density has integral one. -/
lemma integral_betaPDFReal_eq_one {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, betaPDFReal α β x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (betaPDFReal_nonneg_of_pos hα hβ))
    (stronglyMeasurable_betaPDFReal α β).aestronglyMeasurable]
  simpa [betaPDF] using congrArg ENNReal.toReal (lintegral_betaPDF_eq_one hα hβ)

/-- The real beta density is integrable. -/
lemma integrable_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (betaPDFReal α β) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_betaPDFReal_eq_one hα hβ]
  exact one_ne_zero

/-- Multiplying a beta density by `x ^ z` shifts its first shape parameter.
This pointwise identity is the elementary core of the Mellin transform. -/
lemma rpow_mul_betaPDFReal {α β z x : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαz : 0 < α + z) :
    x ^ z * betaPDFReal α β x =
      (beta (α + z) β / beta α β) * betaPDFReal (α + z) β x := by
  rw [betaPDFReal, betaPDFReal]
  by_cases hx : 0 < x ∧ x < 1
  · rw [if_pos hx, if_pos hx]
    have hB : beta α β ≠ 0 := (beta_pos hα hβ).ne'
    have hBz : beta (α + z) β ≠ 0 := (beta_pos hαz hβ).ne'
    have hxpow : x ^ z * x ^ (α - 1) = x ^ (α + z - 1) := by
      rw [← Real.rpow_add hx.1]
      congr 1
      ring
    calc
      x ^ z * (1 / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1)) =
          (1 / beta α β) * (x ^ z * x ^ (α - 1)) * (1 - x) ^ (β - 1) := by ring
      _ = (1 / beta α β) * x ^ (α + z - 1) * (1 - x) ^ (β - 1) := by rw [hxpow]
      _ = (beta (α + z) β / beta α β) *
          (1 / beta (α + z) β * x ^ (α + z - 1) * (1 - x) ^ (β - 1)) := by
        field_simp
  · rw [if_neg hx, if_neg hx]
    ring

/-- Exact Mellin transform of the beta distribution:

`E[X^z] = B(α+z,β) / B(α,β)` whenever `α,β,α+z` are positive. -/
theorem integral_rpow_betaMeasure {α β z : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαz : 0 < α + z) :
    ∫ x, x ^ z ∂betaMeasure α β = beta (α + z) β / beta α β := by
  rw [betaMeasure]
  change (∫ x, x ^ z ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (betaPDFReal α β x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_betaPDFReal α β).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal (betaPDFReal_nonneg_of_pos hα hβ _),
    mul_comm (betaPDFReal α β _), rpow_mul_betaPDFReal hα hβ hαz]
  rw [integral_const_mul, integral_betaPDFReal_eq_one hαz hβ, mul_one]

/-- Gamma-quotient form of the beta Mellin transform. -/
theorem integral_rpow_betaMeasure_eq_gamma_quotient {α β z : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαz : 0 < α + z) :
    ∫ x, x ^ z ∂betaMeasure α β =
      (Real.Gamma (α + z) * Real.Gamma β / Real.Gamma (α + z + β)) /
        (Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)) := by
  rw [integral_rpow_betaMeasure hα hβ hαz]
  rfl

/-- On the support of a beta measure, `exp (t * log x)` and `x ^ t`
agree almost everywhere.  This explicitly handles the fact that the real
logarithm is defined at nonpositive inputs as well. -/
lemma exp_mul_log_ae_eq_rpow (α β t : ℝ) :
    (fun x ↦ exp (t * log x)) =ᵐ[betaMeasure α β] (fun x ↦ x ^ t) := by
  rw [betaMeasure]
  change (fun x ↦ exp (t * log x)) =ᵐ[
    volume.withDensity (fun x ↦ ENNReal.ofReal (betaPDFReal α β x))] (fun x ↦ x ^ t)
  refine (ae_withDensity_iff (μ := volume)
    (measurable_betaPDFReal α β).ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hpdf
  have hx : 0 < x := by
    by_contra hx'
    apply hpdf
    have hzero : betaPDFReal α β x = 0 := by
      rw [betaPDFReal, if_neg]
      exact fun hx ↦ hx' hx.1
    rw [hzero]
    exact ENNReal.ofReal_zero
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- Moment-generating integral of `log X` for a beta-distributed `X`. -/
theorem integral_exp_mul_log_betaMeasure {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαt : 0 < α + t) :
    ∫ x, exp (t * log x) ∂betaMeasure α β = beta (α + t) β / beta α β := by
  rw [integral_congr_ae (exp_mul_log_ae_eq_rpow α β t)]
  exact integral_rpow_betaMeasure hα hβ hαt

/-- The exponential moment of `log X` is integrable throughout the natural
half-line `t > -α`. -/
lemma integrable_exp_mul_log_betaMeasure {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαt : 0 < α + t) :
    Integrable (fun x ↦ exp (t * log x)) (betaMeasure α β) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_mul_log_betaMeasure hα hβ hαt]
  exact (div_pos (beta_pos hαt hβ) (beta_pos hα hβ)).ne'

/-- The exact moment-generating function of the log-beta law. -/
theorem mgf_log_betaMeasure {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαt : 0 < α + t) :
    mgf log (betaMeasure α β) t = beta (α + t) β / beta α β := by
  exact integral_exp_mul_log_betaMeasure hα hβ hαt

/-- Zero lies in the interior of the domain of the log-beta moment-generating
function. -/
lemma zero_mem_interior_integrableExpSet_log_betaMeasure {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    0 ∈ interior (integrableExpSet log (betaMeasure α β)) := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset]
  refine ⟨-α, α, ?_, ?_⟩
  · constructor <;> linarith
  · intro t ht
    exact integrable_exp_mul_log_betaMeasure hα hβ (by linarith [ht.1])

/-- Every natural power of the logarithm is beta-integrable.  This is a
formal consequence of the existence of exponential moments on both sides of
zero, not an unproved differentiation-under-the-integral assertion. -/
theorem integrable_pow_log_betaMeasure {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    Integrable (fun x ↦ log x ^ n) (betaMeasure α β) :=
  integrable_pow_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_log_betaMeasure hα hβ) n

/-- Near zero, the log-beta moment-generating function is exactly the beta
quotient. -/
lemma mgf_log_betaMeasure_eventuallyEq {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    mgf log (betaMeasure α β) =ᶠ[𝓝 0]
      (fun t ↦ beta (α + t) β / beta α β) := by
  filter_upwards [Ioi_mem_nhds (show -α < (0 : ℝ) by linarith)] with t ht
  have ht' : -α < t := ht
  exact mgf_log_betaMeasure hα hβ (by linarith)

/-- All raw log-beta moments are the derivatives at zero of the exact beta
quotient. -/
theorem integral_pow_log_betaMeasure_eq_iteratedDeriv_beta_ratio
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    ∫ x, log x ^ n ∂betaMeasure α β =
      iteratedDeriv n (fun t ↦ beta (α + t) β / beta α β) 0 := by
  calc
    ∫ x, log x ^ n ∂betaMeasure α β =
        iteratedDeriv n (mgf log (betaMeasure α β)) 0 :=
      (iteratedDeriv_mgf_zero
        (zero_mem_interior_integrableExpSet_log_betaMeasure hα hβ) n).symm
    _ = iteratedDeriv n (fun t ↦ beta (α + t) β / beta α β) 0 :=
      (mgf_log_betaMeasure_eventuallyEq hα hβ).iteratedDeriv_eq n

/-- Exact cumulant-generating function supplied by the beta quotient. -/
def betaLogCGF (α β t : ℝ) : ℝ :=
  log (beta (α + t) β / beta α β)

/-- Near zero, the cumulant-generating function of `log X` is the logarithm
of the exact beta quotient. -/
lemma cgf_log_betaMeasure_eventuallyEq {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    cgf log (betaMeasure α β) =ᶠ[𝓝 0] betaLogCGF α β := by
  filter_upwards [mgf_log_betaMeasure_eventuallyEq hα hβ] with t ht
  rw [cgf, betaLogCGF, ht]

/-- Every log-beta cumulant, defined as a derivative of the cumulant-
generating function, is the corresponding derivative of the explicit beta
quotient.  In particular, this covers orders one, two, and three. -/
theorem logBeta_cumulant_eq_iteratedDeriv_betaLogCGF
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    iteratedDeriv n (cgf log (betaMeasure α β)) 0 =
      iteratedDeriv n (betaLogCGF α β) 0 :=
  (cgf_log_betaMeasure_eventuallyEq hα hβ).iteratedDeriv_eq n

/-- The beta expectation of `log X` is the first derivative of the explicit
log-beta quotient. -/
theorem integral_log_betaMeasure_eq_deriv_betaLogCGF
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, log x ∂betaMeasure α β = deriv (betaLogCGF α β) 0 := by
  letI : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hzero := zero_mem_interior_integrableExpSet_log_betaMeasure hα hβ
  calc
    ∫ x, log x ∂betaMeasure α β = deriv (cgf log (betaMeasure α β)) 0 := by
      simpa using (deriv_cgf_zero hzero).symm
    _ = deriv (betaLogCGF α β) 0 := by
      simpa only [iteratedDeriv_one] using
        logBeta_cumulant_eq_iteratedDeriv_betaLogCGF hα hβ 1

/-- The centered second log moment (the variance) is the second derivative of
the explicit log-beta quotient. -/
theorem integral_centered_sq_log_betaMeasure_eq_second_deriv_betaLogCGF
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, (log x - ∫ y, log y ∂betaMeasure α β) ^ 2 ∂betaMeasure α β =
      iteratedDeriv 2 (betaLogCGF α β) 0 := by
  letI : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hzero := zero_mem_interior_integrableExpSet_log_betaMeasure hα hβ
  have hmean : deriv (cgf log (betaMeasure α β)) 0 =
      ∫ x, log x ∂betaMeasure α β := by
    simpa using deriv_cgf_zero hzero
  have hvariance := iteratedDeriv_two_cgf_eq_integral hzero
  have hcgf : iteratedDeriv 2 (cgf log (betaMeasure α β)) 0 =
      ∫ x, (log x - ∫ y, log y ∂betaMeasure α β) ^ 2 ∂betaMeasure α β := by
    simpa only [hmean, zero_mul, exp_zero, mul_one, mgf_zero, div_one] using hvariance
  calc
    ∫ x, (log x - ∫ y, log y ∂betaMeasure α β) ^ 2 ∂betaMeasure α β =
        iteratedDeriv 2 (cgf log (betaMeasure α β)) 0 := hcgf.symm
    _ = iteratedDeriv 2 (betaLogCGF α β) 0 :=
      logBeta_cumulant_eq_iteratedDeriv_betaLogCGF hα hβ 2

/-- Closed formula for every positive-order derivative of the real logarithm
away from zero. -/
lemma iteratedDeriv_succ_real_log (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) log x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) * x ^ (-1 - (n : ℤ)) := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate,
    iter_deriv_inv]

lemma iteratedDeriv_two_real_log_one : iteratedDeriv 2 log 1 = -1 := by
  simpa using iteratedDeriv_succ_real_log 1 1

lemma iteratedDeriv_three_real_log_one : iteratedDeriv 3 log 1 = 2 := by
  simpa using iteratedDeriv_succ_real_log 2 1

/-- The third derivative of the log-beta cumulant-generating function is the
usual algebraic third cumulant built from the first three raw moments. -/
theorem third_cgf_log_betaMeasure_eq_raw_moments
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    iteratedDeriv 3 (cgf log (betaMeasure α β)) 0 =
      (∫ x, log x ^ 3 ∂betaMeasure α β) -
        3 * (∫ x, log x ^ 2 ∂betaMeasure α β) *
          (∫ x, log x ∂betaMeasure α β) +
        2 * (∫ x, log x ∂betaMeasure α β) ^ 3 := by
  letI : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hzero := zero_mem_interior_integrableExpSet_log_betaMeasure hα hβ
  have hcomp := iteratedDeriv_comp_three
    (𝕜 := ℝ) (g := log) (f := mgf log (betaMeasure α β)) (x := 0)
    (Real.contDiffAt_log.2 (by simp))
    ((analyticAt_mgf hzero).contDiffAt)
  rw [show (log ∘ mgf log (betaMeasure α β)) =
      cgf log (betaMeasure α β) by rfl] at hcomp
  rw [mgf_zero, iteratedDeriv_three_real_log_one,
    iteratedDeriv_two_real_log_one, Real.deriv_log,
    iteratedDeriv_mgf_zero hzero 3, iteratedDeriv_mgf_zero hzero 2,
    deriv_mgf_zero hzero] at hcomp
  simp only [Pi.pow_apply] at hcomp
  norm_num at hcomp
  nlinarith

/-- The centered third log moment is exactly the third derivative of the
explicit log-beta quotient.  Thus the third probabilistic cumulant has been
identified without assuming a formal differentiation-under-the-integral
rule. -/
theorem integral_centered_cube_log_betaMeasure_eq_third_deriv_betaLogCGF
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, (log x - ∫ y, log y ∂betaMeasure α β) ^ 3 ∂betaMeasure α β =
      iteratedDeriv 3 (betaLogCGF α β) 0 := by
  letI : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  let m1 : ℝ := ∫ x, log x ∂betaMeasure α β
  have h1 : Integrable (fun x ↦ log x) (betaMeasure α β) := by
    simpa using integrable_pow_log_betaMeasure hα hβ 1
  have h2 : Integrable (fun x ↦ log x ^ 2) (betaMeasure α β) :=
    integrable_pow_log_betaMeasure hα hβ 2
  have h3 : Integrable (fun x ↦ log x ^ 3) (betaMeasure α β) :=
    integrable_pow_log_betaMeasure hα hβ 3
  have ht2 : Integrable (fun x ↦ (3 * m1) * log x ^ 2) (betaMeasure α β) :=
    h2.const_mul _
  have ht3 : Integrable (fun x ↦ (3 * m1 ^ 2) * log x) (betaMeasure α β) :=
    h1.const_mul _
  have hsub : Integrable (fun x ↦ log x ^ 3 - (3 * m1) * log x ^ 2)
      (betaMeasure α β) := h3.sub ht2
  have hadd : Integrable
      (fun x ↦ (log x ^ 3 - (3 * m1) * log x ^ 2) + (3 * m1 ^ 2) * log x)
      (betaMeasure α β) := hsub.add ht3
  have hcentered :
      (∫ x, (log x - m1) ^ 3 ∂betaMeasure α β) =
        (∫ x, log x ^ 3 ∂betaMeasure α β) -
          3 * (∫ x, log x ^ 2 ∂betaMeasure α β) * m1 + 2 * m1 ^ 3 := by
    calc
      (∫ x, (log x - m1) ^ 3 ∂betaMeasure α β) =
          ∫ x, ((log x ^ 3 - (3 * m1) * log x ^ 2) +
            (3 * m1 ^ 2) * log x) - m1 ^ 3 ∂betaMeasure α β := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = (∫ x, log x ^ 3 ∂betaMeasure α β) -
          3 * (∫ x, log x ^ 2 ∂betaMeasure α β) * m1 + 2 * m1 ^ 3 := by
        rw [integral_sub hadd (integrable_const (m1 ^ 3)),
          integral_add hsub ht3, integral_sub h3 ht2,
          integral_const_mul, integral_const_mul, integral_const]
        simp only [smul_eq_mul]
        simp
        ring
  change (∫ x, (log x - m1) ^ 3 ∂betaMeasure α β) = _
  calc
    (∫ x, (log x - m1) ^ 3 ∂betaMeasure α β) =
        (∫ x, log x ^ 3 ∂betaMeasure α β) -
          3 * (∫ x, log x ^ 2 ∂betaMeasure α β) * m1 + 2 * m1 ^ 3 := hcentered
    _ = iteratedDeriv 3 (cgf log (betaMeasure α β)) 0 := by
      rw [third_cgf_log_betaMeasure_eq_raw_moments hα hβ]
    _ = iteratedDeriv 3 (betaLogCGF α β) 0 :=
      logBeta_cumulant_eq_iteratedDeriv_betaLogCGF hα hβ 3

end

end LogdetLean
