import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import LogdetLean.LogGammaPolygamma
import Mathlib.Tactic
/-!
# Mellin transform and logarithmic moments of a Gamma law

This is the reusable scalar analytic package behind the chi-square radial
computations in both log-determinant papers.  For shape `a>0` and rate `r>0`
it proves

`E X^t = r^(-t) Gamma(a+t)/Gamma(a)`, `a+t>0`,

then identifies the exact mean and variance of `log X` with the locally built
digamma and trigamma series.  The proof is from Mathlib's Gamma density and
its Gamma integral; no chi-square or special moment theorem is assumed.

The identities are classical.  In the old paper the chi-square Mellin
specialization is equation (5.5), printed p. 11, and its first derivative is
equation (5.6); the log-variance calculation is then used in the proof of
(5.3), printed p. 12.  The same calculation appears in the new manuscript's
general-correlation appendix.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Topology

noncomputable section

set_option linter.style.haveILetI false

lemma gammaPDF_toReal_of_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    (gammaPDF a r x).toReal = gammaPDFReal a r x := by
  rw [gammaPDF]
  exact ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)

lemma integral_gammaPDFReal_eq_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, gammaPDFReal a r x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (gammaPDFReal_nonneg ha hr))
    (stronglyMeasurable_gammaPDFReal a r).aestronglyMeasurable]
  simpa [gammaPDF] using
    congrArg ENNReal.toReal (lintegral_gammaPDF_eq_one ha hr)

lemma integrable_gammaPDFReal {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gammaPDFReal_eq_one ha hr]
  exact one_ne_zero

/-- Multiplication by `x^t` shifts the Gamma shape. -/
lemma rpow_mul_gammaPDFReal {a r t x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hat : 0 < a + t) (hx : 0 < x) :
    x ^ t * gammaPDFReal a r x =
      (r ^ (-t) * Real.Gamma (a + t) / Real.Gamma a) *
        gammaPDFReal (a + t) r x := by
  rw [gammaPDFReal, gammaPDFReal, if_pos hx.le, if_pos hx.le]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGat : Real.Gamma (a + t) ≠ 0 :=
    (Real.Gamma_pos_of_pos hat).ne'
  have hxp : x ^ t * x ^ (a - 1) = x ^ (a + t - 1) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hrp : r ^ (-t) * r ^ (a + t) = r ^ a := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  calc
    x ^ t * (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
        (r ^ a / Real.Gamma a) * (x ^ t * x ^ (a - 1)) *
          Real.exp (-(r * x)) := by ring
    _ = (r ^ a / Real.Gamma a) * x ^ (a + t - 1) *
          Real.exp (-(r * x)) := by rw [hxp]
    _ = (r ^ (-t) * Real.Gamma (a + t) / Real.Gamma a) *
        (r ^ (a + t) / Real.Gamma (a + t) * x ^ (a + t - 1) *
          Real.exp (-(r * x))) := by
      field_simp [hGa, hGat]
      rw [hrp]

/-- Exact real Mellin transform of the Gamma distribution. -/
theorem integral_rpow_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hat : 0 < a + t) :
    ∫ x, x ^ t ∂gammaMeasure a r =
      r ^ (-t) * Real.Gamma (a + t) / Real.Gamma a := by
  rw [gammaMeasure]
  change (∫ x, x ^ t ∂volume.withDensity
    (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal a r).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _),
    mul_comm (gammaPDFReal a r _)]
  have hae : (fun x ↦ x ^ t * gammaPDFReal a r x) =ᵐ[volume]
      (fun x ↦ (r ^ (-t) * Real.Gamma (a + t) / Real.Gamma a) *
        gammaPDFReal (a + t) r x) := by
    have hne : ∀ᵐ x ∂volume, x ≠ (0 : ℝ) := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx0
    by_cases hx : 0 < x
    · exact rpow_mul_gammaPDFReal ha hr hat hx
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      simp [gammaPDFReal, not_le.mpr hxneg]
  rw [integral_congr_ae hae]
  rw [integral_const_mul, integral_gammaPDFReal_eq_one hat hr, mul_one]

lemma exp_mul_log_ae_eq_rpow_gamma (a r t : ℝ) :
    (fun x ↦ Real.exp (t * Real.log x)) =ᵐ[gammaMeasure a r]
      (fun x ↦ x ^ t) := by
  rw [gammaMeasure]
  change (fun x ↦ Real.exp (t * Real.log x)) =ᵐ[
    volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x))]
      (fun x ↦ x ^ t)
  refine (ae_withDensity_iff
    (measurable_gammaPDFReal a r).ennreal_ofReal).2 ?_
  have hne : ∀ᵐ x ∂volume, x ≠ (0 : ℝ) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx0
  intro hpdf
  have hx : 0 < x := by
    by_contra hx'
    apply hpdf
    have hxle : x ≤ 0 := le_of_not_gt hx'
    have hxneg : x < 0 := lt_of_le_of_ne hxle hx0
    simp [gammaPDFReal, not_le.mpr hxneg]
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem integral_exp_mul_log_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hat : 0 < a + t) :
    ∫ x, Real.exp (t * Real.log x) ∂gammaMeasure a r =
      r ^ (-t) * Real.Gamma (a + t) / Real.Gamma a := by
  rw [integral_congr_ae (exp_mul_log_ae_eq_rpow_gamma a r t)]
  exact integral_rpow_gammaMeasure ha hr hat

lemma integrable_exp_mul_log_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hat : 0 < a + t) :
    Integrable (fun x ↦ Real.exp (t * Real.log x)) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_mul_log_gammaMeasure ha hr hat]
  exact (div_pos
    (mul_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos hat))
    (Real.Gamma_pos_of_pos ha)).ne'

theorem mgf_log_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hat : 0 < a + t) :
    mgf Real.log (gammaMeasure a r) t =
      r ^ (-t) * Real.Gamma (a + t) / Real.Gamma a :=
  integral_exp_mul_log_gammaMeasure ha hr hat

lemma zero_mem_interior_integrableExpSet_log_gammaMeasure {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    0 ∈ interior (integrableExpSet Real.log (gammaMeasure a r)) := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset]
  refine ⟨-a, a, ?_, ?_⟩
  · constructor <;> linarith
  · intro t ht
    exact integrable_exp_mul_log_gammaMeasure ha hr (by linarith [ht.1])

theorem integrable_pow_log_gammaMeasure {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x ↦ Real.log x ^ n) (gammaMeasure a r) :=
  integrable_pow_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_log_gammaMeasure ha hr) n

/-- An additive expression for the exact log-Gamma CGF. -/
def gammaLogCGF (a r t : ℝ) : ℝ :=
  -t * Real.log r + Real.log (Real.Gamma (a + t)) -
    Real.log (Real.Gamma a)

lemma cgf_log_gammaMeasure_eventuallyEq {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    cgf Real.log (gammaMeasure a r) =ᶠ[nhds 0] gammaLogCGF a r := by
  filter_upwards [Ioi_mem_nhds (show -a < (0 : ℝ) by linarith)] with t ht
  have ht' : -a < t := ht
  have hat : 0 < a + t := by linarith
  rw [cgf, mgf_log_gammaMeasure ha hr hat]
  unfold gammaLogCGF
  have hrt : r ^ (-t) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGat : Real.Gamma (a + t) ≠ 0 :=
    (Real.Gamma_pos_of_pos hat).ne'
  rw [Real.log_div (mul_ne_zero hrt hGat) hGa,
    Real.log_mul hrt hGat, Real.log_rpow hr]

theorem gammaLogCumulant_eq_iteratedDeriv
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    iteratedDeriv n (cgf Real.log (gammaMeasure a r)) 0 =
      iteratedDeriv n (gammaLogCGF a r) 0 :=
  (cgf_log_gammaMeasure_eventuallyEq ha hr).iteratedDeriv_eq n

private theorem hasDerivAt_logGamma_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Real.log ∘ Real.Gamma) (digammaSeries x) x := by
  have hd : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x :=
    (Real.differentiableAt_Gamma (fun n ↦ by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)).log (Real.Gamma_pos_of_pos hx).ne'
  rw [← deriv_logGamma_eq_digammaSeries hx]
  exact hd.hasDerivAt

theorem hasDerivAt_gammaLogCGF {a r t : ℝ}
    (hat : 0 < a + t) :
    HasDerivAt (gammaLogCGF a r)
      (digammaSeries (a + t) - Real.log r) t := by
  have hshift : HasDerivAt (fun s : ℝ ↦ a + s) 1 t :=
    (hasDerivAt_id t).const_add a
  have hgamma : HasDerivAt
      (fun s : ℝ ↦ Real.log (Real.Gamma (a + s)))
      (digammaSeries (a + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_logGamma_pos hat).comp t hshift
  have hlinear : HasDerivAt (fun s : ℝ ↦ -s * Real.log r)
      (-Real.log r) t := by
    simpa [mul_comm] using (hasDerivAt_id (x := t)).neg.mul_const (Real.log r)
  have h := (hlinear.add hgamma).sub
    (hasDerivAt_const t (Real.log (Real.Gamma a)))
  have hfun : gammaLogCGF a r =
      (((fun t : ℝ ↦ -t * Real.log r) +
        (fun t ↦ Real.log (Real.Gamma (a + t)))) -
        (fun _t ↦ Real.log (Real.Gamma a))) := by rfl
  rw [hfun]
  exact h.congr_deriv (by ring)

theorem deriv_gammaLogCGF_zero {a r : ℝ} (ha : 0 < a) (_hr : 0 < r) :
    deriv (gammaLogCGF a r) 0 = digammaSeries a - Real.log r := by
  simpa using (hasDerivAt_gammaLogCGF (a := a) (r := r) (t := 0)
    (by simpa using ha)).deriv

/-- Second derivative of the explicit Gamma log-CGF. -/
theorem iteratedDeriv_two_gammaLogCGF_zero {a r : ℝ}
    (ha : 0 < a) :
    iteratedDeriv 2 (gammaLogCGF a r) 0 = trigammaSeries a := by
  have hevent : deriv (gammaLogCGF a r) =ᶠ[nhds 0]
      (fun t ↦ digammaSeries (a + t) - Real.log r) := by
    filter_upwards [Ioi_mem_nhds (show -a < (0 : ℝ) by linarith)] with t ht
    have ht' : -a < t := ht
    exact (hasDerivAt_gammaLogCGF (a := a) (r := r) (t := t)
      (by linarith)).deriv
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ,
    iteratedDeriv_one, hevent.deriv_eq]
  have hshift : HasDerivAt (fun t : ℝ ↦ a + t) 1 0 :=
    (hasDerivAt_id 0).const_add a
  have hd : deriv (fun t : ℝ ↦ digammaSeries (a + t)) 0 =
      trigammaSeries a := by
    have hout : HasDerivAt digammaSeries (trigammaSeries (a + 0)) (a + 0) :=
      hasDerivAt_digammaSeries (by simpa using ha)
    have hc := hout.comp 0 hshift
    change deriv (digammaSeries ∘ HAdd.hAdd a) 0 = trigammaSeries a
    simpa only [add_zero, mul_one] using hc.deriv
  rw [deriv_sub_const]
  exact hd

/-- Exact logarithmic mean of a Gamma variable. -/
theorem integral_log_gammaMeasure_eq {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    ∫ x, Real.log x ∂gammaMeasure a r =
      digammaSeries a - Real.log r := by
  let _ : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  have h0 := zero_mem_interior_integrableExpSet_log_gammaMeasure ha hr
  calc
    ∫ x, Real.log x ∂gammaMeasure a r =
        deriv (cgf Real.log (gammaMeasure a r)) 0 := by
      simpa using (deriv_cgf_zero h0).symm
    _ = deriv (gammaLogCGF a r) 0 := by
      simpa only [iteratedDeriv_one] using
        gammaLogCumulant_eq_iteratedDeriv ha hr 1
    _ = digammaSeries a - Real.log r := deriv_gammaLogCGF_zero ha hr

/-- Exact variance of `log X` for `X~Gamma(a,r)`. -/
theorem integral_centered_sq_log_gammaMeasure_eq {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    ∫ x, (Real.log x - ∫ y, Real.log y ∂gammaMeasure a r) ^ 2
        ∂gammaMeasure a r = trigammaSeries a := by
  let _ : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  have h0 := zero_mem_interior_integrableExpSet_log_gammaMeasure ha hr
  have hcumul : iteratedDeriv 2 (cgf Real.log (gammaMeasure a r)) 0 =
      iteratedDeriv 2 (gammaLogCGF a r) 0 :=
    gammaLogCumulant_eq_iteratedDeriv ha hr 2
  have hvariance := iteratedDeriv_two_cgf_eq_integral h0
  have hmean : deriv (cgf Real.log (gammaMeasure a r)) 0 =
      ∫ x, Real.log x ∂gammaMeasure a r := by
    simpa using deriv_cgf_zero h0
  have hcgf :
      ∫ x, (Real.log x - ∫ y, Real.log y ∂gammaMeasure a r) ^ 2
          ∂gammaMeasure a r =
        iteratedDeriv 2 (cgf Real.log (gammaMeasure a r)) 0 := by
    symm
    simpa only [hmean, zero_mul, exp_zero, mul_one, mgf_zero, div_one]
      using hvariance
  rw [hcgf, hcumul]
  exact iteratedDeriv_two_gammaLogCGF_zero ha

end

end LogdetLean
