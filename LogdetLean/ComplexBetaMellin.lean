import LogdetLean.BetaMellin
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
/-!
# Complex Mellin transform and characteristic function of a log-Beta variable

The exact mathematical source for the Mellin quotient is Rouault (2007),
equation (2.10), printed p. 189.  Rouault states the real half-plane formula
`E[X^μ] = Γ(a+μ)Γ(a+b)/(Γ(a)Γ(a+b+μ))`, `μ > -a`.
The characteristic-function specialization and the finite Gamma product also
appear in Xie--Sun (2021), equations (13)--(16), printed pp. 435--436.

The proofs below do not import either published formula as an axiom.  They
derive the complex extension directly from mathlib's Beta density and complex
Beta integral, with the natural domain `Re z > -a` made explicit.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology ComplexConjugate

noncomputable section

set_option linter.style.haveILetI false

/-- The complex Gamma quotient in the Mellin transform of `Beta(α, β)`. -/
def complexBetaMellinQuotient (α β : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma ((α : ℂ) + z) * Complex.Gamma ((α + β : ℝ) : ℂ) /
    (Complex.Gamma (α : ℂ) * Complex.Gamma (((α + β : ℝ) : ℂ) + z))

private lemma ae_pos_betaMeasure_for_complexMellin (α β : ℝ) :
    ∀ᵐ x ∂betaMeasure α β, 0 < x := by
  rw [betaMeasure]
  refine (ae_withDensity_iff (μ := volume)
    (measurable_betaPDFReal α β).ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hpdf
  by_contra hx
  apply hpdf
  have hzero : betaPDFReal α β x = 0 := by
    rw [betaPDFReal, if_neg]
    exact fun hpos ↦ hx hpos.1
  rw [hzero]
  exact ENNReal.ofReal_zero

/-- The complex Mellin integrand is Bochner integrable on the natural
half-plane `Re z > -α`.  This is the domain accompanying Rouault (2007),
equation (2.10): the norm of `x^z` is the real exponential moment with
parameter `Re z`. -/
theorem integrable_cpow_betaMeasure {α β : ℝ} {z : ℂ}
    (hα : 0 < α) (hβ : 0 < β) (hαz : 0 < ((α : ℂ) + z).re) :
    Integrable (fun x : ℝ ↦ (x : ℂ) ^ z) (betaMeasure α β) := by
  have hreal : Integrable (fun x : ℝ ↦ Real.exp (z.re * Real.log x))
      (betaMeasure α β) :=
    integrable_exp_mul_log_betaMeasure hα hβ (by
      simpa only [Complex.add_re, Complex.ofReal_re] using hαz)
  have hcomplex : Integrable
      (fun x : ℝ ↦ Complex.exp (z * (Real.log x : ℂ)))
      (betaMeasure α β) := by
    rw [← integrable_norm_iff (by fun_prop)]
    refine hreal.congr ?_
    filter_upwards with x
    simp [Complex.norm_exp, Complex.mul_re]
  refine hcomplex.congr ?_
  filter_upwards [ae_pos_betaMeasure_for_complexMellin α β] with x hx
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 1
  ring

/-- The real normalizing constant used by `betaMeasure`, coerced to `ℂ`, is
exactly mathlib's complex Beta integral at positive real parameters. -/
lemma ofReal_beta_eq_complexBetaIntegral {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    (beta α β : ℂ) = Complex.betaIntegral (α : ℂ) (β : ℂ) := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div (α : ℂ) (β : ℂ)
    (by simpa) (by simpa)]
  simp only [beta, Complex.Gamma_ofReal]
  push_cast
  rw [show (α : ℂ) + (β : ℂ) = ((α + β : ℝ) : ℂ) by simp,
    Complex.Gamma_ofReal]

/-- On the open Beta support, multiplication by a complex power shifts the
first complex Beta-integral parameter. -/
lemma cpow_mul_betaPDFReal_complex {α β : ℝ} {z : ℂ} {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    ((betaPDFReal α β x : ℝ) : ℂ) * (x : ℂ) ^ z =
      ((1 / beta α β : ℝ) : ℂ) *
        ((x : ℂ) ^ ((α : ℂ) + z - 1) *
          (1 - (x : ℂ)) ^ ((β : ℂ) - 1)) := by
  rw [betaPDFReal, if_pos ⟨hx.1, hx.2⟩]
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  have h1x0 : ((1 - x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hx.2.ne')
  push_cast
  rw [Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  have hpow :
      (x : ℂ) ^ ((α : ℂ) - 1) * (x : ℂ) ^ z =
        (x : ℂ) ^ ((α : ℂ) + z - 1) := by
    rw [← Complex.cpow_add _ _ hx0]
    congr 1
    ring
  calc
    1 / (beta α β : ℂ) * (x : ℂ) ^ ((α : ℂ) - 1) *
          (1 - (x : ℂ)) ^ ((β : ℂ) - 1) * (x : ℂ) ^ z =
        1 / (beta α β : ℂ) *
          ((x : ℂ) ^ ((α : ℂ) - 1) * (x : ℂ) ^ z) *
          (1 - (x : ℂ)) ^ ((β : ℂ) - 1) := by ring
    _ = 1 / (beta α β : ℂ) *
        ((x : ℂ) ^ ((α : ℂ) + z - 1) *
          (1 - (x : ℂ)) ^ ((β : ℂ) - 1)) := by rw [hpow]; ring

/-- Complex Mellin transform in Beta-integral form.  The condition
`0 < Re(α+z)` is the exact integrability domain needed at the origin. -/
theorem integral_cpow_betaMeasure_eq_betaIntegral_quotient
    {α β : ℝ} {z : ℂ} (hα : 0 < α) (hβ : 0 < β)
    (_hαz : 0 < ((α : ℂ) + z).re) :
    (∫ x : ℝ, (x : ℂ) ^ z ∂betaMeasure α β) =
      Complex.betaIntegral ((α : ℂ) + z) (β : ℂ) /
        Complex.betaIntegral (α : ℂ) (β : ℂ) := by
  rw [betaMeasure]
  change (∫ x : ℝ, (x : ℂ) ^ z ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (betaPDFReal α β x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_betaPDFReal α β).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
    (betaPDFReal_nonneg_of_pos hα hβ _)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (0 : ℝ) 1)]
  · calc
      (∫ x : ℝ in Ioo 0 1,
          ((betaPDFReal α β x : ℝ) : ℂ) * (x : ℂ) ^ z) =
          ∫ x : ℝ in Ioo 0 1,
            ((1 / beta α β : ℝ) : ℂ) *
              ((x : ℂ) ^ ((α : ℂ) + z - 1) *
                (1 - (x : ℂ)) ^ ((β : ℂ) - 1)) := by
            apply setIntegral_congr_fun measurableSet_Ioo
            intro x hx
            exact cpow_mul_betaPDFReal_complex hx
      _ = ((1 / beta α β : ℝ) : ℂ) *
          ∫ x : ℝ in Ioo 0 1,
            ((x : ℂ) ^ ((α : ℂ) + z - 1) *
              (1 - (x : ℂ)) ^ ((β : ℂ) - 1)) := by
            rw [integral_const_mul]
      _ = ((1 / beta α β : ℝ) : ℂ) *
          Complex.betaIntegral ((α : ℂ) + z) (β : ℂ) := by
            rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
              integral_Ioc_eq_integral_Ioo]
      _ = Complex.betaIntegral ((α : ℂ) + z) (β : ℂ) /
          Complex.betaIntegral (α : ℂ) (β : ℂ) := by
            rw [← ofReal_beta_eq_complexBetaIntegral hα hβ]
            push_cast
            rw [div_eq_mul_inv]
            ring
  · intro x hx
    rw [betaPDFReal, if_neg]
    · simp
    · simpa only [mem_Ioo] using hx

/-- Complex Mellin transform in Gamma-quotient form.  This is the exact
complex extension of Rouault (2007), equation (2.10). -/
theorem integral_cpow_betaMeasure_eq_complexBetaMellinQuotient
    {α β : ℝ} {z : ℂ} (hα : 0 < α) (hβ : 0 < β)
    (hαz : 0 < ((α : ℂ) + z).re) :
    (∫ x : ℝ, (x : ℂ) ^ z ∂betaMeasure α β) =
      complexBetaMellinQuotient α β z := by
  rw [integral_cpow_betaMeasure_eq_betaIntegral_quotient hα hβ hαz]
  rw [Complex.betaIntegral_eq_Gamma_mul_div ((α : ℂ) + z) (β : ℂ)
      hαz (by simpa),
    Complex.betaIntegral_eq_Gamma_mul_div (α : ℂ) (β : ℂ)
      (by simpa) (by simpa)]
  unfold complexBetaMellinQuotient
  have hGa : Complex.Gamma (α : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa)
  have hGb : Complex.Gamma (β : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa)
  have hGab : Complex.Gamma ((α : ℂ) + (β : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using add_pos hα hβ)
  have hGazb : Complex.Gamma (((α : ℂ) + z) + (β : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      rw [Complex.add_re]
      simpa using add_pos hαz hβ)
  rw [show ((α : ℂ) + (β : ℂ)) = ((α + β : ℝ) : ℂ) by simp]
  rw [show ((α : ℂ) + z) + (β : ℂ) = ((α + β : ℝ) : ℂ) + z by
    push_cast
    ring]
  field_simp

/-- The Gamma quotient has no zero in its natural half-plane.  This fact is
needed before taking a logarithm in the later Edgeworth analysis. -/
theorem complexBetaMellinQuotient_ne_zero
    {α β : ℝ} {z : ℂ} (hα : 0 < α) (hβ : 0 < β)
    (hαz : 0 < ((α : ℂ) + z).re) :
    complexBetaMellinQuotient α β z ≠ 0 := by
  unfold complexBetaMellinQuotient
  apply div_ne_zero
  · exact mul_ne_zero
      (Complex.Gamma_ne_zero_of_re_pos hαz)
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using add_pos hα hβ))
  · exact mul_ne_zero
      (Complex.Gamma_ne_zero_of_re_pos (by simpa))
      (Complex.Gamma_ne_zero_of_re_pos (by
        simp only [Complex.add_re, Complex.ofReal_re] at hαz ⊢
        linarith))

/-- On the support of a Beta law, the probability character
`exp(i t log x)` equals the complex power `x^(it)` almost everywhere. -/
lemma cexp_mul_log_ae_eq_cpow (α β t : ℝ) :
    (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (Real.log x : ℂ) * Complex.I))
      =ᵐ[betaMeasure α β]
    (fun x : ℝ ↦ (x : ℂ) ^ ((t : ℂ) * Complex.I)) := by
  rw [betaMeasure]
  change (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (Real.log x : ℂ) * Complex.I))
      =ᵐ[volume.withDensity
        (fun x ↦ ENNReal.ofReal (betaPDFReal α β x))]
      (fun x : ℝ ↦ (x : ℂ) ^ ((t : ℂ) * Complex.I))
  refine (ae_withDensity_iff (μ := volume)
    (measurable_betaPDFReal α β).ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hpdf
  have hx : 0 < x := by
    by_contra hx'
    apply hpdf
    have hzero : betaPDFReal α β x = 0 := by
      rw [betaPDFReal, if_neg]
      exact fun hpos ↦ hx' hpos.1
    rw [hzero]
    exact ENNReal.ofReal_zero
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 1
  ring

/-- The probability-character kernel used for the log-Beta characteristic
function is integrable.  It is the pure-imaginary specialization of the
half-plane integrability theorem above. -/
theorem integrable_cexp_mul_log_betaMeasure
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    Integrable
      (fun x : ℝ ↦ Complex.exp
        ((t : ℂ) * (Real.log x : ℂ) * Complex.I))
      (betaMeasure α β) := by
  refine (integrable_cpow_betaMeasure hα hβ (z := (t : ℂ) * Complex.I)
    (by simpa)).congr ?_
  exact (cexp_mul_log_ae_eq_cpow α β t).symm

/-- Characteristic function of one log-Beta factor, in the exact Gamma
quotient used in Xie--Sun (2021), equations (13)--(16). -/
theorem charFun_map_log_betaMeasure_eq_complexBetaMellinQuotient
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    charFun ((betaMeasure α β).map Real.log) t =
      complexBetaMellinQuotient α β ((t : ℂ) * Complex.I) := by
  rw [charFun_apply_real]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_congr_ae (cexp_mul_log_ae_eq_cpow α β t)]
  exact integral_cpow_betaMeasure_eq_complexBetaMellinQuotient hα hβ (by simpa)

/-- The characteristic function of one log-Beta factor is nonzero at every
real frequency. -/
theorem charFun_map_log_betaMeasure_ne_zero
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    charFun ((betaMeasure α β).map Real.log) t ≠ 0 := by
  rw [charFun_map_log_betaMeasure_eq_complexBetaMellinQuotient hα hβ]
  exact complexBetaMellinQuotient_ne_zero hα hβ (by simpa)

end

end LogdetLean
