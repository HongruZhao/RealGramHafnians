import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic
import LogdetLean.NormalScaleComparison
import LogdetLean.SignedDensityFourierSmoothing
import LogdetLean.SignedEdgeworthComparator
/-!
# Density and Fourier transform of the signed first Edgeworth comparator

This file proves, without treating the comparator as a probability law, that
the real function

`phi(x) * (1 - a * (x^3 - 3*x))`

has cumulative function `Phi(x) - a(1-x^2)phi(x)` and Fourier transform
`exp(-t^2/2) * (1 + I*a*t^3)`.  The calculation is the elementary Hermite
integration-by-parts argument used in classical first-order Edgeworth
expansions.  Unlike the smoothing inequality in
`FejerSmoothingFourier.lean`, no external analytic theorem is imported for
these identities: the mass, CDF, Fourier transform, and quantitative bounds
are derived below from mathlib's Gaussian integral and differentiation
lemmas.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology

noncomputable section

/-- The signed density whose cumulative function is the first Edgeworth
comparator. -/
def signedFirstEdgeworthDensity (a x : ℝ) : ℝ :=
  standardNormalDensity x * (1 - a * (x ^ 3 - 3 * x))

/-- The third probabilists' Hermite polynomial times the standard Gaussian
density. -/
def thirdHermiteGaussian (x : ℝ) : ℝ :=
  (x ^ 3 - 3 * x) * standardNormalDensity x

theorem signedFirstEdgeworthDensity_eq (a x : ℝ) :
    signedFirstEdgeworthDensity a x =
      standardNormalDensity x - a * thirdHermiteGaussian x := by
  unfold signedFirstEdgeworthDensity thirdHermiteGaussian
  ring

theorem integrable_pow_mul_standardNormalDensity (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n * standardNormalDensity x) := by
  have habs : Integrable (fun x : ℝ ↦ ‖(id x)‖ ^ n)
      (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (n : ENNReal) (by simp)).integrable_norm_pow'
  have hpow : Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 1) := by
    apply habs.mono
    · fun_prop
    · exact Filter.Eventually.of_forall fun x ↦ by
        simp only [id_eq, norm_pow]
        rw [Real.norm_of_nonneg (norm_nonneg x)]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)] at hpow
  have hdens := (integrable_withDensity_iff
    (measurable_gaussianPDF 0 1)
    (Filter.Eventually.of_forall fun x ↦ gaussianPDF_lt_top)).1 hpow
  apply hdens.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change x ^ n * (gaussianPDF 0 1 x).toReal =
      x ^ n * standardNormalDensity x
    rw [toReal_gaussianPDF]
    rw [← standardNormalDensity_eq_gaussianPDFReal]

theorem integrable_standardNormalDensity :
    Integrable standardNormalDensity := by
  simpa using integrable_pow_mul_standardNormalDensity 0

theorem integrable_mul_standardNormalDensity :
    Integrable (fun x : ℝ ↦ x * standardNormalDensity x) := by
  simpa using integrable_pow_mul_standardNormalDensity 1

theorem integrable_thirdHermiteGaussian :
    Integrable thirdHermiteGaussian := by
  have h3 := integrable_pow_mul_standardNormalDensity 3
  have h1 := integrable_mul_standardNormalDensity.const_mul 3
  apply (h3.sub h1).congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change x ^ 3 * standardNormalDensity x -
      3 * (x * standardNormalDensity x) = thirdHermiteGaussian x
    unfold thirdHermiteGaussian
    ring

theorem integrable_signedFirstEdgeworthDensity (a : ℝ) :
    Integrable (signedFirstEdgeworthDensity a) := by
  rw [show signedFirstEdgeworthDensity a = fun x ↦
      standardNormalDensity x - a * thirdHermiteGaussian x by
    funext x
    exact signedFirstEdgeworthDensity_eq a x]
  exact integrable_standardNormalDensity.sub
    (integrable_thirdHermiteGaussian.const_mul a)

theorem integrable_id_mul_signedFirstEdgeworthDensity (a : ℝ) :
    Integrable (fun x : ℝ ↦ x * signedFirstEdgeworthDensity a x) := by
  have h1 := integrable_pow_mul_standardNormalDensity 1
  have h4 := integrable_pow_mul_standardNormalDensity 4
  have h2 := (integrable_pow_mul_standardNormalDensity 2).const_mul 3
  have hH : Integrable (fun x : ℝ ↦
      x * thirdHermiteGaussian x) := by
    apply (h4.sub h2).congr
    exact Filter.Eventually.of_forall fun x ↦ by
      change x ^ 4 * standardNormalDensity x -
        3 * (x ^ 2 * standardNormalDensity x) =
          x * thirdHermiteGaussian x
      unfold thirdHermiteGaussian
      ring
  apply (h1.sub (hH.const_mul a)).congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change x ^ 1 * standardNormalDensity x -
      a * (x * thirdHermiteGaussian x) =
        x * signedFirstEdgeworthDensity a x
    rw [signedFirstEdgeworthDensity_eq]
    ring

theorem hasDerivAt_standardNormalDensity (x : ℝ) :
    HasDerivAt standardNormalDensity
      (-x * standardNormalDensity x) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ -(y ^ 2) / 2) (-x) x := by
    rw [show -x = -(2 * x) / 2 by ring]
    simpa [Pi.neg_apply, Pi.div_apply]
      using (((hasDerivAt_pow 2 x).neg).div_const 2)
  have h := ((Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x hinner).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  change HasDerivAt
    (fun y : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(y ^ 2) / 2))
    (-x * ((Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(x ^ 2) / 2))) x
  have hfun : (fun y : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(y ^ 2) / 2)) =
      fun y : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp ∘ fun z : ℝ ↦ -(z ^ 2) / 2) y := by rfl
  have hval : -x * ((Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(x ^ 2) / 2)) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-(x ^ 2) / 2) * -x) := by ring
  rw [hfun, hval]
  exact h

theorem hasDerivAt_mul_standardNormalDensity (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y * standardNormalDensity y)
      (normalEdgeworthShape x) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_standardNormalDensity x)
  have heq : 1 * standardNormalDensity x +
      x * (-x * standardNormalDensity x) = normalEdgeworthShape x := by
    unfold normalEdgeworthShape
    ring
  rw [← heq]
  change HasDerivAt (id * standardNormalDensity)
    (1 * standardNormalDensity x +
      x * (-x * standardNormalDensity x)) x
  exact h

theorem hasDerivAt_normalEdgeworthShape (x : ℝ) :
    HasDerivAt normalEdgeworthShape (thirdHermiteGaussian x) x := by
  have hpoly : HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-2 * x) x := by
    have hp := (hasDerivAt_pow 2 x).const_sub 1
    rw [show -2 * x = -(2 * x) by ring]
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hp
  have h := hpoly.mul (hasDerivAt_standardNormalDensity x)
  have heq : -2 * x * standardNormalDensity x +
      (1 - x ^ 2) * (-x * standardNormalDensity x) =
        thirdHermiteGaussian x := by
    unfold thirdHermiteGaussian
    ring
  rw [← heq]
  change HasDerivAt
    ((fun y : ℝ ↦ 1 - y ^ 2) * standardNormalDensity)
    (-2 * x * standardNormalDensity x +
      (1 - x ^ 2) * (-x * standardNormalDensity x)) x
  exact h

theorem integrable_normalEdgeworthShape :
    Integrable normalEdgeworthShape := by
  have h0 := integrable_standardNormalDensity
  have h2 := integrable_pow_mul_standardNormalDensity 2
  apply (h0.sub h2).congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change standardNormalDensity x - x ^ 2 * standardNormalDensity x =
      normalEdgeworthShape x
    unfold normalEdgeworthShape
    ring

/-- Multiplication by the unit-modulus Fourier phase preserves
integrability. -/
theorem integrable_edgeworthPhase_mul_ofReal
    {f : ℝ → ℝ} (hf : Integrable f) (t : ℝ) :
    Integrable (fun x : ℝ ↦
      Complex.exp (↑(x * t) * Complex.I) * (f x : ℂ)) := by
  have hfc : Integrable (fun x : ℝ ↦ (f x : ℂ)) := hf.ofReal
  apply hfc.mono
  · fun_prop
  · exact Filter.Eventually.of_forall fun x ↦ by
      rw [Complex.norm_mul, Complex.norm_exp]
      simp

theorem hasDerivAt_edgeworthPhase (t x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.exp (↑(y * t) * Complex.I))
      (((t : ℂ) * Complex.I) *
        Complex.exp (↑(x * t) * Complex.I)) x := by
  let F : ℂ → ℂ := fun z ↦
    Complex.exp ((z * (t : ℂ)) * Complex.I)
  have hinner : HasDerivAt (fun z : ℂ ↦
      (z * (t : ℂ)) * Complex.I) ((t : ℂ) * Complex.I) (x : ℂ) := by
    convert! ((hasDerivAt_id (x : ℂ)).mul_const
      (t : ℂ)).mul_const Complex.I using 1
    all_goals ring
  have hF : HasDerivAt F
      (((t : ℂ) * Complex.I) *
        Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I)) (x : ℂ) := by
    convert! (Complex.hasDerivAt_exp _).comp (x : ℂ) hinner using 1
    all_goals ring
  simpa [F] using hF.comp_ofReal

/-- One-step Fourier integration by parts.  It is stated for real `v` and
then complexified, which is exactly what the Hermite calculation needs. -/
theorem integral_edgeworthPhase_mul_deriv
    (v v' : ℝ → ℝ)
    (hvderiv : ∀ x, HasDerivAt v (v' x) x)
    (hv : Integrable v) (hv' : Integrable v') (t : ℝ) :
    (∫ x : ℝ,
        Complex.exp (↑(x * t) * Complex.I) * (v' x : ℂ)) =
      -((t : ℂ) * Complex.I) *
        ∫ x : ℝ,
          Complex.exp (↑(x * t) * Complex.I) * (v x : ℂ) := by
  let u : ℝ → ℂ := fun x ↦ Complex.exp (↑(x * t) * Complex.I)
  let u' : ℝ → ℂ := fun x ↦
    ((t : ℂ) * Complex.I) * Complex.exp (↑(x * t) * Complex.I)
  let w : ℝ → ℂ := fun x ↦ (v x : ℂ)
  let w' : ℝ → ℂ := fun x ↦ (v' x : ℂ)
  have hu : ∀ x ∈ tsupport w, HasDerivAt u (u' x) x := by
    intro x _hx
    exact hasDerivAt_edgeworthPhase t x
  have hw : ∀ x ∈ tsupport u, HasDerivAt w (w' x) x := by
    intro x _hx
    exact (hvderiv x).ofReal_comp
  have huw' : Integrable (u * w') := by
    change Integrable (fun x : ℝ ↦
      Complex.exp (↑(x * t) * Complex.I) * (v' x : ℂ))
    exact integrable_edgeworthPhase_mul_ofReal hv' t
  have huw : Integrable (u * w) := by
    change Integrable (fun x : ℝ ↦
      Complex.exp (↑(x * t) * Complex.I) * (v x : ℂ))
    exact integrable_edgeworthPhase_mul_ofReal hv t
  have hu'w : Integrable (u' * w) := by
    have hbase := integrable_edgeworthPhase_mul_ofReal hv t
    apply (hbase.const_mul ((t : ℂ) * Complex.I)).congr
    exact Filter.Eventually.of_forall fun x ↦ by
      simp only [u', w, Pi.mul_apply]
      ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    hu hw huw' hu'w huw
  calc
    (∫ x : ℝ,
        Complex.exp (↑(x * t) * Complex.I) * (v' x : ℂ)) =
        ∫ x : ℝ, u x * w' x := by rfl
    _ = -(∫ x : ℝ, u' x * w x) := hibp
    _ = -(((t : ℂ) * Complex.I) *
        ∫ x : ℝ,
          Complex.exp (↑(x * t) * Complex.I) * (v x : ℂ)) := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        simp only [u', w]
        ring
    _ = -((t : ℂ) * Complex.I) *
        ∫ x : ℝ,
          Complex.exp (↑(x * t) * Complex.I) * (v x : ℂ) := by ring

theorem signedDensityCDF_thirdHermiteGaussian (x : ℝ) :
    signedDensityCDF thirdHermiteGaussian x = normalEdgeworthShape x := by
  unfold signedDensityCDF
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := x) (m := 0)
    (fun y _hy ↦ hasDerivAt_normalEdgeworthShape y)
    integrable_thirdHermiteGaussian.integrableOn (by
      have h0c := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
        (a := (1 / 2 : ℝ)) (by norm_num) (0 : ℝ)
      have h2c := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
        (a := (1 / 2 : ℝ)) (by norm_num) (2 : ℝ)
      have h0 : Tendsto (fun y : ℝ ↦ Real.exp (-(y ^ 2) / 2))
          atBot (nhds 0) := by
        have := h0c.mono_left atBot_le_cocompact
        convert this using 1
        funext y
        simp only [Real.rpow_zero, one_mul]
        congr 1
        ring
      have h2 : Tendsto
          (fun y : ℝ ↦ y ^ 2 * Real.exp (-(y ^ 2) / 2))
          atBot (nhds 0) := by
        have := h2c.mono_left atBot_le_cocompact
        convert this using 1
        funext y
        rw [Real.rpow_two, sq_abs]
        rw [show -(y ^ 2) / 2 = -(1 / 2 : ℝ) * y ^ 2 by ring]
      have hdiff := h0.sub h2
      let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
      have hc : Tendsto (fun _ : ℝ ↦ c) atBot (nhds c) :=
        tendsto_const_nhds
      have hmul := hc.mul hdiff
      have hfun : normalEdgeworthShape = fun y : ℝ ↦
          c * (Real.exp (-(y ^ 2) / 2) -
            y ^ 2 * Real.exp (-(y ^ 2) / 2)) := by
        funext y
        unfold normalEdgeworthShape standardNormalDensity gaussianCore c
        ring
      rw [hfun]
      simpa using hmul)
  simpa using h

theorem signedDensityCDF_signedFirstEdgeworthDensity (a x : ℝ) :
    signedDensityCDF (signedFirstEdgeworthDensity a) x =
      signedFirstEdgeworthCDF a x := by
  unfold signedDensityCDF
  have hphi : IntegrableOn standardNormalDensity (Iic x) :=
    integrable_standardNormalDensity.integrableOn
  have hH : IntegrableOn (fun y : ℝ ↦ a * thirdHermiteGaussian y)
      (Iic x) := (integrable_thirdHermiteGaussian.const_mul a).integrableOn
  rw [show signedFirstEdgeworthDensity a = fun y : ℝ ↦
      standardNormalDensity y - a * thirdHermiteGaussian y by
    funext y
    exact signedFirstEdgeworthDensity_eq a y]
  rw [integral_sub hphi hH, integral_const_mul]
  unfold signedFirstEdgeworthCDF
  rw [standardGaussian_cdf_eq_integral_Iic]
  have hphiEq : (∫ y : ℝ in Iic x, standardNormalDensity y) =
      ∫ y : ℝ in Iic x, gaussianPDFReal 0 1 y := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro y _hy
    exact standardNormalDensity_eq_gaussianPDFReal y
  have hHEq : (∫ y : ℝ in Iic x, thirdHermiteGaussian y) =
      normalEdgeworthShape x := by
    simpa only [signedDensityCDF] using
      signedDensityCDF_thirdHermiteGaussian x
  rw [hphiEq, hHEq]

theorem integral_thirdHermiteGaussian :
    ∫ x : ℝ, thirdHermiteGaussian x = 0 := by
  have hneg := integral_neg_eq_self thirdHermiteGaussian volume
  have hodd : (fun x : ℝ ↦ thirdHermiteGaussian (-x)) =
      fun x : ℝ ↦ -thirdHermiteGaussian x := by
    funext x
    unfold thirdHermiteGaussian standardNormalDensity gaussianCore
    rw [neg_sq]
    ring
  rw [hodd, integral_neg] at hneg
  linarith

theorem integral_signedFirstEdgeworthDensity (a : ℝ) :
    ∫ x : ℝ, signedFirstEdgeworthDensity a x = 1 := by
  rw [show signedFirstEdgeworthDensity a = fun x : ℝ ↦
      standardNormalDensity x - a * thirdHermiteGaussian x by
    funext x
    exact signedFirstEdgeworthDensity_eq a x]
  rw [integral_sub integrable_standardNormalDensity
    (integrable_thirdHermiteGaussian.const_mul a), integral_const_mul,
    integral_thirdHermiteGaussian, mul_zero, sub_zero]
  simpa only [standardNormalDensity_eq_gaussianPDFReal] using
    integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : NNReal) ≠ 0)

theorem signedDensityFourier_standardNormalDensity (t : ℝ) :
    signedDensityFourier standardNormalDensity t =
      Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
  rw [signedDensityFourier]
  calc
    (∫ y : ℝ, Complex.exp (↑(y * t) * Complex.I) *
        (standardNormalDensity y : ℂ)) =
        ∫ y : ℝ, Complex.exp (↑(y * t) * Complex.I)
          ∂(gaussianReal 0 1) := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        change Complex.exp (↑(y * t) * Complex.I) *
            (standardNormalDensity y : ℂ) =
          gaussianPDFReal 0 1 y • Complex.exp (↑(y * t) * Complex.I)
        rw [← standardNormalDensity_eq_gaussianPDFReal]
        simp [mul_comm]
    _ = charFun (gaussianReal 0 1) t := by
      rw [charFun_eq_integral_probChar]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        simp [probChar_apply, mul_comm]
    _ = Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
      rw [charFun_gaussianReal]
      congr 1
      push_cast
      ring

theorem signedDensityFourier_thirdHermiteGaussian (t : ℝ) :
    signedDensityFourier thirdHermiteGaussian t =
      -(Complex.I * (t : ℂ) ^ 3) *
        Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
  let F0 : ℂ := ∫ x : ℝ,
    Complex.exp (↑(x * t) * Complex.I) * (standardNormalDensity x : ℂ)
  let F1 : ℂ := ∫ x : ℝ,
    Complex.exp (↑(x * t) * Complex.I) *
      (x * standardNormalDensity x : ℂ)
  let F2 : ℂ := ∫ x : ℝ,
    Complex.exp (↑(x * t) * Complex.I) *
      (normalEdgeworthShape x : ℂ)
  let F3 : ℂ := ∫ x : ℝ,
    Complex.exp (↑(x * t) * Complex.I) *
      (thirdHermiteGaussian x : ℂ)
  have hnegphi : Integrable
      (fun x : ℝ ↦ -x * standardNormalDensity x) := by
    apply integrable_mul_standardNormalDensity.neg.congr
    exact Filter.Eventually.of_forall fun x ↦ by
      change -(x * standardNormalDensity x) =
        -x * standardNormalDensity x
      ring
  have hstep0 := integral_edgeworthPhase_mul_deriv
    standardNormalDensity
    (fun x : ℝ ↦ -x * standardNormalDensity x)
    hasDerivAt_standardNormalDensity integrable_standardNormalDensity
    hnegphi t
  have hleft0 : (∫ x : ℝ,
      Complex.exp (↑(x * t) * Complex.I) *
        ((-x * standardNormalDensity x : ℝ) : ℂ)) = -F1 := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      dsimp [F1]
      push_cast
      ring
  rw [hleft0] at hstep0
  have hF1 : F1 = ((t : ℂ) * Complex.I) * F0 := by
    calc
      F1 = -(-F1) := by ring
      _ = -(-((t : ℂ) * Complex.I) * F0) := by rw [hstep0]
      _ = ((t : ℂ) * Complex.I) * F0 := by ring
  have hstep1 := integral_edgeworthPhase_mul_deriv
    (fun x : ℝ ↦ x * standardNormalDensity x)
    normalEdgeworthShape hasDerivAt_mul_standardNormalDensity
    integrable_mul_standardNormalDensity integrable_normalEdgeworthShape t
  have hstep1' : F2 = -((t : ℂ) * Complex.I) * F1 := by
    simpa [F1, F2] using hstep1
  have hF2 : F2 = (t : ℂ) ^ 2 * F0 := by
    calc
      F2 = -((t : ℂ) * Complex.I) * F1 := hstep1'
      _ = -((t : ℂ) * Complex.I) *
          (((t : ℂ) * Complex.I) * F0) := by rw [hF1]
      _ = -((t : ℂ) ^ 2 * Complex.I ^ 2) * F0 := by ring
      _ = (t : ℂ) ^ 2 * F0 := by rw [Complex.I_sq]; ring
  have hstep2 := integral_edgeworthPhase_mul_deriv
    normalEdgeworthShape thirdHermiteGaussian
    hasDerivAt_normalEdgeworthShape integrable_normalEdgeworthShape
    integrable_thirdHermiteGaussian t
  change F3 = -((t : ℂ) * Complex.I) * F2 at hstep2
  have hF3 : F3 = -(Complex.I * (t : ℂ) ^ 3) * F0 := by
    calc
      F3 = -((t : ℂ) * Complex.I) * F2 := hstep2
      _ = -((t : ℂ) * Complex.I) * ((t : ℂ) ^ 2 * F0) := by
        rw [hF2]
      _ = -(Complex.I * (t : ℂ) ^ 3) * F0 := by ring
  change F3 = _
  rw [hF3]
  have hF0 : F0 = signedDensityFourier standardNormalDensity t := by rfl
  rw [hF0, signedDensityFourier_standardNormalDensity]

theorem signedDensityFourier_signedFirstEdgeworthDensity (a t : ℝ) :
    signedDensityFourier (signedFirstEdgeworthDensity a) t =
      Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) *
        (1 + Complex.I * (a : ℂ) * (t : ℂ) ^ 3) := by
  have hphi := integrable_edgeworthPhase_mul_ofReal
    integrable_standardNormalDensity t
  have hH := integrable_edgeworthPhase_mul_ofReal
    integrable_thirdHermiteGaussian t
  rw [signedDensityFourier]
  calc
    (∫ x : ℝ, Complex.exp (↑(x * t) * Complex.I) *
        (signedFirstEdgeworthDensity a x : ℂ)) =
        ∫ x : ℝ,
          (Complex.exp (↑(x * t) * Complex.I) *
              (standardNormalDensity x : ℂ) -
            (a : ℂ) *
              (Complex.exp (↑(x * t) * Complex.I) *
                (thirdHermiteGaussian x : ℂ))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change Complex.exp (↑(x * t) * Complex.I) *
            (signedFirstEdgeworthDensity a x : ℂ) =
          Complex.exp (↑(x * t) * Complex.I) *
              (standardNormalDensity x : ℂ) -
            (a : ℂ) *
              (Complex.exp (↑(x * t) * Complex.I) *
                (thirdHermiteGaussian x : ℂ))
        rw [signedFirstEdgeworthDensity_eq]
        push_cast
        ring
    _ = (∫ x : ℝ,
          Complex.exp (↑(x * t) * Complex.I) *
            (standardNormalDensity x : ℂ)) -
        ∫ x : ℝ, (a : ℂ) *
          (Complex.exp (↑(x * t) * Complex.I) *
            (thirdHermiteGaussian x : ℂ)) := by
      rw [integral_sub hphi (hH.const_mul (a : ℂ))]
    _ = signedDensityFourier standardNormalDensity t -
        (a : ℂ) * signedDensityFourier thirdHermiteGaussian t := by
      rw [integral_const_mul]
      rfl
    _ = _ := by
      rw [signedDensityFourier_standardNormalDensity,
        signedDensityFourier_thirdHermiteGaussian]
      ring

/-! ## Uniform analytic certificates for smoothing -/

theorem abs_cube_mul_exp_neg_sq_half_le_eight (x : ℝ) :
    |x| ^ 3 * Real.exp (-(x ^ 2) / 2) ≤ 8 := by
  let y : ℝ := |x|
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hexple : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg x]
  by_cases hy1 : y ≤ 1
  · have hy3 : y ^ 3 ≤ 1 := by nlinarith [sq_nonneg y]
    calc
      |x| ^ 3 * Real.exp (-(x ^ 2) / 2) =
          y ^ 3 * Real.exp (-(x ^ 2) / 2) := by rfl
      _ ≤ 1 * 1 := mul_le_mul hy3 hexple (Real.exp_nonneg _) (by positivity)
      _ ≤ 8 := by norm_num
  · have hyone : 1 ≤ y := le_of_not_ge hy1
    have hseries := Real.pow_div_factorial_le_exp
      (y ^ 2 / 2) (by positivity) 2
    have hbase : y ^ 4 / 8 ≤ Real.exp (y ^ 2 / 2) := by
      convert hseries using 1
      all_goals norm_num
      all_goals ring
    have hmul := mul_le_mul_of_nonneg_right hbase
      (Real.exp_nonneg (-(y ^ 2) / 2))
    have hquart : y ^ 4 / 8 * Real.exp (-(y ^ 2) / 2) ≤ 1 := by
      calc
        y ^ 4 / 8 * Real.exp (-(y ^ 2) / 2) ≤
            Real.exp (y ^ 2 / 2) * Real.exp (-(y ^ 2) / 2) := hmul
        _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have hcubquart : y ^ 3 / 8 * Real.exp (-(y ^ 2) / 2) ≤ 1 := by
      calc
        y ^ 3 / 8 * Real.exp (-(y ^ 2) / 2) ≤
            y ^ 4 / 8 * Real.exp (-(y ^ 2) / 2) := by
          gcongr
          nlinarith [mul_nonneg hy (sq_nonneg y)]
        _ ≤ 1 := hquart
    have hfinal : y ^ 3 * Real.exp (-(y ^ 2) / 2) ≤ 8 := by
      calc
        y ^ 3 * Real.exp (-(y ^ 2) / 2) =
            8 * (y ^ 3 / 8 * Real.exp (-(y ^ 2) / 2)) := by ring
        _ ≤ 8 * 1 := mul_le_mul_of_nonneg_left hcubquart (by norm_num)
        _ = 8 := by ring
    simpa [y, sq_abs] using hfinal

theorem abs_thirdHermiteGaussian_le (x : ℝ) :
    |thirdHermiteGaussian x| ≤
      11 / Real.sqrt (2 * Real.pi) := by
  have hcub := abs_cube_mul_exp_neg_sq_half_le_eight x
  have hlin := abs_mul_exp_neg_sq_half_le_one x
  have hpoly : |x ^ 3 - 3 * x| * Real.exp (-(x ^ 2) / 2) ≤ 11 := by
    calc
      |x ^ 3 - 3 * x| * Real.exp (-(x ^ 2) / 2) ≤
          (|x| ^ 3 + 3 * |x|) * Real.exp (-(x ^ 2) / 2) := by
        gcongr
        calc
          |x ^ 3 - 3 * x| ≤ |x ^ 3| + |3 * x| := abs_sub _ _
          _ = |x| ^ 3 + 3 * |x| := by
            rw [abs_pow, abs_mul]
            norm_num
      _ = |x| ^ 3 * Real.exp (-(x ^ 2) / 2) +
          3 * (|x| * Real.exp (-(x ^ 2) / 2)) := by ring
      _ ≤ 8 + 3 * 1 := by gcongr
      _ = 11 := by norm_num
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  unfold thirdHermiteGaussian standardNormalDensity gaussianCore
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (inv_pos.mpr hsqrt)]
  calc
    |x ^ 3 - 3 * x| *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) =
        (|x ^ 3 - 3 * x| * Real.exp (-(x ^ 2) / 2)) /
          Real.sqrt (2 * Real.pi) := by field_simp
    _ ≤ 11 / Real.sqrt (2 * Real.pi) :=
      div_le_div_of_nonneg_right hpoly hsqrt.le

def signedFirstEdgeworthLipschitzConstant (a : ℝ) : ℝ :=
  (1 + 11 * |a|) / Real.sqrt (2 * Real.pi)

theorem signedFirstEdgeworthLipschitzConstant_nonneg (a : ℝ) :
    0 ≤ signedFirstEdgeworthLipschitzConstant a := by
  unfold signedFirstEdgeworthLipschitzConstant
  positivity

theorem abs_signedFirstEdgeworthDensity_le (a x : ℝ) :
    |signedFirstEdgeworthDensity a x| ≤
      signedFirstEdgeworthLipschitzConstant a := by
  have hphi : |standardNormalDensity x| ≤
      1 / Real.sqrt (2 * Real.pi) := by
    unfold standardNormalDensity gaussianCore
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (inv_pos.mpr (by positivity : 0 < Real.sqrt (2 * Real.pi)))]
    have he : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg x]
    simpa [one_div] using mul_le_mul_of_nonneg_left he (by positivity :
      0 ≤ (Real.sqrt (2 * Real.pi))⁻¹)
  rw [signedFirstEdgeworthDensity_eq]
  calc
    |standardNormalDensity x - a * thirdHermiteGaussian x| ≤
        |standardNormalDensity x| + |a * thirdHermiteGaussian x| :=
      abs_sub _ _
    _ = |standardNormalDensity x| + |a| * |thirdHermiteGaussian x| := by
      rw [abs_mul]
    _ ≤ 1 / Real.sqrt (2 * Real.pi) +
        |a| * (11 / Real.sqrt (2 * Real.pi)) := by
      exact add_le_add hphi
        (mul_le_mul_of_nonneg_left (abs_thirdHermiteGaussian_le x)
          (abs_nonneg a))
    _ = signedFirstEdgeworthLipschitzConstant a := by
      unfold signedFirstEdgeworthLipschitzConstant
      field_simp [ne_of_gt (by positivity : 0 < Real.sqrt (2 * Real.pi))]

theorem hasDerivAt_signedFirstEdgeworthCDF (a x : ℝ) :
    HasDerivAt (signedFirstEdgeworthCDF a)
      (signedFirstEdgeworthDensity a x) x := by
  have hcdf : HasDerivAt
      (fun y : ℝ ↦ cdf (gaussianReal 0 1) y)
      (gaussianPDFReal 0 1 x) x := hasDerivAt_standardGaussian_cdf x
  have hshape : HasDerivAt
      (fun y : ℝ ↦ a * normalEdgeworthShape y)
      (a * thirdHermiteGaussian x) x :=
    (hasDerivAt_normalEdgeworthShape x).const_mul a
  have h := hcdf.sub hshape
  have hderiv : gaussianPDFReal 0 1 x - a * thirdHermiteGaussian x =
      signedFirstEdgeworthDensity a x := by
    rw [← standardNormalDensity_eq_gaussianPDFReal,
      signedFirstEdgeworthDensity_eq]
  rw [← hderiv]
  convert! h using 1

theorem signedFirstEdgeworthCDF_lipschitz (a : ℝ) :
    HasRealLipschitzBound (signedFirstEdgeworthCDF a)
      (signedFirstEdgeworthLipschitzConstant a) := by
  intro x y
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := signedFirstEdgeworthCDF a)
    (f' := signedFirstEdgeworthDensity a)
    (fun z _hz ↦ (hasDerivAt_signedFirstEdgeworthCDF a z).hasDerivWithinAt)
    (fun z _hz ↦ by
      rw [Real.norm_eq_abs]
      exact abs_signedFirstEdgeworthDensity_le a z)
    convex_univ (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using hmvt

theorem signedDensityCDF_signedFirstEdgeworthDensity_lipschitz (a : ℝ) :
    HasRealLipschitzBound
      (signedDensityCDF (signedFirstEdgeworthDensity a))
      (signedFirstEdgeworthLipschitzConstant a) := by
  have hfun : signedDensityCDF (signedFirstEdgeworthDensity a) =
      signedFirstEdgeworthCDF a := by
    funext x
    exact signedDensityCDF_signedFirstEdgeworthDensity a x
  rw [hfun]
  exact signedFirstEdgeworthCDF_lipschitz a

def signedFirstEdgeworthCDFUniformBound (a : ℝ) : ℝ :=
  1 + |a| / Real.sqrt (2 * Real.pi)

theorem signedFirstEdgeworthCDFUniformBound_nonneg (a : ℝ) :
    0 ≤ signedFirstEdgeworthCDFUniformBound a := by
  unfold signedFirstEdgeworthCDFUniformBound
  positivity

theorem abs_signedFirstEdgeworthCDF_le (a x : ℝ) :
    |signedFirstEdgeworthCDF a x| ≤
      signedFirstEdgeworthCDFUniformBound a := by
  have hcdf0 := cdf_nonneg (gaussianReal 0 1) x
  have hcdf1 := cdf_le_one (gaussianReal 0 1) x
  unfold signedFirstEdgeworthCDF signedFirstEdgeworthCDFUniformBound
  calc
    |cdf (gaussianReal 0 1) x - a * normalEdgeworthShape x| ≤
        |cdf (gaussianReal 0 1) x| + |a * normalEdgeworthShape x| :=
      abs_sub _ _
    _ = cdf (gaussianReal 0 1) x +
        |a| * |normalEdgeworthShape x| := by
      rw [abs_of_nonneg hcdf0, abs_mul]
    _ ≤ 1 + |a| * (1 / Real.sqrt (2 * Real.pi)) := by
      exact add_le_add hcdf1
        (mul_le_mul_of_nonneg_left (abs_normalEdgeworthShape_le x)
          (abs_nonneg a))
    _ = 1 + |a| / Real.sqrt (2 * Real.pi) := by ring

theorem continuous_signedFirstEdgeworthCDF (a : ℝ) :
    Continuous (signedFirstEdgeworthCDF a) :=
  continuous_iff_continuousAt.2 fun x ↦
    (hasDerivAt_signedFirstEdgeworthCDF a x).continuousAt

theorem continuous_signedDensityCDF_signedFirstEdgeworthDensity (a : ℝ) :
    Continuous (signedDensityCDF (signedFirstEdgeworthDensity a)) := by
  have hfun : signedDensityCDF (signedFirstEdgeworthDensity a) =
      signedFirstEdgeworthCDF a := by
    funext x
    exact signedDensityCDF_signedFirstEdgeworthDensity a x
  rw [hfun]
  exact continuous_signedFirstEdgeworthCDF a

/-- The signed Edgeworth CDF is bounded, so its Fejer smoothing integral
exists even though the Fejer law does not have a finite first absolute
moment. -/
theorem integrable_fejer_signedDensityCDF_shift
    (a x T : ℝ) :
    Integrable (fun z ↦
      signedDensityCDF (signedFirstEdgeworthDensity a) (x - z / T))
      fejerMeasure := by
  let K : ℝ := signedFirstEdgeworthCDFUniformBound a
  have hK : 0 ≤ K := by
    dsimp [K]
    exact signedFirstEdgeworthCDFUniformBound_nonneg a
  apply (integrable_const (K : ℝ)).mono
  · exact ((continuous_signedDensityCDF_signedFirstEdgeworthDensity a).comp
      (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK]
      rw [signedDensityCDF_signedFirstEdgeworthDensity]
      exact abs_signedFirstEdgeworthCDF_le a (x - z / T)

theorem cdf_sub_signedFirstEdgeworthDensityCDF_le
    (μ : Measure ℝ) (a x : ℝ) :
    |cdf μ x - signedDensityCDF (signedFirstEdgeworthDensity a) x| ≤
      2 + |a| / Real.sqrt (2 * Real.pi) := by
  have hcdf0 := cdf_nonneg μ x
  have hcdf1 := cdf_le_one μ x
  calc
    |cdf μ x - signedDensityCDF (signedFirstEdgeworthDensity a) x| ≤
        |cdf μ x| +
          |signedDensityCDF (signedFirstEdgeworthDensity a) x| := abs_sub _ _
    _ = cdf μ x + |signedFirstEdgeworthCDF a x| := by
      rw [abs_of_nonneg hcdf0,
        signedDensityCDF_signedFirstEdgeworthDensity]
    _ ≤ 1 + signedFirstEdgeworthCDFUniformBound a := by
      exact add_le_add hcdf1 (abs_signedFirstEdgeworthCDF_le a x)
    _ = 2 + |a| / Real.sqrt (2 * Real.pi) := by
      unfold signedFirstEdgeworthCDFUniformBound
      ring

/-- Closed Fourier formula paired with `signedFirstEdgeworthCDF a`. -/
def signedFirstEdgeworthFourier (a t : ℝ) : ℂ :=
  Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) *
    (1 + Complex.I * (a : ℂ) * (t : ℂ) ^ 3)

theorem signedDensityFourier_signedFirstEdgeworthDensity_eq (a : ℝ) :
    signedDensityFourier (signedFirstEdgeworthDensity a) =
      signedFirstEdgeworthFourier a := by
  funext t
  exact signedDensityFourier_signedFirstEdgeworthDensity a t

/-- Ready-to-use Fejer--Esseen inequality for the signed first Edgeworth
comparator.  All comparator-side analytic hypotheses are discharged here;
the caller supplies only the law's first moment and the local weighted
Fourier integrability. -/
theorem cdfComparatorDistance_signedFirstEdgeworth_le_fejer_esseen
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y : ℝ ↦ y) μ)
    (a : ℝ) {S : ℝ} (hS : 0 < S)
    (hint : IntegrableOn
      (fourierQuotientError (charFun μ) (signedFirstEdgeworthFourier a))
      (Icc (-S) S)) :
    cdfComparatorDistance μ (signedFirstEdgeworthCDF a) ≤
      (1 / Real.pi) *
        truncatedFourierDiscrepancy (charFun μ)
          (signedFirstEdgeworthFourier a) S +
      64 * Real.pi * signedFirstEdgeworthLipschitzConstant a / S := by
  have hfourier := signedDensityFourier_signedFirstEdgeworthDensity_eq a
  have hG : signedDensityCDF (signedFirstEdgeworthDensity a) =
      signedFirstEdgeworthCDF a := by
    funext x
    exact signedDensityCDF_signedFirstEdgeworthDensity a x
  have hint' : IntegrableOn
      (fourierQuotientError (charFun μ)
        (signedDensityFourier (signedFirstEdgeworthDensity a)))
      (Icc (-S) S) := by
    rw [hfourier]
    exact hint
  have h := cdfComparatorDistance_signedDensity_le_fejer_esseen
    μ hμ (signedFirstEdgeworthDensity a)
    (integrable_signedFirstEdgeworthDensity a)
    (integrable_id_mul_signedFirstEdgeworthDensity a)
    (integral_signedFirstEdgeworthDensity a) hS
    (signedFirstEdgeworthLipschitzConstant_nonneg a)
    (signedDensityCDF_signedFirstEdgeworthDensity_lipschitz a)
    (fun x ↦ integrable_fejer_signedDensityCDF_shift
      a x (S / (2 * Real.pi)))
    (fun x ↦ cdf_sub_signedFirstEdgeworthDensityCDF_le μ a x)
    hint'
  rw [hG, hfourier] at h
  exact h

end

end LogdetLean
