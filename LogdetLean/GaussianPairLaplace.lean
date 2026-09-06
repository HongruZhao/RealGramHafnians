import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Real

noncomputable section

def gaussianQuadraticIntegral (A B : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ *
    Real.exp (B ^ 2 / (4 * (A + 1 / 2))) *
    Real.sqrt (Real.pi / (A + 1 / 2))

lemma integral_exp_neg_mul_sq_add_mul_gaussianReal (A B : ℝ)
    (hA : -(1 / 2 : ℝ) < A) :
    ∫ x, Real.exp (-A * x ^ 2 + B * x) ∂gaussianReal 0 1 =
      gaussianQuadraticIntegral A B := by
  rw [integral_gaussianReal_eq_integral_smul
    (v := (1 : NNReal)) (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_one, sub_zero,
    mul_one]
  let c := A + 1 / 2
  have hc : 0 < c := by dsimp [c]; linarith
  let d := B / (2 * c)
  have hpoint (x : ℝ) :
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
          Real.exp (-A * x ^ 2 + B * x) =
        ((Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (B ^ 2 / (4 * c))) *
          Real.exp (-c * (x - d) ^ 2) := by
    rw [mul_assoc, mul_assoc]
    apply congrArg (fun y ↦ (Real.sqrt (2 * Real.pi))⁻¹ * y)
    rw [← Real.exp_add]
    rw [← Real.exp_add]
    congr 1
    dsimp only [d]
    field_simp [hc.ne']
    dsimp only [c]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun x : ℝ ↦ Real.exp (-c * x ^ 2)) d]
  rw [integral_gaussian c]
  simp [gaussianQuadraticIntegral, c]

lemma gaussianQuadraticIntegral_zero (A : ℝ) (hA : -(1 / 2 : ℝ) < A) :
    gaussianQuadraticIntegral A 0 = (Real.sqrt (1 + 2 * A))⁻¹ := by
  have hC : 0 < A + 1 / 2 := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 hpi).ne'
  have hsqrtC : Real.sqrt (A + 1 / 2) ≠ 0 :=
    (Real.sqrt_pos.2 hC).ne'
  have hsqrt2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  unfold gaussianQuadraticIntegral
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.exp_zero, mul_one]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_div (le_of_lt hpi)]
  have hsqrt : Real.sqrt 2 * Real.sqrt (A + 1 / 2) =
      Real.sqrt (1 + 2 * A) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [← hsqrt]
  field_simp

lemma integral_bivariate_correlated_sq_laplace_raw
    (s t rho c : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ w : ℝ × ℝ,
        Real.exp (-s * w.1 ^ 2 - t * (rho * w.1 + c * w.2) ^ 2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      let C := t * c ^ 2 + 1 / 2
      let Aout := s + t * rho ^ 2 - t ^ 2 * rho ^ 2 * c ^ 2 / C
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / C)) *
        gaussianQuadraticIntegral Aout 0 := by
  let f : ℝ × ℝ → ℝ := fun w ↦
    Real.exp (-s * w.1 ^ 2 - t * (rho * w.1 + c * w.2) ^ 2)
  have hfmeas : AEStronglyMeasurable f
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    exact (by fun_prop : Measurable f).aestronglyMeasurable
  have hfbound : ∀ᵐ w ∂((gaussianReal 0 1).prod (gaussianReal 0 1)),
      ‖f w‖ ≤ 1 := by
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hs (sq_nonneg w.1),
        mul_nonneg ht (sq_nonneg (rho * w.1 + c * w.2))])
  have hfint : Integrable f
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    Integrable.of_bound hfmeas 1 hfbound
  rw [show (∫ w : ℝ × ℝ, Real.exp
      (-s * w.1 ^ 2 - t * (rho * w.1 + c * w.2) ^ 2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = ∫ w, f w
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) by rfl]
  rw [MeasureTheory.integral_prod f hfint]
  let C := t * c ^ 2 + 1 / 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hinner (x : ℝ) :
      ∫ y, f (x, y) ∂gaussianReal 0 1 =
        Real.exp (-(s + t * rho ^ 2) * x ^ 2) *
          gaussianQuadraticIntegral (t * c ^ 2) (-2 * t * rho * c * x) := by
    have hpoint (y : ℝ) :
        f (x, y) = Real.exp (-(s + t * rho ^ 2) * x ^ 2) *
          Real.exp (-(t * c ^ 2) * y ^ 2 + (-2 * t * rho * c * x) * y) := by
      unfold f
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [hpoint, MeasureTheory.integral_const_mul]
    rw [integral_exp_neg_mul_sq_add_mul_gaussianReal]
    linarith [mul_nonneg ht (sq_nonneg c)]
  simp_rw [hinner]
  let K := (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / C)
  let Aout := s + t * rho ^ 2 - t ^ 2 * rho ^ 2 * c ^ 2 / C
  have hrewrite (x : ℝ) :
      Real.exp (-(s + t * rho ^ 2) * x ^ 2) *
          gaussianQuadraticIntegral (t * c ^ 2) (-2 * t * rho * c * x) =
        K * Real.exp (-Aout * x ^ 2) := by
    have hfactor :
        gaussianQuadraticIntegral (t * c ^ 2) (-2 * t * rho * c * x) =
          K * Real.exp ((-2 * t * rho * c * x) ^ 2 / (4 * C)) := by
      simp only [gaussianQuadraticIntegral,
        show t * c ^ 2 + 1 / 2 = C by rfl]
      dsimp only [K]
      ring
    rw [hfactor]
    calc
      Real.exp (-(s + t * rho ^ 2) * x ^ 2) *
          (K * Real.exp ((-2 * t * rho * c * x) ^ 2 / (4 * C))) =
          K * (Real.exp (-(s + t * rho ^ 2) * x ^ 2) *
            Real.exp ((-2 * t * rho * c * x) ^ 2 / (4 * C))) := by ring
      _ = K * Real.exp (-Aout * x ^ 2) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        dsimp [Aout]
        field_simp [hC.ne']
        ring
  simp_rw [hrewrite, MeasureTheory.integral_const_mul]
  have hAout : -(1 / 2 : ℝ) < Aout := by
    have hAeq : Aout = s + t * rho ^ 2 * (1 / 2) / C := by
      dsimp [Aout, C]
      have hC' : t * c ^ 2 + 1 / 2 ≠ 0 := by positivity
      field_simp [hC']
      ring
    rw [hAeq]
    have hnonneg : 0 ≤ s + t * rho ^ 2 * (1 / 2) / C :=
      add_nonneg hs (div_nonneg
        (mul_nonneg (mul_nonneg ht (sq_nonneg rho)) (by norm_num)) hC.le)
    linarith
  have hout := integral_exp_neg_mul_sq_add_mul_gaussianReal Aout 0 hAout
  simp only [zero_mul, add_zero] at hout
  rw [hout]

lemma integral_bivariate_correlated_sq_laplace
    (s t rho c : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ w : ℝ × ℝ,
        Real.exp (-s * w.1 ^ 2 - t * (rho * w.1 + c * w.2) ^ 2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (Real.sqrt ((1 + 2 * s) * (1 + 2 * t * c ^ 2) +
        2 * t * rho ^ 2))⁻¹ := by
  rw [integral_bivariate_correlated_sq_laplace_raw s t rho c hs ht]
  dsimp only
  let C := t * c ^ 2 + 1 / 2
  let Aout := s + t * rho ^ 2 - t ^ 2 * rho ^ 2 * c ^ 2 / C
  have hC : 0 < C := by dsimp [C]; positivity
  have hAeq : Aout = s + t * rho ^ 2 * (1 / 2) / C := by
    dsimp [Aout, C]
    have hC' : t * c ^ 2 + 1 / 2 ≠ 0 := by positivity
    field_simp [hC']
    ring
  have hAout0 : 0 ≤ Aout := by
    rw [hAeq]
    exact add_nonneg hs (div_nonneg
      (mul_nonneg (mul_nonneg ht (sq_nonneg rho)) (by norm_num)) hC.le)
  have hAinner : -(1 / 2 : ℝ) < t * c ^ 2 := by
    linarith [mul_nonneg ht (sq_nonneg c)]
  have hAout : -(1 / 2 : ℝ) < Aout := lt_of_lt_of_le (by norm_num) hAout0
  have hK :
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / C) =
        gaussianQuadraticIntegral (t * c ^ 2) 0 := by
    simp [gaussianQuadraticIntegral, C]
  rw [hK, gaussianQuadraticIntegral_zero _ hAinner,
    gaussianQuadraticIntegral_zero _ hAout]
  rw [← mul_inv]
  have hd1 : 0 ≤ 1 + 2 * t * c ^ 2 := by positivity
  rw [show 1 + 2 * (t * c ^ 2) = 1 + 2 * t * c ^ 2 by ring]
  rw [← Real.sqrt_mul hd1]
  have harg : (1 + 2 * t * c ^ 2) * (1 + 2 * Aout) =
      (1 + 2 * s) * (1 + 2 * t * c ^ 2) + 2 * t * rho ^ 2 := by
    dsimp only [Aout]
    field_simp [hC.ne']
    dsimp only [C]
    ring
  rw [harg]

lemma integral_bivariate_correlated_sq_laplace_sqrt
    (s t rho : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hrho : |rho| ≤ 1) :
    ∫ w : ℝ × ℝ,
        Real.exp (-s * w.1 ^ 2 -
          t * (rho * w.1 + Real.sqrt (1 - rho ^ 2) * w.2) ^ 2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * rho ^ 2 * s * t))⁻¹ := by
  rw [integral_bivariate_correlated_sq_laplace s t rho
    (Real.sqrt (1 - rho ^ 2)) hs ht]
  have hrho2 : rho ^ 2 ≤ 1 := by
    rw [abs_le] at hrho
    nlinarith [sq_nonneg (rho - 1), sq_nonneg (rho + 1)]
  rw [Real.sq_sqrt (sub_nonneg.mpr hrho2)]
  congr 2
  ring

def gaussianPairProductMeasure (m : ℕ) : Measure (Fin m → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin m ↦ (gaussianReal 0 1).prod (gaussianReal 0 1))

def pairNormSqFirst {m : ℕ} (w : Fin m → ℝ × ℝ) : ℝ :=
  ∑ k, (w k).1 ^ 2

def pairNormSqCorrelated {m : ℕ} (rho : ℝ)
    (w : Fin m → ℝ × ℝ) : ℝ :=
  ∑ k, (rho * (w k).1 + Real.sqrt (1 - rho ^ 2) * (w k).2) ^ 2

lemma integral_pairNormSq_laplace {m : ℕ} (s t rho : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hrho : |rho| ≤ 1) :
    ∫ w, Real.exp (-s * pairNormSqFirst w -
        t * pairNormSqCorrelated rho w) ∂gaussianPairProductMeasure m =
      ((Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * rho ^ 2 * s * t))⁻¹) ^ m := by
  have hpoint (w : Fin m → ℝ × ℝ) :
      Real.exp (-s * pairNormSqFirst w - t * pairNormSqCorrelated rho w) =
        ∏ k, Real.exp (-s * (w k).1 ^ 2 -
          t * (rho * (w k).1 + Real.sqrt (1 - rho ^ 2) * (w k).2) ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    unfold pairNormSqFirst pairNormSqCorrelated
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  unfold gaussianPairProductMeasure
  calc
    (∫ w : Fin m → ℝ × ℝ,
        ∏ k, Real.exp (-s * (w k).1 ^ 2 -
          t * (rho * (w k).1 + Real.sqrt (1 - rho ^ 2) * (w k).2) ^ 2)
        ∂Measure.pi (fun _ : Fin m ↦
          (gaussianReal 0 1).prod (gaussianReal 0 1))) =
      (∫ w : ℝ × ℝ,
        Real.exp (-s * w.1 ^ 2 -
          t * (rho * w.1 + Real.sqrt (1 - rho ^ 2) * w.2) ^ 2)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ^ m := by
      simpa only [Fintype.card_fin] using
        (MeasureTheory.integral_fintype_prod_eq_pow (ι := Fin m)
        (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
        (f := fun w : ℝ × ℝ ↦
          Real.exp (-s * w.1 ^ 2 -
            t * (rho * w.1 + Real.sqrt (1 - rho ^ 2) * w.2) ^ 2)))
    _ = ((Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * rho ^ 2 * s * t))⁻¹) ^ m := by
      rw [integral_bivariate_correlated_sq_laplace_sqrt s t rho hs ht hrho]
