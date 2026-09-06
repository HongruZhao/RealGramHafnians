import LogdetLean.GramHafnian.ShiftedAnticoncentration.AuxiliaryGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
/-!
# Bilinear Gaussian Fourier kernel

This file formalizes the analytic interpolation kernel used when two
Fourier coordinates are exposed.  We begin with the one-dimensional
completed-square identity, including its normalization; finite-dimensional
versions are obtained by product integration.
-/

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped BigOperators Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- A normalized one-dimensional Gaussian completed square. -/
theorem integral_cexp_tilted_standardGaussian
    (lambda : ℝ) (hlambda : 0 < lambda) (d : ℂ) :
    ∫ x : ℝ,
        Complex.exp
          (-(((lambda - 1) / 2 : ℝ) : ℂ) * (x : ℂ) ^ 2 + d * x)
        ∂gaussianReal 0 1 =
      ((Real.sqrt lambda)⁻¹ : ℂ) *
        Complex.exp (d ^ 2 / (2 * lambda)) := by
  rw [integral_gaussianReal_eq_integral_smul
    (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [Complex.real_smul]
  unfold gaussianPDFReal
  push_cast
  simp only [mul_one, sub_zero]
  simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
  have hquad : (-(lambda : ℂ) / 2).re < 0 := by
    norm_num
    linarith
  have hintegrand : (fun x : ℝ =>
      Complex.exp (-((x : ℂ) ^ 2) / 2 +
        (-(((lambda : ℂ) - 1) / 2) * (x : ℂ) ^ 2 + d * x))) =
      (fun x : ℝ => Complex.exp
        (-(lambda : ℂ) / 2 * (x : ℂ) ^ 2 + d * x + 0)) := by
      funext x
      congr 1
      ring
  rw [hintegrand]
  rw [integral_cexp_quadratic (b := -(lambda : ℂ) / 2) hquad d 0]
  simp only [zero_sub]
  have hsqrt_lambda : Real.sqrt lambda ≠ 0 :=
    (Real.sqrt_pos.2 hlambda).ne'
  have hsqrt_two_pi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hbase : (Real.pi : ℂ) / -(-(lambda : ℂ) / 2) =
      ((2 * Real.pi / lambda : ℝ) : ℂ) := by
    push_cast
    field_simp [ne_of_gt hlambda]
  rw [hbase]
  have hcpow : ((2 * Real.pi / lambda : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (Real.sqrt (2 * Real.pi / lambda) : ℝ) := by
    calc
      ((2 * Real.pi / lambda : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
          (((2 * Real.pi / lambda) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        symm
        simpa using Complex.ofReal_cpow
          (by positivity : 0 ≤ 2 * Real.pi / lambda) (1 / 2 : ℝ)
      _ = (Real.sqrt (2 * Real.pi / lambda) : ℝ) := by
        rw [Real.sqrt_eq_rpow]
  rw [hcpow]
  have hreal : (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.sqrt (2 * Real.pi / lambda) = (Real.sqrt lambda)⁻¹ := by
    rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
    field_simp [hsqrt_lambda, hsqrt_two_pi]
  have hrealC : (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
      (Real.sqrt (2 * Real.pi / lambda) : ℝ) =
        (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast hreal
  push_cast at hrealC
  rw [← mul_assoc, hrealC]
  congr 1
  field_simp
  congr 1
  ring

/-- Coordinatewise completed square for a finite product of independent
standard real Gaussians.  This is the diagonal positive-definite Gaussian
integral with all normalizing factors exposed. -/
theorem integral_cexp_diagonal_tilted_standardGaussian
    {n : ℕ} (lambda : Fin n → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (d : Fin n → ℂ) :
    ∫ x : Fin n → ℝ,
        Complex.exp (∑ i,
          (-((((lambda i - 1) / 2 : ℝ) : ℂ)) * (x i : ℂ) ^ 2 +
            d i * x i))
        ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) =
      (∏ i, ((Real.sqrt (lambda i))⁻¹ : ℂ)) *
        Complex.exp (∑ i, d i ^ 2 / (2 * lambda i)) := by
  have hintegrand : (fun x : Fin n → ℝ =>
      Complex.exp (∑ i,
        (-((((lambda i - 1) / 2 : ℝ) : ℂ)) * (x i : ℂ) ^ 2 +
          d i * x i))) =
      (fun x : Fin n → ℝ => ∏ i,
        Complex.exp
          (-((((lambda i - 1) / 2 : ℝ) : ℂ)) * (x i : ℂ) ^ 2 +
            d i * x i)) := by
    funext x
    rw [Complex.exp_sum]
  rw [hintegrand]
  rw [integral_fintype_prod_eq_prod
    (μ := fun _ : Fin n => gaussianReal 0 1)
    (fun i (x : ℝ) => Complex.exp
      (-((((lambda i - 1) / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2 +
        d i * x))]
  simp_rw [integral_cexp_tilted_standardGaussian _ (hlambda _) _]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]

/-! ## The bilinear kernel and its first Gaussian integration -/

/-- The exact `F_{T,L}(a,b)` integral from the paper, formulated for
continuous linear maps on a finite-dimensional real Hilbert space. -/
def bilinearGaussianIntegral
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) : ℂ :=
  ∫ p : E × E,
    Complex.exp (((inner ℝ p.1 (T p.2) +
      inner ℝ p.1 (L b) + inner ℝ p.2 (L a) : ℝ) : ℂ) * Complex.I)
    ∂((stdGaussian E).prod (stdGaussian E))

private theorem integrable_bilinearGaussianIntegral_kernel
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) :
    Integrable (fun p : E × E =>
      Complex.exp (((inner ℝ p.1 (T p.2) +
        inner ℝ p.1 (L b) + inner ℝ p.2 (L a) : ℝ) : ℂ) * Complex.I))
      ((stdGaussian E).prod (stdGaussian E)) := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with p
  rw [Complex.norm_exp]
  simp

/-- Conditioning first on the second Gaussian gives the exact heat-kernel
factor.  This is the first line of the paper's completed-square calculation. -/
theorem bilinearGaussianIntegral_eq_integral_after_first
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) :
    bilinearGaussianIntegral T L a b =
      ∫ h : E,
        Complex.exp (-((‖T h + L b‖ : ℂ) ^ 2) / 2) *
          Complex.exp (((inner ℝ h (L a) : ℝ) : ℂ) * Complex.I)
        ∂(stdGaussian E) := by
  unfold bilinearGaussianIntegral
  have hint := integrable_bilinearGaussianIntegral_kernel T L a b
  rw [integral_prod _ hint, integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards [] with h
  have hphase : (fun g : E =>
      Complex.exp (((inner ℝ g (T h) + inner ℝ g (L b) +
        inner ℝ h (L a) : ℝ) : ℂ) * Complex.I)) =
      (fun g : E =>
        Complex.exp (((inner ℝ g (T h + L b) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((inner ℝ h (L a) : ℝ) : ℂ) * Complex.I)) := by
    funext g
    rw [← Complex.exp_add]
    congr 1
    push_cast
    rw [inner_add_right]
    rw [Complex.ofReal_add]
    ring
  rw [hphase, integral_mul_const]
  change charFun (stdGaussian E) (T h + L b) *
      Complex.exp (((inner ℝ h (L a) : ℝ) : ℂ) * Complex.I) = _
  rw [charFun_stdGaussian]

/-! ## The completed-square normal form

The matrix calculation in the paper produces a positive determinant factor,
two nonnegative quadratic forms, and one real bilinear phase.  The following
normal form isolates exactly the part of that calculation used by coordinate
compression.  Keeping this as a separate definition makes the interpolation
argument independent of any choice of eigenbasis used to evaluate the
Gaussian integral.
-/

/-- Completed-square normal form of the two-coordinate Gaussian kernel.

`prefactor` is `det (I + TᵀT)⁻¹²`, `qLeft` and `qRight` are the two
positive quadratic endpoint energies, and `phase` is the real mixed phase.
-/
def completedSquareKernel
    (prefactor qLeft qRight phase s t : ℝ) : ℂ :=
  (prefactor : ℂ) *
    Complex.exp (-((s ^ 2 * qLeft + t ^ 2 * qRight : ℝ) : ℂ) / 2) *
    Complex.exp (-((s * t * phase : ℝ) : ℂ) * Complex.I)

/-- The completed-square formula has precisely the advertised modulus: its
mixed term is a pure phase and disappears. -/
theorem norm_completedSquareKernel
    {prefactor qLeft qRight phase s t : ℝ} (hprefactor : 0 ≤ prefactor) :
    ‖completedSquareKernel prefactor qLeft qRight phase s t‖ =
      prefactor * Real.exp (-(s ^ 2 * qLeft + t ^ 2 * qRight) / 2) := by
  unfold completedSquareKernel
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hprefactor, Complex.norm_exp, Complex.norm_exp]
  have hmain :
      (-((s ^ 2 * qLeft + t ^ 2 * qRight : ℝ) : ℂ) / 2).re =
        -(s ^ 2 * qLeft + t ^ 2 * qRight) / 2 := by
    norm_num [← Complex.ofReal_pow]
  have hphase : (-((s * t * phase : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp
  rw [hmain, hphase, Real.exp_zero, mul_one]

/-- The first positive endpoint of the completed-square kernel. -/
theorem completedSquareKernel_left_endpoint
    (prefactor qLeft qRight phase : ℝ) :
    completedSquareKernel prefactor qLeft qRight phase 1 0 =
      (prefactor * Real.exp (-qLeft / 2) : ℝ) := by
  simp [completedSquareKernel]

/-- The second positive endpoint of the completed-square kernel. -/
theorem completedSquareKernel_right_endpoint
    (prefactor qLeft qRight phase : ℝ) :
    completedSquareKernel prefactor qLeft qRight phase 0 1 =
      (prefactor * Real.exp (-qRight / 2) : ℝ) := by
  simp [completedSquareKernel]

/-- Both endpoint values are nonnegative when the determinant prefactor is. -/
theorem completedSquareKernel_endpoints_nonneg
    {prefactor qLeft qRight phase : ℝ} (hprefactor : 0 ≤ prefactor) :
    0 ≤ (completedSquareKernel prefactor qLeft qRight phase 1 0).re ∧
      0 ≤ (completedSquareKernel prefactor qLeft qRight phase 0 1).re := by
  rw [completedSquareKernel_left_endpoint,
    completedSquareKernel_right_endpoint]
  constructor <;> simp only [Complex.ofReal_re] <;> positivity

/-- Exact geometric interpolation on the quarter circle.  This is the
pointwise identity to which Hölder is applied after averaging over all
unexposed Gaussian coordinates. -/
theorem norm_completedSquareKernel_sqrt_interpolation
    {prefactor qLeft qRight phase theta : ℝ}
    (hprefactor : 0 < prefactor) (htheta : 0 ≤ theta)
    (htheta_one : theta ≤ 1) :
    ‖completedSquareKernel prefactor qLeft qRight phase
        (Real.sqrt theta) (Real.sqrt (1 - theta))‖ =
      (prefactor * Real.exp (-qLeft / 2)) ^ theta *
        (prefactor * Real.exp (-qRight / 2)) ^ (1 - theta) := by
  rw [norm_completedSquareKernel hprefactor.le]
  have hsqrt_theta : (Real.sqrt theta) ^ 2 = theta :=
    (Real.sq_sqrt htheta)
  have hsqrt_one : (Real.sqrt (1 - theta)) ^ 2 = 1 - theta :=
    Real.sq_sqrt (sub_nonneg.mpr htheta_one)
  rw [hsqrt_theta, hsqrt_one]
  rw [show -(theta * qLeft + (1 - theta) * qRight) / 2 =
      theta * (-qLeft / 2) + (1 - theta) * (-qRight / 2) by ring]
  have hleft : 0 < prefactor * Real.exp (-qLeft / 2) :=
    mul_pos hprefactor (Real.exp_pos _)
  have hright : 0 < prefactor * Real.exp (-qRight / 2) :=
    mul_pos hprefactor (Real.exp_pos _)
  rw [Real.rpow_def_of_pos hleft, Real.rpow_def_of_pos hright]
  rw [Real.log_mul hprefactor.ne' (Real.exp_ne_zero _),
    Real.log_mul hprefactor.ne' (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp, ← Real.exp_add]
  have hexp_log : Real.exp (Real.log prefactor) = prefactor :=
    Real.exp_log hprefactor
  calc
    prefactor * Real.exp
        (theta * (-qLeft / 2) + (1 - theta) * (-qRight / 2)) =
        Real.exp (Real.log prefactor) * Real.exp
          (theta * (-qLeft / 2) + (1 - theta) * (-qRight / 2)) := by
          rw [hexp_log]
    _ = Real.exp (Real.log prefactor +
          (theta * (-qLeft / 2) + (1 - theta) * (-qRight / 2))) := by
          exact (Real.exp_add _ _).symm
    _ = Real.exp
          ((Real.log prefactor + -qLeft / 2) * theta +
            (Real.log prefactor + -qRight / 2) * (1 - theta)) := by
          congr 1
          ring

/-! ## Hölder averaging -/

/-- The exact ENNReal Hölder step used to average the pointwise geometric
interpolation identity over the remainder measure. -/
theorem lintegral_geometric_interpolation_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ENNReal) (theta : ℝ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1) :
    ∫⁻ ω, f ω ^ theta * g ω ^ (1 - theta) ∂μ ≤
      (∫⁻ ω, f ω ∂μ) ^ theta * (∫⁻ ω, g ω ∂μ) ^ (1 - theta) := by
  apply ENNReal.lintegral_mul_norm_pow_le hf hg htheta
    (sub_nonneg.mpr htheta_one)
  ring

/-! ## Direct evaluation in one singular coordinate -/

/-- The normalized two-real-Gaussian bilinear integral in one singular
coordinate.  This is the scalar building block for the singular-value
decomposition of `F_{T,L}`. -/
def scalarBilinearGaussianIntegral (tau u v : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ,
    Complex.exp ((((p.1 * tau * p.2 + p.1 * v + p.2 * u : ℝ) : ℂ) *
      Complex.I))
    ∂((gaussianReal 0 1).prod (gaussianReal 0 1))

private theorem integrable_scalarBilinearGaussianIntegral_kernel
    (tau u v : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      Complex.exp ((((p.1 * tau * p.2 + p.1 * v + p.2 * u : ℝ) : ℂ) *
        Complex.I)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with p
  rw [Complex.norm_exp]
  simp

/-- First condition the scalar bilinear integral on its second Gaussian. -/
theorem scalarBilinearGaussianIntegral_eq_after_first
    (tau u v : ℝ) :
    scalarBilinearGaussianIntegral tau u v =
      ∫ h : ℝ,
        Complex.exp (-(((tau * h + v : ℝ) : ℂ) ^ 2) / 2) *
          Complex.exp (((h * u : ℝ) : ℂ) * Complex.I)
        ∂(gaussianReal 0 1) := by
  unfold scalarBilinearGaussianIntegral
  have hint := integrable_scalarBilinearGaussianIntegral_kernel tau u v
  rw [integral_prod _ hint, integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards [] with h
  have hphase : (fun g : ℝ =>
      Complex.exp ((((g * tau * h + g * v + h * u : ℝ) : ℂ) *
        Complex.I))) =
      (fun g : ℝ =>
        Complex.exp (((g * (tau * h + v) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((h * u : ℝ) : ℂ) * Complex.I)) := by
    funext g
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hphase, integral_mul_const]
  have hchar :
      (∫ a : ℝ,
        Complex.exp (((a * (tau * h + v) : ℝ) : ℂ) * Complex.I)
        ∂(gaussianReal 0 1)) =
        charFun (gaussianReal 0 1) (tau * h + v) := by
    rw [charFun_apply_real]
    congr with a
    congr 1
    push_cast
    ring
  rw [hchar]
  rw [charFun_gaussianReal]
  norm_num
  congr 1
  ring

/-- Exact one-coordinate completed-square formula, including the determinant
factor, both positive quadratic endpoint terms, and the mixed pure phase. -/
theorem scalarBilinearGaussianIntegral_eq_completedSquareKernel
    (tau u v : ℝ) :
    scalarBilinearGaussianIntegral tau u v =
      completedSquareKernel
        (Real.sqrt (1 + tau ^ 2))⁻¹
        (u ^ 2 / (1 + tau ^ 2))
        (v ^ 2 / (1 + tau ^ 2))
        (tau * u * v / (1 + tau ^ 2)) 1 1 := by
  rw [scalarBilinearGaussianIntegral_eq_after_first]
  let lambda : ℝ := 1 + tau ^ 2
  let d : ℂ := -(tau * v : ℝ) + (u : ℂ) * Complex.I
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hintegrand : (fun h : ℝ =>
      Complex.exp (-(((tau * h + v : ℝ) : ℂ) ^ 2) / 2) *
        Complex.exp (((h * u : ℝ) : ℂ) * Complex.I)) =
      (fun h : ℝ =>
        Complex.exp (-((v : ℂ) ^ 2) / 2) *
          Complex.exp
            (-((((lambda - 1) / 2 : ℝ) : ℂ)) * (h : ℂ) ^ 2 +
              d * h)) := by
    funext h
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp [lambda, d]
    push_cast
    ring
  rw [hintegrand, integral_const_mul,
    integral_cexp_tilted_standardGaussian lambda hlambda d]
  unfold completedSquareKernel
  dsimp [lambda, d]
  have hdenom : (1 + tau ^ 2 : ℝ) ≠ 0 := by positivity
  have hdenomC : (((1 + tau ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hdenom
  have hdenomC' : (1 + (tau : ℂ) ^ 2) ≠ 0 := by
    simpa [← Complex.ofReal_pow] using hdenomC
  simp only [one_pow, one_mul]
  rw [Complex.ofReal_inv]
  calc
    Complex.exp (-((v : ℂ) ^ 2) / 2) *
        (((Real.sqrt (1 + tau ^ 2))⁻¹ : ℂ) *
          Complex.exp
            ((-(tau * v : ℝ) + (u : ℂ) * Complex.I) ^ 2 /
              (2 * ((1 + tau ^ 2 : ℝ) : ℂ)))) =
      ((Real.sqrt (1 + tau ^ 2))⁻¹ : ℂ) *
        (Complex.exp (-((v : ℂ) ^ 2) / 2) *
          Complex.exp
            ((-(tau * v : ℝ) + (u : ℂ) * Complex.I) ^ 2 /
              (2 * ((1 + tau ^ 2 : ℝ) : ℂ)))) := by ring
    _ = ((Real.sqrt (1 + tau ^ 2))⁻¹ : ℂ) *
        (Complex.exp
          (-(((u ^ 2 / (1 + tau ^ 2) +
            v ^ 2 / (1 + tau ^ 2) : ℝ) : ℂ)) / 2) *
          Complex.exp
            (-((tau * u * v / (1 + tau ^ 2) : ℝ) : ℂ) * Complex.I)) := by
      congr 1
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp [hdenomC']
      ring_nf
      simp [Complex.I_sq]
      ring
    _ = ((Real.sqrt (1 + tau ^ 2))⁻¹ : ℂ) *
          Complex.exp
            (-(((u ^ 2 / (1 + tau ^ 2) +
              v ^ 2 / (1 + tau ^ 2) : ℝ) : ℂ)) / 2) *
          Complex.exp
            (-((tau * u * v / (1 + tau ^ 2) : ℝ) : ℂ) * Complex.I) := by
      exact (mul_assoc _ _ _).symm

/-! ## Exact finite diagonal kernel -/

/-- The finite product realization of the bilinear kernel after choosing
singular coordinates for `T`.  Each coordinate contains an independent pair
of standard real Gaussians. -/
def diagonalBilinearGaussianIntegral
    {n : ℕ} (tau u v : Fin n → ℝ) : ℂ :=
  ∫ p : Fin n → ℝ × ℝ,
    Complex.exp (∑ i,
      (((p i).1 * tau i * (p i).2 + (p i).1 * v i + (p i).2 * u i : ℝ) : ℂ) *
        Complex.I)
    ∂(Measure.pi fun _ : Fin n ↦
      (gaussianReal 0 1).prod (gaussianReal 0 1))

/-- Product decomposition of the finite diagonal bilinear kernel. -/
theorem diagonalBilinearGaussianIntegral_eq_prod
    {n : ℕ} (tau u v : Fin n → ℝ) :
    diagonalBilinearGaussianIntegral tau u v =
      ∏ i, scalarBilinearGaussianIntegral (tau i) (u i) (v i) := by
  unfold diagonalBilinearGaussianIntegral scalarBilinearGaussianIntegral
  have hintegrand : (fun p : Fin n → ℝ × ℝ =>
      Complex.exp (∑ i,
        ((((p i).1 * tau i * (p i).2 + (p i).1 * v i +
          (p i).2 * u i : ℝ) : ℂ) * Complex.I))) =
      (fun p : Fin n → ℝ × ℝ => ∏ i,
        Complex.exp
          (((((p i).1 * tau i * (p i).2 + (p i).1 * v i +
            (p i).2 * u i : ℝ) : ℂ) * Complex.I))) := by
    funext p
    rw [Complex.exp_sum]
  rw [hintegrand]
  exact integral_fintype_prod_eq_prod
    (fun i (p : ℝ × ℝ) =>
      Complex.exp
        ((((p.1 * tau i * p.2 + p.1 * v i + p.2 * u i : ℝ) : ℂ) *
          Complex.I)))

/-- Exact completed-square formula in singular coordinates.  The product of
the scalar determinant factors is `det (I + TᵀT)⁻¹²`; the two sums are
the endpoint quadratic forms, and the final sum is the mixed phase. -/
theorem diagonalBilinearGaussianIntegral_eq_completedSquareKernel
    {n : ℕ} (tau u v : Fin n → ℝ) :
    diagonalBilinearGaussianIntegral tau u v =
      completedSquareKernel
        (∏ i, (Real.sqrt (1 + (tau i) ^ 2))⁻¹)
        (∑ i, (u i) ^ 2 / (1 + (tau i) ^ 2))
        (∑ i, (v i) ^ 2 / (1 + (tau i) ^ 2))
        (∑ i, tau i * u i * v i / (1 + (tau i) ^ 2)) 1 1 := by
  rw [diagonalBilinearGaussianIntegral_eq_prod]
  simp_rw [scalarBilinearGaussianIntegral_eq_completedSquareKernel]
  unfold completedSquareKernel
  simp only [one_pow, one_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp_rw [← Complex.exp_sum]
  congr 1
  · have henergyReal :
        (∑ x, -(u x ^ 2 / (1 + tau x ^ 2) +
          v x ^ 2 / (1 + tau x ^ 2)) / 2) =
          -((∑ x, u x ^ 2 / (1 + tau x ^ 2)) +
            ∑ x, v x ^ 2 / (1 + tau x ^ 2)) / 2 := by
      let A : Fin n → ℝ := fun x =>
        u x ^ 2 / (1 + tau x ^ 2)
      let B : Fin n → ℝ := fun x =>
        v x ^ 2 / (1 + tau x ^ 2)
      calc
        (∑ x, -(A x + B x) / 2) =
            ∑ x, ((-1 / 2 : ℝ) * (A x + B x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = (-1 / 2 : ℝ) * ∑ x, (A x + B x) := by
          rw [Finset.mul_sum]
        _ = (-1 / 2 : ℝ) * ((∑ x, A x) + ∑ x, B x) := by
          rw [Finset.sum_add_distrib]
        _ = -((∑ x, u x ^ 2 / (1 + tau x ^ 2)) +
            ∑ x, v x ^ 2 / (1 + tau x ^ 2)) / 2 := by
          dsimp [A, B]
          ring
    have henergy :
        (∑ x, -(((u x ^ 2 / (1 + tau x ^ 2) +
          v x ^ 2 / (1 + tau x ^ 2) : ℝ) : ℂ)) / 2) =
          -((((∑ x, u x ^ 2 / (1 + tau x ^ 2)) +
            ∑ x, v x ^ 2 / (1 + tau x ^ 2) : ℝ) : ℂ)) / 2 := by
      exact_mod_cast henergyReal
    rw [henergy]
    push_cast
    rfl
  · congr 1
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_neg_distrib]
    push_cast
    rfl

end

end LogdetLean.GramHafnian
