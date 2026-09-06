import LogdetLean.GaussianAntiConcentration
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Sharp shifted intervals for real Gaussian linear forms

This is the beta-one counterpart of `GaussianDisk.lean`.  A linear form of
iid standard real Gaussians is represented exactly as a standard Gaussian
scaled by the square root of the coefficient energy.  The peak-density
bound then gives the uniform shifted interval estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Real InnerProductSpace

namespace LogdetLean.GramHafnian

noncomputable section

/-- Real Euclidean coordinate space used by the beta-one Fourier argument. -/
abbrev RealGaussianEuclideanSpace (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Squared Euclidean norm of a real coefficient vector. -/
def realCoefficientEnergy {k : ℕ} (y : Fin k → ℝ) : ℝ :=
  ∑ i, y i ^ 2

theorem realCoefficientEnergy_nonneg {k : ℕ} (y : Fin k → ℝ) :
    0 ≤ realCoefficientEnergy y := by
  unfold realCoefficientEnergy
  positivity

/-- The real transpose linear form. -/
def realTransposeLinearForm {k : ℕ} (y : Fin k → ℝ)
    (x : RealGaussianEuclideanSpace k) : ℝ :=
  ∑ i, x i * y i

@[fun_prop]
theorem measurable_realTransposeLinearForm {k : ℕ} (y : Fin k → ℝ) :
    Measurable (realTransposeLinearForm y) := by
  unfold realTransposeLinearForm
  fun_prop

/-- Fourier vector representing a real linear form. -/
def realTransposeCharVector {k : ℕ} (y : Fin k → ℝ) (t : ℝ) :
    RealGaussianEuclideanSpace k :=
  WithLp.toLp 2 (fun i ↦ y i * t)

theorem real_inner_realTransposeLinearForm {k : ℕ}
    (y : Fin k → ℝ) (x : RealGaussianEuclideanSpace k) (t : ℝ) :
    inner ℝ (realTransposeLinearForm y x) t =
      inner ℝ x (realTransposeCharVector y t) := by
  simp only [realTransposeLinearForm, realTransposeCharVector,
    PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem norm_sq_realTransposeCharVector {k : ℕ}
    (y : Fin k → ℝ) (t : ℝ) :
    ‖realTransposeCharVector y t‖ ^ 2 = realCoefficientEnergy y * t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [realTransposeCharVector, PiLp.toLp_apply, mul_pow]
  unfold realCoefficientEnergy
  rw [← Finset.sum_mul]

/-- Exact characteristic function of a real linear form of a standard
multivariate Gaussian. -/
theorem charFun_map_realTransposeLinearForm_stdGaussian {k : ℕ}
    (y : Fin k → ℝ) (t : ℝ) :
    charFun ((stdGaussian (RealGaussianEuclideanSpace k)).map
        (realTransposeLinearForm y)) t =
      Complex.exp
        (-((realCoefficientEnergy y * t ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFun_apply, integral_map
    (measurable_realTransposeLinearForm y).aemeasurable (by fun_prop)]
  have hintegrand :
      (fun x : RealGaussianEuclideanSpace k ↦
          Complex.exp
            (↑(inner ℝ (realTransposeLinearForm y x) t) * Complex.I)) =
        (fun x ↦ Complex.exp
          (↑(inner ℝ x (realTransposeCharVector y t)) * Complex.I)) := by
    funext x
    rw [real_inner_realTransposeLinearForm]
  rw [hintegrand, ← charFun_apply, charFun_stdGaussian]
  congr 1
  norm_cast
  rw [norm_sq_realTransposeCharVector]

/-- Exact law of the linear form: a standard scalar Gaussian scaled by the
square root of the coefficient energy.  Energy zero is included. -/
theorem map_realTransposeLinearForm_stdGaussian_eq_scaled_realGaussian
    {k : ℕ} (y : Fin k → ℝ) :
    (stdGaussian (RealGaussianEuclideanSpace k)).map
        (realTransposeLinearForm y) =
      (gaussianReal 0 1).map
        (fun x : ℝ ↦ Real.sqrt (realCoefficientEnergy y) • x) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_realTransposeLinearForm_stdGaussian,
    charFun_map_smul, charFun_gaussianReal]
  simp only [NNReal.coe_one, Complex.ofReal_zero, mul_zero, zero_mul,
    zero_sub, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  congr 1
  norm_cast
  rw [mul_pow, Real.sq_sqrt (realCoefficientEnergy_nonneg y)]
  ring

/-- Ordinary function-space realization of the iid real linear form. -/
def iidRealTransposeLinearForm {k : ℕ} (y : Fin k → ℝ)
    (x : Fin k → ℝ) : ℝ :=
  ∑ i, x i * y i

@[fun_prop]
theorem measurable_iidRealTransposeLinearForm {k : ℕ} (y : Fin k → ℝ) :
    Measurable (iidRealTransposeLinearForm y) := by
  unfold iidRealTransposeLinearForm
  fun_prop

/-- Function-space form of the exact iid real Gaussian linear-functional
law. -/
theorem map_iidRealTransposeLinearForm_eq_scaled_realGaussian
    {k : ℕ} (y : Fin k → ℝ) :
    (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1).map
        (iidRealTransposeLinearForm y) =
      (gaussianReal 0 1).map
        (fun x : ℝ ↦ Real.sqrt (realCoefficientEnergy y) • x) := by
  have hcomp : iidRealTransposeLinearForm y =
      realTransposeLinearForm y ∘ WithLp.toLp 2 := by
    rfl
  rw [hcomp, ← Measure.map_map
    (measurable_realTransposeLinearForm y) (by fun_prop),
    map_pi_eq_stdGaussian]
  exact map_realTransposeLinearForm_stdGaussian_eq_scaled_realGaussian y

/-- A positive rescaling of the standard real Gaussian has mass at most
`2 rho / (s sqrt(2 pi))` in every interval of radius `rho`. -/
theorem map_pos_mul_standardGaussian_Icc_le
    (s : ℝ) (hs : 0 < s) (z ρ : ℝ) (hρ : 0 ≤ ρ) :
    ((gaussianReal 0 1).map (fun x : ℝ ↦ s * x)).real
        (Icc (z - ρ) (z + ρ)) ≤
      (2 * ρ) / (s * Real.sqrt (2 * Real.pi)) := by
  have hpre :
      (fun x : ℝ ↦ s * x) ⁻¹' Icc (z - ρ) (z + ρ) =
        Icc ((z - ρ) / s) ((z + ρ) / s) := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor
    · intro hx
      constructor
      · apply (div_le_iff₀ hs).2
        simpa [mul_comm] using hx.1
      · apply (le_div_iff₀ hs).2
        simpa [mul_comm] using hx.2
    · intro hx
      constructor
      · simpa [mul_comm] using (div_le_iff₀ hs).1 hx.1
      · simpa [mul_comm] using (le_div_iff₀ hs).1 hx.2
  rw [map_measureReal_apply (by fun_prop) measurableSet_Icc, hpre]
  calc
    (gaussianReal 0 1).real (Icc ((z - ρ) / s) ((z + ρ) / s)) ≤
        (2 * (ρ / s)) / Real.sqrt (2 * Real.pi) := by
      have h := LogdetLean.standardGaussian_measureReal_Icc_le
        (z / s) (ρ / s) (div_nonneg hρ hs.le)
      convert h using 1 <;> field_simp [hs.ne'] <;> ring
    _ = (2 * ρ) / (s * Real.sqrt (2 * Real.pi)) := by
      field_simp [hs.ne', Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi)]

/-- Sharp shifted interval estimate for a nondegenerate iid real Gaussian
linear form. -/
theorem pi_realGaussian_transpose_abs_sub_le
    {k : ℕ} (y : Fin k → ℝ)
    (henergy : 0 < realCoefficientEnergy y)
    (z ρ : ℝ) (hρ : 0 ≤ ρ) :
    (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1).real
        {x : Fin k → ℝ |
          |iidRealTransposeLinearForm y x - z| ≤ ρ} ≤
      (2 * ρ) /
        (Real.sqrt (realCoefficientEnergy y) * Real.sqrt (2 * Real.pi)) := by
  have hset : {w : ℝ | |w - z| ≤ ρ} = Icc (z - ρ) (z + ρ) := by
    ext w
    change |w - z| ≤ ρ ↔ z - ρ ≤ w ∧ w ≤ z + ρ
    rw [abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  change (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1).real
      ((iidRealTransposeLinearForm y) ⁻¹' {w : ℝ | |w - z| ≤ ρ}) ≤ _
  rw [← map_measureReal_apply (measurable_iidRealTransposeLinearForm y)
      (by rw [hset]; exact measurableSet_Icc),
    map_iidRealTransposeLinearForm_eq_scaled_realGaussian, hset]
  exact map_pos_mul_standardGaussian_Icc_le
    (Real.sqrt (realCoefficientEnergy y)) (Real.sqrt_pos.2 henergy) z ρ hρ

end

end LogdetLean.GramHafnian
