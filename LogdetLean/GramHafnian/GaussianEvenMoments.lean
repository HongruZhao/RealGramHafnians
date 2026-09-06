import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic
/-!
# Exact even moments of a standard real Gaussian

This module supplies the scalar Wick input needed by the Gram--hafnian
development.  It proves the even moments directly from the Gamma integral;
no moment formula is assumed as a project axiom.
-/

namespace LogdetLean.GramHafnian

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped Nat

/-- Every polynomial monomial is integrable under the standard real Gaussian.
This is the reusable domination input for the complex-coordinate calculation. -/
theorem integrable_pow_gaussianReal (r : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ r) (gaussianReal 0 1) := by
  have habs : Integrable (fun x : ℝ ↦ ‖(id x)‖ ^ r)
      (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (r : ENNReal)
      (by exact ENNReal.coe_ne_top)).integrable_norm_pow'
  apply habs.mono
  · fun_prop
  · exact Filter.Eventually.of_forall fun x ↦ by
      simp only [id_eq, norm_pow]
      rw [Real.norm_of_nonneg (norm_nonneg x)]

/-- The unnormalized even Gaussian integral on the positive half-line. -/
theorem integral_Ioi_pow_two_mul_exp_neg_sq_half (n : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (2 * n) * Real.exp (-(x ^ 2 / 2))) =
      (1 / 2 : ℝ) ^ (-(((2 * n : ℕ) : ℝ) + 1) / 2) *
        (1 / 2) * Real.Gamma ((((2 * n : ℕ) : ℝ) + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (((2 * n : ℕ) : ℝ))) (b := (1 / 2 : ℝ))
    (by norm_num)
    (by
      have hnonneg : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
    (by norm_num)
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [Real.rpow_natCast, Real.rpow_two]
  congr 2 <;> ring

/-- The unnormalized standard-Gaussian even moment over the whole line. -/
theorem integral_pow_two_mul_exp_neg_sq_half (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) * Real.exp (-(x ^ 2 / 2))) =
      2 * ((1 / 2 : ℝ) ^ (-(((2 * n : ℕ) : ℝ) + 1) / 2) *
        (1 / 2) * Real.Gamma ((((2 * n : ℕ) : ℝ) + 1) / 2)) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (2 * n) * Real.exp (-(x ^ 2 / 2))
  have heven : (fun x : ℝ ↦ f |x|) = f := by
    funext x
    change |x| ^ (2 * n) * Real.exp (-(|x| ^ 2 / 2)) =
      x ^ (2 * n) * Real.exp (-(x ^ 2 / 2))
    rw [sq_abs, Even.pow_abs (even_two_mul n)]
  change (∫ x : ℝ, f x) = _
  rw [← heven, integral_comp_abs,
    integral_Ioi_pow_two_mul_exp_neg_sq_half]

/-- The exact `2n`-th moment of the standard real Gaussian. -/
theorem integral_pow_two_gaussianReal (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂gaussianReal 0 1) =
      ((2 * n - 1 : ℕ)‼ : ℝ) := by
  rw [integral_gaussianReal_eq_integral_smul
    (by norm_num : (1 : NNReal) ≠ 0)]
  change (∫ x : ℝ, gaussianPDFReal 0 1 x * x ^ (2 * n)) = _
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, sub_zero, mul_one]
  rw [show (∫ x : ℝ, (√(2 * π))⁻¹ *
      Real.exp (-(x ^ 2) / 2) * x ^ (2 * n)) =
      (√(2 * π))⁻¹ *
        ∫ x : ℝ, x ^ (2 * n) * Real.exp (-(x ^ 2 / 2)) by
    rw [show (fun x : ℝ ↦ (√(2 * π))⁻¹ *
        Real.exp (-(x ^ 2) / 2) * x ^ (2 * n)) =
        fun x : ℝ ↦ (√(2 * π))⁻¹ *
          (x ^ (2 * n) * Real.exp (-(x ^ 2 / 2))) by
      funext x
      ring]
    simpa using (MeasureTheory.integral_const_mul
      (μ := volume) (L := ℝ) (√(2 * π))⁻¹
      (fun x : ℝ ↦ x ^ (2 * n) * Real.exp (-(x ^ 2 / 2))))]
  rw [integral_pow_two_mul_exp_neg_sq_half]
  have harg : ((((2 * n : ℕ) : ℝ) + 1) / 2) =
      (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  rw [harg]
  rw [Real.Gamma_nat_add_half]
  have hsqrtpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hsqrt2pi : √(2 * π) = √2 * √π := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsqrt2pi]
  have hsqrt2 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  have hpow : (1 / 2 : ℝ) ^ (-(((2 * n : ℕ) : ℝ) + 1) / 2) =
      (2 : ℝ) ^ n * √2 := by
    have hexp : -(((2 * n : ℕ) : ℝ) + 1) / 2 =
        -((n : ℝ) + 1 / 2) := by
      push_cast
      ring
    rw [hexp, one_div, Real.rpow_neg (by positivity),
      Real.inv_rpow (by positivity), inv_inv,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_natCast]
    simpa [one_div] using congrArg (fun z : ℝ ↦ (2 : ℝ) ^ n * z)
      (Real.sqrt_eq_rpow 2).symm
  rw [hpow]
  push_cast
  field_simp [hsqrtpi.ne', hsqrt2.ne']

/-- Odd moments of the centered standard real Gaussian vanish. -/
theorem integral_pow_odd_gaussianReal (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n + 1) ∂gaussianReal 0 1) = 0 := by
  have hsymm : Measure.map (fun x : ℝ ↦ -x) (gaussianReal 0 1) =
      gaussianReal 0 1 := by rw [gaussianReal_map_neg]; simp
  have hint : Integrable (fun x : ℝ ↦ x ^ (2 * n + 1)) (gaussianReal 0 1) := by
    have habs : Integrable (fun x : ℝ ↦ ‖(id x)‖ ^ (2 * n + 1))
        (gaussianReal 0 1) :=
      (memLp_id_gaussianReal' ((2 * n + 1 : ℕ) : ENNReal)
        (by exact ENNReal.coe_ne_top)).integrable_norm_pow'
    apply habs.mono
    · fun_prop
    · exact Filter.Eventually.of_forall fun x ↦ by
        simp only [id_eq, norm_pow]
        rw [Real.norm_of_nonneg (norm_nonneg x)]
  have hstrong : AEStronglyMeasurable (fun x : ℝ ↦ x ^ (2 * n + 1))
      ((gaussianReal 0 1).map fun x : ℝ ↦ -x) := by
    rw [hsymm]
    exact hint.aestronglyMeasurable
  have hmap := integral_map (μ := gaussianReal 0 1)
    (f := fun x : ℝ ↦ x ^ (2 * n + 1)) (by fun_prop) hstrong
  rw [hsymm] at hmap
  have hneg : (∫ x : ℝ, (-x) ^ (2 * n + 1) ∂gaussianReal 0 1) =
      -(∫ x : ℝ, x ^ (2 * n + 1) ∂gaussianReal 0 1) := by
    have hodd : Odd (2 * n + 1) := ⟨n, by omega⟩
    simp_rw [hodd.neg_pow]
    exact integral_neg _
  rw [hneg] at hmap
  linarith

/-- Complex-valued version of the exact even-moment formula. -/
theorem integral_complex_pow_two_gaussianReal (n : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ (2 * n) ∂gaussianReal 0 1) =
      Complex.ofReal (((2 * n - 1 : ℕ)‼ : ℝ)) := by
  calc
    (∫ x : ℝ, (x : ℂ) ^ (2 * n) ∂gaussianReal 0 1) =
        ∫ x : ℝ, ((x ^ (2 * n) : ℝ) : ℂ) ∂gaussianReal 0 1 := by
      congr 1
      funext x
      norm_num
    _ = Complex.ofReal (∫ x : ℝ, x ^ (2 * n) ∂gaussianReal 0 1) :=
      integral_complex_ofReal
    _ = Complex.ofReal (((2 * n - 1 : ℕ)‼ : ℝ)) := by
      rw [integral_pow_two_gaussianReal]

/-- Complex-valued version of the vanishing odd-moment formula. -/
theorem integral_complex_pow_odd_gaussianReal (n : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ (2 * n + 1) ∂gaussianReal 0 1) = 0 := by
  calc
    (∫ x : ℝ, (x : ℂ) ^ (2 * n + 1) ∂gaussianReal 0 1) =
        ∫ x : ℝ, ((x ^ (2 * n + 1) : ℝ) : ℂ) ∂gaussianReal 0 1 := by
      congr 1
      funext x
      norm_num
    _ = Complex.ofReal (∫ x : ℝ, x ^ (2 * n + 1) ∂gaussianReal 0 1) :=
      integral_complex_ofReal
    _ = 0 := by rw [integral_pow_odd_gaussianReal]; norm_num

end

end LogdetLean.GramHafnian
