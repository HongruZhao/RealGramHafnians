import LogdetLean.GammaMellin
import LogdetLean.GramHafnian.CircularGaussianMoments
/-!
# Gamma inverse moments for the Fourier-compression step

The paper uses the rate-one convention.  This file specializes the existing
proved Mellin transform to exponent `-1` and records the exact real and
`ENNReal` inverse moments.  No special-function identity is assumed: the
only simplification is the proved Gamma recursion `Γ(a)= (a-1)Γ(a-1)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Exact inverse moment of a Gamma law with arbitrary positive rate. -/
theorem integral_inv_gammaMeasure {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    ∫ x : ℝ, x⁻¹ ∂gammaMeasure a r = r / (a - 1) := by
  have hmellin := LogdetLean.integral_rpow_gammaMeasure
    (a := a) (r := r) (t := -1) (by linarith) hr (by linarith)
  have hgamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    have hrec := Real.Gamma_add_one (s := a - 1) (by linarith)
    convert hrec using 1 <;> ring
  calc
    (∫ x : ℝ, x⁻¹ ∂gammaMeasure a r) =
        r * Real.Gamma (a - 1) / Real.Gamma a := by
      simpa only [Real.rpow_neg_one, neg_neg, Real.rpow_one,
        sub_eq_add_neg] using hmellin
    _ = r / (a - 1) := by
      rw [hgamma]
      have hshape : a - 1 ≠ 0 := by linarith
      have hG : Real.Gamma (a - 1) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by linarith)).ne'
      field_simp [hshape, hG]

/-- Integrability of the inverse for every positive rate. -/
theorem integrable_inv_gammaMeasure {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x⁻¹) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_inv_gammaMeasure ha hr]
  exact div_ne_zero hr.ne' (by linarith)

/-- `ENNReal` form of the arbitrary-rate inverse Gamma moment. -/
theorem lintegral_ofReal_inv_gammaMeasure {a r : ℝ}
    (ha : 1 < a) (hr : 0 < r) :
    ∫⁻ x : ℝ, ENNReal.ofReal x⁻¹ ∂gammaMeasure a r =
      ENNReal.ofReal (r / (a - 1)) := by
  have hnonpos : gammaMeasure a r (Iic 0) = 0 := by
    have hset : Iic (0 : ℝ) = Iio 0 ∪ {0} := by
      ext x
      simp [le_iff_lt_or_eq]
    rw [hset, measure_union_null]
    · rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
      exact lintegral_gammaPDF_of_nonpos (le_refl 0)
    · simp [gammaMeasure]
  have hpos : ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
    rw [ae_iff]
    simpa only [show {x : ℝ | ¬ 0 < x} = Iic 0 by ext x; simp] using hnonpos
  have hnonneg : 0 ≤ᵐ[gammaMeasure a r] (fun x : ℝ ↦ x⁻¹) := by
    filter_upwards [hpos] with x hx
    exact inv_nonneg.mpr hx.le
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_inv_gammaMeasure ha hr) hnonneg]
  rw [integral_inv_gammaMeasure ha hr]

/-- Exact inverse moment of a rate-one Gamma law. -/
theorem integral_inv_gammaMeasure_one {a : ℝ} (ha : 1 < a) :
    ∫ x : ℝ, x⁻¹ ∂gammaMeasure a 1 = (a - 1)⁻¹ := by
  have hmellin := LogdetLean.integral_rpow_gammaMeasure
    (a := a) (r := 1) (t := -1) (by linarith) (by norm_num) (by linarith)
  have hgamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    have hrec := Real.Gamma_add_one (s := a - 1) (by linarith)
    convert hrec using 1 <;> ring
  calc
    (∫ x : ℝ, x⁻¹ ∂gammaMeasure a 1) =
        Real.Gamma (a - 1) / Real.Gamma a := by
      simpa only [Real.rpow_neg_one, one_div, one_mul, neg_neg,
        Real.one_rpow, sub_eq_add_neg] using hmellin
    _ = (a - 1)⁻¹ := by
      rw [hgamma]
      have hshape : a - 1 ≠ 0 := by linarith
      have hG : Real.Gamma (a - 1) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by linarith)).ne'
      field_simp [hshape, hG]

/-- Integrability follows from the nonzero finite Mellin integral; Lean's
Bochner integral is zero for a nonintegrable function, so a nonzero evaluated
integral certifies integrability. -/
theorem integrable_inv_gammaMeasure_one {a : ℝ} (ha : 1 < a) :
    Integrable (fun x : ℝ ↦ x⁻¹) (gammaMeasure a 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_inv_gammaMeasure_one ha]
  exact inv_ne_zero (by linarith)

/-- A rate-one Gamma variable of shape `a>1` has the exact nonnegative
inverse moment `(a-1)⁻¹`, in the `ENNReal` form used by Tonelli arguments. -/
theorem lintegral_ofReal_inv_gammaMeasure_one {a : ℝ} (ha : 1 < a) :
    ∫⁻ x : ℝ, ENNReal.ofReal x⁻¹ ∂gammaMeasure a 1 =
      ENNReal.ofReal (a - 1)⁻¹ := by
  have hnonpos : gammaMeasure a 1 (Iic 0) = 0 := by
    have hset : Iic (0 : ℝ) = Iio 0 ∪ {0} := by
      ext x
      simp [le_iff_lt_or_eq]
    rw [hset, measure_union_null]
    · rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
      exact lintegral_gammaPDF_of_nonpos (le_refl 0)
    · simp [gammaMeasure]
  have hpos : ∀ᵐ x ∂gammaMeasure a 1, 0 < x := by
    rw [ae_iff]
    simpa only [show {x : ℝ | ¬ 0 < x} = Iic 0 by ext x; simp] using hnonpos
  have hnonneg : 0 ≤ᵐ[gammaMeasure a 1] (fun x : ℝ ↦ x⁻¹) := by
    filter_upwards [hpos] with x hx
    exact inv_nonneg.mpr hx.le
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_inv_gammaMeasure_one ha) hnonneg]
  rw [integral_inv_gammaMeasure_one ha]

/-- Integer-shape form used at cofactor level `r`: if
`G ~ Gamma(2r-1,1)`, then `E G⁻¹ = 1/(2r-2)`. -/
theorem lintegral_ofReal_inv_gammaMeasure_two_mul_sub_one
    {r : ℕ} (hr : 2 ≤ r) :
    ∫⁻ x : ℝ, ENNReal.ofReal x⁻¹
        ∂gammaMeasure (2 * (r : ℝ) - 1) 1 =
      ENNReal.ofReal (2 * (r : ℝ) - 2)⁻¹ := by
  have hshape : (1 : ℝ) < 2 * (r : ℝ) - 1 := by
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  simpa only [sub_sub, one_add_one_eq_two] using
    (lintegral_ofReal_inv_gammaMeasure_one (a := 2 * (r : ℝ) - 1) hshape)

end

end LogdetLean.GramHafnian
