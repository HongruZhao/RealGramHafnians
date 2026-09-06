import LogdetLean.GammaMellin
import Mathlib.MeasureTheory.Measure.Real
/-!
# Negative one-half moments of Gamma laws

The real Gram--hafnian small-ball problem requires `E[V^(-1/2)]`, rather
than the inverse first moment occurring in the complex proof.  This file
derives the exact Gamma factor directly from the already verified Mellin
transform.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Exact negative one-half moment of a Gamma law in the rate convention
used by mathlib and the project. -/
theorem integral_rpow_neg_half_gammaMeasure {a r : ℝ}
    (ha : 1 / 2 < a) (hr : 0 < r) :
    ∫ x : ℝ, x ^ (-(1 / 2 : ℝ)) ∂gammaMeasure a r =
      r ^ (1 / 2 : ℝ) * Real.Gamma (a - 1 / 2) / Real.Gamma a := by
  have hmellin := LogdetLean.integral_rpow_gammaMeasure
    (a := a) (r := r) (t := -(1 / 2 : ℝ)) (by linarith) hr (by linarith)
  convert hmellin using 1 <;> ring

/-- Integrability of the negative one-half power. -/
theorem integrable_rpow_neg_half_gammaMeasure {a r : ℝ}
    (ha : 1 / 2 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_rpow_neg_half_gammaMeasure ha hr]
  have hshape : 0 < a - 1 / 2 := by linarith
  exact (div_pos
    (mul_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos hshape))
    (Real.Gamma_pos_of_pos (by linarith))).ne'

/-- Gamma laws with positive shape and rate are supported on the positive
half-line. -/
theorem gammaMeasure_pos_ae {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  have hnonpos : gammaMeasure a r (Iic 0) = 0 := by
    have hset : Iic (0 : ℝ) = Iio 0 ∪ {0} := by
      ext x
      simp [le_iff_lt_or_eq]
    rw [hset, measure_union_null]
    · rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
      exact lintegral_gammaPDF_of_nonpos (le_refl 0)
    · simp [gammaMeasure]
  rw [ae_iff]
  simpa only [show {x : ℝ | ¬ 0 < x} = Iic 0 by ext x; simp] using hnonpos

/-- Extended-nonnegative form of the exact negative one-half Gamma moment. -/
theorem lintegral_ofReal_rpow_neg_half_gammaMeasure {a r : ℝ}
    (ha : 1 / 2 < a) (hr : 0 < r) :
    ∫⁻ x : ℝ, ENNReal.ofReal (x ^ (-(1 / 2 : ℝ))) ∂gammaMeasure a r =
      ENNReal.ofReal
        (r ^ (1 / 2 : ℝ) * Real.Gamma (a - 1 / 2) / Real.Gamma a) := by
  have hpos := gammaMeasure_pos_ae (show 0 < a by linarith) hr
  have hnonneg :
      0 ≤ᵐ[gammaMeasure a r] (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [hpos] with x hx
    exact Real.rpow_nonneg hx.le _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_rpow_neg_half_gammaMeasure ha hr) hnonneg]
  rw [integral_rpow_neg_half_gammaMeasure ha hr]

/-- The real auxiliary Fourier radius at cofactor level `r` has
`chi-square(2r-1)` law.  Its negative one-half moment is the exact factor
appearing in the beta-one recurrence. -/
theorem chiSquare_odd_negativeHalfFactor (r : ℕ) (hr : 2 ≤ r) :
    ∫ x : ℝ, x ^ (-(1 / 2 : ℝ))
        ∂gammaMeasure ((2 * (r : ℝ) - 1) / 2) (1 / 2) =
      (1 / 2 : ℝ) ^ (1 / 2 : ℝ) * Real.Gamma ((r : ℝ) - 1) /
        Real.Gamma ((r : ℝ) - 1 / 2) := by
  have hshape : (1 / 2 : ℝ) < (2 * (r : ℝ) - 1) / 2 := by
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have h := integral_rpow_neg_half_gammaMeasure
    (a := (2 * (r : ℝ) - 1) / 2) (r := 1 / 2)
    hshape (by norm_num)
  convert h using 1 <;> congr 2 <;> ring

end

end LogdetLean.GramHafnian
