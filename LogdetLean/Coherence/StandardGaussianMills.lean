import LogdetLean.Coherence.ProbabilityIntegralTransform
import LogdetLean.GaussianAntiConcentration
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
/-!
# Elementary standard-Gaussian Mills and perturbation bounds

This file supplies the relative Gaussian-tail estimates used by the
noncentral-Pearson moderate-deviation argument.  All constants are explicit,
but deliberately non-optimal: the point is a global, axiom-free bound that is
stable under perturbations whose size is small compared with the reciprocal
Gaussian hazard.
-/

namespace LogdetLean.Coherence

open MeasureTheory ProbabilityTheory Set

noncomputable section

-- Use the normed-algebra structure on `ℝ` for one-dimensional calculus.
-- This resolves the harmless `Module ℝ ℝ` typeclass diamond between the
-- ordered-ring and real-inner-product imports in the surrounding project.
attribute [local instance 2000] NormedAlgebra.toNormedSpace

/-- `HasDerivAt` with the normed-algebra real scalar structure.  Mathlib has
two propositionally equal `Module ℝ ℝ` paths in this import graph; naming the
one used by its derivative combinators keeps the internal calculus lemmas
definitionally aligned. -/
abbrev algebraRealHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule _ _ f f' x

/-- The upper tail of the standard Gaussian law. -/
def standardGaussianUpperTail (x : ℝ) : ℝ :=
  1 - cdf (gaussianReal 0 1) x

@[simp] theorem standardGaussianUpperTail_eq_one_sub_standardNormalCDF (x : ℝ) :
    standardGaussianUpperTail x = 1 - standardNormalCDF x := rfl

/-- The standard Gaussian upper tail is strictly positive at every finite
point. -/
theorem standardGaussianUpperTail_pos (x : ℝ) :
    0 < standardGaussianUpperTail x := by
  have hx := cdf_mem_Ioo_of_strictMono (gaussianReal 0 1)
    strictMono_standardNormalCDF x
  unfold standardGaussianUpperTail
  exact sub_pos.mpr hx.2

theorem standardGaussianUpperTail_nonneg (x : ℝ) :
    0 ≤ standardGaussianUpperTail x :=
  (standardGaussianUpperTail_pos x).le

/-- The derivative of the upper tail is minus the Gaussian density. -/
theorem hasDerivAt_standardGaussianUpperTail (x : ℝ) :
    algebraRealHasDerivAt standardGaussianUpperTail
      (-gaussianPDFReal 0 1 x) x := by
  change algebraRealHasDerivAt
    (fun y ↦ 1 - cdf (gaussianReal 0 1) y)
    (-gaussianPDFReal 0 1 x) x
  simpa only [algebraRealHasDerivAt] using
    (LogdetLean.hasDerivAt_standardGaussian_cdf x).const_sub (1 : ℝ)

/-- The standard Gaussian density decreases on the nonnegative half-line. -/
theorem standardGaussianPDF_antitoneOn_nonneg :
    AntitoneOn (gaussianPDFReal 0 1) (Ici 0) := by
  intro x hx y hy hxy
  rw [gaussianPDFReal, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hsqrt : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  apply mul_le_mul_of_nonneg_left _ hsqrt
  apply Real.exp_le_exp.mpr
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hprod : 0 ≤ (y - x) * (y + x) :=
    mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
  nlinarith

/-- Moving by `1/(1+x)` from a nonnegative `x` decreases the Gaussian
density by at most the fixed factor `exp(-2)`. -/
theorem exp_neg_two_mul_standardGaussianPDF_le_shift
    {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-2) * gaussianPDFReal 0 1 x ≤
      gaussianPDFReal 0 1 (x + 1 / (1 + x)) := by
  have hden : 0 < 1 + x := by linarith
  let a : ℝ := 1 / (1 + x)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha_le : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one hden).2 (by linarith)
  have hxa_le : x * a ≤ 1 := by
    dsimp [a]
    rw [one_div, ← div_eq_mul_inv]
    exact (div_le_one hden).2 (by linarith)
  have hsquare : (x + a) ^ 2 ≤ x ^ 2 + 4 := by
    nlinarith [sq_nonneg a]
  change Real.exp (-2) * gaussianPDFReal 0 1 x ≤
    gaussianPDFReal 0 1 (x + a)
  rw [gaussianPDFReal, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hsqrt : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  calc
    Real.exp (-2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp ((-2) + (-x ^ 2 / 2)) := by
          rw [Real.exp_add]
          ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(x + a) ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ hsqrt
      apply Real.exp_le_exp.mpr
      nlinarith

/-- An elementary lower Mills bound.  The constant `exp(-2)` is not sharp,
but the order `phi(x)/(1+x)` is the sharp order needed downstream. -/
theorem exp_neg_two_mul_pdf_div_one_add_le_upperTail
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / (1 + x)) *
        (Real.exp (-2) * gaussianPDFReal 0 1 x) ≤
      standardGaussianUpperTail x := by
  let a : ℝ := 1 / (1 + x)
  have hden : 0 < 1 + x := by linarith
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let F : ℝ → ℝ := cdf (gaussianReal 0 1)
  have hdiff : Differentiable ℝ F := by
    intro y
    exact (LogdetLean.hasDerivAt_standardGaussian_cdf y).differentiableAt
  have hmvt :
      gaussianPDFReal 0 1 (x + a) * ((x + a) - x) ≤
        F (x + a) - F x := by
    apply Convex.mul_sub_le_image_sub_of_le_deriv
      (D := Icc x (x + a)) (convex_Icc x (x + a))
      hdiff.continuous.continuousOn hdiff.differentiableOn
    · intro y hy
      rw [(LogdetLean.hasDerivAt_standardGaussian_cdf y).deriv]
      have hy' : y ∈ Icc x (x + a) := interior_subset hy
      exact standardGaussianPDF_antitoneOn_nonneg
        (hx.trans hy'.1) (hx.trans (by linarith : x ≤ x + a)) hy'.2
    · exact ⟨le_rfl, by linarith⟩
    · exact ⟨by linarith, le_rfl⟩
    · linarith
  have hshift := exp_neg_two_mul_standardGaussianPDF_le_shift hx
  have hinterval :
      a * (Real.exp (-2) * gaussianPDFReal 0 1 x) ≤
        F (x + a) - F x := by
    calc
      a * (Real.exp (-2) * gaussianPDFReal 0 1 x) ≤
          a * gaussianPDFReal 0 1 (x + a) :=
        mul_le_mul_of_nonneg_left hshift ha.le
      _ = gaussianPDFReal 0 1 (x + a) * ((x + a) - x) := by ring
      _ ≤ F (x + a) - F x := hmvt
  have hCDF : F (x + a) ≤ 1 := cdf_le_one _ _
  unfold standardGaussianUpperTail
  dsimp [F] at hinterval hCDF
  dsimp [a] at hinterval ⊢
  linarith

/-- A global Gaussian hazard bound.  Its linear growth in `|x|` is the key
feature; the constant `exp 2` is harmless for moderate deviations. -/
theorem standardGaussianPDF_le_exp_two_mul_abs_mul_upperTail (x : ℝ) :
    gaussianPDFReal 0 1 x ≤
      Real.exp 2 * (1 + |x|) * standardGaussianUpperTail x := by
  by_cases hx : 0 ≤ x
  · have hmills := exp_neg_two_mul_pdf_div_one_add_le_upperTail hx
    have hfactor : 0 ≤ Real.exp 2 * (1 + x) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmills hfactor
    rw [abs_of_nonneg hx]
    calc
      gaussianPDFReal 0 1 x =
          (Real.exp 2 * (1 + x)) *
            ((1 / (1 + x)) *
              (Real.exp (-2) * gaussianPDFReal 0 1 x)) := by
        have hden : (1 + x) ≠ 0 := by linarith
        field_simp
        rw [mul_assoc, ← Real.exp_add]
        norm_num
      _ ≤ (Real.exp 2 * (1 + x)) * standardGaussianUpperTail x := hmul
      _ = Real.exp 2 * (1 + x) * standardGaussianUpperTail x := rfl
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hpeak := LogdetLean.gaussianPDFReal_zero_one_le_peak x
    have hpdfzero :
        1 / Real.sqrt (2 * Real.pi) = gaussianPDFReal 0 1 0 := by
      rw [gaussianPDFReal]
      norm_num
    rw [hpdfzero] at hpeak
    have hmills0 :=
      exp_neg_two_mul_pdf_div_one_add_le_upperTail (x := 0) (le_refl 0)
    norm_num at hmills0
    have htailmono :
        standardGaussianUpperTail 0 ≤ standardGaussianUpperTail x := by
      have hcdf := monotone_cdf (gaussianReal 0 1) hxneg.le
      unfold standardGaussianUpperTail
      linarith
    have hbase : gaussianPDFReal 0 1 x ≤
        Real.exp 2 * standardGaussianUpperTail x := by
      calc
        gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 0 := hpeak
        _ = Real.exp 2 *
            (Real.exp (-2) * gaussianPDFReal 0 1 0) := by
          symm
          calc
            Real.exp 2 *
                (Real.exp (-2) * gaussianPDFReal 0 1 0) =
              (Real.exp 2 * Real.exp (-2)) *
                gaussianPDFReal 0 1 0 := by ring
            _ = gaussianPDFReal 0 1 0 := by
              rw [← Real.exp_add]
              norm_num
        _ ≤ Real.exp 2 * standardGaussianUpperTail 0 :=
          mul_le_mul_of_nonneg_left hmills0 (Real.exp_pos _).le
        _ ≤ Real.exp 2 * standardGaussianUpperTail x :=
          mul_le_mul_of_nonneg_left htailmono (Real.exp_pos _).le
    have hone : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
    calc
      gaussianPDFReal 0 1 x ≤ Real.exp 2 * standardGaussianUpperTail x := hbase
      _ ≤ Real.exp 2 * (1 + |x|) * standardGaussianUpperTail x := by
        calc
          Real.exp 2 * standardGaussianUpperTail x =
              (Real.exp 2 * 1) * standardGaussianUpperTail x := by ring
          _ ≤ (Real.exp 2 * (1 + |x|)) * standardGaussianUpperTail x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hone (Real.exp_pos 2).le)
              (standardGaussianUpperTail_nonneg x)

/-- Derivative of the log upper tail. -/
theorem hasDerivAt_log_standardGaussianUpperTail (x : ℝ) :
    algebraRealHasDerivAt (fun y ↦ Real.log (standardGaussianUpperTail y))
      (-gaussianPDFReal 0 1 x / standardGaussianUpperTail x) x := by
  simpa using
    (hasDerivAt_standardGaussianUpperTail x).log
      (standardGaussianUpperTail_pos x).ne'

/-- The absolute logarithmic derivative of the Gaussian upper tail grows at
most linearly. -/
theorem abs_log_standardGaussianUpperTail_deriv_le (x : ℝ) :
    |-gaussianPDFReal 0 1 x / standardGaussianUpperTail x| ≤
      Real.exp 2 * (1 + |x|) := by
  rw [abs_div, abs_neg, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x),
    abs_of_pos (standardGaussianUpperTail_pos x)]
  exact (div_le_iff₀ (standardGaussianUpperTail_pos x)).2
    (standardGaussianPDF_le_exp_two_mul_abs_mul_upperTail x)

/-- Global Lipschitz-type control of the logarithmic Gaussian tail along a
finite perturbation. -/
theorem abs_log_upperTail_add_sub_log_upperTail_le (x h : ℝ) :
    |Real.log (standardGaussianUpperTail (x + h)) -
        Real.log (standardGaussianUpperTail x)| ≤
      Real.exp 2 * |h| * (1 + |x| + |h|) := by
  let F : ℝ → ℝ := fun t ↦
    Real.log (standardGaussianUpperTail (x + t * h))
  let F' : ℝ → ℝ := fun t ↦
    h * (-gaussianPDFReal 0 1 (x + t * h) /
      standardGaussianUpperTail (x + t * h))
  have hderiv : ∀ t : ℝ, algebraRealHasDerivAt F (F' t) t := by
    intro t
    have hinner : algebraRealHasDerivAt (fun s : ℝ ↦ x + s * h) h t := by
      simpa using ((hasDerivAt_id t).mul_const h).const_add x
    change algebraRealHasDerivAt
      (fun s ↦ Real.log (standardGaussianUpperTail (x + s * h)))
      (h * (-gaussianPDFReal 0 1 (x + t * h) /
        standardGaussianUpperTail (x + t * h))) t
    convert
      (hasDerivAt_log_standardGaussianUpperTail (x + t * h)).comp t hinner
        using 1 <;>
      simp [Function.comp_def, mul_comm]
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖F' t‖ ≤ Real.exp 2 * |h| * (1 + |x| + |h|) := by
    intro t ht
    have ht_abs : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2
    have harg : |x + t * h| ≤ |x| + |h| := by
      calc
        |x + t * h| ≤ |x| + |t * h| := abs_add_le _ _
        _ = |x| + |t| * |h| := by rw [abs_mul]
        _ ≤ |x| + 1 * |h| := by gcongr
        _ = |x| + |h| := by ring
    have hhazard := abs_log_standardGaussianUpperTail_deriv_le (x + t * h)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |h| *
          |-gaussianPDFReal 0 1 (x + t * h) /
            standardGaussianUpperTail (x + t * h)| ≤
          |h| * (Real.exp 2 * (1 + |x + t * h|)) :=
        mul_le_mul_of_nonneg_left hhazard (abs_nonneg h)
      _ ≤ |h| * (Real.exp 2 * (1 + (|x| + |h|))) := by
        gcongr
      _ = Real.exp 2 * |h| * (1 + |x| + |h|) := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := (0 : ℝ)) (y := 1)
    (s := Icc (0 : ℝ) 1) (f := F) (f' := F')
    (fun t _ht ↦ (hderiv t).hasDerivWithinAt)
    (fun t ht ↦ hbound t ht) (convex_Icc (0 : ℝ) 1)
      (by norm_num) (by norm_num)
  simpa [F, Real.norm_eq_abs] using hmvt

/-- Two-sided multiplicative perturbation control for the Gaussian upper
tail. -/
theorem standardGaussianUpperTail_multiplicative_perturbation (x h : ℝ) :
    let E := Real.exp 2 * |h| * (1 + |x| + |h|)
    standardGaussianUpperTail x * Real.exp (-E) ≤
        standardGaussianUpperTail (x + h) ∧
      standardGaussianUpperTail (x + h) ≤
        standardGaussianUpperTail x * Real.exp E := by
  let E : ℝ := Real.exp 2 * |h| * (1 + |x| + |h|)
  change standardGaussianUpperTail x * Real.exp (-E) ≤
      standardGaussianUpperTail (x + h) ∧
    standardGaussianUpperTail (x + h) ≤
      standardGaussianUpperTail x * Real.exp E
  let A : ℝ := Real.log (standardGaussianUpperTail (x + h)) -
    Real.log (standardGaussianUpperTail x)
  have hlog : |A| ≤ E := by
    simpa [A, E] using abs_log_upperTail_add_sub_log_upperTail_le x h
  have hpair : -E ≤ A ∧ A ≤ E := (abs_le.mp hlog)
  change
    (-E ≤ Real.log (standardGaussianUpperTail (x + h)) -
        Real.log (standardGaussianUpperTail x)) ∧
      (Real.log (standardGaussianUpperTail (x + h)) -
        Real.log (standardGaussianUpperTail x) ≤ E) at hpair
  have hlower :
      Real.log (standardGaussianUpperTail x) - E ≤
        Real.log (standardGaussianUpperTail (x + h)) := by
    linarith [hpair.1]
  have hupper :
      Real.log (standardGaussianUpperTail (x + h)) ≤
        Real.log (standardGaussianUpperTail x) + E := by
    linarith [hpair.2]
  constructor
  · have hexp := Real.exp_le_exp.mpr hlower
    rw [Real.exp_sub,
      Real.exp_log (standardGaussianUpperTail_pos x),
      Real.exp_log (standardGaussianUpperTail_pos (x + h)),
      div_eq_mul_inv, ← Real.exp_neg] at hexp
    exact hexp
  · have hexp := Real.exp_le_exp.mpr hupper
    rw [Real.exp_add,
      Real.exp_log (standardGaussianUpperTail_pos x),
      Real.exp_log (standardGaussianUpperTail_pos (x + h))] at hexp
    exact hexp

/-- Ratio form of the same multiplicative perturbation estimate. -/
theorem standardGaussianUpperTail_ratio_perturbation (x h : ℝ) :
    let E := Real.exp 2 * |h| * (1 + |x| + |h|)
    Real.exp (-E) ≤
        standardGaussianUpperTail (x + h) /
          standardGaussianUpperTail x ∧
      standardGaussianUpperTail (x + h) /
          standardGaussianUpperTail x ≤ Real.exp E := by
  dsimp only
  obtain ⟨hlower, hupper⟩ :=
    standardGaussianUpperTail_multiplicative_perturbation x h
  constructor
  · exact (le_div_iff₀ (standardGaussianUpperTail_pos x)).2 (by
      simpa [mul_comm] using hlower)
  · exact (div_le_iff₀ (standardGaussianUpperTail_pos x)).2 (by
      simpa [mul_comm] using hupper)

end

end LogdetLean.Coherence
