import LogdetLean.NullEdgeworthGaussianWindow
import LogdetLean.NullGlobalPolynomial
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
/-!
# A large Fourier window for the uniform null Edgeworth estimate

The analytic Taylor expansion is used only on `|t| <= Delta / 4`.  Outside
that window, the exact Gamma-product modulus is monotone in `|t|`, so its
value is frozen at the endpoint and is exponentially small.  The signed
Gaussian--Hermite comparator is handled by an elementary Gaussian envelope.
The eventual Esseen cutoff is the explicit polynomial scale `S = Delta^4`.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

noncomputable section

set_option linter.style.haveILetI false

/-- Standardization preserves the monotonicity in absolute frequency of the
exact Gamma-product modulus. -/
theorem norm_charFun_standardizedNullLaw_antitone_abs
    {m p : ℕ} (h : Admissible m p) {u v : ℝ} (huv : |u| ≤ |v|) :
    ‖charFun (standardizedNullLaw m p) v‖ ≤
      ‖charFun (standardizedNullLaw m p) u‖ := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hs : 0 < Real.sqrt (nullVSeries m p) := Real.sqrt_pos.2 hV
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_charFun_standardizedNullLaw_sq_eq_nullRawModulusSqEulerProduct h,
    norm_charFun_standardizedNullLaw_sq_eq_nullRawModulusSqEulerProduct h]
  unfold nullRawModulusSqEulerProduct
  apply Finset.prod_le_prod
  · intro j hj
    exact (betaModulusEulerProduct_eq_exp_neg_logLoss
      (betaShapeA_pos_of_mem_Icc h.2 hj) (betaShapeTotal_pos h)
      (v / Real.sqrt (nullVSeries m p))).symm ▸ (Real.exp_pos _).le
  · intro j hj
    apply betaModulusEulerProduct_antitone_abs
      (betaShapeA_pos_of_mem_Icc h.2 hj)
      (le_of_lt (betaShapeA_lt_total (Finset.mem_Icc.mp hj).1))
    rw [abs_div, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right huv hs.le

/-- The local Taylor cutoff. -/
def nullEdgeworthLocalCutoff (m p : ℕ) : ℝ :=
  nullAnalyticScale m p / 4

/-- The large Esseen cutoff.  Its fourth power is one order beyond the
universal lower scale `lambda >= (3/8) Delta^{-3}`. -/
def nullEdgeworthSmoothingCutoff (m p : ℕ) : ℝ :=
  (nullAnalyticScale m p) ^ 4

theorem nullEdgeworthLocalCutoff_pos
    {m p : ℕ} (h : Admissible m p) :
    0 < nullEdgeworthLocalCutoff m p := by
  exact div_pos (nullAnalyticScale_pos h) (by norm_num)

theorem nullEdgeworthSmoothingCutoff_pos
    {m p : ℕ} (h : Admissible m p) :
    0 < nullEdgeworthSmoothingCutoff m p := by
  exact pow_pos (nullAnalyticScale_pos h) 4

/-- Endpoint damping at the edge of the Taylor window. -/
theorem norm_charFun_standardizedNullLaw_le_at_localCutoff
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : nullEdgeworthLocalCutoff m p ≤ |t|) :
    ‖charFun (standardizedNullLaw m p) t‖ ≤
      Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) := by
  let a : ℝ := nullEdgeworthLocalCutoff m p
  have ha : 0 < a := by
    dsimp [a]
    exact nullEdgeworthLocalCutoff_pos h
  have hmono := norm_charFun_standardizedNullLaw_antitone_abs h
    (u := a) (v := t) (by simpa [abs_of_pos ha] using ht)
  have hlocal := norm_charFun_standardizedNullLaw_le_gaussian_local h
    (eta := (1 / 4 : ℝ)) (t := a) (by norm_num) (by
      dsimp [a, nullEdgeworthLocalCutoff]
      rw [abs_of_pos (div_pos (nullAnalyticScale_pos h) (by norm_num))]
      have heq : nullAnalyticScale m p / 4 =
          (1 / 4 : ℝ) * nullAnalyticScale m p := by ring
      rw [heq])
  calc
    ‖charFun (standardizedNullLaw m p) t‖ ≤
        ‖charFun (standardizedNullLaw m p) a‖ := hmono
    _ ≤ Real.exp (-(a ^ 2 / (2 * (1 + (1 / 4 : ℝ) ^ 2)))) := hlocal
    _ = Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) := by
      congr 1
      dsimp [a, nullEdgeworthLocalCutoff]
      ring

/-- Absolute first moment of `exp(-t^2/4)`. -/
theorem integral_abs_mul_exp_neg_sq_quarter :
    (∫ t : ℝ, |t| * Real.exp (-(t ^ 2 / 4))) = 4 := by
  let f : ℝ → ℝ := fun x ↦ x * Real.exp (-(x ^ 2 / 4))
  have hf : (fun t : ℝ ↦ |t| * Real.exp (-(t ^ 2 / 4))) =
      fun t ↦ f |t| := by
    funext t
    simp only [f, sq_abs]
  rw [hf, integral_comp_abs]
  have hI := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (1 : ℝ)) (b := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hI' : (∫ x in Ioi (0 : ℝ), f x) = 2 := by
    rw [show (∫ x in Ioi (0 : ℝ), f x) =
        ∫ x in Ioi (0 : ℝ), x ^ (1 : ℝ) *
          Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℝ)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      simp only [f]
      rw [show -(x ^ 2 / 4) = -(1 / 4 : ℝ) * x ^ 2 by ring]
      simp only [Real.rpow_one, Real.rpow_ofNat]]
    rw [hI]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [hI']
  norm_num

/-- Absolute third moment of `exp(-t^2/4)`. -/
theorem integral_abs_cube_mul_exp_neg_sq_quarter :
    (∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 / 4))) = 16 := by
  let f : ℝ → ℝ := fun x ↦ x ^ 3 * Real.exp (-(x ^ 2 / 4))
  have hf : (fun t : ℝ ↦ |t| ^ 3 * Real.exp (-(t ^ 2 / 4))) =
      fun t ↦ f |t| := by
    funext t
    simp only [f, sq_abs]
  rw [hf, integral_comp_abs]
  have hI := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (3 : ℝ)) (b := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hI' : (∫ x in Ioi (0 : ℝ), f x) = 8 := by
    rw [show (∫ x in Ioi (0 : ℝ), f x) =
        ∫ x in Ioi (0 : ℝ), x ^ (3 : ℝ) *
          Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℝ)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      simp only [f]
      rw [show -(x ^ 2 / 4) = -(1 / 4 : ℝ) * x ^ 2 by ring]
      simp only [Real.rpow_ofNat]]
    rw [hI]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [hI']
  norm_num

theorem integrable_abs_mul_exp_neg_sq_quarter :
    Integrable (fun t : ℝ ↦ |t| * Real.exp (-(t ^ 2 / 4))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 4 : ℝ)) (by norm_num) (s := (1 : ℝ)) (by norm_num)
  refine h.norm.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only
  simp only [Real.rpow_one]
  rw [norm_mul, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [show -(1 / 4 : ℝ) * x ^ 2 = -(x ^ 2 / 4) by ring]

theorem integrable_abs_cube_mul_exp_neg_sq_quarter :
    Integrable (fun t : ℝ ↦ |t| ^ 3 * Real.exp (-(t ^ 2 / 4))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 4 : ℝ)) (by norm_num) (s := (3 : ℝ)) (by norm_num)
  refine h.norm.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only
  simp only [Real.rpow_ofNat]
  rw [norm_mul, norm_pow, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [show -(1 / 4 : ℝ) * x ^ 2 = -(x ^ 2 / 4) by ring]

/-- A global integrable envelope used only for the Gaussian--Hermite
comparator outside the local Taylor window. -/
def nullFirstEdgeworthComparatorOuterEnvelope
    (m p : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-((nullEdgeworthLocalCutoff m p) ^ 2 / 4)) *
    (|t| * Real.exp (-(t ^ 2 / 4)) /
        (nullEdgeworthLocalCutoff m p) ^ 2 +
      (nullLambdaSeries m p / 6) * |t| ^ 3 *
        Real.exp (-(t ^ 2 / 4)) / nullEdgeworthLocalCutoff m p)

theorem nullFirstEdgeworthComparatorOuterEnvelope_nonneg
    {m p : ℕ} (h : Admissible m p) (t : ℝ) :
    0 ≤ nullFirstEdgeworthComparatorOuterEnvelope m p t := by
  unfold nullFirstEdgeworthComparatorOuterEnvelope
  have ha := (nullEdgeworthLocalCutoff_pos h).le
  have hl := (nullLambdaSeries_pos h).le
  positivity

theorem integrable_nullFirstEdgeworthComparatorOuterEnvelope
    {m p : ℕ} (h : Admissible m p) :
    Integrable (nullFirstEdgeworthComparatorOuterEnvelope m p) := by
  have ha : 0 < nullEdgeworthLocalCutoff m p :=
    nullEdgeworthLocalCutoff_pos h
  unfold nullFirstEdgeworthComparatorOuterEnvelope
  have h1 : Integrable
      (fun t : ℝ ↦ |t| * Real.exp (-(t ^ 2 / 4))) := by
    exact integrable_abs_mul_exp_neg_sq_quarter
  have h3 : Integrable
      (fun t : ℝ ↦ |t| ^ 3 * Real.exp (-(t ^ 2 / 4))) := by
    exact integrable_abs_cube_mul_exp_neg_sq_quarter
  have hsum := (h1.div_const (nullEdgeworthLocalCutoff m p ^ 2)).add
    ((h3.const_mul (nullLambdaSeries m p / 6)).div_const
      (nullEdgeworthLocalCutoff m p))
  have hmul := hsum.const_mul
    (Real.exp (-((nullEdgeworthLocalCutoff m p) ^ 2 / 4)))
  apply hmul.congr
  exact Filter.Eventually.of_forall fun t ↦ by
    dsimp only [Pi.add_apply]
    field_simp [ha.ne']

theorem integral_nullFirstEdgeworthComparatorOuterEnvelope
    {m p : ℕ} (h : Admissible m p) :
    (∫ t : ℝ, nullFirstEdgeworthComparatorOuterEnvelope m p t) =
      Real.exp (-((nullEdgeworthLocalCutoff m p) ^ 2 / 4)) *
        (4 / (nullEdgeworthLocalCutoff m p) ^ 2 +
          8 * nullLambdaSeries m p /
            (3 * nullEdgeworthLocalCutoff m p)) := by
  have ha : 0 < nullEdgeworthLocalCutoff m p :=
    nullEdgeworthLocalCutoff_pos h
  unfold nullFirstEdgeworthComparatorOuterEnvelope
  rw [integral_const_mul]
  have h1 := integrable_abs_mul_exp_neg_sq_quarter
  have h3 := integrable_abs_cube_mul_exp_neg_sq_quarter
  have hfun : (fun a : ℝ ↦
      |a| * Real.exp (-(a ^ 2 / 4)) / nullEdgeworthLocalCutoff m p ^ 2 +
        nullLambdaSeries m p / 6 * |a| ^ 3 *
          Real.exp (-(a ^ 2 / 4)) / nullEdgeworthLocalCutoff m p) =
      (fun a : ℝ ↦
        (|a| * Real.exp (-(a ^ 2 / 4))) /
            nullEdgeworthLocalCutoff m p ^ 2 +
          ((nullLambdaSeries m p / 6) *
            (|a| ^ 3 * Real.exp (-(a ^ 2 / 4)))) /
              nullEdgeworthLocalCutoff m p) := by
    funext a
    ring
  rw [hfun, integral_add (h1.div_const _)
      ((h3.const_mul (nullLambdaSeries m p / 6)).div_const _),
    integral_div, integral_div]
  have hi3 : (∫ a : ℝ,
      nullLambdaSeries m p / 6 *
        (|a| ^ 3 * Real.exp (-(a ^ 2 / 4)))) =
      (nullLambdaSeries m p / 6) * 16 := by
    rw [integral_const_mul, integral_abs_cube_mul_exp_neg_sq_quarter]
  rw [integral_abs_mul_exp_neg_sq_quarter, hi3]
  field_simp [ha.ne']
  ring

theorem norm_nullFirstEdgeworthCharFun_le
    {m p : ℕ} (h : Admissible m p) (t : ℝ) :
    ‖nullFirstEdgeworthCharFun m p t‖ ≤
      Real.exp (-(t ^ 2 / 2)) *
        (1 + nullLambdaSeries m p * |t| ^ 3 / 6) := by
  unfold nullFirstEdgeworthCharFun
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    ‖1 + nullCubicCharacteristicTerm m p t‖ ≤
        ‖(1 : ℂ)‖ + ‖nullCubicCharacteristicTerm m p t‖ := norm_add_le _ _
    _ = 1 + nullLambdaSeries m p * |t| ^ 3 / 6 := by
      rw [norm_nullCubicCharacteristicTerm h]
      norm_num

/-- Outside the local window, the weighted comparator is dominated by the
global Gaussian envelope above. -/
theorem norm_nullFirstEdgeworthCharFun_div_abs_le_outerEnvelope
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : nullEdgeworthLocalCutoff m p ≤ |t|) :
    ‖nullFirstEdgeworthCharFun m p t‖ / |t| ≤
      nullFirstEdgeworthComparatorOuterEnvelope m p t := by
  let a : ℝ := nullEdgeworthLocalCutoff m p
  let x : ℝ := |t|
  have ha : 0 < a := by dsimp [a]; exact nullEdgeworthLocalCutoff_pos h
  have hx : 0 < x := ha.trans_le (by simpa [a, x] using ht)
  have hatx : a ≤ x := by simpa [a, x] using ht
  have hsquare : a ^ 2 ≤ t ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ ha.le (abs_nonneg t)).2 (by simpa [x] using hatx)
  have hexpSplit : Real.exp (-(t ^ 2 / 2)) =
      Real.exp (-(t ^ 2 / 4)) * Real.exp (-(t ^ 2 / 4)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpEndpoint : Real.exp (-(t ^ 2 / 4)) ≤
      Real.exp (-(a ^ 2 / 4)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hone : 1 / x ≤ x / a ^ 2 := by
    rw [div_le_div_iff₀ hx (sq_pos_of_pos ha)]
    nlinarith
  have htwo : x ^ 2 ≤ x ^ 3 / a := by
    rw [le_div_iff₀ ha]
    nlinarith [mul_le_mul_of_nonneg_left hatx (sq_nonneg x)]
  have hbase := norm_nullFirstEdgeworthCharFun_le h t
  calc
    ‖nullFirstEdgeworthCharFun m p t‖ / |t| ≤
        (Real.exp (-(t ^ 2 / 2)) *
          (1 + nullLambdaSeries m p * x ^ 3 / 6)) / x := by
      simpa [x] using div_le_div_of_nonneg_right hbase hx.le
    _ = Real.exp (-(t ^ 2 / 2)) *
        (1 / x + (nullLambdaSeries m p / 6) * x ^ 2) := by
      field_simp [hx.ne']
    _ ≤ (Real.exp (-(t ^ 2 / 4)) * Real.exp (-(a ^ 2 / 4))) *
        (x / a ^ 2 + (nullLambdaSeries m p / 6) * (x ^ 3 / a)) := by
      rw [hexpSplit]
      have hl : 0 ≤ nullLambdaSeries m p / 6 :=
        div_nonneg (nullLambdaSeries_pos h).le (by norm_num)
      have hleft : 0 ≤ 1 / x + nullLambdaSeries m p / 6 * x ^ 2 := by
        positivity
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hexpEndpoint (Real.exp_pos _).le
      · exact add_le_add hone (mul_le_mul_of_nonneg_left htwo hl)
      · exact hleft
      · positivity
    _ = nullFirstEdgeworthComparatorOuterEnvelope m p t := by
      dsimp [a, x]
      unfold nullFirstEdgeworthComparatorOuterEnvelope
      ring

/-- Pointwise majorant valid on the whole large Esseen window. -/
theorem fourierQuotientError_null_firstEdgeworth_le_largeWindowEnvelope
    {m p : ℕ} (h : Admissible m p) (t : ℝ) :
    fourierQuotientError
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p) t ≤
      nullFirstEdgeworthGaussianEnvelope m p t +
        Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) /
          nullEdgeworthLocalCutoff m p +
        nullFirstEdgeworthComparatorOuterEnvelope m p t := by
  by_cases ht : |t| ≤ nullEdgeworthLocalCutoff m p
  · have hlocal :=
      fourierQuotientError_null_firstEdgeworth_le_gaussianEnvelope h (by
        simpa [nullEdgeworthLocalCutoff] using ht)
    exact hlocal.trans (by
      have hc : 0 ≤ Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) /
          nullEdgeworthLocalCutoff m p :=
        div_nonneg (Real.exp_pos _).le (nullEdgeworthLocalCutoff_pos h).le
      have he := nullFirstEdgeworthComparatorOuterEnvelope_nonneg h t
      linarith)
  · have houter : nullEdgeworthLocalCutoff m p ≤ |t| :=
      (le_of_not_ge ht)
    have ht0 : t ≠ 0 := by
      intro htzero
      subst t
      simp only [abs_zero] at houter
      linarith [nullEdgeworthLocalCutoff_pos h]
    have habs : 0 < |t| := abs_pos.mpr ht0
    have hactual := norm_charFun_standardizedNullLaw_le_at_localCutoff h houter
    have hactualDiv :
        ‖charFun (standardizedNullLaw m p) t‖ / |t| ≤
          Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) /
            nullEdgeworthLocalCutoff m p := by
      calc
        ‖charFun (standardizedNullLaw m p) t‖ / |t| ≤
            Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) / |t| :=
          div_le_div_of_nonneg_right hactual habs.le
        _ ≤ Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) /
            nullEdgeworthLocalCutoff m p := by
          exact div_le_div_of_nonneg_left (Real.exp_pos _).le
            (nullEdgeworthLocalCutoff_pos h) houter
    have hcomp := norm_nullFirstEdgeworthCharFun_div_abs_le_outerEnvelope h houter
    have htri : fourierQuotientError
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p) t ≤
        ‖charFun (standardizedNullLaw m p) t‖ / |t| +
          ‖nullFirstEdgeworthCharFun m p t‖ / |t| := by
      unfold fourierQuotientError
      rw [← add_div]
      exact div_le_div_of_nonneg_right (norm_sub_le _ _) (abs_nonneg t)
    exact htri.trans (by
      have hE := nullFirstEdgeworthGaussianEnvelope_nonneg h t
      linarith)

/-- Integrability of the weighted discrepancy on the large polynomial
window. -/
theorem integrableOn_fourierQuotientError_null_firstEdgeworth_largeWindow
    {m p : ℕ} (h : Admissible m p) :
    IntegrableOn
      (fourierQuotientError
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p))
      (Icc (-(nullEdgeworthSmoothingCutoff m p))
        (nullEdgeworthSmoothingCutoff m p)) := by
  letI : IsProbabilityMeasure (standardizedNullLaw m p) :=
    isProbabilityMeasure_standardizedNullLaw h.2
  let S : ℝ := nullEdgeworthSmoothingCutoff m p
  let E : ℝ → ℝ := nullFirstEdgeworthGaussianEnvelope m p
  let C : ℝ := Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) /
    nullEdgeworthLocalCutoff m p
  let H : ℝ → ℝ := nullFirstEdgeworthComparatorOuterEnvelope m p
  have hcomp : Continuous (nullFirstEdgeworthCharFun m p) := by
    unfold nullFirstEdgeworthCharFun nullCubicCharacteristicTerm
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fourierQuotientError
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p)) := by
    unfold fourierQuotientError
    exact ((continuous_charFun.sub hcomp).norm.measurable.div
      continuous_abs.measurable).aestronglyMeasurable
  have hconst : IntegrableOn (fun _t : ℝ ↦ C) (Icc (-S) S) :=
    integrableOn_const (by simp [Real.volume_Icc])
  have hmajor : IntegrableOn (fun t ↦ E t + C + H t) (Icc (-S) S) :=
    ((integrable_nullFirstEdgeworthGaussianEnvelope m p).integrableOn.add
      hconst).add
        (integrable_nullFirstEdgeworthComparatorOuterEnvelope h).integrableOn
  apply hmajor.mono' hmeas.restrict
  filter_upwards with t
  rw [Real.norm_eq_abs,
    abs_of_nonneg (fourierQuotientError_nonneg _ _ t)]
  simpa [E, C, H] using
    fourierQuotientError_null_firstEdgeworth_le_largeWindowEnvelope h t

/-- The complete weighted discrepancy on `[-Delta^4, Delta^4]`. -/
theorem truncatedFourierDiscrepancy_null_firstEdgeworth_largeWindow_le
    {m p : ℕ} (h : Admissible m p) :
    truncatedFourierDiscrepancy
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p)
        (nullEdgeworthSmoothingCutoff m p) ≤
      8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
        8 * nullLambdaSeries m p ^ 2 / 3 +
        8 * (nullAnalyticScale m p) ^ 3 *
          Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) +
        Real.exp (-((nullAnalyticScale m p) ^ 2 / 64)) *
          (64 / (nullAnalyticScale m p) ^ 2 +
            32 * nullLambdaSeries m p /
              (3 * nullAnalyticScale m p)) := by
  let S : ℝ := nullEdgeworthSmoothingCutoff m p
  let E : ℝ → ℝ := nullFirstEdgeworthGaussianEnvelope m p
  let C : ℝ := Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) /
    nullEdgeworthLocalCutoff m p
  let H : ℝ → ℝ := nullFirstEdgeworthComparatorOuterEnvelope m p
  have hS : 0 < S := by dsimp [S]; exact nullEdgeworthSmoothingCutoff_pos h
  have hE : Integrable E := by
    dsimp [E]
    exact integrable_nullFirstEdgeworthGaussianEnvelope m p
  have hH : Integrable H := by
    dsimp [H]
    exact integrable_nullFirstEdgeworthComparatorOuterEnvelope h
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (Real.exp_pos _).le (nullEdgeworthLocalCutoff_pos h).le
  have hconstInt : IntegrableOn (fun _t : ℝ ↦ C) (Icc (-S) S) :=
    integrableOn_const (by simp [Real.volume_Icc])
  have hmajor : IntegrableOn (fun t ↦ E t + C + H t) (Icc (-S) S) :=
    (hE.integrableOn.add hconstInt).add hH.integrableOn
  unfold truncatedFourierDiscrepancy
  calc
    (∫ t in Icc (-S) S,
        fourierQuotientError
          (charFun (standardizedNullLaw m p))
          (nullFirstEdgeworthCharFun m p) t) ≤
      ∫ t in Icc (-S) S, (E t + C + H t) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun t ↦
            fourierQuotientError_nonneg _ _ t
        · exact hmajor
        · filter_upwards with t
          simpa [E, C, H] using
            fourierQuotientError_null_firstEdgeworth_le_largeWindowEnvelope h t
    _ = (∫ t in Icc (-S) S, E t) +
        (∫ _t in Icc (-S) S, C) +
        (∫ t in Icc (-S) S, H t) := by
      rw [integral_add, integral_add]
      · exact hE.integrableOn
      · exact hconstInt
      · exact hE.integrableOn.add hconstInt
      · exact hH.integrableOn
    _ ≤ (∫ t : ℝ, E t) + 2 * S * C + (∫ t : ℝ, H t) := by
      have hEnonneg : 0 ≤ᵐ[volume] E :=
        Filter.Eventually.of_forall fun t ↦ by
          dsimp [E]
          exact nullFirstEdgeworthGaussianEnvelope_nonneg h t
      have hHnonneg : 0 ≤ᵐ[volume] H :=
        Filter.Eventually.of_forall fun t ↦ by
          dsimp [H]
          exact nullFirstEdgeworthComparatorOuterEnvelope_nonneg h t
      have hEset := setIntegral_le_integral hE hEnonneg (s := Icc (-S) S)
      have hHset := setIntegral_le_integral hH hHnonneg (s := Icc (-S) S)
      have hconst : (∫ _t in Icc (-S) S, C) = 2 * S * C := by
        rw [integral_const, measureReal_restrict_apply MeasurableSet.univ]
        simp only [univ_inter, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ S - -S), smul_eq_mul]
        ring
      rw [hconst]
      gcongr
    _ = 8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
        8 * nullLambdaSeries m p ^ 2 / 3 +
        8 * (nullAnalyticScale m p) ^ 3 *
          Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) +
        Real.exp (-((nullAnalyticScale m p) ^ 2 / 64)) *
          (64 / (nullAnalyticScale m p) ^ 2 +
            32 * nullLambdaSeries m p /
              (3 * nullAnalyticScale m p)) := by
      rw [show (∫ t : ℝ, E t) =
          8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
            8 * nullLambdaSeries m p ^ 2 / 3 by
        dsimp [E]
        exact integral_nullFirstEdgeworthGaussianEnvelope m p]
      rw [show (∫ t : ℝ, H t) =
          Real.exp (-((nullEdgeworthLocalCutoff m p) ^ 2 / 4)) *
            (4 / (nullEdgeworthLocalCutoff m p) ^ 2 +
              8 * nullLambdaSeries m p /
                (3 * nullEdgeworthLocalCutoff m p)) by
        dsimp [H]
        exact integral_nullFirstEdgeworthComparatorOuterEnvelope h]
      dsimp [S, C, nullEdgeworthSmoothingCutoff,
        nullEdgeworthLocalCutoff]
      have hD := (nullAnalyticScale_pos h).ne'
      field_simp [hD]
      ring_nf

/-! ## A relative Fourier remainder -/

/-- The finite large-window bound displayed by the preceding theorem. -/
def nullFirstEdgeworthLargeFourierBound (m p : ℕ) : ℝ :=
  8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
    8 * nullLambdaSeries m p ^ 2 / 3 +
    8 * (nullAnalyticScale m p) ^ 3 *
      Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) +
    Real.exp (-((nullAnalyticScale m p) ^ 2 / 64)) *
      (64 / (nullAnalyticScale m p) ^ 2 +
        32 * nullLambdaSeries m p /
          (3 * nullAnalyticScale m p))

/-- A dimensionless relative error.  All its terms tend to zero whenever
`Delta -> infinity` and `lambda -> 0`. -/
def nullFirstEdgeworthLargeFourierRatio (m p : ℕ) : ℝ :=
  8 / (9 * nullAnalyticScale m p) +
    8 * nullLambdaSeries m p / 3 +
    (64 / 3) * (nullAnalyticScale m p) ^ 6 *
      Real.exp (-((nullAnalyticScale m p) ^ 2 / 34)) +
    Real.exp (-((nullAnalyticScale m p) ^ 2 / 64)) *
      ((512 / 3) * nullAnalyticScale m p +
        32 / (3 * nullAnalyticScale m p))

theorem truncatedFourierDiscrepancy_null_firstEdgeworth_largeWindow_le_bound
    {m p : ℕ} (h : Admissible m p) :
    truncatedFourierDiscrepancy
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p)
        (nullEdgeworthSmoothingCutoff m p) ≤
      nullFirstEdgeworthLargeFourierBound m p := by
  exact truncatedFourierDiscrepancy_null_firstEdgeworth_largeWindow_le h

/-- The universal lower scale `lambda Delta^3 >= 3/8` converts every
large-window tail into `lambda` times a vanishing relative error. -/
theorem nullFirstEdgeworthLargeFourierBound_le_lambda_mul_ratio
    {m p : ℕ} (h : Admissible m p) :
    nullFirstEdgeworthLargeFourierBound m p ≤
      nullLambdaSeries m p *
        nullFirstEdgeworthLargeFourierRatio m p := by
  let D : ℝ := nullAnalyticScale m p
  let lambda : ℝ := nullLambdaSeries m p
  have hD : 0 < D := by dsimp [D]; exact nullAnalyticScale_pos h
  have hlambda : 0 < lambda := by dsimp [lambda]; exact nullLambdaSeries_pos h
  have hlower : (3 / 8 : ℝ) ≤ lambda * D ^ 3 := by
    simpa [D, lambda] using
      three_eighths_le_nullLambdaSeries_mul_analyticScale_cube h
  have hactual :
      8 * D ^ 3 * Real.exp (-(D ^ 2 / 34)) ≤
        lambda * ((64 / 3) * D ^ 6 * Real.exp (-(D ^ 2 / 34))) := by
    have hmul := mul_le_mul_of_nonneg_right hlower
      (show 0 ≤ (64 / 3 : ℝ) * D ^ 3 *
        Real.exp (-(D ^ 2 / 34)) by positivity)
    nlinarith [hmul]
  have hcompFirst :
      Real.exp (-(D ^ 2 / 64)) * (64 / D ^ 2) ≤
        lambda * (Real.exp (-(D ^ 2 / 64)) * ((512 / 3) * D)) := by
    have hmul := mul_le_mul_of_nonneg_right hlower
      (show 0 ≤ (512 / 3 : ℝ) * Real.exp (-(D ^ 2 / 64)) /
        D ^ 2 by positivity)
    field_simp [hD.ne'] at hmul ⊢
    nlinarith [hmul]
  have hcompSecond :
      Real.exp (-(D ^ 2 / 64)) * (32 * lambda / (3 * D)) =
        lambda * (Real.exp (-(D ^ 2 / 64)) * (32 / (3 * D))) := by ring
  dsimp [nullFirstEdgeworthLargeFourierBound,
    nullFirstEdgeworthLargeFourierRatio, D, lambda]
  dsimp [D, lambda] at hactual hcompFirst hcompSecond
  calc
    8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
          8 * nullLambdaSeries m p ^ 2 / 3 +
          8 * nullAnalyticScale m p ^ 3 *
              Real.exp (-(nullAnalyticScale m p ^ 2 / 34)) +
          Real.exp (-(nullAnalyticScale m p ^ 2 / 64)) *
            (64 / nullAnalyticScale m p ^ 2 +
              32 * nullLambdaSeries m p /
                (3 * nullAnalyticScale m p)) ≤
        8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
          8 * nullLambdaSeries m p ^ 2 / 3 +
          nullLambdaSeries m p *
            ((64 / 3) * nullAnalyticScale m p ^ 6 *
              Real.exp (-(nullAnalyticScale m p ^ 2 / 34))) +
          nullLambdaSeries m p *
            (Real.exp (-(nullAnalyticScale m p ^ 2 / 64)) *
              ((512 / 3) * nullAnalyticScale m p)) +
          nullLambdaSeries m p *
            (Real.exp (-(nullAnalyticScale m p ^ 2 / 64)) *
              (32 / (3 * nullAnalyticScale m p))) := by
      rw [mul_add]
      linarith [hactual, hcompFirst, hcompSecond]
    _ = nullLambdaSeries m p *
        (8 / (9 * nullAnalyticScale m p) +
          8 * nullLambdaSeries m p / 3 +
          64 / 3 * nullAnalyticScale m p ^ 6 *
            Real.exp (-(nullAnalyticScale m p ^ 2 / 34)) +
          Real.exp (-(nullAnalyticScale m p ^ 2 / 64)) *
            (512 / 3 * nullAnalyticScale m p +
              32 / (3 * nullAnalyticScale m p))) := by ring

theorem tendsto_pow_six_mul_exp_neg_sq_div_34 :
    Tendsto (fun x : ℝ ↦ x ^ 6 * Real.exp (-(x ^ 2 / 34)))
      atTop (nhds 0) := by
  have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (a := (1 / 34 : ℝ)) (by norm_num) (6 : ℝ)).mono_left
      atTop_le_cocompact
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [abs_of_pos hx]
  rw [show x ^ (6 : ℝ) = x ^ 6 by exact Real.rpow_natCast x 6]
  rw [show -(1 / 34 : ℝ) * x ^ 2 = -(x ^ 2 / 34) by ring]

theorem tendsto_mul_exp_neg_sq_div_64 :
    Tendsto (fun x : ℝ ↦ x * Real.exp (-(x ^ 2 / 64)))
      atTop (nhds 0) := by
  have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (a := (1 / 64 : ℝ)) (by norm_num) (1 : ℝ)).mono_left
      atTop_le_cocompact
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [abs_of_pos hx, Real.rpow_one]
  rw [show -(1 / 64 : ℝ) * x ^ 2 = -(x ^ 2 / 64) by ring]

theorem tendsto_exp_neg_sq_div_64_div :
    Tendsto (fun x : ℝ ↦ Real.exp (-(x ^ 2 / 64)) / x)
      atTop (nhds 0) := by
  have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (a := (1 / 64 : ℝ)) (by norm_num) (-1 : ℝ)).mono_left
      atTop_le_cocompact
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [abs_of_pos hx, Real.rpow_neg hx.le, Real.rpow_one]
  field_simp [hx.ne']

/-- The relative large-window Fourier error vanishes along every eventually
admissible triangular sequence, including the hard edge `m(p)=p`. -/
theorem tendsto_nullFirstEdgeworthLargeFourierRatio_zero_of_eventually_admissible
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ nullFirstEdgeworthLargeFourierRatio (m p) p)
      atTop (nhds 0) := by
  let D : ℕ → ℝ := fun p ↦ nullAnalyticScale (m p) p
  let lambda : ℕ → ℝ := fun p ↦ nullLambdaSeries (m p) p
  have hD : Tendsto D atTop atTop := by
    dsimp [D]
    exact tendsto_nullAnalyticScale_atTop_of_eventually_admissible m hadm
  have hlambda : Tendsto lambda atTop (nhds 0) := by
    dsimp [lambda]
    exact tendsto_nullLambdaSeries_zero_of_eventually_admissible m hadm
  have hinv : Tendsto (fun p ↦ 1 / D p) atTop (nhds 0) :=
    hD.const_div_atTop 1
  have h6 : Tendsto
      (fun p ↦ D p ^ 6 * Real.exp (-(D p ^ 2 / 34)))
      atTop (nhds 0) := tendsto_pow_six_mul_exp_neg_sq_div_34.comp hD
  have h1 : Tendsto
      (fun p ↦ D p * Real.exp (-(D p ^ 2 / 64)))
      atTop (nhds 0) := tendsto_mul_exp_neg_sq_div_64.comp hD
  have hm1 : Tendsto
      (fun p ↦ Real.exp (-(D p ^ 2 / 64)) / D p)
      atTop (nhds 0) := tendsto_exp_neg_sq_div_64_div.comp hD
  have hsum :=
    ((hinv.const_mul (8 / 9 : ℝ)).add
      (hlambda.const_mul (8 / 3 : ℝ))).add
      ((h6.const_mul (64 / 3 : ℝ)).add
        ((h1.const_mul (512 / 3 : ℝ)).add
          (hm1.const_mul (32 / 3 : ℝ))))
  convert hsum using 1
  · funext p
    simp only [D, lambda, nullFirstEdgeworthLargeFourierRatio]
    ring
  · norm_num

end

end LogdetLean
