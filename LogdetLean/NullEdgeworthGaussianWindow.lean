import LogdetLean.NullFirstEdgeworthFourier
import Mathlib.MeasureTheory.Integral.Gamma
/-!
# Gaussian-weighted first-Edgeworth error on the quarter analytic window

The generic local Taylor estimate in `NullFirstEdgeworthFourier` is sharpened
here on `|t| <= Delta/4`.  The scale-separation inequality
`lambda * Delta <= 3` makes the full logarithmic correction at most `t^2/6`.
Consequently exponentiating the logarithm loses only part of the Gaussian
factor, rather than an uncontrolled exponential in `|t|^3`.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

noncomputable section

set_option linter.style.haveILetI false

/-- On the quarter analytic window, the order-four logarithmic tail is at
most `2 lambda |t|^4 / (9 Delta)`. -/
theorem norm_nullHigherCharacteristicRemainder_le_quarter_scale
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| ≤ nullAnalyticScale m p / 4) :
    ‖nullHigherCharacteristicRemainder m p t‖ ≤
      2 * nullLambdaSeries m p * |t| ^ 4 /
        (9 * nullAnalyticScale m p) := by
  let x : ℝ := |t|
  let lambda : ℝ := nullLambdaSeries m p
  let Delta : ℝ := nullAnalyticScale m p
  have hDelta : 0 < Delta := by
    dsimp [Delta]
    exact nullAnalyticScale_pos h
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxquarter : x ≤ Delta / 4 := by simpa [x, Delta] using ht
  have hxDelta : x < Delta := by linarith
  have hratio : x / Delta ≤ 1 / 4 := by
    rw [div_le_iff₀ hDelta]
    linarith
  have hden : (3 / 4 : ℝ) ≤ 1 - x / Delta := by linarith
  have hdenpos : 0 < 1 - x / Delta := by linarith
  have hdenOrder : (9 / 2 : ℝ) * Delta ≤
      6 * Delta * (1 - x / Delta) := by
    calc
      (9 / 2 : ℝ) * Delta = 6 * Delta * (3 / 4) := by ring
      _ ≤ 6 * Delta * (1 - x / Delta) := by gcongr
  have hbase := norm_nullHigherCharacteristicRemainder_le h
    (t := t) (by simpa [x, Delta] using hxDelta)
  change ‖nullHigherCharacteristicRemainder m p t‖ ≤ _
  calc
    ‖nullHigherCharacteristicRemainder m p t‖ ≤
        lambda * x ^ 4 /
          (6 * Delta * (1 - x / Delta)) := by
      simpa [lambda, x, Delta] using hbase
    _ ≤ lambda * x ^ 4 / ((9 / 2) * Delta) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by dsimp [lambda]; exact (nullLambdaSeries_pos h).le)
          (pow_nonneg hx 4))
        (mul_pos (by norm_num) hDelta) hdenOrder
    _ = 2 * lambda * x ^ 4 / (9 * Delta) := by
      field_simp [hDelta.ne']
    _ = 2 * nullLambdaSeries m p * |t| ^ 4 /
        (9 * nullAnalyticScale m p) := by rfl

/-- The complete cubic-plus-higher logarithmic correction is at most
`|t|^2/6` on the quarter analytic window. -/
theorem norm_nullCubic_add_higher_le_quarter_scale
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| ≤ nullAnalyticScale m p / 4) :
    ‖nullCubicCharacteristicTerm m p t +
        nullHigherCharacteristicRemainder m p t‖ ≤ |t| ^ 2 / 6 := by
  let x : ℝ := |t|
  let lambda : ℝ := nullLambdaSeries m p
  let Delta : ℝ := nullAnalyticScale m p
  have hDelta : 0 < Delta := by
    dsimp [Delta]
    exact nullAnalyticScale_pos h
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact nullLambdaSeries_pos h
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxquarter : x ≤ Delta / 4 := by simpa [x, Delta] using ht
  have hratio : x / Delta ≤ 1 / 4 := by
    rw [div_le_iff₀ hDelta]
    linarith
  have htail := norm_nullHigherCharacteristicRemainder_le_quarter_scale h ht
  have htailSmall :
      ‖nullHigherCharacteristicRemainder m p t‖ ≤ lambda * x ^ 3 / 18 := by
    calc
      ‖nullHigherCharacteristicRemainder m p t‖ ≤
          2 * lambda * x ^ 4 / (9 * Delta) := by
        simpa [lambda, x, Delta] using htail
      _ = (2 * lambda * x ^ 3 / 9) * (x / Delta) := by
        field_simp [hDelta.ne']
      _ ≤ (2 * lambda * x ^ 3 / 9) * (1 / 4) := by
        exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = lambda * x ^ 3 / 18 := by ring
  have hlogCubic :
      ‖nullCubicCharacteristicTerm m p t‖ = lambda * x ^ 3 / 6 := by
    simpa [lambda, x] using norm_nullCubicCharacteristicTerm h t
  have hlog :
      ‖nullCubicCharacteristicTerm m p t +
          nullHigherCharacteristicRemainder m p t‖ ≤
        2 * lambda * x ^ 3 / 9 := by
    calc
      ‖nullCubicCharacteristicTerm m p t +
          nullHigherCharacteristicRemainder m p t‖ ≤
        ‖nullCubicCharacteristicTerm m p t‖ +
          ‖nullHigherCharacteristicRemainder m p t‖ := norm_add_le _ _
      _ ≤ lambda * x ^ 3 / 6 + lambda * x ^ 3 / 18 := by
        rw [hlogCubic]
        gcongr
      _ = 2 * lambda * x ^ 3 / 9 := by ring
  have hlambdaDelta : lambda * Delta ≤ 3 := by
    simpa [lambda, Delta] using
      nullLambdaSeries_mul_analyticScale_le_three h
  have hlambdax : lambda * x ≤ 3 / 4 := by
    calc
      lambda * x ≤ lambda * (Delta / 4) := by gcongr
      _ = (lambda * Delta) / 4 := by ring
      _ ≤ 3 / 4 := by gcongr
  change ‖nullCubicCharacteristicTerm m p t +
      nullHigherCharacteristicRemainder m p t‖ ≤ _
  calc
    ‖nullCubicCharacteristicTerm m p t +
        nullHigherCharacteristicRemainder m p t‖ ≤
      2 * lambda * x ^ 3 / 9 := hlog
    _ = x ^ 2 * (2 * (lambda * x) / 9) := by ring
    _ ≤ x ^ 2 * (1 / 6) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
      linarith
    _ = |t| ^ 2 / 6 := by dsimp [x]; ring

/-- Gaussian-weighted first-Edgeworth error on `|t| <= Delta/4`.

The two summands respectively come from the order-four logarithmic tail and
the quadratic error in exponentiating the cubic logarithm. -/
theorem norm_charFun_sub_firstEdgeworth_le_gaussian_quarter_scale
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| ≤ nullAnalyticScale m p / 4) :
    ‖charFun (standardizedNullLaw m p) t -
        nullFirstEdgeworthCharFun m p t‖ ≤
      (2 * nullLambdaSeries m p /
          (9 * nullAnalyticScale m p)) * |t| ^ 4 *
            Real.exp (-(t ^ 2 / 2)) +
        (4 * nullLambdaSeries m p ^ 2 / 81) * |t| ^ 6 *
            Real.exp (-(t ^ 2 / 3)) := by
  let x : ℝ := |t|
  let lambda : ℝ := nullLambdaSeries m p
  let Delta : ℝ := nullAnalyticScale m p
  let H : ℝ := lambda * x ^ 4 /
    (6 * Delta * (1 - x / Delta))
  let B : ℝ := lambda * x ^ 3 / 6 + H
  have hDelta : 0 < Delta := by
    dsimp [Delta]
    exact nullAnalyticScale_pos h
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact nullLambdaSeries_pos h
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxquarter : x ≤ Delta / 4 := by simpa [x, Delta] using ht
  have hxDelta : x < Delta := by linarith
  have hden : 0 < 1 - x / Delta :=
    sub_pos.mpr ((div_lt_one hDelta).2 hxDelta)
  have hH : 0 ≤ H := by
    dsimp [H]
    positivity
  have hHbound : H ≤ 2 * lambda * x ^ 4 / (9 * Delta) := by
    have htail := norm_nullHigherCharacteristicRemainder_le_quarter_scale h ht
    have hraw := norm_nullHigherCharacteristicRemainder_le h
      (t := t) (by simpa [x, Delta] using hxDelta)
    -- Both bounds have the same exact Taylor majorant on their left.  The
    -- denominator comparison used in the quarter-scale lemma therefore also
    -- bounds `H` itself.
    have hratio : x / Delta ≤ 1 / 4 := by
      rw [div_le_iff₀ hDelta]
      linarith
    have hdenLower : (3 / 4 : ℝ) ≤ 1 - x / Delta := by linarith
    have hdenOrder : (9 / 2 : ℝ) * Delta ≤
        6 * Delta * (1 - x / Delta) := by
      calc
        (9 / 2 : ℝ) * Delta = 6 * Delta * (3 / 4) := by ring
        _ ≤ 6 * Delta * (1 - x / Delta) := by gcongr
    dsimp [H]
    calc
      lambda * x ^ 4 / (6 * Delta * (1 - x / Delta)) ≤
          lambda * x ^ 4 / ((9 / 2) * Delta) := by
        exact div_le_div_of_nonneg_left (by positivity)
          (mul_pos (by norm_num) hDelta) hdenOrder
      _ = 2 * lambda * x ^ 4 / (9 * Delta) := by
        field_simp [hDelta.ne']
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBbound : B ≤ 2 * lambda * x ^ 3 / 9 := by
    have hratio : x / Delta ≤ 1 / 4 := by
      rw [div_le_iff₀ hDelta]
      linarith
    have hHsmall : H ≤ lambda * x ^ 3 / 18 := by
      calc
        H ≤ 2 * lambda * x ^ 4 / (9 * Delta) := hHbound
        _ = (2 * lambda * x ^ 3 / 9) * (x / Delta) := by
          field_simp [hDelta.ne']
        _ ≤ (2 * lambda * x ^ 3 / 9) * (1 / 4) := by
          exact mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = lambda * x ^ 3 / 18 := by ring
    dsimp [B]
    calc
      lambda * x ^ 3 / 6 + H ≤
          lambda * x ^ 3 / 6 + lambda * x ^ 3 / 18 := by gcongr
      _ = 2 * lambda * x ^ 3 / 9 := by ring
  have hBquad : B ≤ x ^ 2 / 6 := by
    have hlambdaDelta : lambda * Delta ≤ 3 := by
      simpa [lambda, Delta] using
        nullLambdaSeries_mul_analyticScale_le_three h
    have hlambdax : lambda * x ≤ 3 / 4 := by
      calc
        lambda * x ≤ lambda * (Delta / 4) := by gcongr
        _ = (lambda * Delta) / 4 := by ring
        _ ≤ 3 / 4 := by gcongr
    calc
      B ≤ 2 * lambda * x ^ 3 / 9 := hBbound
      _ = x ^ 2 * (2 * (lambda * x) / 9) := by ring
      _ ≤ x ^ 2 * (1 / 6) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
        linarith
      _ = x ^ 2 / 6 := by ring
  have htSquare : t ^ 2 = x ^ 2 := by
    dsimp [x]
    exact (sq_abs t).symm
  have hpoint := norm_charFun_standardizedNullLaw_sub_firstEdgeworth_le h
    (t := t) (by simpa [x, Delta] using hxDelta)
  have hexpMono : Real.exp B ≤ Real.exp (x ^ 2 / 6) :=
    Real.exp_le_exp.mpr hBquad
  change ‖charFun (standardizedNullLaw m p) t -
      nullFirstEdgeworthCharFun m p t‖ ≤ _
  calc
    ‖charFun (standardizedNullLaw m p) t -
        nullFirstEdgeworthCharFun m p t‖ ≤
      Real.exp (-(t ^ 2 / 2)) * (H + B ^ 2 * Real.exp B) := by
        simpa [lambda, x, Delta, H, B] using hpoint
    _ ≤ Real.exp (-(t ^ 2 / 2)) *
        (2 * lambda * x ^ 4 / (9 * Delta) +
          (2 * lambda * x ^ 3 / 9) ^ 2 * Real.exp (x ^ 2 / 6)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact add_le_add hHbound (by gcongr)
    _ = (2 * lambda / (9 * Delta)) * x ^ 4 *
          Real.exp (-(t ^ 2 / 2)) +
        (4 * lambda ^ 2 / 81) * x ^ 6 *
          Real.exp (-(t ^ 2 / 3)) := by
      rw [htSquare]
      have hexp : Real.exp (-(x ^ 2 / 2)) * Real.exp (x ^ 2 / 6) =
          Real.exp (-(x ^ 2 / 3)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (-(x ^ 2 / 2)) *
            (2 * lambda * x ^ 4 / (9 * Delta) +
              (2 * lambda * x ^ 3 / 9) ^ 2 * Real.exp (x ^ 2 / 6)) =
          Real.exp (-(x ^ 2 / 2)) *
              (2 * lambda * x ^ 4 / (9 * Delta)) +
            (2 * lambda * x ^ 3 / 9) ^ 2 *
              (Real.exp (-(x ^ 2 / 2)) * Real.exp (x ^ 2 / 6)) := by ring
        _ = _ := by rw [hexp]; ring
    _ = (2 * nullLambdaSeries m p /
          (9 * nullAnalyticScale m p)) * |t| ^ 4 *
            Real.exp (-(t ^ 2 / 2)) +
        (4 * nullLambdaSeries m p ^ 2 / 81) * |t| ^ 6 *
            Real.exp (-(t ^ 2 / 3)) := by rfl

/-! ## Exact Gaussian moment integrals -/

theorem integrable_abs_cube_mul_exp_neg_sq_half :
    Integrable (fun t : ℝ => |t| ^ 3 * Real.exp (-(t ^ 2 / 2))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (by norm_num) (s := (3 : ℝ)) (by norm_num)
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  simp only [Real.rpow_ofNat]
  rw [norm_mul, norm_pow, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [show -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2 / 2) by ring]

theorem integral_abs_cube_mul_exp_neg_sq_half :
    (∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 / 2))) = 4 := by
  let f : ℝ → ℝ := fun x => x ^ 3 * Real.exp (-(x ^ 2 / 2))
  have hf : (fun t : ℝ => |t| ^ 3 * Real.exp (-(t ^ 2 / 2))) =
      fun t => f |t| := by
    funext t
    simp only [f, sq_abs]
  rw [hf, integral_comp_abs]
  have hI := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (3 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hI' : (∫ x in Ioi (0 : ℝ), f x) = 2 := by
    rw [show (∫ x in Ioi (0 : ℝ), f x) =
        ∫ x in Ioi (0 : ℝ), x ^ (3 : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      simp only [f]
      rw [show -(x ^ 2 / 2) = -(1 / 2 : ℝ) * x ^ 2 by ring]
      simp only [Real.rpow_ofNat]]
    rw [hI]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [hI']
  norm_num

theorem integrable_abs_fifth_mul_exp_neg_sq_third :
    Integrable (fun t : ℝ => |t| ^ 5 * Real.exp (-(t ^ 2 / 3))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 3 : ℝ)) (by norm_num) (s := (5 : ℝ)) (by norm_num)
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  simp only [Real.rpow_ofNat]
  rw [norm_mul, norm_pow, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [show -(1 / 3 : ℝ) * x ^ 2 = -(x ^ 2 / 3) by ring]

theorem integral_abs_fifth_mul_exp_neg_sq_third :
    (∫ t : ℝ, |t| ^ 5 * Real.exp (-(t ^ 2 / 3))) = 54 := by
  let f : ℝ → ℝ := fun x => x ^ 5 * Real.exp (-(x ^ 2 / 3))
  have hf : (fun t : ℝ => |t| ^ 5 * Real.exp (-(t ^ 2 / 3))) =
      fun t => f |t| := by
    funext t
    simp only [f, sq_abs]
  rw [hf, integral_comp_abs]
  have hI := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (5 : ℝ)) (b := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hI' : (∫ x in Ioi (0 : ℝ), f x) = 27 := by
    rw [show (∫ x in Ioi (0 : ℝ), f x) =
        ∫ x in Ioi (0 : ℝ), x ^ (5 : ℝ) *
          Real.exp (-(1 / 3 : ℝ) * x ^ (2 : ℝ)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      simp only [f]
      rw [show -(x ^ 2 / 3) = -(1 / 3 : ℝ) * x ^ 2 by ring]
      simp only [Real.rpow_ofNat]]
    rw [hI]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [hI']
  norm_num

/-! ## Integrated low-frequency input -/

/-- An integrable majorant for the weighted Fourier error. -/
def nullFirstEdgeworthGaussianEnvelope (m p : ℕ) (t : ℝ) : ℝ :=
  (2 * nullLambdaSeries m p / (9 * nullAnalyticScale m p)) *
      |t| ^ 3 * Real.exp (-(t ^ 2 / 2)) +
    (4 * nullLambdaSeries m p ^ 2 / 81) *
      |t| ^ 5 * Real.exp (-(t ^ 2 / 3))

theorem nullFirstEdgeworthGaussianEnvelope_nonneg
    {m p : ℕ} (h : Admissible m p) (t : ℝ) :
    0 ≤ nullFirstEdgeworthGaussianEnvelope m p t := by
  unfold nullFirstEdgeworthGaussianEnvelope
  have hDelta := nullAnalyticScale_pos h
  have hlambda := nullLambdaSeries_pos h
  positivity

theorem integrable_nullFirstEdgeworthGaussianEnvelope
    (m p : ℕ) :
    Integrable (nullFirstEdgeworthGaussianEnvelope m p) := by
  unfold nullFirstEdgeworthGaussianEnvelope
  have h3 : Integrable (fun t : ℝ =>
      (2 * nullLambdaSeries m p / (9 * nullAnalyticScale m p)) *
        |t| ^ 3 * Real.exp (-(t ^ 2 / 2))) := by
    simpa only [mul_assoc] using
      integrable_abs_cube_mul_exp_neg_sq_half.const_mul
        (2 * nullLambdaSeries m p / (9 * nullAnalyticScale m p))
  have h5 : Integrable (fun t : ℝ =>
      (4 * nullLambdaSeries m p ^ 2 / 81) *
        |t| ^ 5 * Real.exp (-(t ^ 2 / 3))) := by
    simpa only [mul_assoc] using
      integrable_abs_fifth_mul_exp_neg_sq_third.const_mul
        (4 * nullLambdaSeries m p ^ 2 / 81)
  exact h3.add h5

theorem integral_nullFirstEdgeworthGaussianEnvelope
    (m p : ℕ) :
    (∫ t : ℝ, nullFirstEdgeworthGaussianEnvelope m p t) =
      8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
        8 * nullLambdaSeries m p ^ 2 / 3 := by
  unfold nullFirstEdgeworthGaussianEnvelope
  have hrewrite : (fun t : ℝ =>
      2 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) *
          |t| ^ 3 * Real.exp (-(t ^ 2 / 2)) +
        4 * nullLambdaSeries m p ^ 2 / 81 *
          |t| ^ 5 * Real.exp (-(t ^ 2 / 3))) =
      (fun t : ℝ =>
        (2 * nullLambdaSeries m p / (9 * nullAnalyticScale m p)) *
            (|t| ^ 3 * Real.exp (-(t ^ 2 / 2))) +
          (4 * nullLambdaSeries m p ^ 2 / 81) *
            (|t| ^ 5 * Real.exp (-(t ^ 2 / 3)))) := by
    funext t
    ring
  rw [hrewrite]
  rw [integral_add
    (integrable_abs_cube_mul_exp_neg_sq_half.const_mul _)
    (integrable_abs_fifth_mul_exp_neg_sq_third.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_abs_cube_mul_exp_neg_sq_half,
    integral_abs_fifth_mul_exp_neg_sq_third]
  ring

/-- Pointwise domination of the Esseen quotient on the quarter analytic
window. -/
theorem fourierQuotientError_null_firstEdgeworth_le_gaussianEnvelope
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| ≤ nullAnalyticScale m p / 4) :
    fourierQuotientError
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p) t ≤
      nullFirstEdgeworthGaussianEnvelope m p t := by
  by_cases ht0 : t = 0
  · subst t
    simp only [fourierQuotientError, abs_zero, div_zero]
    exact nullFirstEdgeworthGaussianEnvelope_nonneg h 0
  · have habs : 0 < |t| := abs_pos.mpr ht0
    have hpoint :=
      norm_charFun_sub_firstEdgeworth_le_gaussian_quarter_scale h ht
    unfold fourierQuotientError
    rw [div_le_iff₀ habs]
    calc
      ‖charFun (standardizedNullLaw m p) t -
          nullFirstEdgeworthCharFun m p t‖ ≤
        (2 * nullLambdaSeries m p /
            (9 * nullAnalyticScale m p)) * |t| ^ 4 *
              Real.exp (-(t ^ 2 / 2)) +
          (4 * nullLambdaSeries m p ^ 2 / 81) * |t| ^ 6 *
              Real.exp (-(t ^ 2 / 3)) := hpoint
      _ = nullFirstEdgeworthGaussianEnvelope m p t * |t| := by
        unfold nullFirstEdgeworthGaussianEnvelope
        ring

/-- The Esseen quotient is integrable on the quarter analytic window. -/
theorem integrableOn_fourierQuotientError_null_firstEdgeworth_quarter_scale
    {m p : ℕ} (h : Admissible m p) :
    IntegrableOn
      (fourierQuotientError
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p))
      (Icc (-(nullAnalyticScale m p / 4))
        (nullAnalyticScale m p / 4)) := by
  letI : IsProbabilityMeasure (standardizedNullLaw m p) :=
    isProbabilityMeasure_standardizedNullLaw h.2
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
  apply Integrable.mono'
    (integrable_nullFirstEdgeworthGaussianEnvelope m p).integrableOn
    hmeas.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs,
    abs_of_nonneg (fourierQuotientError_nonneg _ _ _)]
  apply fourierQuotientError_null_firstEdgeworth_le_gaussianEnvelope h
  rw [abs_le]
  exact ⟨by linarith [ht.1], ht.2⟩

/-- Explicit Gaussian-weighted low-frequency Fourier estimate.  Unlike the
coarser polynomial estimate, its right side contains no positive power of the
cutoff. -/
theorem truncatedFourierDiscrepancy_null_firstEdgeworth_quarter_scale_le
    {m p : ℕ} (h : Admissible m p) :
    truncatedFourierDiscrepancy
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p)
        (nullAnalyticScale m p / 4) ≤
      8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
        8 * nullLambdaSeries m p ^ 2 / 3 := by
  let T : ℝ := nullAnalyticScale m p / 4
  let E : ℝ → ℝ := nullFirstEdgeworthGaussianEnvelope m p
  have hEint : Integrable E := by
    dsimp [E]
    exact integrable_nullFirstEdgeworthGaussianEnvelope m p
  have hEnonneg : 0 ≤ᵐ[volume] E :=
    Filter.Eventually.of_forall fun t => by
      dsimp [E]
      exact nullFirstEdgeworthGaussianEnvelope_nonneg h t
  unfold truncatedFourierDiscrepancy
  calc
    (∫ t in Icc (-T) T,
        fourierQuotientError
          (charFun (standardizedNullLaw m p))
          (nullFirstEdgeworthCharFun m p) t) ≤
      ∫ t in Icc (-T) T, E t := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun t =>
            fourierQuotientError_nonneg _ _ t
        · exact hEint.integrableOn
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          apply fourierQuotientError_null_firstEdgeworth_le_gaussianEnvelope h
          dsimp [T] at ht ⊢
          rw [abs_le]
          exact ⟨by linarith [ht.1], ht.2⟩
    _ ≤ ∫ t : ℝ, E t := setIntegral_le_integral hEint hEnonneg
    _ = 8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
        8 * nullLambdaSeries m p ^ 2 / 3 := by
      dsimp [E]
      exact integral_nullFirstEdgeworthGaussianEnvelope m p

end

end LogdetLean
