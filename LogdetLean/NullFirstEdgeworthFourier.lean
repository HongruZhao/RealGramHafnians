import LogdetLean.NullGlobalPolynomial
import LogdetLean.NullLocalCharacteristic
import LogdetLean.QuantitativeFourier
import LogdetLean.SignedEdgeworthComparator
/-!
# Model-specific Fourier input for the first null Edgeworth comparator

This module separates the cubic cumulant from the exact analytic logarithm,
bounds the order-four-and-higher remainder, and transfers the result to the
weighted characteristic-function discrepancy used in Esseen smoothing.
No CDF smoothing theorem is assumed here.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

noncomputable section

set_option linter.style.haveILetI false

/-- The standardized order-three cumulant magnitude is exactly `lambda`. -/
theorem nullStandardizedCumulantMagnitudeSeries_three_eq_lambda
    {m p : ℕ} (h : Admissible m p) :
    nullStandardizedCumulantMagnitudeSeries 3 m p =
      nullLambdaSeries m p := by
  unfold nullStandardizedCumulantMagnitudeSeries nullLambdaSeries
  rw [nullCumulantMagnitudeSeries_three h,
    nullVSeries_rpow_three_halves h]

/-- The exact cubic Taylor coefficient is `-lambda/6`. -/
theorem nullStandardizedCgfTaylorCoeff_three
    {m p : ℕ} (h : Admissible m p) :
    nullStandardizedCgfTaylorCoeff 3 m p =
      -nullLambdaSeries m p / 6 := by
  rw [nullStandardizedCgfTaylorCoeff_eq_sign_mul_magnitude_div_factorial
    (by norm_num) h,
    nullStandardizedCumulantMagnitudeSeries_three_eq_lambda h]
  norm_num

/-- Terms of order four and higher in the exact complex CGF. -/
def nullComplexCgfHigherTail (m p : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ,
    (nullStandardizedCgfTaylorCoeff (n + 4) m p : ℂ) * z ^ (n + 4)

theorem summable_norm_nullComplexCgfHigherTail
    {m p : ℕ} (h : Admissible m p) {z : ℂ}
    (hz : ‖z‖ < nullAnalyticScale m p) :
    Summable (fun n : ℕ =>
      ‖(nullStandardizedCgfTaylorCoeff (n + 4) m p : ℂ) *
        z ^ (n + 4)‖) := by
  have htail := summable_norm_nullComplexCgfTaylorTail h hz
  have hshift := (summable_nat_add_iff 1).2 htail
  simpa [add_assoc] using hshift

/-- Exact split of the CGF tail into cubic and higher-order terms. -/
theorem nullComplexCgfTaylorTail_eq_cubic_add_higher
    {m p : ℕ} (h : Admissible m p) {z : ℂ}
    (hz : ‖z‖ < nullAnalyticScale m p) :
    nullComplexCgfTaylorTail m p z =
      (nullStandardizedCgfTaylorCoeff 3 m p : ℂ) * z ^ 3 +
        nullComplexCgfHigherTail m p z := by
  let f : ℕ → ℂ := fun n =>
    (nullStandardizedCgfTaylorCoeff (n + 3) m p : ℂ) * z ^ (n + 3)
  have hsum : Summable f := by
    apply Summable.of_norm
    simpa [f] using summable_norm_nullComplexCgfTaylorTail h hz
  have hsplit := hsum.sum_add_tsum_nat_add 1
  unfold nullComplexCgfTaylorTail nullComplexCgfHigherTail
  change (∑' n : ℕ, f n) = _
  rw [← hsplit]
  simp [f, add_assoc]

/-- Geometric order-four bound for the higher logarithmic remainder. -/
theorem norm_nullComplexCgfHigherTail_le
    {m p : ℕ} (h : Admissible m p) {z : ℂ}
    (hz : ‖z‖ < nullAnalyticScale m p) :
    ‖nullComplexCgfHigherTail m p z‖ ≤
      nullLambdaSeries m p * ‖z‖ ^ 4 /
        (6 * nullAnalyticScale m p *
          (1 - ‖z‖ / nullAnalyticScale m p)) := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hq0 : 0 ≤ ‖z‖ / nullAnalyticScale m p := by positivity
  have hq1 : ‖z‖ / nullAnalyticScale m p < 1 :=
    (div_lt_one hDelta).2 hz
  have hsumNorm := summable_norm_nullComplexCgfHigherTail h hz
  have hgeom : Summable (fun n : ℕ =>
      (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
        (‖z‖ / nullAnalyticScale m p) ^ (n + 1)) := by
    have hs := (summable_geometric_of_lt_one hq0 hq1).mul_left
      (nullLambdaSeries m p * ‖z‖ ^ 3 / 6)
    exact (summable_nat_add_iff 1).2 hs
  unfold nullComplexCgfHigherTail
  calc
    ‖∑' n : ℕ,
        (nullStandardizedCgfTaylorCoeff (n + 4) m p : ℂ) *
          z ^ (n + 4)‖ ≤
      ∑' n : ℕ,
        ‖(nullStandardizedCgfTaylorCoeff (n + 4) m p : ℂ) *
          z ^ (n + 4)‖ := norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' n : ℕ,
        (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
          (‖z‖ / nullAnalyticScale m p) ^ (n + 1) :=
      hsumNorm.tsum_le_tsum (fun n => by
        simpa [add_assoc] using
          norm_nullComplexCgfTaylorTail_term_le h z (n + 1)) hgeom
    _ = (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
        ((‖z‖ / nullAnalyticScale m p) /
          (1 - ‖z‖ / nullAnalyticScale m p)) := by
      rw [show (fun n : ℕ =>
          (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
            (‖z‖ / nullAnalyticScale m p) ^ (n + 1)) =
        (fun n : ℕ =>
          ((nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
            (‖z‖ / nullAnalyticScale m p)) *
              (‖z‖ / nullAnalyticScale m p) ^ n) by
        funext n
        rw [pow_succ]
        ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      ring
    _ = nullLambdaSeries m p * ‖z‖ ^ 4 /
        (6 * nullAnalyticScale m p *
          (1 - ‖z‖ / nullAnalyticScale m p)) := by
      have hden : 1 - ‖z‖ / nullAnalyticScale m p ≠ 0 :=
        (sub_pos.mpr hq1).ne'
      field_simp [hDelta.ne', hden]

/-- Higher logarithmic remainder on the imaginary axis. -/
def nullHigherCharacteristicRemainder (m p : ℕ) (t : ℝ) : ℂ :=
  nullComplexCgfHigherTail m p ((t : ℂ) * Complex.I)

/-- Exact cubic term on the imaginary axis. -/
def nullCubicCharacteristicTerm (m p : ℕ) (t : ℝ) : ℂ :=
  (nullLambdaSeries m p * t ^ 3 / 6 : ℂ) * Complex.I

theorem cgf_cubic_term_on_imaginary_axis
    {m p : ℕ} (h : Admissible m p) (t : ℝ) :
    (nullStandardizedCgfTaylorCoeff 3 m p : ℂ) *
        ((t : ℂ) * Complex.I) ^ 3 =
      nullCubicCharacteristicTerm m p t := by
  rw [nullStandardizedCgfTaylorCoeff_three h]
  unfold nullCubicCharacteristicTerm
  push_cast
  rw [mul_pow, show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq, neg_one_mul]]
  ring

/-- Exact local characteristic exponent with the cubic term separated. -/
theorem charFun_standardizedNullLaw_eq_gaussian_cubic_higher
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| < nullAnalyticScale m p) :
    charFun (standardizedNullLaw m p) t =
      Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) *
        Complex.exp (nullCubicCharacteristicTerm m p t +
          nullHigherCharacteristicRemainder m p t) := by
  rw [charFun_standardizedNullLaw_eq_gaussian_cexp_remainder h ht]
  have hsplit := nullComplexCgfTaylorTail_eq_cubic_add_higher h
    (z := (t : ℂ) * Complex.I) (by
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using ht)
  unfold nullLocalCharacteristicRemainder
  rw [hsplit, cgf_cubic_term_on_imaginary_axis h]
  change Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ) +
      (nullCubicCharacteristicTerm m p t +
        nullHigherCharacteristicRemainder m p t)) = _
  rw [Complex.exp_add]

theorem norm_nullCubicCharacteristicTerm
    {m p : ℕ} (h : Admissible m p) (t : ℝ) :
    ‖nullCubicCharacteristicTerm m p t‖ =
      nullLambdaSeries m p * |t| ^ 3 / 6 := by
  unfold nullCubicCharacteristicTerm
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [abs_of_pos (nullLambdaSeries_pos h)]
  norm_num

theorem norm_nullHigherCharacteristicRemainder_le
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| < nullAnalyticScale m p) :
    ‖nullHigherCharacteristicRemainder m p t‖ ≤
      nullLambdaSeries m p * |t| ^ 4 /
        (6 * nullAnalyticScale m p *
          (1 - |t| / nullAnalyticScale m p)) := by
  unfold nullHigherCharacteristicRemainder
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    norm_nullComplexCgfHigherTail_le h
      (z := (t : ℂ) * Complex.I) (by
        simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using ht)

/-- Characteristic function paired with the signed first Edgeworth CDF
`signedFirstEdgeworthCDF (lambda/6)`. -/
def nullFirstEdgeworthCharFun (m p : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) *
    (1 + nullCubicCharacteristicTerm m p t)

/-- Explicit pointwise Fourier error after retaining the cubic term. -/
theorem norm_charFun_standardizedNullLaw_sub_firstEdgeworth_le
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| < nullAnalyticScale m p) :
    ‖charFun (standardizedNullLaw m p) t -
        nullFirstEdgeworthCharFun m p t‖ ≤
      Real.exp (-(t ^ 2 / 2)) *
        (nullLambdaSeries m p * |t| ^ 4 /
            (6 * nullAnalyticScale m p *
              (1 - |t| / nullAnalyticScale m p)) +
          (nullLambdaSeries m p * |t| ^ 3 / 6 +
            nullLambdaSeries m p * |t| ^ 4 /
              (6 * nullAnalyticScale m p *
                (1 - |t| / nullAnalyticScale m p))) ^ 2 *
            Real.exp
              (nullLambdaSeries m p * |t| ^ 3 / 6 +
                nullLambdaSeries m p * |t| ^ 4 /
                  (6 * nullAnalyticScale m p *
                    (1 - |t| / nullAnalyticScale m p)))) := by
  let c : ℂ := nullCubicCharacteristicTerm m p t
  let r : ℂ := nullHigherCharacteristicRemainder m p t
  let C : ℝ := nullLambdaSeries m p * |t| ^ 3 / 6
  let H : ℝ := nullLambdaSeries m p * |t| ^ 4 /
    (6 * nullAnalyticScale m p *
      (1 - |t| / nullAnalyticScale m p))
  have hden : 0 < 1 - |t| / nullAnalyticScale m p :=
    sub_pos.mpr ((div_lt_one (nullAnalyticScale_pos h)).2 ht)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (mul_nonneg (nullLambdaSeries_pos h).le (by positivity)) (by norm_num)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact div_nonneg
      (mul_nonneg (nullLambdaSeries_pos h).le (by positivity))
      (mul_nonneg
        (mul_nonneg (by norm_num) (nullAnalyticScale_pos h).le) hden.le)
  have hc : ‖c‖ = C := by
    dsimp [c, C]
    exact norm_nullCubicCharacteristicTerm h t
  have hr : ‖r‖ ≤ H := by
    dsimp [r, H]
    exact norm_nullHigherCharacteristicRemainder_le h ht
  have hcr : ‖c + r‖ ≤ C + H := by
    calc
      ‖c + r‖ ≤ ‖c‖ + ‖r‖ := norm_add_le _ _
      _ ≤ C + H := by rw [hc]; linarith
  have hexp : ‖Complex.exp (c + r) - (1 + (c + r))‖ ≤
      ‖c + r‖ ^ 2 * Real.exp ‖c + r‖ := by
    simpa [Finset.sum_range_succ] using
      Complex.norm_exp_sub_sum_le_norm_mul_exp (c + r) 2
  have hexpBound : ‖Complex.exp (c + r) - (1 + (c + r))‖ ≤
      (C + H) ^ 2 * Real.exp (C + H) := by
    exact hexp.trans (by gcongr)
  rw [charFun_standardizedNullLaw_eq_gaussian_cubic_higher h ht]
  unfold nullFirstEdgeworthCharFun
  change ‖Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) * Complex.exp (c + r) -
      Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) * (1 + c)‖ ≤ _
  rw [← mul_sub, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    ‖Complex.exp (c + r) - (1 + c)‖ =
        ‖(Complex.exp (c + r) - (1 + (c + r))) + r‖ := by
      congr 1
      ring
    _ ≤ ‖Complex.exp (c + r) - (1 + (c + r))‖ + ‖r‖ := norm_add_le _ _
    _ ≤ (C + H) ^ 2 * Real.exp (C + H) + H := by linarith
    _ = H + (C + H) ^ 2 * Real.exp (C + H) := by ring

/-! ## An explicit weighted low-frequency integral -/

/-- Uniform order-four coefficient for the higher logarithmic tail on
`|t| <= T`. -/
def nullHigherCutoffCoefficient (m p : ℕ) (T : ℝ) : ℝ :=
  nullLambdaSeries m p /
    (6 * nullAnalyticScale m p *
      (1 - T / nullAnalyticScale m p))

/-- Uniform coefficient in `|c(t)+r(t)| <= K |t|^3` on `|t| <= T`. -/
def nullLogCutoffCoefficient (m p : ℕ) (T : ℝ) : ℝ :=
  nullLambdaSeries m p / 6 + nullHigherCutoffCoefficient m p T * T

/-- Explicit order-four coefficient after exponentiating the cubic-plus-tail
logarithm. -/
def nullFirstEdgeworthFourierCoefficient (m p : ℕ) (T : ℝ) : ℝ :=
  nullHigherCutoffCoefficient m p T +
    (nullLogCutoffCoefficient m p T) ^ 2 * T ^ 2 *
      Real.exp (nullLogCutoffCoefficient m p T * T ^ 3)

theorem nullHigherCutoffCoefficient_nonneg
    {m p : ℕ} (h : Admissible m p) {T : ℝ}
    (_hT : 0 ≤ T) (hTD : T < nullAnalyticScale m p) :
    0 ≤ nullHigherCutoffCoefficient m p T := by
  unfold nullHigherCutoffCoefficient
  have hden : 0 < 1 - T / nullAnalyticScale m p :=
    sub_pos.mpr ((div_lt_one (nullAnalyticScale_pos h)).2 hTD)
  exact div_nonneg (nullLambdaSeries_pos h).le
    (mul_nonneg
      (mul_nonneg (by norm_num) (nullAnalyticScale_pos h).le) hden.le)

theorem nullLogCutoffCoefficient_nonneg
    {m p : ℕ} (h : Admissible m p) {T : ℝ}
    (hT : 0 ≤ T) (hTD : T < nullAnalyticScale m p) :
    0 ≤ nullLogCutoffCoefficient m p T := by
  unfold nullLogCutoffCoefficient
  exact add_nonneg (div_nonneg (nullLambdaSeries_pos h).le (by norm_num))
    (mul_nonneg (nullHigherCutoffCoefficient_nonneg h hT hTD) hT)

theorem nullFirstEdgeworthFourierCoefficient_nonneg
    {m p : ℕ} (h : Admissible m p) {T : ℝ}
    (hT : 0 ≤ T) (hTD : T < nullAnalyticScale m p) :
    0 ≤ nullFirstEdgeworthFourierCoefficient m p T := by
  unfold nullFirstEdgeworthFourierCoefficient
  exact add_nonneg (nullHigherCutoffCoefficient_nonneg h hT hTD)
    (mul_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.exp_pos _).le)

/-- Uniform order-four characteristic-function error on a strict subdisk. -/
theorem norm_charFun_sub_firstEdgeworth_le_cutoff_pow_four
    {m p : ℕ} (h : Admissible m p) {T t : ℝ}
    (hT : 0 ≤ T) (hTD : T < nullAnalyticScale m p)
    (ht : |t| ≤ T) :
    ‖charFun (standardizedNullLaw m p) t -
        nullFirstEdgeworthCharFun m p t‖ ≤
      nullFirstEdgeworthFourierCoefficient m p T * |t| ^ 4 := by
  let x : ℝ := |t|
  let A : ℝ := nullHigherCutoffCoefficient m p T
  let K : ℝ := nullLogCutoffCoefficient m p T
  let H : ℝ := nullLambdaSeries m p * x ^ 4 /
    (6 * nullAnalyticScale m p *
      (1 - x / nullAnalyticScale m p))
  let B : ℝ := nullLambdaSeries m p * x ^ 3 / 6 + H
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxT : x ≤ T := by simpa [x] using ht
  have hTDx : x < nullAnalyticScale m p := hxT.trans_lt hTD
  have hdenT : 0 < 1 - T / nullAnalyticScale m p :=
    sub_pos.mpr ((div_lt_one hDelta).2 hTD)
  have hdenx : 0 < 1 - x / nullAnalyticScale m p :=
    sub_pos.mpr ((div_lt_one hDelta).2 hTDx)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact nullHigherCutoffCoefficient_nonneg h hT hTD
  have hK : 0 ≤ K := by
    dsimp [K]
    exact nullLogCutoffCoefficient_nonneg h hT hTD
  have hH : 0 ≤ H := by
    dsimp [H]
    exact div_nonneg
      (mul_nonneg (nullLambdaSeries_pos h).le (pow_nonneg hx 4))
      (mul_nonneg
        (mul_nonneg (by norm_num) hDelta.le) hdenx.le)
  have hdenOrder :
      6 * nullAnalyticScale m p *
          (1 - T / nullAnalyticScale m p) ≤
        6 * nullAnalyticScale m p *
          (1 - x / nullAnalyticScale m p) := by
    have : x / nullAnalyticScale m p ≤
        T / nullAnalyticScale m p :=
      div_le_div_of_nonneg_right hxT hDelta.le
    gcongr
  have hHA : H ≤ A * x ^ 4 := by
    dsimp [H, A, nullHigherCutoffCoefficient]
    have hnum : 0 ≤ nullLambdaSeries m p * x ^ 4 :=
      mul_nonneg (nullLambdaSeries_pos h).le (pow_nonneg hx 4)
    calc
      nullLambdaSeries m p * x ^ 4 /
          (6 * nullAnalyticScale m p *
            (1 - x / nullAnalyticScale m p)) ≤
        nullLambdaSeries m p * x ^ 4 /
          (6 * nullAnalyticScale m p *
            (1 - T / nullAnalyticScale m p)) :=
        div_le_div_of_nonneg_left hnum
          (mul_pos (mul_pos (by norm_num) hDelta) hdenT) hdenOrder
      _ = (nullLambdaSeries m p /
          (6 * nullAnalyticScale m p *
            (1 - T / nullAnalyticScale m p))) * x ^ 4 := by ring
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg
      (div_nonneg (mul_nonneg (nullLambdaSeries_pos h).le (pow_nonneg hx 3))
        (by norm_num)) hH
  have hBKx : B ≤ K * x ^ 3 := by
    dsimp [B, K, nullLogCutoffCoefficient]
    calc
      nullLambdaSeries m p * x ^ 3 / 6 + H ≤
          nullLambdaSeries m p * x ^ 3 / 6 + A * x ^ 4 :=
        add_le_add le_rfl hHA
      _ = (nullLambdaSeries m p / 6 + A * x) * x ^ 3 := by ring
      _ ≤ (nullLambdaSeries m p / 6 + A * T) * x ^ 3 := by
        gcongr
  have hx3 : x ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hx hxT 3
  have hx2 : x ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hx hxT 2
  have hBKT : B ≤ K * T ^ 3 := hBKx.trans
    (mul_le_mul_of_nonneg_left hx3 hK)
  have hpoint := norm_charFun_standardizedNullLaw_sub_firstEdgeworth_le h
    (t := t) (by simpa [x] using hTDx)
  have hexpneg : Real.exp (-(t ^ 2 / 2)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by
      have : 0 ≤ t ^ 2 / 2 := by positivity
      linarith)
  have hinnerNonneg : 0 ≤ H + B ^ 2 * Real.exp B :=
    add_nonneg hH (mul_nonneg (sq_nonneg B) (Real.exp_pos B).le)
  have hstrip :
      Real.exp (-(t ^ 2 / 2)) * (H + B ^ 2 * Real.exp B) ≤
        H + B ^ 2 * Real.exp B := by
    simpa using mul_le_of_le_one_left hinnerNonneg hexpneg
  have hBexp : B ^ 2 * Real.exp B ≤
      K ^ 2 * x ^ 6 * Real.exp (K * T ^ 3) := by
    calc
      B ^ 2 * Real.exp B ≤ (K * x ^ 3) ^ 2 * Real.exp (K * T ^ 3) := by
        gcongr
      _ = K ^ 2 * x ^ 6 * Real.exp (K * T ^ 3) := by ring
  have hx6 : x ^ 6 ≤ T ^ 2 * x ^ 4 := by
    calc
      x ^ 6 = x ^ 2 * x ^ 4 := by ring
      _ ≤ T ^ 2 * x ^ 4 :=
        mul_le_mul_of_nonneg_right hx2 (by positivity)
  change ‖charFun (standardizedNullLaw m p) t -
      nullFirstEdgeworthCharFun m p t‖ ≤ _
  calc
    ‖charFun (standardizedNullLaw m p) t -
        nullFirstEdgeworthCharFun m p t‖ ≤
      Real.exp (-(t ^ 2 / 2)) * (H + B ^ 2 * Real.exp B) := by
        simpa [x, H, B] using hpoint
    _ ≤ H + B ^ 2 * Real.exp B := hstrip
    _ ≤ A * x ^ 4 +
        K ^ 2 * x ^ 6 * Real.exp (K * T ^ 3) := add_le_add hHA hBexp
    _ ≤ A * x ^ 4 +
        K ^ 2 * (T ^ 2 * x ^ 4) * Real.exp (K * T ^ 3) := by
      gcongr
    _ = nullFirstEdgeworthFourierCoefficient m p T * |t| ^ 4 := by
      dsimp [A, K, x]
      unfold nullFirstEdgeworthFourierCoefficient
      ring

/-- Explicit truncated weighted Fourier estimate for the actual null law
against its signed first Edgeworth comparator. -/
theorem truncatedFourierDiscrepancy_null_firstEdgeworth_le
    {m p : ℕ} (h : Admissible m p) {T : ℝ}
    (hT : 0 ≤ T) (hTD : T < nullAnalyticScale m p) :
    truncatedFourierDiscrepancy
        (charFun (standardizedNullLaw m p))
        (nullFirstEdgeworthCharFun m p) T ≤
      2 * nullFirstEdgeworthFourierCoefficient m p T * T ^ 4 := by
  have hC := nullFirstEdgeworthFourierCoefficient_nonneg h hT hTD
  have hbound := truncatedFourierDiscrepancy_le_of_local_pow
    (φ := charFun (standardizedNullLaw m p))
    (ψ := nullFirstEdgeworthCharFun m p)
    (T := T) (C := nullFirstEdgeworthFourierCoefficient m p T)
    (n := 3) hT hC (fun t ht =>
      norm_charFun_sub_firstEdgeworth_le_cutoff_pow_four h hT hTD
        (by rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩))
  simpa [pow_succ] using hbound

end

end LogdetLean
