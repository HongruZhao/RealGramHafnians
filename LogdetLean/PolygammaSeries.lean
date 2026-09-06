import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic
/-!
# Positive series for the first two polygamma quantities

This file develops, directly from convergent positive series, exactly the
quantities needed for the variance and third cumulant of a log-Beta random
variable.  No differentiation of the Gamma function is needed here.

For `x > 0` we use

* `trigammaSeries x = ∑ l, 1 / (x + l)^2`, and
* `negPsiTwoSeries x = 2 ∑ l, 1 / (x + l)^3`.

The second expression is the positive quantity `-ψ₂(x)` in conventional
polygamma notation.
-/

namespace LogdetLean

noncomputable section

open Filter

/-- The positive series representation of the trigamma function on `(0,∞)`. -/
def trigammaSeries (x : ℝ) : ℝ :=
  ∑' l : ℕ, 1 / (x + (l : ℝ)) ^ 2

/-- The positive series representation of `-ψ₂(x)` on `(0,∞)`. -/
def negPsiTwoSeries (x : ℝ) : ℝ :=
  2 * ∑' l : ℕ, 1 / (x + (l : ℝ)) ^ 3

/-- A shifted reciprocal-power series is summable on the positive half-line. -/
private theorem summable_shifted_inv_pow {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 1 < k) :
    Summable (fun l : ℕ ↦ 1 / (x + (l : ℝ)) ^ k) := by
  have hbase : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) ^ k) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr hk)
  rw [← summable_nat_add_iff 1]
  refine hbase.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  apply one_div_le_one_div_of_le (pow_pos hn k)
  gcongr
  linarith

/-- The trigamma defining series is summable for every `x > 0`. -/
theorem summable_trigammaSeries_terms {x : ℝ} (hx : 0 < x) :
    Summable (fun l : ℕ ↦ 1 / (x + (l : ℝ)) ^ 2) :=
  summable_shifted_inv_pow hx (by norm_num)

/-- The unscaled cubic series defining `negPsiTwoSeries` is summable for `x > 0`. -/
theorem summable_negPsiTwoSeries_terms {x : ℝ} (hx : 0 < x) :
    Summable (fun l : ℕ ↦ 1 / (x + (l : ℝ)) ^ 3) :=
  summable_shifted_inv_pow hx (by norm_num)

/-- Every trigamma-series summand is nonnegative on the positive half-line. -/
theorem trigammaSeries_term_nonneg {x : ℝ} (hx : 0 < x) (l : ℕ) :
    0 ≤ 1 / (x + (l : ℝ)) ^ 2 := by
  positivity

/-- Every cubic-series summand is nonnegative on the positive half-line. -/
theorem negPsiTwoSeries_term_nonneg {x : ℝ} (hx : 0 < x) (l : ℕ) :
    0 ≤ 1 / (x + (l : ℝ)) ^ 3 := by
  positivity

/-- The trigamma series is nonnegative on `(0,∞)`. -/
theorem trigammaSeries_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ trigammaSeries x := by
  exact tsum_nonneg (trigammaSeries_term_nonneg hx)

/-- The trigamma series is strictly positive on `(0,∞)`. -/
theorem trigammaSeries_pos {x : ℝ} (hx : 0 < x) :
    0 < trigammaSeries x := by
  unfold trigammaSeries
  exact (summable_trigammaSeries_terms hx).tsum_pos
    (trigammaSeries_term_nonneg hx) 0 (by simpa using one_div_pos.mpr (sq_pos_of_pos hx))

/-- The positive version of the second polygamma series is nonnegative. -/
theorem negPsiTwoSeries_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ negPsiTwoSeries x := by
  unfold negPsiTwoSeries
  positivity

/-- The positive version of the second polygamma series is strictly positive. -/
theorem negPsiTwoSeries_pos {x : ℝ} (hx : 0 < x) :
    0 < negPsiTwoSeries x := by
  unfold negPsiTwoSeries
  have hsum : 0 < ∑' l : ℕ, 1 / (x + (l : ℝ)) ^ 3 :=
    (summable_negPsiTwoSeries_terms hx).tsum_pos
      (negPsiTwoSeries_term_nonneg hx) 0 (by simpa using one_div_pos.mpr (pow_pos hx 3))
  positivity

/-- Increasing the positive argument decreases every quadratic summand. -/
theorem trigammaSeries_term_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (l : ℕ) :
    1 / (y + (l : ℝ)) ^ 2 ≤ 1 / (x + (l : ℝ)) ^ 2 := by
  apply one_div_le_one_div_of_le
  · positivity
  · gcongr

/-- Increasing the positive argument decreases every cubic summand. -/
theorem negPsiTwoSeries_term_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (l : ℕ) :
    1 / (y + (l : ℝ)) ^ 3 ≤ 1 / (x + (l : ℝ)) ^ 3 := by
  apply one_div_le_one_div_of_le
  · positivity
  · gcongr

/-- `trigammaSeries` is antitone on the positive half-line. -/
theorem trigammaSeries_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    trigammaSeries y ≤ trigammaSeries x := by
  unfold trigammaSeries
  exact (summable_trigammaSeries_terms (hx.trans_le hxy)).tsum_le_tsum
    (trigammaSeries_term_antitone hx hxy)
    (summable_trigammaSeries_terms hx)

/-- `negPsiTwoSeries` is antitone on the positive half-line. -/
theorem negPsiTwoSeries_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    negPsiTwoSeries y ≤ negPsiTwoSeries x := by
  unfold negPsiTwoSeries
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (summable_negPsiTwoSeries_terms (hx.trans_le hxy)).tsum_le_tsum
      (negPsiTwoSeries_term_antitone hx hxy)
      (summable_negPsiTwoSeries_terms hx)

/-- The trigamma series is strictly decreasing on the positive half-line. -/
theorem trigammaSeries_strictAnti {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    trigammaSeries y < trigammaSeries x := by
  unfold trigammaSeries
  apply Summable.tsum_lt_tsum_of_nonneg
      (fun l ↦ trigammaSeries_term_nonneg (hx.trans hxy) l)
      (fun l ↦ trigammaSeries_term_antitone hx hxy.le l) (i := 0)
  · simp only [Nat.cast_zero, add_zero]
    have hsquares : x ^ 2 < y ^ 2 := by nlinarith
    exact one_div_lt_one_div_of_lt (sq_pos_of_pos hx) hsquares
  · exact summable_trigammaSeries_terms hx

/-- The positive second-polygamma series is strictly decreasing on `(0,∞)`. -/
theorem negPsiTwoSeries_strictAnti {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    negPsiTwoSeries y < negPsiTwoSeries x := by
  unfold negPsiTwoSeries
  gcongr
  apply Summable.tsum_lt_tsum_of_nonneg
      (fun l ↦ negPsiTwoSeries_term_nonneg (hx.trans hxy) l)
      (fun l ↦ negPsiTwoSeries_term_antitone hx hxy.le l) (i := 0)
  · simp only [Nat.cast_zero, add_zero]
    have hcubes : x ^ 3 < y ^ 3 := by
      have hdiff : 0 < y - x := sub_pos.mpr hxy
      have hquad : 0 < y ^ 2 + y * x + x ^ 2 := by
        nlinarith [sq_pos_of_pos hx, sq_pos_of_pos (hx.trans hxy), mul_pos (hx.trans hxy) hx]
      nlinarith [mul_pos hdiff hquad]
    exact one_div_lt_one_div_of_lt (pow_pos hx 3) hcubes
  · exact summable_negPsiTwoSeries_terms hx

/-- Strict-antitonicity as a function on the set `(0,∞)`. -/
theorem trigammaSeries_strictAntiOn :
    StrictAntiOn trigammaSeries (Set.Ioi 0) := by
  intro x hx y hy hxy
  exact trigammaSeries_strictAnti hx hxy

/-- Strict-antitonicity of `-ψ₂` as a function on `(0,∞)`. -/
theorem negPsiTwoSeries_strictAntiOn :
    StrictAntiOn negPsiTwoSeries (Set.Ioi 0) := by
  intro x hx y hy hxy
  exact negPsiTwoSeries_strictAnti hx hxy

/-- A difference of trigamma series may be moved term-by-term inside the sum. -/
theorem trigammaSeries_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    trigammaSeries x - trigammaSeries y =
      ∑' l : ℕ, (1 / (x + (l : ℝ)) ^ 2 - 1 / (y + (l : ℝ)) ^ 2) := by
  unfold trigammaSeries
  rw [(summable_trigammaSeries_terms hx).tsum_sub (summable_trigammaSeries_terms hy)]

/-- A difference of the positive second-polygamma series is a sum of
termwise cubic differences. -/
theorem negPsiTwoSeries_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    negPsiTwoSeries x - negPsiTwoSeries y =
      2 * ∑' l : ℕ, (1 / (x + (l : ℝ)) ^ 3 - 1 / (y + (l : ℝ)) ^ 3) := by
  unfold negPsiTwoSeries
  rw [(summable_negPsiTwoSeries_terms hx).tsum_sub (summable_negPsiTwoSeries_terms hy)]
  ring

/-- The trigamma difference used in each variance summand is nonnegative. -/
theorem trigammaSeries_sub_nonneg {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ trigammaSeries x - trigammaSeries y := by
  exact sub_nonneg.mpr (trigammaSeries_antitone hx hxy)

/-- The positive second-polygamma difference used for the magnitude of the
third cumulant is nonnegative. -/
theorem negPsiTwoSeries_sub_nonneg {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ negPsiTwoSeries x - negPsiTwoSeries y := by
  exact sub_nonneg.mpr (negPsiTwoSeries_antitone hx hxy)

/-- A single strictly ordered pair gives a strictly positive trigamma
difference. -/
theorem trigammaSeries_sub_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < trigammaSeries x - trigammaSeries y := by
  exact sub_pos.mpr (trigammaSeries_strictAnti hx hxy)

/-- A single strictly ordered pair gives a strictly positive `-ψ₂`
difference. -/
theorem negPsiTwoSeries_sub_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < negPsiTwoSeries x - negPsiTwoSeries y := by
  exact sub_pos.mpr (negPsiTwoSeries_strictAnti hx hxy)

/-! ## Elementary two-sided trigamma bounds

The following proof is a discrete version of the integral comparison.  The
positive reciprocal gaps telescope exactly, and each gap lies between the
adjacent reciprocal squares.  This avoids importing any unproved analytic
identification with a derivative of `log Γ`.
-/

private theorem reciprocalGap_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ 1 / a - 1 / (a + 1) := by
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le ha (by linarith)

private theorem reciprocalGap_le_inv_sq {a : ℝ} (ha : 0 < a) :
    1 / a - 1 / (a + 1) ≤ 1 / a ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha10 : a + 1 ≠ 0 := by linarith
  field_simp [ha0, ha10]
  nlinarith

private theorem shifted_inv_sq_le_reciprocalGap {a : ℝ} (ha : 0 < a) :
    1 / (a + 1) ^ 2 ≤ 1 / a - 1 / (a + 1) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha10 : a + 1 ≠ 0 := by linarith
  field_simp [ha0, ha10]
  nlinarith

/-- The reciprocal gaps telescope to `1/x`. -/
private theorem reciprocalGap_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun l : ℕ ↦
      1 / (x + (l : ℝ)) - 1 / (x + ((l + 1 : ℕ) : ℝ))) (1 / x) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hat : Tendsto (fun n : ℕ ↦ x + (n : ℝ)) atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ ↦ (x + (n : ℝ))⁻¹) atTop (nhds 0) :=
      hat.inv_tendsto_atTop
    simp_rw [Finset.sum_range_sub']
    have hconst : Tendsto (fun _ : ℕ ↦ (x⁻¹ : ℝ)) atTop (nhds x⁻¹) :=
      tendsto_const_nhds
    simpa only [one_div, Nat.cast_zero, add_zero, sub_zero] using hconst.sub hinv
  · intro l
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      reciprocalGap_nonneg (a := x + (l : ℝ)) (by positivity)

/-- The basic lower estimate `1/x ≤ ∑ₗ 1/(x+l)²`. -/
theorem one_div_le_trigammaSeries {x : ℝ} (hx : 0 < x) :
    1 / x ≤ trigammaSeries x := by
  have hgap := reciprocalGap_hasSum hx
  unfold trigammaSeries
  calc
    1 / x = ∑' l : ℕ,
        (1 / (x + (l : ℝ)) - 1 / (x + ((l + 1 : ℕ) : ℝ))) :=
      hgap.tsum_eq.symm
    _ ≤ ∑' l : ℕ, 1 / (x + (l : ℝ)) ^ 2 :=
      hgap.summable.tsum_le_tsum (fun l ↦ by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          reciprocalGap_le_inv_sq (a := x + (l : ℝ)) (by positivity))
        (summable_trigammaSeries_terms hx)

/-- The basic upper estimate `∑ₗ 1/(x+l)² ≤ 1/x + 1/x²`. -/
theorem trigammaSeries_le_one_div_add_one_div_sq {x : ℝ} (hx : 0 < x) :
    trigammaSeries x ≤ 1 / x + 1 / x ^ 2 := by
  have hgap := reciprocalGap_hasSum hx
  have hs := summable_trigammaSeries_terms hx
  unfold trigammaSeries
  rw [hs.tsum_eq_zero_add]
  have htail :
      ∑' l : ℕ, 1 / (x + ((l + 1 : ℕ) : ℝ)) ^ 2 ≤
        ∑' l : ℕ,
          (1 / (x + (l : ℝ)) - 1 / (x + ((l + 1 : ℕ) : ℝ))) := by
    exact ((summable_nat_add_iff 1).2 hs).tsum_le_tsum (fun l ↦ by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
        shifted_inv_sq_le_reciprocalGap (a := x + (l : ℝ)) (by positivity))
      hgap.summable
  rw [hgap.tsum_eq] at htail
  simp only [Nat.cast_zero, add_zero]
  linarith

/-- The convenient paired form of the elementary trigamma bounds. -/
theorem trigammaSeries_bounds {x : ℝ} (hx : 0 < x) :
    1 / x ≤ trigammaSeries x ∧ trigammaSeries x ≤ 1 / x + 1 / x ^ 2 :=
  ⟨one_div_le_trigammaSeries hx, trigammaSeries_le_one_div_add_one_div_sq hx⟩

/-! The same telescoping argument also gives quantitative bounds for the
positive cubic series.  They are useful when estimating the magnitude of the
third cumulant. -/

private theorem squareReciprocalGap_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ 1 / a ^ 2 - 1 / (a + 1) ^ 2 := by
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (sq_pos_of_pos ha) (by nlinarith)

private theorem squareReciprocalGap_le_two_inv_cube {a : ℝ} (ha : 0 < a) :
    1 / a ^ 2 - 1 / (a + 1) ^ 2 ≤ 2 * (1 / a ^ 3) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha10 : a + 1 ≠ 0 := by linarith
  field_simp [ha0, ha10]
  nlinarith

private theorem two_shifted_inv_cube_le_squareReciprocalGap {a : ℝ} (ha : 0 < a) :
    2 * (1 / (a + 1) ^ 3) ≤ 1 / a ^ 2 - 1 / (a + 1) ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha10 : a + 1 ≠ 0 := by linarith
  field_simp [ha0, ha10]
  nlinarith

private theorem squareReciprocalGap_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun l : ℕ ↦
      1 / (x + (l : ℝ)) ^ 2 - 1 / (x + ((l + 1 : ℕ) : ℝ)) ^ 2) (1 / x ^ 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hat : Tendsto (fun n : ℕ ↦ x + (n : ℝ)) atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ ↦ (x + (n : ℝ))⁻¹) atTop (nhds 0) :=
      hat.inv_tendsto_atTop
    have hinv2 : Tendsto (fun n : ℕ ↦ (x + (n : ℝ))⁻¹ ^ 2) atTop (nhds (0 : ℝ)) := by
      simpa using hinv.pow 2
    simp_rw [Finset.sum_range_sub']
    have hconst : Tendsto (fun _ : ℕ ↦ ((x ^ 2)⁻¹ : ℝ)) atTop (nhds (x ^ 2)⁻¹) :=
      tendsto_const_nhds
    simpa only [one_div, inv_pow, Nat.cast_zero, add_zero, sub_zero] using hconst.sub hinv2
  · intro l
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      squareReciprocalGap_nonneg (a := x + (l : ℝ)) (by positivity)

/-- The lower cubic-series estimate `1/x² ≤ -ψ₂(x)`. -/
theorem one_div_sq_le_negPsiTwoSeries {x : ℝ} (hx : 0 < x) :
    1 / x ^ 2 ≤ negPsiTwoSeries x := by
  have hgap := squareReciprocalGap_hasSum hx
  unfold negPsiTwoSeries
  rw [← tsum_mul_left]
  calc
    1 / x ^ 2 = ∑' l : ℕ,
        (1 / (x + (l : ℝ)) ^ 2 - 1 / (x + ((l + 1 : ℕ) : ℝ)) ^ 2) :=
      hgap.tsum_eq.symm
    _ ≤ ∑' l : ℕ, 2 * (1 / (x + (l : ℝ)) ^ 3) :=
      hgap.summable.tsum_le_tsum (fun l ↦ by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          squareReciprocalGap_le_two_inv_cube (a := x + (l : ℝ)) (by positivity))
        ((summable_negPsiTwoSeries_terms hx).mul_left 2)

/-- The upper cubic-series estimate `-ψ₂(x) ≤ 1/x² + 2/x³`. -/
theorem negPsiTwoSeries_le_one_div_sq_add_two_div_cube {x : ℝ} (hx : 0 < x) :
    negPsiTwoSeries x ≤ 1 / x ^ 2 + 2 / x ^ 3 := by
  have hgap := squareReciprocalGap_hasSum hx
  have hs := summable_negPsiTwoSeries_terms hx
  have htail :
      ∑' l : ℕ, 2 * (1 / (x + ((l + 1 : ℕ) : ℝ)) ^ 3) ≤
        ∑' l : ℕ,
          (1 / (x + (l : ℝ)) ^ 2 - 1 / (x + ((l + 1 : ℕ) : ℝ)) ^ 2) := by
    exact (((summable_nat_add_iff 1).2 hs).mul_left 2).tsum_le_tsum (fun l ↦ by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
        two_shifted_inv_cube_le_squareReciprocalGap
          (a := x + (l : ℝ)) (by positivity)) hgap.summable
  rw [tsum_mul_left, hgap.tsum_eq] at htail
  unfold negPsiTwoSeries
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, add_zero]
  calc
    2 * (1 / x ^ 3 + ∑' b : ℕ, 1 / (x + ↑(b + 1)) ^ 3) =
        2 / x ^ 3 + 2 * ∑' b : ℕ, 1 / (x + ↑(b + 1)) ^ 3 := by ring
    _ ≤ 2 / x ^ 3 + 1 / x ^ 2 := by
      simpa only [add_comm] using add_le_add_left htail (2 / x ^ 3)
    _ = 1 / x ^ 2 + 2 / x ^ 3 := by ring

/-- The paired form of the elementary cubic-series bounds. -/
theorem negPsiTwoSeries_bounds {x : ℝ} (hx : 0 < x) :
    1 / x ^ 2 ≤ negPsiTwoSeries x ∧
      negPsiTwoSeries x ≤ 1 / x ^ 2 + 2 / x ^ 3 :=
  ⟨one_div_sq_le_negPsiTwoSeries hx,
    negPsiTwoSeries_le_one_div_sq_add_two_div_cube hx⟩

end

end LogdetLean
