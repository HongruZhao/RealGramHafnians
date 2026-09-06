import LogdetLean.HigherCumulants
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
/-!
# Finite scale-separation inequalities

This file formalizes the deterministic estimates for

`a = (m-p+1)/2`, `V = V_{m,p}`, `A = A_{m,p}`,
`Delta = a * sqrt V`, and `lambda = A / V^(3/2)`.

The proof follows the elementary reciprocal-power comparison in the paper's
Appendix “Cumulant and scale inequalities.”  These inequalities are direct
Lean derivations.  They are not imported from Xie--Sun or from a probability
library.
-/

namespace LogdetLean

open Filter Set
open scoped BigOperators

noncomputable section

/-- The smallest first Beta shape, `a_*=(m-p+1)/2`. -/
def nullMinShape (m p : ℕ) : ℝ := betaShapeA m p

@[simp] theorem nullMinShape_eq (m p : ℕ) :
    nullMinShape m p = betaShapeA m p := rfl

theorem nullMinShape_pos {m p : ℕ} (h : Admissible m p) :
    0 < nullMinShape m p := betaShapeA_pos_of_le h.2

theorem nullAnalyticScale_pos {m p : ℕ} (h : Admissible m p) :
    0 < nullAnalyticScale m p := by
  unfold nullAnalyticScale
  exact mul_pos (betaShapeA_pos_of_le h.2)
    (Real.sqrt_pos.2 (nullVSeries_pos h))

/-- Fixed-exponent inequality behind `A a <= 3 V`. -/
theorem two_mul_cubic_difference_le_three_mul_quadratic_difference
    {a u v : ℝ} (ha : 0 < a) (hau : a ≤ u) (huv : u < v) :
    2 * a * (1 / u ^ 3 - 1 / v ^ 3) ≤
      3 * (1 / u ^ 2 - 1 / v ^ 2) := by
  have hu : 0 < u := ha.trans_le hau
  have hv : 0 < v := hu.trans huv
  have hpoly1 :
    2 * a * (v ^ 2 + v * u + u ^ 2) ≤
        2 * u * (v ^ 2 + v * u + u ^ 2) := by
    gcongr
  have hpoly2 :
      2 * u * (v ^ 2 + v * u + u ^ 2) ≤
        3 * u * v * (v + u) := by
    have hpos : 0 ≤ u * (v - u) * (v + 2 * u) := by positivity
    nlinarith
  have hpoly := hpoly1.trans hpoly2
  have hgap : 0 ≤ v - u := huv.le |> sub_nonneg.mpr
  have hmul := mul_le_mul_of_nonneg_left hpoly hgap
  field_simp [hu.ne', hv.ne']
  nlinarith [hmul]

private theorem quadratic_difference_le_two_gap_mul_inv_cube
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    1 / u ^ 2 - 1 / v ^ 2 ≤ 2 * (v - u) * (1 / u ^ 3) := by
  have hv : 0 < v := hu.trans huv
  have hfactor : 0 ≤ (u - v) ^ 2 * (u + 2 * v) := by positivity
  field_simp [hu.ne', hv.ne']
  nlinarith [hfactor]

/-- A quadratic reciprocal-power difference is bounded by its shape gap
times the positive second-polygamma series at the smaller shape. -/
theorem reciprocalPowerDifference_two_le_gap_mul_negPsiTwo
    {a M : ℝ} (ha : 0 < a) (haM : a < M) :
    reciprocalPowerDifference 2 a M ≤
      (M - a) * negPsiTwoSeries a := by
  have hM : 0 < M := ha.trans haM
  have hleft := summable_reciprocalPowerDifference
    (r := 2) (by norm_num) ha hM
  have hcub := summable_negPsiTwoSeries_terms ha
  have hright := hcub.mul_left (2 * (M - a))
  unfold reciprocalPowerDifference negPsiTwoSeries
  calc
    (∑' l : ℕ, (1 / (a + (l : ℝ)) ^ 2 -
        1 / (M + (l : ℝ)) ^ 2)) ≤
        ∑' l : ℕ, (2 * (M - a)) *
          (1 / (a + (l : ℝ)) ^ 3) := by
      exact hleft.tsum_le_tsum (fun l ↦ by
        have hal : 0 < a + (l : ℝ) := by positivity
        have hlt : a + (l : ℝ) < M + (l : ℝ) := by linarith
        have hpoint := quadratic_difference_le_two_gap_mul_inv_cube hal hlt
        simpa only [add_sub_add_right_eq_sub] using hpoint) hright
    _ = (2 * (M - a)) *
        ∑' l : ℕ, 1 / (a + (l : ℝ)) ^ 3 := by
      rw [← hcub.tsum_mul_left]
    _ = (M - a) *
        (2 * ∑' l : ℕ, 1 / (a + (l : ℝ)) ^ 3) := by ring

private theorem one_div_sq_add_two_div_cube_le_three_div_sq
    {a : ℝ} (ha : 1 ≤ a) :
    1 / a ^ 2 + 2 / a ^ 3 ≤ 3 / a ^ 2 := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  field_simp [ha0.ne']
  nlinarith

private theorem betaShapeA_min_le {m p j : ℕ}
    (hj : j ∈ Finset.Icc 2 p) :
    betaShapeA m p ≤ betaShapeA m j := by
  unfold betaShapeA
  have hjp : (j : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  linarith

private theorem card_Icc_two_cast_eq_pred (p : ℕ) (hp : 2 ≤ p) :
    (((Finset.Icc 2 p).card : ℕ) : ℝ) = (p : ℝ) - 1 := by
  rw [Nat.card_Icc]
  have hp1 : 1 ≤ p := by omega
  rw [show p + 1 - 2 = p - 1 by omega, Nat.cast_sub hp1]
  norm_num

/-- A useful upper bound when the minimum beta shape is not much larger
than the dimension. -/
theorem nullVSeries_le_pred_mul_minShape_recip_bounds {m p : ℕ}
    (h : Admissible m p) :
    nullVSeries m p ≤ ((p : ℝ) - 1) *
      (1 / nullMinShape m p + 1 / (nullMinShape m p) ^ 2) := by
  have ha : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  have htotal : 0 < betaShapeTotal m := betaShapeTotal_pos h
  unfold nullVSeries
  calc
    (∑ j ∈ Finset.Icc 2 p,
        (trigammaSeries (betaShapeA m j) -
          trigammaSeries (betaShapeTotal m))) ≤
        ∑ _j ∈ Finset.Icc 2 p,
          (1 / betaShapeA m p + 1 / (betaShapeA m p) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      have haj : 0 < betaShapeA m j := betaShapeA_pos_of_mem_Icc h.2 hj
      have hmin : betaShapeA m p ≤ betaShapeA m j :=
        betaShapeA_min_le hj
      have hdrop :
          trigammaSeries (betaShapeA m j) -
              trigammaSeries (betaShapeTotal m) ≤
            trigammaSeries (betaShapeA m j) := by
        have := trigammaSeries_nonneg htotal
        linarith
      exact hdrop.trans <| (trigammaSeries_antitone ha hmin).trans
        (trigammaSeries_le_one_div_add_one_div_sq ha)
    _ = ((p : ℝ) - 1) *
        (1 / nullMinShape m p + 1 / (nullMinShape m p) ^ 2) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      rw [card_Icc_two_cast_eq_pred p h.1]
      rfl

/-- The exact finite upper scale inequality `A a <= 3 V`. -/
theorem nullASeries_mul_minShape_le_three_mul_V {m p : ℕ}
    (h : Admissible m p) :
    nullASeries m p * nullMinShape m p ≤ 3 * nullVSeries m p := by
  rw [nullASeries_eq_doubleSeries h, nullVSeries_eq_doubleSeries h]
  unfold nullMinShape
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have haj : 0 < betaShapeA m j := betaShapeA_pos_of_mem_Icc h.2 hj
  have hap : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  have htotal : 0 < betaShapeTotal m := betaShapeTotal_pos h
  have hamin := betaShapeA_min_le (m := m) hj
  have hcub := summable_nullASeries_inner h hj
  have hsq := summable_nullVSeries_inner h hj
  have hleft := hcub.mul_left (2 * betaShapeA m p)
  have hright := hsq.mul_left 3
  rw [show (2 * (∑' l : ℕ,
      (1 / (betaShapeA m j + (l : ℝ)) ^ 3 -
        1 / (betaShapeTotal m + (l : ℝ)) ^ 3))) * betaShapeA m p =
      (2 * betaShapeA m p) * (∑' l : ℕ,
        (1 / (betaShapeA m j + (l : ℝ)) ^ 3 -
          1 / (betaShapeTotal m + (l : ℝ)) ^ 3)) by ring]
  rw [← hcub.tsum_mul_left]
  rw [← hsq.tsum_mul_left]
  exact hleft.tsum_le_tsum (fun l ↦ by
    apply two_mul_cubic_difference_le_three_mul_quadratic_difference hap
    · have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
      linarith
    · have hj2 := (Finset.mem_Icc.mp hj).1
      have hlt := betaShapeA_lt_total (m := m) hj2
      linarith) hright

/-- The upper scale inequality in the normalized form used by Fourier
estimates: `lambda <= 3 / Delta`. -/
theorem nullLambdaSeries_le_three_div_analyticScale {m p : ℕ}
    (h : Admissible m p) :
    nullLambdaSeries m p ≤ 3 / nullAnalyticScale m p := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hsqrt : 0 < Real.sqrt (nullVSeries m p) := Real.sqrt_pos.2 hV
  have ha : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  rw [nullLambdaSeries_eq, nullVSeries_rpow_three_halves h]
  unfold nullAnalyticScale
  apply (div_le_div_iff₀ (pow_pos hsqrt 3) (mul_pos ha hsqrt)).2
  have hscale := nullASeries_mul_minShape_le_three_mul_V h
  unfold nullMinShape at hscale
  have hmul := mul_le_mul_of_nonneg_right hscale hsqrt.le
  calc
    nullASeries m p * (betaShapeA m p * Real.sqrt (nullVSeries m p)) =
        (nullASeries m p * betaShapeA m p) *
          Real.sqrt (nullVSeries m p) := by ring
    _ ≤ (3 * nullVSeries m p) * Real.sqrt (nullVSeries m p) := hmul
    _ = 3 * Real.sqrt (nullVSeries m p) ^ 3 := by
      nth_rewrite 1 [← Real.sq_sqrt hV.le]
      ring

/-- Equivalent product form of the upper scale inequality. -/
theorem nullLambdaSeries_mul_analyticScale_le_three {m p : ℕ}
    (h : Admissible m p) :
    nullLambdaSeries m p * nullAnalyticScale m p ≤ 3 := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hupper := nullLambdaSeries_le_three_div_analyticScale h
  calc
    nullLambdaSeries m p * nullAnalyticScale m p ≤
        (3 / nullAnalyticScale m p) * nullAnalyticScale m p :=
      mul_le_mul_of_nonneg_right hupper hDelta.le
    _ = 3 := by field_simp [hDelta.ne']

/-- A one-step telescoping comparison.  Summing it over `l` gives the lower
integral-type estimate needed for the cubic reciprocal-power difference. -/
private theorem quadratic_forward_difference_le_twice_cubic_difference
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    (1 / u ^ 2 - 1 / v ^ 2) -
        (1 / (u + 1) ^ 2 - 1 / (v + 1) ^ 2) ≤
      2 * (1 / u ^ 3 - 1 / v ^ 3) := by
  have hv : 0 < v := hu.trans huv
  have hu1 : 0 < u + 1 := by linarith
  have hv1 : 0 < v + 1 := by linarith
  let P : ℝ :=
    3 * u ^ 4 * v + 2 * u ^ 4 +
    3 * u ^ 3 * v ^ 2 + 8 * u ^ 3 * v + 4 * u ^ 3 +
    3 * u ^ 2 * v ^ 3 + 8 * u ^ 2 * v ^ 2 + 7 * u ^ 2 * v + 2 * u ^ 2 +
    3 * u * v ^ 4 + 8 * u * v ^ 3 + 7 * u * v ^ 2 + 2 * u * v +
    2 * v ^ 4 + 4 * v ^ 3 + 2 * v ^ 2
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hfactor : 0 ≤ (v - u) * P :=
    mul_nonneg (sub_nonneg.mpr huv.le) hP
  field_simp [hu.ne', hv.ne', hu1.ne', hv1.ne']
  dsimp [P] at hfactor
  nlinarith [hfactor]

private theorem linear_forward_difference_le_quadratic_difference
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    (1 / u - 1 / v) - (1 / (u + 1) - 1 / (v + 1)) ≤
      1 / u ^ 2 - 1 / v ^ 2 := by
  have hv : 0 < v := hu.trans huv
  have hu1 : 0 < u + 1 := by linarith
  have hv1 : 0 < v + 1 := by linarith
  let P : ℝ := u ^ 2 + u * v + u + v ^ 2 + v
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hfactor : 0 ≤ (v - u) * P :=
    mul_nonneg (sub_nonneg.mpr huv.le) hP
  field_simp [hu.ne', hv.ne', hu1.ne', hv1.ne']
  dsimp [P] at hfactor
  nlinarith [hfactor]

private theorem reciprocal_difference_one_le_square_majorant
    {a M l : ℝ} (ha : 0 < a) (haM : a < M) (hl : 0 ≤ l) :
    0 ≤ 1 / (a + l) - 1 / (M + l) ∧
    1 / (a + l) - 1 / (M + l) ≤
      (M - a) * (1 / (a + l) ^ 2) := by
  have hu : 0 < a + l := by linarith
  have hv : 0 < M + l := by linarith
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le hu (by linarith))
  · field_simp [hu.ne', hv.ne']
    have hmul : 0 ≤ (M - a) * (a + l) * (M - a) := by positivity
    nlinarith [hmul]

private theorem summable_reciprocal_difference_one {a M : ℝ}
    (ha : 0 < a) (haM : a < M) :
    Summable (fun l : ℕ ↦
      1 / (a + (l : ℝ)) - 1 / (M + (l : ℝ))) := by
  have hmajor : Summable (fun l : ℕ ↦
      (M - a) * (1 / (a + (l : ℝ)) ^ 2)) :=
    (summable_shifted_reciprocal_pow ha (by norm_num : 1 < 2)).mul_left (M - a)
  exact hmajor.of_nonneg_of_le
    (fun l ↦ (reciprocal_difference_one_le_square_majorant ha haM
      (Nat.cast_nonneg l)).1)
    (fun l ↦ (reciprocal_difference_one_le_square_majorant ha haM
      (Nat.cast_nonneg l)).2)

private theorem tsum_forward_difference {g : ℕ → ℝ} (hg : Summable g) :
    ∑' l : ℕ, (g l - g (l + 1)) = g 0 := by
  have hgshift : Summable (fun l : ℕ ↦ g (l + 1)) :=
    (summable_nat_add_iff 1).2 hg
  rw [hg.tsum_sub hgshift]
  have hdecomp := hg.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hdecomp
  linarith

/-- Discrete integral comparison for the quadratic reciprocal-power series. -/
theorem linear_difference_le_reciprocalPowerDifference_two
    {a M : ℝ} (ha : 0 < a) (haM : a < M) :
    1 / a - 1 / M ≤ reciprocalPowerDifference 2 a M := by
  let g : ℕ → ℝ := fun l ↦
    1 / (a + (l : ℝ)) - 1 / (M + (l : ℝ))
  let f : ℕ → ℝ := fun l ↦
    1 / (a + (l : ℝ)) ^ 2 - 1 / (M + (l : ℝ)) ^ 2
  have hM : 0 < M := ha.trans haM
  have hg : Summable g := by
    dsimp [g]
    exact summable_reciprocal_difference_one ha haM
  have hfdiff : Summable (fun l : ℕ ↦ g l - g (l + 1)) :=
    hg.sub ((summable_nat_add_iff 1).2 hg)
  have hf : Summable f := by
    dsimp [f]
    exact summable_reciprocalPowerDifference (by norm_num) ha hM
  have hsum : (∑' l : ℕ, (g l - g (l + 1))) ≤ ∑' l : ℕ, f l :=
    hfdiff.tsum_le_tsum (fun l ↦ by
      dsimp [g, f]
      have hal : 0 < a + (l : ℝ) := by positivity
      have hlt : a + (l : ℝ) < M + (l : ℝ) := by linarith
      have hstep := linear_forward_difference_le_quadratic_difference hal hlt
      norm_num [Nat.cast_add, Nat.cast_one] at hstep ⊢
      ring_nf at hstep ⊢
      exact hstep) hf
  unfold reciprocalPowerDifference
  have hmain : g 0 ≤ ∑' l : ℕ, f l := by
    rw [← tsum_forward_difference hg]
    exact hsum
  simpa [g, f] using hmain

/-- Discrete integral comparison for the cubic reciprocal-power series. -/
theorem half_quadratic_difference_le_reciprocalPowerDifference_three
    {a M : ℝ} (ha : 0 < a) (haM : a < M) :
    (1 / 2 : ℝ) * (1 / a ^ 2 - 1 / M ^ 2) ≤
      reciprocalPowerDifference 3 a M := by
  let g : ℕ → ℝ := fun l ↦
    1 / (a + (l : ℝ)) ^ 2 - 1 / (M + (l : ℝ)) ^ 2
  let f : ℕ → ℝ := fun l ↦
    1 / (a + (l : ℝ)) ^ 3 - 1 / (M + (l : ℝ)) ^ 3
  have hM : 0 < M := ha.trans haM
  have hg : Summable g := by
    dsimp [g]
    exact summable_reciprocalPowerDifference (by norm_num) ha hM
  have hfdiff : Summable (fun l : ℕ ↦ g l - g (l + 1)) :=
    hg.sub ((summable_nat_add_iff 1).2 hg)
  have hf : Summable f := by
    dsimp [f]
    exact summable_reciprocalPowerDifference (by norm_num) ha hM
  have hleft := hfdiff.mul_left (1 / 2 : ℝ)
  have hsum :
      (∑' l : ℕ, (1 / 2 : ℝ) * (g l - g (l + 1))) ≤ ∑' l : ℕ, f l :=
    hleft.tsum_le_tsum (fun l ↦ by
      dsimp [g, f]
      have hal : 0 < a + (l : ℝ) := by positivity
      have hlt : a + (l : ℝ) < M + (l : ℝ) := by linarith
      have hstep := quadratic_forward_difference_le_twice_cubic_difference
        hal hlt
      norm_num [Nat.cast_add, Nat.cast_one] at hstep ⊢
      ring_nf at hstep ⊢
      linarith) hf
  unfold reciprocalPowerDifference
  have hmain : (1 / 2 : ℝ) * g 0 ≤ ∑' l : ℕ, f l := calc
    (1 / 2 : ℝ) * g 0 =
        (1 / 2 : ℝ) * (∑' l : ℕ, (g l - g (l + 1))) := by
      rw [tsum_forward_difference hg]
    _ = ∑' l : ℕ, (1 / 2 : ℝ) * (g l - g (l + 1)) := by
      rw [tsum_mul_left]
    _ ≤ ∑' l : ℕ, f l := hsum
  simpa [g, f] using hmain

private theorem normalized_shape_cubic_lower {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (3 / 8 : ℝ) ≤ ((x + 1) / 2) ^ 3 *
      (1 / ((x + 1) / 2) ^ 2 - 1 / ((x + y + 2) / 2) ^ 2) := by
  have hx1 : 0 < x + 1 := by linarith
  have hxy2 : 0 < x + y + 2 := by linarith
  have hP : 0 ≤
      8 * x ^ 2 * y + 5 * x ^ 2 + 4 * x * y ^ 2 +
        18 * x * y + 8 * x + y ^ 2 + 4 * y := by positivity
  field_simp [hx1.ne', hxy2.ne']
  nlinarith [hP]

/-- The first nontrivial summand alone gives a uniform lower bound after
multiplication by the cube of the smallest shape. -/
theorem minShape_cube_mul_quadratic_difference_lower {m p : ℕ}
    (h : Admissible m p) :
    (3 / 8 : ℝ) ≤ (nullMinShape m p) ^ 3 *
      (1 / (betaShapeA m p) ^ 2 - 1 / (betaShapeTotal m) ^ 2) := by
  let x : ℝ := (m : ℝ) - (p : ℝ)
  let y : ℝ := (p : ℝ) - 2
  have hx : 0 ≤ x := by
    dsimp [x]
    have hpmR : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast h.2
    linarith
  have hy : 0 ≤ y := by
    dsimp [y]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1
    linarith
  have hshape : betaShapeA m p = (x + 1) / 2 := by
    unfold betaShapeA
    dsimp [x]
  have htotal : betaShapeTotal m = (x + y + 2) / 2 := by
    unfold betaShapeTotal
    dsimp [x, y]
    ring
  unfold nullMinShape
  rw [hshape, htotal]
  exact normalized_shape_cubic_lower hx hy

/-- The cubic series `A` dominates the elementary quadratic difference at
the smallest shape. -/
theorem quadratic_difference_le_nullASeries {m p : ℕ}
    (h : Admissible m p) :
    1 / (betaShapeA m p) ^ 2 - 1 / (betaShapeTotal m) ^ 2 ≤
      nullASeries m p := by
  have hmem : p ∈ Finset.Icc 2 p := Finset.mem_Icc.mpr ⟨h.1, le_rfl⟩
  have ha : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  have hlt : betaShapeA m p < betaShapeTotal m :=
    betaShapeA_lt_total (m := m) h.1
  have hhalf :=
    half_quadratic_difference_le_reciprocalPowerDifference_three ha hlt
  have hsingle :
      2 * reciprocalPowerDifference 3 (betaShapeA m p) (betaShapeTotal m) ≤
        ∑ j ∈ Finset.Icc 2 p,
          2 * reciprocalPowerDifference 3
            (betaShapeA m j) (betaShapeTotal m) := by
    exact Finset.single_le_sum
      (s := Finset.Icc 2 p)
      (f := fun j ↦ 2 * reciprocalPowerDifference 3
        (betaShapeA m j) (betaShapeTotal m))
      (fun j hj ↦ by
        have haj : 0 < betaShapeA m j := betaShapeA_pos_of_mem_Icc h.2 hj
        have hjlt : betaShapeA m j < betaShapeTotal m :=
          betaShapeA_lt_total (m := m) (Finset.mem_Icc.mp hj).1
        have hnonneg := reciprocalPowerDifference_nonneg
          (r := 3) (by norm_num) haj hjlt.le
        positivity)
      hmem
  rw [nullASeries_eq_doubleSeries h]
  unfold reciprocalPowerDifference at hsingle hhalf
  linarith

/-- Exact lower finite scale inequality `A a^3 >= 3/8`. -/
theorem three_eighths_le_nullASeries_mul_minShape_cube {m p : ℕ}
    (h : Admissible m p) :
    (3 / 8 : ℝ) ≤ nullASeries m p * (nullMinShape m p) ^ 3 := by
  have hquad := quadratic_difference_le_nullASeries h
  have ha : 0 ≤ (nullMinShape m p) ^ 3 :=
    pow_nonneg (nullMinShape_pos h).le 3
  have hmul := mul_le_mul_of_nonneg_right hquad ha
  have hlower := minShape_cube_mul_quadratic_difference_lower h
  calc
    (3 / 8 : ℝ) ≤ (nullMinShape m p) ^ 3 *
        (1 / (betaShapeA m p) ^ 2 - 1 / (betaShapeTotal m) ^ 2) := hlower
    _ ≤ (nullMinShape m p) ^ 3 * nullASeries m p := by
      nlinarith [hmul]
    _ = nullASeries m p * (nullMinShape m p) ^ 3 := by ring

/-- The lower scale inequality in the normalized form used by Fourier
estimates: `(3/8) / Delta^3 <= lambda`. -/
theorem three_eighths_div_analyticScale_cube_le_nullLambdaSeries
    {m p : ℕ} (h : Admissible m p) :
    (3 / 8 : ℝ) / (nullAnalyticScale m p) ^ 3 ≤
      nullLambdaSeries m p := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hsqrt : 0 < Real.sqrt (nullVSeries m p) := Real.sqrt_pos.2 hV
  have ha : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  rw [nullLambdaSeries_eq, nullVSeries_rpow_three_halves h]
  unfold nullAnalyticScale
  apply (div_le_div_iff₀ (pow_pos (mul_pos ha hsqrt) 3)
    (pow_pos hsqrt 3)).2
  have hscale := three_eighths_le_nullASeries_mul_minShape_cube h
  unfold nullMinShape at hscale
  have hmul := mul_le_mul_of_nonneg_right hscale
    (pow_nonneg hsqrt.le 3)
  calc
    (3 / 8 : ℝ) * Real.sqrt (nullVSeries m p) ^ 3 ≤
        (nullASeries m p * betaShapeA m p ^ 3) *
          Real.sqrt (nullVSeries m p) ^ 3 := hmul
    _ = nullASeries m p *
        (betaShapeA m p * Real.sqrt (nullVSeries m p)) ^ 3 := by ring

/-- Equivalent product form of the lower scale inequality. -/
theorem three_eighths_le_nullLambdaSeries_mul_analyticScale_cube
    {m p : ℕ} (h : Admissible m p) :
    (3 / 8 : ℝ) ≤
      nullLambdaSeries m p * (nullAnalyticScale m p) ^ 3 := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hlower :=
    three_eighths_div_analyticScale_cube_le_nullLambdaSeries h
  have hmul := mul_le_mul_of_nonneg_right hlower
    (pow_nonneg hDelta.le 3)
  calc
    (3 / 8 : ℝ) =
        ((3 / 8 : ℝ) / (nullAnalyticScale m p) ^ 3) *
          (nullAnalyticScale m p) ^ 3 := by
      field_simp [hDelta.ne']
    _ ≤ nullLambdaSeries m p * (nullAnalyticScale m p) ^ 3 := hmul

private theorem shape_linear_difference_lower {m j : ℕ}
    (hj2 : 2 ≤ j) (hjm : j ≤ m) :
    2 * ((j : ℝ) - 1) / (m : ℝ) ^ 2 ≤
      1 / betaShapeA m j - 1 / betaShapeTotal m := by
  have hmN : 0 < m := by omega
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmN
  have hjmR : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
  have hj2R : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
  have hshape : 0 < (m : ℝ) - (j : ℝ) + 1 := by linarith
  unfold betaShapeA betaShapeTotal
  field_simp [hm.ne', hshape.ne']
  have hj1 : 0 ≤ (j : ℝ) - 1 := by linarith
  have hprod : 0 ≤ ((j : ℝ) - 1) * ((j : ℝ) - 1) :=
    mul_nonneg hj1 hj1
  nlinarith [hprod]

private theorem sum_Icc_two_cast_sub_one (p : ℕ) (hp : 2 ≤ p) :
    (∑ j ∈ Finset.Icc 2 p, ((j : ℝ) - 1)) =
      (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 + k := ⟨p - 2, by omega⟩
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 2 + (k + 1) = (2 + k) + 1 by omega]
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih (by omega)]
      push_cast
      ring

/-- Refined upper variance bound when the smallest shape is at least one. -/
theorem nullVSeries_le_three_quarters_dimension_div_minShape_sq
    {m p : ℕ} (h : Admissible m p) (ha1 : 1 ≤ nullMinShape m p) :
    nullVSeries m p ≤
      3 * (p : ℝ) * ((p : ℝ) - 1) /
        (4 * (nullMinShape m p) ^ 2) := by
  have ha : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  have hnegA : negPsiTwoSeries (betaShapeA m p) ≤
      3 / (betaShapeA m p) ^ 2 := by
    exact (negPsiTwoSeries_le_one_div_sq_add_two_div_cube ha).trans
      (one_div_sq_add_two_div_cube_le_three_div_sq ha1)
  rw [nullVSeries_eq_doubleSeries h]
  unfold nullMinShape
  calc
    (∑ j ∈ Finset.Icc 2 p, ∑' l : ℕ,
        (1 / (betaShapeA m j + (l : ℝ)) ^ 2 -
          1 / (betaShapeTotal m + (l : ℝ)) ^ 2)) ≤
        ∑ j ∈ Finset.Icc 2 p,
          (((j : ℝ) - 1) / 2) *
            (3 / (betaShapeA m p) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjb := Finset.mem_Icc.mp hj
      have haj : 0 < betaShapeA m j := betaShapeA_pos_of_mem_Icc h.2 hj
      have hlt : betaShapeA m j < betaShapeTotal m :=
        betaShapeA_lt_total (m := m) hjb.1
      have hmin : betaShapeA m p ≤ betaShapeA m j := betaShapeA_min_le hj
      have hnegj : negPsiTwoSeries (betaShapeA m j) ≤
          3 / (betaShapeA m p) ^ 2 :=
        (negPsiTwoSeries_antitone ha hmin).trans hnegA
      have hgap : betaShapeTotal m - betaShapeA m j =
          ((j : ℝ) - 1) / 2 := by
        unfold betaShapeTotal betaShapeA
        ring
      have hrpd := reciprocalPowerDifference_two_le_gap_mul_negPsiTwo haj hlt
      unfold reciprocalPowerDifference at hrpd
      calc
        (∑' l : ℕ, (1 / (betaShapeA m j + (l : ℝ)) ^ 2 -
            1 / (betaShapeTotal m + (l : ℝ)) ^ 2)) ≤
            (betaShapeTotal m - betaShapeA m j) *
              negPsiTwoSeries (betaShapeA m j) := hrpd
        _ ≤ (((j : ℝ) - 1) / 2) *
              (3 / (betaShapeA m p) ^ 2) := by
          rw [hgap]
          apply mul_le_mul_of_nonneg_left hnegj
          have hj2R : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjb.1
          linarith
    _ = 3 * (p : ℝ) * ((p : ℝ) - 1) /
          (4 * (betaShapeA m p) ^ 2) := by
      calc
        (∑ j ∈ Finset.Icc 2 p,
            (((j : ℝ) - 1) / 2) *
              (3 / (betaShapeA m p) ^ 2)) =
            (3 / (2 * (betaShapeA m p) ^ 2)) *
              ∑ j ∈ Finset.Icc 2 p, ((j : ℝ) - 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = 3 * (p : ℝ) * ((p : ℝ) - 1) /
            (4 * (betaShapeA m p) ^ 2) := by
          rw [sum_Icc_two_cast_sub_one p h.1]
          ring

/-- A uniform elementary lower bound for the null variance series. -/
theorem nullVSeries_lower_p_mul_pred_div_m_sq {m p : ℕ}
    (h : Admissible m p) :
    (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤ nullVSeries m p := by
  have hsum_eval :
      (∑ j ∈ Finset.Icc 2 p,
        2 * ((j : ℝ) - 1) / (m : ℝ) ^ 2) =
        (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
    calc
      (∑ j ∈ Finset.Icc 2 p,
          2 * ((j : ℝ) - 1) / (m : ℝ) ^ 2) =
          (2 / (m : ℝ) ^ 2) *
            ∑ j ∈ Finset.Icc 2 p, ((j : ℝ) - 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
        rw [sum_Icc_two_cast_sub_one p h.1]
        ring
  rw [nullVSeries_eq_doubleSeries h]
  calc
    (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 =
        ∑ j ∈ Finset.Icc 2 p,
          2 * ((j : ℝ) - 1) / (m : ℝ) ^ 2 := hsum_eval.symm
    _ ≤ ∑ j ∈ Finset.Icc 2 p, ∑' l : ℕ,
        (1 / (betaShapeA m j + (l : ℝ)) ^ 2 -
          1 / (betaShapeTotal m + (l : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjb := Finset.mem_Icc.mp hj
      have hjm : j ≤ m := le_trans hjb.2 h.2
      have ha : 0 < betaShapeA m j := betaShapeA_pos_of_le hjm
      have hlt : betaShapeA m j < betaShapeTotal m :=
        betaShapeA_lt_total (m := m) hjb.1
      have hshape := shape_linear_difference_lower hjb.1 hjm
      have hintegral :=
        linear_difference_le_reciprocalPowerDifference_two ha hlt
      unfold reciprocalPowerDifference at hintegral
      exact hshape.trans hintegral

private theorem sum_recip_betaShape_eq_Ico {m p : ℕ}
    (h : Admissible m p) :
    (∑ j ∈ Finset.Icc 2 p, 1 / betaShapeA m j) =
      2 * ∑ r ∈ Finset.Ico (m - p + 1) m, ((r : ℝ)⁻¹) := by
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hrewrite :
      (∑ j ∈ Finset.Icc 2 p, 1 / betaShapeA m j) =
        ∑ j ∈ Finset.Icc 2 p,
          2 * (((m - j + 1 : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≤ m := le_trans (Finset.mem_Icc.mp hj).2 h.2
    have hpos : 0 < m - j + 1 := by omega
    unfold betaShapeA
    rw [show ((m - j + 1 : ℕ) : ℝ) =
        (m : ℝ) - (j : ℝ) + 1 by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hjm]
      ]
    field_simp
  rw [hrewrite, Finset.mul_sum]
  apply Finset.sum_bij (fun j _hj ↦ m - j + 1)
  · intro j hj
    have hjb := Finset.mem_Icc.mp hj
    apply Finset.mem_Ico.mpr
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    have h₁ := (Finset.mem_Icc.mp hj₁).2
    have h₂ := (Finset.mem_Icc.mp hj₂).2
    omega
  · intro r hr
    have hrb := Finset.mem_Ico.mp hr
    refine ⟨m - r + 1, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      omega
    · omega
  · intro j hj
    rfl

private theorem sum_shape_linear_difference_eq_Ico {m p : ℕ}
    (h : Admissible m p) :
    (∑ j ∈ Finset.Icc 2 p,
      (1 / betaShapeA m j - 1 / betaShapeTotal m)) =
      2 * ((∑ r ∈ Finset.Ico (m - p + 1) m, ((r : ℝ)⁻¹)) -
        ((p : ℝ) - 1) / (m : ℝ)) := by
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmN : 0 < m := by omega
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hconst :
      (∑ _j ∈ Finset.Icc 2 p, (1 / betaShapeTotal m : ℝ)) =
        ((p : ℝ) - 1) * (2 / (m : ℝ)) := by
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    rw [Nat.card_Icc]
    have hp1 : 1 ≤ p := by omega
    have hc : (((p + 1 - 2 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
      rw [show p + 1 - 2 = p - 1 by omega, Nat.cast_sub hp1]
      norm_num
    rw [hc]
    unfold betaShapeTotal
    field_simp
  rw [Finset.sum_sub_distrib, sum_recip_betaShape_eq_Ico h, hconst]
  ring

theorem sum_shape_linear_difference_le_nullVSeries {m p : ℕ}
    (h : Admissible m p) :
    (∑ j ∈ Finset.Icc 2 p,
      (1 / betaShapeA m j - 1 / betaShapeTotal m)) ≤ nullVSeries m p := by
  rw [nullVSeries_eq_doubleSeries h]
  apply Finset.sum_le_sum
  intro j hj
  have hjb := Finset.mem_Icc.mp hj
  have hjm : j ≤ m := le_trans hjb.2 h.2
  have ha : 0 < betaShapeA m j := betaShapeA_pos_of_le hjm
  have hlt : betaShapeA m j < betaShapeTotal m :=
    betaShapeA_lt_total (m := m) hjb.1
  have hintegral :=
    linear_difference_le_reciprocalPowerDifference_two ha hlt
  unfold reciprocalPowerDifference at hintegral
  exact hintegral

private theorem log_nat_ratio_le_sum_Ico_recip {q m : ℕ}
    (hq : 0 < q) (hqm : q ≤ m) :
    Real.log ((m : ℝ) / (q : ℝ)) ≤
      ∑ r ∈ Finset.Ico q m, ((r : ℝ)⁻¹) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hqmR : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqm
  have hanti : AntitoneOn (fun x : ℝ ↦ x⁻¹)
      (Set.Icc (q : ℝ) (m : ℝ)) := inv_antitoneOn_Icc_right hqR
  have hint := hanti.integral_le_sum_Ico hqm
  have hzero : (0 : ℝ) ∉ Set.uIcc (q : ℝ) (m : ℝ) := by
    rw [Set.uIcc_of_le hqmR]
    intro hz
    have := hz.1
    linarith
  rw [integral_inv hzero] at hint
  exact hint

/-- Logarithmic lower bound, sharp enough to control the nearly-square
regime.  Here `q=m-p+1` is the residual degree of freedom. -/
theorem nullVSeries_log_lower {m p : ℕ} (h : Admissible m p) :
    2 * (Real.log ((m : ℝ) / ((m - p + 1 : ℕ) : ℝ)) -
      ((p : ℝ) - 1) / (m : ℝ)) ≤ nullVSeries m p := by
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hq : 0 < m - p + 1 := by omega
  have hqm : m - p + 1 ≤ m := by omega
  have hlog := log_nat_ratio_le_sum_Ico_recip hq hqm
  have hsum := sum_shape_linear_difference_le_nullVSeries h
  rw [sum_shape_linear_difference_eq_Ico h] at hsum
  nlinarith

/-- Shape-ratio logarithm controlled by the variance.  This is the cutoff
comparison `log(2M/a) <= C(1+V)` with the explicit universal constant `C=2`. -/
theorem log_two_total_div_minShape_le_two_mul_one_add_V
    {m p : ℕ} (h : Admissible m p) :
    Real.log (2 * betaShapeTotal m / nullMinShape m p) ≤
      2 * (1 + nullVSeries m p) := by
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmN : 0 < m := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hp2) hpm
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hqN : 0 < m - p + 1 := by omega
  have hq : 0 < ((m - p + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hqN
  have hfrac : ((p : ℝ) - 1) / (m : ℝ) ≤ 1 := by
    apply (div_le_one hm).2
    have hpmR : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpm
    linarith
  have hVlog := nullVSeries_log_lower h
  have hlog2 :=
    Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hlog2
  have hVnonneg : 0 ≤ nullVSeries m p := nullVSeries_nonneg hpm
  have hratio :
      2 * betaShapeTotal m / nullMinShape m p =
        2 * ((m : ℝ) / ((m - p + 1 : ℕ) : ℝ)) := by
    unfold betaShapeTotal nullMinShape betaShapeA
    rw [show ((m - p + 1 : ℕ) : ℝ) =
        (m : ℝ) - (p : ℝ) + 1 by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hpm]]
    field_simp [hq.ne']
  rw [hratio, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (div_ne_zero hm.ne' hq.ne')]
  nlinarith

/-- The analytic scale never exceeds the dimension: `Delta^2 <= p^2`.
This uniform polynomial upper bound is used to compare logarithmic cutoffs. -/
theorem nullAnalyticScale_sq_le_dimension_sq {m p : ℕ}
    (h : Admissible m p) :
    (nullAnalyticScale m p) ^ 2 ≤ (p : ℝ) ^ 2 := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have ha : 0 < nullMinShape m p := nullMinShape_pos h
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1
  have hDeltaSq : (nullAnalyticScale m p) ^ 2 =
      (nullMinShape m p) ^ 2 * nullVSeries m p := by
    unfold nullAnalyticScale nullMinShape
    rw [mul_pow, Real.sq_sqrt hV.le]
  rw [hDeltaSq]
  by_cases hsmall : nullMinShape m p ≤ (p : ℝ)
  · have hupper := nullVSeries_le_pred_mul_minShape_recip_bounds h
    have hmul := mul_le_mul_of_nonneg_left hupper (pow_nonneg ha.le 2)
    calc
      nullMinShape m p ^ 2 * nullVSeries m p ≤
          nullMinShape m p ^ 2 *
            (((p : ℝ) - 1) *
              (1 / nullMinShape m p +
                1 / nullMinShape m p ^ 2)) := hmul
      _ = ((p : ℝ) - 1) * (nullMinShape m p + 1) := by
        field_simp [ha.ne']
      _ ≤ (p : ℝ) ^ 2 := by nlinarith
  · have hlarge : (p : ℝ) ≤ nullMinShape m p := le_of_not_ge hsmall
    have ha1 : 1 ≤ nullMinShape m p := by linarith
    have hupper :=
      nullVSeries_le_three_quarters_dimension_div_minShape_sq h ha1
    have hmul := mul_le_mul_of_nonneg_left hupper (pow_nonneg ha.le 2)
    calc
      nullMinShape m p ^ 2 * nullVSeries m p ≤
          nullMinShape m p ^ 2 *
            (3 * (p : ℝ) * ((p : ℝ) - 1) /
              (4 * nullMinShape m p ^ 2)) := hmul
      _ = 3 * (p : ℝ) * ((p : ℝ) - 1) / 4 := by
        field_simp [ha.ne']
      _ ≤ (p : ℝ) ^ 2 := by nlinarith

theorem nullAnalyticScale_le_dimension {m p : ℕ} (h : Admissible m p) :
    nullAnalyticScale m p ≤ (p : ℝ) := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hp : 0 < (p : ℝ) := by
    exact Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) h.1)
  have hsquare := nullAnalyticScale_sq_le_dimension_sq h
  nlinarith [sq_nonneg (nullAnalyticScale m p + (p : ℝ))]

/-- Logarithmic cutoff comparison following from `Delta <= p`. -/
theorem log_nullAnalyticScale_le_log_dimension {m p : ℕ}
    (h : Admissible m p) :
    Real.log (nullAnalyticScale m p) ≤ Real.log (p : ℝ) := by
  have hp : (p : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]
    exact Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) h.1)
  exact (Real.strictMonoOn_log.le_iff_le
    (nullAnalyticScale_pos h) hp).2
      (nullAnalyticScale_le_dimension h)

/-- Exact residual-degree representation of the square analytic scale. -/
theorem nullAnalyticScale_sq_eq_residual_sq_mul_V {m p : ℕ}
    (h : Admissible m p) :
    (nullAnalyticScale m p) ^ 2 =
      (((m - p + 1 : ℕ) : ℝ) ^ 2 / 4) * nullVSeries m p := by
  have hV : 0 ≤ nullVSeries m p := (nullVSeries_pos h).le
  have hcast : ((m - p + 1 : ℕ) : ℝ) =
      (m : ℝ) - (p : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub h.2]
  unfold nullAnalyticScale betaShapeA
  rw [mul_pow, Real.sq_sqrt hV, hcast]
  ring

/-- A coarse lower bound uniform over every admissible `m >= p`.  Its
logarithmic growth is sufficient for the sequential uniform-limit theorem. -/
theorem log_dimension_sub_two_div_sixteen_le_nullAnalyticScale_sq
    {m p : ℕ} (h : Admissible m p) :
    (Real.log (p : ℝ) - 2) / 16 ≤ (nullAnalyticScale m p) ^ 2 := by
  let qN : ℕ := m - p + 1
  let q : ℝ := (qN : ℝ)
  let pr : ℝ := (p : ℝ)
  let mr : ℝ := (m : ℝ)
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hqN : 0 < qN := by dsimp [qN]; omega
  have hq : 0 < q := by exact Nat.cast_pos.mpr hqN
  have hp : 0 < pr := by
    dsimp [pr]
    exact Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) hp2)
  have hpone : 1 ≤ pr := by
    dsimp [pr]
    exact_mod_cast (show 1 ≤ p by omega)
  have hmN : 0 < m := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hp2) hpm
  have hm : 0 < mr := by
    dsimp [mr]
    exact Nat.cast_pos.mpr hmN
  have hqeq : q = mr - pr + 1 := by
    dsimp [q, qN, mr, pr]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hpm]
  have hprm : pr ≤ mr := by
    dsimp [pr, mr]
    exact_mod_cast hpm
  have hVlower : pr * (pr - 1) / mr ^ 2 ≤ nullVSeries m p := by
    simpa [pr, mr] using nullVSeries_lower_p_mul_pred_div_m_sq h
  have hDbase :
      (q ^ 2 / 4) * (pr * (pr - 1) / mr ^ 2) ≤
        (nullAnalyticScale m p) ^ 2 := by
    rw [nullAnalyticScale_sq_eq_residual_sq_mul_V h]
    change (q ^ 2 / 4) * (pr * (pr - 1) / mr ^ 2) ≤
      (q ^ 2 / 4) * nullVSeries m p
    exact mul_le_mul_of_nonneg_left hVlower (by positivity)
  have hlogUpper : Real.log pr ≤ pr - 1 := Real.log_le_sub_one_of_pos hp
  by_cases hhalf : mr / 2 ≤ q
  · have hmq : mr ^ 2 ≤ 4 * q ^ 2 := by nlinarith [sq_nonneg (q - mr / 2)]
    have hprod : 0 ≤ pr * (pr - 1) := mul_nonneg hp.le (sub_nonneg.mpr hpone)
    have hmul := mul_le_mul_of_nonneg_left hmq hprod
    have hcase : pr * (pr - 1) / 16 ≤
        (q ^ 2 / 4) * (pr * (pr - 1) / mr ^ 2) := by
      field_simp [hm.ne']
      nlinarith [hmul]
    dsimp [pr] at hlogUpper ⊢
    nlinarith [hcase.trans hDbase]
  · have hhalf' : q < mr / 2 := lt_of_not_ge hhalf
    by_cases hqbig : pr ≤ q ^ 2
    · have hm_lt : mr < 2 * pr := by linarith [hqeq]
      have hm_sq : mr ^ 2 ≤ 4 * pr ^ 2 := by nlinarith
      have hqp0 := mul_le_mul_of_nonneg_right hqbig hp.le
      have hqp : pr ^ 2 ≤ q ^ 2 * pr := by nlinarith [hqp0]
      have hcore : mr ^ 2 ≤ 4 * (q ^ 2 * pr) := by nlinarith
      have hpred : 0 ≤ pr - 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcore hpred
      have hcase : (pr - 1) / 16 ≤
          (q ^ 2 / 4) * (pr * (pr - 1) / mr ^ 2) := by
        field_simp [hm.ne']
        nlinarith [hmul]
      dsimp [pr] at hlogUpper ⊢
      nlinarith [hcase.trans hDbase]
    · have hqsmall : q ^ 2 < pr := lt_of_not_ge hqbig
      have hratioPos : 0 < mr / q := div_pos hm hq
      have hpq : pr * q ^ 2 ≤ mr ^ 2 := by
        have hqle : q ^ 2 ≤ pr := hqsmall.le
        have hmulq := mul_le_mul_of_nonneg_left hqle hp.le
        have hpsq : pr ^ 2 ≤ mr ^ 2 := by nlinarith
        nlinarith
      have hratioSq : pr ≤ (mr / q) ^ 2 := by
        rw [div_pow]
        exact (le_div_iff₀ (sq_pos_of_pos hq)).2 hpq
      have hlogratio : Real.log pr ≤ 2 * Real.log (mr / q) := by
        have hratioSqPos : 0 < (mr / q) ^ 2 := sq_pos_of_pos hratioPos
        have hmono :=
          (Real.strictMonoOn_log.le_iff_le hp hratioSqPos).2 hratioSq
        rw [Real.log_pow] at hmono
        norm_num at hmono
        exact hmono
      have hfrac : (pr - 1) / mr ≤ 1 := by
        apply (div_le_one hm).2
        linarith [hprm]
      have hH : (Real.log pr - 2) / 2 ≤
          Real.log (mr / q) - (pr - 1) / mr := by
        nlinarith
      by_cases htarget : Real.log pr - 2 ≤ 0
      · have hDeltaSq : 0 ≤ (nullAnalyticScale m p) ^ 2 := sq_nonneg _
        dsimp [pr] at htarget ⊢
        nlinarith
      · have hHnonneg : 0 ≤ Real.log (mr / q) - (pr - 1) / mr := by
          nlinarith [hH]
        have hqone : 1 ≤ q := by
          have hqN1 : 1 ≤ qN := hqN
          dsimp [q]
          exact_mod_cast hqN1
        have hqSq : 1 ≤ q ^ 2 := by nlinarith
        have hmulH := mul_le_mul_of_nonneg_right hqSq hHnonneg
        have hVlog := nullVSeries_log_lower h
        have hVlog' :
            2 * (Real.log (mr / q) - (pr - 1) / mr) ≤
              nullVSeries m p := by
          simpa [mr, pr, q, qN] using hVlog
        have hDlog :
            (q ^ 2 / 2) *
                (Real.log (mr / q) - (pr - 1) / mr) ≤
              (nullAnalyticScale m p) ^ 2 := by
          rw [nullAnalyticScale_sq_eq_residual_sq_mul_V h]
          change (q ^ 2 / 2) *
              (Real.log (mr / q) - (pr - 1) / mr) ≤
            (q ^ 2 / 4) * nullVSeries m p
          have hmulV := mul_le_mul_of_nonneg_left hVlog'
            (show 0 ≤ q ^ 2 / 4 by positivity)
          nlinarith
        dsimp [pr] at htarget ⊢
        nlinarith [hH, hmulH, hDlog]

/-- Sequential formulation of uniform scale separation: along every
admissible choice `m(p) >= p`, the analytic scale tends to infinity. -/
theorem tendsto_nullAnalyticScale_atTop_of_eventually_admissible
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ nullAnalyticScale (m p) p) atTop atTop := by
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsub : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ) - 2) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-2 : ℝ) hlog
  have hlower : Tendsto
      (fun p : ℕ ↦ (Real.log (p : ℝ) - 2) / 16) atTop atTop :=
    hsub.atTop_div_const (by norm_num)
  have hbound :
      (fun p : ℕ ↦ (Real.log (p : ℝ) - 2) / 16) ≤ᶠ[atTop]
        (fun p ↦ (nullAnalyticScale (m p) p) ^ 2) :=
    hadm.mono fun p hp ↦
      log_dimension_sub_two_div_sixteen_le_nullAnalyticScale_sq hp
  have hsquare : Tendsto
      (fun p ↦ (nullAnalyticScale (m p) p) ^ 2) atTop atTop :=
    tendsto_atTop_mono' atTop hbound hlower
  have hsqrt : Tendsto
      (fun p ↦ Real.sqrt ((nullAnalyticScale (m p) p) ^ 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hsquare
  apply hsqrt.congr'
  filter_upwards [hadm] with p hp
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (nullAnalyticScale_pos hp)]

/-- Consequently the standardized third-cumulant scale tends to zero,
uniformly in the same sequential sense. -/
theorem tendsto_nullLambdaSeries_zero_of_eventually_admissible
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ nullLambdaSeries (m p) p) atTop (nhds 0) := by
  have hDelta :=
    tendsto_nullAnalyticScale_atTop_of_eventually_admissible m hadm
  have hupperLimit : Tendsto
      (fun p ↦ 3 / nullAnalyticScale (m p) p) atTop (nhds 0) :=
    hDelta.const_div_atTop 3
  apply squeeze_zero'
  · exact hadm.mono fun p hp ↦ (nullLambdaSeries_pos hp).le
  · exact hadm.mono fun p hp ↦
      nullLambdaSeries_le_three_div_analyticScale hp
  · exact hupperLimit

end

end LogdetLean
