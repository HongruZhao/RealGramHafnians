import LogdetLean.FullTarget
import LogdetLean.PolygammaSeries
import Mathlib.Tactic
/-!
# Positive series candidates for the null variance and third-cumulant scale

This file constructs the finite sums of absolutely convergent positive series
that evaluate the quantities called `V_{m,p}` and `A_{m,p}` in the paper.
Nothing here uses a probabilistic limit or an asymptotic approximation.

The definitions are deliberately named `nullVSeries` and `nullASeries`.
Identifying them with the measure moments `nullVariance` and
`nullThirdMagnitude` requires the separate log-Beta cumulant theorem; that
probabilistic identification is **not** asserted in this file.

For `2 ≤ p ≤ m`, put

* `a_j = (m-j+1)/2`,
* `M = m/2`,
* `V_{m,p} = ∑_j (ψ₁(a_j)-ψ₁(M))`, and
* `A_{m,p} = ∑_j ((-ψ₂)(a_j)-(-ψ₂)(M))`.

The series definitions in `PolygammaSeries` make every summand visibly
positive: for `j ≥ 2`, one has `0 < a_j < M`, and inverse powers strictly
decrease as their argument increases.

The exact finite cumulant formulas being represented are Xie--Sun (2021),
equations (5)--(7), printed pp. 430--431. This file independently proves the
finite-series algebra and positivity; the separate probabilistic
identification is in BetaCumulantSeries. See PROVENANCE.md.
-/

namespace LogdetLean

open scoped BigOperators

noncomputable section

/-- The common beta-shape sum `M=m/2`. -/
def betaShapeTotal (m : ℕ) : ℝ := (m : ℝ) / 2

/-- The finite-series candidate for the null variance `V_{m,p}`. -/
def nullVSeries (m p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 p,
    (trigammaSeries (betaShapeA m j) - trigammaSeries (betaShapeTotal m))

/-- The finite-series candidate for the positive magnitude `A_{m,p}`. -/
def nullASeries (m p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 p,
    (negPsiTwoSeries (betaShapeA m j) - negPsiTwoSeries (betaShapeTotal m))

/-- The dimensionless standardized third-cumulant magnitude `A/V^(3/2)`.
The value is set by ordinary real division, so this definition also makes
sense outside the admissible range; positivity below shows its denominator is
nonzero in the range used in the paper. -/
def nullLambdaSeries (m p : ℕ) : ℝ :=
  nullASeries m p / nullVSeries m p ^ (3 / 2 : ℝ)

/-- Every summation index has a positive lower beta shape. -/
theorem betaShapeA_pos_of_mem_Icc {m p j : ℕ} (hpm : p ≤ m)
    (hj : j ∈ Finset.Icc 2 p) :
    0 < betaShapeA m j := by
  exact betaShapeA_pos_of_le (le_trans (Finset.mem_Icc.mp hj).2 hpm)

/-- The common beta-shape sum is positive in the nontrivial range. -/
theorem betaShapeTotal_pos {m p : ℕ} (h : Admissible m p) :
    0 < betaShapeTotal m := by
  unfold betaShapeTotal
  rcases h with ⟨hp, hpm⟩
  have hm : 0 < m := by omega
  positivity

/-- For every actual beta factor, its lower shape is strictly below `m/2`. -/
theorem betaShapeA_lt_total {m j : ℕ} (hj : 2 ≤ j) :
    betaShapeA m j < betaShapeTotal m := by
  unfold betaShapeA betaShapeTotal
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  linarith

/-- Every inner difference series in the formula for `V_{m,p}` converges. -/
theorem summable_nullVSeries_inner {m p j : ℕ} (h : Admissible m p)
    (hj : j ∈ Finset.Icc 2 p) :
    Summable (fun l : ℕ ↦
      1 / (betaShapeA m j + (l : ℝ)) ^ 2 -
        1 / (betaShapeTotal m + (l : ℝ)) ^ 2) := by
  exact (summable_trigammaSeries_terms
      (betaShapeA_pos_of_mem_Icc h.2 hj)).sub
    (summable_trigammaSeries_terms (betaShapeTotal_pos h))

/-- Every inner difference series in the formula for `A_{m,p}` converges. -/
theorem summable_nullASeries_inner {m p j : ℕ} (h : Admissible m p)
    (hj : j ∈ Finset.Icc 2 p) :
    Summable (fun l : ℕ ↦
      1 / (betaShapeA m j + (l : ℝ)) ^ 3 -
        1 / (betaShapeTotal m + (l : ℝ)) ^ 3) := by
  exact (summable_negPsiTwoSeries_terms
      (betaShapeA_pos_of_mem_Icc h.2 hj)).sub
    (summable_negPsiTwoSeries_terms (betaShapeTotal_pos h))

/-- Each exact variance summand is nonnegative. -/
theorem nullVSeries_summand_nonneg {m p j : ℕ} (hpm : p ≤ m)
    (hj : j ∈ Finset.Icc 2 p) :
    0 ≤ trigammaSeries (betaShapeA m j) -
      trigammaSeries (betaShapeTotal m) := by
  have haj : 0 < betaShapeA m j := betaShapeA_pos_of_mem_Icc hpm hj
  have hlt : betaShapeA m j < betaShapeTotal m :=
    betaShapeA_lt_total (Finset.mem_Icc.mp hj).1
  exact sub_nonneg.mpr (trigammaSeries_antitone haj hlt.le)

/-- Each exact third-cumulant-magnitude summand is nonnegative. -/
theorem nullASeries_summand_nonneg {m p j : ℕ} (hpm : p ≤ m)
    (hj : j ∈ Finset.Icc 2 p) :
    0 ≤ negPsiTwoSeries (betaShapeA m j) -
      negPsiTwoSeries (betaShapeTotal m) := by
  have haj : 0 < betaShapeA m j := betaShapeA_pos_of_mem_Icc hpm hj
  have hlt : betaShapeA m j < betaShapeTotal m :=
    betaShapeA_lt_total (Finset.mem_Icc.mp hj).1
  exact sub_nonneg.mpr (negPsiTwoSeries_antitone haj hlt.le)

/-- `V_{m,p}` is nonnegative whenever the beta-product parameters exist. -/
theorem nullVSeries_nonneg {m p : ℕ} (hpm : p ≤ m) :
    0 ≤ nullVSeries m p := by
  unfold nullVSeries
  exact Finset.sum_nonneg fun j hj ↦ nullVSeries_summand_nonneg hpm hj

/-- `A_{m,p}` is nonnegative whenever the beta-product parameters exist. -/
theorem nullASeries_nonneg {m p : ℕ} (hpm : p ≤ m) :
    0 ≤ nullASeries m p := by
  unfold nullASeries
  exact Finset.sum_nonneg fun j hj ↦ nullASeries_summand_nonneg hpm hj

/-- `V_{m,p}` is strictly positive in the nontrivial range `2 ≤ p ≤ m`. -/
theorem nullVSeries_pos {m p : ℕ} (h : Admissible m p) :
    0 < nullVSeries m p := by
  unfold nullVSeries
  refine Finset.sum_pos' (fun j hj ↦ nullVSeries_summand_nonneg h.2 hj) ?_
  refine ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩, ?_⟩
  have ha : 0 < betaShapeA m 2 :=
    betaShapeA_pos_of_le (le_trans h.1 h.2)
  have hlt : betaShapeA m 2 < betaShapeTotal m := betaShapeA_lt_total le_rfl
  exact sub_pos.mpr (trigammaSeries_strictAnti ha hlt)

/-- `A_{m,p}` is strictly positive in the nontrivial range `2 ≤ p ≤ m`. -/
theorem nullASeries_pos {m p : ℕ} (h : Admissible m p) :
    0 < nullASeries m p := by
  unfold nullASeries
  refine Finset.sum_pos' (fun j hj ↦ nullASeries_summand_nonneg h.2 hj) ?_
  refine ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩, ?_⟩
  have ha : 0 < betaShapeA m 2 :=
    betaShapeA_pos_of_le (le_trans h.1 h.2)
  have hlt : betaShapeA m 2 < betaShapeTotal m := betaShapeA_lt_total le_rfl
  exact sub_pos.mpr (negPsiTwoSeries_strictAnti ha hlt)

/-- The standardized third-cumulant magnitude is strictly positive. -/
theorem nullLambdaSeries_pos {m p : ℕ} (h : Admissible m p) :
    0 < nullLambdaSeries m p := by
  unfold nullLambdaSeries
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hA : 0 < nullASeries m p := nullASeries_pos h
  positivity

/-- Exact double-series computation of `V_{m,p}`. -/
theorem nullVSeries_eq_doubleSeries {m p : ℕ} (h : Admissible m p) :
    nullVSeries m p =
      ∑ j ∈ Finset.Icc 2 p, ∑' l : ℕ,
        (1 / (betaShapeA m j + (l : ℝ)) ^ 2 -
          1 / (betaShapeTotal m + (l : ℝ)) ^ 2) := by
  unfold nullVSeries
  apply Finset.sum_congr rfl
  intro j hj
  exact trigammaSeries_sub (betaShapeA_pos_of_mem_Icc h.2 hj)
    (betaShapeTotal_pos h)

/-- Exact double-series computation of `A_{m,p}`. -/
theorem nullASeries_eq_doubleSeries {m p : ℕ} (h : Admissible m p) :
    nullASeries m p =
      ∑ j ∈ Finset.Icc 2 p, 2 * ∑' l : ℕ,
        (1 / (betaShapeA m j + (l : ℝ)) ^ 3 -
          1 / (betaShapeTotal m + (l : ℝ)) ^ 3) := by
  unfold nullASeries
  apply Finset.sum_congr rfl
  intro j hj
  exact negPsiTwoSeries_sub (betaShapeA_pos_of_mem_Icc h.2 hj)
    (betaShapeTotal_pos h)

/-- The scale used in the first Edgeworth correction is exactly
`A_{m,p}/V_{m,p}^{3/2}`. -/
theorem nullLambdaSeries_eq (m p : ℕ) :
    nullLambdaSeries m p =
      nullASeries m p / nullVSeries m p ^ (3 / 2 : ℝ) := rfl

end

end LogdetLean
