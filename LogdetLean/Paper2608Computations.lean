import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
/-!
# Reusable deterministic computations for arXiv:2608.00565

This file formalizes elementary algebraic steps used in Hongru Zhao,
"On the Log Determinant of Sample Correlation Matrices under Gaussianity"
(arXiv:2608.00565v1, 2026).  These statements are not probabilistic inputs:
they are direct Lean proofs of the variance-proxy and Lyapunov bookkeeping
appearing in Proposition 3.2, Lemma 5.6, and Appendix D.

The formulas are also reusable in the sharper Berry--Esseen project.  No
claim of mathematical originality is made.  See `PROVENANCE.md` for the
project-wide credit and exact-source policy.
-/

namespace LogdetLean

open scoped BigOperators

noncomputable section

/-- The variance proxy from equation (3.3) of arXiv:2608.00565v1. -/
def generalRVarianceProxy (m : ℕ) (v a : ℝ) : ℝ :=
  v + 2 * a / (m : ℝ)

/-- The elementary null center from equation (3.7), written for real
parameters so its algebra can be reused independently of natural casts. -/
def elementaryNullCenterReal (m p : ℝ) : ℝ :=
  (p - m + 1 / 2) * Real.log (1 - p / m) - ((m - 1) / m) * p

/-- The elementary null variance from equation (3.8). -/
def elementaryNullVarianceReal (m p : ℝ) : ℝ :=
  -2 * (p / m + Real.log (1 - p / m))

/-- The logarithmic gap variable `L=log(m/d)` used in Appendix E. -/
def gapLogReal (m d : ℝ) : ℝ := Real.log (m / d)

/-- Exact rewriting (E.1) of the elementary center after putting `d=m-p`. -/
theorem elementaryNullCenterReal_gap_rewrite
    {m p d : ℝ} (hm : 0 < m) (hd : 0 < d) (hgap : p = m - d) :
    elementaryNullCenterReal m p =
      (d - 1 / 2) * gapLogReal m d - p + p / m := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hone : 1 - p / m = d / m := by
    rw [hgap]
    field_simp
    ring
  have hlog : Real.log (d / m) = -gapLogReal m d := by
    rw [gapLogReal, Real.log_div hd0 hm0, Real.log_div hm0 hd0]
    ring
  unfold elementaryNullCenterReal
  rw [hone, hlog, hgap]
  field_simp
  ring

/-- Exact rewriting (E.1) of the elementary variance. -/
theorem elementaryNullVarianceReal_gap_rewrite
    {m p d : ℝ} (hm : 0 < m) (hd : 0 < d) (hgap : p = m - d) :
    elementaryNullVarianceReal m p =
      2 * (gapLogReal m d - p / m) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hone : 1 - p / m = d / m := by
    rw [hgap]
    field_simp
    ring
  have hlog : Real.log (d / m) = -gapLogReal m d := by
    rw [gapLogReal, Real.log_div hd0 hm0, Real.log_div hm0 hd0]
    ring
  unfold elementaryNullVarianceReal
  rw [hone, hlog]
  ring

/-- The variance proxy is nonnegative when both of its components are. -/
theorem generalRVarianceProxy_nonneg {m : ℕ} {v a : ℝ}
    (hv : 0 ≤ v) (ha : 0 ≤ a) :
    0 ≤ generalRVarianceProxy m v a := by
  unfold generalRVarianceProxy
  positivity

/-- Adding the same nonnegative variance contribution to numerator and
denominator cannot enlarge their relative discrepancy.  This is the exact
algebraic step used at the end of Lemma 5.6. -/
theorem abs_ratio_add_same_nonneg_le {v s c : ℝ}
    (hs : 0 < s) (hc : 0 ≤ c) :
    |(v + c) / (s + c) - 1| ≤ |v / s - 1| := by
  have hsc : 0 < s + c := add_pos_of_pos_of_nonneg hs hc
  rw [div_sub_one (ne_of_gt hsc), div_sub_one (ne_of_gt hs)]
  simp only [add_sub_add_right_eq_sub]
  rw [abs_div, abs_div]
  have hsabs : |s| = s := abs_of_pos hs
  have hscabs : |s + c| = s + c := abs_of_pos hsc
  rw [hsabs, hscabs]
  apply (div_le_div_iff₀ hsc hs).2
  nlinarith [abs_nonneg (v - s)]

/-- If an exact variance differs from the proxy by at most `4a/m^2`, then
its relative excess over the proxy is at most `2/m`.  This is the last
calculation in Proposition 3.2. -/
theorem variance_proxy_relative_excess_le
    {m : ℕ} {v a tauSq : ℝ}
    (hm : 0 < m) (hv : 0 ≤ v) (ha : 0 ≤ a)
    (hlower : 0 ≤ tauSq - generalRVarianceProxy m v a)
    (hupper : tauSq - generalRVarianceProxy m v a ≤
      4 * a / (m : ℝ) ^ 2) :
    tauSq - generalRVarianceProxy m v a ≤
      (2 / (m : ℝ)) * generalRVarianceProxy m v a := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  by_cases ha0 : a = 0
  · subst a
    have hz : tauSq - generalRVarianceProxy m v 0 ≤ 0 := by
      simpa using hupper
    exact hz.trans (mul_nonneg (by positivity)
      (generalRVarianceProxy_nonneg hv (le_refl 0)))
  · have hproxy : 2 * a / (m : ℝ) ≤ generalRVarianceProxy m v a := by
      unfold generalRVarianceProxy
      linarith
    calc
      tauSq - generalRVarianceProxy m v a ≤ 4 * a / (m : ℝ) ^ 2 := hupper
      _ = (2 / (m : ℝ)) * (2 * a / (m : ℝ)) := by
        field_simp
        ring
      _ ≤ (2 / (m : ℝ)) * generalRVarianceProxy m v a := by
        gcongr

/-- Pointwise bounded nonnegative summands satisfy
`sum w_i^2 ≤ W * sum w_i`.  This is the finite-sum estimate used in the
Lyapunov calculation in Appendix D. -/
theorem sum_sq_le_bound_mul_sum
    {ι : Type*} {s : Finset ι} {w : ι → ℝ} {W : ℝ}
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hwW : ∀ i ∈ s, w i ≤ W) :
    ∑ i ∈ s, (w i) ^ 2 ≤ W * ∑ i ∈ s, w i := by
  calc
    ∑ i ∈ s, (w i) ^ 2 ≤ ∑ i ∈ s, W * w i := by
      gcongr with i hi
      nlinarith [hw0 i hi, hwW i hi]
    _ = W * ∑ i ∈ s, w i := by
      rw [Finset.mul_sum]

/-- Entrywise correlations satisfy the fourth-power comparison used in
equations (5.11) and (C.3): if `|r_i| ≤ 1`, then the sum of fourth powers is
at most the sum of squares. -/
theorem sum_fourth_le_sum_sq_of_abs_le_one
    {ι : Type*} {s : Finset ι} {r : ι → ℝ}
    (hr : ∀ i ∈ s, |r i| ≤ 1) :
    ∑ i ∈ s, (r i) ^ 4 ≤ ∑ i ∈ s, (r i) ^ 2 := by
  refine Finset.sum_le_sum ?_
  intro i hi
  have hsq : (r i) ^ 2 ≤ 1 := by
    simpa [pow_two] using
      (abs_le_one_iff_mul_self_le_one.mp (hr i hi))
  have hsq0 : 0 ≤ (r i) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsq hsq0
  calc
    (r i) ^ 4 = (r i) ^ 2 * (r i) ^ 2 := by ring
    _ ≤ (r i) ^ 2 * 1 := hmul
    _ = (r i) ^ 2 := by ring

/-- If `R=I+A` and `tr(A)=0`, then
`tr(R^2)=card+tr(A^2)`.  This is the matrix algebra in equation (5.11). -/
theorem trace_one_add_square_of_trace_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (htrace : Matrix.trace A = 0) :
    Matrix.trace ((1 + A) * (1 + A)) =
      (Fintype.card ι : ℝ) + Matrix.trace (A * A) := by
  calc
    Matrix.trace ((1 + A) * (1 + A)) =
        Matrix.trace (1 + A + A + A * A) := by
      congr 1
      noncomm_ring
    _ = (Fintype.card ι : ℝ) + Matrix.trace (A * A) := by
      rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
        Matrix.trace_one, htrace]
      simp

/-- Abstract Lyapunov bookkeeping: fourth moments of the form
`d_i + 3 w_i^2` are controlled by the fourth-cumulant sum and the largest
variance summand.  This is the deterministic inequality on page 28 of
arXiv:2608.00565v1. -/
theorem lyapunov_fourth_sum_bound
    {ι : Type*} {s : Finset ι} {w d : ι → ℝ} {W V : ℝ}
    (hV : 0 < V) (hVsum : ∑ i ∈ s, w i = V)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hwW : ∀ i ∈ s, w i ≤ W) :
    (∑ i ∈ s, (d i + 3 * (w i) ^ 2)) / V ^ 2 ≤
      (∑ i ∈ s, d i) / V ^ 2 + 3 * W / V := by
  have hsq := sum_sq_le_bound_mul_sum (s := s) hw0 hwW
  rw [hVsum] at hsq
  have hVne : V ≠ 0 := ne_of_gt hV
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdiv : (3 * ∑ i ∈ s, (w i) ^ 2) / V ^ 2 ≤ 3 * W / V := by
    apply (div_le_iff₀ (sq_pos_of_pos hV)).2
    calc
      3 * ∑ i ∈ s, (w i) ^ 2 ≤ 3 * (W * V) := by nlinarith
      _ = (3 * W / V) * V ^ 2 := by
        field_simp
  rw [add_div]
  simpa [add_comm] using
    (add_le_add_right hdiv ((∑ i ∈ s, d i) / V ^ 2))

end

end LogdetLean
