import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
/-!
# The scalar third-derivative estimate in the Wishart transform

This module formalizes the elementary complex inequality used after
diagonalizing the covariance matrix in Appendix F of the sharp
log-determinant manuscript.  The displayed rational function is exactly the
right-hand side of equation `dlambda-third` there.  Its derivation by three
complex differentiations belongs in the later transform module; the present
file proves the global imaginary-axis bound, including the nearly singular
case `r \downarrow 0`.

For provenance, the formula being bounded is the scalar summand obtained from

`d_lambda(z) = -(alpha+z) Log(1 + z lambda/(alpha+z))`,

with `r=1+lambda`; compare Zhao (2026), arXiv:2608.00565v1, Appendix F, and
the new manuscript's equations `dlambda`--`DA-third-bound`.  The proof below
is a direct Lean derivation from `|alpha+i u| >= alpha`.
-/

namespace LogdetLean

noncomputable section

open Complex

private theorem norm_ofReal_add_mul_I_ge
    {alpha u : ℝ} (halpha : 0 ≤ alpha) :
    alpha ≤ ‖(alpha : ℂ) + (u : ℂ) * I‖ := by
  have h := Complex.abs_re_le_norm ((alpha : ℂ) + (u : ℂ) * I)
  simpa [abs_of_nonneg halpha] using h

private theorem norm_pow_mul_pow_ge
    {alpha u v : ℝ} (halpha : 0 ≤ alpha) (k l : ℕ) :
    alpha ^ (k + l) ≤
      ‖((alpha : ℂ) + (u : ℂ) * I) ^ k *
        ((alpha : ℂ) + (v : ℂ) * I) ^ l‖ := by
  rw [norm_mul, norm_pow, norm_pow, pow_add]
  exact mul_le_mul
    (pow_le_pow_left₀ halpha (norm_ofReal_add_mul_I_ge halpha) k)
    (pow_le_pow_left₀ halpha (norm_ofReal_add_mul_I_ge halpha) l)
    (pow_nonneg halpha _) (pow_nonneg (norm_nonneg _) _)

/-- The scalar rational expression obtained by differentiating the Wishart
log-transform three times. -/
def wishartScalarThirdExpression
    (alpha r lambda u : ℝ) : ℂ :=
  -(3 * alpha ^ 2 * lambda ^ 2 : ℝ) /
      (((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
        ((alpha : ℂ) + (r * u : ℂ) * I) ^ 2) -
    (2 * alpha ^ 3 * lambda ^ 3 : ℝ) /
      (((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
        ((alpha : ℂ) + (r * u : ℂ) * I) ^ 3)

private theorem first_wishart_scalar_term_norm_le
    {alpha r lambda u : ℝ} (halpha : 0 < alpha) :
    ‖(-(3 * alpha ^ 2 * lambda ^ 2 : ℝ) : ℂ) /
        (((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
          ((alpha : ℂ) + (r * u : ℂ) * I) ^ 2)‖
      ≤ 3 * lambda ^ 2 / alpha ^ 2 := by
  have hden : alpha ^ 4 ≤
      ‖((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
        ((alpha : ℂ) + (r * u : ℂ) * I) ^ 2‖ := by
    simpa using norm_pow_mul_pow_ge halpha.le (u := u) (v := r * u) 2 2
  have hdenpos : 0 <
      ‖((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
        ((alpha : ℂ) + (r * u : ℂ) * I) ^ 2‖ :=
    lt_of_lt_of_le (pow_pos halpha 4) hden
  rw [norm_div]
  have hnum : ‖(-(3 * alpha ^ 2 * lambda ^ 2 : ℝ) : ℂ)‖ =
      3 * alpha ^ 2 * lambda ^ 2 := by
    rw [norm_neg, norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ 3 * alpha ^ 2 * lambda ^ 2)]
  rw [hnum]
  have ha2 : 0 < alpha ^ 2 := pow_pos halpha 2
  apply (div_le_div_iff₀ hdenpos ha2).2
  calc
    (3 * alpha ^ 2 * lambda ^ 2) * alpha ^ 2 =
        (3 * lambda ^ 2) * alpha ^ 4 := by ring
    _ ≤ (3 * lambda ^ 2) *
        ‖((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
          ((alpha : ℂ) + (r * u : ℂ) * I) ^ 2‖ := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

private theorem second_wishart_scalar_term_norm_le
    {alpha r lambda u : ℝ} (halpha : 0 < alpha) :
    ‖((2 * alpha ^ 3 * lambda ^ 3 : ℝ) : ℂ) /
        (((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
          ((alpha : ℂ) + (r * u : ℂ) * I) ^ 3)‖
      ≤ 2 * |lambda| ^ 3 / alpha ^ 2 := by
  have hden : alpha ^ 5 ≤
      ‖((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
        ((alpha : ℂ) + (r * u : ℂ) * I) ^ 3‖ := by
    simpa using norm_pow_mul_pow_ge halpha.le (u := u) (v := r * u) 2 3
  have hdenpos : 0 <
      ‖((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
        ((alpha : ℂ) + (r * u : ℂ) * I) ^ 3‖ :=
    lt_of_lt_of_le (pow_pos halpha 5) hden
  rw [norm_div]
  have hnum : ‖((2 * alpha ^ 3 * lambda ^ 3 : ℝ) : ℂ)‖ =
      2 * alpha ^ 3 * |lambda| ^ 3 := by
    rw [norm_real]
    simp [abs_of_pos halpha]
  rw [hnum]
  have ha2 : 0 < alpha ^ 2 := pow_pos halpha 2
  apply (div_le_div_iff₀ hdenpos ha2).2
  calc
    (2 * alpha ^ 3 * |lambda| ^ 3) * alpha ^ 2 =
        (2 * |lambda| ^ 3) * alpha ^ 5 := by ring
    _ ≤ (2 * |lambda| ^ 3) *
        ‖((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
          ((alpha : ℂ) + (r * u : ℂ) * I) ^ 3‖ := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

/-- Uniform imaginary-axis estimate for one eigenvalue contribution.  Notice
that no lower bound on `r` is needed; only `alpha>0` matters. -/
theorem norm_wishartScalarThirdExpression_le
    {alpha r lambda u : ℝ} (halpha : 0 < alpha) :
    ‖wishartScalarThirdExpression alpha r lambda u‖ ≤
      (3 * lambda ^ 2 + 2 * |lambda| ^ 3) / alpha ^ 2 := by
  unfold wishartScalarThirdExpression
  calc
    ‖(-(3 * alpha ^ 2 * lambda ^ 2 : ℝ) : ℂ) /
          (((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
            ((alpha : ℂ) + (r * u : ℂ) * I) ^ 2) -
        (2 * alpha ^ 3 * lambda ^ 3 : ℝ) /
          (((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
            ((alpha : ℂ) + (r * u : ℂ) * I) ^ 3)‖
      ≤ ‖(-(3 * alpha ^ 2 * lambda ^ 2 : ℝ) : ℂ) /
          (((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
            ((alpha : ℂ) + (r * u : ℂ) * I) ^ 2)‖ +
        ‖((2 * alpha ^ 3 * lambda ^ 3 : ℝ) : ℂ) /
          (((alpha : ℂ) + (u : ℂ) * I) ^ 2 *
            ((alpha : ℂ) + (r * u : ℂ) * I) ^ 3)‖ := norm_sub_le _ _
    _ ≤ 3 * lambda ^ 2 / alpha ^ 2 +
        2 * |lambda| ^ 3 / alpha ^ 2 := add_le_add
      (first_wishart_scalar_term_norm_le halpha)
      (second_wishart_scalar_term_norm_le halpha)
    _ = (3 * lambda ^ 2 + 2 * |lambda| ^ 3) / alpha ^ 2 := by ring

/-- The same estimate after substituting `alpha=m/2`, in the normalization
used by the sample-correlation papers. -/
theorem norm_wishartScalarThirdExpression_half_dimension_le
    {m r lambda u : ℝ} (hm : 0 < m) :
    ‖wishartScalarThirdExpression (m / 2) r lambda u‖ ≤
      (12 * lambda ^ 2 + 8 * |lambda| ^ 3) / m ^ 2 := by
  have h := norm_wishartScalarThirdExpression_le
    (alpha := m / 2) (r := r) (lambda := lambda) (u := u) (by positivity)
  convert h using 1
  field_simp
  ring

/-- Summed eigenvalue form of the global third-derivative estimate.  This is
the finite-dimensional analytic inequality that becomes
`(12 tr A^2 + 8 tr |A|^3)/m^2` after the spectral theorem identifies the two
real sums with matrix traces. -/
theorem norm_sum_wishartScalarThirdExpression_half_dimension_le
    {ι : Type*} {s : Finset ι} {m u : ℝ} (lambda : ι → ℝ)
    (hm : 0 < m) :
    ‖∑ i ∈ s, wishartScalarThirdExpression (m / 2)
        (1 + lambda i) (lambda i) u‖ ≤
      (12 * ∑ i ∈ s, lambda i ^ 2) / m ^ 2 +
        (8 * ∑ i ∈ s, |lambda i| ^ 3) / m ^ 2 := by
  calc
    ‖∑ i ∈ s, wishartScalarThirdExpression (m / 2)
        (1 + lambda i) (lambda i) u‖ ≤
        ∑ i ∈ s, ‖wishartScalarThirdExpression (m / 2)
          (1 + lambda i) (lambda i) u‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s,
        (12 * lambda i ^ 2 + 8 * |lambda i| ^ 3) / m ^ 2 := by
      exact Finset.sum_le_sum fun i _hi ↦
        norm_wishartScalarThirdExpression_half_dimension_le hm
    _ = (12 * ∑ i ∈ s, lambda i ^ 2) / m ^ 2 +
        (8 * ∑ i ∈ s, |lambda i| ^ 3) / m ^ 2 := by
      calc
        ∑ i ∈ s, (12 * lambda i ^ 2 + 8 * |lambda i| ^ 3) / m ^ 2 =
            (∑ i ∈ s, (12 * lambda i ^ 2 + 8 * |lambda i| ^ 3)) /
              m ^ 2 := by rw [Finset.sum_div]
        _ = ((12 * ∑ i ∈ s, lambda i ^ 2) +
              (8 * ∑ i ∈ s, |lambda i| ^ 3)) / m ^ 2 := by
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = (12 * ∑ i ∈ s, lambda i ^ 2) / m ^ 2 +
            (8 * ∑ i ∈ s, |lambda i| ^ 3) / m ^ 2 := add_div _ _ _

end

end LogdetLean
