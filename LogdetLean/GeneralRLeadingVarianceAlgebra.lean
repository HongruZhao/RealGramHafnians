import LogdetLean.CorrelationMatrixAlgebra
import LogdetLean.Paper2608Computations
import LogdetLean.ScaleSeparation
import Mathlib.Tactic
/-!
# Variance algebra for the general-correlation leading term

This file isolates the deterministic comparison between the exact variance
of the leading Wishart term and the paper's proxy scale.  The later transform
module proves that the displayed expression really is `Var(M_R)`; no such
probabilistic identification is assumed here.
-/

namespace LogdetLean

noncomputable section

/-- The variance formula for the leading Wishart component:
`w_R^2=s_R^2+p(psi_1(m/2)-2/m)`. -/
def generalRLeadingVarianceSq {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy +
    (p : ℝ) *
      (trigammaSeries (betaShapeTotal m) - 2 / (m : ℝ))

/-- Positive proxy standard deviation `s_R`. -/
def generalRProxyScale {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  Real.sqrt
    (generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy)

/-- Exact standard deviation `w_R` of the leading component, once the
probabilistic variance identity is supplied by the transform module. -/
def generalRLeadingScale {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  Real.sqrt (generalRLeadingVarianceSq m R)

/-- The radial trigamma correction is nonnegative. -/
theorem trigamma_total_sub_two_div_dimension_nonneg
    {m : ℕ} (hm : 0 < m) :
    0 ≤ trigammaSeries (betaShapeTotal m) - 2 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hM : 0 < betaShapeTotal m := by
    unfold betaShapeTotal
    positivity
  have hlower := one_div_le_trigammaSeries hM
  have heq : 1 / betaShapeTotal m = 2 / (m : ℝ) := by
    unfold betaShapeTotal
    field_simp [hmR.ne']
  linarith

/-- The same correction is at most `4/m^2`. -/
theorem trigamma_total_sub_two_div_dimension_le_four_div_sq
    {m : ℕ} (hm : 0 < m) :
    trigammaSeries (betaShapeTotal m) - 2 / (m : ℝ) ≤
      4 / (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hM : 0 < betaShapeTotal m := by
    unfold betaShapeTotal
    positivity
  have hupper := trigammaSeries_le_one_div_add_one_div_sq hM
  have hone : 1 / betaShapeTotal m = 2 / (m : ℝ) := by
    unfold betaShapeTotal
    field_simp [hmR.ne']
  have hsquare : 1 / (betaShapeTotal m) ^ 2 = 4 / (m : ℝ) ^ 2 := by
    unfold betaShapeTotal
    field_simp [hmR.ne']
    ring
  linarith

/-- Exact difference between the leading variance formula and the proxy. -/
theorem generalRLeadingVarianceSq_sub_proxy
    {m p : ℕ} (R : CorrelationMatrix p) :
    generalRLeadingVarianceSq m R -
        generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy =
      (p : ℝ) *
        (trigammaSeries (betaShapeTotal m) - 2 / (m : ℝ)) := by
  unfold generalRLeadingVarianceSq
  ring

/-- The leading variance formula is no smaller than the proxy. -/
theorem generalRLeadingVarianceSq_sub_proxy_nonneg
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 ≤ generalRLeadingVarianceSq m R -
      generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  rw [generalRLeadingVarianceSq_sub_proxy]
  exact mul_nonneg (Nat.cast_nonneg _)
    (trigamma_total_sub_two_div_dimension_nonneg hm)

/-- The absolute scale mismatch is at most `4p/m^2`. -/
theorem generalRLeadingVarianceSq_sub_proxy_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRLeadingVarianceSq m R -
        generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy ≤
      4 * (p : ℝ) / (m : ℝ) ^ 2 := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  rw [generalRLeadingVarianceSq_sub_proxy]
  have hcorr := trigamma_total_sub_two_div_dimension_le_four_div_sq
    hm
  calc
    (p : ℝ) *
        (trigammaSeries (betaShapeTotal m) - 2 / (m : ℝ)) ≤
        (p : ℝ) * (4 / (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hcorr (Nat.cast_nonneg _)
    _ = 4 * (p : ℝ) / (m : ℝ) ^ 2 := by ring

/-- The proxy itself is strictly positive on the admissible range. -/
theorem generalRVarianceProxy_null_energy_pos
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 < generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have henergy : 0 ≤ 2 * R.deviationEnergy / (m : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) R.deviationEnergy_nonneg)
      (Nat.cast_nonneg _)
  unfold generalRVarianceProxy
  exact add_pos_of_pos_of_nonneg (nullVSeries_pos h)
    henergy

/-- Relative scale mismatch, exactly the estimate used to replace `w_R` by
`s_R`: `(w_R^2-s_R^2)/s_R^2 <= 4/(p-1)`. -/
theorem generalRLeadingVarianceSq_relative_excess_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    (generalRLeadingVarianceSq m R -
        generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy) /
        generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy ≤
      4 / ((p : ℝ) - 1) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hpone : 1 < p := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpone
  have hspos := generalRVarianceProxy_null_energy_pos h R
  have hdiff := generalRLeadingVarianceSq_sub_proxy_le h R
  have hV := nullVSeries_lower_p_mul_pred_div_m_sq h
  have hproxy :
      (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
        generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy := by
    unfold generalRVarianceProxy
    exact hV.trans (le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) R.deviationEnergy_nonneg)
        (Nat.cast_nonneg _)))
  have hnum :
      generalRLeadingVarianceSq m R -
          generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy ≤
        4 * (p : ℝ) / (m : ℝ) ^ 2 := hdiff
  apply (div_le_iff₀ hspos).2
  have hden : 0 < (p : ℝ) - 1 := sub_pos.mpr hpR
  have hscaled := mul_le_mul_of_nonneg_left hproxy
    (show 0 ≤ 4 / ((p : ℝ) - 1) by positivity)
  calc
    generalRLeadingVarianceSq m R -
          generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy ≤
        4 * (p : ℝ) / (m : ℝ) ^ 2 := hnum
    _ = (4 / ((p : ℝ) - 1)) *
        ((p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2) := by
      field_simp [hden.ne', hmR.ne']
    _ ≤ (4 / ((p : ℝ) - 1)) *
        generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy := hscaled

/-- Positivity of the exact leading variance formula. -/
theorem generalRLeadingVarianceSq_pos
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 < generalRLeadingVarianceSq m R := by
  have hproxy := generalRVarianceProxy_null_energy_pos h R
  have hdiff := generalRLeadingVarianceSq_sub_proxy_nonneg h R
  linarith

theorem generalRProxyScale_pos
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 < generalRProxyScale m R := by
  unfold generalRProxyScale
  exact Real.sqrt_pos.2 (generalRVarianceProxy_null_energy_pos h R)

theorem generalRLeadingScale_pos
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 < generalRLeadingScale m R := by
  unfold generalRLeadingScale
  exact Real.sqrt_pos.2 (generalRLeadingVarianceSq_pos h R)

@[simp]
theorem generalRProxyScale_sq
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRProxyScale m R ^ 2 =
      generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy := by
  unfold generalRProxyScale
  exact Real.sq_sqrt (generalRVarianceProxy_null_energy_pos h R).le

@[simp]
theorem generalRLeadingScale_sq
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRLeadingScale m R ^ 2 = generalRLeadingVarianceSq m R := by
  unfold generalRLeadingScale
  exact Real.sq_sqrt (generalRLeadingVarianceSq_pos h R).le

/-- Squared-scale hypotheses in exactly the form consumed by
`NormalScaleComparison` and `GeneralRBoundAssembly`. -/
theorem generalRScale_difference_bounds
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 ≤ generalRLeadingScale m R ^ 2 - generalRProxyScale m R ^ 2 ∧
      generalRLeadingScale m R ^ 2 - generalRProxyScale m R ^ 2 ≤
        (4 / ((p : ℝ) - 1)) * generalRProxyScale m R ^ 2 := by
  rw [generalRLeadingScale_sq h R, generalRProxyScale_sq h R]
  constructor
  · exact generalRLeadingVarianceSq_sub_proxy_nonneg h R
  · have hspos := generalRVarianceProxy_null_energy_pos h R
    exact (div_le_iff₀ hspos).mp
      (generalRLeadingVarianceSq_relative_excess_le h R)

end

end LogdetLean
