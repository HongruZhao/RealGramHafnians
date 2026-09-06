import LogdetLean.KibbleCovarianceSeries
import LogdetLean.GeneralRNonlinearRemainder
import LogdetLean.NullVA
/-!
# Exact general-correlation variance series and deterministic comparison

This file assembles the coefficient series into the formula denoted
`tau_R^2` in Zhao (2026):

`V_{m,p} + sum_{i != j} c_m(r_ij)`.

The assembly is deterministic.  Using the coefficient-tail theorem in
`KibbleCovarianceSeries`, it proves unconditionally

`0 <= tau_R^2 - (V_{m,p}+2 a_R/m) <= 4 a_R/m^2`

and the relative comparison by `2/m`.  Identifying this expression with the
actual variance of the sample-correlation log determinant additionally uses
the Gaussian/Wishart covariance bridge; that probabilistic bridge is kept
separate and is not assumed here.
-/

namespace LogdetLean

noncomputable section

open scoped BigOperators

open MeasureTheory ProbabilityTheory

/-- Pure covariance algebra behind the exact `tau_R^2` formula.  It cleanly
separates the finite-sum calculation from the three model-specific inputs:
the determinant variance, its covariance with each log radius, and the pair
log-radius covariance. -/
theorem variance_sub_finsetSum_eq_base_add_offDiag
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (L : Ω → ℝ) (q : ι → Ω → ℝ) (V t : ℝ) (c : ι → ι → ℝ)
    (hL : MemLp L 2 μ) (hq : ∀ i, MemLp (q i) 2 μ)
    (hvarL : Var[L; μ] = V + (Fintype.card ι : ℝ) * t)
    (hcovL : ∀ i, cov[L, q i; μ] = t)
    (hcovQ : ∀ i j,
      cov[q i, q j; μ] = if i = j then t else c i j) :
    Var[fun ω ↦ L ω - ∑ i, q i ω; μ] =
      V + ∑ i : ι, ∑ j : ι with i ≠ j, c i j := by
  have hsum : MemLp (fun ω ↦ ∑ i, q i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ ↦ hq i)
  rw [variance_fun_sub hL hsum, covariance_fun_sum_right hq hL,
    variance_fun_sum hq, hvarL]
  simp_rw [hcovL, hcovQ]
  have hfilter (i : ι) : Finset.univ.filter (fun j ↦ i = j) = {i} := by
    ext j
    simp [eq_comm]
  simp_rw [Finset.sum_ite]
  simp_rw [hfilter]
  simp_rw [Finset.sum_add_distrib]
  simp [mul_comm]
  ring

/-- The exact Kibble-series expression for `tau_R^2`. -/
def generalRExactVarianceSeries {p : ℕ} (m : ℕ) (R : CorrelationMatrix p) : ℝ :=
  nullVSeries m p +
    ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
      logRadiusCovarianceSeries m (R.val i j)

/-- The same variance proxy `s_R^2=V_{m,p}+2a_R/m` used in the paper. -/
def generalRSeriesVarianceProxy {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy

private theorem sum_offDiag_first_term {m p : ℕ} (hm : 0 < m)
    (R : CorrelationMatrix p) :
    ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
      2 * (R.val i j) ^ 2 / (m : ℝ) =
        2 * R.deviationEnergy / (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  calc
    ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
        2 * (R.val i j) ^ 2 / (m : ℝ) =
        ∑ i : Fin p, (2 / (m : ℝ)) *
          ∑ j : Fin p with i ≠ j, (R.val i j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (2 / (m : ℝ)) *
        ∑ i : Fin p, ∑ j : Fin p with i ≠ j, (R.val i j) ^ 2 := by
      rw [Finset.mul_sum]
    _ = 2 * R.deviationEnergy / (m : ℝ) := by
      rw [← R.deviationEnergy_eq_sum_offDiag_sq]
      ring

private theorem sum_offDiag_fourth_le_energy {p : ℕ}
    (R : CorrelationMatrix p) :
    ∑ i : Fin p, ∑ j : Fin p with i ≠ j, (R.val i j) ^ 4 ≤
      R.deviationEnergy := by
  rw [R.deviationEnergy_eq_sum_offDiag_sq]
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  have habs := R.abs_apply_le_one i j
  have hsq : (R.val i j) ^ 2 ≤ 1 := by
    simpa [pow_two] using abs_le_one_iff_mul_self_le_one.mp habs
  have hsq0 : 0 ≤ (R.val i j) ^ 2 := sq_nonneg _
  calc
    (R.val i j) ^ 4 = (R.val i j) ^ 2 * (R.val i j) ^ 2 := by ring
    _ ≤ (R.val i j) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hsq hsq0
    _ = (R.val i j) ^ 2 := by ring

private theorem sum_offDiag_remainder_identity {m p : ℕ} (hm : 0 < m)
    (R : CorrelationMatrix p) :
    generalRExactVarianceSeries m R - generalRSeriesVarianceProxy m R =
      ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
        (logRadiusCovarianceSeries m (R.val i j) -
          2 * (R.val i j) ^ 2 / (m : ℝ)) := by
  have hfirst := sum_offDiag_first_term hm R
  unfold generalRExactVarianceSeries generalRSeriesVarianceProxy
    generalRVarianceProxy
  rw [← hfirst]
  simp_rw [Finset.sum_sub_distrib]
  ring

/-- Exact nonnegative comparison with the paper's variance proxy. -/
theorem generalRExactVarianceSeries_sub_proxy_nonneg
    {m p : ℕ} (hm : 2 ≤ m) (R : CorrelationMatrix p) :
    0 ≤ generalRExactVarianceSeries m R -
      generalRSeriesVarianceProxy m R := by
  rw [sum_offDiag_remainder_identity (by omega) R]
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro j _hj
  exact (logRadiusCovarianceSeries_remainder_bounds hm
    (R.abs_apply_le_one i j)).1

/-- Exact `4 a_R/m^2` upper comparison. -/
theorem generalRExactVarianceSeries_sub_proxy_le
    {m p : ℕ} (hm : 2 ≤ m) (R : CorrelationMatrix p) :
    generalRExactVarianceSeries m R - generalRSeriesVarianceProxy m R ≤
      4 * R.deviationEnergy / (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by positivity
  rw [sum_offDiag_remainder_identity (by omega) R]
  calc
    ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
        (logRadiusCovarianceSeries m (R.val i j) -
          2 * (R.val i j) ^ 2 / (m : ℝ)) ≤
        ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
          4 * (R.val i j) ^ 4 / (m : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact (logRadiusCovarianceSeries_remainder_bounds hm
        (R.abs_apply_le_one i j)).2
    _ = (4 / (m : ℝ) ^ 2) *
        ∑ i : Fin p, ∑ j : Fin p with i ≠ j, (R.val i j) ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ (4 / (m : ℝ) ^ 2) * R.deviationEnergy := by
      exact mul_le_mul_of_nonneg_left (sum_offDiag_fourth_le_energy R)
        (by positivity)
    _ = 4 * R.deviationEnergy / (m : ℝ) ^ 2 := by ring

/-- The combined two-sided exact comparison. -/
theorem generalRExactVarianceSeries_proxy_bounds
    {m p : ℕ} (hm : 2 ≤ m) (R : CorrelationMatrix p) :
    0 ≤ generalRExactVarianceSeries m R - generalRSeriesVarianceProxy m R ∧
      generalRExactVarianceSeries m R - generalRSeriesVarianceProxy m R ≤
        4 * R.deviationEnergy / (m : ℝ) ^ 2 :=
  ⟨generalRExactVarianceSeries_sub_proxy_nonneg hm R,
    generalRExactVarianceSeries_sub_proxy_le hm R⟩

/-- The relative excess is at most `2/m`, exactly as in Proposition 3.2. -/
theorem generalRExactVarianceSeries_relative_excess_le
    {m p : ℕ} (hm : 2 ≤ m) (hpm : p ≤ m) (R : CorrelationMatrix p) :
    generalRExactVarianceSeries m R - generalRSeriesVarianceProxy m R ≤
      (2 / (m : ℝ)) * generalRSeriesVarianceProxy m R := by
  exact variance_proxy_relative_excess_le (by omega)
    (nullVSeries_nonneg hpm) R.deviationEnergy_nonneg
    (generalRExactVarianceSeries_sub_proxy_nonneg hm R)
    (generalRExactVarianceSeries_sub_proxy_le hm R)

/-- A transparent transfer theorem for the eventual actual-variance bridge:
any quantity proved equal to the exact Kibble-series expression inherits the
same sharp comparison immediately. -/
theorem variance_proxy_bounds_of_eq_generalRExactVarianceSeries
    {m p : ℕ} {tauSq : ℝ} (hm : 2 ≤ m) (R : CorrelationMatrix p)
    (htau : tauSq = generalRExactVarianceSeries m R) :
    0 ≤ tauSq - generalRSeriesVarianceProxy m R ∧
      tauSq - generalRSeriesVarianceProxy m R ≤
        4 * R.deviationEnergy / (m : ℝ) ^ 2 := by
  rw [htau]
  exact generalRExactVarianceSeries_proxy_bounds hm R

end

end LogdetLean
