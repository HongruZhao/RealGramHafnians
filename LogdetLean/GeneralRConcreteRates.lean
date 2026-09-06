import LogdetLean.GeneralRLeadingVarianceAlgebra
import LogdetLean.GeneralRRateAlgebra
import LogdetLean.CorrelationEigenvalues
import Mathlib.Tactic
/-!
# Concrete general-correlation rate parameters

This module specializes the abstract rate algebra to a correlation matrix.
It is shared by the quantitative Berry--Esseen theorem and the qualitative
CLT obtained when these rates tend to zero.
-/

namespace LogdetLean

noncomputable section

open Filter
open scoped BigOperators

/-- Squared proxy scale `s_R²=V_{m,p}+2a_R/m`. -/
def generalRProxyVarianceSq {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy

/-- Normalized nonlinear-remainder variance rate
`Q_R=4(p+a_R)/(m²s_R²)`. -/
def generalRNonlinearRateQ {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRemainderRateQ (m : ℝ) (p : ℝ) R.deviationEnergy
    (generalRProxyVarianceSq m R)

/-- The positive cube-root scale used in the perturbation theorem. -/
def generalRNonlinearCubeRootRate {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  (generalRNonlinearRateQ m R) ^ ((3 : ℝ)⁻¹)

/-- Cubic spectral rate
`rho_R=sum_i |lambda_i(R-I)|³/(m²s_R³)`. -/
def generalRSpectralCubicRate {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRCubicRateRho (m : ℝ)
    (∑ i, |R.deviationEigenvalues i| ^ 3)
    (generalRProxyScale m R)

theorem generalRProxyVarianceSq_pos
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 < generalRProxyVarianceSq m R := by
  exact generalRVarianceProxy_null_energy_pos h R

theorem generalRProxyVarianceSq_eq_scale_sq
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRProxyVarianceSq m R = generalRProxyScale m R ^ 2 := by
  symm
  exact generalRProxyScale_sq h R

theorem generalRNonlinearRateQ_pos
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 < generalRNonlinearRateQ m R := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hs := generalRProxyVarianceSq_pos h R
  unfold generalRNonlinearRateQ generalRemainderRateQ
  exact div_pos
    (mul_pos (by norm_num)
      (add_pos_of_pos_of_nonneg hpR R.deviationEnergy_nonneg))
    (mul_pos (sq_pos_of_pos hmR) hs)

theorem generalRNonlinearCubeRootRate_pos
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 < generalRNonlinearCubeRootRate m R := by
  unfold generalRNonlinearCubeRootRate
  exact Real.rpow_pos_of_pos (generalRNonlinearRateQ_pos h R) _

@[simp]
theorem generalRNonlinearCubeRootRate_cube
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRNonlinearCubeRootRate m R ^ 3 =
      generalRNonlinearRateQ m R := by
  unfold generalRNonlinearCubeRootRate
  exact Real.rpow_inv_natCast_pow
    (generalRNonlinearRateQ_pos h R).le (by norm_num)

/-- Uniform dimension-only simplification of the nonlinear rate. -/
theorem generalRNonlinearRateQ_le_simple
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRNonlinearRateQ m R ≤
      4 / ((p : ℝ) - 1) + 2 / (m : ℝ) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hs := generalRProxyVarianceSq_pos h R
  have hnull0 := nullVSeries_lower_p_mul_pred_div_m_sq h
  have hnull :
      (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
        generalRProxyVarianceSq m R := by
    unfold generalRProxyVarianceSq generalRVarianceProxy
    exact hnull0.trans (le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) R.deviationEnergy_nonneg)
        (Nat.cast_nonneg _)))
  have hcorr :
      2 * R.deviationEnergy / (m : ℝ) ≤
        generalRProxyVarianceSq m R := by
    unfold generalRProxyVarianceSq generalRVarianceProxy
    exact le_add_of_nonneg_left (nullVSeries_nonneg hpm)
  exact generalRemainderRateQ_le_simple hmR hpR hs hnull hcorr

/-- Uniform arbitrary-correlation simplification of the cubic spectral rate. -/
theorem generalRSpectralCubicRate_le_simple
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRSpectralCubicRate m R ≤
      1 / (2 * Real.sqrt 2 * Real.sqrt (m : ℝ)) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hs : 0 < generalRProxyScale m R := generalRProxyScale_pos h R
  have hscale :
      2 * (∑ i, R.deviationEigenvalues i ^ 2) / (m : ℝ) ≤
        generalRProxyScale m R ^ 2 := by
    rw [generalRProxyScale_sq h R,
      ← R.deviationEnergy_eq_sum_eigenvalues_sq]
    unfold generalRVarianceProxy
    exact le_add_of_nonneg_left (nullVSeries_nonneg hpm)
  exact generalRCubicRateRho_eigenvalues_le_simple
    (index := Finset.univ) R.deviationEigenvalues hmR hs hscale

/-- `Q_R` vanishes uniformly over arbitrary correlation-matrix arrays. -/
theorem tendsto_generalRNonlinearRateQ_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ generalRNonlinearRateQ (m p) (R p))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [hadm] with p hp
    unfold generalRNonlinearRateQ generalRemainderRateQ
    have hs : 0 < generalRProxyVarianceSq (m p) (R p) :=
      generalRProxyVarianceSq_pos hp (R p)
    exact div_nonneg
      (mul_nonneg (by norm_num)
        (add_nonneg (Nat.cast_nonneg _) (R p).deviationEnergy_nonneg))
      (mul_nonneg (sq_nonneg _) hs.le)
  · filter_upwards [hadm] with p hp
    exact generalRNonlinearRateQ_le_simple hp (R p)
  · exact tendsto_generalRemainder_simple_envelope_zero m hadm

/-- The cube-root perturbation rate also tends uniformly to zero. -/
theorem tendsto_generalRNonlinearCubeRootRate_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ generalRNonlinearCubeRootRate (m p) (R p))
      atTop (nhds 0) := by
  have hQ := tendsto_generalRNonlinearRateQ_zero m R hadm
  unfold generalRNonlinearCubeRootRate
  have hcont := Real.continuousAt_rpow_const (0 : ℝ) ((3 : ℝ)⁻¹)
    (Or.inr (by positivity : (0 : ℝ) ≤ (3 : ℝ)⁻¹))
  simpa [Function.comp_def] using hcont.tendsto.comp hQ

/-- `rho_R` vanishes uniformly over arbitrary correlation-matrix arrays. -/
theorem tendsto_generalRSpectralCubicRate_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ generalRSpectralCubicRate (m p) (R p))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [hadm] with p hp
    unfold generalRSpectralCubicRate generalRCubicRateRho
    have hs := generalRProxyScale_pos hp (R p)
    exact div_nonneg
      (Finset.sum_nonneg fun i _ ↦ pow_nonneg (abs_nonneg _) 3)
      (mul_nonneg (sq_nonneg _) (pow_nonneg hs.le 3))
  · filter_upwards [hadm] with p hp
    exact generalRSpectralCubicRate_le_simple hp (R p)
  · exact tendsto_generalRCubic_simple_envelope_zero m
      (hadm.mono fun p hp ↦ hp.2)

end

end LogdetLean
