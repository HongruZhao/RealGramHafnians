import LogdetLean.GammaModulusProduct
import LogdetLean.NullCharacteristicFunction
import LogdetLean.ScaleSeparation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
/-!
# Full-frequency modulus estimates for the null log-determinant law

This file starts from the exact Gamma quotient for the actual standardized
null law and proves the positive Euler product for its squared modulus.  It
then derives raw-frequency monotonicity, local Gaussian damping, and a global
integrable polynomial majorant.  Every statement includes the hard edge
`m = p` under the common assumption `Admissible m p`.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

noncomputable section

set_option linter.style.haveILetI false

/-- Finite product over the Bartlett factors of their infinite Euler
products.  This is the squared modulus at raw frequency `u`. -/
def nullRawModulusSqEulerProduct (m p : ℕ) (u : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 2 p,
    betaModulusEulerProduct (betaShapeA m j) (betaShapeTotal m) u

/-- The corresponding finite sum of logarithmic losses. -/
def nullRawModulusLogLoss (m p : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 p,
    betaModulusLogLoss (betaShapeA m j) (betaShapeTotal m) u

/-- Exact infinite product for one Bartlett log-Beta characteristic factor. -/
theorem norm_logBetaCharacteristicFactor_sq_eq_betaModulusEulerProduct
    {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) (u : ℝ) :
    ‖logBetaCharacteristicFactor m j u‖ ^ 2 =
      betaModulusEulerProduct
        (betaShapeA m j) (betaShapeTotal m) u := by
  rw [← Complex.normSq_eq_norm_sq]
  unfold logBetaCharacteristicFactor
  rw [normSq_complexBetaMellinQuotient_mul_I_eq_betaModulusEulerProduct
    (betaShapeA_pos_of_le hjm) (betaShapeB_pos_of_two_le hj)]
  rw [betaShapeA_add_betaShapeB_eq_total]

/-- Exact `|phi(u)|^2` double product for the uncentered raw log-Beta sum. -/
theorem norm_charFun_logBetaSumLaw_sq_eq_nullRawModulusSqEulerProduct
    {m p : ℕ} (hpm : p ≤ m) (u : ℝ) :
    ‖charFun (logBetaSumLaw m p) u‖ ^ 2 =
      nullRawModulusSqEulerProduct m p u := by
  rw [charFun_logBetaSumLaw_eq_logBetaCharacteristicProduct hpm]
  unfold logBetaCharacteristicProduct nullRawModulusSqEulerProduct
  rw [norm_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  exact norm_logBetaCharacteristicFactor_sq_eq_betaModulusEulerProduct
    ((Finset.mem_Icc.mp hj).2.trans hpm) (Finset.mem_Icc.mp hj).1 u

/-- Centering changes only phase, so the same exact infinite product is the
squared modulus of the centered raw law. -/
theorem norm_charFun_centeredLogBetaSumLaw_sq_eq_nullRawModulusSqEulerProduct
    {m p : ℕ} (hpm : p ≤ m) (u : ℝ) :
    ‖charFun (centeredLogBetaSumLaw m p) u‖ ^ 2 =
      nullRawModulusSqEulerProduct m p u := by
  rw [charFun_centeredLogBetaSumLaw_eq_centeredGammaProduct hpm]
  unfold centeredLogBetaCharacteristicProduct
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul,
    sub_zero, neg_zero, Real.exp_zero, one_mul]
  rw [← charFun_logBetaSumLaw_eq_logBetaCharacteristicProduct hpm]
  exact norm_charFun_logBetaSumLaw_sq_eq_nullRawModulusSqEulerProduct hpm u

/-- Exact infinite-product identity for the actual standardized null law.
The raw frequency is `u=t/sqrt(V)`. -/
theorem norm_charFun_standardizedNullLaw_sq_eq_nullRawModulusSqEulerProduct
    {m p : ℕ} (h : Admissible m p) (t : ℝ) :
    ‖charFun (standardizedNullLaw m p) t‖ ^ 2 =
      nullRawModulusSqEulerProduct m p
        (t / Real.sqrt (nullVSeries m p)) := by
  rw [charFun_standardizedNullLaw_eq_standardizedGammaProduct h.2]
  unfold standardizedLogBetaCharacteristicProduct
  rw [nullVariance_eq_nullVSeries h.2]
  rw [← charFun_centeredLogBetaSumLaw_eq_centeredGammaProduct h.2]
  exact norm_charFun_centeredLogBetaSumLaw_sq_eq_nullRawModulusSqEulerProduct
    h.2 _

/-- The double Euler product is exactly the exponential of minus its
logarithmic loss. -/
theorem nullRawModulusSqEulerProduct_eq_exp_neg_logLoss
    {m p : ℕ} (h : Admissible m p) (u : ℝ) :
    nullRawModulusSqEulerProduct m p u =
      Real.exp (-nullRawModulusLogLoss m p u) := by
  unfold nullRawModulusSqEulerProduct nullRawModulusLogLoss
  calc
    (∏ j ∈ Finset.Icc 2 p,
        betaModulusEulerProduct (betaShapeA m j) (betaShapeTotal m) u) =
        ∏ j ∈ Finset.Icc 2 p,
          Real.exp (-betaModulusLogLoss
            (betaShapeA m j) (betaShapeTotal m) u) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact betaModulusEulerProduct_eq_exp_neg_logLoss
        (betaShapeA_pos_of_mem_Icc h.2 hj) (betaShapeTotal_pos h) u
    _ = Real.exp (∑ j ∈ Finset.Icc 2 p,
        -betaModulusLogLoss (betaShapeA m j) (betaShapeTotal m) u) := by
      rw [Real.exp_sum]
    _ = Real.exp (-∑ j ∈ Finset.Icc 2 p,
        betaModulusLogLoss (betaShapeA m j) (betaShapeTotal m) u) := by
      rw [Finset.sum_neg_distrib]

/-! ## Raw-frequency monotonicity -/

theorem betaModulusEulerFactor_antitone_sq
    {a M s t : ℝ} (ha : 0 < a) (haM : a ≤ M)
    (hs : 0 ≤ s) (hst : s ≤ t) (l : ℕ) :
    betaModulusEulerFactor a M (Real.sqrt t) l ≤
      betaModulusEulerFactor a M (Real.sqrt s) l := by
  have ht : 0 ≤ t := hs.trans hst
  have hal : 0 < a + (l : ℝ) := by positivity
  have hMl : 0 < M + (l : ℝ) := ha.trans_le haM |> fun hM ↦ by positivity
  have hsq : (a + (l : ℝ)) ^ 2 ≤ (M + (l : ℝ)) ^ 2 := by gcongr
  unfold betaModulusEulerFactor
  rw [Real.sq_sqrt ht, Real.sq_sqrt hs]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  field_simp [hal.ne', hMl.ne']
  nlinarith

theorem betaModulusEulerProduct_antitone_abs
    {a M u v : ℝ} (ha : 0 < a) (haM : a ≤ M)
    (huv : |u| ≤ |v|) :
    betaModulusEulerProduct a M v ≤ betaModulusEulerProduct a M u := by
  have huSq : 0 ≤ u ^ 2 := sq_nonneg u
  have huvSq : u ^ 2 ≤ v ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg u) (abs_nonneg v)).2 huv
  have hM : 0 < M := ha.trans_le haM
  have huSum := summable_betaModulusLogLoss_terms ha hM u
  have hvSum := summable_betaModulusLogLoss_terms ha hM v
  have hloss : betaModulusLogLoss a M u ≤ betaModulusLogLoss a M v := by
    unfold betaModulusLogLoss
    apply huSum.tsum_le_tsum _ hvSum
    intro l
    have hfac : betaModulusEulerFactor a M v l ≤
        betaModulusEulerFactor a M u l := by
      have hsqrt := betaModulusEulerFactor_antitone_sq
        ha haM huSq huvSq l
      simpa [Real.sqrt_sq_eq_abs, betaModulusEulerFactor, sq_abs] using hsqrt
    have hlog := Real.log_le_log
      (betaModulusEulerFactor_pos ha hM v l) hfac
    unfold betaModulusEulerFactor at hlog
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)] at hlog
    linarith
  rw [betaModulusEulerProduct_eq_exp_neg_logLoss ha hM v,
    betaModulusEulerProduct_eq_exp_neg_logLoss ha hM u]
  exact Real.exp_le_exp.mpr (neg_le_neg hloss)

/-- The raw squared modulus, and hence the raw modulus, is decreasing in
absolute frequency. -/
theorem norm_charFun_centeredLogBetaSumLaw_antitone_abs
    {m p : ℕ} (h : Admissible m p) {u v : ℝ} (huv : |u| ≤ |v|) :
    ‖charFun (centeredLogBetaSumLaw m p) v‖ ≤
      ‖charFun (centeredLogBetaSumLaw m p) u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_charFun_centeredLogBetaSumLaw_sq_eq_nullRawModulusSqEulerProduct h.2,
    norm_charFun_centeredLogBetaSumLaw_sq_eq_nullRawModulusSqEulerProduct h.2]
  unfold nullRawModulusSqEulerProduct
  apply Finset.prod_le_prod
  · intro j hj
    exact (betaModulusEulerProduct_eq_exp_neg_logLoss
      (betaShapeA_pos_of_mem_Icc h.2 hj) (betaShapeTotal_pos h) v).symm ▸
        (Real.exp_pos _).le
  · intro j hj
    exact betaModulusEulerProduct_antitone_abs
      (betaShapeA_pos_of_mem_Icc h.2 hj)
      (le_of_lt (betaShapeA_lt_total (Finset.mem_Icc.mp hj).1)) huv

/-! ## Local Gaussian damping -/

/-- Elementary logarithmic comparison behind local Gaussian damping. -/
theorem scaled_reciprocal_sq_difference_le_log_difference
    {x y u eta : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (heta : 0 ≤ eta) (hu : |u| ≤ eta * x) :
    u ^ 2 / (1 + eta ^ 2) * (1 / x ^ 2 - 1 / y ^ 2) ≤
      Real.log (1 + u ^ 2 / x ^ 2) -
        Real.log (1 + u ^ 2 / y ^ 2) := by
  have hy : 0 < y := hx.trans_le hxy
  let A : ℝ := u ^ 2 / x ^ 2
  let B : ℝ := u ^ 2 / y ^ 2
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBA : B ≤ A := by
    dsimp [A, B]
    gcongr
  have hAx : A ≤ eta ^ 2 := by
    have hright : 0 ≤ eta * x := mul_nonneg heta hx.le
    have hsquare := (sq_le_sq₀ (abs_nonneg u) hright).2 hu
    rw [sq_abs, mul_pow] at hsquare
    dsimp [A]
    exact (div_le_iff₀ (sq_pos_of_pos hx)).2 (by simpa [mul_comm] using hsquare)
  have hq : 0 < (1 + A) / (1 + B) := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hq
  rw [Real.log_div (by positivity : 1 + A ≠ 0)
    (by positivity : 1 + B ≠ 0)] at hlog
  have hstep : (A - B) / (1 + eta ^ 2) ≤
      1 - ((1 + A) / (1 + B))⁻¹ := by
    rw [inv_div]
    have hid : 1 - (1 + B) / (1 + A) = (A - B) / (1 + A) := by
      field_simp [show 1 + A ≠ 0 by positivity]
      ring
    rw [hid]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hBA)
      (by positivity) (by linarith)
  have hrewrite :
      u ^ 2 / (1 + eta ^ 2) * (1 / x ^ 2 - 1 / y ^ 2) =
        (A - B) / (1 + eta ^ 2) := by
    dsimp [A, B]
    field_simp [hx.ne', hy.ne']
  rw [hrewrite]
  exact hstep.trans hlog

theorem betaModulusLogLoss_lower_local
    {a M amin u eta : ℝ} (ha : 0 < a) (haM : a ≤ M)
    (_hamin : 0 < amin) (hamina : amin ≤ a)
    (heta : 0 ≤ eta) (hu : |u| ≤ eta * amin) :
    u ^ 2 / (1 + eta ^ 2) * reciprocalPowerDifference 2 a M ≤
      betaModulusLogLoss a M u := by
  have hM : 0 < M := ha.trans_le haM
  have hleft := (summable_reciprocalPowerDifference
    (r := 2) (by norm_num) ha hM).mul_left (u ^ 2 / (1 + eta ^ 2))
  have hright := summable_betaModulusLogLoss_terms ha hM u
  unfold reciprocalPowerDifference betaModulusLogLoss
  rw [← tsum_mul_left]
  exact hleft.tsum_le_tsum (fun l ↦ by
    have hxl : 0 < a + (l : ℝ) := by positivity
    have hxy : a + (l : ℝ) ≤ M + (l : ℝ) := by linarith
    have hfreq : |u| ≤ eta * (a + (l : ℝ)) :=
      hu.trans (mul_le_mul_of_nonneg_left (by linarith) heta)
    simpa only [add_sub_add_right_eq_sub] using
      scaled_reciprocal_sq_difference_le_log_difference
        hxl hxy heta hfreq) hright

/-- The complete raw logarithmic loss dominates its variance quadratic on
the disk `|u| <= eta a_*`. -/
theorem nullRawModulusLogLoss_lower_local
    {m p : ℕ} (h : Admissible m p) {eta u : ℝ}
    (heta : 0 ≤ eta) (hu : |u| ≤ eta * nullMinShape m p) :
    u ^ 2 * nullVSeries m p / (1 + eta ^ 2) ≤
      nullRawModulusLogLoss m p u := by
  rw [nullVSeries_eq_doubleSeries h]
  unfold nullRawModulusLogLoss
  change u ^ 2 *
      (∑ j ∈ Finset.Icc 2 p, reciprocalPowerDifference 2
        (betaShapeA m j) (betaShapeTotal m)) / (1 + eta ^ 2) ≤
    ∑ j ∈ Finset.Icc 2 p,
      betaModulusLogLoss (betaShapeA m j) (betaShapeTotal m) u
  rw [div_eq_mul_inv]
  rw [show u ^ 2 *
      (∑ j ∈ Finset.Icc 2 p, reciprocalPowerDifference 2
        (betaShapeA m j) (betaShapeTotal m)) * (1 + eta ^ 2)⁻¹ =
      (u ^ 2 / (1 + eta ^ 2)) *
        (∑ j ∈ Finset.Icc 2 p, reciprocalPowerDifference 2
          (betaShapeA m j) (betaShapeTotal m)) by ring]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have haj : 0 < betaShapeA m j := betaShapeA_pos_of_mem_Icc h.2 hj
  have haM : betaShapeA m j ≤ betaShapeTotal m :=
    (betaShapeA_lt_total (Finset.mem_Icc.mp hj).1).le
  have hamin : 0 < nullMinShape m p := nullMinShape_pos h
  have haminj : nullMinShape m p ≤ betaShapeA m j := by
    unfold nullMinShape betaShapeA
    have hjp : j ≤ p := (Finset.mem_Icc.mp hj).2
    have hjpR : (j : ℝ) ≤ (p : ℝ) := by exact_mod_cast hjp
    linarith
  have hone : 0 < 1 + eta ^ 2 := by positivity
  have hfactor := betaModulusLogLoss_lower_local haj haM hamin haminj heta hu
  convert hfactor using 1

/-- Raw-frequency Gaussian damping, uniformly through the hard edge. -/
theorem norm_charFun_centeredLogBetaSumLaw_le_gaussian_local
    {m p : ℕ} (h : Admissible m p) {eta u : ℝ}
    (heta : 0 ≤ eta) (hu : |u| ≤ eta * nullMinShape m p) :
    ‖charFun (centeredLogBetaSumLaw m p) u‖ ≤
      Real.exp (-(u ^ 2 * nullVSeries m p /
        (2 * (1 + eta ^ 2)))) := by
  have hD := nullRawModulusLogLoss_lower_local h heta hu
  have hsq := norm_charFun_centeredLogBetaSumLaw_sq_eq_nullRawModulusSqEulerProduct
    h.2 u
  rw [nullRawModulusSqEulerProduct_eq_exp_neg_logLoss h u] at hsq
  apply (sq_le_sq₀ (norm_nonneg _)
    (Real.exp_pos (-(u ^ 2 * nullVSeries m p /
      (2 * (1 + eta ^ 2))))).le).mp
  rw [hsq, pow_two, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hden : 0 < 1 + eta ^ 2 := by positivity
  have heq :
      -(u ^ 2 * nullVSeries m p / (2 * (1 + eta ^ 2))) +
          -(u ^ 2 * nullVSeries m p / (2 * (1 + eta ^ 2))) =
        -(u ^ 2 * nullVSeries m p / (1 + eta ^ 2)) := by
    field_simp [hden.ne']
    ring
  rw [heq]
  exact neg_le_neg hD

/-- Standardized local Gaussian damping on `|t| <= eta Delta`. -/
theorem norm_charFun_standardizedNullLaw_le_gaussian_local
    {m p : ℕ} (h : Admissible m p) {eta t : ℝ}
    (heta : 0 ≤ eta) (ht : |t| ≤ eta * nullAnalyticScale m p) :
    ‖charFun (standardizedNullLaw m p) t‖ ≤
      Real.exp (-(t ^ 2 / (2 * (1 + eta ^ 2)))) := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hs : 0 < Real.sqrt (nullVSeries m p) := Real.sqrt_pos.2 hV
  have hrawFreq : |t / Real.sqrt (nullVSeries m p)| ≤
      eta * nullMinShape m p := by
    rw [abs_div, abs_of_pos hs]
    unfold nullAnalyticScale at ht
    change |t| ≤ eta *
      (nullMinShape m p * Real.sqrt (nullVSeries m p)) at ht
    exact (div_le_iff₀ hs).2 (by simpa [mul_assoc] using ht)
  rw [charFun_standardizedNullLaw_eq_standardizedGammaProduct h.2]
  unfold standardizedLogBetaCharacteristicProduct
  rw [nullVariance_eq_nullVSeries h.2]
  rw [← charFun_centeredLogBetaSumLaw_eq_centeredGammaProduct h.2]
  have hlocal := norm_charFun_centeredLogBetaSumLaw_le_gaussian_local
    h heta hrawFreq
  convert hlocal using 1
  congr 2
  rw [div_pow, Real.sq_sqrt hV.le]
  field_simp [hV.ne']

end

end LogdetLean
