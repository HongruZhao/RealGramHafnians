import LogdetLean.ComplexBetaMellin
import LogdetLean.HigherCumulants
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
/-!
# Euler product for the modulus of the Gamma function

This file derives the positive-real-axis specialization of DLMF 5.8.3 from
mathlib's kernel-checked Euler limit formula `Complex.GammaSeq_tendsto_Gamma`.
It is the special-function input for the full-frequency log-Beta estimates.
-/

namespace LogdetLean

open Filter Real
open scoped BigOperators Topology

noncomputable section

/-- The `l`th positive Euler factor in the squared Gamma-modulus formula. -/
def gammaModulusEulerFactor (x u : ℝ) (l : ℕ) : ℝ :=
  (1 + u ^ 2 / (x + (l : ℝ)) ^ 2)⁻¹

/-- The complete positive Euler product in the squared Gamma-modulus formula. -/
def gammaModulusEulerProduct (x u : ℝ) : ℝ :=
  ∏' l : ℕ, gammaModulusEulerFactor x u l

/-- The absolutely convergent logarithmic series paired with the Gamma Euler
product. -/
def gammaModulusLogSeries (x u : ℝ) : ℝ :=
  ∑' l : ℕ, Real.log (1 + u ^ 2 / (x + (l : ℝ)) ^ 2)

theorem gammaModulusEulerFactor_pos {x : ℝ} (hx : 0 < x) (u : ℝ) (l : ℕ) :
    0 < gammaModulusEulerFactor x u l := by
  unfold gammaModulusEulerFactor
  positivity

theorem summable_gammaModulusEulerPerturbation {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Summable (fun l : ℕ ↦ u ^ 2 / (x + (l : ℝ)) ^ 2) := by
  simpa [div_eq_mul_inv] using
    (summable_shifted_reciprocal_pow (x := x) hx (r := 2) (by norm_num)).mul_left
      (u ^ 2)

theorem multipliable_gammaModulusEulerFactor {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Multipliable (gammaModulusEulerFactor x u) := by
  have hlog := Real.summable_log_one_add_of_summable
    (summable_gammaModulusEulerPerturbation hx u)
  apply Real.multipliable_of_summable_log
  · exact fun l ↦ gammaModulusEulerFactor_pos hx u l
  · refine hlog.neg.congr (fun l ↦ ?_)
    unfold gammaModulusEulerFactor
    rw [Real.log_inv]

theorem summable_log_gammaModulusEulerFactor {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Summable (fun l : ℕ ↦ Real.log (gammaModulusEulerFactor x u l)) := by
  have hlog := Real.summable_log_one_add_of_summable
    (summable_gammaModulusEulerPerturbation hx u)
  refine hlog.neg.congr (fun l ↦ ?_)
  unfold gammaModulusEulerFactor
  rw [Real.log_inv]

/-- The Gamma Euler product is strictly positive, including at `u=0`. -/
theorem gammaModulusEulerProduct_pos {x : ℝ} (hx : 0 < x) (u : ℝ) :
    0 < gammaModulusEulerProduct x u := by
  unfold gammaModulusEulerProduct
  rw [← Real.rexp_tsum_eq_tprod
    (fun l ↦ gammaModulusEulerFactor_pos hx u l)
    (summable_log_gammaModulusEulerFactor hx u)]
  exact Real.exp_pos _

theorem gammaModulusEulerProduct_eq_exp_neg_logSeries
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    gammaModulusEulerProduct x u =
      Real.exp (-gammaModulusLogSeries x u) := by
  have hlogOne := Real.summable_log_one_add_of_summable
    (summable_gammaModulusEulerPerturbation hx u)
  have hlogFactor := summable_log_gammaModulusEulerFactor hx u
  unfold gammaModulusEulerProduct gammaModulusLogSeries
  rw [← Real.rexp_tsum_eq_tprod
    (fun l ↦ gammaModulusEulerFactor_pos hx u l) hlogFactor]
  congr 1
  rw [← tsum_neg]
  apply tsum_congr
  intro l
  unfold gammaModulusEulerFactor
  rw [Real.log_inv]

/-- The `l`th ratio in the squared log-Beta modulus product. -/
def betaModulusEulerFactor (a M u : ℝ) (l : ℕ) : ℝ :=
  (1 + u ^ 2 / (M + (l : ℝ)) ^ 2) /
    (1 + u ^ 2 / (a + (l : ℝ)) ^ 2)

/-- The one-factor infinite product occurring in the squared log-Beta
characteristic-function modulus. -/
def betaModulusEulerProduct (a M u : ℝ) : ℝ :=
  ∏' l : ℕ, betaModulusEulerFactor a M u l

/-- The logarithmic loss of one log-Beta factor. -/
def betaModulusLogLoss (a M u : ℝ) : ℝ :=
  ∑' l : ℕ,
    (Real.log (1 + u ^ 2 / (a + (l : ℝ)) ^ 2) -
      Real.log (1 + u ^ 2 / (M + (l : ℝ)) ^ 2))

theorem betaModulusEulerFactor_pos
    {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (u : ℝ) (l : ℕ) :
    0 < betaModulusEulerFactor a M u l := by
  unfold betaModulusEulerFactor
  positivity

theorem summable_betaModulusLogLoss_terms
    {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (u : ℝ) :
    Summable (fun l : ℕ ↦
      (Real.log (1 + u ^ 2 / (a + (l : ℝ)) ^ 2) -
        Real.log (1 + u ^ 2 / (M + (l : ℝ)) ^ 2))) :=
  (Real.summable_log_one_add_of_summable
      (summable_gammaModulusEulerPerturbation ha u)).sub
    (Real.summable_log_one_add_of_summable
      (summable_gammaModulusEulerPerturbation hM u))

theorem betaModulusEulerFactor_eq_div_gammaFactors
    {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (u : ℝ) (l : ℕ) :
    betaModulusEulerFactor a M u l =
      gammaModulusEulerFactor a u l / gammaModulusEulerFactor M u l := by
  unfold betaModulusEulerFactor gammaModulusEulerFactor
  have hal : 0 < a + (l : ℝ) := by positivity
  have hMl : 0 < M + (l : ℝ) := by positivity
  field_simp [hal.ne', hMl.ne']

theorem betaModulusEulerProduct_eq_div_gammaProducts
    {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (u : ℝ) :
    betaModulusEulerProduct a M u =
      gammaModulusEulerProduct a u / gammaModulusEulerProduct M u := by
  have haMul := multipliable_gammaModulusEulerFactor ha u
  have hMMul := multipliable_gammaModulusEulerFactor hM u
  unfold betaModulusEulerProduct
  rw [show (fun l ↦ betaModulusEulerFactor a M u l) =
      (fun l ↦ gammaModulusEulerFactor a u l /
        gammaModulusEulerFactor M u l) by
    funext l
    exact betaModulusEulerFactor_eq_div_gammaFactors ha hM u l]
  exact haMul.tprod_div₀ hMMul (gammaModulusEulerProduct_pos hM u).ne'

theorem betaModulusEulerProduct_eq_exp_neg_logLoss
    {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (u : ℝ) :
    betaModulusEulerProduct a M u =
      Real.exp (-betaModulusLogLoss a M u) := by
  rw [betaModulusEulerProduct_eq_div_gammaProducts ha hM u,
    gammaModulusEulerProduct_eq_exp_neg_logSeries ha u,
    gammaModulusEulerProduct_eq_exp_neg_logSeries hM u]
  rw [← Real.exp_sub]
  unfold betaModulusLogLoss gammaModulusLogSeries
  have haSum := Real.summable_log_one_add_of_summable
    (summable_gammaModulusEulerPerturbation ha u)
  have hMSum := Real.summable_log_one_add_of_summable
    (summable_gammaModulusEulerPerturbation hM u)
  rw [haSum.tsum_sub hMSum]
  congr 1
  ring

private theorem normSq_GammaSeq_add_mul_I
    {x : ℝ} (_hx : 0 < x) (u : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Complex.normSq
        (Complex.GammaSeq ((x : ℂ) + (u : ℂ) * Complex.I) n) =
      ((((n : ℝ) ^ x) * (Nat.factorial n : ℝ)) ^ 2) /
        ∏ l ∈ Finset.range (n + 1),
          ((x + (l : ℝ)) ^ 2 + u ^ 2) := by
  unfold Complex.GammaSeq
  rw [Complex.normSq_eq_norm_sq, norm_div, norm_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, mul_one,
    Complex.norm_natCast, norm_prod, div_pow]
  rw [← Finset.prod_pow]
  simp only [add_zero]
  congr 2
  funext l
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
    Complex.mul_im, Complex.I_im, mul_zero, sub_zero, mul_one,
    Complex.natCast_re, Complex.natCast_im, add_zero]
  ring

private theorem normSq_GammaSeq_ofReal
    {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    Complex.normSq (Complex.GammaSeq (x : ℂ) n) =
      ((((n : ℝ) ^ x) * (Nat.factorial n : ℝ)) ^ 2) /
        ∏ l ∈ Finset.range (n + 1), (x + (l : ℝ)) ^ 2 := by
  simpa using normSq_GammaSeq_add_mul_I hx 0 hn

private theorem normSq_GammaSeq_ratio_eq_prod_range
    {x : ℝ} (hx : 0 < x) (u : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Complex.normSq
          (Complex.GammaSeq ((x : ℂ) + (u : ℂ) * Complex.I) n) /
        Complex.normSq (Complex.GammaSeq (x : ℂ) n) =
      ∏ l ∈ Finset.range (n + 1), gammaModulusEulerFactor x u l := by
  rw [normSq_GammaSeq_add_mul_I hx u hn, normSq_GammaSeq_ofReal hx hn]
  have hbase : 0 < ((n : ℝ) ^ x) * (Nat.factorial n : ℝ) := by positivity
  have hden : ∀ l ∈ Finset.range (n + 1), 0 < x + (l : ℝ) := by
    intro l hl
    positivity
  rw [div_div_div_cancel_left' _ _ (pow_ne_zero 2 hbase.ne')]
  rw [← Finset.prod_div_distrib]
  unfold gammaModulusEulerFactor
  field_simp [hbase.ne', (Finset.prod_pos hden).ne']

/-- Positive-real-axis Euler product for the squared Gamma-modulus ratio.
This is the exact specialization of DLMF 5.8.3 needed by the log-Beta law. -/
theorem normSq_Gamma_add_mul_I_div_Gamma_ofReal
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Complex.normSq
          (Complex.Gamma ((x : ℂ) + (u : ℂ) * Complex.I)) /
        Complex.normSq (Complex.Gamma (x : ℂ)) =
      gammaModulusEulerProduct x u := by
  have hnum := Complex.continuous_normSq.continuousAt.tendsto.comp
    (Complex.GammaSeq_tendsto_Gamma
      ((x : ℂ) + (u : ℂ) * Complex.I))
  have hden := Complex.continuous_normSq.continuousAt.tendsto.comp
    (Complex.GammaSeq_tendsto_Gamma (x : ℂ))
  have hden_ne : Complex.normSq (Complex.Gamma (x : ℂ)) ≠ 0 := by
    exact (Complex.normSq_eq_zero.not.mpr
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using hx)))
  have hratio := hnum.div hden hden_ne
  have hmult := multipliable_gammaModulusEulerFactor hx u
  have hprod : Tendsto
      (fun n : ℕ ↦ ∏ l ∈ Finset.range n, gammaModulusEulerFactor x u l)
      atTop (nhds (gammaModulusEulerProduct x u)) := by
    unfold gammaModulusEulerProduct
    exact (hmult.hasProd_iff_tendsto_nat).mp hmult.hasProd
  have hshift := hprod.comp (tendsto_add_atTop_nat 1)
  apply tendsto_nhds_unique hratio
  apply hshift.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simpa [Function.comp_apply] using
    (normSq_GammaSeq_ratio_eq_prod_range hx u hn).symm

/-- Exact infinite product for the squared modulus of a pure-imaginary
Beta Mellin quotient. -/
theorem normSq_complexBetaMellinQuotient_mul_I_eq_betaModulusEulerProduct
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    Complex.normSq
        (complexBetaMellinQuotient a b ((u : ℂ) * Complex.I)) =
      betaModulusEulerProduct a (a + b) u := by
  have hM : 0 < a + b := add_pos ha hb
  have hGa : Complex.normSq (Complex.Gamma (a : ℂ)) ≠ 0 :=
    Complex.normSq_eq_zero.not.mpr
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using ha))
  have hGM : Complex.normSq (Complex.Gamma ((a + b : ℝ) : ℂ)) ≠ 0 :=
    Complex.normSq_eq_zero.not.mpr
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using hM))
  have hGMi : Complex.normSq
      (Complex.Gamma (((a + b : ℝ) : ℂ) + (u : ℂ) * Complex.I)) ≠ 0 :=
    Complex.normSq_eq_zero.not.mpr
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using hM))
  unfold complexBetaMellinQuotient
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul]
  rw [betaModulusEulerProduct_eq_div_gammaProducts ha hM u]
  rw [← normSq_Gamma_add_mul_I_div_Gamma_ofReal ha u,
    ← normSq_Gamma_add_mul_I_div_Gamma_ofReal hM u]
  field_simp [hGa, hGM, hGMi]

end

end LogdetLean
