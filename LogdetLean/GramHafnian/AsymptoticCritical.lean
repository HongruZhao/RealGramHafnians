import LogdetLean.GramHafnian.FiniteBesselMajorant
import Mathlib.Analysis.Normed.Group.Tannery
/-!
# The quadratic critical window

This file upgrades the finite Gram--hafnian correction formula to its sharp
quadratic-scale infinite-series limit.  The limiting series is the
confluent-hypergeometric/Bessel crossover

`sum_j (1/2)_j (2 y)^j / (j!)^2`.

The proof is organized around Tannery's theorem: extend the terminating
finite sum by zero, prove convergence of every fixed summand, and dominate
all summands by one summable Bessel series.
-/

open scoped BigOperators Topology
open Finset Filter

namespace LogdetLean.GramHafnian

noncomputable section

/-- The finite correction summand, extended by zero beyond its terminating
index. -/
def extendedFiniteTerm (k n j : ℕ) : ℝ :=
  if j ≤ n then finiteTerm k n j else 0

@[simp] theorem extendedFiniteTerm_of_le
    (k n j : ℕ) (hj : j ≤ n) :
    extendedFiniteTerm k n j = finiteTerm k n j := by
  simp [extendedFiniteTerm, hj]

@[simp] theorem extendedFiniteTerm_of_lt
    (k n j : ℕ) (hj : n < j) :
    extendedFiniteTerm k n j = 0 := by
  simp [extendedFiniteTerm, Nat.not_le.mpr hj]

/-- The infinite sum of the zero-extended summands is exactly the original
finite correction. -/
theorem tsum_extendedFiniteTerm_eq_finiteCorrection (k n : ℕ) :
    (∑' j : ℕ, extendedFiniteTerm k n j) = finiteCorrection k n := by
  rw [finiteCorrection]
  rw [tsum_eq_sum (s := range (n + 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    exact extendedFiniteTerm_of_le k n j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  · intro j hj
    rw [extendedFiniteTerm_of_lt]
    exact Nat.le_of_not_gt (by
      simpa [Finset.mem_range] using hj)

/-- One Bessel-series coefficient. -/
def besselSeriesTerm (y : ℝ) (j : ℕ) : ℝ :=
  rising (1 / 2 : ℝ) j * (2 * y) ^ j / ((j.factorial : ℝ) ^ 2)

theorem besselSeriesTerm_nonneg {y : ℝ} (hy : 0 ≤ y) (j : ℕ) :
    0 ≤ besselSeriesTerm y j := by
  unfold besselSeriesTerm
  exact div_nonneg
    (mul_nonneg (rising_half_nonneg j) (pow_nonneg (by positivity) j))
    (sq_nonneg _)

theorem summable_besselSeriesTerm {y : ℝ} (hy : 0 ≤ y) :
    Summable (besselSeriesTerm y) := by
  change Summable (fun j : ℕ ↦
    rising (1 / 2 : ℝ) j * (2 * y) ^ j / ((j.factorial : ℝ) ^ 2))
  exact besselMajorant_summable y hy

theorem tsum_besselSeriesTerm (y : ℝ) :
    (∑' j : ℕ, besselSeriesTerm y j) = besselMajorant y := by
  rfl

/-- Consecutive-summand factor in the exact finite correction. -/
def criticalRecurrenceFactor (k n j : ℕ) : ℝ :=
  (((n - j : ℕ) : ℝ) ^ 2 * ((2 * j + 1 : ℕ) : ℝ)) /
    (((j + 1 : ℕ) : ℝ) ^ 2 * ((k + 2 * j : ℕ) : ℝ))

theorem finiteTerm_succ_eq_mul_criticalRecurrenceFactor
    (k n j : ℕ) (hk : 0 < k) (hj : j < n) :
    finiteTerm k n (j + 1) =
      finiteTerm k n j * criticalRecurrenceFactor k n j := by
  have hterm : finiteTerm k n j ≠ 0 :=
    ne_of_gt (finiteTerm_pos k n j hk (Nat.le_of_lt hj))
  have hratio := finiteTerm_succ_ratio k n j hk hj
  rw [div_eq_iff hterm] at hratio
  simpa [criticalRecurrenceFactor, mul_comm] using hratio

/-- Removing a fixed integer from `n` is asymptotically invisible after
division by `n`. -/
theorem tendsto_natSub_div_natCast_one (j : ℕ) :
    Tendsto (fun n : ℕ ↦ (((n - j : ℕ) : ℝ) / (n : ℝ)))
      atTop (nhds 1) := by
  have hbase : Tendsto (fun n : ℕ ↦
      (1 : ℝ) - (j : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub
      (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ)) using 1 <;> norm_num
  apply hbase.congr'
  filter_upwards [eventually_ge_atTop j, eventually_ge_atTop 1] with n hjn hn
  rw [Nat.cast_sub hjn]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0]

/-- A fixed additive perturbation of the row dimension is asymptotically
invisible in the quotient `k/(k+constant)`. -/
theorem tendsto_k_div_k_add_fixed_one
    (kseq : ℕ → ℕ) (j : ℕ)
    (hkTop : Tendsto kseq atTop atTop) :
    Tendsto (fun n : ℕ ↦
      (kseq n : ℝ) / ((kseq n + 2 * j : ℕ) : ℝ))
      atTop (nhds 1) := by
  have h := (tendsto_natCast_div_add_atTop ((2 * j : ℕ) : ℝ)).comp hkTop
  have heq :
      (fun n : ℕ ↦ (kseq n : ℝ) /
        ((kseq n + 2 * j : ℕ) : ℝ)) =
      ((fun q : ℕ ↦ (q : ℝ) / ((q : ℝ) + (2 * j : ℝ))) ∘ kseq) := by
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
  rw [heq]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- Under quadratic scaling, the exact consecutive-summand factor converges
to the corresponding ratio of Bessel-series coefficients. -/
theorem tendsto_criticalRecurrenceFactor
    (kseq : ℕ → ℕ) (y : ℝ) (j : ℕ)
    (hkTop : Tendsto kseq atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) atTop (nhds y)) :
    Tendsto (fun n : ℕ ↦ criticalRecurrenceFactor (kseq n) n j)
      atTop (nhds (y * (((2 * j + 1 : ℕ) : ℝ) /
        ((j + 1 : ℕ) : ℝ) ^ 2))) := by
  have hsub := (tendsto_natSub_div_natCast_one j).pow 2
  have hkfrac := tendsto_k_div_k_add_fixed_one kseq j hkTop
  have hprod := (((hsub.mul hratio).mul hkfrac).mul_const
    (((2 * j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2))
  have hprod' : Tendsto
      (fun n : ℕ ↦
        ((((n - j : ℕ) : ℝ) / (n : ℝ)) ^ 2 *
          ((n : ℝ) ^ 2 / (kseq n : ℝ)) *
          ((kseq n : ℝ) / ((kseq n + 2 * j : ℕ) : ℝ)) *
          (((2 * j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2)))
      atTop (nhds (y * (((2 * j + 1 : ℕ) : ℝ) /
        ((j + 1 : ℕ) : ℝ) ^ 2))) := by
    convert hprod using 1 <;> ring
  apply hprod'.congr'
  filter_upwards [eventually_ge_atTop (j + 1),
      (hkTop.eventually (eventually_ge_atTop 1))]
    with n hn hk
  have hnNat : 0 < n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnNat.ne'
  have hk0 : (kseq n : ℝ) ≠ 0 := by positivity
  have hkadd0 : (((kseq n + 2 * j : ℕ) : ℝ)) ≠ 0 := by positivity
  have hjden0 : (((j + 1 : ℕ) : ℝ) ^ 2) ≠ 0 := by positivity
  unfold criticalRecurrenceFactor
  field_simp [hn0, hk0, hkadd0, hjden0]

/-- Exact consecutive-coefficient recurrence for the limiting Bessel series. -/
theorem besselSeriesTerm_succ (y : ℝ) (j : ℕ) :
    besselSeriesTerm y (j + 1) =
      besselSeriesTerm y j *
        (y * (((2 * j + 1 : ℕ) : ℝ) /
          ((j + 1 : ℕ) : ℝ) ^ 2)) := by
  rw [besselSeriesTerm, besselSeriesTerm, rising_succ, pow_succ,
    Nat.factorial_succ]
  push_cast
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hj, hfac]
  ring

/-- Every fixed exact summand converges to the corresponding coefficient in
the Bessel crossover series.  The proof uses only the exact finite recurrence,
so it avoids a separate asymptotic expansion of binomial coefficients and
Pochhammer symbols. -/
theorem tendsto_extendedFiniteTerm_critical
    (kseq : ℕ → ℕ) (y : ℝ) (j : ℕ)
    (hkTop : Tendsto kseq atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) atTop (nhds y)) :
    Tendsto (fun n : ℕ ↦ extendedFiniteTerm (kseq n) n j)
      atTop (nhds (besselSeriesTerm y j)) := by
  induction j with
  | zero =>
      simpa [extendedFiniteTerm, besselSeriesTerm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  | succ j ih =>
      have hfactor := tendsto_criticalRecurrenceFactor kseq y j hkTop hratio
      have hmul := ih.mul hfactor
      rw [besselSeriesTerm_succ]
      apply hmul.congr'
      filter_upwards [eventually_ge_atTop (j + 1),
          hkTop.eventually (eventually_ge_atTop 1)]
        with n hn hk
      have hjlt : j < n := by omega
      rw [extendedFiniteTerm_of_le _ _ _ hn,
        extendedFiniteTerm_of_le _ _ _ (Nat.le_of_lt hjlt)]
      exact (finiteTerm_succ_eq_mul_criticalRecurrenceFactor
        (kseq n) n j (by omega) hjlt).symm

/-- Pointwise domination of every zero-extended finite summand by a fixed
Bessel-series coefficient. -/
theorem norm_extendedFiniteTerm_le_besselSeriesTerm
    (k n j : ℕ) (Y : ℝ) (hk : 0 < k) (hY : 0 ≤ Y)
    (hscale : (n : ℝ) ^ 2 / (k : ℝ) ≤ Y) :
    ‖extendedFiniteTerm k n j‖ ≤ besselSeriesTerm Y j := by
  by_cases hj : j ≤ n
  · rw [extendedFiniteTerm_of_le _ _ _ hj, Real.norm_eq_abs,
      abs_of_nonneg (finiteTerm_nonneg k n j)]
    refine (finiteTerm_le_bessel_series_term k n j hk).trans ?_
    unfold besselSeriesTerm
    have hbase : (2 : ℝ) * (n : ℝ) ^ 2 / (k : ℝ) ≤ 2 * Y := by
      calc
        (2 : ℝ) * (n : ℝ) ^ 2 / (k : ℝ) =
            2 * ((n : ℝ) ^ 2 / (k : ℝ)) := by ring
        _ ≤ 2 * Y := mul_le_mul_of_nonneg_left hscale (by norm_num)
    have hbase0 : 0 ≤ (2 : ℝ) * (n : ℝ) ^ 2 / (k : ℝ) := by
      positivity
    have hpow :
        ((2 : ℝ) * (n : ℝ) ^ 2 / (k : ℝ)) ^ j ≤ (2 * Y) ^ j :=
      pow_le_pow_left₀ hbase0 hbase j
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (rising_half_nonneg j))
      (sq_nonneg _)
  · rw [extendedFiniteTerm, if_neg hj, norm_zero]
    exact besselSeriesTerm_nonneg hY j

/-- Sharp quadratic-window convergence of the complete finite correction.

If `k_n → ∞` and `n²/k_n → y ≥ 0`, then the exact correction factor
converges to the entire Bessel crossover series `besselMajorant y`.
-/
theorem tendsto_finiteCorrection_besselMajorant
    (kseq : ℕ → ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hkTop : Tendsto kseq atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) atTop (nhds y)) :
    Tendsto (fun n : ℕ ↦ finiteCorrection (kseq n) n)
      atTop (nhds (besselMajorant y)) := by
  let Y : ℝ := y + 1
  have hY : 0 ≤ Y := by dsimp [Y]; linarith
  have hsum : Summable (besselSeriesTerm Y) :=
    summable_besselSeriesTerm hY
  have hpoint : ∀ j : ℕ, Tendsto
      (fun n : ℕ ↦ extendedFiniteTerm (kseq n) n j)
      atTop (nhds (besselSeriesTerm y j)) := fun j ↦
    tendsto_extendedFiniteTerm_critical kseq y j hkTop hratio
  have hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n :=
    hkTop.eventually (eventually_ge_atTop 1)
  have hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ Y := by
    exact (hratio.eventually_lt_const (by dsimp [Y]; linarith)).mono
      (fun n hn ↦ hn.le)
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      ‖extendedFiniteTerm (kseq n) n j‖ ≤ besselSeriesTerm Y j := by
    filter_upwards [hk, hscale] with n hn hs
    intro j
    exact norm_extendedFiniteTerm_le_besselSeriesTerm
      (kseq n) n j Y hn hY hs
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  rw [show (∑' j : ℕ, besselSeriesTerm y j) = besselMajorant y by rfl] at ht
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n ↦
    tsum_extendedFiniteTerm_eq_finiteCorrection (kseq n) n

theorem besselMajorant_pos {y : ℝ} (hy : 0 ≤ y) :
    0 < besselMajorant y := by
  have hs := summable_besselSeriesTerm hy
  have hzero : (0 : ℝ) < besselSeriesTerm y 0 := by
    simp [besselSeriesTerm]
  have hle : besselSeriesTerm y 0 ≤ ∑' j : ℕ, besselSeriesTerm y j := by
    simpa using hs.sum_le_tsum ({0} : Finset ℕ)
      (fun j _ ↦ besselSeriesTerm_nonneg hy j)
  simpa [tsum_besselSeriesTerm] using lt_of_lt_of_le hzero hle

/-- The critical crossover for the normalized second-moment ratio itself. -/
theorem tendsto_gramSecondMomentRatio_div_baseline_bessel
    (kseq : ℕ → ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hkTop : Tendsto kseq atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) atTop (nhds y)) :
    Tendsto (fun n : ℕ ↦
      gramSecondMomentRatio (kseq n) n / centralBaseline n)
      atTop (nhds (1 / besselMajorant y)) := by
  have hcorr := tendsto_finiteCorrection_besselMajorant kseq y hy hkTop hratio
  have hinv := hcorr.inv₀ (ne_of_gt (besselMajorant_pos hy))
  have heq :
      (fun n : ℕ ↦ (finiteCorrection (kseq n) n)⁻¹) =ᶠ[atTop]
        (fun n : ℕ ↦
          gramSecondMomentRatio (kseq n) n / centralBaseline n) :=
    Filter.Eventually.of_forall fun n ↦ by
      change (finiteCorrection (kseq n) n)⁻¹ =
        (centralBaseline n / finiteCorrection (kseq n) n) /
          centralBaseline n
      field_simp [ne_of_gt (centralBaseline_pos n)]
  simpa [one_div] using hinv.congr' heq

/-- Converting the usual aspect-ratio statement `k_n/n² → c>0` to the
reciprocal ratio used by the finite-summand proof. -/
theorem tendsto_nsq_div_k_of_k_div_nsq
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ))
      atTop (nhds (1 / c)) := by
  have hinv := haspect.inv₀ (ne_of_gt hc)
  have heq :
      (fun n : ℕ ↦ ((kseq n : ℝ) / (n : ℝ) ^ 2)⁻¹) =ᶠ[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1,
      hkTop.eventually (eventually_ge_atTop 1)] with n hn hk
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hk0 : (kseq n : ℝ) ≠ 0 := by positivity
    field_simp [hn0, hk0]
  simpa [one_div] using hinv.congr' heq

/-- Paper-facing sharp quadratic crossover.  For `k_n/n² → c>0`, the
finite correction converges to the explicit series
`besselMajorant (1/c)`, classically `exp(1/c) I₀(1/c)`. -/
theorem tendsto_finiteCorrection_quadratic_crossover
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦ finiteCorrection (kseq n) n)
      atTop (nhds (besselMajorant (1 / c))) := by
  exact tendsto_finiteCorrection_besselMajorant kseq (1 / c)
    (one_div_nonneg.mpr hc.le) hkTop
    (tendsto_nsq_div_k_of_k_div_nsq kseq c hc hkTop haspect)

/-- Paper-facing sharp quadratic crossover for the normalized moment ratio. -/
theorem tendsto_gramSecondMomentRatio_quadratic_crossover
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦
      gramSecondMomentRatio (kseq n) n / centralBaseline n)
      atTop (nhds (1 / besselMajorant (1 / c))) := by
  exact tendsto_gramSecondMomentRatio_div_baseline_bessel
    kseq (1 / c) (one_div_nonneg.mpr hc.le) hkTop
    (tendsto_nsq_div_k_of_k_div_nsq kseq c hc hkTop haspect)

end

end LogdetLean.GramHafnian
