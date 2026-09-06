import RealGramHafnians.Proofs.SharpRealConstant
/-!
# Polynomial small balls at the logarithmic dimension scale

This module formalizes the eventual corollary in the AIHP manuscript.  The
strict gap in the radius exponent absorbs both the fixed Gaussian interval
constant and the `o(1)` loss caused by replacing `k_n - n - 1` with `k_n`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Real ENNReal Nat Topology

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 5000000

/-- The sharp elementary exponent has the paper asymptotic upper bound.
This is the quantified replacement for the informal `o(1)` in the paper. -/
theorem eventually_sharpReal_elementary_exponent_le_log
    (kseq : ℕ → ℕ) {D eta : ℝ} (hD : 0 < D) (heta : 0 < eta)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      2 * n + 2 ≤ kseq n ∧
      (3 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (4 * ((kseq n - n - 1 : ℕ) : ℝ)) ≤
        (3 * D / 4 + eta) * Real.log (n : ℝ) := by
  have hratio : Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦
      1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hxUpperT : Tendsto (fun n : ℕ ↦
      2 * D * Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    have hc : Tendsto (fun _n : ℕ ↦ 2 * D) atTop (nhds (2 * D)) :=
      tendsto_const_nhds
    simpa [mul_div_assoc] using hc.mul hratio
  have hlogTerm : Tendsto (fun n : ℕ ↦
      4 * D * Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    have hc : Tendsto (fun _n : ℕ ↦ 4 * D) atTop (nhds (4 * D)) :=
      tendsto_const_nhds
    simpa [mul_div_assoc] using hc.mul hratio
  have hinvTerm : Tendsto (fun n : ℕ ↦
      1 / (2 * (n : ℝ))) atTop (nhds 0) := by
    have hc : Tendsto (fun _n : ℕ ↦ (1 / 2 : ℝ))
        atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
    have h := hc.mul hinv
    convert h using 1 <;> simp <;> ring
  have herrT : Tendsto (fun n : ℕ ↦
      D * (4 * D * Real.log (n : ℝ) / (n : ℝ) +
        1 / (2 * (n : ℝ)))) atTop (nhds 0) := by
    have hc : Tendsto (fun _n : ℕ ↦ D) atTop (nhds D) :=
      tendsto_const_nhds
    have h := hc.mul (hlogTerm.add hinvTerm)
    convert h using 1 <;> simp
  have hxHalf : ∀ᶠ n : ℕ in atTop,
      2 * D * Real.log (n : ℝ) / (n : ℝ) < 1 / 2 :=
    hxUpperT.eventually_lt_const (by norm_num)
  have herr : ∀ᶠ n : ℕ in atTop,
      D * (4 * D * Real.log (n : ℝ) / (n : ℝ) +
        1 / (2 * (n : ℝ))) < eta :=
    herrT.eventually_lt_const heta
  filter_upwards [eventually_ge_atTop 2, hk, hscale, hxHalf, herr]
      with n hn hkpos hsc hxSmall herrSmall
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hkR : (0 : ℝ) < (kseq n : ℝ) := by exact_mod_cast hkpos
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hx0 : 0 ≤ ((n : ℝ) + 1) / (kseq n : ℝ) := by positivity
  have hx : ((n : ℝ) + 1) / (kseq n : ℝ) ≤
      2 * D * Real.log (n : ℝ) / (n : ℝ) := by
    calc
      ((n : ℝ) + 1) / (kseq n : ℝ) ≤
          (2 * (n : ℝ)) / (kseq n : ℝ) := by
        exact div_le_div_of_nonneg_right (by linarith) hkR.le
      _ = 2 * ((n : ℝ) ^ 2 / (kseq n : ℝ)) / (n : ℝ) := by
        field_simp [hnpos.ne', hkR.ne']
      _ ≤ 2 * (D * Real.log (n : ℝ)) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsc (by norm_num)) hnpos.le
      _ = 2 * D * Real.log (n : ℝ) / (n : ℝ) := by ring
  have hxhalf : ((n : ℝ) + 1) / (kseq n : ℝ) ≤ 1 / 2 :=
    hx.trans hxSmall.le
  have hdimensionR : 2 * (n : ℝ) + 2 ≤ (kseq n : ℝ) := by
    have hm := (div_le_iff₀ hkR).1 hxhalf
    nlinarith
  have hdimension : 2 * n + 2 ≤ kseq n := by
    exact_mod_cast hdimensionR
  refine ⟨hdimension, ?_⟩
  have hdenNat : 0 < kseq n - n - 1 := by omega
  have hden : (0 : ℝ) < ((kseq n - n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hgapCast : ((kseq n - n - 1 : ℕ) : ℝ) =
      (kseq n : ℝ) - (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ kseq n - n)]
    rw [Nat.cast_sub (by omega : n ≤ kseq n)]
    push_cast
    ring
  have hinvOneSub :
      (1 - (((n : ℝ) + 1) / (kseq n : ℝ)))⁻¹ ≤
        1 + 2 * (((n : ℝ) + 1) / (kseq n : ℝ)) := by
    apply (inv_le_iff_one_le_mul₀ (by linarith)).2
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr (by linarith :
      0 ≤ 1 - 2 * (((n : ℝ) + 1) / (kseq n : ℝ))))]
  have hfactor :
      (3 / 4 + 1 / (4 * (n : ℝ))) *
          (1 + 2 * (((n : ℝ) + 1) / (kseq n : ℝ))) ≤
        3 / 4 + 2 * (((n : ℝ) + 1) / (kseq n : ℝ)) +
          1 / (2 * (n : ℝ)) := by
    field_simp [hnpos.ne']
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr (by linarith :
      0 ≤ 1 - 2 * (((n : ℝ) + 1) / (kseq n : ℝ))))]
  have herrActual :
      D * (2 * (((n : ℝ) + 1) / (kseq n : ℝ)) +
          1 / (2 * (n : ℝ))) ≤ eta := by
    have hinside :
        2 * (((n : ℝ) + 1) / (kseq n : ℝ)) +
            1 / (2 * (n : ℝ)) ≤
          4 * D * Real.log (n : ℝ) / (n : ℝ) +
            1 / (2 * (n : ℝ)) := by
      calc
        2 * (((n : ℝ) + 1) / (kseq n : ℝ)) +
            1 / (2 * (n : ℝ)) ≤
          2 * (2 * D * Real.log (n : ℝ) / (n : ℝ)) +
            1 / (2 * (n : ℝ)) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hx (by norm_num)) le_rfl
        _ = 4 * D * Real.log (n : ℝ) / (n : ℝ) +
            1 / (2 * (n : ℝ)) := by ring
    exact (mul_le_mul_of_nonneg_left hinside hD.le).trans herrSmall.le
  have hrewrite :
      (3 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (4 * ((kseq n - n - 1 : ℕ) : ℝ)) =
        ((n : ℝ) ^ 2 / (kseq n : ℝ)) *
          (3 / 4 + 1 / (4 * (n : ℝ))) *
          (1 - (((n : ℝ) + 1) / (kseq n : ℝ)))⁻¹ := by
    rw [hgapCast]
    field_simp [hnpos.ne', hkR.ne', hden.ne']
    ring
  rw [hrewrite]
  have hmiddleNonneg :
      0 ≤ 3 / 4 + 1 / (4 * (n : ℝ)) := by positivity
  have honeNonneg :
      0 ≤ 1 + 2 * (((n : ℝ) + 1) / (kseq n : ℝ)) := by
    positivity
  calc
    ((n : ℝ) ^ 2 / (kseq n : ℝ)) *
          (3 / 4 + 1 / (4 * (n : ℝ))) *
          (1 - (((n : ℝ) + 1) / (kseq n : ℝ)))⁻¹ ≤
        ((n : ℝ) ^ 2 / (kseq n : ℝ)) *
          (3 / 4 + 1 / (4 * (n : ℝ))) *
          (1 + 2 * (((n : ℝ) + 1) / (kseq n : ℝ))) := by
      gcongr
    _ ≤ (D * Real.log (n : ℝ)) *
          (3 / 4 + 1 / (4 * (n : ℝ))) *
          (1 + 2 * (((n : ℝ) + 1) / (kseq n : ℝ))) := by
      gcongr
    _ ≤ (D * Real.log (n : ℝ)) *
          (3 / 4 + 2 * (((n : ℝ) + 1) / (kseq n : ℝ)) +
            1 / (2 * (n : ℝ))) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hfactor (mul_nonneg hD.le hlogpos.le)
    _ = Real.log (n : ℝ) *
          (3 * D / 4 +
            D * (2 * (((n : ℝ) + 1) / (kseq n : ℝ)) +
              1 / (2 * (n : ℝ)))) := by ring
    _ ≤ Real.log (n : ℝ) * (3 * D / 4 + eta) := by
      gcongr
    _ = (3 * D / 4 + eta) * Real.log (n : ℝ) := by ring

/-- **Polynomial small-ball corollary (ENNReal form).**  This is the exact
quantified statement of Corollary 2.4 in the AIHP manuscript. -/
theorem eventually_standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_polynomial_sharp
    (kseq : ℕ → ℕ) {A D alpha : ℝ}
    (hA : 0 < A) (hD : 0 < D)
    (halpha : A + 3 * D / 4 + 1 / 2 < alpha)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℝ,
      (standardRealGaussianColumnMatrixMeasure n (kseq n))
          {X | |realGramHafnianObservable n (kseq n) X - z| ≤
            (n : ℝ) ^ (-alpha) * realGramHafnianRMS n (kseq n)} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-A)) := by
  let eta : ℝ :=
    (alpha - (A + 3 * D / 4 + 1 / 2)) / 4
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  have hexponent := eventually_sharpReal_elementary_exponent_le_log
    kseq hD heta hk hscale
  let C : ℝ := realGaussianIntervalPrefactor 1 * Real.sqrt 2
  have hgrow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ eta)
      atTop atTop :=
    (tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop
  have hC : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ eta :=
    hgrow.eventually (eventually_ge_atTop C)
  filter_upwards [eventually_ge_atTop 2, hexponent, hC]
      with n hn hexpBound hCn
  intro z
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hdimensionStrong : 2 * n + 2 ≤ kseq n := hexpBound.1
  have hk2 : 2 ≤ kseq n := by omega
  have hdim : 2 * n - 1 ≤ kseq n := by omega
  have hkn : n + 2 ≤ kseq n := by omega
  have hsqrtOdd :
      Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) ≤
        Real.sqrt 2 * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) ≤
          Real.sqrt (((2 * n : ℕ) : ℝ)) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast (show 2 * n - 1 ≤ 2 * n by omega)
      _ = Real.sqrt (2 * (n : ℝ)) := by push_cast; rfl
      _ = Real.sqrt 2 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpref0 : 0 ≤ realGaussianIntervalPrefactor 1 :=
    realGaussianIntervalPrefactor_nonneg (by norm_num)
  have hsqrtCoefficient :
      realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) ≤
        (n : ℝ) ^ (1 / 2 + eta) := by
    calc
      realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) ≤
        C * Real.sqrt (n : ℝ) := by
          dsimp [C]
          nlinarith [mul_le_mul_of_nonneg_left hsqrtOdd hpref0]
      _ ≤ (n : ℝ) ^ eta * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right hCn (Real.sqrt_nonneg _)
      _ = (n : ℝ) ^ (1 / 2 + eta) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
        ring_nf
  have hexponential :
      Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((kseq n - n - 1 : ℕ) : ℝ))) ≤
        (n : ℝ) ^ (3 * D / 4 + eta) := by
    calc
      Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((kseq n - n - 1 : ℕ) : ℝ))) ≤
        Real.exp ((3 * D / 4 + eta) * Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr hexpBound.2
      _ = (n : ℝ) ^ (3 * D / 4 + eta) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
  have hcoefficient :
      realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp
            ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (4 * ((kseq n - n - 1 : ℕ) : ℝ))) ≤
        (n : ℝ) ^ (1 / 2 + 3 * D / 4 + 2 * eta) := by
    calc
      realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp
            ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (4 * ((kseq n - n - 1 : ℕ) : ℝ))) ≤
        (n : ℝ) ^ (1 / 2 + eta) *
          (n : ℝ) ^ (3 * D / 4 + eta) := by
            exact mul_le_mul hsqrtCoefficient hexponential
              (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
      _ = (n : ℝ) ^ (1 / 2 + 3 * D / 4 + 2 * eta) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
  have hbudget :
      (realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp
            ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (4 * ((kseq n - n - 1 : ℕ) : ℝ)))) *
          (n : ℝ) ^ (-alpha) ≤
        (n : ℝ) ^ (-A) := by
    calc
      (realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp
            ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (4 * ((kseq n - n - 1 : ℕ) : ℝ)))) *
          (n : ℝ) ^ (-alpha) ≤
        (n : ℝ) ^ (1 / 2 + 3 * D / 4 + 2 * eta) *
          (n : ℝ) ^ (-alpha) :=
        mul_le_mul_of_nonneg_right hcoefficient
          (Real.rpow_nonneg hnpos.le _)
      _ = (n : ℝ) ^
          (1 / 2 + 3 * D / 4 + 2 * eta - alpha) := by
        rw [← Real.rpow_add hnpos]
        congr 1
      _ ≤ (n : ℝ) ^ (-A) := by
        apply Real.rpow_le_rpow_of_exponent_le hnOne
        dsimp [eta]
        linarith
  have hfinite :=
    standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_exp_sharp
      hn1 hk2 hdim hkn z ((n : ℝ) ^ (-alpha)) (by positivity)
  have hcoefficient0 : 0 ≤
      realGaussianIntervalPrefactor 1 *
        Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
        Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((kseq n - n - 1 : ℕ) : ℝ))) := by positivity
  calc
    (standardRealGaussianColumnMatrixMeasure n (kseq n))
        {X | |realGramHafnianObservable n (kseq n) X - z| ≤
          (n : ℝ) ^ (-alpha) * realGramHafnianRMS n (kseq n)} ≤
      ENNReal.ofReal
          (realGaussianIntervalPrefactor 1 *
            Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
            Real.exp
              ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
                (4 * ((kseq n - n - 1 : ℕ) : ℝ)))) *
        ENNReal.ofReal ((n : ℝ) ^ (-alpha)) := hfinite
    _ = ENNReal.ofReal
        ((realGaussianIntervalPrefactor 1 *
            Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
            Real.exp
              ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
                (4 * ((kseq n - n - 1 : ℕ) : ℝ)))) *
          (n : ℝ) ^ (-alpha)) := by
      rw [ENNReal.ofReal_mul hcoefficient0]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-A)) :=
      ENNReal.ofReal_le_ofReal hbudget

/-- Paper-facing real-probability form of the polynomial corollary. -/
theorem eventually_standardRealGaussianColumnMatrix_normalizedShiftedSmallBallProbability_le_polynomial_sharp
    (kseq : ℕ → ℕ) {A D alpha : ℝ}
    (hA : 0 < A) (hD : 0 < D)
    (halpha : A + 3 * D / 4 + 1 / 2 < alpha)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℝ,
      (standardRealGaussianColumnMatrixMeasure n (kseq n)).real
          {X | |realGramHafnianObservable n (kseq n) X - z| ≤
            (n : ℝ) ^ (-alpha) * realGramHafnianRMS n (kseq n)} ≤
        (n : ℝ) ^ (-A) := by
  have henn :=
    eventually_standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_polynomial_sharp
      kseq hA hD halpha hk hscale
  filter_upwards [henn] with n hn
  intro z
  have hp : 0 ≤ (n : ℝ) ^ (-A) := Real.rpow_nonneg (by positivity) _
  have hreal :
      ((standardRealGaussianColumnMatrixMeasure n (kseq n))
        {X | |realGramHafnianObservable n (kseq n) X - z| ≤
          (n : ℝ) ^ (-alpha) *
            realGramHafnianRMS n (kseq n)}).toReal ≤
        (ENNReal.ofReal ((n : ℝ) ^ (-A))).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hn z)
  change ((standardRealGaussianColumnMatrixMeasure n (kseq n))
      {X | |realGramHafnianObservable n (kseq n) X - z| ≤
        (n : ℝ) ^ (-alpha) * realGramHafnianRMS n (kseq n)}).toReal ≤ _
  simpa [ENNReal.toReal_ofReal hp] using hreal

end

end LogdetLean.GramHafnian
