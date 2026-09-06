import LogdetLean.Coherence.NoncentralPearsonRateAlgebra
import Mathlib.Tactic
/-!
# Fine shift of the exact Pearson threshold

The planted height intensity depends on a first-order, not merely relative,
comparison of the exact studentized thresholds at levels `a_p+x` and `a_p`.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real
open scoped Topology

theorem classicalCoherenceThreshold_eq_zero_add
    (m p : ℕ) (x : ℝ) :
    classicalCoherenceThreshold m p x =
      classicalCoherenceThreshold m p 0 + x := by
  unfold classicalCoherenceThreshold
  ring

/-- Exact difference of the two squared studentized thresholds. -/
theorem pearsonExactThresholdSq_sub_zero
    {m p : ℕ} {x : ℝ} (hm : 1 ≤ m)
    (hxrange : classicalCoherenceThreshold m p x < (m : ℝ))
    (h0range : classicalCoherenceThreshold m p 0 < (m : ℝ)) :
    pearsonExactThresholdSq m p x - pearsonExactThresholdSq m p 0 =
      x * (((m : ℝ) - 1) / (m : ℝ)) /
        ((1 - classicalCoherenceThreshold m p x / (m : ℝ)) *
          (1 - classicalCoherenceThreshold m p 0 / (m : ℝ))) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm))
  have hdx : (m : ℝ) - classicalCoherenceThreshold m p x ≠ 0 :=
    (sub_pos.mpr hxrange).ne'
  have hd0 : (m : ℝ) - classicalCoherenceThreshold m p 0 ≠ 0 :=
    (sub_pos.mpr h0range).ne'
  rw [pearsonExactThresholdSq_eq, pearsonExactThresholdSq_eq]
  field_simp [hm0, hdx, hd0]
  rw [classicalCoherenceThreshold_eq_zero_add]
  ring

/-- The exact squared-threshold increment converges to the score increment
itself, uniformly over every nonsingular gap. -/
theorem tendsto_pearsonExactThresholdSq_sub_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      pearsonExactThresholdSq (mseq p) p x -
        pearsonExactThresholdSq (mseq p) p 0)
      atTop (nhds x) := by
  have hpredNat := tendsto_pred_mseq_div_mseq_one hadm
  have hpred : Tendsto (fun p : ℕ ↦
      ((mseq p : ℝ) - 1) / (mseq p : ℝ)) atTop (nhds 1) := by
    apply hpredNat.congr'
    filter_upwards [hadm] with p hp
    have hm1 : 1 ≤ mseq p := (by omega : 1 ≤ 2).trans (hp.1.trans hp.2)
    rw [Nat.cast_sub hm1, Nat.cast_one]
  have hxratio := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  have h0ratio := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm 0
  have hdx : Tendsto (fun p : ℕ ↦
      1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _p : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).sub hxratio
  have hd0 : Tendsto (fun p : ℕ ↦
      1 - classicalCoherenceThreshold (mseq p) p 0 / (mseq p : ℝ))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _p : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).sub h0ratio
  have hcoef : Tendsto (fun p : ℕ ↦
      (((mseq p : ℝ) - 1) / (mseq p : ℝ)) /
        ((1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) *
          (1 - classicalCoherenceThreshold (mseq p) p 0 / (mseq p : ℝ))))
      atTop (nhds 1) := by
    have h := hpred.div (hdx.mul hd0) (by norm_num : (1 * 1 : ℝ) ≠ 0)
    have heq : ((fun p : ℕ ↦ ((mseq p : ℝ) - 1) / (mseq p : ℝ)) /
        (fun p : ℕ ↦
          (1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) *
            (1 - classicalCoherenceThreshold (mseq p) p 0 / (mseq p : ℝ)))) =ᶠ[atTop]
        (fun p : ℕ ↦
          (((mseq p : ℝ) - 1) / (mseq p : ℝ)) /
            ((1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) *
              (1 - classicalCoherenceThreshold (mseq p) p 0 / (mseq p : ℝ)))) :=
      Eventually.of_forall fun _p ↦ rfl
    simpa only [one_div, inv_one, mul_one] using h.congr' heq
  have hmul := hcoef.const_mul x
  have hmul' : Tendsto (fun p ↦ x *
      ((((mseq p : ℝ) - 1) / (mseq p : ℝ)) /
        ((1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) *
          (1 - classicalCoherenceThreshold (mseq p) p 0 / (mseq p : ℝ)))))
      atTop (nhds x) := by simpa only [mul_one] using hmul
  apply hmul'.congr'
  filter_upwards [hadm,
      eventually_classicalCoherenceThreshold_scoreRange hadm x,
      eventually_classicalCoherenceThreshold_scoreRange hadm 0]
    with p hp hxr h0r
  have hraw := (pearsonExactThresholdSq_sub_zero
    ((by omega : 1 ≤ 2).trans (hp.1.trans hp.2))
    hxr.2 h0r.2).symm
  calc
    x * ((((mseq p : ℝ) - 1) / (mseq p : ℝ)) /
        ((1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) *
          (1 - classicalCoherenceThreshold (mseq p) p 0 / (mseq p : ℝ)))) =
      x * (((mseq p : ℝ) - 1) / (mseq p : ℝ)) /
        ((1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) *
          (1 - classicalCoherenceThreshold (mseq p) p 0 / (mseq p : ℝ))) := by ring
    _ = _ := hraw

/-- The exact baseline studentized threshold diverges. -/
theorem tendsto_pearsonExactThreshold_zero_atTop
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦ pearsonExactThreshold (mseq p) p 0)
      atTop atTop := by
  have hlevel := tendsto_classicalCoherenceThreshold_atTop 0
  have hratio := tendsto_pearsonExactThreshold_div_sqrt_level_one hadm 0
  have hsqrt := Real.tendsto_sqrt_atTop.comp hlevel
  have hprod := hsqrt.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hratio
  apply hprod.congr'
  filter_upwards [eventually_classicalCoherenceThreshold_scoreRange hadm 0]
    with p hrange
  have hsqrt0 : 0 < Real.sqrt
      (classicalCoherenceThreshold (mseq p) p 0) := Real.sqrt_pos.2 hrange.1
  change Real.sqrt (classicalCoherenceThreshold (mseq p) p 0) *
      (pearsonExactThreshold (mseq p) p 0 /
        Real.sqrt (classicalCoherenceThreshold (mseq p) p 0)) =
    pearsonExactThreshold (mseq p) p 0
  field_simp [hsqrt0.ne']

/-- The exact baseline studentized threshold has the classical
`2 * sqrt(log p)` scale, uniformly over every nonsingular gap. -/
theorem tendsto_pearsonExactThreshold_zero_div_sqrt_log_two
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦
      pearsonExactThreshold (mseq p) p 0 /
        Real.sqrt (Real.log (p : ℝ)))
      atTop (nhds 2) := by
  have hq := tendsto_pearsonExactThreshold_div_sqrt_level_one hadm 0
  have hs := tendsto_sqrt_log_div_classicalCoherenceThreshold 0
  have hdiv := hq.div hs (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have heq : (fun p : ℕ ↦
      (pearsonExactThreshold (mseq p) p 0 /
          Real.sqrt (classicalCoherenceThreshold (mseq p) p 0)) /
        Real.sqrt (Real.log (p : ℝ) /
          classicalCoherenceThreshold (mseq p) p 0)) =ᶠ[atTop]
      (fun p : ℕ ↦
        pearsonExactThreshold (mseq p) p 0 /
          Real.sqrt (Real.log (p : ℝ))) := by
    filter_upwards [eventually_classicalCoherenceThreshold_scoreRange hadm 0,
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_gt_atTop (0 : ℝ))]
      with p hp hlog
    have ha : 0 < classicalCoherenceThreshold (mseq p) p 0 := hp.1
    have hsa : 0 < Real.sqrt
        (classicalCoherenceThreshold (mseq p) p 0) := Real.sqrt_pos.2 ha
    have hsa0 : 0 < Real.sqrt
        (classicalCoherenceThreshold 0 p 0) := by
      simpa [classicalCoherenceThreshold] using hsa
    have hsl : 0 < Real.sqrt (Real.log (p : ℝ)) := Real.sqrt_pos.2 hlog
    have hlog' : 0 ≤ Real.log (p : ℝ) := by
      simpa [Function.comp_apply] using hlog.le
    rw [show classicalCoherenceThreshold (mseq p) p 0 =
        classicalCoherenceThreshold 0 p 0 by rfl]
    rw [Real.sqrt_div hlog']
    field_simp [hsa0.ne', hsl.ne']
  norm_num at hdiv ⊢
  exact hdiv.congr' heq

/-- First-order score shift of the exact studentized threshold. -/
theorem tendsto_pearsonExactThreshold_zero_mul_sub
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      pearsonExactThreshold (mseq p) p 0 *
        (pearsonExactThreshold (mseq p) p x -
          pearsonExactThreshold (mseq p) p 0))
      atTop (nhds (x / 2)) := by
  let q0 : ℕ → ℝ := fun p ↦ pearsonExactThreshold (mseq p) p 0
  let qx : ℕ → ℝ := fun p ↦ pearsonExactThreshold (mseq p) p x
  have hq0Top : Tendsto q0 atTop atTop :=
    tendsto_pearsonExactThreshold_zero_atTop hadm
  have hqxTop : Tendsto qx atTop atTop := by
    have hlevel := tendsto_classicalCoherenceThreshold_atTop x
    have hratio := tendsto_pearsonExactThreshold_div_sqrt_level_one hadm x
    have hsqrt := Real.tendsto_sqrt_atTop.comp hlevel
    have hprod := hsqrt.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hratio
    apply hprod.congr'
    filter_upwards [eventually_classicalCoherenceThreshold_scoreRange hadm x]
      with p hrange
    have hsqrt0 : 0 < Real.sqrt
        (classicalCoherenceThreshold (mseq p) p x) := Real.sqrt_pos.2 hrange.1
    change Real.sqrt (classicalCoherenceThreshold (mseq p) p x) *
        (pearsonExactThreshold (mseq p) p x /
          Real.sqrt (classicalCoherenceThreshold (mseq p) p x)) =
      pearsonExactThreshold (mseq p) p x
    field_simp [hsqrt0.ne']
  have hsqdiff : Tendsto (fun p ↦ qx p ^ 2 - q0 p ^ 2)
      atTop (nhds x) := by
    have hraw := tendsto_pearsonExactThresholdSq_sub_zero hadm x
    apply hraw.congr'
    filter_upwards [hadm,
        eventually_classicalCoherenceThreshold_scoreRange hadm x,
        eventually_classicalCoherenceThreshold_scoreRange hadm 0]
      with p hp hxr h0r
    have hsx := sq_pearsonExactThreshold
      (m := mseq p) (p := p) (x := x)
      ((by omega : 1 ≤ 2).trans (hp.1.trans hp.2)) hxr.1.le hxr.2
    have hs0 := sq_pearsonExactThreshold
      (m := mseq p) (p := p) (x := 0)
      ((by omega : 1 ≤ 2).trans (hp.1.trans hp.2)) h0r.1.le h0r.2
    dsimp [q0, qx]
    unfold pearsonExactThresholdSq at *
    nlinarith
  have hsumTop : Tendsto (fun p ↦ qx p + q0 p) atTop atTop := by
    have hle : ∀ᶠ p in atTop, qx p ≤ qx p + q0 p := by
      filter_upwards [hq0Top.eventually (eventually_ge_atTop (0 : ℝ))]
        with p hp0
      linarith
    exact Filter.tendsto_atTop_mono' atTop hle hqxTop
  have hdiff : Tendsto (fun p ↦ qx p - q0 p) atTop (nhds 0) := by
    have hdiv := hsqdiff.div_atTop hsumTop
    apply hdiv.congr'
    filter_upwards [hq0Top.eventually (eventually_gt_atTop 0),
      hqxTop.eventually (eventually_gt_atTop 0)] with p h0 hxpos
    have hsumne : qx p + q0 p ≠ 0 := by linarith
    field_simp [hsumne]
    ring
  have hratio : Tendsto (fun p ↦ qx p / q0 p) atTop (nhds 1) := by
    have hsmall := hdiff.div_atTop hq0Top
    have hadd := (tendsto_const_nhds : Tendsto (fun _p : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).add hsmall
    have heq : (fun p ↦ 1 + (qx p - q0 p) / q0 p) =ᶠ[atTop]
        (fun p ↦ qx p / q0 p) := by
      filter_upwards [hq0Top.eventually (eventually_ne_atTop 0)] with p h0
      field_simp [h0]
      ring
    simpa only [add_zero] using hadd.congr' heq
  have hhalf : Tendsto (fun p ↦ q0 p / (qx p + q0 p))
      atTop (nhds (1 / 2 : ℝ)) := by
    have hden := hratio.add_const 1
    have hraw := (tendsto_const_nhds : Tendsto (fun _p : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).div hden (by norm_num : (1 + 1 : ℝ) ≠ 0)
    have heq : ((fun _p : ℕ ↦ (1 : ℝ)) /
        (fun p ↦ qx p / q0 p + 1)) =ᶠ[atTop]
        (fun p ↦ q0 p / (qx p + q0 p)) := by
      filter_upwards [hq0Top.eventually (eventually_ne_atTop 0)] with p h0
      change 1 / (qx p / q0 p + 1) = q0 p / (qx p + q0 p)
      field_simp [h0]
    norm_num at hraw ⊢
    exact hraw.congr' heq
  have hprod := hhalf.mul hsqdiff
  have hprod' : Tendsto (fun p ↦
      q0 p / (qx p + q0 p) * (qx p ^ 2 - q0 p ^ 2))
      atTop (nhds (x / 2)) := by
    convert hprod using 1 <;> ring
  apply hprod'.congr'
  filter_upwards [hq0Top.eventually (eventually_gt_atTop 0),
      hqxTop.eventually (eventually_gt_atTop 0)] with p h0 hxpos
  have hsumne : qx p + q0 p ≠ 0 := by linarith
  field_simp [hsumne]
  ring

end

end LogdetLean.Coherence
