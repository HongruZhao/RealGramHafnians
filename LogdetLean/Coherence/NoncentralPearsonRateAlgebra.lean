import LogdetLean.Coherence.BetaEndpointAsymptotic
/-!
# Deterministic rate algebra for noncentral Pearson moderate deviations

This module contains no probability approximation theorem.  It records the
exact conversion from a squared Pearson-correlation threshold to the
studentized threshold and proves that the two deterministic error profiles in
the proposed moderate-deviation bound vanish throughout every all-gap regime.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real
open scoped Topology Real

/-- Exact squared threshold for the studentized Pearson statistic
`T = sqrt (m - 1) * R / sqrt (1 - R^2)` when the squared-correlation score
`m * R^2` is compared with the classical level `a_p + x`. -/
def pearsonExactThresholdSq (m p : ℕ) (x : ℝ) : ℝ :=
  ((m : ℝ) - 1) * classicalCoherenceThreshold m p x /
    ((m : ℝ) - classicalCoherenceThreshold m p x)

/-- Nonnegative square root of the exact squared Pearson threshold. -/
def pearsonExactThreshold (m p : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (pearsonExactThresholdSq m p x)

/-- The displayed exact threshold formula, exposed as a rewrite theorem. -/
theorem pearsonExactThresholdSq_eq (m p : ℕ) (x : ℝ) :
    pearsonExactThresholdSq m p x =
      ((m : ℝ) - 1) * classicalCoherenceThreshold m p x /
        ((m : ℝ) - classicalCoherenceThreshold m p x) := rfl

/-- Squaring the exact threshold recovers its defining rational expression
on the natural score range `0 <= a_p + x < m`. -/
theorem sq_pearsonExactThreshold
    {m p : ℕ} {x : ℝ} (hm : 1 ≤ m)
    (hlevel0 : 0 ≤ classicalCoherenceThreshold m p x)
    (hlevelm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    pearsonExactThreshold m p x ^ 2 =
      ((m : ℝ) - 1) * classicalCoherenceThreshold m p x /
        ((m : ℝ) - classicalCoherenceThreshold m p x) := by
  unfold pearsonExactThreshold pearsonExactThresholdSq
  rw [Real.sq_sqrt]
  exact div_nonneg
    (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hm)) hlevel0)
    (sub_nonneg.mpr hlevelm.le)

/-- Exact deterministic event-algebra behind the Pearson threshold.  No
distributional assertion is used: on `R^2 < 1`, crossing `m R^2 > y` is
equivalent to crossing the corresponding studentized squared threshold. -/
theorem pearson_score_iff_studentized_score
    {m : ℕ} (hm : 2 ≤ m) {r y : ℝ}
    (hr : r ^ 2 < 1) (_hy0 : 0 ≤ y) (hym : y < (m : ℝ)) :
    y < (m : ℝ) * r ^ 2 ↔
      ((m : ℝ) - 1) * y / ((m : ℝ) - y) <
        ((m : ℝ) - 1) * r ^ 2 / (1 - r ^ 2) := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [div_lt_div_iff₀ (sub_pos.mpr hym) (sub_pos.mpr hr)]
  have hid :
      (((m : ℝ) - 1) * r ^ 2) * ((m : ℝ) - y) -
          (((m : ℝ) - 1) * y) * (1 - r ^ 2) =
        ((m : ℝ) - 1) * ((m : ℝ) * r ^ 2 - y) := by
    ring
  constructor
  · intro h
    have hprod :
        0 < ((m : ℝ) - 1) * ((m : ℝ) * r ^ 2 - y) :=
      mul_pos hm1 (sub_pos.mpr h)
    rw [← hid] at hprod
    linarith
  · intro h
    have hprod :
        0 < ((m : ℝ) - 1) * ((m : ℝ) * r ^ 2 - y) := by
      rw [← hid]
      linarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hm1).mp hprod)

/-- Classical-level specialization of the exact score conversion. -/
theorem classicalPearson_score_iff_studentized_score
    {m p : ℕ} (hm : 2 ≤ m) {r x : ℝ}
    (hr : r ^ 2 < 1)
    (hlevel0 : 0 ≤ classicalCoherenceThreshold m p x)
    (hlevelm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    classicalCoherenceThreshold m p x < (m : ℝ) * r ^ 2 ↔
      pearsonExactThresholdSq m p x <
        ((m : ℝ) - 1) * r ^ 2 / (1 - r ^ 2) := by
  simpa [pearsonExactThresholdSq] using
    pearson_score_iff_studentized_score hm hr hlevel0 hlevelm

/-- In every all-gap regime, the classical level eventually lies in its
natural exact-score range `(0,m)`. -/
theorem eventually_classicalCoherenceThreshold_scoreRange
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    ∀ᶠ p in atTop,
      0 < classicalCoherenceThreshold (mseq p) p x ∧
        classicalCoherenceThreshold (mseq p) p x < (mseq p : ℝ) := by
  have hlevel := tendsto_classicalCoherenceThreshold_atTop x
  have hratio := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  filter_upwards [hadm,
      hlevel.eventually (eventually_gt_atTop 0),
      hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with p hp hlevelp hratiop
  have hm0 : (0 : ℝ) < (mseq p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hp.1.trans hp.2))
  constructor
  · simpa [classicalCoherenceThreshold] using hlevelp
  · exact (div_lt_one hm0).mp (by
      simpa [classicalCoherenceThreshold] using hratiop)

/-- The exact squared studentized threshold is asymptotic to the original
squared-correlation score level, uniformly over every gap `m-p`. -/
theorem tendsto_pearsonExactThresholdSq_div_level_one
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      pearsonExactThresholdSq (mseq p) p x /
        classicalCoherenceThreshold (mseq p) p x)
      atTop (nhds 1) := by
  have hpredNat := tendsto_pred_mseq_div_mseq_one hadm
  have hpred : Tendsto (fun p : ℕ ↦
      ((mseq p : ℝ) - 1) / (mseq p : ℝ))
      atTop (nhds 1) := by
    apply hpredNat.congr'
    filter_upwards [hadm] with p hp
    have hm1 : 1 ≤ mseq p :=
      (by omega : 1 ≤ 2).trans (hp.1.trans hp.2)
    rw [Nat.cast_sub hm1, Nat.cast_one]
  have hlevel := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  have hden : Tendsto (fun p : ℕ ↦
      1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ))
      atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _p : ℕ ↦ (1 : ℝ))
        atTop (nhds 1)).sub hlevel
  have hquot := hpred.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hquot1 : Tendsto (fun p : ℕ ↦
      (((mseq p : ℝ) - 1) / (mseq p : ℝ)) /
        (1 - classicalCoherenceThreshold (mseq p) p x /
          (mseq p : ℝ))) atTop (nhds 1) := by
    change Tendsto (fun p : ℕ ↦
      (((mseq p : ℝ) - 1) / (mseq p : ℝ)) /
        (1 - classicalCoherenceThreshold (mseq p) p x /
          (mseq p : ℝ))) atTop (nhds ((1 : ℝ) / 1)) at hquot
    simpa using hquot
  apply hquot1.congr'
  filter_upwards [hadm,
    eventually_classicalCoherenceThreshold_scoreRange hadm x]
    with p hp hrange
  have hm0 : (mseq p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      (lt_of_lt_of_le (by omega : 0 < 2) (hp.1.trans hp.2)))
  have hlevel0 :
      classicalCoherenceThreshold (mseq p) p x ≠ 0 := hrange.1.ne'
  have hden0 :
      (mseq p : ℝ) - classicalCoherenceThreshold (mseq p) p x ≠ 0 :=
    (sub_pos.mpr hrange.2).ne'
  unfold pearsonExactThresholdSq
  field_simp [hm0, hlevel0, hden0]

/-- Consequently, the exact studentized threshold divided by
`sqrt(a_p+x)` tends to one.  This is a relative deterministic replacement;
it is not a moderate-deviation probability statement. -/
theorem tendsto_pearsonExactThreshold_div_sqrt_level_one
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      pearsonExactThreshold (mseq p) p x /
        Real.sqrt (classicalCoherenceThreshold (mseq p) p x))
      atTop (nhds 1) := by
  have hratio := tendsto_pearsonExactThresholdSq_div_level_one hadm x
  have hsqrt : Tendsto (fun p : ℕ ↦
      Real.sqrt
        (pearsonExactThresholdSq (mseq p) p x /
          classicalCoherenceThreshold (mseq p) p x))
      atTop (nhds 1) := by
    simpa using hratio.sqrt
  apply hsqrt.congr'
  filter_upwards [hadm,
    eventually_classicalCoherenceThreshold_scoreRange hadm x]
    with p hp hrange
  have hm1 : (1 : ℝ) ≤ (mseq p : ℝ) := by
    exact_mod_cast ((by omega : 1 ≤ 2).trans (hp.1.trans hp.2))
  have hqSq0 : 0 ≤ pearsonExactThresholdSq (mseq p) p x := by
    unfold pearsonExactThresholdSq
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hm1) hrange.1.le)
      (sub_nonneg.mpr hrange.2.le)
  simpa [pearsonExactThreshold] using
    (Real.sqrt_div hqSq0
      (classicalCoherenceThreshold (mseq p) p x))

/-- The first deterministic rate in the audited moderate-deviation bound. -/
def pearsonMDGaussianPerturbationRate (m p : ℕ) : ℝ :=
  Real.log (p : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt (m : ℝ)

/-- The discarded-chi-event rate after division by the smallest Gaussian
tail allowed by `q + |lambda| <= C sqrt(log p)`. -/
def pearsonMDDiscardedChiRate (C L : ℝ) (p : ℕ) : ℝ :=
  Real.sqrt (Real.log (p : ℝ)) *
    (p : ℝ) ^ (C ^ 2 / 2 - L)

/-- Relative chi-radius used in the good-event truncation. -/
def pearsonMDChiRadius (L : ℝ) (m p : ℕ) : ℝ :=
  Real.sqrt
    (L * Real.log (p : ℝ) / ((m : ℝ) - 1))

/-- Perturbation of a Gaussian-tail argument on the simultaneous chi good
event. -/
def pearsonMDArgumentPerturbation
    (L q lambda : ℝ) (m p : ℕ) : ℝ :=
  2 * (q + |lambda|) * pearsonMDChiRadius L m p

/-- Deterministic exponent in the relative normal-tail perturbation bound.
The constant `exp(3/2)` is the elementary hazard-rate constant used in the
mathematical audit. -/
def pearsonMDTailExponent
    (L q lambda : ℝ) (m p : ℕ) : ℝ :=
  Real.exp (3 / 2 : ℝ) * pearsonMDArgumentPerturbation L q lambda m p *
    (1 + q + |lambda| + pearsonMDArgumentPerturbation L q lambda m p)

/-- Any fixed power of `log p`, divided by `m - 1`, vanishes uniformly over
all admissible sequences. -/
private theorem tendsto_log_pow_div_mseq_sub_one_zero
    (n : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) ^ n / ((mseq p : ℝ) - 1))
      atTop (nhds 0) := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hbase : Tendsto
      (fun p : ℕ ↦ Real.log (p : ℝ) ^ n / (p : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero.comp hpR
  apply squeeze_zero'
  · filter_upwards [hadm, eventually_ge_atTop 1] with p hadmp hp
    have hlog0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp)
    have hm1 : (0 : ℝ) < (mseq p : ℝ) - 1 := by
      have hmR : (2 : ℝ) ≤ (mseq p : ℝ) := by
        exact_mod_cast hadmp.1.trans hadmp.2
      linarith
    exact div_nonneg (pow_nonneg hlog0 n) hm1.le
  · filter_upwards [hadm] with p hp
    have hp2 : 2 ≤ p := hp.1
    have hpR0 : (0 : ℝ) < (p : ℝ) := by positivity
    have hlog0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    have hmR : (p : ℝ) ≤ (mseq p : ℝ) := by exact_mod_cast hp.2
    have hden : (p : ℝ) / 2 ≤ (mseq p : ℝ) - 1 := by
      have hpR2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    calc
      Real.log (p : ℝ) ^ n / ((mseq p : ℝ) - 1) ≤
          Real.log (p : ℝ) ^ n / ((p : ℝ) / 2) :=
        div_le_div_of_nonneg_left (pow_nonneg hlog0 n)
          (div_pos hpR0 (by norm_num)) hden
      _ = 2 * (Real.log (p : ℝ) ^ n / (p : ℝ)) := by
        field_simp [hpR0.ne']
  · simpa using hbase.const_mul 2

/-- The chi good-event radius itself tends to zero. -/
theorem tendsto_pearsonMDChiRadius_zero
    {L : ℝ} {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦ pearsonMDChiRadius L (mseq p) p)
      atTop (nhds 0) := by
  have hratio := tendsto_log_pow_div_mseq_sub_one_zero 1 hadm
  have hscaled : Tendsto
      (fun p : ℕ ↦
        L * (Real.log (p : ℝ) / ((mseq p : ℝ) - 1)))
      atTop (nhds 0) := by
    simpa using hratio.const_mul L
  have hsqrt : Tendsto
      (fun p : ℕ ↦
        Real.sqrt (L * (Real.log (p : ℝ) /
          ((mseq p : ℝ) - 1)))) atTop (nhds 0) := by
    simpa using hscaled.sqrt
  apply hsqrt.congr'
  filter_upwards with p
  unfold pearsonMDChiRadius
  apply congrArg Real.sqrt
  ring

/-- Multiplying the chi radius by `sqrt(log p)` still gives a null rate. -/
theorem tendsto_sqrtLog_mul_pearsonMDChiRadius_zero
    {L : ℝ} {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦
      Real.sqrt (Real.log (p : ℝ)) *
        pearsonMDChiRadius L (mseq p) p)
      atTop (nhds 0) := by
  have hsq := tendsto_log_pow_div_mseq_sub_one_zero 2 hadm
  have hscaled : Tendsto
      (fun p : ℕ ↦
        L * (Real.log (p : ℝ) ^ 2 / ((mseq p : ℝ) - 1)))
      atTop (nhds 0) := by
    simpa using hsq.const_mul L
  have hsqrt : Tendsto
      (fun p : ℕ ↦ Real.sqrt
        (L * (Real.log (p : ℝ) ^ 2 /
          ((mseq p : ℝ) - 1)))) atTop (nhds 0) := by
    simpa using hscaled.sqrt
  apply hsqrt.congr'
  filter_upwards [hadm] with p hp
  have hp1 : 1 ≤ p := (by omega : 1 ≤ 2).trans hp.1
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hm1 : (0 : ℝ) < (mseq p : ℝ) - 1 := by
    have hmR : (2 : ℝ) ≤ (mseq p : ℝ) := by
      exact_mod_cast hp.1.trans hp.2
    linarith
  unfold pearsonMDChiRadius
  rw [← Real.sqrt_mul hlog0]
  apply congrArg Real.sqrt
  ring

/-- Multiplying the chi radius by `log p` also gives a null rate.  Squaring
this quantity exposes the audited `log^3/(m-1)` rate. -/
theorem tendsto_log_mul_pearsonMDChiRadius_zero
    {L : ℝ} (hL : 0 ≤ L) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) * pearsonMDChiRadius L (mseq p) p)
      atTop (nhds 0) := by
  have hcube := tendsto_log_pow_div_mseq_sub_one_zero 3 hadm
  have hscaled : Tendsto
      (fun p : ℕ ↦
        L * (Real.log (p : ℝ) ^ 3 / ((mseq p : ℝ) - 1)))
      atTop (nhds 0) := by
    simpa using hcube.const_mul L
  have hsqrt : Tendsto
      (fun p : ℕ ↦ Real.sqrt
        (L * (Real.log (p : ℝ) ^ 3 /
          ((mseq p : ℝ) - 1)))) atTop (nhds 0) := by
    simpa using hscaled.sqrt
  apply hsqrt.congr'
  filter_upwards [hadm] with p hp
  have hp1 : 1 ≤ p := (by omega : 1 ≤ 2).trans hp.1
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hm1 : (0 : ℝ) < (mseq p : ℝ) - 1 := by
    have hmR : (2 : ℝ) ≤ (mseq p : ℝ) := by
      exact_mod_cast hp.1.trans hp.2
    linarith
  let B : ℝ := L * Real.log (p : ℝ) / ((mseq p : ℝ) - 1)
  let R : ℝ := L * (Real.log (p : ℝ) ^ 3 /
    ((mseq p : ℝ) - 1))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hleft0 : 0 ≤ Real.log (p : ℝ) * Real.sqrt B :=
    mul_nonneg hlog0 (Real.sqrt_nonneg _)
  have hright0 : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  have hleftsq :
      (Real.log (p : ℝ) * Real.sqrt B) ^ 2 = R := by
    rw [mul_pow, Real.sq_sqrt hB0]
    dsimp [B, R]
    field_simp [hm1.ne']
  have hrightsq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR0
  change Real.sqrt R = Real.log (p : ℝ) * Real.sqrt B
  nlinarith

/-- The concentration side condition used in the finite moderate-deviation
inequality, `sqrt(L log p/(m-1)) <= 1/4`, holds eventually in every all-gap
regime. -/
theorem eventually_pearsonMDChiRadius_le_quarter
    {L : ℝ} {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    ∀ᶠ p in atTop,
      pearsonMDChiRadius L (mseq p) p ≤ (1 / 4 : ℝ) := by
  have h := tendsto_pearsonMDChiRadius_zero (L := L) hadm
  exact (h.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
      fun _ hp ↦ hp.le

/-- Under the explicit coherence-scale hypothesis
`q + |lambda| <= C sqrt(log p)`, the good-event perturbation of the Gaussian
tail argument tends to zero. -/
theorem tendsto_pearsonMDArgumentPerturbation_zero
    {C L : ℝ} (hC : 0 ≤ C) {mseq : ℕ → ℕ}
    {qseq lambdaSeq : ℕ → ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hq : ∀ᶠ p in atTop, 0 ≤ qseq p)
    (hscale : ∀ᶠ p in atTop,
      qseq p + |lambdaSeq p| ≤
        C * Real.sqrt (Real.log (p : ℝ))) :
    Tendsto (fun p : ℕ ↦
      pearsonMDArgumentPerturbation
        L (qseq p) (lambdaSeq p) (mseq p) p)
      atTop (nhds 0) := by
  have hscaled :=
    tendsto_sqrtLog_mul_pearsonMDChiRadius_zero
      (L := L) (mseq := mseq) hadm
  have hupper : Tendsto (fun p : ℕ ↦
      (2 * C) *
        (Real.sqrt (Real.log (p : ℝ)) *
          pearsonMDChiRadius L (mseq p) p))
      atTop (nhds 0) := by
    simpa using hscaled.const_mul (2 * C)
  apply squeeze_zero'
  · filter_upwards [hq] with p hqp
    unfold pearsonMDArgumentPerturbation
    exact mul_nonneg
      (mul_nonneg (by norm_num) (add_nonneg hqp (abs_nonneg _)))
      (Real.sqrt_nonneg _)
  · filter_upwards [hadm, hq, hscale] with p hp hqp hscalep
    have hp1 : 1 ≤ p := (by omega : 1 ≤ 2).trans hp.1
    have hlog0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp1)
    have hs0 : 0 ≤ qseq p + |lambdaSeq p| :=
      add_nonneg hqp (abs_nonneg _)
    have hright0 : 0 ≤ C * Real.sqrt (Real.log (p : ℝ)) :=
      mul_nonneg hC (Real.sqrt_nonneg _)
    have hradius0 : 0 ≤ pearsonMDChiRadius L (mseq p) p :=
      Real.sqrt_nonneg _
    calc
      pearsonMDArgumentPerturbation
          L (qseq p) (lambdaSeq p) (mseq p) p =
          2 * (qseq p + |lambdaSeq p|) *
            pearsonMDChiRadius L (mseq p) p := rfl
      _ ≤ 2 * (C * Real.sqrt (Real.log (p : ℝ))) *
            pearsonMDChiRadius L (mseq p) p := by
        gcongr
      _ = (2 * C) *
            (Real.sqrt (Real.log (p : ℝ)) *
              pearsonMDChiRadius L (mseq p) p) := by ring
  · exact hupper

/-- The argument perturbation times its coherence-scale location also tends
to zero.  This is the nontrivial cross term in the normal-tail exponent. -/
theorem tendsto_pearsonMDArgumentPerturbation_mul_scale_zero
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    {mseq : ℕ → ℕ} {qseq lambdaSeq : ℕ → ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hq : ∀ᶠ p in atTop, 0 ≤ qseq p)
    (hscale : ∀ᶠ p in atTop,
      qseq p + |lambdaSeq p| ≤
        C * Real.sqrt (Real.log (p : ℝ))) :
    Tendsto (fun p : ℕ ↦
      pearsonMDArgumentPerturbation
          L (qseq p) (lambdaSeq p) (mseq p) p *
        (qseq p + |lambdaSeq p|))
      atTop (nhds 0) := by
  have hlogradius := tendsto_log_mul_pearsonMDChiRadius_zero
    (L := L) hL hadm
  have hupper : Tendsto (fun p : ℕ ↦
      (2 * C ^ 2) *
        (Real.log (p : ℝ) * pearsonMDChiRadius L (mseq p) p))
      atTop (nhds 0) := by
    simpa using hlogradius.const_mul (2 * C ^ 2)
  apply squeeze_zero'
  · filter_upwards [hq] with p hqp
    unfold pearsonMDArgumentPerturbation
    have hs0 : 0 ≤ qseq p + |lambdaSeq p| :=
      add_nonneg hqp (abs_nonneg _)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hs0)
        (Real.sqrt_nonneg _)) hs0
  · filter_upwards [hadm, hq, hscale] with p hp hqp hscalep
    have hp1 : 1 ≤ p := (by omega : 1 ≤ 2).trans hp.1
    have hlog0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp1)
    have hs0 : 0 ≤ qseq p + |lambdaSeq p| :=
      add_nonneg hqp (abs_nonneg _)
    have hb0 : 0 ≤ C * Real.sqrt (Real.log (p : ℝ)) :=
      mul_nonneg hC (Real.sqrt_nonneg _)
    have hsquare :
        (qseq p + |lambdaSeq p|) ^ 2 ≤
          (C * Real.sqrt (Real.log (p : ℝ))) ^ 2 :=
      (sq_le_sq₀ hs0 hb0).2 hscalep
    have hradius0 : 0 ≤ pearsonMDChiRadius L (mseq p) p :=
      Real.sqrt_nonneg _
    calc
      pearsonMDArgumentPerturbation
          L (qseq p) (lambdaSeq p) (mseq p) p *
          (qseq p + |lambdaSeq p|) =
          2 * (qseq p + |lambdaSeq p|) ^ 2 *
            pearsonMDChiRadius L (mseq p) p := by
        unfold pearsonMDArgumentPerturbation
        ring
      _ ≤ 2 * (C * Real.sqrt (Real.log (p : ℝ))) ^ 2 *
            pearsonMDChiRadius L (mseq p) p := by
        gcongr
      _ = (2 * C ^ 2) *
            (Real.log (p : ℝ) *
              pearsonMDChiRadius L (mseq p) p) := by
        rw [mul_pow, Real.sq_sqrt hlog0]
        ring
  · exact hupper

/-- The full relative-normal-tail exponent tends to zero under the explicit
moderate-deviation scale hypothesis. -/
theorem tendsto_pearsonMDTailExponent_zero
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    {mseq : ℕ → ℕ} {qseq lambdaSeq : ℕ → ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hq : ∀ᶠ p in atTop, 0 ≤ qseq p)
    (hscale : ∀ᶠ p in atTop,
      qseq p + |lambdaSeq p| ≤
        C * Real.sqrt (Real.log (p : ℝ))) :
    Tendsto (fun p : ℕ ↦
      pearsonMDTailExponent
        L (qseq p) (lambdaSeq p) (mseq p) p)
      atTop (nhds 0) := by
  have hdelta := tendsto_pearsonMDArgumentPerturbation_zero
    (L := L) hC hadm hq hscale
  have hcross :=
    tendsto_pearsonMDArgumentPerturbation_mul_scale_zero
      (L := L) hC hL hadm hq hscale
  have hsum := (hdelta.add hcross).add (hdelta.pow 2)
  have hscaled : Tendsto (fun p : ℕ ↦
      Real.exp (3 / 2 : ℝ) *
        (pearsonMDArgumentPerturbation
              L (qseq p) (lambdaSeq p) (mseq p) p +
            pearsonMDArgumentPerturbation
                L (qseq p) (lambdaSeq p) (mseq p) p *
              (qseq p + |lambdaSeq p|) +
            pearsonMDArgumentPerturbation
                L (qseq p) (lambdaSeq p) (mseq p) p ^ 2))
      atTop (nhds 0) := by
    simpa using hsum.const_mul (Real.exp (3 / 2 : ℝ))
  apply hscaled.congr'
  filter_upwards with p
  unfold pearsonMDTailExponent
  ring

/-- Fully deterministic relative-error profile from the finite comparison:
the normal-tail perturbation `exp(eta)-1` plus the chi-complement rate after
division by the smallest allowed Gaussian tail. -/
def pearsonMDRelativeErrorProfile
    (C L q lambda : ℝ) (m p : ℕ) : ℝ :=
  Real.exp (pearsonMDTailExponent L q lambda m p) - 1 +
    pearsonMDDiscardedChiRate C L p

/-- The logarithmic three-halves rate vanishes uniformly along every
admissible dimension sequence `p <= m`. -/
theorem tendsto_pearsonMDGaussianPerturbationRate_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦
      pearsonMDGaussianPerturbationRate (mseq p) p)
      atTop (nhds 0) := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hbaseReal : Tendsto
      (fun t : ℝ ↦ Real.log t ^ (3 / 2 : ℝ) / t ^ (1 / 2 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hbase : Tendsto
      (fun p : ℕ ↦ Real.log (p : ℝ) ^ (3 / 2 : ℝ) /
        Real.sqrt (p : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, Real.sqrt_eq_rpow] using hbaseReal.comp hpR
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with p hp
    exact div_nonneg
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hp)) _)
      (Real.sqrt_nonneg _)
  · filter_upwards [hadm] with p hp
    have hp1N : 1 ≤ p := (by omega : 1 ≤ 2).trans hp.1
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hp.1)
    have hsqrtp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp0
    have hpm : Real.sqrt (p : ℝ) ≤ Real.sqrt (mseq p : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hp.2)
    exact div_le_div_of_nonneg_left
      (Real.rpow_nonneg (Real.log_nonneg (by
        exact_mod_cast hp1N)) _)
      hsqrtp hpm
  · simpa [pearsonMDGaussianPerturbationRate] using hbase

/-- If `L > C^2/2`, the bad-event contribution divided by the Gaussian tail
vanishes.  This is the sharp deterministic inequality needed for the
one-edge relative approximation; no extra `+2` margin is required here. -/
theorem tendsto_pearsonMDDiscardedChiRate_zero
    {C L : ℝ} (hgap : C ^ 2 / 2 < L) :
    Tendsto (fun p : ℕ ↦ pearsonMDDiscardedChiRate C L p)
      atTop (nhds 0) := by
  let s : ℝ := L - C ^ 2 / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hreal : Tendsto
      (fun t : ℝ ↦ Real.log t ^ (1 / 2 : ℝ) / t ^ s)
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ) hs).tendsto_div_nhds_zero
  have hnat := hreal.comp hpR
  apply hnat.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  unfold pearsonMDDiscardedChiRate
  rw [Real.sqrt_eq_rpow]
  have hexp : C ^ 2 / 2 - L = -s := by dsimp [s]; ring
  rw [hexp, Real.rpow_neg hp0.le]
  rfl

/-- The actual deterministic relative-error profile tends to zero under
`p <= m`, `q >= 0`, `q + |lambda| <= C sqrt(log p)`, `C >= 0`, `L >= 0`,
and the sharp exponent gap `L > C^2/2`.  This theorem still assumes no
probabilistic comparison inequality. -/
theorem tendsto_pearsonMDRelativeErrorProfile_zero
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hgap : C ^ 2 / 2 < L)
    {mseq : ℕ → ℕ} {qseq lambdaSeq : ℕ → ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hq : ∀ᶠ p in atTop, 0 ≤ qseq p)
    (hscale : ∀ᶠ p in atTop,
      qseq p + |lambdaSeq p| ≤
        C * Real.sqrt (Real.log (p : ℝ))) :
    Tendsto (fun p : ℕ ↦
      pearsonMDRelativeErrorProfile
        C L (qseq p) (lambdaSeq p) (mseq p) p)
      atTop (nhds 0) := by
  have heta := tendsto_pearsonMDTailExponent_zero
    (L := L) hC hL hadm hq hscale
  have hexp0 : Tendsto (fun p : ℕ ↦
      Real.exp
        (pearsonMDTailExponent
          L (qseq p) (lambdaSeq p) (mseq p) p))
      atTop (nhds 1) := by
    simpa [Function.comp_def] using
      (Real.continuous_exp.tendsto 0).comp heta
  have hexp : Tendsto (fun p : ℕ ↦
      Real.exp
        (pearsonMDTailExponent
          L (qseq p) (lambdaSeq p) (mseq p) p) - 1)
      atTop (nhds 0) := by
    simpa using hexp0.sub
      (tendsto_const_nhds : Tendsto (fun _p : ℕ ↦ (1 : ℝ))
        atTop (nhds 1))
  have hbad := tendsto_pearsonMDDiscardedChiRate_zero hgap
  simpa [pearsonMDRelativeErrorProfile] using hexp.add hbad

/-- The complete deterministic error profile appearing in Theorem A of the
mathematical audit. -/
def pearsonMDTotalRate (C L : ℝ) (m p : ℕ) : ℝ :=
  pearsonMDGaussianPerturbationRate m p +
    pearsonMDDiscardedChiRate C L p

/-- Both audited error terms vanish simultaneously under the exact all-gap
and exponent-gap hypotheses. -/
theorem tendsto_pearsonMDTotalRate_zero
    {C L : ℝ} {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hgap : C ^ 2 / 2 < L) :
    Tendsto (fun p : ℕ ↦ pearsonMDTotalRate C L (mseq p) p)
      atTop (nhds 0) := by
  simpa [pearsonMDTotalRate] using
    (tendsto_pearsonMDGaussianPerturbationRate_zero hadm).add
      (tendsto_pearsonMDDiscardedChiRate_zero hgap)

end

end LogdetLean.Coherence
