import LogdetLean.Coherence.BetaTailRatio
import LogdetLean.Coherence.BetaEndpointAsymptotic
/-!
# Vanishing overshoots of the coherence Beta tail

For `X ~ Beta(1/2,(m-1)/2)`, this file proves that the upper tail at a
fixed larger multiple `c > 1` of the classical coherence threshold is
negligible relative to the upper tail at the original threshold, uniformly
along every nonsingular sequence `2 ≤ p ≤ m`.

The proof is finite-dimensional up to the last limit.  The Mills-ratio
inequality reduces the probability quotient to endpoint terms, and a local
exponential estimate makes their quotient vanish.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology Real

/-- Exact cancellation in the quotient of two Beta half-tail endpoints. -/
theorem betaHalfTailEndpoint_mul_ratio
    {b t c : ℝ} (hb : 0 < b) (ht : 0 < t) (hc : 0 < c)
    (ht1 : t < 1) (hct1 : c * t < 1) :
    betaHalfTailEndpoint b (c * t) / betaHalfTailEndpoint b t =
      c ^ (-(1 / 2 : ℝ)) * ((1 - c * t) / (1 - t)) ^ b := by
  have hct : 0 < c * t := mul_pos hc ht
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  have h1ct : 0 < 1 - c * t := sub_pos.mpr hct1
  have htpow : t ^ (-(1 / 2 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos ht _).ne'
  have hdenpow : (1 - t) ^ b ≠ 0 :=
    (Real.rpow_pos_of_pos h1t _).ne'
  unfold betaHalfTailEndpoint
  rw [Real.mul_rpow hc.le ht.le]
  rw [Real.div_rpow h1ct.le h1t.le]
  field_simp [hb.ne', htpow, hdenpow]

/-- A finite exponential upper bound for the endpoint quotient.  The loss
`(c-1)/2` is deliberately elementary and is sufficient for every fixed
`c > 1`. -/
theorem betaHalfTailEndpoint_ratio_le_exp
    {b t c : ℝ} (hb : 1 < b) (ht : 0 < t) (hc : 1 < c)
    (hct1 : c * t < 1) :
    betaHalfTailEndpoint b (c * t) /
        (betaHalfTailEndpoint b t / (1 + 1 / (2 * b * t))) ≤
      (1 + 1 / (2 * b * t)) *
        Real.exp (-(b * ((c - 1) / 2) * t)) := by
  let δ : ℝ := (c - 1) / 2
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hc0 : 0 < c := zero_lt_one.trans hc
  have ht1 : t < 1 := by
    have htc : t < c * t := by nlinarith
    exact htc.trans hct1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδt0 : 0 ≤ δ * t := (mul_pos hδ ht).le
  have hratio0 : 0 < (1 - c * t) / (1 - t) :=
    div_pos (sub_pos.mpr hct1) (sub_pos.mpr ht1)
  have hratio_le : (1 - c * t) / (1 - t) ≤ 1 - δ * t := by
    rw [div_le_iff₀ (sub_pos.mpr ht1)]
    have hnonneg : 0 ≤ δ * t * (1 + t) := by positivity
    dsimp [δ] at hnonneg ⊢
    nlinarith
  have honeδ : 0 < 1 - δ * t := lt_of_lt_of_le hratio0 hratio_le
  have honeδexp : 1 - δ * t ≤ Real.exp (-(δ * t)) :=
    Real.one_sub_le_exp_neg (δ * t)
  have hpowratio : ((1 - c * t) / (1 - t)) ^ b ≤
      (1 - δ * t) ^ b :=
    Real.rpow_le_rpow hratio0.le hratio_le hb0.le
  have hpowexp : (1 - δ * t) ^ b ≤
      (Real.exp (-(δ * t))) ^ b :=
    Real.rpow_le_rpow honeδ.le honeδexp hb0.le
  have hcexponent : c ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc.le (by norm_num)
  have hratio_nonneg : 0 ≤ ((1 - c * t) / (1 - t)) ^ b :=
    Real.rpow_nonneg hratio0.le b
  have hendpoint :
      betaHalfTailEndpoint b (c * t) / betaHalfTailEndpoint b t ≤
        Real.exp (-(b * δ * t)) := by
    rw [betaHalfTailEndpoint_mul_ratio hb0 ht hc0 ht1 hct1]
    calc
      c ^ (-(1 / 2 : ℝ)) * ((1 - c * t) / (1 - t)) ^ b ≤
          1 * ((1 - c * t) / (1 - t)) ^ b :=
        mul_le_mul_of_nonneg_right hcexponent hratio_nonneg
      _ ≤ (1 - δ * t) ^ b := by simpa using hpowratio
      _ ≤ (Real.exp (-(δ * t))) ^ b := hpowexp
      _ = Real.exp (-(b * δ * t)) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _)]
        rw [Real.log_exp]
        congr 1
        ring
  have hEt : 0 < betaHalfTailEndpoint b t := by
    unfold betaHalfTailEndpoint
    positivity
  have hcorr : 0 < 1 + 1 / (2 * b * t) := by positivity
  calc
    betaHalfTailEndpoint b (c * t) /
        (betaHalfTailEndpoint b t / (1 + 1 / (2 * b * t))) =
      (1 + 1 / (2 * b * t)) *
        (betaHalfTailEndpoint b (c * t) / betaHalfTailEndpoint b t) := by
      field_simp [hEt.ne', hcorr.ne']
    _ ≤ (1 + 1 / (2 * b * t)) * Real.exp (-(b * δ * t)) :=
      mul_le_mul_of_nonneg_left hendpoint hcorr.le
    _ = (1 + 1 / (2 * b * t)) *
        Real.exp (-(b * ((c - 1) / 2) * t)) := by rfl

/-- Ratio of the two exact Beta upper-tail probabilities. -/
def betaCorrelationOvershootRatio (c : ℝ) (m p : ℕ) (x : ℝ) : ℝ :=
  let b : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let t : ℝ := classicalCoherenceThreshold m p x / (m : ℝ)
  (betaMeasure (1 / 2) b).real (Ioi (c * t)) /
    (betaMeasure (1 / 2) b).real (Ioi t)

/-- Explicit exponential majorant for the overshoot-tail ratio. -/
def betaCorrelationOvershootExpBound
    (c : ℝ) (m p : ℕ) (x : ℝ) : ℝ :=
  let b : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let t : ℝ := classicalCoherenceThreshold m p x / (m : ℝ)
  (1 + 1 / (2 * b * t)) *
    Real.exp (-(b * ((c - 1) / 2) * t))

/-- The explicit overshoot majorant tends to zero for every fixed multiplier
strictly larger than one, uniformly over every admissible gap sequence. -/
theorem tendsto_betaCorrelationOvershootExpBound_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {c : ℝ} (hc : 1 < c) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      betaCorrelationOvershootExpBound c (mseq p) p x)
      atTop (nhds 0) := by
  let δ : ℝ := (c - 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hrate := tendsto_betaCorrelationMillsRate_atTop hadm x
  have hscaled : Tendsto (fun p : ℕ ↦
      (((mseq p - 1 : ℕ) : ℝ) / 2) * δ *
        (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)))
      atTop atTop := by
    have hmul := hrate.const_mul_atTop (by positivity : 0 < δ / 2)
    apply hmul.congr'
    filter_upwards [] with p
    unfold betaCorrelationMillsRate
    ring
  have hexp : Tendsto (fun p : ℕ ↦
      Real.exp (-((((mseq p - 1 : ℕ) : ℝ) / 2) * δ *
        (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)))))
      atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  have hcorr := tendsto_betaCorrelationMillsCorrection_one hadm x
  have hprod := hcorr.mul hexp
  have hprod0 : Tendsto (fun p : ℕ ↦
      (1 + 1 / betaCorrelationMillsRate (mseq p) p x) *
        Real.exp (-((((mseq p - 1 : ℕ) : ℝ) / 2) * δ *
          (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)))))
      atTop (nhds 0) := by simpa using hprod
  apply hprod0.congr'
  filter_upwards [] with p
  unfold betaCorrelationOvershootExpBound betaCorrelationMillsRate
  dsimp only

/-- Exact finite comparison of the Beta overshoot ratio with its elementary
exponential majorant. -/
theorem betaCorrelationOvershootRatio_le_expBound
    {m p : ℕ} {x c : ℝ} (hm : 4 ≤ m)
    (hthreshold : 0 < classicalCoherenceThreshold m p x)
    (hc : 1 < c)
    (hscaledThreshold :
      c * (classicalCoherenceThreshold m p x / (m : ℝ)) < 1) :
    betaCorrelationOvershootRatio c m p x ≤
      betaCorrelationOvershootExpBound c m p x := by
  let b : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let t : ℝ := classicalCoherenceThreshold m p x / (m : ℝ)
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hb : 1 < b := by
    dsimp [b]
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have ht : 0 < t := div_pos hthreshold hm0
  have hts : t ≤ c * t := by nlinarith
  have hmeasure := betaMeasure_half_Ioi_ratio_le_endpoint_ratio
    hb ht hts hscaledThreshold
  have hendpoint := betaHalfTailEndpoint_ratio_le_exp
    hb ht hc hscaledThreshold
  unfold betaCorrelationOvershootRatio betaCorrelationOvershootExpBound
  dsimp only
  exact hmeasure.trans hendpoint

/-- All-gap Beta overshoot theorem.  For every fixed `c > 1`, the upper
tail at `c` times the classical squared-correlation threshold is negligible
relative to the tail at the original threshold. -/
theorem tendsto_betaCorrelationOvershootRatio_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {c : ℝ} (hc : 1 < c) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      betaCorrelationOvershootRatio c (mseq p) p x)
      atTop (nhds 0) := by
  have hbound := tendsto_betaCorrelationOvershootExpBound_zero hadm hc x
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  have hct : Tendsto (fun p : ℕ ↦
      c * (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul ht)
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ by
      unfold betaCorrelationOvershootRatio
      dsimp only
      exact div_nonneg measureReal_nonneg measureReal_nonneg
  · filter_upwards [hadm, eventually_ge_atTop 4,
      ha.eventually (eventually_gt_atTop 0),
      hct.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with p hp hp4 hapos hct1
    have hm4 : 4 ≤ mseq p := hp4.trans hp.2
    have hthreshold : 0 < classicalCoherenceThreshold (mseq p) p x := by
      simpa [classicalCoherenceThreshold] using hapos
    exact betaCorrelationOvershootRatio_le_expBound hm4 hthreshold hc hct1
  · exact hbound

/-- Convenient doubled-threshold specialization used in the conditional
matching prefix proof. -/
theorem tendsto_betaCorrelationDoubleOvershootRatio_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      betaCorrelationOvershootRatio 2 (mseq p) p x)
      atTop (nhds 0) :=
  tendsto_betaCorrelationOvershootRatio_zero hadm (by norm_num) x

end

end LogdetLean.Coherence
