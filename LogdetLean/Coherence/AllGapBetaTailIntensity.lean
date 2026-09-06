import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import LogdetLean.Coherence.BetaHalfNormalization
import LogdetLean.Coherence.BetaTailTarget
/-!
# Reduction of the all-gap Beta-tail intensity to one endpoint asymptotic

This module proves all measure-theoretic and Mills-ratio reductions needed
for `AllGapBetaTailIntensityTarget`.  The only remaining named bridge is the
deterministic endpoint asymptotic `AllGapBetaEndpointIntensityTarget`; it no
longer contains a probability measure or an integral.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology Real

/-- Deterministic endpoint approximation to one correlation-tail
probability. -/
def betaCorrelationEndpointProbability (m p : ℕ) (x : ℝ) : ℝ :=
  betaHalfTailEndpoint (((m - 1 : ℕ) : ℝ) / 2)
      (classicalCoherenceThreshold m p x / (m : ℝ)) /
    beta (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)

/-- The sole deterministic analytic bridge left after the exact Beta-density
identity, the endpoint Mills bound, and the normalization-constant theorem.
It is strictly smaller than `AllGapBetaTailIntensityTarget`: the probability
measure and tail integral have disappeared. -/
def AllGapBetaEndpointIntensityTarget : Prop :=
  ∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      ∀ x : ℝ,
        Tendsto
          (fun p ↦ ((p.choose 2 : ℕ) : ℝ) *
            betaCorrelationEndpointProbability (mseq p) p x)
          atTop (nhds (classicalCoherenceIntensity x))

/-- The classical threshold divided by `log p` tends to four. -/
theorem tendsto_classicalCoherenceThreshold_div_log (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      classicalCoherenceThreshold 0 p x / Real.log (p : ℝ))
      atTop (nhds 4) := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpR
  have hloglog : Tendsto (fun p : ℕ ↦
      Real.log (Real.log (p : ℝ)) / Real.log (p : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hx : Tendsto (fun p : ℕ ↦ x / Real.log (p : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop x
  have hlim : Tendsto (fun p : ℕ ↦
      4 - Real.log (Real.log (p : ℝ)) / Real.log (p : ℝ) +
        x / Real.log (p : ℝ)) atTop (nhds 4) := by
    simpa using
      (tendsto_const_nhds.sub hloglog).add hx
  apply hlim.congr'
  filter_upwards [hlog.eventually (eventually_ne_atTop 0)] with p hp
  unfold classicalCoherenceThreshold
  field_simp [hp]

/-- The classical threshold diverges to positive infinity. -/
theorem tendsto_classicalCoherenceThreshold_atTop (x : ℝ) :
    Tendsto (fun p : ℕ ↦ classicalCoherenceThreshold 0 p x)
      atTop atTop := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpR
  have hratio := tendsto_classicalCoherenceThreshold_div_log x
  have hprod := hlog.atTop_mul_pos (by norm_num : (0 : ℝ) < 4) hratio
  apply hprod.congr'
  filter_upwards [hlog.eventually (eventually_ne_atTop 0)] with p hp
  field_simp [hp]

/-- The classical threshold is negligible compared with `p`. -/
theorem tendsto_classicalCoherenceThreshold_div_nat (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      classicalCoherenceThreshold 0 p x / (p : ℝ))
      atTop (nhds 0) := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpR
  have hlogdiv : Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) / (p : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hpR
  have hprod := (tendsto_classicalCoherenceThreshold_div_log x).mul hlogdiv
  have hprod0 : Tendsto (fun p : ℕ ↦
      classicalCoherenceThreshold 0 p x / Real.log (p : ℝ) *
        (Real.log (p : ℝ) / (p : ℝ))) atTop (nhds 0) := by
    simpa using hprod
  apply hprod0.congr'
  filter_upwards [hlog.eventually (eventually_ne_atTop 0),
    hpR.eventually (eventually_ne_atTop 0)] with p hlogp hp
  field_simp [hlogp, hp]

/-- Uniformly over every admissible sequence `m >= p`, the squared-
correlation threshold `a_p/m` tends to zero. -/
theorem tendsto_classicalCoherenceThreshold_div_mseq_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ))
      atTop (nhds 0) := by
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have hap := tendsto_classicalCoherenceThreshold_div_nat x
  apply squeeze_zero'
  · filter_upwards [hadm,
      ha.eventually (eventually_ge_atTop 0)] with p hp hapos
    exact div_nonneg (by simpa [classicalCoherenceThreshold] using hapos)
      (Nat.cast_nonneg _)
  · filter_upwards [hadm,
      ha.eventually (eventually_ge_atTop 0)] with p hp hapos
    have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) hp.1
    have hmN : 0 < mseq p := hpN.trans_le hp.2
    have hpa : 0 ≤ classicalCoherenceThreshold (mseq p) p x := by
      simpa [classicalCoherenceThreshold] using hapos
    have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpN
    have hpmR : (p : ℝ) ≤ (mseq p : ℝ) := Nat.cast_le.mpr hp.2
    exact div_le_div_of_nonneg_left hpa hpR hpmR
  · simpa [classicalCoherenceThreshold] using hap

/-- The effective Mills-rate denominator `2 b t` for
`b=(m-1)/2` and `t=a_p/m`. -/
def betaCorrelationMillsRate (m p : ℕ) (x : ℝ) : ℝ :=
  2 * (((m - 1 : ℕ) : ℝ) / 2) *
    (classicalCoherenceThreshold m p x / (m : ℝ))

/-- Admissibility forces the dimension sequence to infinity. -/
theorem tendsto_mseq_atTop_of_admissible
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto mseq atTop atTop := by
  exact Filter.tendsto_atTop_mono' atTop
    (hadm.mono fun _ hp ↦ hp.2) tendsto_id

/-- The elementary factor `(m-1)/m` tends to one along every admissible
dimension sequence. -/
theorem tendsto_pred_mseq_div_mseq_one
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦
      (((mseq p - 1 : ℕ) : ℝ) / (mseq p : ℝ)))
      atTop (nhds 1) := by
  have hmN := tendsto_mseq_atTop_of_admissible hadm
  have hmR : Tendsto (fun p : ℕ ↦ (mseq p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmN
  have hinv : Tendsto (fun p : ℕ ↦ 1 / (mseq p : ℝ))
      atTop (nhds 0) := hmR.const_div_atTop 1
  have hlim : Tendsto (fun p : ℕ ↦ 1 - 1 / (mseq p : ℝ))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds :
      Tendsto (fun _p : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub hinv
  apply hlim.congr'
  filter_upwards [hadm] with p hp
  have hp1 : 1 ≤ p := (by omega : 1 ≤ 2).trans hp.1
  have hm1 : 1 ≤ mseq p := hp1.trans hp.2
  have hm0 : (mseq p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hm1)
  rw [Nat.cast_sub hm1, Nat.cast_one]
  field_simp [hm0]

/-- The Mills rate diverges uniformly over all admissible gaps. -/
theorem tendsto_betaCorrelationMillsRate_atTop
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦ betaCorrelationMillsRate (mseq p) p x)
      atTop atTop := by
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have hratio := tendsto_pred_mseq_div_mseq_one hadm
  have hprod := ha.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hratio
  apply hprod.congr'
  filter_upwards [hadm] with p hp
  have hp1 : 1 ≤ p := (by omega : 1 ≤ 2).trans hp.1
  have hm1 : 1 ≤ mseq p := hp1.trans hp.2
  have hm0N : 0 < mseq p := hm1
  have hm0 : (mseq p : ℝ) ≠ 0 := by exact_mod_cast hm0N.ne'
  unfold betaCorrelationMillsRate classicalCoherenceThreshold
  rw [Nat.cast_sub hm1, Nat.cast_one]
  field_simp [hm0]

/-- Consequently the multiplicative Mills correction tends to one. -/
theorem tendsto_betaCorrelationMillsCorrection_one
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      1 + 1 / betaCorrelationMillsRate (mseq p) p x)
      atTop (nhds 1) := by
  have hzero :=
    (tendsto_betaCorrelationMillsRate_atTop hadm x).const_div_atTop 1
  simpa using (tendsto_const_nhds :
    Tendsto (fun _p : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).add hzero

/-- Exact finite-`m,p` Mills sandwich for the normalized Beta tail. -/
theorem betaCorrelationTail_mills_bounds
    {m p : ℕ} {x : ℝ} (hm : 4 ≤ m)
    (hthreshold0 : 0 < classicalCoherenceThreshold m p x)
    (hthresholdm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    betaCorrelationEndpointProbability m p x /
        (1 + 1 / betaCorrelationMillsRate m p x) ≤
          betaCorrelationTailProbability m p x ∧
      betaCorrelationTailProbability m p x ≤
        betaCorrelationEndpointProbability m p x := by
  let b : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let t : ℝ := classicalCoherenceThreshold m p x / (m : ℝ)
  have hm0N : 0 < m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0N
  have hb : 1 < b := by
    dsimp [b]
    rw [Nat.cast_sub hm1, Nat.cast_one]
    have hmR4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have ht0 : 0 < t := div_pos hthreshold0 hmR
  have ht1 : t < 1 := (div_lt_one hmR).2 hthresholdm
  have hB : 0 < beta (1 / 2) b :=
    beta_pos (by norm_num) (zero_lt_one.trans hb)
  have htail : betaCorrelationTailProbability m p x =
      betaHalfTailIntegral b t / beta (1 / 2) b := by
    unfold betaCorrelationTailProbability
    change (betaMeasure (1 / 2) b).real (Ioi t) = _
    exact betaMeasure_half_Ioi_real_eq_tailIntegral_div hb ht0 ht1
  have hmills := betaHalfTailEndpoint_mills_bounds hb ht0 ht1
  have hrate : betaCorrelationMillsRate m p x = 2 * b * t := by
    rfl
  have hendpoint : betaCorrelationEndpointProbability m p x =
      betaHalfTailEndpoint b t / beta (1 / 2) b := by
    rfl
  rw [htail, hendpoint, hrate]
  constructor
  · calc
      (betaHalfTailEndpoint b t / beta (1 / 2) b) /
          (1 + 1 / (2 * b * t)) =
          (betaHalfTailEndpoint b t / (1 + 1 / (2 * b * t))) /
            beta (1 / 2) b := by ring
      _ ≤ betaHalfTailIntegral b t / beta (1 / 2) b :=
        (div_le_div_iff_of_pos_right hB).2 hmills.1
  · exact (div_le_div_iff_of_pos_right hB).2 hmills.2

/-- The deterministic endpoint target implies the original single-edge
Beta-tail intensity target.  Thus the named endpoint bridge is sufficient,
with no additional probability-theoretic assumption. -/
theorem allGapBetaTailIntensity_of_endpoint
    (hendpointTarget : AllGapBetaEndpointIntensityTarget) :
    AllGapBetaTailIntensityTarget := by
  unfold AllGapBetaTailIntensityTarget
  intro mseq hadm x
  have hendpoint := hendpointTarget mseq hadm x
  have hcorrection := tendsto_betaCorrelationMillsCorrection_one hadm x
  have hlowerRaw := hendpoint.div hcorrection (by norm_num : (1 : ℝ) ≠ 0)
  have hlower : Tendsto (fun p : ℕ ↦
      ((p.choose 2 : ℕ) : ℝ) *
        (betaCorrelationEndpointProbability (mseq p) p x /
          (1 + 1 / betaCorrelationMillsRate (mseq p) p x)))
      atTop (nhds (classicalCoherenceIntensity x)) := by
    have heq :
        ((fun p : ℕ ↦ ((p.choose 2 : ℕ) : ℝ) *
            betaCorrelationEndpointProbability (mseq p) p x) /
          (fun p : ℕ ↦ 1 + 1 / betaCorrelationMillsRate (mseq p) p x))
          =ᶠ[atTop]
        (fun p : ℕ ↦ ((p.choose 2 : ℕ) : ℝ) *
          (betaCorrelationEndpointProbability (mseq p) p x /
            (1 + 1 / betaCorrelationMillsRate (mseq p) p x))) := by
      filter_upwards [] with p
      change (((p.choose 2 : ℕ) : ℝ) *
          betaCorrelationEndpointProbability (mseq p) p x) /
            (1 + 1 / betaCorrelationMillsRate (mseq p) p x) = _
      ring
    simpa using hlowerRaw.congr' heq
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  have hbounds : ∀ᶠ p : ℕ in atTop,
      ((p.choose 2 : ℕ) : ℝ) *
          (betaCorrelationEndpointProbability (mseq p) p x /
            (1 + 1 / betaCorrelationMillsRate (mseq p) p x)) ≤
        ((p.choose 2 : ℕ) : ℝ) *
          betaCorrelationTailProbability (mseq p) p x ∧
      ((p.choose 2 : ℕ) : ℝ) *
          betaCorrelationTailProbability (mseq p) p x ≤
        ((p.choose 2 : ℕ) : ℝ) *
          betaCorrelationEndpointProbability (mseq p) p x := by
    filter_upwards [hadm, eventually_ge_atTop 4,
      ha.eventually (eventually_gt_atTop 0),
      ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with p hp hp4 hapos ht1
    have hm4 : 4 ≤ mseq p := hp4.trans hp.2
    have hthreshold0 : 0 < classicalCoherenceThreshold (mseq p) p x := by
      simpa [classicalCoherenceThreshold] using hapos
    have hmR : (0 : ℝ) < (mseq p : ℝ) := by
      exact_mod_cast (by omega : 0 < mseq p)
    have hthresholdm : classicalCoherenceThreshold (mseq p) p x <
        (mseq p : ℝ) := (div_lt_one hmR).1 ht1
    have hmills := betaCorrelationTail_mills_bounds hm4 hthreshold0 hthresholdm
    exact ⟨mul_le_mul_of_nonneg_left hmills.1 (Nat.cast_nonneg _),
      mul_le_mul_of_nonneg_left hmills.2 (Nat.cast_nonneg _)⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hendpoint (hbounds.mono fun _ h ↦ h.1)
      (hbounds.mono fun _ h ↦ h.2)

end

end LogdetLean.Coherence
