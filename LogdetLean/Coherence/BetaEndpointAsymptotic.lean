import LogdetLean.Coherence.AllGapBetaTailIntensity
/-!
# Deterministic endpoint asymptotics for the all-gap Beta tail

This file attacks the last deterministic bridge isolated in
`AllGapBetaTailIntensity`.  It first factors the endpoint exactly into the
already verified Beta normalization and an elementary power core.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter ProbabilityTheory Real Set
open scoped Topology Real

/-- Elementary power core of the Beta endpoint approximation. -/
def betaCorrelationPowerCore (m p : ℕ) (x : ℝ) : ℝ :=
  classicalCoherenceThreshold m p x ^ (-(1 / 2 : ℝ)) *
    (1 - classicalCoherenceThreshold m p x / (m : ℝ)) ^
      (((m - 1 : ℕ) : ℝ) / 2)

/-- Scaling a positive argument inside the negative half power. -/
theorem div_rpow_neg_half_eq_sqrt_mul_rpow_neg_half
    {a M : ℝ} (ha : 0 < a) (hM : 0 < M) :
    (a / M) ^ (-(1 / 2 : ℝ)) =
      √M * a ^ (-(1 / 2 : ℝ)) := by
  have hsqrta : √a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsqrtM : √M ≠ 0 := (Real.sqrt_pos.2 hM).ne'
  rw [Real.div_rpow ha.le hM.le]
  rw [show -(1 / 2 : ℝ) = -(1 / 2 : ℝ) by rfl,
    Real.rpow_neg ha.le, Real.rpow_neg hM.le,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  field_simp [hsqrta, hsqrtM]

/-- Exact factorization of the endpoint approximation into its normalization
constant and elementary power core. -/
theorem betaCorrelationEndpointProbability_eq_normalization_mul_core
    {m p : ℕ} {x : ℝ} (hm : 2 ≤ m)
    (hthreshold : 0 < classicalCoherenceThreshold m p x) :
    betaCorrelationEndpointProbability m p x =
      betaHalfEndpointNormalization m * betaCorrelationPowerCore m p x := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  have hbcast : (((m - 1 : ℕ) : ℝ) / 2) =
      ((m : ℝ) - 1) / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hbpos : 0 < ((m : ℝ) - 1) / 2 := by
    have hmR2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hBpos : 0 < beta (1 / 2) (((m : ℝ) - 1) / 2) :=
    beta_pos (by norm_num) hbpos
  unfold betaCorrelationEndpointProbability betaHalfTailEndpoint
    betaHalfEndpointNormalization betaCorrelationPowerCore
  rw [hbcast,
    div_rpow_neg_half_eq_sqrt_mul_rpow_neg_half hthreshold hmR]
  field_simp [hbpos.ne', hBpos.ne']

/-- Elementary edge-count asymptotic. -/
theorem tendsto_choose_two_div_sq :
    Tendsto (fun p : ℕ ↦ ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2)
      atTop (nhds (1 / 2 : ℝ)) := by
  have hinv : Tendsto (fun p : ℕ ↦ 1 / (p : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlim : Tendsto (fun p : ℕ ↦ (1 - 1 / (p : ℝ)) / 2)
      atTop (nhds (1 / 2 : ℝ)) := by
    simpa using ((tendsto_const_nhds :
      Tendsto (fun _p : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub hinv).div_const 2
  apply hlim.congr'
  filter_upwards [eventually_ne_atTop 0] with p hp
  rw [Nat.cast_choose_two]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp [hpR]

/-- The square-root threshold factor has limit one half. -/
theorem tendsto_sqrt_log_div_classicalCoherenceThreshold (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      √(Real.log (p : ℝ) / classicalCoherenceThreshold 0 p x))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hratio := tendsto_classicalCoherenceThreshold_div_log x
  have hinv := hratio.inv₀ (by norm_num : (4 : ℝ) ≠ 0)
  have hinv' : Tendsto (fun p : ℕ ↦
      (classicalCoherenceThreshold 0 p x / Real.log (p : ℝ))⁻¹)
      atTop (nhds (1 / 4 : ℝ)) := by
    norm_num at hinv ⊢
    exact hinv
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpR
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have hquot : Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) / classicalCoherenceThreshold 0 p x)
      atTop (nhds (1 / 4 : ℝ)) := by
    apply hinv'.congr'
    filter_upwards [hlog.eventually (eventually_ne_atTop 0),
      ha.eventually (eventually_ne_atTop 0)] with p hlogp hap
    field_simp [hlogp, hap]
  have hsqrt := hquot.sqrt
  convert hsqrt using 1
  norm_num

/-- Exact cancellation of the classical extreme-value centering inside the
exponential. -/
theorem exp_neg_classicalCoherenceThreshold_half
    {m p : ℕ} {x : ℝ} (hp : 1 < p) :
    Real.exp (-classicalCoherenceThreshold m p x / 2) =
      (1 / (p : ℝ) ^ 2) * √(Real.log (p : ℝ)) * Real.exp (-x / 2) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp)
  have hfirst : Real.exp (-2 * Real.log (p : ℝ)) = 1 / (p : ℝ) ^ 2 := by
    rw [show -2 * Real.log (p : ℝ) = -(2 * Real.log (p : ℝ)) by ring,
      Real.exp_neg,
      show (2 : ℝ) * Real.log (p : ℝ) =
        Real.log (p : ℝ) + Real.log (p : ℝ) by ring,
      Real.exp_add, Real.exp_log hpR]
    ring
  have hsecond : Real.exp (Real.log (Real.log (p : ℝ)) / 2) =
      √(Real.log (p : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlog]
    congr 1
    ring
  unfold classicalCoherenceThreshold
  rw [show -(4 * Real.log (p : ℝ) - Real.log (Real.log (p : ℝ)) + x) / 2 =
      -2 * Real.log (p : ℝ) +
        Real.log (Real.log (p : ℝ)) / 2 + (-x / 2) by ring,
    Real.exp_add, Real.exp_add, hfirst, hsecond]

/-- The square of the threshold is negligible compared with `p`. -/
theorem tendsto_classicalCoherenceThreshold_sq_div_nat (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      classicalCoherenceThreshold 0 p x ^ 2 / (p : ℝ))
      atTop (nhds 0) := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpR
  have hlogSq : Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) ^ 2 / (p : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp hpR
  have hratioSq := (tendsto_classicalCoherenceThreshold_div_log x).pow 2
  have hprod := hratioSq.mul hlogSq
  have hprod0 : Tendsto (fun p : ℕ ↦
      (classicalCoherenceThreshold 0 p x / Real.log (p : ℝ)) ^ 2 *
        (Real.log (p : ℝ) ^ 2 / (p : ℝ))) atTop (nhds 0) := by
    simpa using hprod
  apply hprod0.congr'
  filter_upwards [hlog.eventually (eventually_ne_atTop 0)] with p hlogp
  field_simp [hlogp]

/-- Uniformly for `m >= p`, the square of the threshold is negligible
compared with `m`. -/
theorem tendsto_classicalCoherenceThreshold_sq_div_mseq_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      classicalCoherenceThreshold (mseq p) p x ^ 2 / (mseq p : ℝ))
      atTop (nhds 0) := by
  have hupper := tendsto_classicalCoherenceThreshold_sq_div_nat x
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hadm] with p hp
    have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) hp.1
    have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpN
    have hpmR : (p : ℝ) ≤ (mseq p : ℝ) := Nat.cast_le.mpr hp.2
    exact div_le_div_of_nonneg_left (sq_nonneg _) hpR hpmR
  · simpa [classicalCoherenceThreshold] using hupper

/-- Logarithmic error comparing the Beta power with its exponential
approximation. -/
def betaCorrelationLogPowerError (m p : ℕ) (x : ℝ) : ℝ :=
  (((m - 1 : ℕ) : ℝ) / 2) *
      Real.log (1 - classicalCoherenceThreshold m p x / (m : ℝ)) +
    classicalCoherenceThreshold m p x / 2

/-- A convenient deterministic upper bound for the logarithmic error. -/
def betaCorrelationLogPowerErrorBound (m p : ℕ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (classicalCoherenceThreshold m p x ^ 2 / (m : ℝ)) /
        (1 - classicalCoherenceThreshold m p x / (m : ℝ)) +
    (classicalCoherenceThreshold m p x / (m : ℝ)) / 2

private theorem abs_log_one_sub_linear_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    |y + Real.log (1 - y)| ≤ y ^ 2 / (1 - y) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := y) (by simpa [abs_of_nonneg hy0] using hy1) 1
  simpa [abs_of_nonneg hy0] using h

/-- Finite logarithmic error bound. -/
theorem abs_betaCorrelationLogPowerError_le
    {m p : ℕ} {x : ℝ} (hm : 2 ≤ m)
    (hthreshold0 : 0 ≤ classicalCoherenceThreshold m p x)
    (hthresholdm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    |betaCorrelationLogPowerError m p x| ≤
      betaCorrelationLogPowerErrorBound m p x := by
  let A : ℝ := classicalCoherenceThreshold m p x
  let M : ℝ := (m : ℝ)
  let y : ℝ := A / M
  let b : ℝ := (M - 1) / 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hM2 : (2 : ℝ) ≤ M := by dsimp [M]; exact_mod_cast hm
  have hy0 : 0 ≤ y := div_nonneg hthreshold0 hM.le
  have hy1 : y < 1 := (div_lt_one hM).2 hthresholdm
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hbM : b ≤ M / 2 := by dsimp [b]; linarith
  have hrem := abs_log_one_sub_linear_le hy0 hy1
  have hden : 0 < 1 - y := sub_pos.mpr hy1
  have hrem0 : 0 ≤ y ^ 2 / (1 - y) := div_nonneg (sq_nonneg _) hden.le
  have htri : |b * (y + Real.log (1 - y)) + y / 2| ≤
      b * |y + Real.log (1 - y)| + y / 2 := by
    calc
      |b * (y + Real.log (1 - y)) + y / 2| ≤
          |b * (y + Real.log (1 - y))| + |y / 2| := abs_add_le _ _
      _ = b * |y + Real.log (1 - y)| + y / 2 := by
        rw [abs_mul, abs_of_nonneg hb0, abs_of_nonneg (div_nonneg hy0 (by norm_num))]
  have hbound : |b * (y + Real.log (1 - y)) + y / 2| ≤
      (M / 2) * (y ^ 2 / (1 - y)) + y / 2 := by
    calc
      |b * (y + Real.log (1 - y)) + y / 2| ≤
          b * |y + Real.log (1 - y)| + y / 2 := htri
      _ ≤ b * (y ^ 2 / (1 - y)) + y / 2 := by
        gcongr
      _ ≤ (M / 2) * (y ^ 2 / (1 - y)) + y / 2 := by
        gcongr
  have hm1 : 1 ≤ m := by omega
  have hbcast : (((m - 1 : ℕ) : ℝ) / 2) = b := by
    dsimp [b, M]
    rw [Nat.cast_sub hm1, Nat.cast_one]
  have hAeq : A = M * y := by
    dsimp [y]
    field_simp [hM.ne']
  unfold betaCorrelationLogPowerError betaCorrelationLogPowerErrorBound
  change |(((m - 1 : ℕ) : ℝ) / 2) * Real.log (1 - A / M) + A / 2| ≤
    (1 / 2 : ℝ) * (A ^ 2 / M) / (1 - A / M) + (A / M) / 2
  rw [hbcast, hAeq]
  rw [show M * y / M = y by field_simp [hM.ne']]
  calc
    |b * Real.log (1 - y) + M * y / 2| =
        |b * (y + Real.log (1 - y)) + y / 2| := by
      congr 1
      dsimp [b]
      ring
    _ ≤ (M / 2) * (y ^ 2 / (1 - y)) + y / 2 := hbound
    _ = (1 / 2 : ℝ) * ((M * y) ^ 2 / M) / (1 - y) + y / 2 := by
      field_simp [hM.ne', hden.ne']

/-- The explicit logarithmic-error bound tends to zero uniformly in every
admissible gap regime. -/
theorem tendsto_betaCorrelationLogPowerErrorBound_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦ betaCorrelationLogPowerErrorBound (mseq p) p x)
      atTop (nhds 0) := by
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  have hsq := tendsto_classicalCoherenceThreshold_sq_div_mseq_zero hadm x
  have hden : Tendsto (fun p : ℕ ↦
      (1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ))⁻¹)
      atTop (nhds 1) := by
    have hsub := (tendsto_const_nhds :
      Tendsto (fun _p : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub ht
    simpa using hsub.inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hfirst := ((tendsto_const_nhds :
      Tendsto (fun _p : ℕ ↦ (1 / 2 : ℝ)) atTop (nhds (1 / 2))).mul hsq).mul hden
  have hsecond := ht.div_const 2
  have hsum := hfirst.add hsecond
  simpa [betaCorrelationLogPowerErrorBound, div_eq_mul_inv, mul_assoc] using hsum

/-- The logarithmic power error itself tends to zero. -/
theorem tendsto_betaCorrelationLogPowerError_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦ betaCorrelationLogPowerError (mseq p) p x)
      atTop (nhds 0) := by
  have hbound := tendsto_betaCorrelationLogPowerErrorBound_zero hadm x
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  have habs : Tendsto (fun p : ℕ ↦
      |betaCorrelationLogPowerError (mseq p) p x|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · filter_upwards [hadm,
        ha.eventually (eventually_ge_atTop 0),
        ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
        with p hp hapos ht1
      have hm2 : 2 ≤ mseq p := hp.1.trans hp.2
      have hmR : (0 : ℝ) < (mseq p : ℝ) := by
        exact_mod_cast (by omega : 0 < mseq p)
      have hthreshold0 : 0 ≤ classicalCoherenceThreshold (mseq p) p x := by
        simpa [classicalCoherenceThreshold] using hapos
      have hthresholdm : classicalCoherenceThreshold (mseq p) p x <
          (mseq p : ℝ) := (div_lt_one hmR).1 ht1
      exact abs_betaCorrelationLogPowerError_le hm2 hthreshold0 hthresholdm
    · exact hbound
  rw [tendsto_zero_iff_abs_tendsto_zero]
  simpa [Function.comp_def] using habs

/-- Ratio between the exact Beta power and its exponential approximation. -/
def betaCorrelationPowerExpRatio (m p : ℕ) (x : ℝ) : ℝ :=
  (1 - classicalCoherenceThreshold m p x / (m : ℝ)) ^
      (((m - 1 : ℕ) : ℝ) / 2) /
    Real.exp (-classicalCoherenceThreshold m p x / 2)

/-- The Beta power differs multiplicatively from `exp(-a_p/2)` by a factor
tending to one, uniformly for every admissible gap sequence. -/
theorem tendsto_beta_power_div_exp_one
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦ betaCorrelationPowerExpRatio (mseq p) p x)
      atTop (nhds 1) := by
  have herr := tendsto_betaCorrelationLogPowerError_zero hadm x
  have hexp : Tendsto (fun p : ℕ ↦
      Real.exp (betaCorrelationLogPowerError (mseq p) p x))
      atTop (nhds 1) := by
    have hreal := (Real.continuous_exp.tendsto 0).comp herr
    change Tendsto (fun p : ℕ ↦
      Real.exp (betaCorrelationLogPowerError (mseq p) p x))
        atTop (nhds (Real.exp 0)) at hreal
    simpa using hreal
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  apply hexp.congr'
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with p ht1
  have hbase : 0 < 1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ) :=
    sub_pos.mpr ht1
  unfold betaCorrelationPowerExpRatio
  rw [Real.rpow_def_of_pos hbase, ← Real.exp_sub]
  unfold betaCorrelationLogPowerError
  congr 1
  ring

/-- The remaining inverse-square-root factor is exactly a square root of a
ratio. -/
theorem rpow_neg_half_mul_sqrt_eq_sqrt_div
    {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    a ^ (-(1 / 2 : ℝ)) * √L = √(L / a) := by
  have hsqrta : √a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  rw [show -(1 / 2 : ℝ) = -(1 / 2 : ℝ) by rfl,
    Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow,
    Real.sqrt_div hL.le a]
  field_simp [hsqrta]

/-- Algebraic form of the limiting intensity constant. -/
theorem classicalCoherenceIntensity_eq_endpoint_product (x : ℝ) :
    classicalCoherenceIntensity x =
      (1 / 2 : ℝ) * (√2 / √Real.pi) * (1 / 2) *
        Real.exp (-x / 2) * 1 := by
  have hsqrt8pi : √(8 * Real.pi) = 2 * √2 * √Real.pi := by
    calc
      √(8 * Real.pi) = √(4 * (2 * Real.pi)) := by
        congr 1
        ring
      _ = √4 * √(2 * Real.pi) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (2 * Real.pi)
      _ = 2 * (√2 * √Real.pi) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi]
        norm_num
      _ = 2 * √2 * √Real.pi := by ring
  have hsqrt2 : √2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsqrtpi : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold classicalCoherenceIntensity
  rw [hsqrt8pi]
  field_simp [hsqrt2, hsqrtpi]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Product of the five deterministic factors whose limits give the endpoint
intensity. -/
def betaEndpointLimitFactor (m p : ℕ) (x : ℝ) : ℝ :=
  (((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2) *
    betaHalfEndpointNormalization m *
    √(Real.log (p : ℝ) / classicalCoherenceThreshold m p x) *
    Real.exp (-x / 2) * betaCorrelationPowerExpRatio m p x

/-- Limit of the factored deterministic endpoint expression. -/
theorem tendsto_betaEndpointLimitFactor
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦ betaEndpointLimitFactor (mseq p) p x)
      atTop (nhds (classicalCoherenceIntensity x)) := by
  have hm := tendsto_mseq_atTop_of_admissible hadm
  have hchoose := tendsto_choose_two_div_sq
  have hnorm := tendsto_betaHalfEndpointNormalization.comp hm
  have hsqrt0 := tendsto_sqrt_log_div_classicalCoherenceThreshold x
  have hsqrt : Tendsto (fun p : ℕ ↦
      √(Real.log (p : ℝ) /
        classicalCoherenceThreshold (mseq p) p x))
      atTop (nhds (1 / 2 : ℝ)) := by
    simpa [classicalCoherenceThreshold] using hsqrt0
  have hconst : Tendsto (fun _p : ℕ ↦ Real.exp (-x / 2))
      atTop (nhds (Real.exp (-x / 2))) := tendsto_const_nhds
  have hratio := tendsto_beta_power_div_exp_one hadm x
  have hprod := (((hchoose.mul hnorm).mul hsqrt).mul hconst).mul hratio
  have htarget : (1 / 2 : ℝ) * (√2 / √Real.pi) * (1 / 2) *
      Real.exp (-x / 2) * 1 = classicalCoherenceIntensity x :=
    (classicalCoherenceIntensity_eq_endpoint_product x).symm
  rw [← htarget]
  simpa [betaEndpointLimitFactor, mul_assoc] using hprod

/-- Eventually the factored expression is exactly the edge count times the
Beta endpoint approximation. -/
theorem eventually_betaEndpointLimitFactor_eq_endpoint
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    ∀ᶠ p : ℕ in atTop,
      betaEndpointLimitFactor (mseq p) p x =
        ((p.choose 2 : ℕ) : ℝ) *
          betaCorrelationEndpointProbability (mseq p) p x := by
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hpR
  filter_upwards [hadm, eventually_ge_atTop 2,
    ha.eventually (eventually_gt_atTop 0),
    hlog.eventually (eventually_gt_atTop 0)] with p hp hp2 hapos hlogpos
  have hm2 : 2 ≤ mseq p := hp2.trans hp.2
  have hthreshold : 0 < classicalCoherenceThreshold (mseq p) p x := by
    simpa [classicalCoherenceThreshold] using hapos
  have hendpoint :=
    betaCorrelationEndpointProbability_eq_normalization_mul_core hm2 hthreshold
  have hexact := exp_neg_classicalCoherenceThreshold_half
    (m := mseq p) (x := x) (by omega : 1 < p)
  have hsqrt := rpow_neg_half_mul_sqrt_eq_sqrt_div hthreshold hlogpos
  have hsqrt' :
      √(Real.log (p : ℝ) *
          (classicalCoherenceThreshold (mseq p) p x)⁻¹) =
        classicalCoherenceThreshold (mseq p) p x ^ (-(1 / 2 : ℝ)) *
          √(Real.log (p : ℝ)) := by
    simpa [div_eq_mul_inv] using hsqrt.symm
  have hpower :
      (1 - classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) ^
          (((mseq p - 1 : ℕ) : ℝ) / 2) =
        betaCorrelationPowerExpRatio (mseq p) p x *
          Real.exp (-classicalCoherenceThreshold (mseq p) p x / 2) := by
    unfold betaCorrelationPowerExpRatio
    field_simp [Real.exp_ne_zero]
  rw [hendpoint]
  unfold betaCorrelationPowerCore betaEndpointLimitFactor
  rw [hpower, hexact]
  ring_nf
  rw [hsqrt']
  ring_nf

/-- The formerly isolated deterministic endpoint target is fully proved. -/
theorem allGapBetaEndpointIntensity : AllGapBetaEndpointIntensityTarget := by
  intro mseq hadm x
  have hfactor := tendsto_betaEndpointLimitFactor hadm x
  exact hfactor.congr' (eventually_betaEndpointLimitFactor_eq_endpoint hadm x)

/-- Unconditional all-gap one-edge Beta-tail intensity theorem. -/
theorem allGapBetaTailIntensity : AllGapBetaTailIntensityTarget :=
  allGapBetaTailIntensity_of_endpoint allGapBetaEndpointIntensity

end

end LogdetLean.Coherence
