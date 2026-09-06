import LogdetLean.Coherence.BetaEndpointAsymptotic
import LogdetLean.Coherence.QuantitativeJointBerryEsseen
/-!
# Finite Beta intensity and transfer to the fixed coherence law

This module separates two logically different parts of a quantitative
coherence approximation.

* `finiteCoherenceIntensity m p x` is the exact finite-`(m,p)` expected
  number of classical-threshold exceedances.
* `classicalCoherenceIntensity x` is the fixed limiting intensity.

The analytic input to a Berry--Esseen theorem is a finite bound on the
difference of these two intensities.  The deterministic result below proves
that this bound transfers, with constant exactly one, to their exponential
void approximations.  No asymptotic or probabilistic assumption is used in
that transfer.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology Real

/-- The explicit scale suggested by the first finite Beta-tail expansion.
It is totalized in the usual Lean sense for small `m,p`; all quantitative
uses impose `3 ≤ p` and `p ≤ m`. -/
def betaIntensityErrorEnvelope (m p : ℕ) : ℝ :=
  (1 + Real.log (Real.log (p : ℝ))) / Real.log (p : ℝ) +
    Real.log (p : ℝ) ^ 2 / (m : ℝ) + 1 / (p : ℝ)

/-- Endpoint/Mills approximation to the finite intensity. -/
def betaCorrelationEndpointIntensity (m p : ℕ) (x : ℝ) : ℝ :=
  ((p.choose 2 : ℕ) : ℝ) * betaCorrelationEndpointProbability m p x

/-- A named finite analytic obligation on the compact threshold window
`|x| ≤ M`: the exact Beta intensity differs from the fixed intensity by at
most `C` times the explicit envelope.  This is kept as a proposition, not
introduced as an axiom.  Compact localization is essential; a global-in-`x`
estimate requires separate extreme-tail arguments. -/
def HasBetaIntensityFiniteBound (M C : ℝ) : Prop :=
  ∀ m p : ℕ, 3 ≤ p → p ≤ m → ∀ x : ℝ, |x| ≤ M →
    |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| ≤
      C * betaIntensityErrorEnvelope m p

/-- The exact finite Beta intensity is nonnegative. -/
theorem finiteCoherenceIntensity_nonneg (m p : ℕ) (x : ℝ) :
    0 ≤ finiteCoherenceIntensity m p x := by
  exact mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

/-- The fixed coherence intensity is strictly positive. -/
theorem classicalCoherenceIntensity_pos (x : ℝ) :
    0 < classicalCoherenceIntensity x := by
  unfold classicalCoherenceIntensity
  positivity

/-- Positivity of the endpoint approximation in its natural finite range. -/
theorem betaCorrelationEndpointProbability_pos
    {m p : ℕ} {x : ℝ} (hm : 4 ≤ m)
    (hthreshold0 : 0 < classicalCoherenceThreshold m p x)
    (hthresholdm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    0 < betaCorrelationEndpointProbability m p x := by
  let b : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let t : ℝ := classicalCoherenceThreshold m p x / (m : ℝ)
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hm1 : 1 ≤ m := by omega
  have hb : 0 < b := by
    dsimp [b]
    rw [Nat.cast_sub hm1, Nat.cast_one]
    have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have ht : 0 < t := div_pos hthreshold0 hm0
  have ht1 : t < 1 := (div_lt_one hm0).2 hthresholdm
  have hbase : 0 < 1 - t := sub_pos.mpr ht1
  have hendpoint : 0 < betaHalfTailEndpoint b t := by
    unfold betaHalfTailEndpoint
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos ht _)
        (Real.rpow_pos_of_pos hbase _)) hb
  have hbeta : 0 < beta (1 / 2) b := beta_pos (by norm_num) hb
  exact div_pos hendpoint hbeta

/-- Positivity of the scaled endpoint intensity when at least one edge is
present. -/
theorem betaCorrelationEndpointIntensity_pos
    {m p : ℕ} {x : ℝ} (hp : 2 ≤ p) (hm : 4 ≤ m)
    (hthreshold0 : 0 < classicalCoherenceThreshold m p x)
    (hthresholdm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    0 < betaCorrelationEndpointIntensity m p x := by
  exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hp))
    (betaCorrelationEndpointProbability_pos hm hthreshold0 hthresholdm)

/-- Exact scaled Mills sandwich for the finite exceedance intensity. -/
theorem finiteCoherenceIntensity_mills_bounds
    {m p : ℕ} {x : ℝ} (hm : 4 ≤ m)
    (hthreshold0 : 0 < classicalCoherenceThreshold m p x)
    (hthresholdm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    betaCorrelationEndpointIntensity m p x /
        (1 + 1 / betaCorrelationMillsRate m p x) ≤
          finiteCoherenceIntensity m p x ∧
      finiteCoherenceIntensity m p x ≤
        betaCorrelationEndpointIntensity m p x := by
  have h := betaCorrelationTail_mills_bounds hm hthreshold0 hthresholdm
  have hn : 0 ≤ (((p.choose 2 : ℕ) : ℝ)) := Nat.cast_nonneg _
  constructor
  · calc
      betaCorrelationEndpointIntensity m p x /
          (1 + 1 / betaCorrelationMillsRate m p x) =
          ((p.choose 2 : ℕ) : ℝ) *
            (betaCorrelationEndpointProbability m p x /
              (1 + 1 / betaCorrelationMillsRate m p x)) := by
                unfold betaCorrelationEndpointIntensity
                ring
      _ ≤ ((p.choose 2 : ℕ) : ℝ) *
          betaCorrelationTailProbability m p x :=
            mul_le_mul_of_nonneg_left h.1 hn
      _ = finiteCoherenceIntensity m p x := rfl
  · exact mul_le_mul_of_nonneg_left h.2 hn

/-- The exact intensity error is bounded by the endpoint error plus the
explicit Mills correction.  This removes all probability measures from the
remaining rate problem. -/
theorem finiteCoherenceIntensity_sub_fixed_le_endpoint_add_mills
    {m p : ℕ} {x : ℝ} (hm : 4 ≤ m)
    (hthreshold0 : 0 < classicalCoherenceThreshold m p x)
    (hthresholdm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| ≤
      |betaCorrelationEndpointIntensity m p x -
        classicalCoherenceIntensity x| +
      (betaCorrelationEndpointIntensity m p x -
        betaCorrelationEndpointIntensity m p x /
          (1 + 1 / betaCorrelationMillsRate m p x)) := by
  have hM := finiteCoherenceIntensity_mills_bounds hm hthreshold0 hthresholdm
  calc
    |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| ≤
        |finiteCoherenceIntensity m p x -
            betaCorrelationEndpointIntensity m p x| +
          |betaCorrelationEndpointIntensity m p x -
            classicalCoherenceIntensity x| := abs_sub_le _ _ _
    _ = (betaCorrelationEndpointIntensity m p x -
          finiteCoherenceIntensity m p x) +
          |betaCorrelationEndpointIntensity m p x -
            classicalCoherenceIntensity x| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hM.2), neg_sub]
    _ ≤ (betaCorrelationEndpointIntensity m p x -
          betaCorrelationEndpointIntensity m p x /
            (1 + 1 / betaCorrelationMillsRate m p x)) +
          |betaCorrelationEndpointIntensity m p x -
            classicalCoherenceIntensity x| := by
      linarith [hM.1]
    _ = |betaCorrelationEndpointIntensity m p x -
          classicalCoherenceIntensity x| +
        (betaCorrelationEndpointIntensity m p x -
          betaCorrelationEndpointIntensity m p x /
            (1 + 1 / betaCorrelationMillsRate m p x)) := by ring

/-- Finite form of the identity used in the endpoint asymptotic: the Beta
power ratio is exactly the exponential of its logarithmic error. -/
theorem betaCorrelationPowerExpRatio_eq_exp_logPowerError
    {m p : ℕ} {x : ℝ}
    (hbase : 0 < 1 - classicalCoherenceThreshold m p x / (m : ℝ)) :
    betaCorrelationPowerExpRatio m p x =
      Real.exp (betaCorrelationLogPowerError m p x) := by
  unfold betaCorrelationPowerExpRatio
  rw [Real.rpow_def_of_pos hbase, ← Real.exp_sub]
  unfold betaCorrelationLogPowerError
  congr 1
  ring

/-- Explicit finite normalization sandwich inherited from the verified
Gamma-ratio inequality. -/
theorem betaHalfEndpointNormalization_bounds
    {m : ℕ} (hm : 2 ≤ m) :
    √2 / √Real.pi ≤ betaHalfEndpointNormalization m ∧
      betaHalfEndpointNormalization m ≤
        (√2 / √Real.pi) * (1 + 1 / (m : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) / 2 := by positivity
  have hratio := gammaHalfRatioScale_bounds hmpos
  have hc : 0 ≤ √2 / √Real.pi := by positivity
  have heq := betaHalfEndpointNormalization_eq_gamma (by omega : 1 < m)
  rw [heq, betaHalfGammaNormalization_eq]
  constructor
  · simpa using mul_le_mul_of_nonneg_left hratio.1 hc
  · have hu := mul_le_mul_of_nonneg_left hratio.2 hc
    simpa [show (2 : ℝ) * ((m : ℝ) / 2) = (m : ℝ) by ring] using hu

/-- Exact pointwise factorization of the endpoint intensity.  All remaining
quantitative work is now an elementary comparison of the five displayed
real factors. -/
theorem betaCorrelationEndpointIntensity_eq_limitFactor
    {m p : ℕ} {x : ℝ} (hm : 2 ≤ m) (hp : 1 < p)
    (hthreshold : 0 < classicalCoherenceThreshold m p x) :
    betaCorrelationEndpointIntensity m p x =
      betaEndpointLimitFactor m p x := by
  have hlogpos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp)
  have hendpoint :=
    betaCorrelationEndpointProbability_eq_normalization_mul_core hm hthreshold
  have hexact := exp_neg_classicalCoherenceThreshold_half
    (m := m) (x := x) hp
  have hsqrt := rpow_neg_half_mul_sqrt_eq_sqrt_div hthreshold hlogpos
  have hsqrt' :
      √(Real.log (p : ℝ) *
          (classicalCoherenceThreshold m p x)⁻¹) =
        classicalCoherenceThreshold m p x ^ (-(1 / 2 : ℝ)) *
          √(Real.log (p : ℝ)) := by
    simpa [div_eq_mul_inv] using hsqrt.symm
  have hpower :
      (1 - classicalCoherenceThreshold m p x / (m : ℝ)) ^
          (((m - 1 : ℕ) : ℝ) / 2) =
        betaCorrelationPowerExpRatio m p x *
          Real.exp (-classicalCoherenceThreshold m p x / 2) := by
    unfold betaCorrelationPowerExpRatio
    field_simp [Real.exp_ne_zero]
  unfold betaCorrelationEndpointIntensity
  rw [hendpoint]
  unfold betaCorrelationPowerCore betaEndpointLimitFactor
  rw [hpower, hexact]
  ring_nf
  rw [hsqrt']
  ring_nf

/-- Elementary square-root perturbation bound used by the classical
threshold factor. -/
theorem abs_one_div_sqrt_one_sub_sub_one_le
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |1 / √(1 - u) - 1| ≤ 2 * |u| := by
  have hubounds := (abs_le.mp hu)
  have hv : 0 < 1 - u := by linarith
  let s : ℝ := √(1 - u)
  have hspos : 0 < s := Real.sqrt_pos.2 hv
  have hs2 : s ^ 2 = 1 - u := by
    dsimp [s]
    exact Real.sq_sqrt hv.le
  have hsge : (1 / 2 : ℝ) ≤ s := by
    rw [Real.le_sqrt' (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith
  have hden : (1 / 2 : ℝ) ≤ s * (1 + s) := by
    have hone : (1 : ℝ) ≤ 1 + s := by linarith
    calc
      (1 / 2 : ℝ) = (1 / 2) * 1 := by ring
      _ ≤ s * (1 + s) :=
        mul_le_mul hsge hone (by norm_num) (by linarith)
  have hdenpos : 0 < s * (1 + s) := lt_of_lt_of_le (by norm_num) hden
  have hid : 1 / s - 1 = u / (s * (1 + s)) := by
    field_simp [hspos.ne']
    nlinarith
  rw [show √(1 - u) = s by rfl, hid, abs_div,
    abs_of_pos hdenpos]
  apply (div_le_iff₀ hdenpos).2
  nlinarith [abs_nonneg u]

/-- The threshold square-root factor inherits the elementary perturbation
bound. -/
theorem abs_sqrt_log_div_classicalThreshold_sub_half_le
    {m p : ℕ} {x : ℝ}
    (hlog : 0 < Real.log (p : ℝ))
    (hsmall :
      |(Real.log (Real.log (p : ℝ)) - x) /
        (4 * Real.log (p : ℝ))| ≤ 1 / 2) :
    |√(Real.log (p : ℝ) / classicalCoherenceThreshold m p x) - 1 / 2| ≤
      |(Real.log (Real.log (p : ℝ)) - x) /
        (4 * Real.log (p : ℝ))| := by
  let L : ℝ := Real.log (p : ℝ)
  let u : ℝ := (Real.log L - x) / (4 * L)
  have hu : |u| ≤ 1 / 2 := by simpa [u, L] using hsmall
  have hv : 0 < 1 - u := by
    have := (abs_le.mp hu).2
    linarith
  have hratio :
      L / classicalCoherenceThreshold m p x = (1 / 4 : ℝ) / (1 - u) := by
    have hL : L ≠ 0 := (by simpa [L] using hlog.ne')
    unfold classicalCoherenceThreshold
    dsimp [u, L]
    field_simp [hL]
    ring
  have hsqrt :
      √(L / classicalCoherenceThreshold m p x) =
        (1 / 2 : ℝ) / √(1 - u) := by
    rw [hratio, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
  have hpert := abs_one_div_sqrt_one_sub_sub_one_le hu
  dsimp [L] at hsqrt
  rw [hsqrt]
  calc
    |(1 / 2 : ℝ) / √(1 - u) - 1 / 2| =
        (1 / 2) * |1 / √(1 - u) - 1| := by
          rw [show (1 / 2 : ℝ) / √(1 - u) - 1 / 2 =
              (1 / 2) * (1 / √(1 - u) - 1) by ring,
            abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2) * (2 * |u|) :=
      mul_le_mul_of_nonneg_left hpert (by norm_num)
    _ = |(Real.log (Real.log (p : ℝ)) - x) /
        (4 * Real.log (p : ℝ))| := by simp [u, L]

/-- Finite power-ratio error obtained from the verified logarithmic error
bound and the standard exponential remainder inequality. -/
theorem abs_betaCorrelationPowerExpRatio_sub_one_le
    {m p : ℕ} {x : ℝ} (hm : 2 ≤ m)
    (hthreshold0 : 0 ≤ classicalCoherenceThreshold m p x)
    (hthresholdm : classicalCoherenceThreshold m p x < (m : ℝ))
    (hboundOne : betaCorrelationLogPowerErrorBound m p x ≤ 1) :
    |betaCorrelationPowerExpRatio m p x - 1| ≤
      2 * betaCorrelationLogPowerErrorBound m p x := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hbase : 0 < 1 - classicalCoherenceThreshold m p x / (m : ℝ) :=
    sub_pos.mpr ((div_lt_one hm0).2 hthresholdm)
  have herr := abs_betaCorrelationLogPowerError_le
    hm hthreshold0 hthresholdm
  have herrOne : |betaCorrelationLogPowerError m p x| ≤ 1 :=
    herr.trans hboundOne
  rw [betaCorrelationPowerExpRatio_eq_exp_logPowerError hbase]
  exact (Real.abs_exp_sub_one_le herrOne).trans
    (mul_le_mul_of_nonneg_left herr (by norm_num))

/-- Absolute form of the finite normalization error. -/
theorem abs_betaHalfEndpointNormalization_sub_limit_le
    {m : ℕ} (hm : 2 ≤ m) :
    |betaHalfEndpointNormalization m - √2 / √Real.pi| ≤
      (√2 / √Real.pi) / (m : ℝ) := by
  have h := betaHalfEndpointNormalization_bounds hm
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  calc
    betaHalfEndpointNormalization m - √2 / √Real.pi ≤
        (√2 / √Real.pi) * (1 + 1 / (m : ℝ)) -
          √2 / √Real.pi := sub_le_sub_right h.2 _
    _ = (√2 / √Real.pi) / (m : ℝ) := by ring

/-- Exact edge-count factor error. -/
theorem abs_choose_two_div_sq_sub_half
    {p : ℕ} (hp : 0 < p) :
    |((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 - 1 / 2| =
      1 / (2 * (p : ℝ)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Nat.cast_choose_two]
  have heq : ((p : ℝ) * ((p : ℝ) - 1) / 2) / (p : ℝ) ^ 2 - 1 / 2 =
      -(1 / (2 * (p : ℝ))) := by
    field_simp [hpR]
    ring
  rw [heq, abs_neg, abs_of_nonneg]
  positivity

/-- Four-factor telescoping bound, with one common multiplicative factor
kept outside. -/
theorem abs_four_factor_product_sub_le
    (a b c d e A B C : ℝ) :
    |a * b * c * d * e - A * B * C * d| ≤
      |d| *
        (|a - A| * |b| * |c| * |e| +
          |A| * |b - B| * |c| * |e| +
          |A| * |B| * |c - C| * |e| +
          |A| * |B| * |C| * |e - 1|) := by
  have hid :
      a * b * c * d * e - A * B * C * d =
        d * ((a - A) * b * c * e +
          A * (b - B) * c * e +
          A * B * (c - C) * e +
          A * B * C * (e - 1)) := by ring
  rw [hid, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg d)
  calc
    |(a - A) * b * c * e + A * (b - B) * c * e +
        A * B * (c - C) * e + A * B * C * (e - 1)| ≤
      |(a - A) * b * c * e| + |A * (b - B) * c * e| +
        |A * B * (c - C) * e| + |A * B * C * (e - 1)| := by
          calc
            |(a - A) * b * c * e + A * (b - B) * c * e +
                A * B * (c - C) * e + A * B * C * (e - 1)| ≤
              |(a - A) * b * c * e + A * (b - B) * c * e +
                A * B * (c - C) * e| + |A * B * C * (e - 1)| :=
                  abs_add_le _ _
            _ ≤ (|(a - A) * b * c * e| + |A * (b - B) * c * e| +
                |A * B * (c - C) * e|) + |A * B * C * (e - 1)| := by
              gcongr
              calc
                |(a - A) * b * c * e + A * (b - B) * c * e +
                    A * B * (c - C) * e| ≤
                  |(a - A) * b * c * e + A * (b - B) * c * e| +
                    |A * B * (c - C) * e| := abs_add_le _ _
                _ ≤ (|(a - A) * b * c * e| + |A * (b - B) * c * e|) +
                    |A * B * (c - C) * e| := by
                      gcongr
                      exact abs_add_le _ _
            _ = _ := by ring
    _ = |a - A| * |b| * |c| * |e| +
          |A| * |b - B| * |c| * |e| +
          |A| * |B| * |c - C| * |e| +
          |A| * |B| * |C| * |e - 1| := by
            simp only [abs_mul]

/-- Completely explicit algebraic endpoint-error envelope. -/
def betaEndpointFactorErrorEnvelope (m p : ℕ) (x : ℝ) : ℝ :=
  |Real.exp (-x / 2)| *
    (|((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 - 1 / 2| *
        |betaHalfEndpointNormalization m| *
        |√(Real.log (p : ℝ) / classicalCoherenceThreshold m p x)| *
        |betaCorrelationPowerExpRatio m p x| +
      |(1 / 2 : ℝ)| *
        |betaHalfEndpointNormalization m - √2 / √Real.pi| *
        |√(Real.log (p : ℝ) / classicalCoherenceThreshold m p x)| *
        |betaCorrelationPowerExpRatio m p x| +
      |(1 / 2 : ℝ)| * |√2 / √Real.pi| *
        |√(Real.log (p : ℝ) / classicalCoherenceThreshold m p x) - 1 / 2| *
        |betaCorrelationPowerExpRatio m p x| +
      |(1 / 2 : ℝ)| * |√2 / √Real.pi| * |(1 / 2 : ℝ)| *
        |betaCorrelationPowerExpRatio m p x - 1|)

/-- A convenient collection of elementary large-`p` inequalities, chosen
with deliberately loose constants so that they hold uniformly on every
fixed compact `x`-window. -/
def CompactBetaRateConditions (M : ℝ) (p : ℕ) : Prop :=
  0 ≤ M ∧
  1 ≤ Real.log (p : ℝ) ∧
  0 ≤ Real.log (Real.log (p : ℝ)) ∧
  Real.log (Real.log (p : ℝ)) + M ≤ Real.log (p : ℝ) ∧
  100 * Real.log (p : ℝ) ^ 2 ≤ (p : ℝ)

/-- Every fixed compact window eventually satisfies the coarse rate
conditions. -/
theorem eventually_compactBetaRateConditions
    {M : ℝ} (hM : 0 ≤ M) :
    ∀ᶠ p : ℕ in atTop, CompactBetaRateConditions M p := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpR
  have hloglogDiv : Tendsto (fun p : ℕ ↦
      Real.log (Real.log (p : ℝ)) / Real.log (p : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hMdiv : Tendsto (fun p : ℕ ↦ M / Real.log (p : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop M
  have hsum : Tendsto (fun p : ℕ ↦
      (Real.log (Real.log (p : ℝ)) + M) / Real.log (p : ℝ))
      atTop (nhds 0) := by
    have h := hloglogDiv.add hMdiv
    simpa only [zero_add] using h.congr'
      (Eventually.of_forall fun _p ↦ by ring)
  have hlogSq : Tendsto (fun p : ℕ ↦
      100 * Real.log (p : ℝ) ^ 2 / (p : ℝ)) atTop (nhds 0) := by
    have hbase : Tendsto (fun p : ℕ ↦
        Real.log (p : ℝ) ^ 2 / (p : ℝ)) atTop (nhds 0) := by
      simpa [Function.comp_def] using
        (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp hpR
    simpa only [mul_div_assoc, mul_zero] using hbase.const_mul 100
  filter_upwards [hlog.eventually (eventually_ge_atTop 1),
    hsum.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hlogSq.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with p hL hratio hsq
  have hLpos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le zero_lt_one hL
  have hloglog0 : 0 ≤ Real.log (Real.log (p : ℝ)) :=
    Real.log_nonneg hL
  have hsumLe : Real.log (Real.log (p : ℝ)) + M ≤ Real.log (p : ℝ) := by
    have := (div_lt_one hLpos).1 hratio
    exact this.le
  have hpPos : (0 : ℝ) < (p : ℝ) := by
    have hpN : 0 < p := by
      apply Nat.pos_of_ne_zero
      intro hp0
      subst p
      norm_num at hL
    exact_mod_cast hpN
  have hsqLe : 100 * Real.log (p : ℝ) ^ 2 ≤ (p : ℝ) := by
    exact ((div_lt_one hpPos).1 hsq).le
  exact ⟨hM, hL, hloglog0, hsumLe, hsqLe⟩

/-- The coarse compact conditions imply every domain and small-error
hypothesis required by the finite Beta lemmas. -/
theorem compactBetaRateConditions_finite_bounds
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    0 < classicalCoherenceThreshold m p x ∧
    classicalCoherenceThreshold m p x < (m : ℝ) ∧
    |(Real.log (Real.log (p : ℝ)) - x) /
      (4 * Real.log (p : ℝ))| ≤ 1 / 2 ∧
    betaCorrelationLogPowerErrorBound m p x ≤ 1 ∧
    betaCorrelationLogPowerErrorBound m p x ≤
      28 * (Real.log (p : ℝ) ^ 2 / (m : ℝ)) := by
  rcases hcond with ⟨hM, hL, hloglog0, hsumLe, hsq⟩
  let L : ℝ := Real.log (p : ℝ)
  let ell : ℝ := Real.log L
  let A : ℝ := classicalCoherenceThreshold m p x
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hpN : 0 < p := by
    apply Nat.pos_of_ne_zero
    intro hp0
    subst p
    norm_num [L] at hL
  have hpPos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmPos : (0 : ℝ) < (m : ℝ) :=
    lt_of_lt_of_le hpPos (Nat.cast_le.mpr hpm)
  have hxBounds := abs_le.mp hx
  have hMleL : M ≤ L := by
    dsimp [ell, L] at hloglog0 hsumLe ⊢
    linarith
  have hAlower : 2 * L ≤ A := by
    dsimp [A, L, ell]
    unfold classicalCoherenceThreshold
    linarith
  have hAupper : A ≤ 5 * L := by
    dsimp [A, L, ell]
    unfold classicalCoherenceThreshold
    linarith
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos (by norm_num) hLpos) hAlower
  have hpLarge : 5 * L < (p : ℝ) := by
    dsimp [L] at hL hsq ⊢
    nlinarith [sq_nonneg (Real.log (p : ℝ))]
  have hAm : A < (m : ℝ) :=
    hAupper.trans_lt (hpLarge.trans_le (Nat.cast_le.mpr hpm))
  have hnum : |ell - x| ≤ L := by
    calc
      |ell - x| = |ell + (-x)| := by ring
      _ ≤ |ell| + |-x| := abs_add_le _ _
      _ = ell + |x| := by
        rw [abs_neg, abs_of_nonneg]
        simpa [ell, L] using hloglog0
      _ ≤ ell + M := add_le_add le_rfl hx
      _ ≤ L := by simpa [ell, L] using hsumLe
  have hsmallQuarter : |ell - x| / (4 * L) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hLpos)).2
    nlinarith
  have hsmall : |(ell - x) / (4 * L)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hLpos)]
    exact hsmallQuarter.trans (by norm_num)
  have hy0 : 0 ≤ A / (m : ℝ) := div_nonneg hApos.le hmPos.le
  have hyhalf : A / (m : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hmPos).2
    have hpTen : 10 * L ≤ (p : ℝ) := by
      dsimp [L] at hL hsq ⊢
      nlinarith [sq_nonneg (Real.log (p : ℝ))]
    have : 10 * L ≤ (m : ℝ) := hpTen.trans (Nat.cast_le.mpr hpm)
    nlinarith
  have hden : 1 / 2 ≤ 1 - A / (m : ℝ) := by linarith
  have hdenpos : 0 < 1 - A / (m : ℝ) := lt_of_lt_of_le (by norm_num) hden
  have hAsq : A ^ 2 / (m : ℝ) ≤
      25 * (L ^ 2 / (m : ℝ)) := by
    have hraw : A ^ 2 ≤ 25 * L ^ 2 := by
      have hprod : 0 ≤ (5 * L - A) * (5 * L + A) :=
        mul_nonneg (sub_nonneg.mpr hAupper)
          (add_nonneg (mul_nonneg (by norm_num) hLpos.le) hApos.le)
      nlinarith
    calc
      A ^ 2 / (m : ℝ) ≤ (25 * L ^ 2) / (m : ℝ) :=
        (div_le_div_iff_of_pos_right hmPos).2 hraw
      _ = 25 * (L ^ 2 / (m : ℝ)) := by ring
  have hfirst : (1 / 2 : ℝ) * (A ^ 2 / (m : ℝ)) /
      (1 - A / (m : ℝ)) ≤ A ^ 2 / (m : ℝ) := by
    apply (div_le_iff₀ hdenpos).2
    have hq : 0 ≤ A ^ 2 / (m : ℝ) := div_nonneg (sq_nonneg _) hmPos.le
    nlinarith
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hyq : A / (m : ℝ) ≤ 5 * (L ^ 2 / (m : ℝ)) := by
    have hraw : A ≤ 5 * L ^ 2 := by nlinarith
    calc
      A / (m : ℝ) ≤ (5 * L ^ 2) / (m : ℝ) :=
        (div_le_div_iff_of_pos_right hmPos).2 hraw
      _ = 5 * (L ^ 2 / (m : ℝ)) := by ring
  have hbound28 : betaCorrelationLogPowerErrorBound m p x ≤
      28 * (L ^ 2 / (m : ℝ)) := by
    unfold betaCorrelationLogPowerErrorBound
    change (1 / 2 : ℝ) * (A ^ 2 / (m : ℝ)) /
        (1 - A / (m : ℝ)) + (A / (m : ℝ)) / 2 ≤ _
    nlinarith
  have hqHundred : 100 * (L ^ 2 / (m : ℝ)) ≤ 1 := by
    rw [show 100 * (L ^ 2 / (m : ℝ)) =
      (100 * L ^ 2) / (m : ℝ) by ring]
    apply (div_le_iff₀ hmPos).2
    rw [one_mul]
    exact (show 100 * L ^ 2 ≤ (p : ℝ) by simpa [L] using hsq).trans
      (Nat.cast_le.mpr hpm)
  have hboundOne : betaCorrelationLogPowerErrorBound m p x ≤ 1 := by
    nlinarith
  simpa [A, L, ell] using And.intro hApos
    (And.intro hAm (And.intro hsmall (And.intro hboundOne hbound28)))

/-- Each summand in the explicit rate is nonnegative and bounded by the
whole rate under the compact conditions. -/
theorem compactBetaRateConditions_envelope_components
    {M : ℝ} {m p : ℕ} (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) :
    0 ≤ betaIntensityErrorEnvelope m p ∧
    (1 + Real.log (Real.log (p : ℝ))) / Real.log (p : ℝ) ≤
      betaIntensityErrorEnvelope m p ∧
    Real.log (p : ℝ) ^ 2 / (m : ℝ) ≤
      betaIntensityErrorEnvelope m p ∧
    1 / (p : ℝ) ≤ betaIntensityErrorEnvelope m p := by
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  have hLpos : 0 < Real.log (p : ℝ) := by linarith
  have hpN : 0 < p := by
    apply Nat.pos_of_ne_zero
    intro hp0
    subst p
    norm_num at hL
  have hmN : 0 < m := hpN.trans_le hpm
  have hfirst : 0 ≤
      (1 + Real.log (Real.log (p : ℝ))) / Real.log (p : ℝ) :=
    div_nonneg (by linarith) hLpos.le
  have hsecond : 0 ≤ Real.log (p : ℝ) ^ 2 / (m : ℝ) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hthird : 0 ≤ 1 / (p : ℝ) := by positivity
  unfold betaIntensityErrorEnvelope
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

set_option maxHeartbeats 800000 in
/-- Uniform compact-window bound for the purely algebraic endpoint-factor
envelope.  Constants are intentionally loose; the dependence on `m,p` is the
explicit rate itself. -/
theorem betaEndpointFactorErrorEnvelope_le_compact_rate
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    betaEndpointFactorErrorEnvelope m p x ≤
      Real.exp (M / 2) * (√2 / √Real.pi) * (20 + M) *
        betaIntensityErrorEnvelope m p := by
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  have hcond' : CompactBetaRateConditions M p :=
    ⟨hM, hL, hell, hsum, hsq⟩
  have hf := compactBetaRateConditions_finite_bounds hcond' hpm hx
  have hrho := compactBetaRateConditions_envelope_components hcond' hpm
  let L : ℝ := Real.log (p : ℝ)
  let ell : ℝ := Real.log L
  let A : ℝ := classicalCoherenceThreshold m p x
  let rho : ℝ := betaIntensityErrorEnvelope m p
  let K : ℝ := √2 / √Real.pi
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hpN : 0 < p := by
    apply Nat.pos_of_ne_zero
    intro hp0
    subst p
    norm_num [L] at hL
  have hp100 : 100 ≤ p := by
    have hp100R : (100 : ℝ) ≤ (p : ℝ) := by
      have hLsq : 1 ≤ L ^ 2 := by nlinarith
      have hsq' : 100 * L ^ 2 ≤ (p : ℝ) := by simpa [L] using hsq
      nlinarith
    exact_mod_cast hp100R
  have hp2 : 2 ≤ p := by omega
  have hm2 : 2 ≤ m := hp2.trans hpm
  have hpPos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmPos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hMleL : M ≤ L := by
    dsimp [ell, L] at hell hsum ⊢
    linarith
  have hxBounds := abs_le.mp hx
  have hAlower : 2 * L ≤ A := by
    dsimp [A, L, ell]
    unfold classicalCoherenceThreshold
    linarith
  have hAupper : A ≤ 5 * L := by
    dsimp [A, L, ell]
    unfold classicalCoherenceThreshold
    linarith
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos (by norm_num) hLpos) hAlower
  have hAm : A < (m : ℝ) := by simpa [A] using hf.2.1
  have hqHundred : 100 * (L ^ 2 / (m : ℝ)) ≤ 1 := by
    rw [show 100 * (L ^ 2 / (m : ℝ)) =
      (100 * L ^ 2) / (m : ℝ) by ring]
    apply (div_le_iff₀ hmPos).2
    rw [one_mul]
    exact (show 100 * L ^ 2 ≤ (p : ℝ) by simpa [L] using hsq).trans
      (Nat.cast_le.mpr hpm)
  have hrho0 : 0 ≤ rho := by simpa [rho] using hrho.1
  have hr1 : (1 + ell) / L ≤ rho := by
    simpa [rho, ell, L] using hrho.2.1
  have hr2 : L ^ 2 / (m : ℝ) ≤ rho := by
    simpa [rho, L] using hrho.2.2.1
  have hr3 : 1 / (p : ℝ) ≤ rho := by
    simpa [rho] using hrho.2.2.2
  have haeq : ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 =
      (1 - 1 / (p : ℝ)) / 2 := by
    rw [Nat.cast_choose_two]
    field_simp [hpPos.ne']
  have hinvp_le : 1 / (p : ℝ) ≤ 1 := by
    exact (div_le_one hpPos).2 (by exact_mod_cast (show 1 ≤ p by omega))
  have ha0 : 0 ≤ ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have haLe : ((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [haeq]
    have hinvp0 : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith
  have hda : |((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 - 1 / 2| ≤
      rho / 2 := by
    rw [abs_choose_two_div_sq_sub_half hpN]
    calc
      1 / (2 * (p : ℝ)) = (1 / (p : ℝ)) / 2 := by ring
      _ ≤ rho / 2 := div_le_div_of_nonneg_right hr3 (by norm_num)
  have hnormBounds := betaHalfEndpointNormalization_bounds hm2
  have hnorm0 : 0 ≤ betaHalfEndpointNormalization m :=
    hKpos.le.trans hnormBounds.1
  have hinvmHalf : 1 / (m : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hmPos).2
    have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    nlinarith
  have hnormLe : betaHalfEndpointNormalization m ≤ (3 / 2) * K := by
    have := hnormBounds.2
    dsimp [K]
    nlinarith
  have hdb : |betaHalfEndpointNormalization m - K| ≤ K * rho := by
    have hbase := abs_betaHalfEndpointNormalization_sub_limit_le hm2
    have hinvm_le_r2 : 1 / (m : ℝ) ≤ L ^ 2 / (m : ℝ) := by
      apply (div_le_div_iff_of_pos_right hmPos).2
      nlinarith
    dsimp [K] at hbase ⊢
    calc
      |betaHalfEndpointNormalization m - √2 / √Real.pi| ≤
          (√2 / √Real.pi) / (m : ℝ) := hbase
      _ = (√2 / √Real.pi) * (1 / (m : ℝ)) := by ring
      _ ≤ (√2 / √Real.pi) * (L ^ 2 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hinvm_le_r2 hKpos.le
      _ ≤ (√2 / √Real.pi) * rho :=
        mul_le_mul_of_nonneg_left hr2 hKpos.le
  have hratioLA0 : 0 ≤ L / A := div_nonneg hLpos.le hApos.le
  have hratioLAle : L / A ≤ 1 := (div_le_one hApos).2 (by linarith)
  have hsqrt0 : 0 ≤ √(L / A) := Real.sqrt_nonneg _
  have hsqrtLe : √(L / A) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hratioLAle
  have hnum : |ell - x| ≤ ell + M := by
    calc
      |ell - x| = |ell + (-x)| := by ring_nf
      _ ≤ |ell| + |-x| := abs_add_le _ _
      _ = ell + |x| := by rw [abs_neg, abs_of_nonneg]; simpa [ell, L] using hell
      _ ≤ ell + M := add_le_add le_rfl hx
  have huRate : |(ell - x) / (4 * L)| ≤
      ((M + 1) / 4) * ((1 + ell) / L) := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hLpos)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hLpos)).2
    have hell0 : 0 ≤ ell := by simpa [ell, L] using hell
    have hprod : 0 ≤ M * ell := mul_nonneg hM hell0
    calc
      |ell - x| ≤ ell + M := hnum
      _ ≤ (M + 1) * (1 + ell) := by nlinarith
      _ = (((M + 1) / 4) * ((1 + ell) / L)) * (4 * L) := by
        field_simp [hLpos.ne']
  have hdc : |√(L / A) - 1 / 2| ≤ ((M + 1) / 4) * rho := by
    have hs := abs_sqrt_log_div_classicalThreshold_sub_half_le
      (m := m) (p := p) (x := x) (by simpa [L] using hLpos)
      hf.2.2.1
    dsimp [A, L, ell] at hs ⊢
    calc
      |√(Real.log (p : ℝ) / classicalCoherenceThreshold m p x) - 1 / 2| ≤
          |(Real.log (Real.log (p : ℝ)) - x) /
            (4 * Real.log (p : ℝ))| := hs
      _ ≤ ((M + 1) / 4) * ((1 + Real.log (Real.log (p : ℝ))) /
          Real.log (p : ℝ)) := by simpa [ell, L] using huRate
      _ ≤ ((M + 1) / 4) * rho := by
        gcongr
  have hde : |betaCorrelationPowerExpRatio m p x - 1| ≤ 56 * rho := by
    have hpwr := abs_betaCorrelationPowerExpRatio_sub_one_le hm2
      hf.1.le hf.2.1 hf.2.2.2.1
    calc
      |betaCorrelationPowerExpRatio m p x - 1| ≤
          2 * betaCorrelationLogPowerErrorBound m p x := hpwr
      _ ≤ 56 * (L ^ 2 / (m : ℝ)) := by
        have hb : betaCorrelationLogPowerErrorBound m p x ≤
            28 * (L ^ 2 / (m : ℝ)) := by simpa [L] using hf.2.2.2.2
        calc
          2 * betaCorrelationLogPowerErrorBound m p x ≤
              2 * (28 * (L ^ 2 / (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hb (by norm_num)
          _ = 56 * (L ^ 2 / (m : ℝ)) := by ring
      _ ≤ 56 * rho := by
        exact mul_le_mul_of_nonneg_left hr2 (by norm_num)
  have hdeOne : |betaCorrelationPowerExpRatio m p x - 1| ≤ 1 := by
    calc
      |betaCorrelationPowerExpRatio m p x - 1| ≤
          56 * (L ^ 2 / (m : ℝ)) := by
        have hpwr := abs_betaCorrelationPowerExpRatio_sub_one_le hm2
          hf.1.le hf.2.1 hf.2.2.2.1
        have hb : betaCorrelationLogPowerErrorBound m p x ≤
            28 * (L ^ 2 / (m : ℝ)) := by simpa [L] using hf.2.2.2.2
        exact hpwr.trans (by
          calc
            2 * betaCorrelationLogPowerErrorBound m p x ≤
                2 * (28 * (L ^ 2 / (m : ℝ))) :=
              mul_le_mul_of_nonneg_left hb (by norm_num)
            _ = 56 * (L ^ 2 / (m : ℝ)) := by ring)
      _ ≤ 1 := by
        have hq0 : 0 ≤ L ^ 2 / (m : ℝ) :=
          div_nonneg (sq_nonneg _) hmPos.le
        nlinarith only [hqHundred]
  have hpwrAbs : |betaCorrelationPowerExpRatio m p x| ≤ 2 := by
    calc
      |betaCorrelationPowerExpRatio m p x| =
          |betaCorrelationPowerExpRatio m p x - 0| := by ring
      _ ≤ |betaCorrelationPowerExpRatio m p x - 1| + |1 - 0| :=
        abs_sub_le _ _ _
      _ ≤ 2 := by
        norm_num
        linarith only [hdeOne]
  have hexpAbs : |Real.exp (-x / 2)| ≤ Real.exp (M / 2) := by
    rw [Real.abs_exp]
    exact Real.exp_le_exp.mpr (by linarith [hxBounds.1])
  have ht1 :
      |((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 - 1 / 2| *
          |betaHalfEndpointNormalization m| * |√(L / A)| *
          |betaCorrelationPowerExpRatio m p x| ≤
        (rho / 2) * ((3 / 2) * K) * 1 * 2 := by
    rw [abs_of_nonneg hnorm0, abs_of_nonneg hsqrt0]
    gcongr
  have ht2 :
      |(1 / 2 : ℝ)| * |betaHalfEndpointNormalization m - K| *
          |√(L / A)| * |betaCorrelationPowerExpRatio m p x| ≤
        (1 / 2) * (K * rho) * 1 * 2 := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hsqrt0]
    gcongr
  have ht3 :
      |(1 / 2 : ℝ)| * |K| * |√(L / A) - 1 / 2| *
          |betaCorrelationPowerExpRatio m p x| ≤
        (1 / 2) * K * (((M + 1) / 4) * rho) * 2 := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hKpos.le]
    gcongr
  have ht4 :
      |(1 / 2 : ℝ)| * |K| * |(1 / 2 : ℝ)| *
          |betaCorrelationPowerExpRatio m p x - 1| ≤
        (1 / 2) * K * (1 / 2) * (56 * rho) := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hKpos.le]
    gcongr
  unfold betaEndpointFactorErrorEnvelope
  change |Real.exp (-x / 2)| * (_ + _ + _ + _) ≤ _
  calc
    |Real.exp (-x / 2)| * (_ + _ + _ + _) ≤
        Real.exp (M / 2) *
          ((rho / 2) * ((3 / 2) * K) * 1 * 2 +
            (1 / 2) * (K * rho) * 1 * 2 +
            (1 / 2) * K * (((M + 1) / 4) * rho) * 2 +
            (1 / 2) * K * (1 / 2) * (56 * rho)) := by
      apply mul_le_mul hexpAbs
        (add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4)
        (by positivity) (Real.exp_pos _).le
    _ ≤ Real.exp (M / 2) * K * (20 + M) * rho := by
      have hcoef : (67 / 4 : ℝ) + M / 4 ≤ 20 + M := by linarith
      rw [show Real.exp (M / 2) *
          ((rho / 2) * ((3 / 2) * K) * 1 * 2 +
            (1 / 2) * (K * rho) * 1 * 2 +
            (1 / 2) * K * (((M + 1) / 4) * rho) * 2 +
            (1 / 2) * K * (1 / 2) * (56 * rho)) =
          (Real.exp (M / 2) * K * rho) * ((67 / 4) + M / 4) by ring,
        show Real.exp (M / 2) * K * (20 + M) * rho =
          (Real.exp (M / 2) * K * rho) * (20 + M) by ring]
      exact mul_le_mul_of_nonneg_left hcoef
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hKpos.le) hrho0)
    _ = Real.exp (M / 2) * (√2 / √Real.pi) * (20 + M) *
        betaIntensityErrorEnvelope m p := by rfl

/-- The endpoint error is bounded by the explicit factor envelope. -/
theorem abs_betaCorrelationEndpointIntensity_sub_fixed_le_factorEnvelope
    {m p : ℕ} {x : ℝ} (hm : 2 ≤ m) (hp : 1 < p)
    (hthreshold : 0 < classicalCoherenceThreshold m p x) :
    |betaCorrelationEndpointIntensity m p x -
        classicalCoherenceIntensity x| ≤
      betaEndpointFactorErrorEnvelope m p x := by
  rw [betaCorrelationEndpointIntensity_eq_limitFactor hm hp hthreshold,
    classicalCoherenceIntensity_eq_endpoint_product]
  unfold betaEndpointLimitFactor betaEndpointFactorErrorEnvelope
  simpa [mul_assoc] using abs_four_factor_product_sub_le
    (((p.choose 2 : ℕ) : ℝ) / (p : ℝ) ^ 2)
    (betaHalfEndpointNormalization m)
    (√(Real.log (p : ℝ) / classicalCoherenceThreshold m p x))
    (Real.exp (-x / 2))
    (betaCorrelationPowerExpRatio m p x)
    (1 / 2) (√2 / √Real.pi) (1 / 2)

/-- The compact large-`p` conditions force the explicit error envelope to
remain bounded by a harmless numerical constant. -/
theorem betaIntensityErrorEnvelope_le_four
    {M : ℝ} {m p : ℕ}
    (hcond : CompactBetaRateConditions M p) (hpm : p ≤ m) :
    betaIntensityErrorEnvelope m p ≤ 4 := by
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  let L : ℝ := Real.log (p : ℝ)
  let ell : ℝ := Real.log L
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hpN : 0 < p := by
    apply Nat.pos_of_ne_zero
    intro hp0
    subst p
    norm_num [L] at hL
  have hmN : 0 < m := hpN.trans_le hpm
  have hpPos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmPos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hellLe : ell ≤ L := by
    dsimp [ell, L] at hell hsum ⊢
    linarith
  have hfirst : (1 + ell) / L ≤ 2 := by
    apply (div_le_iff₀ hLpos).2
    nlinarith
  have hLsqLeM : L ^ 2 ≤ (m : ℝ) := by
    have hsq' : 100 * L ^ 2 ≤ (p : ℝ) := by simpa [L] using hsq
    have hpCast : (p : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hpm
    nlinarith [sq_nonneg L]
  have hsecond : L ^ 2 / (m : ℝ) ≤ 1 :=
    (div_le_one hmPos).2 hLsqLeM
  have hthird : 1 / (p : ℝ) ≤ 1 :=
    (div_le_one hpPos).2 (by exact_mod_cast (show 1 ≤ p by omega))
  unfold betaIntensityErrorEnvelope
  simpa [L, ell] using (show (1 + ell) / L + L ^ 2 / (m : ℝ) +
      1 / (p : ℝ) ≤ 4 by linarith)

/-- Compact-window endpoint approximation with an explicit dimension-free
coefficient. -/
theorem abs_betaCorrelationEndpointIntensity_sub_fixed_le_compact_rate
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    |betaCorrelationEndpointIntensity m p x -
        classicalCoherenceIntensity x| ≤
      Real.exp (M / 2) * (√2 / √Real.pi) * (20 + M) *
        betaIntensityErrorEnvelope m p := by
  have hf := compactBetaRateConditions_finite_bounds hcond hpm hx
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  have hcond' : CompactBetaRateConditions M p :=
    ⟨hM, hL, hell, hsum, hsq⟩
  have hp100 : 100 ≤ p := by
    have hp100R : (100 : ℝ) ≤ (p : ℝ) := by
      have hLsq : 1 ≤ Real.log (p : ℝ) ^ 2 := by nlinarith
      nlinarith
    exact_mod_cast hp100R
  have hm2 : 2 ≤ m := (by omega : 2 ≤ p).trans hpm
  exact (abs_betaCorrelationEndpointIntensity_sub_fixed_le_factorEnvelope
      hm2 (by omega : 1 < p) hf.1).trans
    (betaEndpointFactorErrorEnvelope_le_compact_rate hcond' hpm hx)

/-- Under the compact rate conditions, the endpoint intensity itself is
uniformly bounded.  This deliberately loose bound is sufficient for the
Mills correction. -/
theorem betaCorrelationEndpointIntensity_le_compact_constant
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    0 ≤ betaCorrelationEndpointIntensity m p x ∧
    betaCorrelationEndpointIntensity m p x ≤
      Real.exp (M / 2) * (√2 / √Real.pi) * (81 + 4 * M) := by
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  have hcond' : CompactBetaRateConditions M p :=
    ⟨hM, hL, hell, hsum, hsq⟩
  have hf := compactBetaRateConditions_finite_bounds hcond' hpm hx
  have hp100 : 100 ≤ p := by
    have hp100R : (100 : ℝ) ≤ (p : ℝ) := by
      have hLsq : 1 ≤ Real.log (p : ℝ) ^ 2 := by nlinarith
      nlinarith
    exact_mod_cast hp100R
  have hm4 : 4 ≤ m := (by omega : 4 ≤ p).trans hpm
  have hE0 : 0 ≤ betaCorrelationEndpointIntensity m p x :=
    (betaCorrelationEndpointIntensity_pos (by omega : 2 ≤ p) hm4
      hf.1 hf.2.1).le
  have hK0 : 0 ≤ √2 / √Real.pi := by positivity
  have hexp : Real.exp (-x / 2) ≤ Real.exp (M / 2) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).1])
  have hlambda : classicalCoherenceIntensity x ≤
      Real.exp (M / 2) * (√2 / √Real.pi) := by
    rw [classicalCoherenceIntensity_eq_endpoint_product]
    calc
      (1 / 2 : ℝ) * (√2 / √Real.pi) * (1 / 2) *
          Real.exp (-x / 2) * 1 =
          (1 / 4) * (√2 / √Real.pi) * Real.exp (-x / 2) := by ring
      _ ≤ (1 / 4) * (√2 / √Real.pi) * Real.exp (M / 2) := by
        exact mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (by norm_num) hK0)
      _ ≤ 1 * (√2 / √Real.pi) * Real.exp (M / 2) := by
        gcongr <;> norm_num
      _ = Real.exp (M / 2) * (√2 / √Real.pi) := by ring
  have herr :=
    abs_betaCorrelationEndpointIntensity_sub_fixed_le_compact_rate
      hcond' hpm hx
  have hrho := betaIntensityErrorEnvelope_le_four hcond' hpm
  have hcoef0 : 0 ≤
      Real.exp (M / 2) * (√2 / √Real.pi) * (20 + M) := by
    positivity
  constructor
  · exact hE0
  · calc
      betaCorrelationEndpointIntensity m p x ≤
          classicalCoherenceIntensity x +
            |betaCorrelationEndpointIntensity m p x -
              classicalCoherenceIntensity x| := by
        linarith [le_abs_self
          (betaCorrelationEndpointIntensity m p x -
            classicalCoherenceIntensity x)]
      _ ≤ Real.exp (M / 2) * (√2 / √Real.pi) +
          Real.exp (M / 2) * (√2 / √Real.pi) * (20 + M) *
            betaIntensityErrorEnvelope m p := add_le_add hlambda herr
      _ ≤ Real.exp (M / 2) * (√2 / √Real.pi) +
          Real.exp (M / 2) * (√2 / √Real.pi) * (20 + M) * 4 := by
        gcongr
      _ = Real.exp (M / 2) * (√2 / √Real.pi) *
          (81 + 4 * M) := by ring

/-- The effective Mills rate is at least `log p` under the compact
large-`p` conditions. -/
theorem betaCorrelationMillsRate_ge_log
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    Real.log (p : ℝ) ≤ betaCorrelationMillsRate m p x := by
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  let L : ℝ := Real.log (p : ℝ)
  let A : ℝ := classicalCoherenceThreshold m p x
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hpN : 0 < p := by
    apply Nat.pos_of_ne_zero
    intro hp0
    subst p
    norm_num [L] at hL
  have hmN : 0 < m := hpN.trans_le hpm
  have hm1 : 1 ≤ m := hmN
  have hm2 : 2 ≤ m := by
    have hp100R : (100 : ℝ) ≤ (p : ℝ) := by
      have hLsq : 1 ≤ L ^ 2 := by nlinarith
      have hsq' : 100 * L ^ 2 ≤ (p : ℝ) := by simpa [L] using hsq
      nlinarith
    have hp100 : 100 ≤ p := by exact_mod_cast hp100R
    omega
  have hmPos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hxBounds := abs_le.mp hx
  have hAlower : 2 * L ≤ A := by
    dsimp [A, L]
    unfold classicalCoherenceThreshold
    linarith
  have hratio : (1 / 2 : ℝ) ≤ (((m - 1 : ℕ) : ℝ) / (m : ℝ)) := by
    rw [Nat.cast_sub hm1, Nat.cast_one]
    apply (le_div_iff₀ hmPos).2
    have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    nlinarith
  have hrateEq : betaCorrelationMillsRate m p x =
      (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * A := by
    unfold betaCorrelationMillsRate
    field_simp [hmPos.ne']
    ring
  rw [hrateEq]
  change L ≤ (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * A
  calc
    L = (1 / 2 : ℝ) * (2 * L) := by ring
    _ ≤ (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * A := by
      exact mul_le_mul hratio hAlower
        (mul_nonneg (by norm_num) hLpos.le)
        (by linarith)

/-- Pure algebra: the finite Mills correction is no larger than intensity
divided by the effective Mills rate. -/
theorem endpointMillsCorrection_le_div_rate
    {E r : ℝ} (hE : 0 ≤ E) (hr : 0 < r) :
    E - E / (1 + 1 / r) ≤ E / r := by
  have hid : E - E / (1 + 1 / r) = E / (r + 1) := by
    field_simp [hr.ne']
    ring
  rw [hid]
  exact div_le_div_of_nonneg_left hE hr (by linarith)

/-- Explicit compact-window bound for the entire finite Mills correction. -/
theorem betaMillsCorrection_le_compact_rate
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    betaCorrelationEndpointIntensity m p x -
        betaCorrelationEndpointIntensity m p x /
          (1 + 1 / betaCorrelationMillsRate m p x) ≤
      Real.exp (M / 2) * (√2 / √Real.pi) * (81 + 4 * M) *
        betaIntensityErrorEnvelope m p := by
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  have hcond' : CompactBetaRateConditions M p :=
    ⟨hM, hL, hell, hsum, hsq⟩
  let L : ℝ := Real.log (p : ℝ)
  let ell : ℝ := Real.log L
  let E : ℝ := betaCorrelationEndpointIntensity m p x
  let r : ℝ := betaCorrelationMillsRate m p x
  let C : ℝ := Real.exp (M / 2) * (√2 / √Real.pi) * (81 + 4 * M)
  let rho : ℝ := betaIntensityErrorEnvelope m p
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hE := betaCorrelationEndpointIntensity_le_compact_constant
    hcond' hpm hx
  have hrLower : L ≤ r := by
    simpa [L, r] using betaCorrelationMillsRate_ge_log hcond' hpm hx
  have hrPos : 0 < r := hLpos.trans_le hrLower
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hdiv : E / r ≤ C / L := by
    exact div_le_div₀ hC0 (by simpa [E, C] using hE.2) hLpos hrLower
  have hinvLeFirst : 1 / L ≤ (1 + ell) / L := by
    apply (div_le_div_iff_of_pos_right hLpos).2
    have hell0 : 0 ≤ ell := by simpa [ell, L] using hell
    linarith
  have hfirstLeRho : (1 + ell) / L ≤ rho := by
    have hrho := compactBetaRateConditions_envelope_components hcond' hpm
    simpa [ell, L, rho] using hrho.2.1
  calc
    betaCorrelationEndpointIntensity m p x -
        betaCorrelationEndpointIntensity m p x /
          (1 + 1 / betaCorrelationMillsRate m p x) ≤ E / r := by
      exact endpointMillsCorrection_le_div_rate hE.1 hrPos
    _ ≤ C / L := hdiv
    _ = C * (1 / L) := by ring
    _ ≤ C * ((1 + ell) / L) :=
      mul_le_mul_of_nonneg_left hinvLeFirst hC0
    _ ≤ C * rho :=
      mul_le_mul_of_nonneg_left hfirstLeRho hC0
    _ = Real.exp (M / 2) * (√2 / √Real.pi) * (81 + 4 * M) *
        betaIntensityErrorEnvelope m p := by rfl

/-- A dimension-free coefficient for the compact-window finite Beta
intensity estimate. -/
def compactBetaIntensityConstant (M : ℝ) : ℝ :=
  Real.exp (M / 2) * (√2 / √Real.pi) * (101 + 5 * M)

/-- The compact-window coefficient is strictly positive on the intended
range. -/
theorem compactBetaIntensityConstant_pos {M : ℝ} (hM : 0 ≤ M) :
    0 < compactBetaIntensityConstant M := by
  unfold compactBetaIntensityConstant
  positivity

/-- Fully explicit finite Beta-intensity estimate under the coarse compact
large-`p` conditions.  This is the analytic estimate needed to replace the
finite intensity by the fixed Gumbel intensity. -/
theorem finiteCoherenceIntensity_sub_fixed_le_compact_rate
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| ≤
      compactBetaIntensityConstant M * betaIntensityErrorEnvelope m p := by
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  have hcond' : CompactBetaRateConditions M p :=
    ⟨hM, hL, hell, hsum, hsq⟩
  have hf := compactBetaRateConditions_finite_bounds hcond' hpm hx
  have hp100 : 100 ≤ p := by
    have hp100R : (100 : ℝ) ≤ (p : ℝ) := by
      have hLsq : 1 ≤ Real.log (p : ℝ) ^ 2 := by nlinarith
      nlinarith
    exact_mod_cast hp100R
  have hm4 : 4 ≤ m := (by omega : 4 ≤ p).trans hpm
  have hsplit :=
    finiteCoherenceIntensity_sub_fixed_le_endpoint_add_mills
      hm4 hf.1 hf.2.1
  have hendpoint :=
    abs_betaCorrelationEndpointIntensity_sub_fixed_le_compact_rate
      hcond' hpm hx
  have hmills := betaMillsCorrection_le_compact_rate hcond' hpm hx
  calc
    |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| ≤
        |betaCorrelationEndpointIntensity m p x -
          classicalCoherenceIntensity x| +
        (betaCorrelationEndpointIntensity m p x -
          betaCorrelationEndpointIntensity m p x /
            (1 + 1 / betaCorrelationMillsRate m p x)) := hsplit
    _ ≤ Real.exp (M / 2) * (√2 / √Real.pi) * (20 + M) *
          betaIntensityErrorEnvelope m p +
        Real.exp (M / 2) * (√2 / √Real.pi) * (81 + 4 * M) *
          betaIntensityErrorEnvelope m p := add_le_add hendpoint hmills
    _ = compactBetaIntensityConstant M * betaIntensityErrorEnvelope m p := by
      unfold compactBetaIntensityConstant
      ring

/-- For every fixed compact threshold window there is a numerical cutoff
after which the explicit finite intensity estimate holds simultaneously for
all `m ≥ p`.  The coefficient is completely independent of `m,p`. -/
theorem eventually_uniform_betaIntensityFiniteBound
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ m : ℕ, p ≤ m → ∀ x : ℝ,
      |x| ≤ M →
      |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| ≤
        compactBetaIntensityConstant M * betaIntensityErrorEnvelope m p := by
  obtain ⟨P, hP⟩ := eventually_atTop.1
    (eventually_compactBetaRateConditions hM)
  refine ⟨P, ?_⟩
  intro p hp m hpm x hx
  exact finiteCoherenceIntensity_sub_fixed_le_compact_rate (hP p hp) hpm hx

/-- Existential form of the eventual compact estimate: both the cutoff and
the dimension-free coefficient are exposed, exactly as required by a
uniform finite-rate statement. -/
theorem exists_eventual_uniform_betaIntensityFiniteBound
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ P : ℕ, ∃ C : ℝ, ∀ p : ℕ, P ≤ p → ∀ m : ℕ, p ≤ m →
      ∀ x : ℝ, |x| ≤ M →
      |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| ≤
        C * betaIntensityErrorEnvelope m p := by
  obtain ⟨P, hP⟩ := eventually_uniform_betaIntensityFiniteBound hM
  exact ⟨P, compactBetaIntensityConstant M, hP⟩

/-- The same existential statement with positivity of the numerical
coefficient recorded explicitly. -/
theorem exists_pos_eventual_uniform_betaIntensityFiniteBound
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ P : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ p : ℕ, P ≤ p → ∀ m : ℕ, p ≤ m → ∀ x : ℝ, |x| ≤ M →
      |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| ≤
        C * betaIntensityErrorEnvelope m p := by
  obtain ⟨P, hP⟩ := eventually_uniform_betaIntensityFiniteBound hM
  exact ⟨P, compactBetaIntensityConstant M,
    compactBetaIntensityConstant_pos hM, hP⟩

/-- The negative exponential is one-Lipschitz on the nonnegative half-line.
This is the deterministic engine which replaces the finite intensity by the
fixed limiting intensity. -/
theorem abs_exp_neg_sub_exp_neg_le
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · have ht : 0 ≤ b - a := sub_nonneg.mpr hab
    have hexpOrder : Real.exp (-b) ≤ Real.exp (-a) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hfactor0 : 0 ≤ 1 - Real.exp (-(b - a)) := by
      have : Real.exp (-(b - a)) ≤ 1 := by
        simpa only [← Real.exp_zero] using
          Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
      linarith
    have hfactorLe : 1 - Real.exp (-(b - a)) ≤ b - a := by
      have h := Real.add_one_le_exp (-(b - a))
      linarith
    have hexpaLe : Real.exp (-a) ≤ 1 := by
      simpa only [← Real.exp_zero] using
        Real.exp_le_exp.mpr (neg_nonpos.mpr ha)
    have hproduct :
        Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤ b - a := by
      calc
        Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤
            1 * (1 - Real.exp (-(b - a))) := by
              exact mul_le_mul_of_nonneg_right hexpaLe hfactor0
        _ ≤ b - a := by simpa using hfactorLe
    have hdiff : Real.exp (-a) - Real.exp (-b) =
        Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
      rw [show -b = -a + (-(b - a)) by ring, Real.exp_add]
      ring
    rw [abs_of_nonneg (sub_nonneg.mpr hexpOrder),
      abs_of_nonpos (sub_nonpos.mpr hab), hdiff]
    simpa [neg_sub] using hproduct
  · have ht : 0 ≤ a - b := sub_nonneg.mpr hba
    have hexpOrder : Real.exp (-a) ≤ Real.exp (-b) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hfactor0 : 0 ≤ 1 - Real.exp (-(a - b)) := by
      have : Real.exp (-(a - b)) ≤ 1 := by
        simpa only [← Real.exp_zero] using
          Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
      linarith
    have hfactorLe : 1 - Real.exp (-(a - b)) ≤ a - b := by
      have h := Real.add_one_le_exp (-(a - b))
      linarith
    have hexpbLe : Real.exp (-b) ≤ 1 := by
      simpa only [← Real.exp_zero] using
        Real.exp_le_exp.mpr (neg_nonpos.mpr hb)
    have hproduct :
        Real.exp (-b) * (1 - Real.exp (-(a - b))) ≤ a - b := by
      calc
        Real.exp (-b) * (1 - Real.exp (-(a - b))) ≤
            1 * (1 - Real.exp (-(a - b))) := by
              exact mul_le_mul_of_nonneg_right hexpbLe hfactor0
        _ ≤ a - b := by simpa using hfactorLe
    have hdiff : Real.exp (-b) - Real.exp (-a) =
        Real.exp (-b) * (1 - Real.exp (-(a - b))) := by
      rw [show -a = -b + (-(a - b)) by ring, Real.exp_add]
      ring
    rw [abs_of_nonpos (sub_nonpos.mpr hexpOrder),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    simpa [neg_sub, hdiff] using hproduct

/-- Pointwise intensity-to-void transfer with no loss in the constant. -/
theorem finiteBetaVoidApproximation_sub_fixed_le_intensity_error
    (m p : ℕ) (x : ℝ) :
    |Real.exp (-finiteCoherenceIntensity m p x) - limitingCoherenceCDF x| ≤
      |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| := by
  unfold limitingCoherenceCDF
  exact abs_exp_neg_sub_exp_neg_le
    (finiteCoherenceIntensity_nonneg m p x)
    (classicalCoherenceIntensity_pos x).le

/-- The explicit finite intensity estimate transfers to the fixed Gumbel
void law with no additional constant. -/
theorem finiteBetaVoidApproximation_sub_fixed_le_compact_rate
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    |Real.exp (-finiteCoherenceIntensity m p x) - limitingCoherenceCDF x| ≤
      compactBetaIntensityConstant M * betaIntensityErrorEnvelope m p := by
  exact (finiteBetaVoidApproximation_sub_fixed_le_intensity_error m p x).trans
    (finiteCoherenceIntensity_sub_fixed_le_compact_rate hcond hpm hx)

/-- Any explicit finite intensity bound transfers verbatim to the fixed
coherence CDF. -/
theorem finiteBetaVoidApproximation_sub_fixed_le_envelope
    {M C : ℝ} (hC : HasBetaIntensityFiniteBound M C)
    {m p : ℕ} (hp : 3 ≤ p) (hpm : p ≤ m) {x : ℝ} (hx : |x| ≤ M) :
    |Real.exp (-finiteCoherenceIntensity m p x) - limitingCoherenceCDF x| ≤
      C * betaIntensityErrorEnvelope m p := by
  exact (finiteBetaVoidApproximation_sub_fixed_le_intensity_error m p x).trans
    (hC m p hp hpm x hx)

/-- The joint exact-intensity approximation can be replaced by the fixed
normal--coherence product at the cost of the *intensity* difference itself.
The exponential step loses no constant. -/
theorem limitingJointError_le_exactIntensity_add_intensityDifference
    (m p : ℕ) (z x : ℝ) :
    limitingJointError m p z x ≤
      exactIntensityJointError m p z x +
        |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| := by
  have htransfer :
      |Real.exp (-finiteCoherenceIntensity m p x) -
          Real.exp (-classicalCoherenceIntensity x)| ≤
        |finiteCoherenceIntensity m p x - classicalCoherenceIntensity x| := by
    simpa [limitingCoherenceCDF] using
      finiteBetaVoidApproximation_sub_fixed_le_intensity_error m p x
  exact (limitingJointError_le_exactIntensity_add_expDifference m p z x).trans
    (add_le_add le_rfl htransfer)

/-- Direct explicit joint transfer: whatever error remains in the
exact-intensity joint approximation is augmented only by the verified
finite Beta rate. -/
theorem limitingJointError_le_exactIntensity_add_compact_rate
    {M : ℝ} {m p : ℕ} {z x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    limitingJointError m p z x ≤
      exactIntensityJointError m p z x +
        compactBetaIntensityConstant M * betaIntensityErrorEnvelope m p := by
  exact (limitingJointError_le_exactIntensity_add_intensityDifference
    m p z x).trans
      (add_le_add le_rfl
        (finiteCoherenceIntensity_sub_fixed_le_compact_rate hcond hpm hx))

/-- Final pointwise assembly with the explicit envelope, conditional only on
the named finite Beta-intensity estimate. -/
theorem limitingJointError_le_exact_add_envelope
    {M C exactErr : ℝ} (hC : HasBetaIntensityFiniteBound M C)
    {m p : ℕ} (hp : 3 ≤ p) (hpm : p ≤ m) {z x : ℝ}
    (hx : |x| ≤ M)
    (hexact : exactIntensityJointError m p z x ≤ exactErr) :
    limitingJointError m p z x ≤
      exactErr + C * betaIntensityErrorEnvelope m p := by
  exact (limitingJointError_le_exactIntensity_add_intensityDifference
    m p z x).trans (add_le_add hexact (hC m p hp hpm x hx))

/-- The already verified all-gap Beta-tail theorem says exactly that the
finite intensity converges to the fixed intensity along every admissible
dimension sequence. -/
theorem tendsto_betaCorrelationIntensity
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦ finiteCoherenceIntensity (mseq p) p x)
      atTop (nhds (classicalCoherenceIntensity x)) := by
  exact allGapBetaTailIntensity mseq hadm x

/-- The explicit envelope tends to zero along every admissible sequence.
This verifies that each of its displayed `m,p` terms vanishes without any
assumption that `p/m` has a limit. -/
theorem tendsto_betaIntensityErrorEnvelope_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦ betaIntensityErrorEnvelope (mseq p) p)
      atTop (nhds 0) := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpR
  have honeDiv : Tendsto (fun p : ℕ ↦ 1 / Real.log (p : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop 1
  have hloglogDiv : Tendsto (fun p : ℕ ↦
      Real.log (Real.log (p : ℝ)) / Real.log (p : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hfirst : Tendsto (fun p : ℕ ↦
      (1 + Real.log (Real.log (p : ℝ))) / Real.log (p : ℝ))
      atTop (nhds 0) := by
    have hadd := honeDiv.add hloglogDiv
    simpa only [zero_add] using hadd.congr'
      (Eventually.of_forall fun _p ↦ by ring)
  have hlogSqDivP : Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) ^ 2 / (p : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp hpR
  have hsecond : Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) ^ 2 / (mseq p : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [hadm] with p hp
      exact div_nonneg (sq_nonneg _)
        (Nat.cast_nonneg (mseq p))
    · filter_upwards [hadm] with p hp
      have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) hp.1
      have hpPos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpN
      have hpm : (p : ℝ) ≤ (mseq p : ℝ) := Nat.cast_le.mpr hp.2
      exact div_le_div_of_nonneg_left (sq_nonneg _) hpPos hpm
    · exact hlogSqDivP
  have hinvP : Tendsto (fun p : ℕ ↦ 1 / (p : ℝ))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  simpa [betaIntensityErrorEnvelope] using
    (hfirst.add hsecond).add hinvP

/-- Consequently the exact finite-intensity void approximation converges to
the fixed coherence law, with no assumption on the limit of `p/m`. -/
theorem tendsto_finiteBetaVoidApproximation
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦ Real.exp (-finiteCoherenceIntensity (mseq p) p x))
      atTop (nhds (limitingCoherenceCDF x)) := by
  unfold limitingCoherenceCDF
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_betaCorrelationIntensity hadm x).neg
  exact h.congr' (Eventually.of_forall fun _p ↦ rfl)

end

end LogdetLean.Coherence
