import LogdetLean.NullWeakCLT
import LogdetLean.ScaleSeparation
import LogdetLean.Coherence.GaussianRetainedPrefixTail
import LogdetLean.Coherence.ModelAndTargets
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
/-!
# A fixed-deletion null CLT

For a fixed `q`, this file removes the first `q - 1` logarithmic beta
factors from the Bartlett log-determinant sum.  The remaining tail is still
centered by its exact mean but is divided by the variance of the *full* sum.
The goal is the all-gap statement that this deleted tail converges weakly to
the standard Gaussian whenever `2 ≤ p ≤ m(p)` eventually.

The proof is deliberately separated into finite exact factorization lemmas,
a deterministic fixed-prefix variance estimate, and a characteristic-function
transfer.  This is the normalization needed by the retained-prefix/tail
factorization in the coherence argument.
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

/-- Law of the logarithmic beta factors with indices strictly larger than
`q`.  Before index `q + 1` the recursion stays at `δ₀`. -/
def deletedLogBetaTailLaw (m q : ℕ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | p + 1 =>
      if q < p + 1 then
        deletedLogBetaTailLaw m q p ∗ logBetaLaw m (p + 1)
      else deletedLogBetaTailLaw m q p

/-- Up to the deletion index the deleted tail is exactly `δ₀`. -/
theorem deletedLogBetaTailLaw_eq_dirac_of_le
    (m q p : ℕ) (hpq : p ≤ q) :
    deletedLogBetaTailLaw m q p = Measure.dirac 0 := by
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [deletedLogBetaTailLaw, if_neg (by omega), ih (by omega)]

set_option linter.style.haveILetI false in
/-- The deleted tail is a probability measure throughout its finite
admissible range. -/
theorem isProbabilityMeasure_deletedLogBetaTailLaw
    {m q p : ℕ} (hq : 1 ≤ q) (hpm : p ≤ m) :
    IsProbabilityMeasure (deletedLogBetaTailLaw m q p) := by
  induction p with
  | zero =>
      rw [deletedLogBetaTailLaw]
      infer_instance
  | succ p ih =>
      rw [deletedLogBetaTailLaw]
      by_cases hqp : q < p + 1
      · rw [if_pos hqp]
        haveI : IsProbabilityMeasure (deletedLogBetaTailLaw m q p) :=
          ih (by omega)
        haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm (by omega)
        infer_instance
      · rw [if_neg hqp]
        exact ih (by omega)

set_option linter.style.haveILetI false in
/-- Exact additive convolution factorization of the full logarithmic beta sum
into the retained prefix through `q` and the deleted tail after `q`. -/
theorem logBetaSumLaw_eq_prefix_conv_deletedTail
    {m q p : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (hpm : p ≤ m) :
    logBetaSumLaw m p =
      logBetaSumLaw m q ∗ deletedLogBetaTailLaw m q p := by
  induction p, hqp using Nat.le_induction with
  | base =>
      haveI : IsProbabilityMeasure (logBetaSumLaw m q) :=
        isProbabilityMeasure_logBetaSumLaw (by omega)
      rw [deletedLogBetaTailLaw_eq_dirac_of_le m q q le_rfl]
      simp
  | succ p hqp ih =>
      have hp2 : 2 ≤ p + 1 := by omega
      have hp1m : p + 1 ≤ m := hpm
      haveI : IsProbabilityMeasure (deletedLogBetaTailLaw m q p) :=
        isProbabilityMeasure_deletedLogBetaTailLaw hq (by omega)
      haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
        isProbabilityMeasure_logBetaLaw hp1m hp2
      rw [logBetaSumLaw, if_pos hp2, deletedLogBetaTailLaw,
        if_pos (by omega), ih (by omega), Measure.conv_assoc]

set_option linter.style.haveILetI false in
/-- The deleted tail has a finite third absolute moment. -/
theorem memLp_id_deletedLogBetaTailLaw
    {m q p : ℕ} (hq : 1 ≤ q) (hpm : p ≤ m) :
    MemLp (fun x : ℝ ↦ x) 3 (deletedLogBetaTailLaw m q p) := by
  induction p with
  | zero =>
      rw [deletedLogBetaTailLaw]
      refine MemLp.of_bound (by fun_prop) 0 ?_
      simp
  | succ p ih =>
      rw [deletedLogBetaTailLaw]
      by_cases hqp : q < p + 1
      · rw [if_pos hqp]
        haveI : IsProbabilityMeasure (deletedLogBetaTailLaw m q p) :=
          isProbabilityMeasure_deletedLogBetaTailLaw hq (by omega)
        haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm (by omega)
        exact memLp_id_conv (ih (by omega))
          (memLp_id_logBetaLaw hpm (by omega))
      · rw [if_neg hqp]
        exact ih (by omega)

/-- Exact mean of the deleted tail, expressed as a difference of the full and
prefix means. -/
def deletedTailCenter (m q p : ℕ) : ℝ :=
  nullCenter m p - nullCenter m q

set_option linter.style.haveILetI false in
/-- The symbolic center above is the actual expectation of the deleted tail. -/
theorem integral_id_deletedLogBetaTailLaw_eq_deletedTailCenter
    {m q p : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (hpm : p ≤ m) :
    ∫ x : ℝ, x ∂deletedLogBetaTailLaw m q p =
      deletedTailCenter m q p := by
  haveI : IsProbabilityMeasure (logBetaSumLaw m q) :=
    isProbabilityMeasure_logBetaSumLaw (hqp.trans hpm)
  haveI : IsProbabilityMeasure (deletedLogBetaTailLaw m q p) :=
    isProbabilityMeasure_deletedLogBetaTailLaw hq hpm
  have hprefix : Integrable (fun x : ℝ ↦ x) (logBetaSumLaw m q) :=
    (memLp_id_logBetaSumLaw (hqp.trans hpm)).integrable (by norm_num)
  have htail : Integrable (fun x : ℝ ↦ x)
      (deletedLogBetaTailLaw m q p) :=
    (memLp_id_deletedLogBetaTailLaw hq hpm).integrable (by norm_num)
  have hmean := integral_id_conv hprefix htail
  rw [← logBetaSumLaw_eq_prefix_conv_deletedTail hq hqp hpm] at hmean
  unfold deletedTailCenter
  unfold nullCenter
  linarith

/-- Exact centered second moment of the deleted tail. -/
def deletedTailVariance (m q p : ℕ) : ℝ :=
  ∫ x, (x - deletedTailCenter m q p) ^ 2
    ∂deletedLogBetaTailLaw m q p

set_option linter.style.haveILetI false in
/-- Variances add across the exact prefix/tail convolution. -/
theorem nullVariance_eq_prefix_add_deletedTailVariance
    {m q p : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (hpm : p ≤ m) :
    nullVariance m p = nullVariance m q + deletedTailVariance m q p := by
  haveI : IsProbabilityMeasure (logBetaSumLaw m q) :=
    isProbabilityMeasure_logBetaSumLaw (hqp.trans hpm)
  haveI : IsProbabilityMeasure (deletedLogBetaTailLaw m q p) :=
    isProbabilityMeasure_deletedLogBetaTailLaw hq hpm
  have hprefix3 := memLp_id_logBetaSumLaw (hqp.trans hpm)
  have htail3 := memLp_id_deletedLogBetaTailLaw hq hpm
  have hvar := integral_centered_sq_conv
    (hprefix3.mono_exponent (by norm_num))
    (htail3.mono_exponent (by norm_num))
  rw [← logBetaSumLaw_eq_prefix_conv_deletedTail hq hqp hpm] at hvar
  rw [integral_id_deletedLogBetaTailLaw_eq_deletedTailCenter hq hqp hpm]
    at hvar
  simpa [nullVariance, nullCenter, deletedTailVariance] using hvar

/-- Deleted tail centered by its exact mean and divided by the standard
deviation of the full `p`-dimensional log-determinant. -/
def standardizedDeletedTailLaw (m q p : ℕ) : Measure ℝ :=
  (deletedLogBetaTailLaw m q p).map
    (fun x ↦ (x - deletedTailCenter m q p) /
      Real.sqrt (nullVariance m p))

set_option linter.style.haveILetI false in
/-- Standardization preserves the probability mass of the deleted tail. -/
theorem isProbabilityMeasure_standardizedDeletedTailLaw
    {m q p : ℕ} (hq : 1 ≤ q) (hpm : p ≤ m) :
    IsProbabilityMeasure (standardizedDeletedTailLaw m q p) := by
  haveI : IsProbabilityMeasure (deletedLogBetaTailLaw m q p) :=
    isProbabilityMeasure_deletedLogBetaTailLaw hq hpm
  unfold standardizedDeletedTailLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The retained prefix, centered by its own exact mean but divided by the
standard deviation of the full `p`-dimensional sum. -/
def standardizedPrefixAtFullScaleLaw (m q p : ℕ) : Measure ℝ :=
  (logBetaSumLaw m q).map
    (fun x ↦ (x - nullCenter m q) / Real.sqrt (nullVariance m p))

set_option linter.style.haveILetI false in
/-- The globally scaled prefix is a probability measure. -/
theorem isProbabilityMeasure_standardizedPrefixAtFullScaleLaw
    {m q p : ℕ} (hqm : q ≤ m) :
    IsProbabilityMeasure (standardizedPrefixAtFullScaleLaw m q p) := by
  haveI : IsProbabilityMeasure (logBetaSumLaw m q) :=
    isProbabilityMeasure_logBetaSumLaw hqm
  unfold standardizedPrefixAtFullScaleLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Characteristic function of a centered and linearly scaled pushforward.
The `1 / s` form is convenient for exact factorization without any positivity
assumption on `s`. -/
theorem charFun_map_sub_div
    (μ : Measure ℝ) (c s t : ℝ) :
    charFun (μ.map (fun x ↦ (x - c) / s)) t =
      charFun μ ((1 / s) * t) *
        Complex.exp (-((((c * ((1 / s) * t) : ℝ) : ℂ) * Complex.I))) := by
  rw [show (fun x : ℝ ↦ (x - c) / s) =
      (fun x ↦ (1 / s) * (x + (-c))) by
    funext x
    ring]
  rw [charFun_map_mul_comp (by fun_prop)]
  rw [charFun_map_add_const]
  simp only [RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast
  ring

set_option linter.style.haveILetI false in
/-- At every finite admissible index, the characteristic function of the full
standardized sum is the product of the globally scaled prefix characteristic
function and the globally scaled deleted-tail characteristic function. -/
theorem charFun_standardizedNullLaw_eq_prefix_mul_deletedTail
    {m q p : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (hpm : p ≤ m) (t : ℝ) :
    charFun (standardizedNullLaw m p) t =
      charFun (standardizedPrefixAtFullScaleLaw m q p) t *
        charFun (standardizedDeletedTailLaw m q p) t := by
  haveI : IsProbabilityMeasure (logBetaSumLaw m q) :=
    isProbabilityMeasure_logBetaSumLaw (hqp.trans hpm)
  haveI : IsProbabilityMeasure (deletedLogBetaTailLaw m q p) :=
    isProbabilityMeasure_deletedLogBetaTailLaw hq hpm
  let u : ℝ := (1 / Real.sqrt (nullVariance m p)) * t
  let A : ℂ := -((((nullCenter m q * u : ℝ) : ℂ) * Complex.I))
  let B : ℂ := -((((deletedTailCenter m q p * u : ℝ) : ℂ) * Complex.I))
  rw [standardizedNullLaw, charFun_map_sub_div,
    standardizedPrefixAtFullScaleLaw, charFun_map_sub_div,
    standardizedDeletedTailLaw, charFun_map_sub_div]
  change charFun (logBetaSumLaw m p) u *
      Complex.exp (-((((nullCenter m p * u : ℝ) : ℂ) * Complex.I))) =
    (charFun (logBetaSumLaw m q) u * Complex.exp A) *
      (charFun (deletedLogBetaTailLaw m q p) u * Complex.exp B)
  rw [logBetaSumLaw_eq_prefix_conv_deletedTail hq hqp hpm, charFun_conv]
  calc
    (charFun (logBetaSumLaw m q) u *
          charFun (deletedLogBetaTailLaw m q p) u) *
        Complex.exp (-((((nullCenter m p * u : ℝ) : ℂ) * Complex.I))) =
      (charFun (logBetaSumLaw m q) u *
          charFun (deletedLogBetaTailLaw m q p) u) *
        (Complex.exp A * Complex.exp B) := by
          rw [← Complex.exp_add]
          congr 2
          unfold A B deletedTailCenter
          push_cast
          ring
    _ = (charFun (logBetaSumLaw m q) u * Complex.exp A) *
        (charFun (deletedLogBetaTailLaw m q p) u * Complex.exp B) := by
          ring

/-- A finite, uniform comparison between a fixed prefix variance and the
variance of the full sum.  The harmless condition `2 q ≤ m` is automatic
for fixed `q` along every admissible sequence indexed by `p → ∞`. -/
theorem nullVSeries_prefix_div_full_le
    {m q p : ℕ} (hq : 2 ≤ q) (hqp : q ≤ p) (hpm : p ≤ m)
    (hlarge : 2 * q ≤ m) :
    nullVSeries m q / nullVSeries m p ≤
      (12 * (q : ℝ) * ((q : ℝ) - 1)) /
        ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hqadm : Admissible m q := ⟨hq, hqp.trans hpm⟩
  have hpadm : Admissible m p := ⟨hq.trans hqp, hpm⟩
  have hmN : 0 < m := by omega
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hP : 0 < (p : ℝ) * ((p : ℝ) - 1) :=
    mul_pos (by positivity) (sub_pos.mpr hpR)
  have hVq : 0 ≤ nullVSeries m q := nullVSeries_nonneg hqadm.2
  have hVp : 0 < nullVSeries m p := nullVSeries_pos hpadm
  have hApos : 0 < nullMinShape m q := nullMinShape_pos hqadm
  have hAone : 1 ≤ nullMinShape m q := by
    unfold nullMinShape betaShapeA
    have hlargeR : (2 : ℝ) * (q : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hlarge
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hm4A : (m : ℝ) ≤ 4 * nullMinShape m q := by
    unfold nullMinShape betaShapeA
    have hlargeR : (2 : ℝ) * (q : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hlarge
    linarith
  have hmSq : (m : ℝ) ^ 2 ≤ 16 * (nullMinShape m q) ^ 2 := by
    have hs := (sq_le_sq₀ hm.le (by positivity :
      0 ≤ 4 * nullMinShape m q)).mpr hm4A
    nlinarith
  have hupper :=
    nullVSeries_le_three_quarters_dimension_div_minShape_sq hqadm hAone
  have hupperCross :
      nullVSeries m q * (4 * (nullMinShape m q) ^ 2) ≤
        3 * (q : ℝ) * ((q : ℝ) - 1) := by
    exact (le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hApos))).mp
      hupper
  have hprefixCross :
      nullVSeries m q * (m : ℝ) ^ 2 ≤
        12 * (q : ℝ) * ((q : ℝ) - 1) := by
    calc
      nullVSeries m q * (m : ℝ) ^ 2 ≤
          nullVSeries m q * (16 * (nullMinShape m q) ^ 2) :=
        mul_le_mul_of_nonneg_left hmSq hVq
      _ = 4 *
          (nullVSeries m q * (4 * (nullMinShape m q) ^ 2)) := by ring
      _ ≤ 4 * (3 * (q : ℝ) * ((q : ℝ) - 1)) := by gcongr
      _ = 12 * (q : ℝ) * ((q : ℝ) - 1) := by ring
  have hlower := nullVSeries_lower_p_mul_pred_div_m_sq hpadm
  have hlowerCross :
      (p : ℝ) * ((p : ℝ) - 1) ≤
        nullVSeries m p * (m : ℝ) ^ 2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hm)).mp hlower
  rw [div_le_div_iff₀ hVp hP]
  calc
    nullVSeries m q * ((p : ℝ) * ((p : ℝ) - 1)) ≤
        nullVSeries m q * (nullVSeries m p * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlowerCross hVq
    _ = nullVSeries m p * (nullVSeries m q * (m : ℝ) ^ 2) := by ring
    _ ≤ nullVSeries m p *
        (12 * (q : ℝ) * ((q : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hprefixCross hVp.le
    _ = (12 * (q : ℝ) * ((q : ℝ) - 1)) * nullVSeries m p := by ring

/-- A fixed prefix carries a vanishing fraction of the full null variance,
uniformly over all eventual admissible sequences `2 ≤ p ≤ m(p)`. -/
theorem tendsto_fixedPrefix_nullVSeries_div_full_zero
    (q : ℕ) (hq : 2 ≤ q) (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p ↦
      nullVSeries (mseq p) q / nullVSeries (mseq p) p)
      atTop (nhds 0) := by
  let C : ℝ := 12 * (q : ℝ) * ((q : ℝ) - 1)
  have hpcast : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpred : Tendsto (fun p : ℕ ↦ (p : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) hpcast)
  have hden : Tendsto (fun p : ℕ ↦
      (p : ℝ) * ((p : ℝ) - 1)) atTop atTop :=
    hpcast.atTop_mul_atTop₀ hpred
  have hupper : Tendsto (fun p : ℕ ↦
      C / ((p : ℝ) * ((p : ℝ) - 1))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  apply squeeze_zero' (g := fun p : ℕ ↦
    C / ((p : ℝ) * ((p : ℝ) - 1)))
  · filter_upwards [hadm, eventually_ge_atTop q] with p hp hpq
    exact div_nonneg (nullVSeries_nonneg (hpq.trans hp.2))
      (nullVSeries_pos hp).le
  · filter_upwards [hadm, eventually_ge_atTop (2 * q)] with p hp hpq
    have hqp : q ≤ p := by omega
    have hlarge : 2 * q ≤ mseq p := hpq.trans hp.2
    simpa [C] using
      nullVSeries_prefix_div_full_le hq hqp hp.2 hlarge
  · exact hupper

set_option linter.style.haveILetI false in
/-- The globally scaled prefix is square-integrable. -/
theorem memLp_id_standardizedPrefixAtFullScaleLaw
    {m q p : ℕ} (hqm : q ≤ m) :
    MemLp (fun x : ℝ ↦ x) 2
      (standardizedPrefixAtFullScaleLaw m q p) := by
  letI : IsProbabilityMeasure (logBetaSumLaw m q) :=
    isProbabilityMeasure_logBetaSumLaw hqm
  have hraw3 : MemLp (fun x : ℝ ↦ x) 3 (logBetaSumLaw m q) :=
    memLp_id_logBetaSumLaw hqm
  have hraw2 : MemLp (fun x : ℝ ↦ x) 2 (logBetaSumLaw m q) :=
    hraw3.mono_exponent (by norm_num)
  have hcenter : MemLp (fun x : ℝ ↦ x - nullCenter m q) 2
      (logBetaSumLaw m q) :=
    hraw2.sub (memLp_const (nullCenter m q))
  have hscaled : MemLp
      (fun x : ℝ ↦ (1 / Real.sqrt (nullVariance m p)) *
        (x - nullCenter m q)) 2 (logBetaSumLaw m q) :=
    hcenter.const_mul _
  unfold standardizedPrefixAtFullScaleLaw
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact MemLp.ae_eq (ae_of_all _ fun x ↦ by
    simp only [Function.comp_apply]
    ring) hscaled

set_option linter.style.haveILetI false in
/-- The exact second moment of the globally scaled prefix is the fixed-prefix
variance divided by the full variance. -/
theorem integral_sq_standardizedPrefixAtFullScaleLaw
    {m q p : ℕ} (hq : 2 ≤ q) (hqp : q ≤ p) (hpm : p ≤ m) :
    ∫ x : ℝ, x ^ 2 ∂standardizedPrefixAtFullScaleLaw m q p =
      nullVSeries m q / nullVSeries m p := by
  have hqadm : Admissible m q := ⟨hq, hqp.trans hpm⟩
  have hpadm : Admissible m p := ⟨hq.trans hqp, hpm⟩
  haveI : IsProbabilityMeasure (logBetaSumLaw m q) :=
    isProbabilityMeasure_logBetaSumLaw hqadm.2
  have hVp : 0 < nullVariance m p := by
    rw [nullVariance_eq_nullVSeries hpm]
    exact nullVSeries_pos hpadm
  unfold standardizedPrefixAtFullScaleLaw
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  have hfun : (fun x : ℝ ↦
      ((x - nullCenter m q) / Real.sqrt (nullVariance m p)) ^ 2) =
      (fun x ↦ (x - nullCenter m q) ^ 2 / nullVariance m p) := by
    funext x
    rw [div_pow, Real.sq_sqrt hVp.le]
  rw [hfun, integral_div]
  change nullVariance m q / nullVariance m p = _
  rw [nullVariance_eq_nullVSeries hqadm.2,
    nullVariance_eq_nullVSeries hpm]

/-- Cauchy--Schwarz in the probability-measure form used below. -/
theorem integral_norm_le_sqrt_integral_sq
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) :
    ∫ x, ‖f x‖ ∂μ ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf
  have hOne : MemLp (fun _ : ℝ ↦ (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_const (1 : ℝ) :
      MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ)
  have h := integral_mul_norm_le_Lp_mul_Lq
    (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    hf' hOne
  simpa [Real.sqrt_eq_rpow] using h

/-- A first-moment Lipschitz bound for a characteristic function at the
origin. -/
theorem norm_charFun_sub_one_le_abs_mul_integral_norm
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (t : ℝ) :
    ‖charFun μ t - 1‖ ≤ |t| * ∫ x : ℝ, |x| ∂μ := by
  have hexp : Integrable
      (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) μ := by
    refine (integrable_const (1 : ℂ)).mono (by fun_prop) ?_
    filter_upwards [] with x
    rw [Complex.norm_exp]
    simp
  have hone : Integrable (fun _ : ℝ ↦ (1 : ℂ)) μ := integrable_const _
  have hbound : Integrable (fun x : ℝ ↦ |t| * |x|) μ :=
    hμ.abs.const_mul _
  rw [charFun_apply_real]
  calc
    ‖(∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂μ) - 1‖ =
        ‖∫ x : ℝ,
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1) ∂μ‖ := by
      rw [integral_sub hexp hone]
      simp
    _ ≤ ∫ x : ℝ, |t| * |x| ∂μ :=
      norm_integral_le_of_norm_le hbound (ae_of_all _ fun x ↦ by
        have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * x)
        simpa [mul_comm, mul_left_comm, abs_mul, Real.norm_eq_abs] using h)
    _ = |t| * ∫ x : ℝ, |x| ∂μ := by rw [integral_const_mul]

set_option linter.style.haveILetI false in
/-- Finite characteristic-function bound for the globally scaled retained
prefix. -/
theorem norm_charFun_prefixAtFullScale_sub_one_le
    {m q p : ℕ} (hq : 2 ≤ q) (hqp : q ≤ p) (hpm : p ≤ m) (t : ℝ) :
    ‖charFun (standardizedPrefixAtFullScaleLaw m q p) t - 1‖ ≤
      |t| * Real.sqrt
        (nullVSeries m q / nullVSeries m p) := by
  letI : IsProbabilityMeasure
      (standardizedPrefixAtFullScaleLaw m q p) :=
    isProbabilityMeasure_standardizedPrefixAtFullScaleLaw (hqp.trans hpm)
  have hLp := memLp_id_standardizedPrefixAtFullScaleLaw
    (p := p) (hqp.trans hpm)
  have hL1 : Integrable (fun x : ℝ ↦ x)
      (standardizedPrefixAtFullScaleLaw m q p) :=
    hLp.integrable (by norm_num)
  calc
    ‖charFun (standardizedPrefixAtFullScaleLaw m q p) t - 1‖ ≤
        |t| * ∫ x : ℝ, |x|
          ∂standardizedPrefixAtFullScaleLaw m q p :=
      norm_charFun_sub_one_le_abs_mul_integral_norm hL1 t
    _ ≤ |t| * Real.sqrt
        (∫ x : ℝ, ‖x‖ ^ 2
          ∂standardizedPrefixAtFullScaleLaw m q p) := by
      gcongr
      simpa [Real.norm_eq_abs] using integral_norm_le_sqrt_integral_sq hLp
    _ = |t| * Real.sqrt
        (nullVSeries m q / nullVSeries m p) := by
      simp only [Real.norm_eq_abs, sq_abs]
      rw [integral_sq_standardizedPrefixAtFullScaleLaw hq hqp hpm]

/-- The globally scaled fixed prefix converges to zero in characteristic
function, uniformly over the all-gap admissible domain. -/
theorem tendsto_charFun_standardizedPrefixAtFullScaleLaw_one
    (q : ℕ) (hq : 2 ≤ q) (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (t : ℝ) :
    Tendsto (fun p ↦
      charFun (standardizedPrefixAtFullScaleLaw (mseq p) q p) t)
      atTop (nhds 1) := by
  have hratio :=
    tendsto_fixedPrefix_nullVSeries_div_full_zero q hq mseq hadm
  have hsqrt : Tendsto (fun p ↦ Real.sqrt
      (nullVSeries (mseq p) q / nullVSeries (mseq p) p))
      atTop (nhds 0) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hratio using 1 <;>
      simp [Function.comp_def]
  have hupper : Tendsto (fun p ↦ |t| * Real.sqrt
      (nullVSeries (mseq p) q / nullVSeries (mseq p) p))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hsqrt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (g := fun p ↦ |t| * Real.sqrt
    (nullVSeries (mseq p) q / nullVSeries (mseq p) p))
  · exact Eventually.of_forall fun p ↦ norm_nonneg _
  · filter_upwards [hadm, eventually_ge_atTop q] with p hp hpq
    exact norm_charFun_prefixAtFullScale_sub_one_le hq hpq hp.2 t
  · exact hupper

/-- Fixed-frequency Gaussian limit for the centered deleted tail in the
normalization of the full log-determinant. -/
theorem tendsto_charFun_standardizedDeletedTailLaw_fixed_frequency
    (q : ℕ) (hq : 2 ≤ q) (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (t : ℝ) :
    Tendsto (fun p ↦
      charFun (standardizedDeletedTailLaw (mseq p) q p) t)
      atTop (nhds (Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)))) := by
  have hfull :=
    tendsto_charFun_standardizedNullLaw_fixed_frequency mseq hadm t
  have hprefix :=
    tendsto_charFun_standardizedPrefixAtFullScaleLaw_one q hq mseq hadm t
  have hquot : Tendsto (fun p ↦
      charFun (standardizedNullLaw (mseq p) p) t /
        charFun (standardizedPrefixAtFullScaleLaw (mseq p) q p) t)
      atTop (nhds (Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)))) := by
    have hquotRaw := hfull.div hprefix (by norm_num : (1 : ℂ) ≠ 0)
    change Tendsto (fun p ↦
      charFun (standardizedNullLaw (mseq p) p) t /
        charFun (standardizedPrefixAtFullScaleLaw (mseq p) q p) t)
      atTop (nhds (Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) / 1)) at hquotRaw
    simpa using hquotRaw
  have hne : ∀ᶠ p in atTop,
      charFun (standardizedPrefixAtFullScaleLaw (mseq p) q p) t ≠ 0 :=
    hprefix.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  apply hquot.congr'
  filter_upwards [hadm, eventually_ge_atTop q, hne] with p hp hpq hnep
  have hfactor := charFun_standardizedNullLaw_eq_prefix_mul_deletedTail
    (m := mseq p) (q := q) (p := p) (by omega) hpq hp.2 t
  rw [hfactor]
  exact mul_div_cancel_left₀ _ hnep

/-- Total measure wrapper for the deleted tail.  The Gaussian fallback only
affects the finitely many indices before `q ≤ p ≤ m(p)` holds. -/
def standardizedDeletedTailMeasureOrGaussian (m q p : ℕ) : Measure ℝ := by
  classical
  exact if 2 ≤ q ∧ q ≤ p ∧ p ≤ m then standardizedDeletedTailLaw m q p
    else gaussianReal 0 1

theorem standardizedDeletedTailMeasureOrGaussian_isProbability
    (m q p : ℕ) :
    IsProbabilityMeasure (standardizedDeletedTailMeasureOrGaussian m q p) := by
  classical
  unfold standardizedDeletedTailMeasureOrGaussian
  by_cases h : 2 ≤ q ∧ q ≤ p ∧ p ≤ m
  · rw [if_pos h]
    exact isProbabilityMeasure_standardizedDeletedTailLaw (by omega) h.2.2
  · rw [if_neg h]
    infer_instance

/-- Probability-measure wrapper for the deleted tail. -/
def standardizedDeletedTailProbabilityMeasureOrGaussian (m q p : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨standardizedDeletedTailMeasureOrGaussian m q p,
    standardizedDeletedTailMeasureOrGaussian_isProbability m q p⟩

/-- Fixed-deletion weak CLT, indexed by dimension `p` and valid uniformly over
the entire eventual domain `2 ≤ p ≤ m(p)`. -/
theorem tendsto_standardizedDeletedTailProbabilityMeasureOrGaussian
    (q : ℕ) (hq : 2 ≤ q) (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto
      (fun p ↦ standardizedDeletedTailProbabilityMeasureOrGaussian
        (mseq p) q p)
      atTop (nhds (⟨gaussianReal 0 1, inferInstance⟩ :
        ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hcf :=
    tendsto_charFun_standardizedDeletedTailLaw_fixed_frequency
      q hq mseq hadm t
  change Tendsto
    (fun p ↦ charFun
      (standardizedDeletedTailProbabilityMeasureOrGaussian
        (mseq p) q p : Measure ℝ) t)
    atTop (nhds (charFun (gaussianReal 0 1) t))
  have hgauss : charFun (gaussianReal 0 1) t =
      Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [charFun_gaussianReal]
    congr 1
    push_cast
    ring
  rw [hgauss]
  apply hcf.congr'
  filter_upwards [hadm, eventually_ge_atTop q] with p hp hpq
  change charFun (standardizedDeletedTailLaw (mseq p) q p) t =
    charFun (standardizedDeletedTailMeasureOrGaussian (mseq p) q p) t
  rw [standardizedDeletedTailMeasureOrGaussian, if_pos ⟨hq, hpq, hp.2⟩]

/-! ## Direct retained-prefix product formulation -/

/-- Sum of the logarithms of the `r` tail coordinates while ignoring the
retained prefix. -/
def retainedTailLogSum {α : Type} (q : ℕ) :
    (r : ℕ) → RetainedPrefixTailTuple α ℝ q r → ℝ
  | 0, _ => 0
  | r + 1, z => retainedTailLogSum q r z.1 + Real.log z.2

/-- Measurability of the retained-tail logarithmic sum. -/
theorem measurable_retainedTailLogSum
    {α : Type} [MeasurableSpace α] (q : ℕ) :
    ∀ r, Measurable (retainedTailLogSum (α := α) q r) := by
  intro r
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
      exact (ih.comp measurable_fst).add (Real.measurable_log.comp measurable_snd)

/-- Mapping a sum on a product measure is additive convolution of the two
pushforwards. -/
theorem map_add_prod_eq_conv_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α → ℝ) (g : β → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measure.map (fun z : α × β ↦ f z.1 + g z.2) (μ.prod ν) =
      Measure.map f μ ∗ Measure.map g ν := by
  unfold Measure.conv
  calc
    Measure.map (fun z : α × β ↦ f z.1 + g z.2) (μ.prod ν) =
        Measure.map ((fun z : ℝ × ℝ ↦ z.1 + z.2) ∘ Prod.map f g)
          (μ.prod ν) := by rfl
    _ = Measure.map (fun z : ℝ × ℝ ↦ z.1 + z.2)
          (Measure.map (Prod.map f g) (μ.prod ν)) :=
      (Measure.map_map (measurable_fst.add measurable_snd)
        (hf.prodMap hg)).symm
    _ = Measure.map (fun z : ℝ × ℝ ↦ z.1 + z.2)
          ((Measure.map f μ).prod (Measure.map g ν)) := by
      rw [Measure.map_prod_map μ ν hf hg]

/-- Logarithmic pushforward of every noninitial Gaussian Gram--Schmidt factor
in the indexing used by the deleted tail. -/
theorem map_log_gaussianGramSchmidtFactorMeasure_eq_logBetaLaw_of_pos
    {m n : ℕ} (hn : 1 ≤ n) (hnm : n < m) :
    Measure.map Real.log (gaussianGramSchmidtFactorMeasure m n) =
      logBetaLaw m (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa [Nat.add_assoc] using
    (map_log_gaussianGramSchmidtFactorMeasure_eq_logBetaLaw
      (m := m) (n := k) (by omega : k + 2 ≤ m))

/-- Under the retained-prefix product measure, the tail log sum has exactly
the deleted logarithmic beta law. -/
theorem map_retainedTailLogSum_eq_deletedLogBetaTailLaw
    (m q r : ℕ) (hq : 1 ≤ q) (hqr : q + r ≤ m) :
    Measure.map (retainedTailLogSum
        (α := centeredSubspace (m + 1)) q r)
      (retainedPrefixTailProductMeasure
        (stdGaussian (centeredSubspace (m + 1)))
        (gaussianGramSchmidtFactorMeasure m) q r) =
      deletedLogBetaTailLaw m q (q + r) := by
  induction r with
  | zero =>
      rw [deletedLogBetaTailLaw_eq_dirac_of_le m q (q + 0) (by omega)]
      simp [retainedTailLogSum, retainedPrefixTailProductMeasure]
  | succ r ih =>
      change Measure.map
          (fun z => retainedTailLogSum
              (α := centeredSubspace (m + 1)) q r z.1 + Real.log z.2)
          ((retainedPrefixTailProductMeasure
              (stdGaussian (centeredSubspace (m + 1)))
              (gaussianGramSchmidtFactorMeasure m) q r).prod
            (gaussianGramSchmidtFactorMeasure m (q + r))) = _
      rw [map_add_prod_eq_conv_map _ _ _ _
        (measurable_retainedTailLogSum
          (α := centeredSubspace (m + 1)) q r) Real.measurable_log]
      rw [ih (by omega)]
      rw [map_log_gaussianGramSchmidtFactorMeasure_eq_logBetaLaw_of_pos
        (by omega) (by omega)]
      rw [show q + (r + 1) = (q + r) + 1 by omega]
      change deletedLogBetaTailLaw m q (q + r) ∗
          logBetaLaw m (q + r + 1) =
        (if q < q + r + 1 then
          deletedLogBetaTailLaw m q (q + r) ∗
            logBetaLaw m (q + r + 1)
        else deletedLogBetaTailLaw m q (q + r))
      rw [if_pos (by omega)]

/-- Standardized retained-tail statistic on the exact product space. -/
def standardizedRetainedTailLogStatistic (m q r : ℕ) :
    RetainedPrefixTailTuple (centeredSubspace (m + 1)) ℝ q r → ℝ :=
  fun z ↦ (retainedTailLogSum q r z - deletedTailCenter m q (q + r)) /
    Real.sqrt (nullVariance m (q + r))

/-- Measurability of the standardized retained-tail statistic. -/
theorem measurable_standardizedRetainedTailLogStatistic (m q r : ℕ) :
    Measurable (standardizedRetainedTailLogStatistic m q r) := by
  unfold standardizedRetainedTailLogStatistic
  exact ((measurable_retainedTailLogSum
    (α := centeredSubspace (m + 1)) q r).sub measurable_const).div_const _

/-- Its map under the retained-prefix product measure is exactly the
standardized deleted-tail law.  This is the form directly usable after
conditioning on any event measurable with respect to the retained prefix. -/
theorem map_standardizedRetainedTailLogStatistic_eq_deletedTailLaw
    (m q r : ℕ) (hq : 1 ≤ q) (hqr : q + r ≤ m) :
    Measure.map (standardizedRetainedTailLogStatistic m q r)
      (retainedPrefixTailProductMeasure
        (stdGaussian (centeredSubspace (m + 1)))
        (gaussianGramSchmidtFactorMeasure m) q r) =
      standardizedDeletedTailLaw m q (q + r) := by
  unfold standardizedRetainedTailLogStatistic standardizedDeletedTailLaw
  rw [show (fun z : RetainedPrefixTailTuple
      (centeredSubspace (m + 1)) ℝ q r ↦
        (retainedTailLogSum q r z - deletedTailCenter m q (q + r)) /
          Real.sqrt (nullVariance m (q + r))) =
      (fun x : ℝ ↦
        (x - deletedTailCenter m q (q + r)) /
          Real.sqrt (nullVariance m (q + r))) ∘ retainedTailLogSum q r by rfl]
  rw [← Measure.map_map (by fun_prop)
    (measurable_retainedTailLogSum
      (α := centeredSubspace (m + 1)) q r)]
  rw [map_retainedTailLogSum_eq_deletedLogBetaTailLaw m q r hq hqr]

/-- The corresponding statistic on the original `m+1`-observation Gaussian
columns: first center and retain `q` columns, then use only the independent
tail factors. -/
def standardizedGaussianRetainedTailStatistic (m q r : ℕ) :
    NestedTuple (ObservationSpace (m + 1)) (q + r) → ℝ :=
  standardizedRetainedTailLogStatistic m q r ∘
    centeredRetainedPrefixTailFactors (m + 1) q r

/-- Exact Gaussian-space law of the retained-prefix tail statistic. -/
theorem map_standardizedGaussianRetainedTailStatistic_eq_deletedTailLaw
    (m q r : ℕ) (hq : 1 ≤ q) (hqr : q + r ≤ m) :
    Measure.map (standardizedGaussianRetainedTailStatistic m q r)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r)) =
      standardizedDeletedTailLaw m q (q + r) := by
  unfold standardizedGaussianRetainedTailStatistic
  rw [← Measure.map_map
    (measurable_standardizedRetainedTailLogStatistic m q r)
    (measurable_centeredRetainedPrefixTailFactors (m + 1) q r)]
  rw [map_centeredRetainedPrefixTailFactors_succ_eq_product m q r hqr]
  exact map_standardizedRetainedTailLogStatistic_eq_deletedTailLaw
    m q r hq hqr

end

end LogdetLean.Coherence
