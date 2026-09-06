import LogdetLean.GeneralRPairLaplace
import LogdetLean.FrullaniLogCovarianceLimit
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology Interval

noncomputable section

namespace LogdetLean.GeneralRDecomposition

variable {m p : ℕ}

def laplaceQIntegrand (R : CorrelationMatrix p) (i : Fin p)
    (s : ℝ) (z : GaussianData m p) : ℝ :=
  s⁻¹ * Real.exp (-s * Q R z i)

def laplaceQIntegral (eps T : ℝ) (R : CorrelationMatrix p) (i : Fin p)
    (z : GaussianData m p) : ℝ :=
  ∫ s in eps..T, laplaceQIntegrand R i s z

@[fun_prop]
lemma measurable_laplaceQIntegrand (R : CorrelationMatrix p) (i : Fin p) :
    Measurable (Function.uncurry (laplaceQIntegrand (m := m) R i)) := by
  unfold laplaceQIntegrand Function.uncurry
  exact measurable_fst.inv.mul
    ((measurable_fst.neg.mul ((measurable_Q R i).comp measurable_snd)).exp)

lemma integrable_laplaceQIntegrand_prod {eps T : ℝ} (heps : 0 < eps)
    (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i : Fin p) :
    Integrable (Function.uncurry (laplaceQIntegrand (m := m) R i))
      ((volume.restrict (uIoc eps T)).prod
        (standardGaussianDataMeasure m p)) := by
  simp only [uIoc_of_le hT]
  apply Integrable.of_bound
    (measurable_laplaceQIntegrand (m := m) R i).aestronglyMeasurable
    eps⁻¹
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le
    (measurable_laplaceQIntegrand (m := m) R i).norm measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  filter_upwards [] with z
  have hsge : eps ≤ s := hs.1.le
  have hspos : 0 < s := heps.trans_le hsge
  have hQ : 0 ≤ Q R z i := by unfold Q; positivity
  rw [Function.uncurry_apply_pair, laplaceQIntegrand, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hspos.le)
      (Real.exp_pos _).le)]
  calc
    s⁻¹ * Real.exp (-s * Q R z i) ≤ s⁻¹ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hspos.le) hQ))
        (inv_nonneg.mpr hspos.le)
    _ ≤ eps⁻¹ := by
      simpa using inv_anti₀ heps hsge

lemma intervalIntegrable_laplaceQIntegrand {eps T : ℝ} (heps : 0 < eps)
    (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i : Fin p) (z : GaussianData m p) :
    IntervalIntegrable (fun s ↦ laplaceQIntegrand R i s z) volume eps T := by
  apply ContinuousOn.intervalIntegrable
  unfold laplaceQIntegrand
  apply ContinuousOn.mul
  · apply continuousOn_inv₀.mono
    intro s hs
    have hs' : s ∈ Icc eps T := by
      simpa only [uIcc_of_le hT] using hs
    have hsge : eps ≤ s := hs'.1
    exact (heps.trans_le hsge).ne'
  · exact Continuous.continuousOn (by fun_prop)

lemma frullaniLogTrunc_Q_eq_const_sub_laplaceQIntegral
    {eps T : ℝ} (heps : 0 < eps) (hT : eps ≤ T)
    (R : CorrelationMatrix p)
    (i : Fin p) (z : GaussianData m p) :
    frullaniLogTrunc eps T (Q R z i) =
      (∫ s in eps..T, s⁻¹ * Real.exp (-s)) -
        laplaceQIntegral eps T R i z := by
  have hf : IntervalIntegrable (fun s : ℝ ↦ s⁻¹ * Real.exp (-s))
      volume eps T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · apply continuousOn_inv₀.mono
      intro s hs
      have hs' : s ∈ Icc eps T := by
        simpa only [uIcc_of_le hT] using hs
      have hsge : eps ≤ s := hs'.1
      exact (heps.trans_le hsge).ne'
    · fun_prop
  have hg : IntervalIntegrable
      (fun s : ℝ ↦ s⁻¹ * Real.exp (-Q R z i * s)) volume eps T := by
    simpa [laplaceQIntegrand, mul_comm] using
      intervalIntegrable_laplaceQIntegrand heps hT R i z
  calc
    frullaniLogTrunc eps T (Q R z i) =
        ∫ s in eps..T,
          (s⁻¹ * Real.exp (-s) - s⁻¹ * Real.exp (-Q R z i * s)) := by
      simp [frullaniLogTrunc, mul_sub]
    _ = (∫ s in eps..T, s⁻¹ * Real.exp (-s)) -
        ∫ s in eps..T, s⁻¹ * Real.exp (-Q R z i * s) :=
      intervalIntegral.integral_sub hf hg
    _ = (∫ s in eps..T, s⁻¹ * Real.exp (-s)) -
        laplaceQIntegral eps T R i z := by
      simp [laplaceQIntegral, laplaceQIntegrand, mul_comm]

lemma abs_laplaceQIntegrand_le_inv_eps {eps s : ℝ} (heps : 0 < eps)
    (hs : eps ≤ s) (R : CorrelationMatrix p) (i : Fin p)
    (z : GaussianData m p) :
    |laplaceQIntegrand R i s z| ≤ eps⁻¹ := by
  have hspos : 0 < s := heps.trans_le hs
  have hQ : 0 ≤ Q R z i := by unfold Q; positivity
  rw [laplaceQIntegrand,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hspos.le)
      (Real.exp_pos _).le)]
  calc
    s⁻¹ * Real.exp (-s * Q R z i) ≤ s⁻¹ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hspos.le) hQ))
        (inv_nonneg.mpr hspos.le)
    _ ≤ eps⁻¹ := by simpa using inv_anti₀ heps hs

lemma abs_laplaceQIntegral_le {eps T : ℝ} (heps : 0 < eps)
    (hT : eps ≤ T) (R : CorrelationMatrix p) (i : Fin p)
    (z : GaussianData m p) :
    |laplaceQIntegral eps T R i z| ≤ eps⁻¹ * (T - eps) := by
  rw [laplaceQIntegral, ← Real.norm_eq_abs]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s ↦ laplaceQIntegrand R i s z) (C := eps⁻¹) (a := eps) (b := T)
    (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      have hs' : s ∈ Ioc eps T := by simpa only [uIoc_of_le hT] using hs
      exact abs_laplaceQIntegrand_le_inv_eps heps hs'.1.le R i z)
  simpa [abs_of_nonneg (sub_nonneg.mpr hT)] using hbound

@[fun_prop]
lemma measurable_laplaceQIntegral {eps T : ℝ} (heps : 0 < eps)
    (hT : eps ≤ T) (R : CorrelationMatrix p) (i : Fin p) :
    Measurable (laplaceQIntegral (m := m) eps T R i) := by
  let c := ∫ s in eps..T, s⁻¹ * Real.exp (-s)
  have hfun : laplaceQIntegral (m := m) eps T R i =
      fun z ↦ c - frullaniLogTrunc eps T (Q R z i) := by
    funext z
    have h := frullaniLogTrunc_Q_eq_const_sub_laplaceQIntegral
      (m := m) heps hT R i z
    dsimp only [c]
    linarith
  rw [hfun]
  exact measurable_const.sub
    ((measurable_frullaniLogTrunc eps T).comp (measurable_Q R i))

lemma integrable_laplaceQIntegrand_mul_bounded_prod
    {eps T C : ℝ} (heps : 0 < eps) (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i : Fin p)
    (H : GaussianData m p → ℝ) (hH : Measurable H)
    (hC : ∀ z, |H z| ≤ C) :
    Integrable (Function.uncurry (fun s z ↦
      laplaceQIntegrand R i s z * H z))
      ((volume.restrict (uIoc eps T)).prod
        (standardGaussianDataMeasure m p)) := by
  simp only [uIoc_of_le hT]
  apply Integrable.of_bound
    (((measurable_laplaceQIntegrand (m := m) R i).mul
      (hH.comp measurable_snd)).aestronglyMeasurable)
    (eps⁻¹ * C)
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le
    ((measurable_laplaceQIntegrand (m := m) R i).mul
      (hH.comp measurable_snd)).norm measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  filter_upwards [] with z
  change |laplaceQIntegrand R i s z * H z| ≤ eps⁻¹ * C
  rw [abs_mul]
  exact mul_le_mul (abs_laplaceQIntegrand_le_inv_eps heps hs.1.le R i z)
    (hC z) (abs_nonneg _) (inv_nonneg.mpr heps.le)

lemma integrable_laplaceQIntegrand_mul_laplaceQIntegral_prod
    {eps T : ℝ} (heps : 0 < eps) (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i j : Fin p) :
    Integrable (Function.uncurry (fun s z ↦
      laplaceQIntegrand R i s z * laplaceQIntegral eps T R j z))
      ((volume.restrict (uIoc eps T)).prod
        (standardGaussianDataMeasure m p)) := by
  exact integrable_laplaceQIntegrand_mul_bounded_prod heps hT R i
    (laplaceQIntegral eps T R j)
    (measurable_laplaceQIntegral heps hT R j)
    (fun z ↦ abs_laplaceQIntegral_le heps hT R j z)

lemma integral_laplaceQIntegral_mul_eq_double
    {eps T : ℝ} (heps : 0 < eps) (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i j : Fin p) :
    ∫ z, laplaceQIntegral eps T R i z * laplaceQIntegral eps T R j z
        ∂standardGaussianDataMeasure m p =
      ∫ s in eps..T, ∫ t in eps..T,
        ∫ z, laplaceQIntegrand R i s z * laplaceQIntegrand R j t z
          ∂standardGaussianDataMeasure m p := by
  let μ := standardGaussianDataMeasure m p
  calc
    ∫ z, laplaceQIntegral eps T R i z * laplaceQIntegral eps T R j z ∂μ =
        ∫ z, (∫ s in eps..T, laplaceQIntegrand R i s z *
          laplaceQIntegral eps T R j z) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [laplaceQIntegral, intervalIntegral.integral_mul_const]
    _ = ∫ s in eps..T, ∫ z, laplaceQIntegrand R i s z *
        laplaceQIntegral eps T R j z ∂μ := by
      exact (intervalIntegral_integral_swap
        (integrable_laplaceQIntegrand_mul_laplaceQIntegral_prod
          heps hT R i j)).symm
    _ = ∫ s in eps..T, ∫ t in eps..T,
        ∫ z, laplaceQIntegrand R i s z * laplaceQIntegrand R j t z ∂μ := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc eps T := by simpa only [uIcc_of_le hT] using hs
      calc
        ∫ z, laplaceQIntegrand R i s z * laplaceQIntegral eps T R j z ∂μ =
            ∫ z, (∫ t in eps..T, laplaceQIntegrand R i s z *
              laplaceQIntegrand R j t z) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [laplaceQIntegral, intervalIntegral.integral_const_mul]
        _ = ∫ t in eps..T, ∫ z,
            laplaceQIntegrand R i s z * laplaceQIntegrand R j t z ∂μ := by
          simpa only [mul_comm] using (intervalIntegral_integral_swap
            (integrable_laplaceQIntegrand_mul_bounded_prod heps hT R j
              (fun z ↦ laplaceQIntegrand R i s z)
              ((measurable_laplaceQIntegrand (m := m) R i).comp
                (measurable_const.prodMk measurable_id))
              (fun z ↦ abs_laplaceQIntegrand_le_inv_eps heps hs'.1 R i z))).symm

lemma memLp_laplaceQIntegral_two {eps T : ℝ} (heps : 0 < eps)
    (hT : eps ≤ T) (R : CorrelationMatrix p) (i : Fin p) :
    MemLp (laplaceQIntegral (m := m) eps T R i) 2
      (standardGaussianDataMeasure m p) := by
  apply MemLp.of_bound
    (measurable_laplaceQIntegral heps hT R i).aestronglyMeasurable
    (eps⁻¹ * (T - eps))
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  exact abs_laplaceQIntegral_le heps hT R i z

lemma integral_laplaceQIntegral_eq_intervalIntegral
    {eps T : ℝ} (heps : 0 < eps) (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, laplaceQIntegral eps T R i z
        ∂standardGaussianDataMeasure m p =
      ∫ s in eps..T, ∫ z, laplaceQIntegrand R i s z
        ∂standardGaussianDataMeasure m p := by
  exact (intervalIntegral_integral_swap
    (integrable_laplaceQIntegrand_prod heps hT R i)).symm

def pairLaplaceValue (m : ℕ) (rho s t : ℝ) : ℝ :=
  (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) - 4 * rho ^ 2 * s * t))⁻¹ ^ m

def marginalLaplaceValue (m : ℕ) (s : ℝ) : ℝ :=
  (Real.sqrt (1 + 2 * s))⁻¹ ^ m

def weightedPairLaplace (m : ℕ) (rho s t : ℝ) : ℝ :=
  s⁻¹ * t⁻¹ * pairLaplaceValue m rho s t

def weightedMarginalProduct (m : ℕ) (s t : ℝ) : ℝ :=
  s⁻¹ * t⁻¹ *
    (marginalLaplaceValue m s * marginalLaplaceValue m t)

def weightedPairCovarianceKernel (m : ℕ) (rho s t : ℝ) : ℝ :=
  weightedPairLaplace m rho s t - weightedMarginalProduct m s t

lemma integral_laplaceQIntegrand_eq_marginalLaplaceValue
    (R : CorrelationMatrix p) (i : Fin p) {s : ℝ} (hs : 0 ≤ s) :
    ∫ z, laplaceQIntegrand R i s z
        ∂standardGaussianDataMeasure m p =
      s⁻¹ * marginalLaplaceValue m s := by
  change (∫ z, s⁻¹ * Real.exp (-s * Q R z i)
    ∂standardGaussianDataMeasure m p) = _
  rw [integral_const_mul]
  have h := integral_exp_Q_pair_laplace (m := m) R i i s 0 hs (le_refl 0)
  simp only [zero_mul, sub_zero, R.apply_self] at h
  simpa [marginalLaplaceValue] using congrArg (fun x ↦ s⁻¹ * x) h

lemma integral_laplaceQIntegrand_mul_eq_weightedPairLaplace
    (R : CorrelationMatrix p) (i j : Fin p) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ z, laplaceQIntegrand R i s z * laplaceQIntegrand R j t z
        ∂standardGaussianDataMeasure m p =
      weightedPairLaplace m (R.val i j) s t := by
  have hpoint : (fun z : GaussianData m p ↦
      laplaceQIntegrand R i s z * laplaceQIntegrand R j t z) =
      fun z ↦ (s⁻¹ * t⁻¹) *
        Real.exp (-s * Q R z i - t * Q R z j) := by
    funext z
    unfold laplaceQIntegrand
    calc
      s⁻¹ * Real.exp (-s * Q R z i) *
          (t⁻¹ * Real.exp (-t * Q R z j)) =
          (s⁻¹ * t⁻¹) *
            (Real.exp (-s * Q R z i) * Real.exp (-t * Q R z j)) := by ring
      _ = (s⁻¹ * t⁻¹) *
          Real.exp (-s * Q R z i - t * Q R z j) := by
        rw [← Real.exp_add]
        congr 2
        ring
  rw [hpoint, integral_const_mul,
    integral_exp_Q_pair_laplace R i j s t hs ht]
  rfl

lemma product_intervalIntegral_marginals_eq_double
    {eps T : ℝ} (R : CorrelationMatrix p) (i j : Fin p) :
    (∫ s in eps..T, ∫ z, laplaceQIntegrand R i s z
      ∂standardGaussianDataMeasure m p) *
      (∫ t in eps..T, ∫ z, laplaceQIntegrand R j t z
      ∂standardGaussianDataMeasure m p) =
    ∫ s in eps..T, ∫ t in eps..T,
      (∫ z, laplaceQIntegrand R i s z
        ∂standardGaussianDataMeasure m p) *
      (∫ z, laplaceQIntegrand R j t z
        ∂standardGaussianDataMeasure m p) := by
  simp only [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const]

lemma covariance_laplaceQIntegral_eq_double_kernel_difference
    {eps T : ℝ} (heps : 0 < eps) (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i j : Fin p) :
    cov[laplaceQIntegral (m := m) eps T R i,
        laplaceQIntegral (m := m) eps T R j;
        standardGaussianDataMeasure m p] =
      (∫ s in eps..T, ∫ t in eps..T,
        weightedPairLaplace m (R.val i j) s t) -
      (∫ s in eps..T, ∫ t in eps..T,
        weightedMarginalProduct m s t) := by
  rw [covariance_eq_sub
    (memLp_laplaceQIntegral_two heps hT R i)
    (memLp_laplaceQIntegral_two heps hT R j)]
  change (∫ z, laplaceQIntegral eps T R i z * laplaceQIntegral eps T R j z
      ∂standardGaussianDataMeasure m p) -
    (∫ z, laplaceQIntegral eps T R i z
      ∂standardGaussianDataMeasure m p) *
    (∫ z, laplaceQIntegral eps T R j z
      ∂standardGaussianDataMeasure m p) = _
  rw [integral_laplaceQIntegral_mul_eq_double heps hT R i j]
  rw [integral_laplaceQIntegral_eq_intervalIntegral heps hT R i,
    integral_laplaceQIntegral_eq_intervalIntegral heps hT R j]
  rw [product_intervalIntegral_marginals_eq_double R i j]
  congr 1
  · apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := by
      have : s ∈ Icc eps T := by simpa only [uIcc_of_le hT] using hs
      exact heps.le.trans this.1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : 0 ≤ t := by
      have : t ∈ Icc eps T := by simpa only [uIcc_of_le hT] using ht
      exact heps.le.trans this.1
    exact integral_laplaceQIntegrand_mul_eq_weightedPairLaplace
      R i j hs' ht'
  · apply intervalIntegral.integral_congr
    intro s hs
    have hs' : 0 ≤ s := by
      have : s ∈ Icc eps T := by simpa only [uIcc_of_le hT] using hs
      exact heps.le.trans this.1
    change (∫ t in eps..T,
      (∫ z, laplaceQIntegrand R i s z
        ∂standardGaussianDataMeasure m p) *
      (∫ z, laplaceQIntegrand R j t z
        ∂standardGaussianDataMeasure m p)) =
      ∫ t in eps..T, weightedMarginalProduct m s t
    rw [integral_laplaceQIntegrand_eq_marginalLaplaceValue R i hs']
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : 0 ≤ t := by
      have : t ∈ Icc eps T := by simpa only [uIcc_of_le hT] using ht
      exact heps.le.trans this.1
    change (s⁻¹ * marginalLaplaceValue m s) *
      (∫ z, laplaceQIntegrand R j t z
        ∂standardGaussianDataMeasure m p) = _
    rw [show (∫ z, laplaceQIntegrand R j t z
        ∂standardGaussianDataMeasure m p) =
        t⁻¹ * marginalLaplaceValue m t from
        integral_laplaceQIntegrand_eq_marginalLaplaceValue R j ht']
    simp [weightedMarginalProduct]
    ring

lemma pairLaplace_discriminant_pos {rho s t : ℝ} (hrho : |rho| ≤ 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 < (1 + 2 * s) * (1 + 2 * t) - 4 * rho ^ 2 * s * t := by
  have hrho2 : rho ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one rho).2 hrho
  have hst : 0 ≤ s * t := mul_nonneg hs ht
  calc
    0 < 1 + 2 * s + 2 * t + 4 * (1 - rho ^ 2) * (s * t) := by positivity
    _ = (1 + 2 * s) * (1 + 2 * t) - 4 * rho ^ 2 * s * t := by ring

lemma continuousOn_weightedPairLaplace_Icc {rho eps T : ℝ}
    (hrho : |rho| ≤ 1) (heps : 0 < eps) :
    ContinuousOn (Function.uncurry (weightedPairLaplace m rho))
      (Icc eps T ×ˢ Icc eps T) := by
  let D : ℝ × ℝ → ℝ := fun w ↦
    (1 + 2 * w.1) * (1 + 2 * w.2) - 4 * rho ^ 2 * w.1 * w.2
  have hD : Continuous D := by unfold D; fun_prop
  have hsqrt : Continuous fun w ↦ Real.sqrt (D w) := by fun_prop
  have hsqrtne : ∀ w ∈ (Icc eps T ×ˢ Icc eps T),
      Real.sqrt (D w) ≠ 0 := by
    intro w hw
    apply ne_of_gt
    rw [Real.sqrt_pos]
    exact pairLaplace_discriminant_pos hrho
      (heps.le.trans hw.1.1) (heps.le.trans hw.2.1)
  unfold Function.uncurry weightedPairLaplace pairLaplaceValue
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact continuous_fst.continuousOn.inv₀ fun w hw ↦
        (heps.trans_le hw.1.1).ne'
    · exact continuous_snd.continuousOn.inv₀ fun w hw ↦
        (heps.trans_le hw.2.1).ne'
  · change ContinuousOn (fun w ↦ (Real.sqrt (D w))⁻¹ ^ m) _
    exact (hsqrt.continuousOn.inv₀ hsqrtne).pow m

lemma continuousOn_weightedMarginalProduct_Icc {eps T : ℝ}
    (heps : 0 < eps) :
    ContinuousOn (Function.uncurry (weightedMarginalProduct m))
      (Icc eps T ×ˢ Icc eps T) := by
  have hsqrts : Continuous fun w : ℝ × ℝ ↦
      Real.sqrt (1 + 2 * w.1) := by fun_prop
  have hsqrtt : Continuous fun w : ℝ × ℝ ↦
      Real.sqrt (1 + 2 * w.2) := by fun_prop
  unfold Function.uncurry weightedMarginalProduct marginalLaplaceValue
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact continuous_fst.continuousOn.inv₀ fun w hw ↦
        (heps.trans_le hw.1.1).ne'
    · exact continuous_snd.continuousOn.inv₀ fun w hw ↦
        (heps.trans_le hw.2.1).ne'
  · apply ContinuousOn.mul
    · apply ContinuousOn.pow
      exact hsqrts.continuousOn.inv₀ fun w hw ↦ by
        apply ne_of_gt
        rw [Real.sqrt_pos]
        linarith [heps.trans_le hw.1.1]
    · apply ContinuousOn.pow
      exact hsqrtt.continuousOn.inv₀ fun w hw ↦ by
        apply ne_of_gt
        rw [Real.sqrt_pos]
        linarith [heps.trans_le hw.2.1]

lemma integrableOn_weightedPairLaplace_prod_Ioc
    {rho eps T : ℝ} (hrho : |rho| ≤ 1) (heps : 0 < eps) :
    IntegrableOn (Function.uncurry (weightedPairLaplace m rho))
      (Ioc eps T ×ˢ Ioc eps T) := by
  have hcont := continuousOn_weightedPairLaplace_Icc (m := m)
    (T := T) hrho heps
  have hint : IntegrableOn (Function.uncurry (weightedPairLaplace m rho))
      (Icc eps T ×ˢ Icc eps T) :=
    hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact hint.mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma integrableOn_weightedMarginalProduct_prod_Ioc
    {eps T : ℝ} (heps : 0 < eps) :
    IntegrableOn (Function.uncurry (weightedMarginalProduct m))
      (Ioc eps T ×ˢ Ioc eps T) := by
  have hcont := continuousOn_weightedMarginalProduct_Icc (m := m) (T := T) heps
  have hint : IntegrableOn (Function.uncurry (weightedMarginalProduct m))
      (Icc eps T ×ˢ Icc eps T) :=
    hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact hint.mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma double_integral_sub_eq_covarianceKernel
    {rho eps T : ℝ} (hrho : |rho| ≤ 1)
    (heps : 0 < eps) (hT : eps ≤ T) :
    (∫ s in eps..T, ∫ t in eps..T, weightedPairLaplace m rho s t) -
      (∫ s in eps..T, ∫ t in eps..T, weightedMarginalProduct m s t) =
    ∫ s in eps..T, ∫ t in eps..T,
      weightedPairCovarianceKernel m rho s t := by
  have hp := integrableOn_weightedPairLaplace_prod_Ioc (m := m)
    (T := T) hrho heps
  have hq := integrableOn_weightedMarginalProduct_prod_Ioc (m := m)
    (T := T) heps
  simp only [intervalIntegral.integral_of_le hT]
  have hpF := setIntegral_prod
    (Function.uncurry (weightedPairLaplace m rho)) hp
  have hqF := setIntegral_prod
    (Function.uncurry (weightedMarginalProduct m)) hq
  have hdF := setIntegral_prod
    (Function.uncurry (weightedPairLaplace m rho) -
      Function.uncurry (weightedMarginalProduct m)) (hp.sub hq)
  have hpF' :
      (∫ w in Ioc eps T ×ˢ Ioc eps T,
        Function.uncurry (weightedPairLaplace m rho) w) =
      ∫ s in Ioc eps T, ∫ t in Ioc eps T,
        weightedPairLaplace m rho s t := by
    simpa only [Measure.volume_eq_prod, Function.uncurry_apply_pair] using hpF
  have hqF' :
      (∫ w in Ioc eps T ×ˢ Ioc eps T,
        Function.uncurry (weightedMarginalProduct m) w) =
      ∫ s in Ioc eps T, ∫ t in Ioc eps T,
        weightedMarginalProduct m s t := by
    simpa only [Measure.volume_eq_prod, Function.uncurry_apply_pair] using hqF
  have hdF' :
      (∫ w in Ioc eps T ×ˢ Ioc eps T,
        (Function.uncurry (weightedPairLaplace m rho) -
          Function.uncurry (weightedMarginalProduct m)) w) =
      ∫ s in Ioc eps T, ∫ t in Ioc eps T,
        (Function.uncurry (weightedPairLaplace m rho) -
          Function.uncurry (weightedMarginalProduct m)) (s, t) := by
    simpa only [Measure.volume_eq_prod, Function.uncurry_apply_pair] using hdF
  calc
    (∫ s in Ioc eps T, ∫ t in Ioc eps T,
        weightedPairLaplace m rho s t) -
        (∫ s in Ioc eps T, ∫ t in Ioc eps T,
          weightedMarginalProduct m s t) =
      (∫ w in Ioc eps T ×ˢ Ioc eps T,
        Function.uncurry (weightedPairLaplace m rho) w) -
      (∫ w in Ioc eps T ×ˢ Ioc eps T,
        Function.uncurry (weightedMarginalProduct m) w) := by
      rw [hpF', hqF']
    _ = ∫ w in Ioc eps T ×ˢ Ioc eps T,
        (Function.uncurry (weightedPairLaplace m rho) -
          Function.uncurry (weightedMarginalProduct m)) w := by
      exact (integral_sub hp hq).symm
    _ = ∫ s in Ioc eps T, ∫ t in Ioc eps T,
        weightedPairCovarianceKernel m rho s t := by
      rw [hdF']
      rfl

lemma covariance_laplaceQIntegral_eq_double_kernel
    {eps T : ℝ} (heps : 0 < eps) (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i j : Fin p) :
    cov[laplaceQIntegral (m := m) eps T R i,
        laplaceQIntegral (m := m) eps T R j;
        standardGaussianDataMeasure m p] =
      ∫ s in eps..T, ∫ t in eps..T,
        weightedPairCovarianceKernel m (R.val i j) s t := by
  rw [covariance_laplaceQIntegral_eq_double_kernel_difference
    heps hT R i j]
  exact double_integral_sub_eq_covarianceKernel
    (R.abs_apply_le_one i j) heps hT

lemma covariance_frullaniLogTrunc_Q_eq_double_kernel
    {eps T : ℝ} (heps : 0 < eps) (hT : eps ≤ T)
    (R : CorrelationMatrix p) (i j : Fin p) :
    cov[fun z : GaussianData m p ↦ frullaniLogTrunc eps T (Q R z i),
        fun z ↦ frullaniLogTrunc eps T (Q R z j);
        standardGaussianDataMeasure m p] =
      ∫ s in eps..T, ∫ t in eps..T,
        weightedPairCovarianceKernel m (R.val i j) s t := by
  let c := ∫ s in eps..T, s⁻¹ * Real.exp (-s)
  have hi : (fun z : GaussianData m p ↦
      frullaniLogTrunc eps T (Q R z i)) =
      fun z ↦ c - laplaceQIntegral eps T R i z := by
    funext z
    exact frullaniLogTrunc_Q_eq_const_sub_laplaceQIntegral
      heps hT R i z
  have hj : (fun z : GaussianData m p ↦
      frullaniLogTrunc eps T (Q R z j)) =
      fun z ↦ c - laplaceQIntegral eps T R j z := by
    funext z
    exact frullaniLogTrunc_Q_eq_const_sub_laplaceQIntegral
      heps hT R j z
  rw [hi, hj]
  rw [covariance_const_sub_left
    ((memLp_laplaceQIntegral_two heps hT R i).integrable (by norm_num)) c]
  rw [covariance_const_sub_right
    ((memLp_laplaceQIntegral_two heps hT R j).integrable (by norm_num)) c]
  simp only [neg_neg]
  exact covariance_laplaceQIntegral_eq_double_kernel heps hT R i j

lemma covariance_frullaniQApprox_eq_double_kernel (n : ℕ)
    (R : CorrelationMatrix p) (i j : Fin p) :
    cov[frullaniQApprox (m := m) n R i,
        frullaniQApprox (m := m) n R j;
        standardGaussianDataMeasure m p] =
      ∫ s in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
        ∫ t in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
          weightedPairCovarianceKernel m (R.val i j) s t := by
  exact covariance_frullaniLogTrunc_Q_eq_double_kernel
    (frullaniApprox_eps_pos n) (frullaniApprox_eps_le_T n) R i j

/-- The exact compact-window Frullani/Laplace representation of the actual
log-radius covariance.  This is the narrow bridge from the common Gaussian
probability space to the scalar Kibble/Laguerre calculation. -/
theorem tendsto_double_kernel_eq_covariance_log_Q (hm : 0 < m)
    (R : CorrelationMatrix p) (i j : Fin p) :
    Tendsto (fun n : ℕ ↦
      ∫ s in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
        ∫ t in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
          weightedPairCovarianceKernel m (R.val i j) s t) atTop
      (nhds (cov[fun z ↦ Real.log (Q R z i),
        fun z ↦ Real.log (Q R z j);
        standardGaussianDataMeasure m p])) := by
  exact (tendsto_covariance_frullaniQApprox hm R i j).congr'
    (Eventually.of_forall fun n ↦
      covariance_frullaniQApprox_eq_double_kernel (m := m) n R i j)

end LogdetLean.GeneralRDecomposition
