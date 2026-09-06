import LogdetLean.GeneralRFrullaniLaplace
import LogdetLean.RadialLaplaceKernel
import LogdetLean.KibbleCovarianceBridge
import LogdetLean.RpowIntervalLimit
/-!
# Actual Gaussian log-radius covariance bounds from the Laplace kernel

This module targets the weaker consequence needed by the exact-variance
comparison while the full kernel-to-Kibble-series evaluation is developed.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology Interval

def kibbleFirstFactor (a s : ℝ) : ℝ :=
  (1 + 2 * s) ^ (-a - 1)

def kibbleFirstAntiderivative (a s : ℝ) : ℝ :=
  -(1 / (2 * a)) * (1 + 2 * s) ^ (-a)

theorem hasDerivAt_kibbleFirstAntiderivative {a s : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) :
    HasDerivAt (kibbleFirstAntiderivative a) (kibbleFirstFactor a s) s := by
  have hbase : HasDerivAt (fun x : ℝ ↦ 1 + 2 * x) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul 2).const_add 1
  have hpos : 0 < 1 + 2 * s := by linarith
  have hpow := hbase.rpow_const (p := -a) (Or.inl hpos.ne')
  have hmul := hpow.const_mul (-(1 / (2 * a)))
  have hvalue : -(1 / (2 * a)) *
      (2 * -a * (1 + 2 * s) ^ (-a - 1)) = kibbleFirstFactor a s := by
    unfold kibbleFirstFactor
    field_simp [ha.ne']
  unfold kibbleFirstAntiderivative
  exact hmul.congr_deriv hvalue

theorem integral_kibbleFirstFactor {a eps T : ℝ}
    (ha : 0 < a) (heps : 0 ≤ eps) (hT : eps ≤ T) :
    ∫ s in eps..T, kibbleFirstFactor a s =
      kibbleFirstAntiderivative a T - kibbleFirstAntiderivative a eps := by
  let hderiv : ∀ s ∈ uIcc eps T,
      HasDerivAt (kibbleFirstAntiderivative a) (kibbleFirstFactor a s) s := by
    intro s hs
    rw [uIcc_of_le hT] at hs
    have hs' : eps ≤ s := by
      exact hs.1
    exact hasDerivAt_kibbleFirstAntiderivative ha (heps.trans hs')
  have hcont : ContinuousOn (kibbleFirstFactor a) (uIcc eps T) := by
    apply continuousOn_of_forall_continuousAt
    intro s hs
    rw [uIcc_of_le hT] at hs
    have hpos : 0 < 1 + 2 * s := by
      have := heps.trans hs.1
      linarith
    unfold kibbleFirstFactor
    exact (by fun_prop : ContinuousAt (fun x : ℝ ↦ 1 + 2 * x) s).rpow_const
      (Or.inl hpos.ne')
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable

lemma kibbleFirstFactor_eq_reciprocal {a s : ℝ} (hs : 0 ≤ s) :
    kibbleFirstFactor a s = 1 / (1 + 2 * s) ^ (a + 1) := by
  have hbase : 0 < 1 + 2 * s := by linarith
  unfold kibbleFirstFactor
  rw [show -a - 1 = -(a + 1) by ring, Real.rpow_neg hbase.le]
  simp only [one_div]

/-- The first (quadratic-in-correlation) term of the weighted Kibble
Laplace kernel.  It is written in the same algebraic form as the
negative-binomial expansion, so the pointwise tail identity below is exact. -/
def kibbleFirstKernel (m : ℕ) (rho s t : ℝ) : ℝ :=
  s⁻¹ * t⁻¹ *
    ((1 / laplaceA s t ^ ((m : ℝ) / 2)) *
      (((m : ℝ) / 2) * rho ^ 2 * laplaceB s t))

/-- Its compact Frullani-window integral. -/
def kibbleFirstWindowIntegral (m : ℕ) (rho : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
    ∫ t in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
      kibbleFirstKernel m rho s t

lemma kibbleFirstKernel_eq_factorized {m : ℕ} {rho s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    kibbleFirstKernel m rho s t =
      2 * (m : ℝ) * rho ^ 2 *
        kibbleFirstFactor ((m : ℝ) / 2) s *
        kibbleFirstFactor ((m : ℝ) / 2) t := by
  let a : ℝ := (m : ℝ) / 2
  let u : ℝ := 1 + 2 * s
  let v : ℝ := 1 + 2 * t
  have hu : 0 < u := by dsimp [u]; linarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hA : laplaceA s t = u * v := by rfl
  have hpowA : (u * v) ^ a = u ^ a * v ^ a :=
    Real.mul_rpow hu.le hv.le
  have hpowu : u ^ (a + 1) = u ^ a * u := by
    simpa using Real.rpow_add hu a 1
  have hpowv : v ^ (a + 1) = v ^ a * v := by
    simpa using Real.rpow_add hv a 1
  rw [kibbleFirstFactor_eq_reciprocal hs.le,
    kibbleFirstFactor_eq_reciprocal ht.le]
  unfold kibbleFirstKernel laplaceB
  rw [hA, hpowA]
  change s⁻¹ * t⁻¹ *
      ((1 / (u ^ a * v ^ a)) * (a * rho ^ 2 * (4 * s * t / (u * v)))) =
    2 * (m : ℝ) * rho ^ 2 * (1 / u ^ (a + 1)) *
      (1 / v ^ (a + 1))
  rw [hpowu, hpowv]
  have hua : u ^ a ≠ 0 := (Real.rpow_pos_of_pos hu a).ne'
  have hva : v ^ a ≠ 0 := (Real.rpow_pos_of_pos hv a).ne'
  dsimp [a]
  field_simp [hs.ne', ht.ne', hu.ne', hv.ne', hua, hva]
  ring

lemma kibbleFirstWindowIntegral_eq {m : ℕ} {rho : ℝ} (n : ℕ) :
    kibbleFirstWindowIntegral m rho n =
      2 * (m : ℝ) * rho ^ 2 *
        (reciprocalPowerWindowIntegral ((m : ℝ) / 2) n) ^ 2 := by
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  let T : ℝ := (n : ℝ) + 1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hT : eps ≤ T := by
    dsimp [eps, T]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      (by nlinarith)
  have hpoint : ∀ s ∈ uIcc eps T, ∀ t ∈ uIcc eps T,
      kibbleFirstKernel m rho s t =
        2 * (m : ℝ) * rho ^ 2 *
          kibbleFirstFactor ((m : ℝ) / 2) s *
          kibbleFirstFactor ((m : ℝ) / 2) t := by
    intro s hs t ht
    rw [uIcc_of_le hT] at hs ht
    exact kibbleFirstKernel_eq_factorized
      (heps.trans_le hs.1) (heps.trans_le ht.1)
  unfold kibbleFirstWindowIntegral
  change (∫ s in eps..T, ∫ t in eps..T, kibbleFirstKernel m rho s t) = _
  calc
    (∫ s in eps..T, ∫ t in eps..T, kibbleFirstKernel m rho s t) =
        ∫ s in eps..T, ∫ t in eps..T,
          2 * (m : ℝ) * rho ^ 2 *
            kibbleFirstFactor ((m : ℝ) / 2) s *
            kibbleFirstFactor ((m : ℝ) / 2) t := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint s hs t ht
    _ = 2 * (m : ℝ) * rho ^ 2 *
        (∫ s in eps..T, kibbleFirstFactor ((m : ℝ) / 2) s) ^ 2 := by
      simp_rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const]
      have houter :
          (∫ x in eps..T,
              2 * (m : ℝ) * rho ^ 2 *
                kibbleFirstFactor ((m : ℝ) / 2) x) =
            (2 * (m : ℝ) * rho ^ 2) *
              ∫ x in eps..T, kibbleFirstFactor ((m : ℝ) / 2) x := by
        rw [intervalIntegral.integral_const_mul]
      rw [houter]
      rw [pow_two]
      ring
    _ = 2 * (m : ℝ) * rho ^ 2 *
        (reciprocalPowerWindowIntegral ((m : ℝ) / 2) n) ^ 2 := by
      congr 2
      unfold reciprocalPowerWindowIntegral
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hT] at hs
      exact kibbleFirstFactor_eq_reciprocal
        (heps.le.trans hs.1)

/-- The first compact-window term tends exactly to `2 rho² / m`. -/
theorem tendsto_kibbleFirstWindowIntegral {m : ℕ} (hm : 0 < m) (rho : ℝ) :
    Tendsto (kibbleFirstWindowIntegral m rho) atTop
      (nhds (2 * rho ^ 2 / (m : ℝ))) := by
  have ha : 0 < (m : ℝ) / 2 := by positivity
  have hI := tendsto_reciprocalPowerWindowIntegral ha
  have hformula : kibbleFirstWindowIntegral m rho = fun n : ℕ ↦
      2 * (m : ℝ) * rho ^ 2 *
        (reciprocalPowerWindowIntegral ((m : ℝ) / 2) n) ^ 2 := by
    funext n
    exact kibbleFirstWindowIntegral_eq n
  rw [hformula]
  have hlim : Tendsto (fun n : ℕ ↦
      (2 * (m : ℝ) * rho ^ 2) *
        (reciprocalPowerWindowIntegral ((m : ℝ) / 2) n) ^ 2) atTop
      (nhds ((2 * (m : ℝ) * rho ^ 2) *
        (1 / (2 * ((m : ℝ) / 2))) ^ 2)) :=
    tendsto_const_nhds.mul (hI.pow 2)
  convert hlim using 1
  field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne']

lemma marginalLaplaceValue_eq_reciprocal_rpow {m : ℕ} {s : ℝ}
    (hs : 0 ≤ s) :
    GeneralRDecomposition.marginalLaplaceValue m s =
      1 / (1 + 2 * s) ^ ((m : ℝ) / 2) := by
  unfold GeneralRDecomposition.marginalLaplaceValue
  exact inv_sqrt_pow_eq_one_div_rpow_half' _ _ (by linarith)

lemma marginalLaplaceProduct_eq_reciprocal_laplaceA {m : ℕ} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    GeneralRDecomposition.marginalLaplaceValue m s *
        GeneralRDecomposition.marginalLaplaceValue m t =
      1 / laplaceA s t ^ ((m : ℝ) / 2) := by
  let a : ℝ := (m : ℝ) / 2
  let u : ℝ := 1 + 2 * s
  let v : ℝ := 1 + 2 * t
  have hu : 0 < u := by dsimp [u]; linarith
  have hv : 0 < v := by dsimp [v]; linarith
  rw [marginalLaplaceValue_eq_reciprocal_rpow hs,
    marginalLaplaceValue_eq_reciprocal_rpow ht]
  change (1 / u ^ a) * (1 / v ^ a) = 1 / (u * v) ^ a
  rw [Real.mul_rpow hu.le hv.le]
  have hua : u ^ a ≠ 0 := (Real.rpow_pos_of_pos hu a).ne'
  have hva : v ^ a ≠ 0 := (Real.rpow_pos_of_pos hv a).ne'
  field_simp [hua, hva]

/-- Exact negative-binomial tail representation of the weighted covariance
kernel after subtracting its first correlation term. -/
lemma weightedPairCovarianceKernel_sub_first_eq_weighted_tail
    {m : ℕ} {rho s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
        kibbleFirstKernel m rho s t =
      s⁻¹ * t⁻¹ *
        (GeneralRDecomposition.pairLaplaceValue m rho s t -
          (1 / laplaceA s t ^ ((m : ℝ) / 2)) *
            (1 + ((m : ℝ) / 2) * rho ^ 2 * laplaceB s t)) := by
  unfold GeneralRDecomposition.weightedPairCovarianceKernel
    GeneralRDecomposition.weightedPairLaplace
    GeneralRDecomposition.weightedMarginalProduct
    kibbleFirstKernel
  rw [show GeneralRDecomposition.marginalLaplaceValue m s *
      GeneralRDecomposition.marginalLaplaceValue m t =
        1 / laplaceA s t ^ ((m : ℝ) / 2) from
    marginalLaplaceProduct_eq_reciprocal_laplaceA hs ht]
  ring

lemma weightedPairCovarianceKernel_sub_first_nonneg
    {m : ℕ} (hm : 0 < m) {rho s t : ℝ}
    (hrho : |rho| ≤ 1) (hs : 0 < s) (ht : 0 < t) :
    0 ≤ GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
      kibbleFirstKernel m rho s t := by
  have hz0 : 0 ≤ rho ^ 2 := sq_nonneg rho
  have hz1 : rho ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one rho).2 hrho
  rw [weightedPairCovarianceKernel_sub_first_eq_weighted_tail hs.le ht.le]
  have htail := jointLaplace_tail_eq (m := m) hm
    (s := s) (t := t) (z := rho ^ 2) hs.le ht.le hz0 hz1
  change (0 : ℝ) ≤ s⁻¹ * t⁻¹ * _
  rw [show GeneralRDecomposition.pairLaplaceValue m rho s t =
      (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) -
        4 * rho ^ 2 * s * t))⁻¹ ^ m by rfl,
    htail]
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr hs.le) (inv_nonneg.mpr ht.le))
    (mul_nonneg
      (div_nonneg zero_le_one
        (Real.rpow_nonneg (laplaceA_pos hs.le ht.le).le _))
      (nbTail_nonneg (by positivity) (mul_nonneg hz0
        (laplaceB_nonneg hs.le ht.le))))

/-- The nonlinear weighted kernel at `rho` is bounded by `rho^4` times
the endpoint nonlinear kernel. -/
lemma weightedPairCovarianceKernel_sub_first_le_endpoint
    {m : ℕ} (hm : 0 < m) {rho s t : ℝ}
    (hrho : |rho| ≤ 1) (hs : 0 < s) (ht : 0 < t) :
    GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
        kibbleFirstKernel m rho s t ≤
      rho ^ 4 *
        (GeneralRDecomposition.weightedPairCovarianceKernel m 1 s t -
          kibbleFirstKernel m 1 s t) := by
  have hz0 : 0 ≤ rho ^ 2 := sq_nonneg rho
  have hz1 : rho ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one rho).2 hrho
  have hraw := jointLaplace_tail_le_fourth (m := m) hm
    (s := s) (t := t) (z := rho ^ 2) hs.le ht.le hz0 hz1
  rw [weightedPairCovarianceKernel_sub_first_eq_weighted_tail hs.le ht.le,
    weightedPairCovarianceKernel_sub_first_eq_weighted_tail
      (rho := (1 : ℝ)) hs.le ht.le]
  have hpref : 0 ≤ s⁻¹ * t⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hs.le) (inv_nonneg.mpr ht.le)
  change s⁻¹ * t⁻¹ * _ ≤ rho ^ 4 * (s⁻¹ * t⁻¹ * _)
  have hmul := mul_le_mul_of_nonneg_left hraw hpref
  unfold GeneralRDecomposition.pairLaplaceValue
  rw [show rho ^ 4 = rho * rho * rho * rho by ring]
  simpa only [one_pow, one_mul, mul_one, pow_two,
    mul_assoc, mul_left_comm, mul_comm] using hmul

lemma continuousOn_uncurry_kibbleFirstKernel_Icc {m : ℕ}
    {rho eps T : ℝ} (heps : 0 < eps) :
    ContinuousOn (Function.uncurry (kibbleFirstKernel m rho))
      (Icc eps T ×ˢ Icc eps T) := by
  let a : ℝ := (m : ℝ) / 2
  let C : ℝ := 2 * (m : ℝ) * rho ^ 2
  let g : ℝ × ℝ → ℝ := fun w ↦
    C * kibbleFirstFactor a w.1 * kibbleFirstFactor a w.2
  have hg : ContinuousOn g (Icc eps T ×ˢ Icc eps T) := by
    apply continuousOn_of_forall_continuousAt
    intro w hw
    have hbase1 : 0 < 1 + 2 * w.1 := by linarith [hw.1.1]
    have hbase2 : 0 < 1 + 2 * w.2 := by linarith [hw.2.1]
    have hfirst1 : ContinuousAt (fun x : ℝ ↦ kibbleFirstFactor a x) w.1 := by
      unfold kibbleFirstFactor
      exact (by fun_prop : ContinuousAt (fun x : ℝ ↦ 1 + 2 * x) w.1).rpow_const
        (Or.inl hbase1.ne')
    have hfirst2 : ContinuousAt (fun x : ℝ ↦ kibbleFirstFactor a x) w.2 := by
      unfold kibbleFirstFactor
      exact (by fun_prop : ContinuousAt (fun x : ℝ ↦ 1 + 2 * x) w.2).rpow_const
        (Or.inl hbase2.ne')
    exact continuousAt_const.mul (hfirst1.comp continuousAt_fst) |>.mul
      (hfirst2.comp continuousAt_snd)
  apply hg.congr
  intro w hw
  change kibbleFirstKernel m rho w.1 w.2 = g w
  exact kibbleFirstKernel_eq_factorized
    (heps.trans_le hw.1.1) (heps.trans_le hw.2.1)

lemma continuousOn_uncurry_weightedPairCovarianceKernel_Icc {m : ℕ}
    {rho eps T : ℝ} (hrho : |rho| ≤ 1) (heps : 0 < eps) :
    ContinuousOn
      (Function.uncurry
        (GeneralRDecomposition.weightedPairCovarianceKernel m rho))
      (Icc eps T ×ˢ Icc eps T) := by
  have hp := GeneralRDecomposition.continuousOn_weightedPairLaplace_Icc
    (m := m) (T := T) hrho heps
  have hq := GeneralRDecomposition.continuousOn_weightedMarginalProduct_Icc
    (m := m) (T := T) heps
  convert hp.sub hq using 1
  ext w
  rfl

lemma continuousOn_uncurry_kibbleKernelRemainder_Icc {m : ℕ}
    {rho eps T : ℝ} (hrho : |rho| ≤ 1) (heps : 0 < eps) :
    ContinuousOn (Function.uncurry (fun s t ↦
      GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
        kibbleFirstKernel m rho s t))
      (Icc eps T ×ˢ Icc eps T) := by
  have h :=
    (continuousOn_uncurry_weightedPairCovarianceKernel_Icc
      (m := m) (T := T) hrho heps).sub
      (continuousOn_uncurry_kibbleFirstKernel_Icc
        (m := m) (rho := rho) (T := T) heps)
  convert h using 1
  ext w
  rfl

/-- Integrate a pointwise inequality over a positive compact square.  This
small Fubini wrapper keeps all integrability obligations explicit. -/
lemma doubleIntervalIntegral_mono_of_continuousOn
    {f g : ℝ × ℝ → ℝ} {eps T : ℝ} (hT : eps ≤ T)
    (hf : ContinuousOn f (Icc eps T ×ˢ Icc eps T))
    (hg : ContinuousOn g (Icc eps T ×ˢ Icc eps T))
    (hle : ∀ w ∈ Icc eps T ×ˢ Icc eps T, f w ≤ g w) :
    (∫ s in eps..T, ∫ t in eps..T, f (s, t)) ≤
      ∫ s in eps..T, ∫ t in eps..T, g (s, t) := by
  have hfIcc : IntegrableOn f (Icc eps T ×ˢ Icc eps T) :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hgIcc : IntegrableOn g (Icc eps T ×ˢ Icc eps T) :=
    hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hfIoc : IntegrableOn f (Ioc eps T ×ˢ Ioc eps T) :=
    hfIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hgIoc : IntegrableOn g (Ioc eps T ×ˢ Ioc eps T) :=
    hgIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hmono :
      (∫ w in Ioc eps T ×ˢ Ioc eps T, f w) ≤
        ∫ w in Ioc eps T ×ˢ Ioc eps T, g w := by
    exact setIntegral_mono_on hfIoc hgIoc
      (measurableSet_Ioc.prod measurableSet_Ioc)
      (fun w hw ↦ hle w
        ⟨⟨hw.1.1.le, hw.1.2⟩, ⟨hw.2.1.le, hw.2.2⟩⟩)
  have hfF := setIntegral_prod f hfIoc
  have hgF := setIntegral_prod g hgIoc
  have hfF' :
      (∫ w in Ioc eps T ×ˢ Ioc eps T, f w) =
        ∫ s in Ioc eps T, ∫ t in Ioc eps T, f (s, t) := by
    simpa only [Measure.volume_eq_prod] using hfF
  have hgF' :
      (∫ w in Ioc eps T ×ˢ Ioc eps T, g w) =
        ∫ s in Ioc eps T, ∫ t in Ioc eps T, g (s, t) := by
    simpa only [Measure.volume_eq_prod] using hgF
  simp only [intervalIntegral.integral_of_le hT]
  rw [← hfF', ← hgF']
  exact hmono

/-- The compact-window integral of the nonlinear Kibble remainder. -/
def kibbleRemainderWindowIntegral (m : ℕ) (rho : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
    ∫ t in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
      (GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
        kibbleFirstKernel m rho s t)

lemma doubleIntervalIntegral_sub_of_continuousOn
    {f g : ℝ × ℝ → ℝ} {eps T : ℝ} (hT : eps ≤ T)
    (hf : ContinuousOn f (Icc eps T ×ˢ Icc eps T))
    (hg : ContinuousOn g (Icc eps T ×ˢ Icc eps T)) :
    (∫ s in eps..T, ∫ t in eps..T, f (s, t) - g (s, t)) =
      (∫ s in eps..T, ∫ t in eps..T, f (s, t)) -
        ∫ s in eps..T, ∫ t in eps..T, g (s, t) := by
  have hfIcc : IntegrableOn f (Icc eps T ×ˢ Icc eps T) :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hgIcc : IntegrableOn g (Icc eps T ×ˢ Icc eps T) :=
    hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hfIoc : IntegrableOn f (Ioc eps T ×ˢ Ioc eps T) :=
    hfIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hgIoc : IntegrableOn g (Ioc eps T ×ˢ Ioc eps T) :=
    hgIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  let d : ℝ × ℝ → ℝ := fun w ↦ f w - g w
  have hdIoc : IntegrableOn d (Ioc eps T ×ˢ Ioc eps T) :=
    hfIoc.sub hgIoc
  have hfF := setIntegral_prod f hfIoc
  have hgF := setIntegral_prod g hgIoc
  have hdF := setIntegral_prod d hdIoc
  have hfF' :
      (∫ w in Ioc eps T ×ˢ Ioc eps T, f w) =
        ∫ s in Ioc eps T, ∫ t in Ioc eps T, f (s, t) := by
    simpa only [Measure.volume_eq_prod] using hfF
  have hgF' :
      (∫ w in Ioc eps T ×ˢ Ioc eps T, g w) =
        ∫ s in Ioc eps T, ∫ t in Ioc eps T, g (s, t) := by
    simpa only [Measure.volume_eq_prod] using hgF
  have hdF' :
      (∫ w in Ioc eps T ×ˢ Ioc eps T, d w) =
        ∫ s in Ioc eps T, ∫ t in Ioc eps T,
          (f (s, t) - g (s, t)) := by
    simpa only [Measure.volume_eq_prod] using hdF
  simp only [intervalIntegral.integral_of_le hT]
  rw [← hdF', ← hfF', ← hgF']
  exact integral_sub hfIoc hgIoc

lemma kibbleRemainderWindowIntegral_eq_sub {m : ℕ} {rho : ℝ}
    (hrho : |rho| ≤ 1) (n : ℕ) :
    kibbleRemainderWindowIntegral m rho n =
      kibbleWindowIntegral m rho n - kibbleFirstWindowIntegral m rho n := by
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  let T : ℝ := (n : ℝ) + 1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hT : eps ≤ T := by
    dsimp [eps, T]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      (by nlinarith)
  have hsub := doubleIntervalIntegral_sub_of_continuousOn hT
    (continuousOn_uncurry_weightedPairCovarianceKernel_Icc
      (m := m) (T := T) hrho heps)
    (continuousOn_uncurry_kibbleFirstKernel_Icc
      (m := m) (rho := rho) (T := T) heps)
  unfold kibbleRemainderWindowIntegral kibbleWindowIntegral
    kibbleFirstWindowIntegral
  exact hsub

theorem kibbleRemainderWindowIntegral_nonneg
    {m : ℕ} (hm : 0 < m) {rho : ℝ} (hrho : |rho| ≤ 1) (n : ℕ) :
    0 ≤ kibbleRemainderWindowIntegral m rho n := by
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  let T : ℝ := (n : ℝ) + 1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hT : eps ≤ T := by
    dsimp [eps, T]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      (by nlinarith)
  have hmono := doubleIntervalIntegral_mono_of_continuousOn hT
    (f := fun _ : ℝ × ℝ ↦ 0)
    (g := Function.uncurry (fun s t ↦
      GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
        kibbleFirstKernel m rho s t))
    continuousOn_const
    (continuousOn_uncurry_kibbleKernelRemainder_Icc
      (m := m) (T := T) hrho heps)
    (fun w hw ↦ weightedPairCovarianceKernel_sub_first_nonneg hm hrho
      (heps.trans_le hw.1.1) (heps.trans_le hw.2.1))
  unfold kibbleRemainderWindowIntegral
  change 0 ≤ ∫ s in eps..T, ∫ t in eps..T,
      (GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
        kibbleFirstKernel m rho s t)
  simpa only [Function.uncurry_apply_pair,
    intervalIntegral.integral_zero] using hmono

theorem kibbleRemainderWindowIntegral_le_endpoint
    {m : ℕ} (hm : 0 < m) {rho : ℝ} (hrho : |rho| ≤ 1) (n : ℕ) :
    kibbleRemainderWindowIntegral m rho n ≤
      rho ^ 4 * kibbleRemainderWindowIntegral m 1 n := by
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  let T : ℝ := (n : ℝ) + 1
  let rem : ℝ → ℝ → ℝ := fun s t ↦
    GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
      kibbleFirstKernel m rho s t
  let remOne : ℝ → ℝ → ℝ := fun s t ↦
    GeneralRDecomposition.weightedPairCovarianceKernel m 1 s t -
      kibbleFirstKernel m 1 s t
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hT : eps ≤ T := by
    dsimp [eps, T]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      (by nlinarith)
  have hrem := continuousOn_uncurry_kibbleKernelRemainder_Icc
    (m := m) (T := T) hrho heps
  have hremOne := continuousOn_uncurry_kibbleKernelRemainder_Icc
    (m := m) (rho := (1 : ℝ)) (T := T) (by norm_num) heps
  have hscaled : ContinuousOn
      (Function.uncurry (fun s t ↦ rho ^ 4 * remOne s t))
      (Icc eps T ×ˢ Icc eps T) := by
    have hc : ContinuousOn (fun _ : ℝ × ℝ ↦ rho ^ 4)
        (Icc eps T ×ˢ Icc eps T) := continuousOn_const
    have h := hc.mul hremOne
    convert h using 1
    ext w
    rfl
  have hmono := doubleIntervalIntegral_mono_of_continuousOn hT
    (f := Function.uncurry rem)
    (g := Function.uncurry (fun s t ↦ rho ^ 4 * remOne s t))
    (by simpa [rem, Function.uncurry] using hrem) hscaled
    (fun w hw ↦ weightedPairCovarianceKernel_sub_first_le_endpoint
      hm hrho (heps.trans_le hw.1.1) (heps.trans_le hw.2.1))
  dsimp only [rem, remOne, Function.uncurry_apply_pair] at hmono
  unfold kibbleRemainderWindowIntegral
  change (∫ s in eps..T, ∫ t in eps..T,
      (GeneralRDecomposition.weightedPairCovarianceKernel m rho s t -
        kibbleFirstKernel m rho s t)) ≤
    rho ^ 4 * (∫ s in eps..T, ∫ t in eps..T,
      (GeneralRDecomposition.weightedPairCovarianceKernel m 1 s t -
        kibbleFirstKernel m 1 s t))
  simpa only [intervalIntegral.integral_const_mul] using hmono

/-- The nonlinear compact-window remainder converges to the actual Gaussian
log-radius covariance minus its explicit first term. -/
theorem tendsto_kibbleRemainderWindowIntegral_eq_actual
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    Tendsto (kibbleRemainderWindowIntegral m (R.val i j)) atTop
      (nhds
        (cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
            fun z ↦ Real.log (GeneralRDecomposition.Q R z j);
            standardGaussianDataMeasure m p] -
          2 * (R.val i j) ^ 2 / (m : ℝ))) := by
  have hkernel : Tendsto (kibbleWindowIntegral m (R.val i j)) atTop
      (nhds
        (cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
            fun z ↦ Real.log (GeneralRDecomposition.Q R z j);
            standardGaussianDataMeasure m p])) := by
    unfold kibbleWindowIntegral
    exact GeneralRDecomposition.tendsto_double_kernel_eq_covariance_log_Q
      hm R i j
  have hfirst := tendsto_kibbleFirstWindowIntegral hm (R.val i j)
  have hsub := hkernel.sub hfirst
  exact hsub.congr' (Eventually.of_forall fun n ↦
    (kibbleRemainderWindowIntegral_eq_sub (m := m)
      (R.abs_apply_le_one i j) n).symm)

/-- At correlation one the remainder limit is the exact trigamma variance
minus `2/m`; this includes the endpoint without a limiting argument in
`rho`. -/
theorem tendsto_kibbleRemainderWindowIntegral_one
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) (i : Fin p) :
    Tendsto (kibbleRemainderWindowIntegral m 1) atTop
      (nhds (trigammaSeries ((m : ℝ) / 2) - 2 / (m : ℝ))) := by
  have h := tendsto_kibbleRemainderWindowIntegral_eq_actual hm R i i
  rw [CorrelationMatrix.apply_self] at h
  have hdiag := covariance_log_Q_self_eq_trigamma hm R i
  rw [hdiag] at h
  simpa using h

/-- Fully unconditional actual-law covariance bounds.  This is the sharp
variance-proxy comparison required in the general-correlation argument, and
does not assume the still-separate full Kibble-series evaluation. -/
theorem actual_logRadiusCovariance_remainder_bounds
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    0 ≤
        cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
            fun z ↦ Real.log (GeneralRDecomposition.Q R z j);
            standardGaussianDataMeasure m p] -
          2 * (R.val i j) ^ 2 / (m : ℝ) ∧
      cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
            fun z ↦ Real.log (GeneralRDecomposition.Q R z j);
            standardGaussianDataMeasure m p] -
          2 * (R.val i j) ^ 2 / (m : ℝ) ≤
        4 * (R.val i j) ^ 4 / (m : ℝ) ^ 2 := by
  let rho : ℝ := R.val i j
  let Lrho : ℝ :=
    cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
        fun z ↦ Real.log (GeneralRDecomposition.Q R z j);
        standardGaussianDataMeasure m p] - 2 * rho ^ 2 / (m : ℝ)
  let Lone : ℝ := trigammaSeries ((m : ℝ) / 2) - 2 / (m : ℝ)
  have hrho : |rho| ≤ 1 := R.abs_apply_le_one i j
  have hR : Tendsto (kibbleRemainderWindowIntegral m rho) atTop (nhds Lrho) := by
    simpa [rho, Lrho] using
      tendsto_kibbleRemainderWindowIntegral_eq_actual hm R i j
  have hOne : Tendsto (kibbleRemainderWindowIntegral m 1) atTop
      (nhds Lone) := by
    simpa [Lone] using tendsto_kibbleRemainderWindowIntegral_one hm R i
  have hnonneg : 0 ≤ Lrho :=
    ge_of_tendsto' hR
      (fun n ↦ kibbleRemainderWindowIntegral_nonneg hm hrho n)
  have hscaled : Tendsto
      (fun n ↦ rho ^ 4 * kibbleRemainderWindowIntegral m 1 n) atTop
      (nhds (rho ^ 4 * Lone)) := tendsto_const_nhds.mul hOne
  have hcompare : Lrho ≤ rho ^ 4 * Lone :=
    le_of_tendsto_of_tendsto' hR hscaled
      (fun n ↦ kibbleRemainderWindowIntegral_le_endpoint hm hrho n)
  have ha : 0 < (m : ℝ) / 2 := by positivity
  have htrig := trigammaSeries_le_one_div_add_one_div_sq ha
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hLone : Lone ≤ 4 / (m : ℝ) ^ 2 := by
    dsimp [Lone]
    calc
      trigammaSeries ((m : ℝ) / 2) - 2 / (m : ℝ) ≤
          (1 / ((m : ℝ) / 2) +
            1 / ((m : ℝ) / 2) ^ 2) - 2 / (m : ℝ) := by
        linarith
      _ = 4 / (m : ℝ) ^ 2 := by field_simp [hm0]; ring
  have hrho4 : 0 ≤ rho ^ 4 := by positivity
  have hupper : Lrho ≤ 4 * rho ^ 4 / (m : ℝ) ^ 2 := by
    calc
      Lrho ≤ rho ^ 4 * Lone := hcompare
      _ ≤ rho ^ 4 * (4 / (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hLone hrho4
      _ = 4 * rho ^ 4 / (m : ℝ) ^ 2 := by ring
  simpa [rho, Lrho] using And.intro hnonneg hupper

theorem sum_offDiag_two_sq_div_eq_deviationEnergy
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) :
    ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
      2 * (R.val i j) ^ 2 / (m : ℝ) =
        2 * R.deviationEnergy / (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  calc
    ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
        2 * (R.val i j) ^ 2 / (m : ℝ) =
        ∑ i : Fin p, (2 / (m : ℝ)) *
          ∑ j : Fin p with i ≠ j, (R.val i j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (2 / (m : ℝ)) *
        ∑ i : Fin p, ∑ j : Fin p with i ≠ j, (R.val i j) ^ 2 := by
      rw [Finset.mul_sum]
    _ = 2 * R.deviationEnergy / (m : ℝ) := by
      rw [← R.deviationEnergy_eq_sum_offDiag_sq]
      field_simp [hmR]

theorem sum_offDiag_fourth_le_deviationEnergy {p : ℕ}
    (R : CorrelationMatrix p) :
    ∑ i : Fin p, ∑ j : Fin p with i ≠ j, (R.val i j) ^ 4 ≤
      R.deviationEnergy := by
  rw [R.deviationEnergy_eq_sum_offDiag_sq]
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  have hsq : (R.val i j) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one (R.val i j)).2 (R.abs_apply_le_one i j)
  calc
    (R.val i j) ^ 4 = (R.val i j) ^ 2 * (R.val i j) ^ 2 := by ring
    _ ≤ (R.val i j) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = (R.val i j) ^ 2 := by ring

/-- Exact covariance-sum assembly on the actual common Gaussian space.  The
only remaining model inputs here are the classical Bartlett determinant
variance and Schur-complement determinant/radius covariance. -/
theorem variance_generalRLogDetNumerator_eq_actual_covariance_sum
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p)
    (hW : MemLp (fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det) 2
      (standardGaussianDataMeasure m p))
    (hvarW : Var[fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det;
        standardGaussianDataMeasure m p] =
      nullVSeries m p + (p : ℝ) * trigammaSeries ((m : ℝ) / 2))
    (hcovW : ∀ i : Fin p,
      cov[fun z : GaussianData m p ↦
          Real.log (GeneralRDecomposition.W0 z).det,
        fun z ↦ Real.log (GeneralRDecomposition.Q R z i);
        standardGaussianDataMeasure m p] =
          trigammaSeries ((m : ℝ) / 2)) :
    Var[generalRLogDetNumerator R;
        standardGaussianDataMeasure m p] =
      nullVSeries m p +
        ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
          cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
              fun z ↦ Real.log (GeneralRDecomposition.Q R z j);
              standardGaussianDataMeasure m p] := by
  let L : GaussianData m p → ℝ := fun z ↦
    Real.log (GeneralRDecomposition.W0 z).det
  let q : Fin p → GaussianData m p → ℝ := fun i z ↦
    Real.log (GeneralRDecomposition.Q R z i)
  let c : Fin p → Fin p → ℝ := fun i j ↦
    cov[q i, q j; standardGaussianDataMeasure m p]
  have hq : ∀ i : Fin p, MemLp (q i) 2
      (standardGaussianDataMeasure m p) := by
    intro i
    exact GeneralRDecomposition.memLp_log_Q_two hm R i
  have hpair : ∀ i j : Fin p,
      cov[q i, q j; standardGaussianDataMeasure m p] =
        if i = j then trigammaSeries ((m : ℝ) / 2) else c i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      simpa [q] using covariance_log_Q_self_eq_trigamma hm R i
    · rw [if_neg hij]
  have h := variance_sub_finsetSum_eq_base_add_offDiag
    L q (nullVSeries m p) (trigammaSeries ((m : ℝ) / 2)) c
    hW hq (by simpa [L] using hvarW) (by simpa [L, q] using hcovW) hpair
  change Var[fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det -
        ∑ i : Fin p, Real.log (GeneralRDecomposition.Q R z i);
      standardGaussianDataMeasure m p] = _
  simpa [L, q, c] using h

/-- The actual general-correlation variance satisfies the paper's sharp
proxy comparison without assuming the full Kibble-series identity. -/
theorem variance_generalRLogDetNumerator_proxy_bounds_from_actual_covariance
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p)
    (hW : MemLp (fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det) 2
      (standardGaussianDataMeasure m p))
    (hvarW : Var[fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det;
        standardGaussianDataMeasure m p] =
      nullVSeries m p + (p : ℝ) * trigammaSeries ((m : ℝ) / 2))
    (hcovW : ∀ i : Fin p,
      cov[fun z : GaussianData m p ↦
          Real.log (GeneralRDecomposition.W0 z).det,
        fun z ↦ Real.log (GeneralRDecomposition.Q R z i);
        standardGaussianDataMeasure m p] =
          trigammaSeries ((m : ℝ) / 2)) :
    0 ≤ Var[generalRLogDetNumerator R;
          standardGaussianDataMeasure m p] -
        generalRSeriesVarianceProxy m R ∧
      Var[generalRLogDetNumerator R;
          standardGaussianDataMeasure m p] -
        generalRSeriesVarianceProxy m R ≤
          4 * R.deviationEnergy / (m : ℝ) ^ 2 := by
  let c : Fin p → Fin p → ℝ := fun i j ↦
    cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
        fun z ↦ Real.log (GeneralRDecomposition.Q R z j);
        standardGaussianDataMeasure m p]
  have hvar := variance_generalRLogDetNumerator_eq_actual_covariance_sum
    hm R hW hvarW hcovW
  have hfirst := sum_offDiag_two_sq_div_eq_deviationEnergy hm R
  have hid :
      (nullVSeries m p + ∑ i : Fin p, ∑ j : Fin p with i ≠ j, c i j) -
          generalRSeriesVarianceProxy m R =
        ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
          (c i j - 2 * (R.val i j) ^ 2 / (m : ℝ)) := by
    unfold generalRSeriesVarianceProxy generalRVarianceProxy
    rw [← hfirst]
    simp_rw [Finset.sum_sub_distrib]
    ring
  rw [hvar]
  change (nullVSeries m p +
      ∑ i : Fin p, ∑ j : Fin p with i ≠ j, c i j) -
      generalRSeriesVarianceProxy m R ≥ 0 ∧ _
  rw [hid]
  constructor
  · apply Finset.sum_nonneg
    intro i _hi
    apply Finset.sum_nonneg
    intro j _hj
    exact (actual_logRadiusCovariance_remainder_bounds hm R i j).1
  · calc
      ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
          (c i j - 2 * (R.val i j) ^ 2 / (m : ℝ)) ≤
          ∑ i : Fin p, ∑ j : Fin p with i ≠ j,
            4 * (R.val i j) ^ 4 / (m : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        apply Finset.sum_le_sum
        intro j _hj
        exact (actual_logRadiusCovariance_remainder_bounds hm R i j).2
      _ = (4 / (m : ℝ) ^ 2) *
          ∑ i : Fin p, ∑ j : Fin p with i ≠ j, (R.val i j) ^ 4 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ ≤ (4 / (m : ℝ) ^ 2) * R.deviationEnergy := by
        exact mul_le_mul_of_nonneg_left
          (sum_offDiag_fourth_le_deviationEnergy R) (by positivity)
      _ = 4 * R.deviationEnergy / (m : ℝ) ^ 2 := by ring

end

end LogdetLean
