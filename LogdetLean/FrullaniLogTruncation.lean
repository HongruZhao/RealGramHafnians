import LogdetLean.GeneralRPairLaplace
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology Interval

noncomputable section

namespace LogdetLean

def frullaniLogTrunc (eps T q : ℝ) : ℝ :=
  ∫ u in eps..T, u⁻¹ * (Real.exp (-u) - Real.exp (-q * u))

@[fun_prop]
lemma measurable_frullaniLogTrunc (eps T : ℝ) :
    Measurable (frullaniLogTrunc eps T) := by
  let f : ℝ → ℝ → ℝ := fun q u ↦
    u⁻¹ * (Real.exp (-u) - Real.exp (-q * u))
  have hf : StronglyMeasurable (Function.uncurry f) :=
    (by fun_prop : Measurable (Function.uncurry f)).stronglyMeasurable
  have hleft : StronglyMeasurable (fun q ↦
      ∫ u in Set.Ioc eps T, f q u) :=
    hf.integral_prod_right
  have hright : StronglyMeasurable (fun q ↦
      ∫ u in Set.Ioc T eps, f q u) :=
    hf.integral_prod_right
  exact (hleft.sub hright).measurable

lemma tendsto_frullaniLogTrunc {q : ℝ} (hq : 0 < q) :
    Tendsto (fun w : ℝ × ℝ ↦ frullaniLogTrunc w.1 w.2 q)
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop) (nhds (Real.log q)) := by
  let g : ℝ → ℝ := Real.exp ∘ fun x ↦ -x
  have hgcont : Continuous g := Real.continuous_exp.comp continuous_neg
  have hL : Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have ht : Tendsto g (nhds 0) (nhds (g 0)) := hgcont.continuousAt
    simpa [g] using ht.mono_left nhdsWithin_le_nhds
  have hR : Tendsto g atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h := Frullani.tendsto_intervalIntegral
    ((hgcont.locallyIntegrable).locallyIntegrableOn (Ioi 0))
    (a := (1 : ℝ))
    (b := q) one_pos hq hL hR
  simpa [frullaniLogTrunc, g, Function.comp_apply, smul_eq_mul,
    Real.log_div] using h

lemma integral_exp_neg_mul (a b v : ℝ) (hv : v ≠ 0) :
    (∫ u in a..b, Real.exp (-v * u)) =
      (Real.exp (-v * a) - Real.exp (-v * b)) / v := by
  let F : ℝ → ℝ := fun u ↦ -Real.exp (-v * u) / v
  have hderiv : deriv F = fun u ↦ Real.exp (-v * u) := by
    funext u
    apply HasDerivAt.deriv
    change HasDerivAt (fun u : ℝ ↦ -Real.exp (-v * u) / v)
      (Real.exp (-v * u)) u
    have hinner : HasDerivAt (fun u : ℝ ↦ -v * u) (-v) u := by
      simpa using (hasDerivAt_id u).const_mul (-v)
    have hd := (((Real.hasDerivAt_exp (-v * u)).comp u hinner).neg.div_const v)
    have hfun : (fun u : ℝ ↦ -Real.exp (-v * u) / v) =
        (fun x ↦ (-Real.exp ∘ HMul.hMul (-v)) x / v) := by
      funext x
      rfl
    rw [hfun]
    apply hd.congr_deriv
    field_simp [hv]
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (a := a) (b := b) F hderiv
    (fun x _hx ↦ by dsimp [F]; fun_prop) (by fun_prop)
  calc
    (∫ u in a..b, Real.exp (-v * u)) = F b - F a := hFTC
    _ = (Real.exp (-v * a) - Real.exp (-v * b)) / v := by
      dsimp [F]
      field_simp [hv]
      ring

lemma inv_mul_exp_sub_eq_intervalIntegral (u q : ℝ) (hu : u ≠ 0) :
    u⁻¹ * (Real.exp (-u) - Real.exp (-q * u)) =
      ∫ v in (1 : ℝ)..q, Real.exp (-v * u) := by
  have h := integral_exp_neg_mul (1 : ℝ) q u hu
  simpa [div_eq_mul_inv, mul_comm] using h.symm

lemma frullaniLogTrunc_eq_intervalIntegral (eps T q : ℝ)
    (heps : 0 < eps) (hT : eps ≤ T) (hqpos : 0 < q) :
    frullaniLogTrunc eps T q =
      ∫ v in (1 : ℝ)..q,
        (Real.exp (-v * eps) - Real.exp (-v * T)) / v := by
  have hpoint :
      (∫ u in eps..T,
        u⁻¹ * (Real.exp (-u) - Real.exp (-q * u))) =
      ∫ u in eps..T, ∫ v in (1 : ℝ)..q, Real.exp (-v * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT] at hu
    exact inv_mul_exp_sub_eq_intervalIntegral u q
      (ne_of_gt (lt_of_lt_of_le heps hu.1))
  rw [frullaniLogTrunc, hpoint]
  have hint : IntegrableOn
      (Function.uncurry (fun u v : ℝ ↦ Real.exp (-v * u)))
      (uIoc eps T ×ˢ uIoc (1 : ℝ) q) := by
    have hbig : IntegrableOn
        (Function.uncurry (fun u v : ℝ ↦ Real.exp (-v * u)))
        (uIcc eps T ×ˢ uIcc (1 : ℝ) q) :=
      (show Continuous
          (Function.uncurry (fun u v : ℝ ↦ Real.exp (-v * u))) by
        fun_prop).continuousOn.integrableOn_compact
          (isCompact_uIcc.prod isCompact_uIcc)
    exact hbig.mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  rw [intervalIntegral_intervalIntegral_swap hint]
  apply intervalIntegral.integral_congr
  intro v hv
  change (∫ u in eps..T, Real.exp (-v * u)) = _
  rw [integral_exp_neg_mul eps T v]
  have hvpos : 0 < v := by
    rcases le_total (1 : ℝ) q with hq | hq
    · rw [uIcc_of_le hq] at hv
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hv.1
    · rw [uIcc_of_ge hq] at hv
      exact lt_of_lt_of_le hqpos hv.1
  exact hvpos.ne'

def frullaniWeight (eps T v : ℝ) : ℝ :=
  (Real.exp (-v * eps) - Real.exp (-v * T)) / v

lemma frullaniWeight_nonneg_le_inv {eps T v : ℝ}
    (heps : 0 < eps) (hT : eps ≤ T) (hv : 0 < v) :
    0 ≤ frullaniWeight eps T v ∧ frullaniWeight eps T v ≤ v⁻¹ := by
  unfold frullaniWeight
  have harg : -v * T ≤ -v * eps := by nlinarith
  have hexple : Real.exp (-v * T) ≤ Real.exp (-v * eps) :=
    Real.exp_le_exp.mpr harg
  have hexpone : Real.exp (-v * eps) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hexple) hv.le
  · calc
      (Real.exp (-v * eps) - Real.exp (-v * T)) / v ≤ 1 / v := by
        rw [div_le_div_iff_of_pos_right hv]
        nlinarith [Real.exp_pos (-v * T)]
      _ = v⁻¹ := by rw [one_div]

lemma intervalIntegrable_frullaniWeight {eps T a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (frullaniWeight eps T) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro v hv
    rw [mem_uIcc] at hv
    have hvpos : 0 < v := by
      rcases hv with hv | hv
      · exact lt_of_lt_of_le ha hv.1
      · exact lt_of_lt_of_le hb hv.1
    exact hvpos.ne'

lemma abs_frullaniLogTrunc_le_abs_log {eps T q : ℝ}
    (heps : 0 < eps) (hT : eps ≤ T) (hqpos : 0 < q) :
    |frullaniLogTrunc eps T q| ≤ |Real.log q| := by
  rw [frullaniLogTrunc_eq_intervalIntegral eps T q heps hT hqpos]
  let k : ℝ → ℝ := frullaniWeight eps T
  change |(∫ v in (1 : ℝ)..q, k v)| ≤ |Real.log q|
  have hkint : IntervalIntegrable k volume (1 : ℝ) q := by
    exact intervalIntegrable_frullaniWeight one_pos hqpos
  have hiint : IntervalIntegrable (fun v : ℝ ↦ v⁻¹) volume (1 : ℝ) q := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro v hv
    rcases (mem_uIcc.mp hv) with hv | hv
    · exact (lt_of_lt_of_le one_pos hv.1).ne'
    · exact (lt_of_lt_of_le hqpos hv.1).ne'
  rcases le_total (1 : ℝ) q with hq | hq
  · have hk0 : 0 ≤ ∫ v in (1 : ℝ)..q, k v :=
      intervalIntegral.integral_nonneg hq fun v hv ↦
        (frullaniWeight_nonneg_le_inv heps hT
          (lt_of_lt_of_le one_pos hv.1)).1
    have hki : (∫ v in (1 : ℝ)..q, k v) ≤
        ∫ v in (1 : ℝ)..q, v⁻¹ :=
      intervalIntegral.integral_mono_on hq hkint hiint fun v hv ↦
        (frullaniWeight_nonneg_le_inv heps hT
          (lt_of_lt_of_le one_pos hv.1)).2
    rw [integral_inv_of_pos one_pos hqpos] at hki
    simp only [div_one] at hki
    rw [abs_of_nonneg hk0, abs_of_nonneg (Real.log_nonneg hq)]
    exact hki
  · have hkint' : IntervalIntegrable k volume q (1 : ℝ) := hkint.symm
    have hiint' : IntervalIntegrable (fun v : ℝ ↦ v⁻¹)
        volume q (1 : ℝ) := hiint.symm
    have hk0 : 0 ≤ ∫ v in q..(1 : ℝ), k v :=
      intervalIntegral.integral_nonneg hq fun v hv ↦
        (frullaniWeight_nonneg_le_inv heps hT
          (lt_of_lt_of_le hqpos hv.1)).1
    have hki : (∫ v in q..(1 : ℝ), k v) ≤
        ∫ v in q..(1 : ℝ), v⁻¹ :=
      intervalIntegral.integral_mono_on hq hkint' hiint' fun v hv ↦
        (frullaniWeight_nonneg_le_inv heps hT
          (lt_of_lt_of_le hqpos hv.1)).2
    rw [integral_inv_of_pos hqpos one_pos] at hki
    have hlog : Real.log q ≤ 0 := Real.log_nonpos hqpos.le hq
    rw [intervalIntegral.integral_symm]
    rw [abs_of_nonpos (neg_nonpos.mpr hk0), abs_of_nonpos hlog]
    simpa [Real.log_div, hqpos.ne'] using hki

end LogdetLean
