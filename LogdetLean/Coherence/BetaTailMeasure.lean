import LogdetLean.BetaMellin
import LogdetLean.Coherence.BetaTailElementary
/-!
# The beta half-tail as an exact beta probability

This file connects the elementary interval integral from
`BetaTailElementary` to mathlib's probability measure
`ProbabilityTheory.betaMeasure`.

For `b > 1` and `0 < t < 1`, the real-valued probability of the upper tail is

`(betaMeasure (1/2) b).real (Ioi t)
    = betaHalfTailIntegral b t / beta (1/2) b`.

The proof expands the density and explicitly removes the part above `1`,
where the beta density vanishes.  Thus no informal appeal to a density formula
is left in the later asymptotic argument.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Interval Real

private lemma betaPDFReal_half_eq_on_unit
    {b x : ℝ} (_hb : 1 < b) (hx0 : 0 < x) (hx1 : x < 1) :
    betaPDFReal (1 / 2) b x =
      (1 / beta (1 / 2) b) *
        (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1)) := by
  rw [betaPDFReal, if_pos ⟨hx0, hx1⟩]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
  ring

private lemma betaPDFReal_half_eq_zero_of_one_le
    {b x : ℝ} (hx : 1 ≤ x) : betaPDFReal (1 / 2) b x = 0 := by
  rw [betaPDFReal, if_neg]
  exact fun h ↦ (not_lt_of_ge hx) h.2

/-- Exact identification of the real-valued upper-tail probability of a
`Beta(1/2,b)` law with the normalized elementary half-tail integral. -/
theorem betaMeasure_half_Ioi_real_eq_tailIntegral
    {b t : ℝ} (hb : 1 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    (betaMeasure (1 / 2) b).real (Ioi t) =
      (1 / beta (1 / 2) b) * betaHalfTailIntegral b t := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hb0 : 0 < b := zero_lt_one.trans hb
  calc
    (betaMeasure (1 / 2) b).real (Ioi t) =
        ∫ _x in Ioi t, (1 : ℝ) ∂betaMeasure (1 / 2) b := by
      simp
    _ = ∫ x in Ioi t, betaPDFReal (1 / 2) b x ∂volume := by
      rw [betaMeasure]
      change (∫ _x in Ioi t, (1 : ℝ) ∂volume.withDensity
        (fun x ↦ ENNReal.ofReal (betaPDFReal (1 / 2) b x))) = _
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
          (measurable_betaPDFReal (1 / 2) b).ennreal_ofReal
          (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) _ measurableSet_Ioi]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      change (ENNReal.ofReal (betaPDFReal (1 / 2) b x)).toReal • (1 : ℝ) = _
      rw [ENNReal.toReal_ofReal
        (LogdetLean.betaPDFReal_nonneg_of_pos hhalf hb0 x)]
      simp
    _ = ∫ x in Ioo t 1, betaPDFReal (1 / 2) b x ∂volume := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      · exact fun x hx ↦ hx.1
      · intro x hx
        apply betaPDFReal_half_eq_zero_of_one_le
        by_contra hnot
        exact hx.2 ⟨hx.1, lt_of_not_ge hnot⟩
    _ = ∫ x in Ioo t 1,
          (1 / beta (1 / 2) b) *
            (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1)) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact betaPDFReal_half_eq_on_unit hb (ht0.trans hx.1) hx.2
    _ = (1 / beta (1 / 2) b) *
        ∫ x in Ioo t 1, x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (b - 1) ∂volume := by
      rw [integral_const_mul]
    _ = (1 / beta (1 / 2) b) * betaHalfTailIntegral b t := by
      unfold betaHalfTailIntegral
      rw [intervalIntegral.integral_of_le ht1.le]
      congr 1
      exact setIntegral_congr_set Ioo_ae_eq_Ioc

/-- The same exact identity with the conventional quotient notation. -/
theorem betaMeasure_half_Ioi_real_eq_tailIntegral_div
    {b t : ℝ} (hb : 1 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    (betaMeasure (1 / 2) b).real (Ioi t) =
      betaHalfTailIntegral b t / beta (1 / 2) b := by
  rw [betaMeasure_half_Ioi_real_eq_tailIntegral hb ht0 ht1]
  ring

end

end LogdetLean.Coherence
