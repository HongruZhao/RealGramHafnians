import LogdetLean.Coherence.BetaTailMeasure
/-!
# A finite ratio bound for beta half-tails

The conditional matching argument needs more than the one-edge intensity.  If
`X` has law `Beta(1/2,b)` and the threshold is `t`, we must control the
conditional overshoot probability

`P(X > s | X > t) = P(X > s) / P(X > t)`, for `t ≤ s`.

This module proves the exact finite reduction to the endpoint terms in the
Mills bounds.  No asymptotic assertion is assumed.  A later module may insert
the coherence thresholds and show that the explicit endpoint quotient tends
to zero.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- The beta half-tail integral is strictly positive inside `(0,1)` when
`b > 1`. -/
theorem betaHalfTailIntegral_pos
    {b t : ℝ} (hb : 1 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < betaHalfTailIntegral b t := by
  have hM := betaHalfTailEndpoint_mills_bounds hb ht0 ht1
  have hendpoint : 0 < betaHalfTailEndpoint b t := by
    unfold betaHalfTailEndpoint
    positivity
  have hden : 0 < 1 + 1 / (2 * b * t) := by positivity
  exact lt_of_lt_of_le (div_pos hendpoint hden) hM.1

/-- Finite Mills-ratio bound for two nested beta half-tails. -/
theorem betaHalfTailIntegral_ratio_le_endpoint_ratio
    {b t s : ℝ} (hb : 1 < b)
    (ht0 : 0 < t) (hts : t ≤ s) (hs1 : s < 1) :
    betaHalfTailIntegral b s / betaHalfTailIntegral b t ≤
      betaHalfTailEndpoint b s /
        (betaHalfTailEndpoint b t / (1 + 1 / (2 * b * t))) := by
  have ht1 : t < 1 := lt_of_le_of_lt hts hs1
  have hs0 : 0 < s := lt_of_lt_of_le ht0 hts
  have hIt0 : 0 < betaHalfTailIntegral b t :=
    betaHalfTailIntegral_pos hb ht0 ht1
  have hEs0 : 0 ≤ betaHalfTailEndpoint b s := by
    unfold betaHalfTailEndpoint
    positivity
  have hden : 0 < 1 + 1 / (2 * b * t) := by positivity
  have hEt0 : 0 < betaHalfTailEndpoint b t := by
    unfold betaHalfTailEndpoint
    positivity
  have hlower := (betaHalfTailEndpoint_mills_bounds hb ht0 ht1).1
  have hupper := (betaHalfTailEndpoint_mills_bounds hb hs0 hs1).2
  calc
    betaHalfTailIntegral b s / betaHalfTailIntegral b t ≤
        betaHalfTailEndpoint b s / betaHalfTailIntegral b t :=
      div_le_div_of_nonneg_right hupper hIt0.le
    _ ≤ betaHalfTailEndpoint b s /
        (betaHalfTailEndpoint b t / (1 + 1 / (2 * b * t))) :=
      div_le_div_of_nonneg_left hEs0 (div_pos hEt0 hden) hlower

/-- The same ratio bound stated directly for `Beta(1/2,b)` probabilities.
The common beta normalizing constant cancels exactly. -/
theorem betaMeasure_half_Ioi_ratio_le_endpoint_ratio
    {b t s : ℝ} (hb : 1 < b)
    (ht0 : 0 < t) (hts : t ≤ s) (hs1 : s < 1) :
    (betaMeasure (1 / 2) b).real (Ioi s) /
        (betaMeasure (1 / 2) b).real (Ioi t) ≤
      betaHalfTailEndpoint b s /
        (betaHalfTailEndpoint b t / (1 + 1 / (2 * b * t))) := by
  have ht1 : t < 1 := lt_of_le_of_lt hts hs1
  rw [betaMeasure_half_Ioi_real_eq_tailIntegral_div hb ht0 ht1,
    betaMeasure_half_Ioi_real_eq_tailIntegral_div hb
      (lt_of_lt_of_le ht0 hts) hs1]
  have hbeta : 0 < beta (1 / 2) b :=
    beta_pos (by norm_num) (zero_lt_one.trans hb)
  rw [div_div_div_cancel_right₀ hbeta.ne']
  exact betaHalfTailIntegral_ratio_le_endpoint_ratio hb ht0 hts hs1

end

end LogdetLean.Coherence
