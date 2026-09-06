import LogdetLean.BetaMellin
import LogdetLean.LogGammaPolygamma
import LogdetLean.ConvolutionMoments
import LogdetLean.NullVA
/-!
# Exact positive-series formulas for log-Beta cumulants

Exact sources for the mathematical identities formalized below are
Xie--Sun (2021), equations (3)--(7), printed pp. 430--431, and
Heiny--Johnston--Prochno (2022), Lemmas 3.3--3.5, printed pp. 14--16.
Rouault (2007), equation (2.10), printed p. 189, supplies the exact Beta
Mellin quotient. The Lean proof independently derives and composes these
identities. See PROVENANCE.md for full citations and scope restrictions.

This file joins two independently proved bridges:

* `BetaMellin` identifies the centered second and third moments of `log X`,
  for `X` beta distributed, with derivatives of the exact beta quotient;
* `LogGammaPolygamma` computes the relevant derivatives of `log Gamma` from
  convergent reciprocal-power series.

The resulting formulas are the single-factor identities used in the exact
computations of `V_{m,p}` and `A_{m,p}`.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set

noncomputable section

private def shiftedLogGammaDifference (alpha betaShape t : Real) : Real :=
  Real.log (Real.Gamma (alpha + t)) -
    Real.log (Real.Gamma (alpha + betaShape + t)) -
    Real.log (Real.Gamma alpha) + Real.log (Real.Gamma (alpha + betaShape))

private def shiftedDigammaDifference (alpha betaShape t : Real) : Real :=
  digammaSeries (alpha + t) - digammaSeries (alpha + betaShape + t)

private def shiftedTrigammaDifference (alpha betaShape t : Real) : Real :=
  trigammaSeries (alpha + t) - trigammaSeries (alpha + betaShape + t)

private def shiftedThirdDifference (alpha betaShape t : Real) : Real :=
  -(negPsiTwoSeries (alpha + t) -
    negPsiTwoSeries (alpha + betaShape + t))

/-- On its natural domain, the log of the beta Mellin quotient is a
difference of four real log-Gamma terms. -/
private theorem betaLogCGF_eq_shiftedLogGammaDifference
    {alpha betaShape t : Real} (halpha : 0 < alpha) (hbeta : 0 < betaShape)
    (halphat : 0 < alpha + t) :
    betaLogCGF alpha betaShape t = shiftedLogGammaDifference alpha betaShape t := by
  have hGamma_alpha : Real.Gamma alpha ≠ 0 :=
    (Real.Gamma_pos_of_pos halpha).ne'
  have hGamma_beta : Real.Gamma betaShape ≠ 0 :=
    (Real.Gamma_pos_of_pos hbeta).ne'
  have hGamma_alphabeta : Real.Gamma (alpha + betaShape) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos halpha hbeta)).ne'
  have hGamma_alphat : Real.Gamma (alpha + t) ≠ 0 :=
    (Real.Gamma_pos_of_pos halphat).ne'
  have hGamma_alphatbeta : Real.Gamma (alpha + t + betaShape) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos halphat hbeta)).ne'
  rw [betaLogCGF, Real.log_div (beta_pos halphat hbeta).ne'
      (beta_pos halpha hbeta).ne']
  unfold ProbabilityTheory.beta shiftedLogGammaDifference
  rw [Real.log_div (mul_ne_zero hGamma_alphat hGamma_beta) hGamma_alphatbeta,
    Real.log_mul hGamma_alphat hGamma_beta,
    Real.log_div (mul_ne_zero hGamma_alpha hGamma_beta) hGamma_alphabeta,
    Real.log_mul hGamma_alpha hGamma_beta]
  ring_nf

/-- The preceding log-Gamma identity holds throughout a neighborhood of
zero, which is exactly what iterated derivatives require. -/
private theorem betaLogCGF_eventuallyEq_shiftedLogGammaDifference
    {alpha betaShape : Real} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    betaLogCGF alpha betaShape =ᶠ[nhds 0]
      shiftedLogGammaDifference alpha betaShape := by
  filter_upwards [Ioi_mem_nhds (show -alpha < (0 : Real) by linarith)] with t ht
  have ht' : -alpha < t := ht
  exact betaLogCGF_eq_shiftedLogGammaDifference halpha hbeta (by linarith)

/-! The next two elementary lemmas let us assemble iterated derivatives from
an explicit chain of ordinary derivatives on an open set.  They avoid any
hidden appeal to a general smoothness theorem. -/

private theorem iteratedDeriv_two_of_hasDerivAt_on_open
    {f f1 f2 : Real -> Real} {s : Set Real} {x : Real}
    (hs : IsOpen s) (hx : x ∈ s)
    (h1 : ∀ y ∈ s, HasDerivAt f (f1 y) y)
    (h2 : ∀ y ∈ s, HasDerivAt f1 (f2 y) y) :
    iteratedDeriv 2 f x = f2 x := by
  have hfirst : iteratedDeriv 1 f =ᶠ[nhds x] f1 := by
    filter_upwards [hs.eventually_mem hx] with y hy
    simpa only [iteratedDeriv_one] using (h1 y hy).deriv
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, hfirst.deriv_eq,
    (h2 x hx).deriv]

private theorem iteratedDeriv_three_of_hasDerivAt_on_open
    {f f1 f2 f3 : Real -> Real} {s : Set Real} {x : Real}
    (hs : IsOpen s) (hx : x ∈ s)
    (h1 : ∀ y ∈ s, HasDerivAt f (f1 y) y)
    (h2 : ∀ y ∈ s, HasDerivAt f1 (f2 y) y)
    (h3 : ∀ y ∈ s, HasDerivAt f2 (f3 y) y) :
    iteratedDeriv 3 f x = f3 x := by
  have hsecond : iteratedDeriv 2 f =ᶠ[nhds x] f2 := by
    filter_upwards [hs.eventually_mem hx] with y hy
    exact iteratedDeriv_two_of_hasDerivAt_on_open hs hy h1 h2
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ, hsecond.deriv_eq,
    (h3 x hx).deriv]

private theorem hasDerivAt_logGamma_eq_digammaSeries
    {x : Real} (hx : 0 < x) :
    HasDerivAt (Real.log ∘ Real.Gamma) (digammaSeries x) x := by
  have hd : DifferentiableAt Real (Real.log ∘ Real.Gamma) x := by
    exact (Real.differentiableAt_Gamma (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)).log (Real.Gamma_pos_of_pos hx).ne'
  rw [← deriv_logGamma_eq_digammaSeries hx]
  exact hd.hasDerivAt

private theorem hasDerivAt_shiftedLogGammaDifference
    {alpha betaShape t : Real} (halphat : 0 < alpha + t)
    (hbeta : 0 < betaShape) :
    HasDerivAt (shiftedLogGammaDifference alpha betaShape)
      (shiftedDigammaDifference alpha betaShape t) t := by
  have hshiftAlpha : HasDerivAt (fun s : Real => alpha + s) 1 t :=
    (hasDerivAt_id t).const_add alpha
  have hshiftAlphaBeta : HasDerivAt
      (fun s : Real => alpha + betaShape + s) 1 t :=
    (hasDerivAt_id t).const_add (alpha + betaShape)
  have hleft : HasDerivAt
      (fun s : Real => Real.log (Real.Gamma (alpha + s)))
      (digammaSeries (alpha + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_logGamma_eq_digammaSeries halphat).comp t hshiftAlpha
  have hright : HasDerivAt
      (fun s : Real => Real.log (Real.Gamma (alpha + betaShape + s)))
      (digammaSeries (alpha + betaShape + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_logGamma_eq_digammaSeries (by linarith)).comp t hshiftAlphaBeta
  have h := ((hleft.sub hright).sub
    (hasDerivAt_const t (Real.log (Real.Gamma alpha)))).add
    (hasDerivAt_const t (Real.log (Real.Gamma (alpha + betaShape))))
  change HasDerivAt
    (fun s : Real => Real.log (Real.Gamma (alpha + s)) -
      Real.log (Real.Gamma (alpha + betaShape + s)) -
      Real.log (Real.Gamma alpha) + Real.log (Real.Gamma (alpha + betaShape)))
    ((digammaSeries (alpha + t) - digammaSeries (alpha + betaShape + t)) - 0 + 0) t at h
  unfold shiftedLogGammaDifference shiftedDigammaDifference
  simpa only [sub_zero, add_zero] using h

private theorem hasDerivAt_shiftedDigammaDifference
    {alpha betaShape t : Real} (halphat : 0 < alpha + t)
    (hbeta : 0 < betaShape) :
    HasDerivAt (shiftedDigammaDifference alpha betaShape)
      (shiftedTrigammaDifference alpha betaShape t) t := by
  have hshiftAlpha : HasDerivAt (fun s : Real => alpha + s) 1 t :=
    (hasDerivAt_id t).const_add alpha
  have hshiftAlphaBeta : HasDerivAt
      (fun s : Real => alpha + betaShape + s) 1 t :=
    (hasDerivAt_id t).const_add (alpha + betaShape)
  have hleft : HasDerivAt (fun s : Real => digammaSeries (alpha + s))
      (trigammaSeries (alpha + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_digammaSeries halphat).comp t hshiftAlpha
  have hright : HasDerivAt
      (fun s : Real => digammaSeries (alpha + betaShape + s))
      (trigammaSeries (alpha + betaShape + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_digammaSeries (by linarith)).comp t hshiftAlphaBeta
  unfold shiftedDigammaDifference shiftedTrigammaDifference
  exact hleft.sub hright

private theorem hasDerivAt_shiftedTrigammaDifference
    {alpha betaShape t : Real} (halphat : 0 < alpha + t)
    (hbeta : 0 < betaShape) :
    HasDerivAt (shiftedTrigammaDifference alpha betaShape)
      (shiftedThirdDifference alpha betaShape t) t := by
  have hshiftAlpha : HasDerivAt (fun s : Real => alpha + s) 1 t :=
    (hasDerivAt_id t).const_add alpha
  have hshiftAlphaBeta : HasDerivAt
      (fun s : Real => alpha + betaShape + s) 1 t :=
    (hasDerivAt_id t).const_add (alpha + betaShape)
  have hleft : HasDerivAt (fun s : Real => trigammaSeries (alpha + s))
      (-negPsiTwoSeries (alpha + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_trigammaSeries halphat).comp t hshiftAlpha
  have hright : HasDerivAt
      (fun s : Real => trigammaSeries (alpha + betaShape + s))
      (-negPsiTwoSeries (alpha + betaShape + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_trigammaSeries (by linarith)).comp t hshiftAlphaBeta
  unfold shiftedTrigammaDifference shiftedThirdDifference
  have h := hleft.sub hright
  change HasDerivAt
    (fun s : Real => trigammaSeries (alpha + s) -
      trigammaSeries (alpha + betaShape + s))
    ((-negPsiTwoSeries (alpha + t)) -
      (-negPsiTwoSeries (alpha + betaShape + t))) t at h
  convert h using 1
  ring

/-- The second derivative of the exact log-beta Mellin quotient is the
difference of two positive trigamma series. -/
theorem iteratedDeriv_two_betaLogCGF_eq_trigammaSeries_sub
    {alpha betaShape : Real} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    iteratedDeriv 2 (betaLogCGF alpha betaShape) 0 =
      trigammaSeries alpha - trigammaSeries (alpha + betaShape) := by
  calc
    iteratedDeriv 2 (betaLogCGF alpha betaShape) 0 =
        iteratedDeriv 2 (shiftedLogGammaDifference alpha betaShape) 0 :=
      (betaLogCGF_eventuallyEq_shiftedLogGammaDifference halpha hbeta).iteratedDeriv_eq 2
    _ = shiftedTrigammaDifference alpha betaShape 0 := by
      apply iteratedDeriv_two_of_hasDerivAt_on_open isOpen_Ioi
        (show (0 : Real) ∈ Ioi (-alpha) by simpa)
      · intro y hy
        have hy' : -alpha < y := hy
        exact hasDerivAt_shiftedLogGammaDifference (by linarith) hbeta
      · intro y hy
        have hy' : -alpha < y := hy
        exact hasDerivAt_shiftedDigammaDifference (by linarith) hbeta
    _ = trigammaSeries alpha - trigammaSeries (alpha + betaShape) := by
      unfold shiftedTrigammaDifference
      congr 2 <;> ring

/-- The third derivative of the exact log-beta Mellin quotient is the
negative difference of two positive reciprocal-cube series. -/
theorem iteratedDeriv_three_betaLogCGF_eq_negPsiTwoSeries_sub
    {alpha betaShape : Real} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    iteratedDeriv 3 (betaLogCGF alpha betaShape) 0 =
      -(negPsiTwoSeries alpha - negPsiTwoSeries (alpha + betaShape)) := by
  calc
    iteratedDeriv 3 (betaLogCGF alpha betaShape) 0 =
        iteratedDeriv 3 (shiftedLogGammaDifference alpha betaShape) 0 :=
      (betaLogCGF_eventuallyEq_shiftedLogGammaDifference halpha hbeta).iteratedDeriv_eq 3
    _ = shiftedThirdDifference alpha betaShape 0 := by
      apply iteratedDeriv_three_of_hasDerivAt_on_open isOpen_Ioi
        (show (0 : Real) ∈ Ioi (-alpha) by simpa)
      · intro y hy
        have hy' : -alpha < y := hy
        exact hasDerivAt_shiftedLogGammaDifference (by linarith) hbeta
      · intro y hy
        have hy' : -alpha < y := hy
        exact hasDerivAt_shiftedDigammaDifference (by linarith) hbeta
      · intro y hy
        have hy' : -alpha < y := hy
        exact hasDerivAt_shiftedTrigammaDifference (by linarith) hbeta
    _ = -(negPsiTwoSeries alpha - negPsiTwoSeries (alpha + betaShape)) := by
      unfold shiftedThirdDifference
      congr 3 <;> ring

/-- Exact variance formula for the logarithm of one beta variable. -/
theorem integral_centered_sq_log_betaMeasure_eq_trigammaSeries_sub
    {alpha betaShape : Real} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    (∫ x, (Real.log x - ∫ y, Real.log y ∂betaMeasure alpha betaShape) ^ 2
      ∂betaMeasure alpha betaShape) =
      trigammaSeries alpha - trigammaSeries (alpha + betaShape) := by
  rw [integral_centered_sq_log_betaMeasure_eq_second_deriv_betaLogCGF halpha hbeta,
    iteratedDeriv_two_betaLogCGF_eq_trigammaSeries_sub halpha hbeta]

/-- Exact centered third-moment formula for the logarithm of one beta
variable. -/
theorem integral_centered_cube_log_betaMeasure_eq_negPsiTwoSeries_sub
    {alpha betaShape : Real} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    (∫ x, (Real.log x - ∫ y, Real.log y ∂betaMeasure alpha betaShape) ^ 3
      ∂betaMeasure alpha betaShape) =
      -(negPsiTwoSeries alpha - negPsiTwoSeries (alpha + betaShape)) := by
  rw [integral_centered_cube_log_betaMeasure_eq_third_deriv_betaLogCGF halpha hbeta,
    iteratedDeriv_three_betaLogCGF_eq_negPsiTwoSeries_sub halpha hbeta]

/-- The negative centered third moment is the positive reciprocal-cube
series difference used in `A_{m,p}`. -/
theorem neg_integral_centered_cube_log_betaMeasure_eq_negPsiTwoSeries_sub
    {alpha betaShape : Real} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    -(∫ x, (Real.log x - ∫ y, Real.log y ∂betaMeasure alpha betaShape) ^ 3
      ∂betaMeasure alpha betaShape) =
      negPsiTwoSeries alpha - negPsiTwoSeries (alpha + betaShape) := by
  rw [integral_centered_cube_log_betaMeasure_eq_negPsiTwoSeries_sub halpha hbeta]
  ring

/-- The two beta shapes of every Bartlett factor add to the common value
`m/2`. -/
theorem betaShapeA_add_betaShapeB_eq_total (m j : Nat) :
    betaShapeA m j + betaShapeB j = betaShapeTotal m := by
  unfold betaShapeA betaShapeB betaShapeTotal
  ring

/-- Exact positive-series formula for the variance of one mapped log-beta
factor in the recursively convolved null law. -/
theorem logBetaVariance_eq_trigammaSeries_sub
    {m j : Nat} (hjm : j ≤ m) (hj : 2 ≤ j) :
    logBetaVariance m j =
      trigammaSeries (betaShapeA m j) - trigammaSeries (betaShapeTotal m) := by
  have hA : 0 < betaShapeA m j := betaShapeA_pos_of_le hjm
  have hB : 0 < betaShapeB j := betaShapeB_pos_of_two_le hj
  unfold logBetaVariance logBetaLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_centered_sq_log_betaMeasure_eq_trigammaSeries_sub hA hB,
    betaShapeA_add_betaShapeB_eq_total]

/-- Exact positive-series formula for minus the centered third moment of one
mapped log-beta factor. -/
theorem logBetaThirdMagnitude_eq_negPsiTwoSeries_sub
    {m j : Nat} (hjm : j ≤ m) (hj : 2 ≤ j) :
    logBetaThirdMagnitude m j =
      negPsiTwoSeries (betaShapeA m j) - negPsiTwoSeries (betaShapeTotal m) := by
  have hA : 0 < betaShapeA m j := betaShapeA_pos_of_le hjm
  have hB : 0 < betaShapeB j := betaShapeB_pos_of_two_le hj
  unfold logBetaThirdMagnitude logBetaLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [neg_integral_centered_cube_log_betaMeasure_eq_negPsiTwoSeries_sub hA hB,
    betaShapeA_add_betaShapeB_eq_total]

/-- The exact variance of the convolved null log-determinant law is the
finite positive series `nullVSeries`. -/
theorem nullVariance_eq_nullVSeries {m p : Nat} (hpm : p ≤ m) :
    nullVariance m p = nullVSeries m p := by
  rw [nullVariance_eq_sum_logBetaVariance hpm]
  unfold nullVSeries
  apply Finset.sum_congr rfl
  intro j hj
  have hjbounds := Finset.mem_Icc.mp hj
  exact logBetaVariance_eq_trigammaSeries_sub
    (le_trans hjbounds.2 hpm) hjbounds.1

/-- Minus the exact centered third moment of the convolved null law is the
finite positive series `nullASeries`. -/
theorem nullThirdMagnitude_eq_nullASeries {m p : Nat} (hpm : p ≤ m) :
    nullThirdMagnitude m p = nullASeries m p := by
  rw [nullThirdMagnitude_eq_sum_logBetaThirdMagnitude hpm]
  unfold nullASeries
  apply Finset.sum_congr rfl
  intro j hj
  have hjbounds := Finset.mem_Icc.mp hj
  exact logBetaThirdMagnitude_eq_negPsiTwoSeries_sub
    (le_trans hjbounds.2 hpm) hjbounds.1

/-- Consequently the probabilistically defined standardized third-cumulant
magnitude is exactly the directly computed positive-series ratio. -/
theorem nullSkewScale_eq_nullLambdaSeries {m p : Nat} (hpm : p ≤ m) :
    nullSkewScale m p = nullLambdaSeries m p := by
  unfold nullSkewScale nullLambdaSeries
  rw [nullVariance_eq_nullVSeries hpm, nullThirdMagnitude_eq_nullASeries hpm]

end

end LogdetLean
