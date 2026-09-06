import LogdetLean.CenteredLogBetaLaw
import LogdetLean.BetaCumulantSeries
/-!
# Exact centering and standardization of the null log determinant

This module evaluates the first moment of `logBetaSumLaw`, defines the exact
finite statistic denoted mathematically by `Z_{0,m,p}`, and proves that the
statistic computed from a centered Gaussian sample has law
`standardizedNullLaw m p`.

## Exact published provenance

* Rouault (2007), equation (2.10), printed p. 189, gives the exact Beta
  Mellin quotient from which the log-Beta mean is differentiated.
* Junshan Xie and Gaoming Sun, “High-dimensional Edgeworth expansion of the
  determinant of sample correlation matrix and its error bound,”
  *Stochastics* **93**(3) (2021), equations (4)--(7), pp. 430--431,
  DOI `10.1080/17442508.2020.1744604`, give the exact finite mean, variance,
  and cumulants in the corresponding notation.
* Johannes Heiny, Samuel Johnston, and Joscha Prochno, “Thin-shell theory for
  rotationally invariant random simplices,” *Electronic Journal of
  Probability* **27** (2022), Lemmas 3.3--3.5, pp. 14--16,
  DOI `10.1214/21-EJP734`, record the same general log-Beta mean and centered
  moment identities.
* NIST DLMF 5.2.2 and 5.7.6 identify the digamma function and its Euler
  series: <https://dlmf.nist.gov/5>.

The Lean proof is an independent rederivation: it differentiates the already
proved Beta Mellin quotient, uses the project's proved Euler-series formula
for `(log Gamma)'`, and then proves finite convolution additivity directly.
The names and totalized definitions below are formalization choices, not
verbatim theorem statements from those sources.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators MeasureTheory

noncomputable section

set_option linter.style.haveILetI false

private def centerShiftedLogGammaDifference
    (alpha betaShape t : ℝ) : ℝ :=
  Real.log (Real.Gamma (alpha + t)) -
    Real.log (Real.Gamma (alpha + betaShape + t)) -
    Real.log (Real.Gamma alpha) +
    Real.log (Real.Gamma (alpha + betaShape))

private theorem betaLogCGF_eq_centerShiftedLogGammaDifference
    {alpha betaShape t : ℝ} (halpha : 0 < alpha) (hbeta : 0 < betaShape)
    (halphat : 0 < alpha + t) :
    betaLogCGF alpha betaShape t =
      centerShiftedLogGammaDifference alpha betaShape t := by
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
  unfold ProbabilityTheory.beta centerShiftedLogGammaDifference
  rw [Real.log_div (mul_ne_zero hGamma_alphat hGamma_beta)
      hGamma_alphatbeta,
    Real.log_mul hGamma_alphat hGamma_beta,
    Real.log_div (mul_ne_zero hGamma_alpha hGamma_beta)
      hGamma_alphabeta,
    Real.log_mul hGamma_alpha hGamma_beta]
  ring_nf

private theorem betaLogCGF_eventuallyEq_centerShiftedLogGammaDifference
    {alpha betaShape : ℝ} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    betaLogCGF alpha betaShape =ᶠ[nhds 0]
      centerShiftedLogGammaDifference alpha betaShape := by
  filter_upwards [Ioi_mem_nhds (show -alpha < (0 : ℝ) by linarith)] with t ht
  have ht' : -alpha < t := ht
  exact betaLogCGF_eq_centerShiftedLogGammaDifference halpha hbeta (by linarith)

private theorem hasDerivAt_logGamma_center
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Real.log ∘ Real.Gamma) (digammaSeries x) x := by
  have hd : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x := by
    exact (Real.differentiableAt_Gamma (fun n ↦ by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)).log (Real.Gamma_pos_of_pos hx).ne'
  rw [← deriv_logGamma_eq_digammaSeries hx]
  exact hd.hasDerivAt

private theorem hasDerivAt_centerShiftedLogGammaDifference
    {alpha betaShape t : ℝ} (halphat : 0 < alpha + t)
    (hbeta : 0 < betaShape) :
    HasDerivAt (centerShiftedLogGammaDifference alpha betaShape)
      (digammaSeries (alpha + t) -
        digammaSeries (alpha + betaShape + t)) t := by
  have hshiftAlpha : HasDerivAt (fun s : ℝ ↦ alpha + s) 1 t :=
    (hasDerivAt_id t).const_add alpha
  have hshiftAlphaBeta : HasDerivAt
      (fun s : ℝ ↦ alpha + betaShape + s) 1 t :=
    (hasDerivAt_id t).const_add (alpha + betaShape)
  have hleft : HasDerivAt
      (fun s : ℝ ↦ Real.log (Real.Gamma (alpha + s)))
      (digammaSeries (alpha + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_logGamma_center halphat).comp t hshiftAlpha
  have hright : HasDerivAt
      (fun s : ℝ ↦ Real.log (Real.Gamma (alpha + betaShape + s)))
      (digammaSeries (alpha + betaShape + t)) t := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_logGamma_center (by linarith)).comp t hshiftAlphaBeta
  have h := ((hleft.sub hright).sub
    (hasDerivAt_const t (Real.log (Real.Gamma alpha)))).add
    (hasDerivAt_const t (Real.log (Real.Gamma (alpha + betaShape))))
  change HasDerivAt
    (fun s : ℝ ↦ Real.log (Real.Gamma (alpha + s)) -
      Real.log (Real.Gamma (alpha + betaShape + s)) -
      Real.log (Real.Gamma alpha) +
      Real.log (Real.Gamma (alpha + betaShape)))
    ((digammaSeries (alpha + t) -
      digammaSeries (alpha + betaShape + t)) - 0 + 0) t at h
  unfold centerShiftedLogGammaDifference
  simpa only [sub_zero, add_zero] using h

/-- The first derivative of the exact log-Beta Mellin quotient is the
digamma difference `psi(alpha)-psi(alpha+betaShape)`. -/
theorem deriv_betaLogCGF_zero_eq_digammaSeries_sub
    {alpha betaShape : ℝ} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    deriv (betaLogCGF alpha betaShape) 0 =
      digammaSeries alpha - digammaSeries (alpha + betaShape) := by
  calc
    deriv (betaLogCGF alpha betaShape) 0 =
        deriv (centerShiftedLogGammaDifference alpha betaShape) 0 :=
      (betaLogCGF_eventuallyEq_centerShiftedLogGammaDifference
        halpha hbeta).deriv_eq
    _ = digammaSeries (alpha + 0) -
          digammaSeries (alpha + betaShape + 0) :=
      (hasDerivAt_centerShiftedLogGammaDifference
        (by simpa using halpha) hbeta).deriv
    _ = digammaSeries alpha - digammaSeries (alpha + betaShape) := by ring_nf

/-- Exact mean of the logarithm of a beta variable. -/
theorem integral_log_betaMeasure_eq_digammaSeries_sub
    {alpha betaShape : ℝ} (halpha : 0 < alpha) (hbeta : 0 < betaShape) :
    ∫ x, Real.log x ∂betaMeasure alpha betaShape =
      digammaSeries alpha - digammaSeries (alpha + betaShape) := by
  rw [integral_log_betaMeasure_eq_deriv_betaLogCGF halpha hbeta,
    deriv_betaLogCGF_zero_eq_digammaSeries_sub halpha hbeta]

/-- Exact mean of one mapped factor `logBetaLaw m j`. -/
theorem integral_id_logBetaLaw_eq_digammaSeries_sub
    {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) :
    ∫ x, x ∂logBetaLaw m j =
      digammaSeries (betaShapeA m j) -
        digammaSeries (betaShapeTotal m) := by
  have hA : 0 < betaShapeA m j := betaShapeA_pos_of_le hjm
  have hB : 0 < betaShapeB j := betaShapeB_pos_of_two_le hj
  unfold logBetaLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_log_betaMeasure_eq_digammaSeries_sub hA hB,
    betaShapeA_add_betaShapeB_eq_total]

/-- The exact finite digamma expression for the null centering. -/
def nullCenterDigammaSeries (m p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 p,
    (digammaSeries (betaShapeA m j) -
      digammaSeries (betaShapeTotal m))

/-- The first moment of the convolved law is the finite sum of the individual
log-Beta means. -/
theorem nullCenter_eq_sum_integral_logBetaLaw
    {m p : ℕ} (hpm : p ≤ m) :
    nullCenter m p =
      ∑ j ∈ Finset.Icc 2 p, ∫ x, x ∂logBetaLaw m j := by
  induction p with
  | zero => simp [nullCenter, logBetaSumLaw]
  | succ p ih =>
      by_cases hp2 : 2 ≤ p + 1
      · haveI : IsProbabilityMeasure (logBetaSumLaw m p) :=
          isProbabilityMeasure_logBetaSumLaw (by omega)
        haveI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm hp2
        have hprev : Integrable (fun x : ℝ ↦ x) (logBetaSumLaw m p) :=
          (memLp_id_logBetaSumLaw (m := m) (p := p) (by omega)).integrable
            (by norm_num)
        have hfactor : Integrable (fun x : ℝ ↦ x) (logBetaLaw m (p + 1)) :=
          (memLp_id_logBetaLaw (m := m) (j := p + 1) hpm hp2).integrable
            (by norm_num)
        rw [nullCenter, logBetaSumLaw, if_pos hp2]
        rw [integral_id_conv hprev hfactor]
        change nullCenter m p + (∫ x, x ∂logBetaLaw m (p + 1)) = _
        rw [ih (by omega), Finset.sum_Icc_succ_top hp2]
      · have hp0 : p = 0 := by omega
        subst p
        simp [nullCenter, logBetaSumLaw]

/-- Exact evaluation of the probabilistically defined centering. -/
theorem nullCenter_eq_nullCenterDigammaSeries
    {m p : ℕ} (hpm : p ≤ m) :
    nullCenter m p = nullCenterDigammaSeries m p := by
  rw [nullCenter_eq_sum_integral_logBetaLaw hpm]
  unfold nullCenterDigammaSeries
  apply Finset.sum_congr rfl
  intro j hj
  have hjbounds := Finset.mem_Icc.mp hj
  exact integral_id_logBetaLaw_eq_digammaSeries_sub
    (le_trans hjbounds.2 hpm) hjbounds.1

/-- The actual centered Gaussian sample log-determinant, not merely the
constructed convolution law, has the explicit finite digamma mean. -/
theorem integral_log_centeredSampleCorrelationDet_eq_nullCenterDigammaSeries
    (m p : ℕ) (hpm : p ≤ m) :
    (∫ z, Real.log (centeredSampleCorrelationDet (m + 1) p z)
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p) =
      nullCenterDigammaSeries m p := by
  let L : NestedTuple (ObservationSpace (m + 1)) p → ℝ :=
    Real.log ∘ centeredSampleCorrelationDet (m + 1) p
  have hL : Measurable L := measurable_log.comp
    (measurable_centeredSampleCorrelationDet (Nat.zero_lt_succ m))
  calc
    (∫ z, Real.log (centeredSampleCorrelationDet (m + 1) p z)
        ∂nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
        ∫ x, x ∂Measure.map L
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) p) := by
      rw [integral_map hL.aemeasurable (by fun_prop)]
      rfl
    _ = ∫ x, x ∂logBetaSumLaw m p := by
      rw [map_log_centeredSampleCorrelationDet_succ_eq_logBetaSumLaw m p hpm]
    _ = nullCenter m p := rfl
    _ = nullCenterDigammaSeries m p :=
      nullCenter_eq_nullCenterDigammaSeries hpm

/-- The exact standardized sample statistic denoted mathematically by
`Z_{0,m,p}`.  It uses only the explicit finite digamma and trigamma series,
not abstract expectations. -/
def Z0mpStatistic (m p : ℕ) :
    NestedTuple (ObservationSpace (m + 1)) p → ℝ :=
  fun z ↦
    (Real.log (centeredSampleCorrelationDet (m + 1) p z) -
      nullCenterDigammaSeries m p) /
      Real.sqrt (nullVSeries m p)

/-- The exact `Z_{0,m,p}` statistic is measurable. -/
theorem measurable_Z0mpStatistic (m p : ℕ) :
    Measurable (Z0mpStatistic m p) := by
  unfold Z0mpStatistic
  have hdet : Measurable (centeredSampleCorrelationDet (m + 1) p) :=
    measurable_centeredSampleCorrelationDet (Nat.zero_lt_succ m)
  exact ((measurable_log.comp hdet).sub measurable_const).div_const _

/-- In the nontrivial admissible range, the standardizing denominator is
strictly positive. -/
theorem sqrt_nullVSeries_pos {m p : ℕ} (h : Admissible m p) :
    0 < Real.sqrt (nullVSeries m p) := by
  exact Real.sqrt_pos.2 (nullVSeries_pos h)

/-- The centered second moment of the actual centered Gaussian sample
log-determinant is the explicit finite trigamma expression `nullVSeries`. -/
theorem integral_centered_sq_log_centeredSampleCorrelationDet_eq_nullVSeries
    (m p : ℕ) (hpm : p ≤ m) :
    (∫ z,
      (Real.log (centeredSampleCorrelationDet (m + 1) p z) -
        nullCenterDigammaSeries m p) ^ 2
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p) =
      nullVSeries m p := by
  let L : NestedTuple (ObservationSpace (m + 1)) p → ℝ :=
    Real.log ∘ centeredSampleCorrelationDet (m + 1) p
  have hL : Measurable L := measurable_log.comp
    (measurable_centeredSampleCorrelationDet (Nat.zero_lt_succ m))
  calc
    (∫ z,
        (Real.log (centeredSampleCorrelationDet (m + 1) p z) -
          nullCenterDigammaSeries m p) ^ 2
        ∂nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
        ∫ x, (x - nullCenterDigammaSeries m p) ^ 2
          ∂Measure.map L
            (nestedProductMeasure
              (stdGaussian (ObservationSpace (m + 1))) p) := by
      rw [integral_map hL.aemeasurable (by fun_prop)]
      rfl
    _ = ∫ x, (x - nullCenterDigammaSeries m p) ^ 2
          ∂logBetaSumLaw m p := by
      rw [map_log_centeredSampleCorrelationDet_succ_eq_logBetaSumLaw m p hpm]
    _ = ∫ x, (x - nullCenter m p) ^ 2 ∂logBetaSumLaw m p := by
      rw [nullCenter_eq_nullCenterDigammaSeries hpm]
    _ = nullVariance m p := rfl
    _ = nullVSeries m p := nullVariance_eq_nullVSeries hpm

/-- Exact pushforward law of `Z_{0,m,p}` under the centered Gaussian sample. -/
theorem map_Z0mpStatistic_eq_standardizedNullLaw
    (m p : ℕ) (hpm : p ≤ m) :
    Measure.map (Z0mpStatistic m p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
      standardizedNullLaw m p := by
  unfold Z0mpStatistic
  rw [← nullCenter_eq_nullCenterDigammaSeries hpm,
    ← nullVariance_eq_nullVSeries hpm]
  unfold standardizedNullLaw
  let g : ℝ → ℝ :=
    fun x ↦ (x - nullCenter m p) / Real.sqrt (nullVariance m p)
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hlog : Measurable
      (Real.log ∘ centeredSampleCorrelationDet (m + 1) p) :=
    measurable_log.comp
      (measurable_centeredSampleCorrelationDet (Nat.zero_lt_succ m))
  change Measure.map
      (g ∘ (Real.log ∘ centeredSampleCorrelationDet (m + 1) p))
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p) =
    Measure.map g (logBetaSumLaw m p)
  rw [← Measure.map_map hg hlog]
  rw [map_log_centeredSampleCorrelationDet_succ_eq_logBetaSumLaw m p hpm]

/-- `HasLaw` form of the exact standardization theorem. -/
theorem hasLaw_Z0mpStatistic_standardizedNullLaw
    (m p : ℕ) (hpm : p ≤ m) :
    HasLaw (Z0mpStatistic m p) (standardizedNullLaw m p)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p) := by
  refine ⟨(measurable_Z0mpStatistic m p).aemeasurable, ?_⟩
  exact map_Z0mpStatistic_eq_standardizedNullLaw m p hpm

/-- Bundled end-to-end statement of Steps 1 and 2.  Starting from the actual
centered Gaussian sample-correlation determinant, it records its exact
log-Beta convolution law, explicit mean and variance, positive normalization,
and exact standardized law.  The sole assumptions are `2 ≤ p ≤ m`. -/
theorem centeredSampleCorrelationLogDet_steps_one_two
    (m p : ℕ) (h : Admissible m p) :
    Measure.map (Real.log ∘ centeredSampleCorrelationDet (m + 1) p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
        logBetaSumLaw m p ∧
      (∫ z, Real.log (centeredSampleCorrelationDet (m + 1) p z)
        ∂nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
        nullCenterDigammaSeries m p ∧
      (∫ z,
        (Real.log (centeredSampleCorrelationDet (m + 1) p z) -
          nullCenterDigammaSeries m p) ^ 2
        ∂nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
        nullVSeries m p ∧
      0 < Real.sqrt (nullVSeries m p) ∧
      Measure.map (Z0mpStatistic m p)
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) p) =
        standardizedNullLaw m p := by
  exact ⟨
    map_log_centeredSampleCorrelationDet_succ_eq_logBetaSumLaw m p h.2,
    integral_log_centeredSampleCorrelationDet_eq_nullCenterDigammaSeries
      m p h.2,
    integral_centered_sq_log_centeredSampleCorrelationDet_eq_nullVSeries
      m p h.2,
    sqrt_nullVSeries_pos h,
    map_Z0mpStatistic_eq_standardizedNullLaw m p h.2⟩

end

end LogdetLean
