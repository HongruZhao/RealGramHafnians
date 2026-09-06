import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealConditionalSmallBall
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!
# Centered Gaussian scale mixtures

Reusable measure-theoretic facts for the density of a centered Gaussian
whose positive variance is itself random.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real Topology

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The density obtained by mixing centered real Gaussians with variance `q w`. -/
def gaussianScaleMixtureDensity (nu : Measure Omega) (q : Omega → ℝ≥0)
    (x : ℝ) : ℝ :=
  ∫ w, gaussianPDFReal 0 (q w) x ∂nu

/-- The same mixed density in the native `ENNReal` format of `withDensity`. -/
def gaussianScaleMixtureDensityENN (nu : Measure Omega) (q : Omega → ℝ≥0)
    (x : ℝ) : ENNReal :=
  ∫⁻ w, gaussianPDF 0 (q w) x ∂nu

/-- The corresponding realization on a product probability space. -/
def gaussianScaleMixtureObservable (q : Omega → ℝ≥0)
    (p : Omega × ℝ) : ℝ :=
  Real.sqrt (q p.1 : ℝ) * p.2

@[fun_prop] theorem measurable_gaussianScaleMixtureObservable
    {q : Omega → ℝ≥0} (hq : Measurable q) :
    Measurable (gaussianScaleMixtureObservable q) := by
  unfold gaussianScaleMixtureObservable
  fun_prop

theorem measurable_gaussianScaleMixtureKernel
    {q : Omega → ℝ≥0} (hq : Measurable q) :
    Measurable (fun p : Omega × ℝ ↦ gaussianPDFReal 0 (q p.1) p.2) := by
  fun_prop

theorem measurable_gaussianScaleMixtureKernelENN
    {q : Omega → ℝ≥0} (hq : Measurable q) :
    Measurable (fun p : Omega × ℝ ↦ gaussianPDF 0 (q p.1) p.2) := by
  fun_prop

@[fun_prop] theorem measurable_gaussianScaleMixtureDensityENN
    (nu : Measure Omega) [SFinite nu] {q : Omega → ℝ≥0} (hq : Measurable q) :
    Measurable (gaussianScaleMixtureDensityENN nu q) := by
  exact (measurable_gaussianScaleMixtureKernelENN hq).lintegral_prod_left'

theorem gaussianPDFReal_le_zero (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ gaussianPDFReal 0 v 0 := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [gaussianPDFReal, gaussianPDFReal]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.exp_le_exp.mpr
    simp only [sub_zero]
    have hz : -(0 : ℝ) ^ 2 / (2 * (v : ℝ)) = 0 := by norm_num
    rw [hz]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (NNReal.coe_nonneg v))

theorem gaussianPDFReal_zero_at_zero (v : ℝ≥0) :
    gaussianPDFReal 0 v 0 =
      (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (v : ℝ))⁻¹ := by
  unfold gaussianPDFReal
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div,
    Real.exp_zero, mul_one]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  ring

theorem lintegral_gaussianScaleMixturePeak
    (nu : Measure Omega) {q : Omega → ℝ≥0} (hq : Measurable q) :
    (∫⁻ w, ENNReal.ofReal (gaussianPDFReal 0 (q w) 0) ∂nu) =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ *
        ennInverseSqrtMoment nu (fun w ↦ (q w : ℝ)) := by
  simp_rw [gaussianPDFReal_zero_at_zero,
    ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  simpa only [ennInverseSqrtMoment] using
    (lintegral_const_mul (μ := nu)
      (f := fun w ↦ ENNReal.ofReal (Real.sqrt (q w : ℝ))⁻¹)
      (ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹)
      hq.coe_nnreal_real.sqrt.inv.ennreal_ofReal)

theorem integrable_gaussianScaleMixturePeak_of_inverseSqrtMoment_ne_top
    (nu : Measure Omega) {q : Omega → ℝ≥0} (hq : Measurable q)
    (hfinite : ennInverseSqrtMoment nu (fun w ↦ (q w : ℝ)) ≠ ∞) :
    Integrable (fun w ↦ gaussianPDFReal 0 (q w) 0) nu := by
  refine ⟨((measurable_gaussianScaleMixtureKernel hq).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun w ↦ gaussianPDFReal_nonneg 0 (q w) 0),
    lintegral_gaussianScaleMixturePeak nu hq, lt_top_iff_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite

theorem continuous_gaussianPDFReal_zero {v : ℝ≥0} (hv : v ≠ 0) :
    Continuous (gaussianPDFReal 0 v) := by
  unfold gaussianPDFReal
  fun_prop

theorem map_sqrt_mul_standardGaussian_eq_gaussianReal (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x : ℝ ↦ Real.sqrt (v : ℝ) * x) =
      gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
  exact Real.sq_sqrt (NNReal.coe_nonneg v)

/-- A centered Gaussian with an almost surely positive random variance has
the Tonelli mixture of the conditional Gaussian densities as its density. -/
theorem map_gaussianScaleMixtureObservable_eq_withDensity
    (nu : Measure Omega) [SFinite nu] {q : Omega → ℝ≥0} (hq : Measurable q)
    (hqpos : ∀ᵐ w ∂nu, q w ≠ 0) :
    Measure.map (gaussianScaleMixtureObservable q)
        (nu.prod (gaussianReal 0 1)) =
      volume.withDensity (gaussianScaleMixtureDensityENN nu q) := by
  ext s hs
  rw [Measure.map_apply (measurable_gaussianScaleMixtureObservable hq) hs,
    Measure.prod_apply ((measurable_gaussianScaleMixtureObservable hq) hs),
    withDensity_apply _ hs]
  calc
    (∫⁻ w, (gaussianReal 0 1)
          (Prod.mk w ⁻¹' (gaussianScaleMixtureObservable q ⁻¹' s)) ∂nu) =
        ∫⁻ w, (gaussianReal 0 (q w)) s ∂nu := by
      apply lintegral_congr_ae
      filter_upwards [hqpos] with w hw
      rw [show Prod.mk w ⁻¹' (gaussianScaleMixtureObservable q ⁻¹' s) =
          (fun x : ℝ ↦ Real.sqrt (q w : ℝ) * x) ⁻¹' s by rfl,
        ← Measure.map_apply (by fun_prop) hs,
        map_sqrt_mul_standardGaussian_eq_gaussianReal]
    _ = ∫⁻ w, ∫⁻ x in s, gaussianPDF 0 (q w) x ∂volume ∂nu := by
      apply lintegral_congr_ae
      filter_upwards [hqpos] with w hw
      exact gaussianReal_apply 0 hw s
    _ = ∫⁻ x in s, ∫⁻ w, gaussianPDF 0 (q w) x ∂nu ∂volume := by
      exact lintegral_lintegral_swap
        ((measurable_gaussianScaleMixtureKernelENN hq).aemeasurable)
    _ = ∫⁻ x in s, gaussianScaleMixtureDensityENN nu q x ∂volume := rfl

theorem integrable_gaussianScaleMixtureKernel
    (nu : Measure Omega) {q : Omega → ℝ≥0} (hq : Measurable q)
    (hpeak : Integrable (fun w ↦ gaussianPDFReal 0 (q w) 0) nu)
    (x : ℝ) :
    Integrable (fun w ↦ gaussianPDFReal 0 (q w) x) nu := by
  apply hpeak.mono'
  · exact ((measurable_gaussianScaleMixtureKernel hq).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact gaussianPDFReal_le_zero (q w) x

/-- In the finite-peak regime the `ENNReal` density used by `withDensity` is
pointwise the `ofReal` lift of the paper's real-valued density. -/
theorem gaussianScaleMixtureDensityENN_eq_ofReal
    (nu : Measure Omega) {q : Omega → ℝ≥0} (hq : Measurable q)
    (hpeak : Integrable (fun w ↦ gaussianPDFReal 0 (q w) 0) nu)
    (x : ℝ) :
    gaussianScaleMixtureDensityENN nu q x =
      ENNReal.ofReal (gaussianScaleMixtureDensity nu q x) := by
  unfold gaussianScaleMixtureDensityENN gaussianScaleMixtureDensity
  simp only [gaussianPDF]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_gaussianScaleMixtureKernel nu hq hpeak x)
    (ae_of_all _ fun w ↦ gaussianPDFReal_nonneg 0 (q w) x)]

theorem gaussianScaleMixtureDensity_le_zero
    (nu : Measure Omega) {q : Omega → ℝ≥0} (hq : Measurable q)
    (hpeak : Integrable (fun w ↦ gaussianPDFReal 0 (q w) 0) nu)
    (x : ℝ) :
    gaussianScaleMixtureDensity nu q x ≤ gaussianScaleMixtureDensity nu q 0 := by
  unfold gaussianScaleMixtureDensity
  exact integral_mono
    (integrable_gaussianScaleMixtureKernel nu hq hpeak x) hpeak
    (fun w ↦ gaussianPDFReal_le_zero (q w) x)

theorem gaussianScaleMixtureDensity_nonneg
    (nu : Measure Omega) (q : Omega → ℝ≥0) (x : ℝ) :
    0 ≤ gaussianScaleMixtureDensity nu q x := by
  unfold gaussianScaleMixtureDensity
  exact integral_nonneg fun w ↦ gaussianPDFReal_nonneg 0 (q w) x

theorem continuous_gaussianScaleMixtureDensity
    (nu : Measure Omega) {q : Omega → ℝ≥0} (hq : Measurable q)
    (hqpos : ∀ᵐ w ∂nu, q w ≠ 0)
    (hpeak : Integrable (fun w ↦ gaussianPDFReal 0 (q w) 0) nu) :
    Continuous (gaussianScaleMixtureDensity nu q) := by
  rw [continuous_iff_continuousAt]
  intro x
  unfold gaussianScaleMixtureDensity
  apply tendsto_integral_filter_of_dominated_convergence
      (fun w ↦ gaussianPDFReal 0 (q w) 0)
  · filter_upwards [] with y
    exact ((measurable_gaussianScaleMixtureKernel hq).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with y
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact gaussianPDFReal_le_zero (q w) y
  · exact hpeak
  · filter_upwards [hqpos] with w hw
    exact (continuous_gaussianPDFReal_zero hw).continuousAt

end

end LogdetLean.GramHafnian
