import RealGramHafnians.Proofs.SharpRealConstant
import RealGramHafnians.Proofs.SharpRealGaussianMixture
/-!
# Density of the real Gaussian Gram-hafnian observable

This module turns the last-column conditional Gaussian law into an actual
Lebesgue density for the literal Gram-hafnian observable.  Its analytic
input is the negative-half moment proved by row suspension.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Real ENNReal NNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 5000000

/-- The conditional variance, bundled as a nonnegative real. -/
def pastRealCofactorVarianceNNReal {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → Fin k → ℝ) : ℝ≥0 :=
  ⟨pastRealCofactorV hr A, pastRealCofactorV_nonneg hr A⟩

@[fun_prop]
theorem measurable_pastRealCofactorVarianceNNReal {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastRealCofactorVarianceNNReal (k := k) hr) := by
  exact (measurable_pastRealCofactorV hr).subtype_mk

/-- Every centered Gaussian density is pointwise bounded by its value at
the origin, including the zero-variance convention used by mathlib. -/
theorem gaussianPDFReal_zero_variance_le_at_zero (v : ℝ≥0) (z : ℝ) :
    gaussianPDFReal 0 v z ≤ gaussianPDFReal 0 v 0 := by
  exact gaussianPDFReal_le_zero v z

/-- The height at zero separates into the universal normalizing constant
and the inverse standard deviation. -/
theorem gaussianPDFReal_zero_at_zero_eq_inv_sqrt (v : ℝ≥0) :
    gaussianPDFReal 0 v 0 =
      (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (v : ℝ))⁻¹ := by
  exact gaussianPDFReal_zero_at_zero v

/-- The centered Gaussian scale-mixture candidate density for the literal
real Gram-hafnian observable. -/
def sharpRealGramHafnianDensity (r k : ℕ) (hr : 1 ≤ r) (z : ℝ) : ℝ :=
  ∫ A, gaussianPDFReal 0 (pastRealCofactorVarianceNNReal hr A) z
    ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k)

theorem sharpRealGramHafnianDensity_eq_gaussianScaleMixtureDensity
    (r k : ℕ) (hr : 1 ≤ r) :
    sharpRealGramHafnianDensity r k hr =
      gaussianScaleMixtureDensity
        (Measure.pi fun _ : OddCofactorIndex r hr ↦
          standardRealGaussianVectorMeasure k)
        (pastRealCofactorVarianceNNReal hr) := by
  rfl

/-- The conditional variance is nonzero almost surely in the literal range. -/
theorem ae_pastRealCofactorVarianceNNReal_ne_zero
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k),
      pastRealCofactorVarianceNNReal hr A ≠ 0 := by
  filter_upwards [ae_pastRealCofactorV_pos_standardRealGaussian hr hk]
    with A hA
  intro hzero
  have hcoe := congrArg ((↑) : ℝ≥0 → ℝ) hzero
  change pastRealCofactorV hr A = 0 at hcoe
  exact hA.ne' hcoe

/-- The verified Gamma-product estimate makes the negative-half moment
finite, not merely bounded in the extended nonnegative reals. -/
theorem sharpRealCofactorInverseSqrtMoment_lt_top
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    sharpRealCofactorInverseSqrtMoment n k hn < ∞ := by
  calc
    sharpRealCofactorInverseSqrtMoment n k hn ≤
        sharpRealGammaCoefficient n k :=
      sharpRealCofactorInverseSqrtMoment_le_coefficient hn hk hdim
    _ = ENNReal.ofReal (sharpRealGammaCoefficientReal n k) :=
      sharpRealGammaCoefficient_eq_ofReal hn hk hdim
    _ < ∞ := ENNReal.ofReal_lt_top

/-- Integrability of the inverse conditional standard deviation. -/
theorem integrable_pastRealCofactorV_inverseSqrt
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    Integrable
      (fun A : OddCofactorIndex n hn → Fin k → ℝ ↦
        (Real.sqrt (pastRealCofactorV hn A))⁻¹)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦
        standardRealGaussianVectorMeasure k) := by
  let nu : Measure (OddCofactorIndex n hn → Fin k → ℝ) :=
    Measure.pi fun _ : OddCofactorIndex n hn ↦
      standardRealGaussianVectorMeasure k
  let g : (OddCofactorIndex n hn → Fin k → ℝ) → ℝ :=
    fun A ↦ (Real.sqrt (pastRealCofactorV hn A))⁻¹
  have hgmeas : Measurable g := by
    dsimp [g]
    fun_prop
  have hgnonneg : ∀ A, 0 ≤ g A := by
    intro A
    dsimp [g]
    positivity
  refine ⟨hgmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hgnonneg)]
  simpa [nu, g, sharpRealCofactorInverseSqrtMoment,
    ennInverseSqrtMoment] using
      sharpRealCofactorInverseSqrtMoment_lt_top hn hk hdim

/-- The conditional Gaussian peak is integrable in the full theorem range. -/
theorem integrable_pastRealCofactorGaussianPeak
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    Integrable
      (fun A : OddCofactorIndex n hn → Fin k → ℝ ↦
        gaussianPDFReal 0 (pastRealCofactorVarianceNNReal hn A) 0)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦
        standardRealGaussianVectorMeasure k) := by
  have hinv := integrable_pastRealCofactorV_inverseSqrt hn hk hdim
  convert hinv.const_mul (Real.sqrt (2 * Real.pi))⁻¹ using 1
  funext A
  rw [gaussianPDFReal_zero_at_zero_eq_inv_sqrt]
  rfl

/-- The literal mixture density is continuous. -/
theorem continuous_sharpRealGramHafnianDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    Continuous (sharpRealGramHafnianDensity n k hn) := by
  rw [sharpRealGramHafnianDensity_eq_gaussianScaleMixtureDensity]
  exact continuous_gaussianScaleMixtureDensity
    (Measure.pi fun _ : OddCofactorIndex n hn ↦
      standardRealGaussianVectorMeasure k)
    (measurable_pastRealCofactorVarianceNNReal hn)
    (ae_pastRealCofactorVarianceNNReal_ne_zero hn hdim)
    (integrable_pastRealCofactorGaussianPeak hn hk hdim)

/-- The literal density is nonnegative and attains its pointwise maximum at
the origin. -/
theorem sharpRealGramHafnianDensity_nonneg_and_le_zero
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) (z : ℝ) :
    0 ≤ sharpRealGramHafnianDensity n k hn z ∧
      sharpRealGramHafnianDensity n k hn z ≤
        sharpRealGramHafnianDensity n k hn 0 := by
  rw [sharpRealGramHafnianDensity_eq_gaussianScaleMixtureDensity]
  constructor
  · exact gaussianScaleMixtureDensity_nonneg
      (Measure.pi fun _ : OddCofactorIndex n hn ↦
        standardRealGaussianVectorMeasure k)
      (pastRealCofactorVarianceNNReal hn) z
  · exact gaussianScaleMixtureDensity_le_zero
      (Measure.pi fun _ : OddCofactorIndex n hn ↦
        standardRealGaussianVectorMeasure k)
      (measurable_pastRealCofactorVarianceNNReal hn)
      (integrable_pastRealCofactorGaussianPeak hn hk hdim) z

/-- Real integral form of the verified inverse-half-moment estimate. -/
theorem integral_pastRealCofactorV_inverseSqrt_le_coefficientReal
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    (∫ A : OddCofactorIndex n hn → Fin k → ℝ,
      (Real.sqrt (pastRealCofactorV hn A))⁻¹
      ∂(Measure.pi fun _ : OddCofactorIndex n hn ↦
        standardRealGaussianVectorMeasure k)) ≤
      sharpRealGammaCoefficientReal n k := by
  let nu : Measure (OddCofactorIndex n hn → Fin k → ℝ) :=
    Measure.pi fun _ : OddCofactorIndex n hn ↦
      standardRealGaussianVectorMeasure k
  let g : (OddCofactorIndex n hn → Fin k → ℝ) → ℝ :=
    fun A ↦ (Real.sqrt (pastRealCofactorV hn A))⁻¹
  have hgint : Integrable g nu := by
    simpa [nu, g] using
      integrable_pastRealCofactorV_inverseSqrt hn hk hdim
  have hgnonneg : ∀ᵐ A ∂nu, 0 ≤ g A :=
    Filter.Eventually.of_forall fun A ↦ by
      dsimp [g]
      positivity
  have hlintegral :
      ENNReal.ofReal (∫ A, g A ∂nu) =
        sharpRealCofactorInverseSqrtMoment n k hn := by
    rw [ofReal_integral_eq_lintegral_ofReal hgint hgnonneg]
    rfl
  have hENN :
      ENNReal.ofReal (∫ A, g A ∂nu) ≤
        ENNReal.ofReal (sharpRealGammaCoefficientReal n k) := by
    rw [hlintegral, ← sharpRealGammaCoefficient_eq_ofReal hn hk hdim]
    exact sharpRealCofactorInverseSqrtMoment_le_coefficient hn hk hdim
  have hcoeffnonneg :=
    sharpRealGammaCoefficientReal_nonneg hn hk hdim
  have hreal := (ENNReal.ofReal_le_ofReal_iff hcoeffnonneg).mp hENN
  simpa [nu, g] using hreal

/-- Quantitative peak bound in the exact real Gamma-product normalization. -/
theorem sharpRealGramHafnianDensity_zero_le_coefficientReal
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    sharpRealGramHafnianDensity n k hn 0 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        sharpRealGammaCoefficientReal n k := by
  unfold sharpRealGramHafnianDensity
  simp_rw [gaussianPDFReal_zero_at_zero_eq_inv_sqrt,
    pastRealCofactorVarianceNNReal]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_pastRealCofactorV_inverseSqrt_le_coefficientReal hn hk hdim)
    (by positivity)

/-! ## Identification of the literal pushforward law -/

/-- The last-column conditional linear form has the same unconditional law
as the scalar Gaussian scale-mixture realization. -/
theorem map_conditionalPastRealLinearForm_eq_gaussianScaleMixtureObservable
    {n k : ℕ} (hn : 1 ≤ n) :
    Measure.map
        (conditionalRealLinearForm (pastRealCofactorCombination hn))
        ((Measure.pi fun _ : OddCofactorIndex n hn ↦
            standardRealGaussianVectorMeasure k).prod
          (standardRealGaussianVectorMeasure k)) =
      Measure.map
        (gaussianScaleMixtureObservable
          (pastRealCofactorVarianceNNReal hn))
        ((Measure.pi fun _ : OddCofactorIndex n hn ↦
            standardRealGaussianVectorMeasure k).prod
          (gaussianReal 0 1)) := by
  let nu : Measure (OddCofactorIndex n hn → Fin k → ℝ) :=
    Measure.pi fun _ : OddCofactorIndex n hn ↦
      standardRealGaussianVectorMeasure k
  let mu : Measure (Fin k → ℝ) := standardRealGaussianVectorMeasure k
  let y := pastRealCofactorCombination (k := k) hn
  let q := pastRealCofactorVarianceNNReal (k := k) hn
  have hy : Measurable y := measurable_pastRealCofactorCombination hn
  have hq : Measurable q := measurable_pastRealCofactorVarianceNNReal hn
  ext s hs
  have hleft : MeasurableSet
      (conditionalRealLinearForm y ⁻¹' s) :=
    hs.preimage (measurable_conditionalRealLinearForm hy)
  have hright : MeasurableSet
      (gaussianScaleMixtureObservable q ⁻¹' s) :=
    hs.preimage (measurable_gaussianScaleMixtureObservable hq)
  rw [Measure.map_apply (measurable_conditionalRealLinearForm hy) hs,
    Measure.map_apply (measurable_gaussianScaleMixtureObservable hq) hs,
    Measure.prod_apply hleft, Measure.prod_apply hright]
  apply lintegral_congr
  intro A
  change mu ((iidRealTransposeLinearForm (y A)) ⁻¹' s) =
    (gaussianReal 0 1)
      ((fun x : ℝ ↦ Real.sqrt (q A : ℝ) * x) ⁻¹' s)
  rw [← Measure.map_apply (measurable_iidRealTransposeLinearForm (y A)) hs,
    ← Measure.map_apply (by fun_prop) hs]
  have hqA : (q A : ℝ) = realCoefficientEnergy (y A) := by
    change pastRealCofactorV hn A =
      realCoefficientEnergy (pastRealCofactorCombination hn A)
    exact pastRealCofactorV_eq_realCoefficientEnergy hn A
  rw [hqA]
  have hlaw := map_iidRealTransposeLinearForm_eq_scaled_realGaussian (y A)
  have hlawSet := congrArg (fun m : Measure ℝ ↦ m s) hlaw
  simpa [mu, standardRealGaussianVectorMeasure, smul_eq_mul] using hlawSet

/-- The literal Gram-hafnian pushforward is the scalar scale-mixture law. -/
theorem map_realGramHafnianObservable_eq_gaussianScaleMixtureObservable
    {n k : ℕ} (hn : 1 ≤ n) :
    Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) =
      Measure.map
        (gaussianScaleMixtureObservable
          (pastRealCofactorVarianceNNReal hn))
        ((Measure.pi fun _ : OddCofactorIndex n hn ↦
            standardRealGaussianVectorMeasure k).prod
          (gaussianReal 0 1)) := by
  let nu : Measure (OddCofactorIndex n hn → Fin k → ℝ) :=
    Measure.pi fun _ : OddCofactorIndex n hn ↦
      standardRealGaussianVectorMeasure k
  let mu : Measure (Fin k → ℝ) := standardRealGaussianVectorMeasure k
  let e := realLastColumnProductEquiv n k hn
  have he := measurePreserving_realLastColumnProductEquiv n k hn
  calc
    Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) =
      Measure.map
        (conditionalRealLinearForm (pastRealCofactorCombination hn))
        (nu.prod mu) := by
          rw [← he.map_eq, Measure.map_map]
          · congr 1
            funext p
            exact
              realGramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm
                hn p
          · exact measurable_realGramHafnianObservable n k
          · exact e.measurable
    _ = Measure.map
        (gaussianScaleMixtureObservable
          (pastRealCofactorVarianceNNReal hn))
        ((Measure.pi fun _ : OddCofactorIndex n hn ↦
            standardRealGaussianVectorMeasure k).prod
          (gaussianReal 0 1)) := by
      simpa [nu, mu] using
        map_conditionalPastRealLinearForm_eq_gaussianScaleMixtureObservable
          (k := k) hn

/-- Native `ENNReal` density identity for the literal observable. -/
theorem map_realGramHafnianObservable_eq_withDensityENN
    {n k : ℕ} (hn : 1 ≤ n) (hdim : 2 * n - 1 ≤ k) :
    Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) =
      volume.withDensity
        (gaussianScaleMixtureDensityENN
          (Measure.pi fun _ : OddCofactorIndex n hn ↦
            standardRealGaussianVectorMeasure k)
          (pastRealCofactorVarianceNNReal hn)) := by
  rw [map_realGramHafnianObservable_eq_gaussianScaleMixtureObservable hn]
  exact map_gaussianScaleMixtureObservable_eq_withDensity
    (Measure.pi fun _ : OddCofactorIndex n hn ↦
      standardRealGaussianVectorMeasure k)
    (measurable_pastRealCofactorVarianceNNReal hn)
    (ae_pastRealCofactorVarianceNNReal_ne_zero hn hdim)

/-- The native extended density agrees pointwise with `ofReal` of the
Bochner-integral density. -/
theorem gaussianScaleMixtureDensityENN_eq_ofReal_sharpRealDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) (z : ℝ) :
    gaussianScaleMixtureDensityENN
        (Measure.pi fun _ : OddCofactorIndex n hn ↦
          standardRealGaussianVectorMeasure k)
        (pastRealCofactorVarianceNNReal hn) z =
      ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z) := by
  have hint := integrable_gaussianScaleMixtureKernel
    (Measure.pi fun _ : OddCofactorIndex n hn ↦
      standardRealGaussianVectorMeasure k)
    (measurable_pastRealCofactorVarianceNNReal hn)
    (integrable_pastRealCofactorGaussianPeak hn hk hdim) z
  have hnonneg :
      ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex n hn ↦
        standardRealGaussianVectorMeasure k),
        0 ≤ gaussianPDFReal 0 (pastRealCofactorVarianceNNReal hn A) z :=
    Filter.Eventually.of_forall fun A ↦
      gaussianPDFReal_nonneg 0 (pastRealCofactorVarianceNNReal hn A) z
  symm
  simpa [sharpRealGramHafnianDensity, gaussianScaleMixtureDensityENN,
    gaussianPDF] using
      ofReal_integral_eq_lintegral_ofReal hint hnonneg

/-- The real-valued continuous function above is an actual Lebesgue density
of the literal real Gram-hafnian observable. -/
theorem map_realGramHafnianObservable_eq_withDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) =
      volume.withDensity
        (fun z ↦ ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z)) := by
  rw [map_realGramHafnianObservable_eq_withDensityENN hn hdim]
  congr 1
  funext z
  exact gaussianScaleMixtureDensityENN_eq_ofReal_sharpRealDensity
    hn hk hdim z

/-- The literal density has total mass one and is Lebesgue integrable. -/
theorem integrable_sharpRealGramHafnianDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    Integrable (sharpRealGramHafnianDensity n k hn) volume := by
  have hcontinuous :=
    continuous_sharpRealGramHafnianDensity hn hk hdim
  have hnonneg : ∀ᵐ z ∂volume,
      0 ≤ sharpRealGramHafnianDensity n k hn z :=
    Filter.Eventually.of_forall fun z ↦
      (sharpRealGramHafnianDensity_nonneg_and_le_zero
        hn hk hdim z).1
  have hmap := map_realGramHafnianObservable_eq_withDensity hn hk hdim
  have hmass := congrArg (fun mu : Measure ℝ ↦ mu Set.univ) hmap
  have hleft :
      (Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k)) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_realGramHafnianObservable n k)
      MeasurableSet.univ]
    simp
  have hlintegral :
      ∫⁻ z, ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z)
        ∂volume = 1 := by
    calc
      ∫⁻ z, ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z)
          ∂volume =
        (Measure.map (realGramHafnianObservable n k)
          (standardRealGaussianColumnMatrixMeasure n k)) Set.univ := by
            simpa [withDensity_apply _ MeasurableSet.univ] using hmass.symm
      _ = 1 := hleft
  refine ⟨hcontinuous.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnonneg, hlintegral]
  exact ENNReal.one_lt_top

theorem integral_sharpRealGramHafnianDensity_eq_one
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    ∫ z, sharpRealGramHafnianDensity n k hn z = 1 := by
  have hint := integrable_sharpRealGramHafnianDensity hn hk hdim
  have hnonneg : ∀ᵐ z ∂volume,
      0 ≤ sharpRealGramHafnianDensity n k hn z :=
    Filter.Eventually.of_forall fun z ↦
      (sharpRealGramHafnianDensity_nonneg_and_le_zero
        hn hk hdim z).1
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg
    hint.aestronglyMeasurable]
  have hmap := map_realGramHafnianObservable_eq_withDensity hn hk hdim
  have hmass := congrArg (fun mu : Measure ℝ ↦ mu Set.univ) hmap
  have hleft :
      (Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k)) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_realGramHafnianObservable n k)
      MeasurableSet.univ]
    simp
  have hlintegral :
      ∫⁻ z, ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z)
        ∂volume = 1 := by
    calc
      ∫⁻ z, ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z)
          ∂volume =
        (Measure.map (realGramHafnianObservable n k)
          (standardRealGaussianColumnMatrixMeasure n k)) Set.univ := by
            simpa [withDensity_apply _ MeasurableSet.univ] using hmass.symm
      _ = 1 := hleft
  rw [hlintegral]
  norm_num

end

end LogdetLean.GramHafnian
