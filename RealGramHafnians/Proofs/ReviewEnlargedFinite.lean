import RealGramHafnians.Proofs.ReviewPositivity
import RealGramHafnians.Proofs.SharpRealPaperStatements
/-! Enlarged finite theorem. Existing observable and coefficient definitions
are reused unchanged. These proofs replace only the rank-based hypotheses;
legacy theorem names remain available for compatibility. -/
open MeasureTheory ProbabilityTheory Set Complex Filter
open scoped BigOperators Real ENNReal NNReal Nat Topology
namespace LogdetLean.GramHafnian.Review
noncomputable section
set_option maxHeartbeats 5000000
theorem ae_pastRealCofactorV_pos_enlarged
    {r k : ℕ} (hr : 1 ≤ r) (hk : r + 1 ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k), 0 < pastRealCofactorV hr A :=
  ae_pastRealCofactorV_pos_standardRealGaussian hr (by omega)


theorem ae_norm_sq_pos_pastRealCofactorCombinationEuclideanLaw
    {r k : ℕ} (hr : 1 ≤ r) (hk : r + 1 ≤ k) :
    ∀ᵐ x ∂(pastRealCofactorCombinationEuclideanLaw r k hr),
      0 < ‖x‖ ^ 2 := by
  unfold pastRealCofactorCombinationEuclideanLaw
  have hset : MeasurableSet
      {x : RealGaussianEuclideanSpace k | 0 < ‖x‖ ^ 2} := by
    change MeasurableSet ((fun x : RealGaussianEuclideanSpace k ↦ ‖x‖ ^ 2) ⁻¹' Set.Ioi 0)
    exact measurableSet_Ioi.preimage (by fun_prop)
  apply (ae_map_iff
    (measurable_pastRealCofactorCombinationEuclidean hr).aemeasurable hset).2
  filter_upwards [ae_pastRealCofactorV_pos_enlarged hr hk]
    with A hA
  rwa [norm_sq_pastRealCofactorCombinationEuclidean]

theorem ae_norm_sq_pos_finiteRealGramCofactorCombinationEuclideanLaw
    {r k : ℕ} (hr : 1 ≤ r) (hk : r + 1 ≤ k) :
    ∀ᵐ x ∂(finiteRealGramCofactorCombinationEuclideanLaw (2 * r - 1) k),
      0 < ‖x‖ ^ 2 := by
  rw [finiteRealGramCofactorCombinationEuclideanLaw_eq_literal r k hr]
  exact ae_norm_sq_pos_pastRealCofactorCombinationEuclideanLaw hr hk

theorem ae_rowSuspensionLowerProductVariance_pos
    {r k : ℕ} (hr2 : 2 ≤ r) (hrlow : 1 ≤ r - 1)
    (hk : (r - 1) + 1 ≤ k) :
    ∀ᵐ p ∂((Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
        standardRealGaussianVectorMeasure k).prod
      (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))),
      0 < rowSuspensionLowerProductVariance hr2 p := by
  let nu := Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
    standardRealGaussianVectorMeasure k
  have hV : ∀ᵐ A ∂nu, 0 < pastRealCofactorV hrlow A :=
    ae_pastRealCofactorV_pos_enlarged hrlow hk
  have hVprod := (Measure.quasiMeasurePreserving_fst
    (μ := nu) (ν := stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))).ae hV
  have hG : ∀ᵐ g ∂(stdGaussian (RealGaussianEuclideanSpace (2 * r - 1))),
      g ≠ 0 := by
    let _ : Nonempty (Fin (2 * r - 1)) := Fin.pos_iff_nonempty.mp (by omega)
    let _ : Nontrivial (RealGaussianEuclideanSpace (2 * r - 1)) := inferInstance
    simpa [ae_iff] using
      LogdetLean.stdGaussian_zero_singleton
        (E := RealGaussianEuclideanSpace (2 * r - 1))
  have hGprod := (Measure.quasiMeasurePreserving_snd
    (μ := nu) (ν := stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))).ae hG
  filter_upwards [hVprod, hGprod] with p hpV hpG
  unfold rowSuspensionLowerProductVariance realAuxiliaryNormSq
  exact mul_pos hpV (by positivity)

/-- Lossless real row-suspension step.  Both factors are exact negative-half
moments of independent chi-square radii. -/
theorem sharpRealCofactorInverseSqrtMoment_step
    {r k : ℕ} (hr2 : 2 ≤ r) (hk : r + 1 ≤ k + 1) :
    sharpRealCofactorInverseSqrtMoment r (k + 1) (by omega) ≤
      sharpRealCofactorInverseSqrtMoment (r - 1) k (by omega) *
        realAuxiliaryGammaHalfFactor (k + 1) *
        realAuxiliaryGammaHalfFactor (2 * r - 1) := by
  let nuLower : Measure
      (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
      standardRealGaussianVectorMeasure k
  let nu := nuLower.prod
    (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))
  have hklower : (r - 1) + 1 ≤ k := by omega
  have hstep := ennInverseSqrt_norm_sq_le_realAuxiliaryGamma_factor
    (d := k + 1) (by omega)
    (finiteRealGramCofactorCombinationEuclideanLaw (2 * r - 1) (k + 1))
    nu
    (rowSuspensionLowerProductVariance (k := k) hr2)
    (measurable_rowSuspensionLowerProductVariance hr2)
    (rowSuspensionLowerProductVariance_nonneg hr2)
    (by
      simpa [nu, nuLower] using
        ae_rowSuspensionLowerProductVariance_pos hr2 (by omega) hklower)
    (physicalCofactorCombination_charFun_re_le_rowSuspension_product
      (k := k) (by omega) hr2)
    (ae_norm_sq_pos_finiteRealGramCofactorCombinationEuclideanLaw
      (k := k + 1) (by omega) hk)
  have hfactor :
      ennInverseSqrtMoment nu
          (rowSuspensionLowerProductVariance (k := k) hr2) =
        sharpRealCofactorInverseSqrtMoment (r - 1) k (by omega) *
          realAuxiliaryGammaHalfFactor (2 * r - 1) := by
    change ennInverseSqrtMoment nu
        (fun p ↦ pastRealCofactorV (k := k) (by omega) p.1 *
          realAuxiliaryNormSq p.2) = _
    have h := ennInverseSqrtMoment_mul_realAuxiliaryNormSq
      nuLower (pastRealCofactorV (k := k) (by omega))
      (measurable_pastRealCofactorV (by omega))
      (pastRealCofactorV_nonneg (by omega)) (by omega : 2 ≤ 2 * r - 1)
    simpa [nu, nuLower, rowSuspensionLowerProductVariance,
      sharpRealCofactorInverseSqrtMoment, realAuxiliaryGammaHalfFactor] using h
  rw [ennInverseSqrtMoment_physicalLaw_eq r (k + 1) (by omega),
    hfactor] at hstep
  simpa [realAuxiliaryGammaHalfFactor, mul_assoc, mul_left_comm, mul_comm]
    using hstep


theorem sharpRealCofactorInverseSqrtMoment_le_coefficient
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    sharpRealCofactorInverseSqrtMoment n k hn ≤
      sharpRealGammaCoefficient n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              change sharpRealCofactorInverseSqrtMoment 1 k _ ≤ _
              rw [sharpRealGammaCoefficient_one]
              unfold sharpRealCofactorInverseSqrtMoment
              exact le_of_eq (ennInverseSqrtMoment_pastRealCofactorV_level_one hk)
          | succ n =>
              have hkpos : 1 ≤ k := by omega
              have hdimLower : (n + 1) + 1 ≤ k - 1 := by omega
              have hkLower : 2 ≤ k - 1 := by omega
              have hstep := sharpRealCofactorInverseSqrtMoment_step
                (r := n + 2) (k := k - 1) (by omega)
                (by simpa [Nat.sub_add_cancel hkpos] using hdim)
              have hih := ih (n + 1) (by omega) (k := k - 1)
                (by omega) hkLower hdimLower
              rw [Nat.sub_add_cancel hkpos] at hstep
              calc
                sharpRealCofactorInverseSqrtMoment (n + 2) k _ ≤
                    sharpRealCofactorInverseSqrtMoment (n + 1) (k - 1) _ *
                      realAuxiliaryGammaHalfFactor k *
                      realAuxiliaryGammaHalfFactor (2 * (n + 2) - 1) := hstep
                _ ≤ sharpRealGammaCoefficient (n + 1) (k - 1) *
                      realAuxiliaryGammaHalfFactor k *
                      realAuxiliaryGammaHalfFactor (2 * (n + 2) - 1) := by
                    gcongr
                _ = sharpRealGammaCoefficient (n + 2) k := by
                    rw [sharpRealGammaCoefficient_add_two]


theorem sharpRealGammaCoefficientReal_nonneg
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    0 ≤ sharpRealGammaCoefficientReal n k := by
  unfold sharpRealGammaCoefficientReal
    sharpRealPhysicalGammaProductReal sharpRealOddGammaProductReal
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro d hd
    have hdLower := (Finset.mem_Icc.mp hd).1
    have hdimd : 2 ≤ d := by omega
    exact realAuxiliaryGammaHalfFactorReal_nonneg hdimd
  · apply Finset.prod_nonneg
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    exact realAuxiliaryGammaHalfFactorReal_nonneg (by omega)

theorem sharpRealGammaCoefficient_eq_ofReal
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    sharpRealGammaCoefficient n k =
      ENNReal.ofReal (sharpRealGammaCoefficientReal n k) := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              rw [sharpRealGammaCoefficient_one,
                sharpRealGammaCoefficientReal_one (by omega),
                realAuxiliaryGammaHalfFactor_eq_ofReal]
          | succ n =>
              have hkpos : 1 ≤ k := by omega
              have hdimLower : (n + 1) + 1 ≤ k - 1 := by omega
              have hkLower : 2 ≤ k - 1 := by omega
              have hih := ih (n + 1) (by omega) (k := k - 1)
                (by omega) hkLower hdimLower
              have hnonnegLower := sharpRealGammaCoefficientReal_nonneg
                (n := n + 1) (k := k - 1) (by omega) hkLower hdimLower
              have hgammaK := realAuxiliaryGammaHalfFactorReal_nonneg
                (by omega : 2 ≤ k)
              rw [sharpRealGammaCoefficient_add_two,
                sharpRealGammaCoefficientReal_succ (by omega) (by omega),
                hih, realAuxiliaryGammaHalfFactor_eq_ofReal,
                realAuxiliaryGammaHalfFactor_eq_ofReal,
                ← ENNReal.ofReal_mul hnonnegLower,
                ← ENNReal.ofReal_mul (mul_nonneg hnonnegLower hgammaK)]

theorem sharpRealNormalizedCoefficient_eq_ofReal
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    sharpRealNormalizedCoefficient n k =
      ENNReal.ofReal
        (realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
          sharpRealGammaCoefficientReal n k) := by
  rw [sharpRealNormalizedCoefficient,
    sharpRealGammaCoefficient_eq_ofReal hn hk hdim]
  rw [ENNReal.ofReal_mul]
  exact realGaussianIntervalPrefactor_nonneg
    (realGramHafnianRMS_nonneg n k)



theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      sharpRealNormalizedCoefficient n k * ENNReal.ofReal epsilon := by
  have hV := ae_pastRealCofactorV_pos_enlarged hn hdim
  have hrms := realGramHafnianRMS_nonneg n k
  have hsmall :=
    standardRealGaussianColumnMatrix_shiftedSmallBall_le_inverseSqrtMoment
      hn hV z (epsilon * realGramHafnianRMS n k) (mul_nonneg hepsilon hrms)
  have hmoment :=
    sharpRealCofactorInverseSqrtMoment_le_coefficient hn hk hdim
  calc
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      ENNReal.ofReal
          (realGaussianIntervalPrefactor
            (epsilon * realGramHafnianRMS n k)) *
        sharpRealCofactorInverseSqrtMoment n k hn := hsmall
    _ ≤ ENNReal.ofReal
          (realGaussianIntervalPrefactor
            (epsilon * realGramHafnianRMS n k)) *
        sharpRealGammaCoefficient n k := by gcongr
    _ = sharpRealNormalizedCoefficient n k * ENNReal.ofReal epsilon := by
      have hpref : realGaussianIntervalPrefactor
          (epsilon * realGramHafnianRMS n k) =
          epsilon * realGaussianIntervalPrefactor (realGramHafnianRMS n k) := by
        unfold realGaussianIntervalPrefactor
        ring
      rw [hpref, ENNReal.ofReal_mul hepsilon]
      unfold sharpRealNormalizedCoefficient
      ac_rfl


theorem ae_pastRealCofactorVarianceNNReal_ne_zero
    {r k : ℕ} (hr : 1 ≤ r) (hk : r + 1 ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k),
      pastRealCofactorVarianceNNReal hr A ≠ 0 := by
  filter_upwards [ae_pastRealCofactorV_pos_enlarged hr hk]
    with A hA
  intro hzero
  have hcoe := congrArg ((↑) : ℝ≥0 → ℝ) hzero
  change pastRealCofactorV hr A = 0 at hcoe
  exact hA.ne' hcoe

/-- The verified Gamma-product estimate makes the negative-half moment
finite, not merely bounded in the extended nonnegative reals. -/
theorem sharpRealCofactorInverseSqrtMoment_lt_top
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
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
    (hdim : n + 1 ≤ k) :
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
    (hdim : n + 1 ≤ k) :
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
    (hdim : n + 1 ≤ k) :
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
    (hdim : n + 1 ≤ k) (z : ℝ) :
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
    (hdim : n + 1 ≤ k) :
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
    (hdim : n + 1 ≤ k) :
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
    {n k : ℕ} (hn : 1 ≤ n) (hdim : n + 1 ≤ k) :
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
    (hdim : n + 1 ≤ k) (z : ℝ) :
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
    (hdim : n + 1 ≤ k) :
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
    (hdim : n + 1 ≤ k) :
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
    (hdim : n + 1 ≤ k) :
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


theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_min_one_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      min 1
        (sharpRealNormalizedCoefficient n k * ENNReal.ofReal epsilon) := by
  apply le_min
  · calc
      (standardRealGaussianColumnMatrixMeasure n k)
          {X | |realGramHafnianObservable n k X - z| ≤
            epsilon * realGramHafnianRMS n k} ≤
        (standardRealGaussianColumnMatrixMeasure n k) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := IsProbabilityMeasure.measure_univ
  · exact
      standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
        hn hk hdim z epsilon hepsilon

/-- The elementary exponential finite estimate, again with the probability
cap made explicit. -/
theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBallProbability_le_min_one_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k).real
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      min 1
        ((realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
            sharpRealGammaCoefficientReal n k) * epsilon) := by
  apply le_min
  · have hmono :
        (standardRealGaussianColumnMatrixMeasure n k)
            {X | |realGramHafnianObservable n k X - z| ≤
              epsilon * realGramHafnianRMS n k} ≤
          (standardRealGaussianColumnMatrixMeasure n k) Set.univ :=
        measure_mono (Set.subset_univ _)
    have hreal := ENNReal.toReal_mono (by simp) hmono
    simpa [Measure.real, IsProbabilityMeasure.measure_univ] using hreal
  · have hfinite :=
        standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
          hn hk hdim z epsilon hepsilon
    rw [sharpRealNormalizedCoefficient_eq_ofReal hn hk hdim] at hfinite
    have hcoefficient :
        0 ≤ realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
          sharpRealGammaCoefficientReal n k :=
      mul_nonneg
        (realGaussianIntervalPrefactor_nonneg
          (realGramHafnianRMS_nonneg n k))
        (sharpRealGammaCoefficientReal_nonneg hn hk hdim)
    rw [← ENNReal.ofReal_mul hcoefficient] at hfinite
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinite
    simpa [Measure.real,
      ENNReal.toReal_ofReal (mul_nonneg hcoefficient hepsilon)] using hreal


theorem sharpRealNormalizedCoefficient_eq_ofReal_coefficientB
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    sharpRealNormalizedCoefficient n k =
      ENNReal.ofReal (sharpRealSmallBallCoefficientB n k) := by
  simpa [sharpRealSmallBallCoefficientB] using
    sharpRealNormalizedCoefficient_eq_ofReal hn hk hdim

/-- Paper notation for the exact real-valued, probability-capped bound. -/
theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBallProbability_le_min_one_coefficientB
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k).real
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      min 1 (sharpRealSmallBallCoefficientB n k * epsilon) := by
  simpa [sharpRealSmallBallCoefficientB] using
    standardRealGaussianColumnMatrix_normalizedShiftedSmallBallProbability_le_min_one_sharp
      hn hk hdim z epsilon hepsilon

/-- The density value at zero is the greatest element of its pointwise range. -/
theorem sharpRealGramHafnianDensity_isGreatest_range
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    IsGreatest (Set.range (sharpRealGramHafnianDensity n k hn))
      (sharpRealGramHafnianDensity n k hn 0) := by
  constructor
  · exact ⟨0, rfl⟩
  · rintro _ ⟨z, rfl⟩
    exact (sharpRealGramHafnianDensity_nonneg_and_le_zero
      hn hk hdim z).2

/-- An explicit upper-bound certificate for the full density range. -/
theorem bddAbove_range_sharpRealGramHafnianDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    BddAbove (Set.range (sharpRealGramHafnianDensity n k hn)) := by
  refine ⟨sharpRealGramHafnianDensity n k hn 0, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact (sharpRealGramHafnianDensity_nonneg_and_le_zero
    hn hk hdim z).2

/-- Boundedness and attainment of the global maximum, in one certificate. -/
theorem sharpRealGramHafnianDensity_bounded_and_globalMaximum
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    BddAbove (Set.range (sharpRealGramHafnianDensity n k hn)) ∧
      IsGreatest (Set.range (sharpRealGramHafnianDensity n k hn))
        (sharpRealGramHafnianDensity n k hn 0) := by
  exact ⟨bddAbove_range_sharpRealGramHafnianDensity hn hk hdim,
    sharpRealGramHafnianDensity_isGreatest_range hn hk hdim⟩

/-- A single finite-parameter certificate containing the headline density and
shifted-anticoncentration conclusions of the paper. -/
theorem sharpRealHeadlineCertificate
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    SharpRealHeadlineCertificate n k hn where
  exactSecondMomentProduct :=
    integral_sq_realGramHafnianObservable_eq n k (by omega)
  exactSecondMomentRMS :=
    integral_sq_realGramHafnianObservable_eq_RMS_sq n k (by omega)
  densityLaw := map_realGramHafnianObservable_eq_withDensity hn hk hdim
  densityContinuous := continuous_sharpRealGramHafnianDensity hn hk hdim
  densityNonnegative := fun z ↦
    (sharpRealGramHafnianDensity_nonneg_and_le_zero hn hk hdim z).1
  densityGlobalMaximum :=
    sharpRealGramHafnianDensity_isGreatest_range hn hk hdim
  densityPeakBound :=
    sharpRealGramHafnianDensity_zero_le_coefficientReal hn hk hdim
  densityIntegrable := integrable_sharpRealGramHafnianDensity hn hk hdim
  densityMassOne := integral_sharpRealGramHafnianDensity_eq_one hn hk hdim
  exactCappedSmallBall := fun z epsilon hepsilon ↦
    standardRealGaussianColumnMatrix_normalizedShiftedSmallBallProbability_le_min_one_coefficientB
      hn hk hdim z epsilon hepsilon


theorem range_sharpRealGramHafnianDensity_subset_Icc
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    Set.range (sharpRealGramHafnianDensity n k hn) ⊆
      Set.Icc 0 (sharpRealGramHafnianDensity n k hn 0) := by
  rintro _ ⟨z, rfl⟩
  exact sharpRealGramHafnianDensity_nonneg_and_le_zero hn hk hdim z

/-- Zero is an explicit lower bound for the range of the density. -/
theorem bddBelow_range_sharpRealGramHafnianDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    BddBelow (Set.range (sharpRealGramHafnianDensity n k hn)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact (sharpRealGramHafnianDensity_nonneg_and_le_zero
    hn hk hdim z).1

/-- The density range is bounded on both sides, with explicit lower and upper
bounds supplied by zero and the value at the origin. -/
theorem bddBelow_and_bddAbove_range_sharpRealGramHafnianDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    BddBelow (Set.range (sharpRealGramHafnianDensity n k hn)) ∧
      BddAbove (Set.range (sharpRealGramHafnianDensity n k hn)) := by
  exact ⟨bddBelow_range_sharpRealGramHafnianDensity hn hk hdim,
    bddAbove_range_sharpRealGramHafnianDensity hn hk hdim⟩

/-- Literal attained-supremum form of
`\|f\|_∞ = f(0)`: since the density is nonnegative, the supremum of its
pointwise values is its sup norm, and the supremum is attained at zero. -/
theorem sSup_range_sharpRealGramHafnianDensity_eq_zero
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    sSup (Set.range (sharpRealGramHafnianDensity n k hn)) =
      sharpRealGramHafnianDensity n k hn 0 := by
  exact (sharpRealGramHafnianDensity_isGreatest_range hn hk hdim).csSup_eq

/-- Every absolute density value is bounded by the attained value at zero;
this is the direct pointwise sup-norm formulation. -/
theorem abs_sharpRealGramHafnianDensity_le_zero
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) (z : ℝ) :
    |sharpRealGramHafnianDensity n k hn z| ≤
      sharpRealGramHafnianDensity n k hn 0 := by
  rw [abs_of_nonneg ((sharpRealGramHafnianDensity_nonneg_and_le_zero
    hn hk hdim z).1)]
  exact (sharpRealGramHafnianDensity_nonneg_and_le_zero hn hk hdim z).2

/-- A bundled, literal certificate for every analytic density assertion in
the finite theorem of the paper. -/
theorem sharpRealDensityLiteralCertificate
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    SharpRealDensityLiteralCertificate n k hn where
  densityLaw := map_realGramHafnianObservable_eq_withDensity hn hk hdim
  continuous := continuous_sharpRealGramHafnianDensity hn hk hdim
  even := even_sharpRealGramHafnianDensity hn
  nonnegative := fun z ↦
    (sharpRealGramHafnianDensity_nonneg_and_le_zero hn hk hdim z).1
  rangeInExplicitBounds :=
    range_sharpRealGramHafnianDensity_subset_Icc hn hk hdim
  rangeBoundedBelow :=
    bddBelow_range_sharpRealGramHafnianDensity hn hk hdim
  rangeBoundedAbove :=
    bddAbove_range_sharpRealGramHafnianDensity hn hk hdim
  maximumAtZero :=
    sharpRealGramHafnianDensity_isGreatest_range hn hk hdim
  attainedSupremum :=
    sSup_range_sharpRealGramHafnianDensity_eq_zero hn hk hdim
  pointwiseSupNorm := fun z ↦
    abs_sharpRealGramHafnianDensity_le_zero hn hk hdim z
  peakBound :=
    sharpRealGramHafnianDensity_zero_le_coefficientReal hn hk hdim
  integrable := integrable_sharpRealGramHafnianDensity hn hk hdim
  unitMass := integral_sharpRealGramHafnianDensity_eq_one hn hk hdim


theorem sharpRealSmallBallCoefficientB_eq_literal_gamma_products
    {n k : ℕ} (hn : 1 ≤ n) (_hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    sharpRealSmallBallCoefficientB n k =
      Real.sqrt (2 / Real.pi) * realGramHafnianRMS n k *
        (∏ j ∈ Finset.range n,
          realAuxiliaryGammaHalfFactorReal (k - j)) *
        (∏ r ∈ Finset.Icc 2 n,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1)) := by
  have hnk : n ≤ k := by omega
  rw [sharpRealSmallBallCoefficientB,
    realGaussianIntervalPrefactor_eq_sqrt_two_div_pi_mul,
    sharpRealGammaCoefficientReal,
    sharpRealPhysicalGammaProductReal_eq_range hnk]
  unfold sharpRealPhysicalGammaRangeProductReal
    sharpRealOddGammaProductReal
  ring

/-- Literal version of equation `(elementary-B)` in the paper. -/
theorem sharpRealSmallBallCoefficientB_le_literal_elementary
    {n k : ℕ} (hn : 1 ≤ n) (_hk : 2 ≤ k)
    (_hdim : n + 1 ≤ k) (hkn : n + 2 ≤ k) :
    sharpRealSmallBallCoefficientB n k ≤
      Real.sqrt
          (2 * (((2 * n - 1 : ℕ) : ℝ)) / Real.pi) *
        Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((k - n - 1 : ℕ) : ℝ))) := by
  have hbound := sharpRealNormalizedCoefficientReal_le_exp_sharp hn hkn
  rw [sharpRealSmallBallCoefficientB]
  calc
    realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
          sharpRealGammaCoefficientReal n k ≤
        realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp
            ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (4 * ((k - n - 1 : ℕ) : ℝ))) := hbound
    _ = Real.sqrt
          (2 * (((2 * n - 1 : ℕ) : ℝ)) / Real.pi) *
        Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((k - n - 1 : ℕ) : ℝ))) := by
      rw [realGaussianIntervalPrefactor_one_mul_sqrt_eq_literal
        (2 * n - 1)]


theorem paperTheorem2_1_density_and_exact_shifted_anticoncentration
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : n + 1 ≤ k) :
    PaperTheorem2_1Certificate n k hn where
  headline := sharpRealHeadlineCertificate hn hk hdim
  density := sharpRealDensityLiteralCertificate hn hk hdim
  rmsNonnegative := realGramHafnianRMS_nonneg n k
  densityPeakProductBound := by
    have h := sharpRealGramHafnianDensity_zero_le_coefficientReal hn hk hdim
    have hnk : n ≤ k := by omega
    rw [sharpRealGammaCoefficientReal,
      sharpRealPhysicalGammaProductReal_eq_range hnk] at h
    change sharpRealGramHafnianDensity n k hn 0 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        sharpRealPhysicalGammaRangeProductReal n k *
        sharpRealOddGammaProductReal n
    simpa only [mul_assoc] using h
  exactRMSProduct := paperEquation2_4_exactRMS n k (by omega)
  coefficientFormula :=
    sharpRealSmallBallCoefficientB_eq_literal_gamma_products hn hk hdim
  elementaryCoefficient := fun hkn ↦
    sharpRealSmallBallCoefficientB_le_literal_elementary hn hk hdim hkn


end
end LogdetLean.GramHafnian.Review
