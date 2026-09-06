import RealGramHafnians.Proofs.SharpRealDensityLiteral
import LogdetLean.GramHafnian.RealComplexAnticoncentration.FractionalLaplaceOrder
/-!
# Paper-facing auxiliary equations

This module gives stable names to substantive displayed equations used by the
AIHP manuscript but not already packaged as numbered theorem wrappers.

The manuscript and the formal proof derive the exact second moment through the
same auxiliary-field/Wick expansion.  The wrappers below expose the literal
real-valued endpoints used in the paper, including the Gamma-ratio estimates
in the appendix.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Real ENNReal NNReal Nat

namespace LogdetLean.GramHafnian

noncomputable section

/-- **Paper equation (2.4), exact second moment.** -/
theorem paperEquation2_4_exactSecondMoment
    (n k : ℕ) (hk : 0 < k) :
    (∫ X, (realGramHafnianObservable n k X) ^ 2
        ∂standardRealGaussianColumnMatrixMeasure n k) =
      (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ) :=
  integral_sq_realGramHafnianObservable_eq n k hk

/-- **Paper equation (2.4), RMS form.**  The scale denoted `σ_{k,n}` in
the paper is the square root of the exact second moment above. -/
theorem paperEquation2_4_exactRMS
    (n k : ℕ) (hk : 0 < k) :
    realGramHafnianRMS n k ^ 2 =
      (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ) := by
  rw [realGramHafnianRMS_sq n k hk]
  simp only [closedFirstMoment, dimensionProduct,
    oddPairingNat_eq_doubleFactorial]

/-- **Paper equation (3.3), last-column expansion.**  The exposed last
column is paired with the odd-cofactor column combination. -/
theorem paperEquation3_3_lastColumnExpansion
    {n k : ℕ} (hn : 1 ≤ n) (X : RealColumnMatrix n k) :
    realGramHafnianObservable n k X =
      ∑ a : Fin k, X (evenLastIndex n hn) a *
        realOddCofactorColumnCombination hn X a :=
  realGramHafnian_eq_lastColumn_dot_cofactorCombination hn X

/-- **Paper equation (6.1), scalar Fourier comparison.**  The outer variable
`z` is the exposed physical row, so `realCoordinateEnergy z` has the paper's
chi-square law `G_{2r-1}`.  The inner variable is the independent lower-level
cofactor background. -/
theorem paperEquation6_1_scalarFourierComparison
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r) (t : ℝ) :
    ‖charFun
        (finiteRealGramCofactorCombinationEuclideanLaw
          (2 * r - 1) (k + 1))
        (t • EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0)‖ ≤
      ∫ z : Fin (2 * r - 1) → ℝ,
        ∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ),
          Real.exp (-(pastRealCofactorV (by omega) A *
            (t ^ 2 * realCoordinateEnergy z)) / 2)
          ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
            standardRealGaussianVectorMeasure k)
        ∂(Measure.pi fun _ : Fin (2 * r - 1) ↦ gaussianReal 0 1) := by
  let muZ : Measure (Fin (2 * r - 1) → ℝ) :=
    Measure.pi fun _ : Fin (2 * r - 1) ↦ gaussianReal 0 1
  let nu : Measure
      (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
      standardRealGaussianVectorMeasure k
  let f : ((Fin (2 * r - 1) → ℝ) ×
      (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ))) → ℝ :=
    fun p ↦ Real.exp (-(pastRealCofactorV (by omega) p.2 *
      (t ^ 2 * realCoordinateEnergy p.1)) / 2)
  have hfmeas : Measurable f := by
    unfold f
    exact (((measurable_pastRealCofactorV (by omega)).comp measurable_snd).mul
      (measurable_const.mul
        (measurable_realCoordinateEnergy_fin.comp measurable_fst))).neg.div_const 2 |>.exp
  have hf : Integrable f (muZ.prod nu) := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with p
    dsimp [f]
    rw [abs_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.mpr
    have hV := pastRealCofactorV_nonneg (by omega) p.2
    have ht : 0 ≤ t ^ 2 := sq_nonneg t
    have henergy := realCoordinateEnergy_nonneg p.1
    have hprod : 0 ≤ pastRealCofactorV (by omega) p.2 *
        (t ^ 2 * realCoordinateEnergy p.1) :=
      mul_nonneg hV (mul_nonneg ht henergy)
    nlinarith
  rw [charFun_finiteRealGramCofactorCombinationEuclideanLaw_axis]
  change ‖∫ z, rowSuspensionCharacteristic (2 * r - 1) k t z ∂muZ‖ ≤
    ∫ z, ∫ A, f (z, A) ∂nu ∂muZ
  apply norm_integral_le_of_norm_le hf.integral_prod_left
  filter_upwards [] with z
  exact norm_rowSuspensionCharacteristic_le_lower_mixture hr hr2 t z

/-- **Paper equation (7.1), conditional centered-normal law.**  For each
fixed past `A`, pushing the fresh last Gaussian column through its literal
cofactor linear form gives a standard real Gaussian scaled by
`sqrt (V_{k,n}(A))`. -/
theorem paperEquation7_1_conditionalNormalLaw
    {n k : ℕ} (hn : 1 ≤ n)
    (A : OddCofactorIndex n hn → (Fin k → ℝ)) :
    Measure.map
        (iidRealTransposeLinearForm (pastRealCofactorCombination hn A))
        (standardRealGaussianVectorMeasure k) =
      Measure.map
        (fun x : ℝ ↦ Real.sqrt (pastRealCofactorV hn A) * x)
        (gaussianReal 0 1) := by
  have h := map_iidRealTransposeLinearForm_eq_scaled_realGaussian
    (pastRealCofactorCombination hn A)
  rw [← pastRealCofactorV_eq_realCoefficientEnergy hn A] at h
  simpa [standardRealGaussianVectorMeasure, smul_eq_mul] using h

/-- **Paper equation (7.2), literal Gaussian density mixture.** -/
theorem paperEquation7_2_densityMixture
    {n k : ℕ} (hn : 1 ≤ n) (z : ℝ) :
    sharpRealGramHafnianDensity n k hn z =
      ∫ A : OddCofactorIndex n hn → Fin k → ℝ,
        (Real.sqrt (2 * Real.pi * pastRealCofactorV hn A))⁻¹ *
          Real.exp (-(z ^ 2) / (2 * pastRealCofactorV hn A))
        ∂(Measure.pi fun _ : OddCofactorIndex n hn ↦
          standardRealGaussianVectorMeasure k) := by
  unfold sharpRealGramHafnianDensity gaussianPDFReal
    pastRealCofactorVarianceNNReal
  simp only [sub_zero]
  apply integral_congr_ae
  filter_upwards [] with A
  rfl

/-- **Paper equation (7.2), density-law interpretation.**  The displayed
mixture is an actual Lebesgue density of the literal Gram hafnian. -/
theorem paperEquation7_2_densityLaw
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) =
      volume.withDensity
        (fun z ↦ ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z)) :=
  map_realGramHafnianObservable_eq_withDensity hn hk hdim

/-- Exact inverse-half Mellin--Laplace representation used in the passage
from Laplace order to inverse square-root moments. -/
theorem paperInverseHalfMellinLaplaceRepresentation
    {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ in Ioi 0, normalizedHalfMellinKernel t x =
      (Real.sqrt x)⁻¹ :=
  integral_normalizedHalfMellinKernel_Ioi hx

/-- The inverse-half kernel with the manuscript's exact `s x / 2`
scaling and `1 / sqrt (2π)` normalization. -/
def paperInverseHalfScaledKernel (s x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ *
    (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(s * x) / 2))

/-- Literal endpoint for the displayed inverse-half representation in the
paper. -/
theorem paperEquationInverseHalfRepresentation
    {x : ℝ} (hx : 0 < x) :
    ∫ s : ℝ in Ioi 0, paperInverseHalfScaledKernel s x =
      (Real.sqrt x)⁻¹ := by
  have hxhalf : 0 < x / 2 := div_pos hx (by norm_num)
  have hbase :=
    integral_rpow_neg_half_mul_exp_neg_mul_Ioi (x := x / 2) hxhalf
  unfold paperInverseHalfScaledKernel
  rw [integral_const_mul]
  have hintegrand :
      (∫ s : ℝ in Ioi 0,
          s ^ (-(1 / 2 : ℝ)) * Real.exp (-(s * x) / 2)) =
        ∫ s : ℝ in Ioi 0,
          s ^ (-(1 / 2 : ℝ)) * Real.exp (-s * (x / 2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    congr 2
    ring
  rw [hintegrand, hbase, Real.Gamma_one_half_eq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrtPi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have hsqrtTwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtX : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsqrtXHalf : Real.sqrt (x / 2) =
      Real.sqrt x / Real.sqrt 2 := by
    rw [Real.sqrt_div hx.le]
  have hsqrtTwoPi : Real.sqrt (2 * Real.pi) =
      Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  rw [hsqrtXHalf, hsqrtTwoPi]
  field_simp [hsqrtPi.ne', hsqrtTwo.ne', hsqrtX.ne']

/-! ## Literal real inverse-half expectations -/

/-- The paper's real-valued expectation `E[V_{k,r}^{-1/2}]`.  The core
Tonelli argument uses an equivalent `ENNReal` moment; the bridge below proves
that the paper-facing quantity is finite and identical in the theorem range. -/
def paperRealCofactorInverseSqrtExpectation
    (r k : ℕ) (hr : 1 ≤ r) : ℝ :=
  ∫ A : OddCofactorIndex r hr → (Fin k → ℝ),
    (Real.sqrt (pastRealCofactorV hr A))⁻¹
    ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k)

theorem paperRealCofactorInverseSqrtExpectation_nonneg
    (r k : ℕ) (hr : 1 ≤ r) :
    0 ≤ paperRealCofactorInverseSqrtExpectation r k hr := by
  unfold paperRealCofactorInverseSqrtExpectation
  exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun A ↦ by
    positivity

theorem ofReal_paperRealCofactorInverseSqrtExpectation_eq_moment
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k)
    (hdim : 2 * r - 1 ≤ k) :
    ENNReal.ofReal (paperRealCofactorInverseSqrtExpectation r k hr) =
      sharpRealCofactorInverseSqrtMoment r k hr := by
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let g : (OddCofactorIndex r hr → (Fin k → ℝ)) → ℝ :=
    fun A ↦ (Real.sqrt (pastRealCofactorV hr A))⁻¹
  have hgint : Integrable g nu := by
    simpa [nu, g] using
      integrable_pastRealCofactorV_inverseSqrt hr hk hdim
  have hgnonneg : ∀ᵐ A ∂nu, 0 ≤ g A :=
    Filter.Eventually.of_forall fun A ↦ by
      dsimp [g]
      positivity
  have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint hgnonneg
  simpa [paperRealCofactorInverseSqrtExpectation,
    sharpRealCofactorInverseSqrtMoment, ennInverseSqrtMoment, nu, g] using h

/-- Literal real one-step row-suspension recursion. -/
theorem paperRealCofactorInverseSqrtExpectation_step
    {r k : ℕ} (hr2 : 2 ≤ r) (hdim : 2 * r - 1 ≤ k) :
    paperRealCofactorInverseSqrtExpectation r k (by omega) ≤
      realAuxiliaryGammaHalfFactorReal k *
        realAuxiliaryGammaHalfFactorReal (2 * r - 1) *
        paperRealCofactorInverseSqrtExpectation (r - 1) (k - 1) (by omega) := by
  have hkpos : 1 ≤ k := by omega
  have hstep := sharpRealCofactorInverseSqrtMoment_step
    (r := r) (k := k - 1) hr2 (by
      simpa [Nat.sub_add_cancel hkpos] using hdim)
  rw [Nat.sub_add_cancel hkpos] at hstep
  have hcur := ofReal_paperRealCofactorInverseSqrtExpectation_eq_moment
    (r := r) (k := k) (by omega) (by omega) hdim
  have hlow := ofReal_paperRealCofactorInverseSqrtExpectation_eq_moment
    (r := r - 1) (k := k - 1) (by omega) (by omega) (by omega)
  rw [← hcur, ← hlow,
    realAuxiliaryGammaHalfFactor_eq_ofReal,
    realAuxiliaryGammaHalfFactor_eq_ofReal] at hstep
  have hrightNe :
      ENNReal.ofReal
            (paperRealCofactorInverseSqrtExpectation (r - 1) (k - 1) (by omega)) *
          ENNReal.ofReal (realAuxiliaryGammaHalfFactorReal k) *
          ENNReal.ofReal (realAuxiliaryGammaHalfFactorReal (2 * r - 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hrightNe).2 hstep
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (paperRealCofactorInverseSqrtExpectation_nonneg (r - 1) (k - 1) (by omega)),
    ENNReal.toReal_ofReal (realAuxiliaryGammaHalfFactorReal_nonneg (by omega)),
    ENNReal.toReal_ofReal (realAuxiliaryGammaHalfFactorReal_nonneg (by omega)),
    ENNReal.toReal_ofReal
      (paperRealCofactorInverseSqrtExpectation_nonneg r k (by omega))] at hreal
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hreal

/-- Literal real iterated Gamma-product endpoint. -/
theorem paperRealCofactorInverseSqrtExpectation_le_products
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    paperRealCofactorInverseSqrtExpectation n k hn ≤
      (∏ j ∈ Finset.range n,
        realAuxiliaryGammaHalfFactorReal (k - j)) *
      (∏ r ∈ Finset.Icc 2 n,
        realAuxiliaryGammaHalfFactorReal (2 * r - 1)) := by
  have h := integral_pastRealCofactorV_inverseSqrt_le_coefficientReal
    hn hk hdim
  have hnk : n ≤ k := by omega
  rw [sharpRealGammaCoefficientReal,
    sharpRealPhysicalGammaProductReal_eq_range hnk] at h
  simpa [paperRealCofactorInverseSqrtExpectation,
    sharpRealPhysicalGammaRangeProductReal,
    sharpRealOddGammaProductReal] using h

/-- **Paper equation (9.1), Gamma-ratio bound.** -/
theorem paperEquation9_1_gammaCauchySchwarz
    {d : ℕ} (hd : 3 ≤ d) :
    realAuxiliaryGammaHalfFactorReal d ^ 2 ≤
      1 / ((d : ℝ) - 2) :=
  realAuxiliaryGammaHalfFactorReal_sq_le_inv_sub_two hd

/-- **Paper equation (9.2), odd-factor telescope.**  This is the literal
double-factorial/product form of the strongest existing exact telescope. -/
theorem paperEquation9_2_oddFactorTelescope
    {n : ℕ} (hn : 1 ≤ n) :
    ((((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ r ∈ Finset.Icc 2 n,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1) ^ 2) ≤
      ((2 * n - 1 : ℕ) : ℝ) := by
  have h := realElementaryKn_sq_le hn
  rw [realElementaryKn_eq_doubleFactorial_gammaProduct hn, mul_pow,
    Real.sq_sqrt (by positivity :
      0 ≤ ((((2 * n - 1)‼ : ℕ) : ℝ)))] at h
  simpa only [Finset.prod_pow] using h

/-- **Paper equation (9.3), physical dimension bound.**  This is the
squared, paper-displayed form of `sharpRealDimensionGammaFactor_le_exp`. -/
theorem paperEquation9_3_physicalDimensionBound
    {n k q : ℕ} (hq : q < n) (hkn : n + 2 ≤ k) :
    ((k + 2 * q : ℕ) : ℝ) *
        realAuxiliaryGammaHalfFactorReal (k - q) ^ 2 ≤
      Real.exp
        ((3 * (q : ℝ) + 2) / ((k - n - 1 : ℕ) : ℝ)) := by
  have h := sharpRealDimensionGammaFactor_le_exp hq hkn
  have hleft :
      0 ≤ Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
        realAuxiliaryGammaHalfFactorReal (k - q) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (realAuxiliaryGammaHalfFactorReal_nonneg (by omega))
  have hright :
      0 ≤ Real.exp
        ((3 * (q : ℝ) + 2) /
          (2 * ((k - n - 1 : ℕ) : ℝ))) :=
    (Real.exp_pos _).le
  have hsquare := (sq_le_sq₀ hleft hright).2 h
  calc
    ((k + 2 * q : ℕ) : ℝ) *
        realAuxiliaryGammaHalfFactorReal (k - q) ^ 2 =
      (Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
        realAuxiliaryGammaHalfFactorReal (k - q)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
    _ ≤ (Real.exp
        ((3 * (q : ℝ) + 2) /
          (2 * ((k - n - 1 : ℕ) : ℝ)))) ^ 2 := hsquare
    _ = Real.exp
        ((3 * (q : ℝ) + 2) / ((k - n - 1 : ℕ) : ℝ)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      have hgap : (0 : ℝ) < ((k - n - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < k - n - 1 by omega)
      field_simp [hgap.ne']
      norm_num

end

end LogdetLean.GramHafnian
