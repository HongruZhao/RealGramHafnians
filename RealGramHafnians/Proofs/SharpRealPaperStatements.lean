import RealGramHafnians.Proofs.SharpRealDensityLiteral
import RealGramHafnians.Proofs.SharpRealCoefficientLiteral
import RealGramHafnians.Proofs.SharpRealAuxiliaryEquations
import RealGramHafnians.Proofs.SharpRealSymmetricGaussianLimit
import RealGramHafnians.Proofs.SharpRealSymmetricGaussianDensity
/-! Main-theorem certificates extracted from the author's paper development.
The GitHub release omits all side-result imports and declarations.
Modified for this headline-only release, September 2026. -/

open MeasureTheory ProbabilityTheory Set Complex Filter
open scoped BigOperators Real ENNReal NNReal Nat Topology

namespace LogdetLean.GramHafnian

noncomputable section

/-! ## Section 2: headline theorems -/

/-- Theorem 2.1 in one paper-facing certificate.  The first two components
contain the exact second moment, RMS normalization, density law, continuity,
nonnegativity, evenness, unit mass, attained maximum, peak bound, and capped
shifted small-ball inequality.  The last component is the literal displayed
formula for `B^R_{k,n}`. -/
structure PaperTheorem2_1Certificate
    (n k : ℕ) (hn : 1 ≤ n) : Prop where
  headline : SharpRealHeadlineCertificate n k hn
  density : SharpRealDensityLiteralCertificate n k hn
  rmsNonnegative : 0 ≤ realGramHafnianRMS n k
  densityPeakProductBound :
    sharpRealGramHafnianDensity n k hn 0 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (∏ j ∈ Finset.range n,
          realAuxiliaryGammaHalfFactorReal (k - j)) *
        (∏ r ∈ Finset.Icc 2 n,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1))
  exactRMSProduct :
    realGramHafnianRMS n k ^ 2 =
      (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ)
  coefficientFormula :
    sharpRealSmallBallCoefficientB n k =
      Real.sqrt (2 / Real.pi) * realGramHafnianRMS n k *
        (∏ j ∈ Finset.range n,
          realAuxiliaryGammaHalfFactorReal (k - j)) *
        (∏ r ∈ Finset.Icc 2 n,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1))
  elementaryCoefficient : n + 2 ≤ k →
    sharpRealSmallBallCoefficientB n k ≤
      Real.sqrt
          (2 * (((2 * n - 1 : ℕ) : ℝ)) / Real.pi) *
        Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((k - n - 1 : ℕ) : ℝ)))

/-- Paper Theorem 2.1: density and exact shifted anticoncentration. -/
theorem paperTheorem2_1_density_and_exact_shifted_anticoncentration
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
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

/-- Theorem 2.2 in one paper-facing certificate: exact RMS, exact limiting
coefficient, its simple finite-dimensional envelope, and the uniform shifted
small-ball conclusion for the independent-edge real symmetric Gaussian
hafnian. -/
structure PaperTheorem2_2SymmetricGaussianCertificate
    (n : ℕ) (hn : 1 ≤ n) : Prop where
  fixedDegreeLimit : SharpRealSymmetricGaussianLimitCertificate n hn
  exactSecondMoment :
    (∫⁻ x : SymmetricGaussianHafnian.Edge (Fin (2 * n)) → ℝ,
        ENNReal.ofReal
          ((SymmetricGaussianHafnian.realEdgeHafnian x) ^ 2)
        ∂SymmetricGaussianHafnian.realEdgeGaussian (Fin (2 * n))) =
      (((2 * n - 1)‼ : ℕ) : ENNReal)
  exactRMS : sharpRealSymmetricHafnianRMS n ^ 2 =
    ((((2 * n - 1)‼ : ℕ) : ℝ))
  coefficientFormula : sharpRealSymmetricSmallBallCoefficient n =
    Real.sqrt (2 / Real.pi) *
      Real.sqrt ((((2 * n - 1)‼ : ℕ) : ℝ)) *
      ∏ r ∈ Finset.Icc 2 n,
        realAuxiliaryGammaHalfFactorReal (2 * r - 1)
  coefficientBound : sharpRealSymmetricSmallBallCoefficient n ≤
    Real.sqrt (2 / Real.pi) *
      Real.sqrt (((2 * n - 1 : ℕ) : ℝ))
  coefficientThreeEighthBounds :
    Real.sqrt (2 / Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) ≤
        sharpRealSymmetricSmallBallCoefficient n ∧
      sharpRealSymmetricSmallBallCoefficient n ≤
        (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ)
  normalizedDensityLaw :
    Measure.map (sharpRealNormalizedSymmetricHafnianObservable n)
        (SymmetricGaussianHafnian.realEdgeGaussian (Fin (2 * n))) =
      volume.withDensity
        (fun x ↦ ENNReal.ofReal
          (sharpRealNormalizedSymmetricHafnianDensity n x))
  normalizedDensityContinuous :
    Continuous (sharpRealNormalizedSymmetricHafnianDensity n)
  normalizedDensityEven :
    Function.Even (sharpRealNormalizedSymmetricHafnianDensity n)
  normalizedDensityMaximum : ∀ x : ℝ,
    0 ≤ sharpRealNormalizedSymmetricHafnianDensity n x ∧
      sharpRealNormalizedSymmetricHafnianDensity n x ≤
        sharpRealNormalizedSymmetricHafnianDensity n 0
  normalizedDensityPeakBound :
    sharpRealNormalizedSymmetricHafnianDensity n 0 ≤
      sharpRealSymmetricSmallBallCoefficient n / 2 ∧
    sharpRealNormalizedSymmetricHafnianDensity n 0 ≤
      (1 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ)
  shiftedSmallBall : ∀ (z epsilon : ℝ), 0 ≤ epsilon →
    (SymmetricGaussianHafnian.realEdgeGaussian (Fin (2 * n)))
        {x | |SymmetricGaussianHafnian.realEdgeHafnian x - z| ≤
          epsilon * sharpRealSymmetricHafnianRMS n} ≤
      min 1 (ENNReal.ofReal
        (sharpRealSymmetricSmallBallCoefficient n * epsilon))

/-- Paper Theorem 2.2: real symmetric Gaussian hafnian
anticoncentration. -/
theorem paperTheorem2_2_real_symmetric_gaussian_anticoncentration
    {n : ℕ} (hn : 1 ≤ n) :
    PaperTheorem2_2SymmetricGaussianCertificate n hn where
  fixedDegreeLimit := sharpRealSymmetricGaussianLimitCertificate hn
  exactSecondMoment := sharpRealSymmetricHafnian_exactSecondMoment n
  exactRMS := sharpRealSymmetricHafnianRMS_sq n
  coefficientFormula :=
    sharpRealSymmetricSmallBallCoefficient_eq_product hn
  coefficientBound :=
    sharpRealSymmetricSmallBallCoefficient_le_sqrt_odd hn
  coefficientThreeEighthBounds :=
    sharpRealSymmetricSmallBallCoefficient_threeEighth_twoSided hn
  normalizedDensityLaw :=
    map_normalizedRealSymmetricGaussianHafnian_eq_withDensity hn
  normalizedDensityContinuous :=
    continuous_sharpRealNormalizedSymmetricHafnianDensity hn
  normalizedDensityEven :=
    even_sharpRealNormalizedSymmetricHafnianDensity hn
  normalizedDensityMaximum := fun x ↦
    sharpRealNormalizedSymmetricHafnianDensity_nonneg_and_le_zero hn x
  normalizedDensityPeakBound := ⟨
    sharpRealNormalizedSymmetricHafnianDensity_zero_le_coefficient_half hn,
    sharpRealNormalizedSymmetricHafnianDensity_zero_le_threeEighth hn⟩
  shiftedSmallBall := fun z epsilon hepsilon ↦
    sharpRealSymmetricGaussian_shiftedSmallBall_of_fixedDegreeLimit
      n hn z epsilon hepsilon

/-- Paper Theorem 2.3 after the main-results reordering.  The former 2.2
name remains as a compatibility endpoint. -/
theorem paperTheorem2_3_real_symmetric_gaussian_anticoncentration
    {n : ℕ} (hn : 1 ≤ n) :
    PaperTheorem2_2SymmetricGaussianCertificate n hn :=
  paperTheorem2_2_real_symmetric_gaussian_anticoncentration hn

/-- Paper Theorem 2.2, isolated paper-facing endpoint for the matching
`n^(3/8)` lower and upper coefficient bounds. -/
theorem paperTheorem2_2_real_symmetric_coefficient_threeEighth_bounds
    {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 / Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) ≤
        sharpRealSymmetricSmallBallCoefficient n ∧
      sharpRealSymmetricSmallBallCoefficient n ≤
        (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) :=
  (paperTheorem2_2_real_symmetric_gaussian_anticoncentration hn).coefficientThreeEighthBounds

/-- Paper Theorem 2.3, isolated endpoint for the matching `n^(3/8)`
coefficient bounds after the main-results reordering. -/
theorem paperTheorem2_3_real_symmetric_coefficient_threeEighth_bounds
    {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 / Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) ≤
        sharpRealSymmetricSmallBallCoefficient n ∧
      sharpRealSymmetricSmallBallCoefficient n ≤
        (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) :=
  paperTheorem2_2_real_symmetric_coefficient_threeEighth_bounds hn

end

end LogdetLean.GramHafnian
