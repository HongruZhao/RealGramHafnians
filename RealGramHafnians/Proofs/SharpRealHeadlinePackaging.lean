import RealGramHafnians.Proofs.SharpRealDensity
import RealGramHafnians.Proofs.SharpRealProbabilityCap
import RealGramHafnians.Proofs.SharpRealPolynomialSmallBall
/-!
# Paper-facing packaging for the sharp real theorem

This module only repackages previously proved endpoints.  It gives a name to
the exact real small-ball coefficient, records the attained global maximum of
the density as an order-theoretic certificate, and bundles the finite headline
claims into one theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Real ENNReal Nat

namespace LogdetLean.GramHafnian

noncomputable section

/-- The exact real coefficient denoted by `B` in the finite paper theorem. -/
def sharpRealSmallBallCoefficientB (n k : ℕ) : ℝ :=
  realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
    sharpRealGammaCoefficientReal n k

/-- The existing normalized `ENNReal` coefficient is exactly `ofReal B`. -/
theorem sharpRealNormalizedCoefficient_eq_ofReal_coefficientB
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    sharpRealNormalizedCoefficient n k =
      ENNReal.ofReal (sharpRealSmallBallCoefficientB n k) := by
  simpa [sharpRealSmallBallCoefficientB] using
    sharpRealNormalizedCoefficient_eq_ofReal hn hk hdim

/-- Paper notation for the exact real-valued, probability-capped bound. -/
theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBallProbability_le_min_one_coefficientB
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k)
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
    (hdim : 2 * n - 1 ≤ k) :
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
    (hdim : 2 * n - 1 ≤ k) :
    BddAbove (Set.range (sharpRealGramHafnianDensity n k hn)) := by
  refine ⟨sharpRealGramHafnianDensity n k hn 0, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact (sharpRealGramHafnianDensity_nonneg_and_le_zero
    hn hk hdim z).2

/-- Boundedness and attainment of the global maximum, in one certificate. -/
theorem sharpRealGramHafnianDensity_bounded_and_globalMaximum
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    BddAbove (Set.range (sharpRealGramHafnianDensity n k hn)) ∧
      IsGreatest (Set.range (sharpRealGramHafnianDensity n k hn))
        (sharpRealGramHafnianDensity n k hn 0) := by
  exact ⟨bddAbove_range_sharpRealGramHafnianDensity hn hk hdim,
    sharpRealGramHafnianDensity_isGreatest_range hn hk hdim⟩

/-- A single finite-parameter certificate containing the headline density and
shifted-anticoncentration conclusions of the paper. -/
structure SharpRealHeadlineCertificate
    (n k : ℕ) (hn : 1 ≤ n) : Prop where
  exactSecondMomentProduct :
    (∫ X, (realGramHafnianObservable n k X) ^ 2
        ∂standardRealGaussianColumnMatrixMeasure n k) =
      (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ)
  exactSecondMomentRMS :
    (∫ X, (realGramHafnianObservable n k X) ^ 2
        ∂standardRealGaussianColumnMatrixMeasure n k) =
      realGramHafnianRMS n k ^ 2
  densityLaw :
    Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) =
      volume.withDensity
        (fun z ↦ ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z))
  densityContinuous : Continuous (sharpRealGramHafnianDensity n k hn)
  densityNonnegative : ∀ z, 0 ≤ sharpRealGramHafnianDensity n k hn z
  densityGlobalMaximum :
    IsGreatest (Set.range (sharpRealGramHafnianDensity n k hn))
      (sharpRealGramHafnianDensity n k hn 0)
  densityPeakBound :
    sharpRealGramHafnianDensity n k hn 0 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        sharpRealGammaCoefficientReal n k
  densityIntegrable :
    Integrable (sharpRealGramHafnianDensity n k hn) volume
  densityMassOne :
    ∫ z, sharpRealGramHafnianDensity n k hn z = 1
  exactCappedSmallBall : ∀ z epsilon : ℝ, 0 ≤ epsilon →
    (standardRealGaussianColumnMatrixMeasure n k).real
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      min 1 (sharpRealSmallBallCoefficientB n k * epsilon)

/-- All finite headline claims follow simultaneously from the proved sharp
real density and small-ball theorems. -/
theorem sharpRealHeadlineCertificate
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
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

end

end LogdetLean.GramHafnian
