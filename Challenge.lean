import RealGramHafnians.Proofs.SharpRealPaperStatements

/-!
# The two headline statements

Copyright (c) 2026 Hongru Zhao. Released under Apache 2.0; see LICENSE.

These are proposition-valued specifications, with no assumed declarations
and no theorem placeholders. `RealGramHafnians.lean` proves both specifications.
The underlying observables are hafnians of actual Gaussian matrices, rather
than arbitrary random variables assumed to satisfy the desired estimates.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Real ENNReal Nat Topology
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.RealSymmetricGaussianLimit

namespace RealGramHafnians

noncomputable section

/-- Theorem 2.1, including the stronger elementary coefficient estimate. -/
structure Theorem21 (n k : ℕ) (hn : 1 ≤ n) : Prop where
  rmsPositive : 0 < realGramHafnianRMS n k
  exactSecondMoment :
    (∫ X, (realGramHafnianObservable n k X) ^ 2
      ∂standardRealGaussianColumnMatrixMeasure n k) =
      (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ)
  rmsSquared :
    realGramHafnianRMS n k ^ 2 =
      (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ)
  coefficientFormula :
    sharpRealSmallBallCoefficientB n k =
      Real.sqrt (2 / Real.pi) * realGramHafnianRMS n k *
        (∏ j ∈ Finset.range n, realAuxiliaryGammaHalfFactorReal (k - j)) *
        (∏ r ∈ Finset.Icc 2 n, realAuxiliaryGammaHalfFactorReal (2 * r - 1))
  densityLaw :
    Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) =
      volume.withDensity
        (fun z ↦ ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z))
  densityContinuous : Continuous (sharpRealGramHafnianDensity n k hn)
  densityNonnegative : ∀ z, 0 ≤ sharpRealGramHafnianDensity n k hn z
  densityBounded : BddAbove (Set.range (sharpRealGramHafnianDensity n k hn))
  densityMaximumAtZero :
    IsGreatest (Set.range (sharpRealGramHafnianDensity n k hn))
      (sharpRealGramHafnianDensity n k hn 0)
  densityMaximum :
    sSup (Set.range (sharpRealGramHafnianDensity n k hn)) =
      sharpRealGramHafnianDensity n k hn 0
  densityPeakBound :
    sharpRealGramHafnianDensity n k hn 0 ≤
      sharpRealSmallBallCoefficientB n k / (2 * realGramHafnianRMS n k)
  shiftedSmallBall : ∀ z epsilon : ℝ, 0 ≤ epsilon →
    (standardRealGaussianColumnMatrixMeasure n k).real
      {X | |realGramHafnianObservable n k X - z| ≤
        epsilon * realGramHafnianRMS n k} ≤
      min 1 (sharpRealSmallBallCoefficientB n k * epsilon)
  elementaryCoefficient : n + 2 ≤ k →
    sharpRealSmallBallCoefficientB n k ≤
      (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) *
        Real.exp ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (4 * ((k - n - 1 : ℕ) : ℝ)))

/-- Theorem 2.3: weak limit, normalization, density, and both interval bounds. -/
structure Theorem23 (n : ℕ) : Prop where
  hafnianWeakLimit :
    Tendsto (normalizedRealGramHafnianLaw n) atTop
      (nhds (realSymmetricGaussianHafnianLaw n))
  rmsLimit :
    Tendsto (fun k : ℕ ↦ realGramHafnianRMS n k / (Real.sqrt (k : ℝ)) ^ n)
      atTop (nhds (sharpRealSymmetricHafnianRMS n))
  exactSecondMoment :
    (∫⁻ x : SymmetricGaussianHafnian.Edge (Fin (2 * n)) → ℝ,
      ENNReal.ofReal ((SymmetricGaussianHafnian.realEdgeHafnian x) ^ 2)
      ∂SymmetricGaussianHafnian.realEdgeGaussian (Fin (2 * n))) =
      (((2 * n - 1)‼ : ℕ) : ENNReal)
  rmsSquared : sharpRealSymmetricHafnianRMS n ^ 2 =
    (((2 * n - 1)‼ : ℕ) : ℝ)
  coefficientLimit :
    Tendsto (fun k : ℕ ↦ sharpRealSmallBallCoefficientB n k)
      atTop (nhds (sharpRealSymmetricSmallBallCoefficient n))
  coefficientFormula :
    sharpRealSymmetricSmallBallCoefficient n =
      Real.sqrt (2 / Real.pi) * Real.sqrt (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ r ∈ Finset.Icc 2 n, realAuxiliaryGammaHalfFactorReal (2 * r - 1)
  normalizedDensityLaw :
    Measure.map (sharpRealNormalizedSymmetricHafnianObservable n)
        (SymmetricGaussianHafnian.realEdgeGaussian (Fin (2 * n))) =
      volume.withDensity
        (fun x ↦ ENNReal.ofReal (sharpRealNormalizedSymmetricHafnianDensity n x))
  normalizedDensityContinuous : Continuous (sharpRealNormalizedSymmetricHafnianDensity n)
  normalizedDensityEven : Function.Even (sharpRealNormalizedSymmetricHafnianDensity n)
  normalizedDensityMaximum : ∀ x : ℝ,
    0 ≤ sharpRealNormalizedSymmetricHafnianDensity n x ∧
      sharpRealNormalizedSymmetricHafnianDensity n x ≤
        sharpRealNormalizedSymmetricHafnianDensity n 0
  normalizedDensityPeakBound :
    sharpRealNormalizedSymmetricHafnianDensity n 0 ≤
      sharpRealSymmetricSmallBallCoefficient n / 2
  elementaryCoefficient : sharpRealSymmetricSmallBallCoefficient n ≤
    (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ)
  shiftedSmallBall : ∀ z epsilon : ℝ, 0 ≤ epsilon →
    (SymmetricGaussianHafnian.realEdgeGaussian (Fin (2 * n)))
      {x | |SymmetricGaussianHafnian.realEdgeHafnian x - z| ≤
        epsilon * sharpRealSymmetricHafnianRMS n} ≤
      min 1 (ENNReal.ofReal (sharpRealSymmetricSmallBallCoefficient n * epsilon))
  elementarySmallBall : ∀ z epsilon : ℝ, 0 ≤ epsilon →
    (SymmetricGaussianHafnian.realEdgeGaussian (Fin (2 * n)))
      {x | |SymmetricGaussianHafnian.realEdgeHafnian x - z| ≤
        epsilon * sharpRealSymmetricHafnianRMS n} ≤
      min 1 (ENNReal.ofReal
        ((2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) * epsilon))

end
end RealGramHafnians
