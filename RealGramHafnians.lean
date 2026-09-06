import Challenge
import RealGramHafnians.Proofs.ReviewSharperCoefficient

/-!
# Shifted Anticoncentration for Real Gram Hafnians and Symmetric Gaussian Hafnians

Copyright (c) 2026 Hongru Zhao. Released under Apache 2.0; see LICENSE.

Public entry point for Theorems 2.1 and 2.3 of the paper. Both theorems are
proved without additional mathematical axioms. Their complete specifications
are in `Challenge.lean`; `Verification.lean` checks their transitive axioms.
-/

open LogdetLean.GramHafnian

namespace RealGramHafnians

/-- Theorem 2.1, for `n ≥ 1` and `k ≥ n + 1`. The additional condition
`k ≥ n + 2` is required only for the elementary coefficient estimate. -/
theorem theorem2_1 {n k : ℕ} (hn : 1 ≤ n) (hkn : n + 1 ≤ k) :
    Theorem21 n k hn := by
  have h := Review.paperTheorem_main_revised hn hkn
  exact {
    rmsPositive := realGramHafnianRMS_pos n k (by omega)
    exactSecondMoment := h.1.headline.exactSecondMomentProduct
    rmsSquared := h.1.exactRMSProduct
    coefficientFormula := h.1.coefficientFormula
    densityLaw := h.1.density.densityLaw
    densityContinuous := h.1.density.continuous
    densityNonnegative := h.1.density.nonnegative
    densityBounded := h.1.density.rangeBoundedAbove
    densityMaximumAtZero := h.1.density.maximumAtZero
    densityMaximum := h.1.density.attainedSupremum
    densityPeakBound := (Review.paperEquation_density_bound hn hkn).2
    shiftedSmallBall := h.1.headline.exactCappedSmallBall
    elementaryCoefficient := h.2
  }

/-- Theorem 2.3, for `n ≥ 1`, including the actual fixed-order Gaussian
Gram limit and the normalized symmetric Gaussian hafnian density. -/
theorem theorem2_3 {n : ℕ} (hn : 1 ≤ n) : Theorem23 n := by
  have h := paperTheorem2_3_real_symmetric_gaussian_anticoncentration hn
  exact {
    hafnianWeakLimit := h.fixedDegreeLimit.normalizedHafnianWeakLimit
    rmsLimit := h.fixedDegreeLimit.normalizedRMSLimit
    exactSecondMoment := h.exactSecondMoment
    rmsSquared := h.exactRMS
    coefficientLimit := h.fixedDegreeLimit.coefficientLimit
    coefficientFormula := h.coefficientFormula
    normalizedDensityLaw := h.normalizedDensityLaw
    normalizedDensityContinuous := h.normalizedDensityContinuous
    normalizedDensityEven := h.normalizedDensityEven
    normalizedDensityMaximum := h.normalizedDensityMaximum
    normalizedDensityPeakBound := h.normalizedDensityPeakBound.1
    elementaryCoefficient := h.coefficientThreeEighthBounds.2
    shiftedSmallBall := h.shiftedSmallBall
    elementarySmallBall := fun z epsilon hepsilon ↦
      Review.paperSymmetric_interval_threeEighth n hn z epsilon hepsilon
  }

end RealGramHafnians
