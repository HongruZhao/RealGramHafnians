import RealGramHafnians.Proofs.SharpRealConstant
/-!
# Probability-capped sharp real small-ball bounds

The finite estimates in `SharpRealSmallBall` and `SharpRealConstant` are
linear in the normalized radius.  This module records the paper-facing
versions capped by the tautological probability bound `1`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Real ENNReal Nat

namespace LogdetLean.GramHafnian

noncomputable section

/-- Exact finite shifted-anticoncentration theorem with the probability
cap made explicit. -/
theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_min_one_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k)
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
theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_min_one_exp_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) (hkn : n + 2 ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      min 1
        (ENNReal.ofReal
            (realGaussianIntervalPrefactor 1 *
              Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
              Real.exp
                ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
                  (4 * ((k - n - 1 : ℕ) : ℝ)))) *
          ENNReal.ofReal epsilon) := by
  apply le_min
  · calc
      (standardRealGaussianColumnMatrixMeasure n k)
          {X | |realGramHafnianObservable n k X - z| ≤
            epsilon * realGramHafnianRMS n k} ≤
        (standardRealGaussianColumnMatrixMeasure n k) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := IsProbabilityMeasure.measure_univ
  · exact
      standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_exp_sharp
        hn hk hdim hkn z epsilon hepsilon

/-- Paper-facing real-valued form of the exact capped theorem.  The
coefficient on the right is literally the normalized Gamma-product
coefficient appearing in the manuscript. -/
theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBallProbability_le_min_one_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k)
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

end

end LogdetLean.GramHafnian
