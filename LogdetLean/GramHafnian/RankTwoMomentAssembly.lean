import LogdetLean.GramHafnian.RankTwoGaussianIntegrability
/-!
# Assembly of the exact rank-two Gaussian moment

This file isolates the final Fubini/radial--angle step from the conditional
rank-two calculation.  Its hypothesis is an almost-everywhere conditional
moment identity, which is exactly the strength needed in the outer integral.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory Module Finset

namespace LogdetLean.GramHafnian

noncomputable section

/-- Once the squared-binomial conditional formula holds almost everywhere,
the literal four-vector Gaussian integral is the closed fourth moment. -/
theorem integral_innerRankTwoBilinear_pow_prod_prod_eq_closedFourthMoment_of_ae
    (k n : ℕ) (hk : 2 ≤ k)
    (hconditional :
      ∀ᵐ g : (EuclideanSpace ℝ (Fin k)) ×
          (EuclideanSpace ℝ (Fin k))
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin k)))),
        (∫ h : (EuclideanSpace ℝ (Fin k)) ×
            (EuclideanSpace ℝ (Fin k)),
            innerRankTwoBilinear g.1 g.2 h ^ (2 * n)
              ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
                (stdGaussian (EuclideanSpace ℝ (Fin k))))) =
          ((2 * n).factorial : ℝ) *
            ∑ j ∈ range (n + 1),
              ((n.choose j : ℕ) : ℝ) ^ 2 *
                (‖g.1‖ ^ 2 * ‖g.2‖ ^ 2) ^ (n - j) *
                (inner ℝ g.1 g.2) ^ (2 * j)) :
    (∫ z :
        ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) ×
          ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))),
        innerRankTwoBilinear z.1.1 z.1.2 z.2 ^ (2 * n)
          ∂(((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
              (stdGaussian (EuclideanSpace ℝ (Fin k)))).prod
            ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
              (stdGaussian (EuclideanSpace ℝ (Fin k)))))) =
      closedFourthMoment k n := by
  let E := EuclideanSpace ℝ (Fin k)
  let μ := (stdGaussian E).prod (stdGaussian E)
  have hdim : finrank ℝ E = k := by simp [E]
  have hfull : Integrable
      (fun z : (E × E) × (E × E) ↦
        innerRankTwoBilinear z.1.1 z.1.2 z.2 ^ (2 * n))
      (μ.prod μ) := by
    simpa only [E, μ] using
      (integrable_innerRankTwoBilinear_pow_stdGaussian_prod_prod
        (E := E) (2 * n))
  calc
    (∫ z : (E × E) × (E × E),
        innerRankTwoBilinear z.1.1 z.1.2 z.2 ^ (2 * n) ∂(μ.prod μ)) =
        ∫ g : E × E, ∫ h : E × E,
          innerRankTwoBilinear g.1 g.2 h ^ (2 * n) ∂μ ∂μ := by
      exact integral_prod _ hfull
    _ = ∫ g : E × E,
          ((2 * n).factorial : ℝ) *
            ∑ j ∈ range (n + 1),
              ((n.choose j : ℕ) : ℝ) ^ 2 *
                (‖g.1‖ ^ 2 * ‖g.2‖ ^ 2) ^ (n - j) *
                (inner ℝ g.1 g.2) ^ (2 * j) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hconditional] with g hg
      exact hg
    _ = ((2 * n).factorial : ℝ) *
          ∫ g : E × E,
            ∑ j ∈ range (n + 1),
              ((n.choose j : ℕ) : ℝ) ^ 2 *
                (‖g.1‖ ^ 2 * ‖g.2‖ ^ 2) ^ (n - j) *
                (inner ℝ g.1 g.2) ^ (2 * j) ∂μ := by
      rw [integral_const_mul]
    _ = ((2 * n).factorial : ℝ) *
          ∑ j ∈ range (n + 1),
            ∫ g : E × E,
              ((n.choose j : ℕ) : ℝ) ^ 2 *
                (‖g.1‖ ^ 2 * ‖g.2‖ ^ 2) ^ (n - j) *
                (inner ℝ g.1 g.2) ^ (2 * j) ∂μ := by
      congr 1
      rw [integral_finsetSum]
      intro j hj
      have hjn : j ≤ n := by simpa using (mem_range.mp hj)
      simpa only [μ, mul_assoc] using
        ((integrable_innerMonomial_gaussianProduct
          (E := E) k n j hdim hk hjn).const_mul
            (((n.choose j : ℕ) : ℝ) ^ 2))
    _ = ((2 * n).factorial : ℝ) *
          ∑ j ∈ range (n + 1),
            ((n.choose j : ℕ) : ℝ) ^ 2 *
              (dimensionProduct k n ^ 2 * pochhammerRatio k j) := by
      congr 1
      apply sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by simpa using (mem_range.mp hj)
      rw [show (fun g : E × E ↦
          ((n.choose j : ℕ) : ℝ) ^ 2 *
            (‖g.1‖ ^ 2 * ‖g.2‖ ^ 2) ^ (n - j) *
            (inner ℝ g.1 g.2) ^ (2 * j)) =
          fun g ↦ ((n.choose j : ℕ) : ℝ) ^ 2 *
            ((‖g.1‖ ^ 2 * ‖g.2‖ ^ 2) ^ (n - j) *
              (inner ℝ g.1 g.2) ^ (2 * j)) by
            funext g
            ring]
      rw [integral_const_mul]
      rw [integral_innerMonomial_gaussianProduct
        (E := E) k n j hdim hk hjn]
    _ = closedFourthMoment k n := by
      rw [closedFourthMoment, finiteCorrection]
      rw [mul_assoc]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [finiteTerm]
      ring

end

end LogdetLean.GramHafnian
