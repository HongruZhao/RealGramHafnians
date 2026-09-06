import LogdetLean.GramHafnian.ExactGramFirstMoment
import LogdetLean.GramHafnian.RankTwoConditionalMoment
import LogdetLean.GramHafnian.GaussianPairLinearIndependence
import LogdetLean.GramHafnian.RankTwoMomentAssembly
import LogdetLean.GramHafnian.RankTwoOneDimensional
/-!
# Exact literal Gaussian Gram--hafnian moments

This is the paper-facing finite endpoint.  The random matrix is the literal
iid circular complex Gaussian matrix from `ActualGramMoments`; no abstract
moment hypothesis occurs in any statement below.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- Exact four-Euclidean-Gaussian moment in every dimension `k >= 2`. -/
theorem integral_innerRankTwoBilinear_pow_prod_prod_eq_closedFourthMoment
    (k n : ℕ) (hk : 2 ≤ k) :
    (∫ z :
        ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) ×
          ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))),
        innerRankTwoBilinear z.1.1 z.1.2 z.2 ^ (2 * n)
          ∂(((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
              (stdGaussian (EuclideanSpace ℝ (Fin k)))).prod
            ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
              (stdGaussian (EuclideanSpace ℝ (Fin k)))))) =
      closedFourthMoment k n := by
  apply
    integral_innerRankTwoBilinear_pow_prod_prod_eq_closedFourthMoment_of_ae
      k n hk
  filter_upwards [ae_linearIndependent_gaussianPair k hk] with g hli
  exact integral_innerRankTwoBilinear_pow_two_mul_of_linearIndependent
    g.1 g.2 n hli

/-- Coordinate-field restatement of the exact rank-two outer moment for
`k >= 2`. -/
theorem integral_rankTwoBilinear_fourRealFields_eq_closedFourthMoment
    (k n : ℕ) (hk : 2 ≤ k) :
    (∫ w : FourRealFields k,
        rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 ^ (2 * n)
          ∂fourRealGaussianFieldsMeasure k) =
      closedFourthMoment k n := by
  rw [integral_rankTwoBilinear_fourRealFields_eq_euclidean]
  exact integral_innerRankTwoBilinear_pow_prod_prod_eq_closedFourthMoment
    k n hk

/-- **Literal Gaussian Gram--hafnian fourth moment.**  In every positive
auxiliary dimension, the fourth absolute moment of the Gram hafnian is the
exact finite closed form. -/
theorem actualGramFourthMomentReal_eq_closedFourthMoment
    (k n : ℕ) (hk : 0 < k) :
    actualGramFourthMomentReal k n = closedFourthMoment k n := by
  rw [actualGramFourthMomentReal_eq_realGaussianRankTwoIntegral]
  by_cases hk1 : k = 1
  · subst k
    exact integral_rankTwoBilinear_fin_one_pow_two_mul_eq_closedFourthMoment n
  · exact integral_rankTwoBilinear_fourRealFields_eq_closedFourthMoment
      k n (by omega)

/-- Complex-valued restatement of the literal fourth-moment identity. -/
theorem actualGramFourthMoment_eq_closedFourthMoment
    (k n : ℕ) (hk : 0 < k) :
    actualGramFourthMoment k n = (closedFourthMoment k n : ℂ) := by
  rw [actualGramFourthMoment_eq_ofReal,
    actualGramFourthMomentReal_eq_closedFourthMoment k n hk]

/-- The literal normalized second-moment ratio of the nonnegative random
variable `|haf(XᵀX)|²`. -/
noncomputable def actualGramSecondMomentRatio (k n : ℕ) : ℝ :=
  actualGramFirstMomentReal k n ^ 2 / actualGramFourthMomentReal k n

/-- **Exact literal normalized moment ratio.** -/
theorem actualGramSecondMomentRatio_eq_gramSecondMomentRatio
    (k n : ℕ) (hk : 0 < k) :
    actualGramSecondMomentRatio k n = gramSecondMomentRatio k n := by
  unfold actualGramSecondMomentRatio
  exact exact_normalized_second_moment_of_closed_forms
    k n hk _ _
      (actualGramFirstMomentReal_eq_closedFirstMoment k n hk)
      (actualGramFourthMomentReal_eq_closedFourthMoment k n hk)

/-- Expanded form of the exact normalized-ratio theorem. -/
theorem actualGram_moment_ratio_eq_gramSecondMomentRatio
    (k n : ℕ) (hk : 0 < k) :
    actualGramFirstMomentReal k n ^ 2 /
        actualGramFourthMomentReal k n =
      gramSecondMomentRatio k n := by
  exact actualGramSecondMomentRatio_eq_gramSecondMomentRatio k n hk

end

end LogdetLean.GramHafnian
