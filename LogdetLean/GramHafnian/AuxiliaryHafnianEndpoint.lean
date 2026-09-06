import LogdetLean.GramHafnian.AuxiliaryGaussian
/-!
# Exact endpoint for the auxiliary-Gaussian hafnian identity

Both sides of the desired identity are reduced here to literal finite sums.
The remaining statement is purely combinatorial: regroup row-colourings with
even multiplicities by the perfect matchings inside every colour class.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

variable {n k : ℕ}

/-- The finite colouring sum produced by actual iid standard-Gaussian
integration. -/
noncomputable def gaussianWickColoringSum
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ) : ℂ :=
  ∑ c : Fin (2 * n) → Fin k,
    complexColoringCoefficient X c *
      ∏ a, (standardRealGaussianMoment (colorMultiplicity c a) : ℂ)

/-- The finite matching-colouring sum obtained by expanding the transpose
Gram hafnian. -/
noncomputable def gramMatchingColoringSum
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ) : ℂ :=
  ∑ M : PerfectMatching n, ∑ c : PairColoring M k,
    coloredMatchingMonomial X M c

theorem integral_complexAuxiliaryFieldProduct_eq_gaussianWickColoringSum
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ) :
    ∫ g, complexAuxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : Fin k ↦ gaussianReal 0 1) =
      gaussianWickColoringSum X := by
  exact integral_complexAuxiliaryFieldProduct_standardGaussian X

theorem gramHafnian_eq_gramMatchingColoringSum
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ) :
    gramHafnian X = gramMatchingColoringSum X := by
  exact gramHafnian_eq_sum_coloredMatchings X

/-- The all-orders auxiliary-Gaussian hafnian identity is now *equivalent*
to one explicit equality of finite sums.  There is no remaining measure
theory or Gaussian analysis in the right-hand statement. -/
theorem auxiliaryGaussian_hafnian_iff_finite_regrouping
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ) :
    (∫ g, complexAuxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : Fin k ↦ gaussianReal 0 1)) = gramHafnian X ↔
      gaussianWickColoringSum X = gramMatchingColoringSum X := by
  rw [integral_complexAuxiliaryFieldProduct_eq_gaussianWickColoringSum,
    gramHafnian_eq_gramMatchingColoringSum]

end LogdetLean.GramHafnian
