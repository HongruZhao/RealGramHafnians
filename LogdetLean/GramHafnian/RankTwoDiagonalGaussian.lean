import LogdetLean.GramHafnian.AuxiliaryGaussian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-!
# Even moments of a diagonal rank-two Gaussian bilinear form

This file proves, without any project axiom, the scalar analytic calculation
that results after diagonalising a real rank-two bilinear form.  Four
independent standard real Gaussians are represented by the product measure
`(gamma x gamma) x (gamma x gamma)`, where `gamma = gaussianReal 0 1`.

The result is deliberately stated first with the exact scalar Gaussian moment
sequence.  Consequently it remains valid at odd indices without a separate
parity reindexing lemma and is immediately usable by later algebraic modules.
-/

open scoped BigOperators Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- The law of a pair of independent standard real Gaussians. -/
def standardGaussianPair : Measure (Real × Real) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- The law of two independent standard Gaussian pairs. -/
def twoStandardGaussianPairs : Measure ((Real × Real) × (Real × Real)) :=
  standardGaussianPair.prod standardGaussianPair

instance : IsProbabilityMeasure standardGaussianPair := by
  unfold standardGaussianPair
  infer_instance

instance : IsProbabilityMeasure twoStandardGaussianPairs := by
  unfold twoStandardGaussianPairs
  infer_instance

instance : SigmaFinite standardGaussianPair := inferInstance
instance : SigmaFinite twoStandardGaussianPairs := inferInstance

/-- A diagonal bilinear form in two independent two-dimensional Gaussian
vectors.  If `x=w.1` and `y=w.2`, this is
`lambdaPlus*x₁*y₁ + lambdaMinus*x₂*y₂`. -/
def diagonalRankTwoBilinear (lambdaPlus lambdaMinus : Real)
    (w : (Real × Real) × (Real × Real)) : Real :=
  lambdaPlus * w.1.1 * w.2.1 + lambdaMinus * w.1.2 * w.2.2

/-- One monomial arising from the binomial expansion of the diagonal form. -/
def diagonalRankTwoMonomial (r s : Nat)
    (w : (Real × Real) × (Real × Real)) : Real :=
  (w.1.1 * w.2.1) ^ r * (w.1.2 * w.2.2) ^ s

theorem integrable_pair_coordinate_powers (r s : Nat) :
    Integrable (fun x : Real × Real ↦ x.1 ^ r * x.2 ^ s)
      standardGaussianPair := by
  unfold standardGaussianPair
  exact (integrable_pow_gaussianReal r).mul_prod
    (integrable_pow_gaussianReal s)

theorem integrable_diagonalRankTwoMonomial (r s : Nat) :
    Integrable (diagonalRankTwoMonomial r s) twoStandardGaussianPairs := by
  unfold diagonalRankTwoMonomial twoStandardGaussianPairs
  have hpair := integrable_pair_coordinate_powers r s
  have hprod : Integrable
      (fun w : (Real × Real) × (Real × Real) ↦
        (w.1.1 ^ r * w.1.2 ^ s) * (w.2.1 ^ r * w.2.2 ^ s))
      (standardGaussianPair.prod standardGaussianPair) :=
    hpair.mul_prod hpair
  apply hprod.congr
  exact Filter.Eventually.of_forall fun w ↦ by
    simp only [Pi.mul_apply]
    ring

/-- Exact factorisation of a diagonal monomial into four scalar Gaussian
moments. -/
theorem integral_diagonalRankTwoMonomial (r s : Nat) :
    (∫ w, diagonalRankTwoMonomial r s w ∂twoStandardGaussianPairs) =
      (standardRealGaussianMoment r * standardRealGaussianMoment s) ^ 2 := by
  unfold diagonalRankTwoMonomial twoStandardGaussianPairs
  have houter := integral_prod_mul
    (μ := standardGaussianPair) (ν := standardGaussianPair)
    (fun x : Real × Real ↦ x.1 ^ r * x.2 ^ s)
    (fun y : Real × Real ↦ y.1 ^ r * y.2 ^ s)
  have hinner := integral_prod_mul
    (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x : Real ↦ x ^ r) (fun y : Real ↦ y ^ s)
  have hpair :
      (∫ x : Real × Real, x.1 ^ r * x.2 ^ s ∂standardGaussianPair) =
        standardRealGaussianMoment r * standardRealGaussianMoment s := by
    unfold standardGaussianPair
    rw [hinner, integral_pow_gaussianReal_eq_standardRealGaussianMoment,
      integral_pow_gaussianReal_eq_standardRealGaussianMoment]
  rw [show (fun w : (Real × Real) × (Real × Real) ↦
      (w.1.1 * w.2.1) ^ r * (w.1.2 * w.2.2) ^ s) =
      fun w ↦ (w.1.1 ^ r * w.1.2 ^ s) *
        (w.2.1 ^ r * w.2.2 ^ s) by
    funext w
    simp only [mul_pow]
    ring]
  rw [houter, hpair]
  ring

/-- Every power of the diagonal rank-two form is integrable. -/
theorem integrable_diagonalRankTwoBilinear_pow
    (lambdaPlus lambdaMinus : Real) (m : Nat) :
    Integrable (fun w ↦ diagonalRankTwoBilinear lambdaPlus lambdaMinus w ^ m)
      twoStandardGaussianPairs := by
  rw [show (fun w : (Real × Real) × (Real × Real) ↦
      diagonalRankTwoBilinear lambdaPlus lambdaMinus w ^ m) =
      fun w ↦ ∑ r ∈ Finset.range (m + 1),
        ((m.choose r : Real) * lambdaPlus ^ r * lambdaMinus ^ (m-r)) *
          diagonalRankTwoMonomial r (m-r) w by
    funext w
    rw [diagonalRankTwoBilinear, add_pow]
    apply Finset.sum_congr rfl
    intro r hr
    unfold diagonalRankTwoMonomial
    simp only [mul_pow]
    ring]
  exact integrable_finsetSum (Finset.range (m + 1)) fun r _ ↦
    (integrable_diagonalRankTwoMonomial r (m-r)).const_mul _

/-- **Exact diagonal rank-two Gaussian moment.**  This is an axiom-free,
finite-sample identity.  Odd summands automatically disappear through
`standardRealGaussianMoment`; for an even outer exponent it is precisely the
usual even-binomial/double-factorial formula. -/
theorem integral_diagonalRankTwoBilinear_pow
    (lambdaPlus lambdaMinus : Real) (m : Nat) :
    (∫ w, diagonalRankTwoBilinear lambdaPlus lambdaMinus w ^ m
        ∂twoStandardGaussianPairs) =
      ∑ r ∈ Finset.range (m + 1),
        (m.choose r : Real) * lambdaPlus ^ r * lambdaMinus ^ (m - r) *
          (standardRealGaussianMoment r *
            standardRealGaussianMoment (m - r)) ^ 2 := by
  have hpoint (w : (Real × Real) × (Real × Real)) :
      diagonalRankTwoBilinear lambdaPlus lambdaMinus w ^ m =
        ∑ r ∈ Finset.range (m + 1),
          ((m.choose r : Real) * lambdaPlus ^ r * lambdaMinus ^ (m-r)) *
            diagonalRankTwoMonomial r (m-r) w := by
    rw [diagonalRankTwoBilinear, add_pow]
    apply Finset.sum_congr rfl
    intro r hr
    unfold diagonalRankTwoMonomial
    simp only [mul_pow]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [integral_const_mul, integral_diagonalRankTwoMonomial]
  · intro r hr
    exact (integrable_diagonalRankTwoMonomial r (m-r)).const_mul _

/-- Paper-facing even-exponent specialization of the preceding theorem. -/
theorem integral_diagonalRankTwoBilinear_pow_two_mul
    (lambdaPlus lambdaMinus : Real) (n : Nat) :
    (∫ w, diagonalRankTwoBilinear lambdaPlus lambdaMinus w ^ (2 * n)
        ∂twoStandardGaussianPairs) =
      ∑ r ∈ Finset.range (2 * n + 1),
        ((2 * n).choose r : Real) * lambdaPlus ^ r *
          lambdaMinus ^ (2 * n - r) *
          (standardRealGaussianMoment r *
            standardRealGaussianMoment (2 * n - r)) ^ 2 :=
  integral_diagonalRankTwoBilinear_pow lambdaPlus lambdaMinus (2 * n)

end

end LogdetLean.GramHafnian
