import LogdetLean.GramHafnian.GramMomentFubini
import LogdetLean.GramHafnian.FiniteMomentAlgebra
/-!
# Actual first and fourth moments of a Gaussian Gram hafnian

This module assembles the literal auxiliary-Gaussian hafnian identity, the
proved joint polynomial integrability/Fubini swap, and the circular-column
Wick contractions.  The remaining outer real-Gaussian integrals are kept as
explicit finite-dimensional endpoints until their closed forms are imported.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

variable {n k : ℕ}

theorem bilinearDot_realVectorToComplex (g h : Fin k → ℝ) :
    bilinearDot (realVectorToComplex g) (realVectorToComplex h) =
      ((bilinearDot g h : ℝ) : ℂ) := by
  unfold bilinearDot realVectorToComplex
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.ofReal_mul]

theorem rankTwoBilinear_realVectorToComplex
    (g₁ g₂ h₁ h₂ : Fin k → ℝ) :
    rankTwoBilinear (realVectorToComplex g₁) (realVectorToComplex g₂)
        (realVectorToComplex h₁) (realVectorToComplex h₂) =
      ((rankTwoBilinear g₁ g₂ h₁ h₂ : ℝ) : ℂ) := by
  unfold rankTwoBilinear
  rw [bilinearDot_realVectorToComplex, bilinearDot_realVectorToComplex,
    bilinearDot_realVectorToComplex, bilinearDot_realVectorToComplex,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]

theorem transposeGram_conjugateRowMatrix_apply
    (X : ComplexColumnMatrix n k) (i j : Fin (2 * n)) :
    transposeGram (conjugateRowMatrix X) i j =
      conj (transposeGram (rowMatrix X) i j) := by
  simp only [transposeGram_apply, conjugateRowMatrix, rowMatrix, map_sum,
    map_mul]

theorem gramHafnian_conjugateRowMatrix (X : ComplexColumnMatrix n k) :
    gramHafnian (conjugateRowMatrix X) =
      conj (gramHafnian (rowMatrix X)) := by
  classical
  unfold gramHafnian hafnian matchingMonomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro M _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact transposeGram_conjugateRowMatrix_apply X i (M i)

theorem secondAuxiliaryIntegrand_eq_auxiliaryProducts
    (w : TwoRealFields k) (X : ComplexColumnMatrix n k) :
    secondAuxiliaryIntegrand w X =
      complexAuxiliaryFieldProduct (rowMatrix X) w.1 *
        complexAuxiliaryFieldProduct (conjugateRowMatrix X) w.2 := by
  unfold secondAuxiliaryIntegrand columnSecondProduct columnSecondIntegrand
    complexColumnForm conjugateColumnForm complexAuxiliaryFieldProduct
    realVectorToComplex rowMatrix conjugateRowMatrix
  rw [Finset.prod_mul_distrib]

theorem fourthAuxiliaryIntegrand_eq_auxiliaryProducts
    (w : FourRealFields k) (X : ComplexColumnMatrix n k) :
    fourthAuxiliaryIntegrand w X =
      (complexAuxiliaryFieldProduct (rowMatrix X) w.1.1 *
        complexAuxiliaryFieldProduct (rowMatrix X) w.1.2) *
      (complexAuxiliaryFieldProduct (conjugateRowMatrix X) w.2.1 *
        complexAuxiliaryFieldProduct (conjugateRowMatrix X) w.2.2) := by
  unfold fourthAuxiliaryIntegrand columnFourthProduct columnFourthIntegrand
    complexColumnForm conjugateColumnForm complexAuxiliaryFieldProduct
    realVectorToComplex rowMatrix conjugateRowMatrix
  repeat' rw [Finset.prod_mul_distrib]
  ring

/-- Integrating the two real auxiliary fields gives the literal absolute
square of the Gram hafnian. -/
theorem integral_secondAuxiliaryIntegrand_fields
    (X : ComplexColumnMatrix n k) :
    ∫ w, secondAuxiliaryIntegrand w X
        ∂(twoRealGaussianFieldsMeasure k) =
      gramHafnian (rowMatrix X) * conj (gramHafnian (rowMatrix X)) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun w ↦
    secondAuxiliaryIntegrand_eq_auxiliaryProducts w X)]
  unfold twoRealGaussianFieldsMeasure standardRealGaussianVectorMeasure
  rw [integral_prod_mul,
    integral_complexAuxiliaryFieldProduct_eq_gramHafnian,
    integral_complexAuxiliaryFieldProduct_eq_gramHafnian,
    gramHafnian_conjugateRowMatrix]

theorem integral_twoAuxiliaryProducts
    (Y Z : Matrix (Fin k) (Fin (2 * n)) ℂ) :
    ∫ w : TwoRealFields k,
        complexAuxiliaryFieldProduct Y w.1 *
          complexAuxiliaryFieldProduct Z w.2
        ∂(twoRealGaussianFieldsMeasure k) =
      gramHafnian Y * gramHafnian Z := by
  unfold twoRealGaussianFieldsMeasure standardRealGaussianVectorMeasure
  rw [integral_prod_mul,
    integral_complexAuxiliaryFieldProduct_eq_gramHafnian,
    integral_complexAuxiliaryFieldProduct_eq_gramHafnian]

/-- Integrating the four real auxiliary fields gives the literal fourth
absolute moment integrand. -/
theorem integral_fourthAuxiliaryIntegrand_fields
    (X : ComplexColumnMatrix n k) :
    ∫ w, fourthAuxiliaryIntegrand w X
        ∂(fourRealGaussianFieldsMeasure k) =
      (gramHafnian (rowMatrix X) * conj (gramHafnian (rowMatrix X))) ^ 2 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun w ↦
    fourthAuxiliaryIntegrand_eq_auxiliaryProducts w X)]
  unfold fourRealGaussianFieldsMeasure
  calc
    (∫ w : FourRealFields k,
        (complexAuxiliaryFieldProduct (rowMatrix X) w.1.1 *
          complexAuxiliaryFieldProduct (rowMatrix X) w.1.2) *
        (complexAuxiliaryFieldProduct (conjugateRowMatrix X) w.2.1 *
          complexAuxiliaryFieldProduct (conjugateRowMatrix X) w.2.2)
        ∂(twoRealGaussianFieldsMeasure k).prod
          (twoRealGaussianFieldsMeasure k)) =
      (∫ u : TwoRealFields k,
          complexAuxiliaryFieldProduct (rowMatrix X) u.1 *
            complexAuxiliaryFieldProduct (rowMatrix X) u.2
          ∂twoRealGaussianFieldsMeasure k) *
        (∫ v : TwoRealFields k,
          complexAuxiliaryFieldProduct (conjugateRowMatrix X) v.1 *
          complexAuxiliaryFieldProduct (conjugateRowMatrix X) v.2
          ∂twoRealGaussianFieldsMeasure k) := by
        exact integral_prod_mul
          (μ := twoRealGaussianFieldsMeasure k)
          (ν := twoRealGaussianFieldsMeasure k) (L := ℂ)
          (fun u : TwoRealFields k ↦
            complexAuxiliaryFieldProduct (rowMatrix X) u.1 *
              complexAuxiliaryFieldProduct (rowMatrix X) u.2)
          (fun v : TwoRealFields k ↦
            complexAuxiliaryFieldProduct (conjugateRowMatrix X) v.1 *
              complexAuxiliaryFieldProduct (conjugateRowMatrix X) v.2)
    _ = (gramHafnian (rowMatrix X) * gramHafnian (rowMatrix X)) *
          (gramHafnian (conjugateRowMatrix X) *
            gramHafnian (conjugateRowMatrix X)) := by
      rw [integral_twoAuxiliaryProducts, integral_twoAuxiliaryProducts]
    _ = (gramHafnian (rowMatrix X) *
          conj (gramHafnian (rowMatrix X))) ^ 2 := by
      rw [gramHafnian_conjugateRowMatrix]
      ring

/-- The actual first absolute-square moment, as a literal integral over an
iid circular complex Gaussian matrix. -/
def actualGramFirstMoment (k n : ℕ) : ℂ :=
  ∫ X, gramHafnian (rowMatrix X) * conj (gramHafnian (rowMatrix X))
    ∂(circularGaussianColumnMatrixMeasure n k)

/-- The actual fourth absolute moment. -/
def actualGramFourthMoment (k n : ℕ) : ℂ :=
  ∫ X, (gramHafnian (rowMatrix X) * conj (gramHafnian (rowMatrix X))) ^ 2
    ∂(circularGaussianColumnMatrixMeasure n k)

/-- Real-valued form of the first absolute-square moment. -/
def actualGramFirstMomentReal (k n : ℕ) : ℝ :=
  ∫ X, Complex.normSq (gramHafnian (rowMatrix X))
    ∂(circularGaussianColumnMatrixMeasure n k)

/-- Real-valued form of the fourth absolute moment. -/
def actualGramFourthMomentReal (k n : ℕ) : ℝ :=
  ∫ X, Complex.normSq (gramHafnian (rowMatrix X)) ^ 2
    ∂(circularGaussianColumnMatrixMeasure n k)

theorem actualGramFirstMoment_eq_ofReal :
    actualGramFirstMoment k n = (actualGramFirstMomentReal k n : ℂ) := by
  unfold actualGramFirstMoment actualGramFirstMomentReal
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X ↦ by
    change gramHafnian (rowMatrix X) * conj (gramHafnian (rowMatrix X)) =
      (Complex.normSq (gramHafnian (rowMatrix X)) : ℂ)
    exact Complex.mul_conj _

theorem actualGramFourthMoment_eq_ofReal :
    actualGramFourthMoment k n = (actualGramFourthMomentReal k n : ℂ) := by
  unfold actualGramFourthMoment actualGramFourthMomentReal
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X ↦ by
    dsimp only
    rw [Complex.mul_conj]
    exact (Complex.ofReal_pow _ 2).symm

theorem actualGramFirstMoment_eq_iterated_auxiliary :
    actualGramFirstMoment k n =
      ∫ X, ∫ w, secondAuxiliaryIntegrand w X
          ∂(twoRealGaussianFieldsMeasure k)
        ∂(circularGaussianColumnMatrixMeasure n k) := by
  unfold actualGramFirstMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X ↦
    (integral_secondAuxiliaryIntegrand_fields X).symm

theorem actualGramFourthMoment_eq_iterated_auxiliary :
    actualGramFourthMoment k n =
      ∫ X, ∫ w, fourthAuxiliaryIntegrand w X
          ∂(fourRealGaussianFieldsMeasure k)
        ∂(circularGaussianColumnMatrixMeasure n k) := by
  unfold actualGramFourthMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X ↦
    (integral_fourthAuxiliaryIntegrand_fields X).symm

/-- Exact M1 reduction after the justified Fubini swap. -/
theorem actualGramFirstMoment_eq_realGaussianBilinearIntegral :
    actualGramFirstMoment k n =
      ∫ w : TwoRealFields k,
        ((bilinearDot w.1 w.2 : ℝ) : ℂ) ^ (2 * n)
        ∂(twoRealGaussianFieldsMeasure k) := by
  rw [actualGramFirstMoment_eq_iterated_auxiliary]
  rw [← integral_integral_swap integrable_uncurry_secondAuxiliaryIntegrand]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w ↦ by
    change (∫ X, columnSecondProduct (realVectorToComplex w.1)
      (realVectorToComplex w.2) X
        ∂(Measure.pi fun _ : Fin (2 * n) ↦ circularGaussianVector k)) = _
    rw [integral_columnSecondProduct_circularGaussianVector,
      bilinearDot_realVectorToComplex]

/-- Exact M2 reduction after the justified Fubini swap. -/
theorem actualGramFourthMoment_eq_realGaussianRankTwoIntegral :
    actualGramFourthMoment k n =
      ∫ w : FourRealFields k,
        ((rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 : ℝ) : ℂ) ^ (2 * n)
        ∂(fourRealGaussianFieldsMeasure k) := by
  rw [actualGramFourthMoment_eq_iterated_auxiliary]
  rw [← integral_integral_swap integrable_uncurry_fourthAuxiliaryIntegrand]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w ↦ by
    change (∫ X, columnFourthProduct
      (realVectorToComplex w.1.1) (realVectorToComplex w.1.2)
      (realVectorToComplex w.2.1) (realVectorToComplex w.2.2) X
        ∂(Measure.pi fun _ : Fin (2 * n) ↦ circularGaussianVector k)) = _
    rw [integral_columnFourthProduct_circularGaussianVector,
      rankTwoBilinear_realVectorToComplex]

theorem actualGramFirstMomentReal_eq_realGaussianBilinearIntegral :
    actualGramFirstMomentReal k n =
      ∫ w : TwoRealFields k,
        bilinearDot w.1 w.2 ^ (2 * n)
        ∂(twoRealGaussianFieldsMeasure k) := by
  apply Complex.ofReal_injective
  rw [← actualGramFirstMoment_eq_ofReal,
    actualGramFirstMoment_eq_realGaussianBilinearIntegral]
  simp_rw [← Complex.ofReal_pow]
  exact integral_complex_ofReal

theorem actualGramFourthMomentReal_eq_realGaussianRankTwoIntegral :
    actualGramFourthMomentReal k n =
      ∫ w : FourRealFields k,
        rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 ^ (2 * n)
        ∂(fourRealGaussianFieldsMeasure k) := by
  apply Complex.ofReal_injective
  rw [← actualGramFourthMoment_eq_ofReal,
    actualGramFourthMoment_eq_realGaussianRankTwoIntegral]
  simp_rw [← Complex.ofReal_pow]
  exact integral_complex_ofReal

end

end LogdetLean.GramHafnian
