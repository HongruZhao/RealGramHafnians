import LogdetLean.GramHafnian.CircularGaussianSecondWick
import LogdetLean.GramHafnian.WickRegrouping
/-!
# Joint polynomial integrability for Gram--hafnian moments

The actual moment calculation interchanges the iid complex columns with two
or four real Gaussian auxiliary fields.  This file proves the required
joint integrability by a literal finite colouring expansion.  Consequently
the later use of Fubini is a theorem application, not a hidden assumption.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

variable {n k : ℕ}

abbrev ComplexColumnMatrix (n k : ℕ) :=
  Fin (2 * n) → (Fin k → ℂ)

def rowMatrix (X : ComplexColumnMatrix n k) :
    Matrix (Fin k) (Fin (2 * n)) ℂ :=
  fun a i ↦ X i a

def conjugateRowMatrix (X : ComplexColumnMatrix n k) :
    Matrix (Fin k) (Fin (2 * n)) ℂ :=
  fun a i ↦ conj (X i a)

def realVectorToComplex (g : Fin k → ℝ) : Fin k → ℂ :=
  fun a ↦ (g a : ℂ)

def circularGaussianColumnMatrixMeasure (n k : ℕ) :
    Measure (ComplexColumnMatrix n k) :=
  Measure.pi fun _ : Fin (2 * n) ↦ circularGaussianVector k

instance (n k : ℕ) : SigmaFinite (circularGaussianColumnMatrixMeasure n k) := by
  unfold circularGaussianColumnMatrixMeasure
  infer_instance

instance (n k : ℕ) : IsProbabilityMeasure
    (circularGaussianColumnMatrixMeasure n k) := by
  unfold circularGaussianColumnMatrixMeasure
  infer_instance

/-- A product of selected coordinates of one real Gaussian vector, embedded
in `ℂ`. -/
def complexRealColorProduct
    (c : Fin (2 * n) → Fin k) (g : Fin k → ℝ) : ℂ :=
  ∏ i, (g (c i) : ℂ)

theorem complexRealColorProduct_eq_coordinatePowers
    (c : Fin (2 * n) → Fin k) (g : Fin k → ℝ) :
    complexRealColorProduct c g =
      complexCoordinatePowerProduct (colorMultiplicity c) g := by
  unfold complexRealColorProduct complexCoordinatePowerProduct
  exact prod_comp_eq_coordinatePowerProduct c (fun a ↦ (g a : ℂ))

theorem integrable_complexRealColorProduct
    (c : Fin (2 * n) → Fin k) :
    Integrable (complexRealColorProduct c)
      (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1) := by
  rw [show complexRealColorProduct c =
      complexCoordinatePowerProduct (colorMultiplicity c) by
    funext g
    exact complexRealColorProduct_eq_coordinatePowers c g]
  unfold complexCoordinatePowerProduct
  exact Integrable.fintype_prod fun a ↦ by
    have h : Integrable (fun x : ℝ ↦
        ((x ^ colorMultiplicity c a : ℝ) : ℂ)) (gaussianReal 0 1) :=
      (integrable_pow_gaussianReal (colorMultiplicity c a)).ofReal
    simpa only [Complex.ofReal_pow] using h

abbrev TwoRealFields (k : ℕ) :=
  (Fin k → ℝ) × (Fin k → ℝ)

abbrev FourRealFields (k : ℕ) :=
  ((Fin k → ℝ) × (Fin k → ℝ)) ×
    ((Fin k → ℝ) × (Fin k → ℝ))

def standardRealGaussianVectorMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k ↦ gaussianReal 0 1

def twoRealGaussianFieldsMeasure (k : ℕ) : Measure (TwoRealFields k) :=
  (standardRealGaussianVectorMeasure k).prod
    (standardRealGaussianVectorMeasure k)

def fourRealGaussianFieldsMeasure (k : ℕ) : Measure (FourRealFields k) :=
  (twoRealGaussianFieldsMeasure k).prod (twoRealGaussianFieldsMeasure k)

instance (k : ℕ) : SigmaFinite (standardRealGaussianVectorMeasure k) := by
  unfold standardRealGaussianVectorMeasure
  infer_instance

instance (k : ℕ) : IsProbabilityMeasure
    (standardRealGaussianVectorMeasure k) := by
  unfold standardRealGaussianVectorMeasure
  infer_instance

instance (k : ℕ) : SigmaFinite (twoRealGaussianFieldsMeasure k) := by
  unfold twoRealGaussianFieldsMeasure
  infer_instance

instance (k : ℕ) : SigmaFinite (fourRealGaussianFieldsMeasure k) := by
  unfold fourRealGaussianFieldsMeasure
  infer_instance

def secondAuxiliaryIntegrand
    (w : TwoRealFields k) (X : ComplexColumnMatrix n k) : ℂ :=
  columnSecondProduct (realVectorToComplex w.1)
    (realVectorToComplex w.2) X

def fourthAuxiliaryIntegrand
    (w : FourRealFields k) (X : ComplexColumnMatrix n k) : ℂ :=
  columnFourthProduct (realVectorToComplex w.1.1)
    (realVectorToComplex w.1.2) (realVectorToComplex w.2.1)
    (realVectorToComplex w.2.2) X

def secondExpansionTerm
    (A B : Fin (2 * n) → Fin k)
    (w : TwoRealFields k) (X : ComplexColumnMatrix n k) : ℂ :=
  complexRealColorProduct A w.1 * complexRealColorProduct B w.2 *
    ∏ i, coordinateSecondMonomial (X i) (A i) (B i)

def fourthExpansionTerm
    (A B C D : Fin (2 * n) → Fin k)
    (w : FourRealFields k) (X : ComplexColumnMatrix n k) : ℂ :=
  (complexRealColorProduct A w.1.1 * complexRealColorProduct B w.1.2) *
    (complexRealColorProduct C w.2.1 * complexRealColorProduct D w.2.2) *
      ∏ i, coordinateFourthMonomial (X i) (A i) (B i) (C i) (D i)

theorem secondAuxiliaryIntegrand_eq_expansion
    (w : TwoRealFields k) (X : ComplexColumnMatrix n k) :
    secondAuxiliaryIntegrand w X =
      ∑ B : Fin (2 * n) → Fin k, ∑ A : Fin (2 * n) → Fin k,
        secondExpansionTerm A B w X := by
  classical
  unfold secondAuxiliaryIntegrand columnSecondProduct
  simp_rw [columnSecondIntegrand_eq_expanded]
  unfold expandedColumnSecond
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro A _
  unfold secondExpansionTerm complexRealColorProduct realVectorToComplex
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

theorem fourthAuxiliaryIntegrand_eq_expansion
    (w : FourRealFields k) (X : ComplexColumnMatrix n k) :
    fourthAuxiliaryIntegrand w X =
      ∑ D : Fin (2 * n) → Fin k, ∑ C : Fin (2 * n) → Fin k,
        ∑ B : Fin (2 * n) → Fin k, ∑ A : Fin (2 * n) → Fin k,
          fourthExpansionTerm A B C D w X := by
  classical
  unfold fourthAuxiliaryIntegrand columnFourthProduct
  simp_rw [columnFourthIntegrand_eq_expanded]
  unfold expandedColumnFourth
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro C _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro A _
  unfold fourthExpansionTerm complexRealColorProduct realVectorToComplex
  repeat' rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem integrable_secondExpansionTerm
    (A B : Fin (2 * n) → Fin k) :
    Integrable (Function.uncurry (secondExpansionTerm A B))
      ((twoRealGaussianFieldsMeasure k).prod
        (circularGaussianColumnMatrixMeasure n k)) := by
  have hA := integrable_complexRealColorProduct A
  have hB := integrable_complexRealColorProduct B
  have hfields : Integrable (fun w : TwoRealFields k ↦
      complexRealColorProduct A w.1 * complexRealColorProduct B w.2)
      (twoRealGaussianFieldsMeasure k) := by
    exact hA.mul_prod hB
  have hcolumns : Integrable (fun X : ComplexColumnMatrix n k ↦
      ∏ i, coordinateSecondMonomial (X i) (A i) (B i))
      (circularGaussianColumnMatrixMeasure n k) := by
    unfold circularGaussianColumnMatrixMeasure
    exact Integrable.fintype_prod fun i ↦
      integrable_coordinateSecondMonomial_circularGaussianVector (A i) (B i)
  exact hfields.mul_prod hcolumns

theorem integrable_fourthExpansionTerm
    (A B C D : Fin (2 * n) → Fin k) :
    Integrable (Function.uncurry (fourthExpansionTerm A B C D))
      ((fourRealGaussianFieldsMeasure k).prod
        (circularGaussianColumnMatrixMeasure n k)) := by
  have hAB : Integrable (fun w : TwoRealFields k ↦
      complexRealColorProduct A w.1 * complexRealColorProduct B w.2)
      (twoRealGaussianFieldsMeasure k) :=
    (integrable_complexRealColorProduct A).mul_prod
      (integrable_complexRealColorProduct B)
  have hCD : Integrable (fun w : TwoRealFields k ↦
      complexRealColorProduct C w.1 * complexRealColorProduct D w.2)
      (twoRealGaussianFieldsMeasure k) :=
    (integrable_complexRealColorProduct C).mul_prod
      (integrable_complexRealColorProduct D)
  have hfields : Integrable (fun w : FourRealFields k ↦
      (complexRealColorProduct A w.1.1 * complexRealColorProduct B w.1.2) *
        (complexRealColorProduct C w.2.1 * complexRealColorProduct D w.2.2))
      (fourRealGaussianFieldsMeasure k) := hAB.mul_prod hCD
  have hcolumns : Integrable (fun X : ComplexColumnMatrix n k ↦
      ∏ i, coordinateFourthMonomial (X i)
        (A i) (B i) (C i) (D i))
      (circularGaussianColumnMatrixMeasure n k) := by
    unfold circularGaussianColumnMatrixMeasure
    exact Integrable.fintype_prod fun i ↦
      integrable_coordinateFourthMonomial_circularGaussianVector
        (A i) (B i) (C i) (D i)
  exact hfields.mul_prod hcolumns

/-- Joint integrability needed to swap the two auxiliary fields with the
complex columns in the actual first-moment calculation. -/
theorem integrable_uncurry_secondAuxiliaryIntegrand :
    Integrable (Function.uncurry (secondAuxiliaryIntegrand (n := n) (k := k)))
      ((twoRealGaussianFieldsMeasure k).prod
        (circularGaussianColumnMatrixMeasure n k)) := by
  apply Integrable.congr
    (integrable_finsetSum _ fun B _ ↦
      integrable_finsetSum _ fun A _ ↦ integrable_secondExpansionTerm A B)
  exact Filter.Eventually.of_forall fun z ↦
    (secondAuxiliaryIntegrand_eq_expansion z.1 z.2).symm

/-- Joint integrability needed to swap the four auxiliary fields with the
complex columns in the actual fourth-moment calculation. -/
theorem integrable_uncurry_fourthAuxiliaryIntegrand :
    Integrable (Function.uncurry (fourthAuxiliaryIntegrand (n := n) (k := k)))
      ((fourRealGaussianFieldsMeasure k).prod
        (circularGaussianColumnMatrixMeasure n k)) := by
  apply Integrable.congr
    (integrable_finsetSum _ fun D _ ↦
      integrable_finsetSum _ fun C _ ↦
        integrable_finsetSum _ fun B _ ↦
          integrable_finsetSum _ fun A _ ↦
            integrable_fourthExpansionTerm A B C D)
  exact Filter.Eventually.of_forall fun z ↦
    (fourthAuxiliaryIntegrand_eq_expansion z.1 z.2).symm

end

end LogdetLean.GramHafnian
