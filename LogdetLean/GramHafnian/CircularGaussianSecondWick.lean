import LogdetLean.GramHafnian.CircularGaussianVectorWick
/-!
# Literal second-moment Wick bridge for iid circular Gaussian columns

This is the two-field counterpart of `CircularGaussianVectorWick`.  It is
used for the first absolute-square moment of a Gram hafnian.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

variable {n k : ℕ}

def singleExponent (a i : Fin k) : ℕ :=
  if i = a then 1 else 0

theorem singleExponent_le_two (a i : Fin k) : singleExponent a i ≤ 2 := by
  unfold singleExponent
  split_ifs <;> omega

theorem prod_pow_singleExponent
    (f : Fin k → ℂ) (a : Fin k) :
    (∏ i, f i ^ singleExponent a i) = f a := by
  classical
  rw [Finset.prod_eq_single a]
  · simp [singleExponent]
  · intro i _ hia
    simp [singleExponent, hia]
  · simp

def coordinateSecondMonomial (x : Fin k → ℂ) (a b : Fin k) : ℂ :=
  x a * conj (x b)

theorem coordinateSecondMonomial_eq_mixedComplexMultiMonomial
    (x : Fin k → ℂ) (a b : Fin k) :
    coordinateSecondMonomial x a b =
      mixedComplexMultiMonomial (singleExponent a) (singleExponent b) x := by
  classical
  unfold coordinateSecondMonomial mixedComplexMultiMonomial
    mixedComplexMonomial
  rw [Finset.prod_mul_distrib, prod_pow_singleExponent,
    prod_pow_singleExponent]

theorem integrable_coordinateSecondMonomial_circularGaussianVector
    (a b : Fin k) :
    Integrable (fun x ↦ coordinateSecondMonomial x a b)
      (circularGaussianVector k) := by
  rw [show (fun x ↦ coordinateSecondMonomial x a b) =
      mixedComplexMultiMonomial (singleExponent a) (singleExponent b) by
    funext x
    exact coordinateSecondMonomial_eq_mixedComplexMultiMonomial x a b]
  unfold circularGaussianVector mixedComplexMultiMonomial
  exact Integrable.fintype_prod fun i ↦
    integrable_mixedComplexMonomial_circularGaussian _ _
      (singleExponent_le_two a i) (singleExponent_le_two b i)

theorem integral_coordinateSecondMonomial_circularGaussianVector
    (a b : Fin k) :
    (∫ x, coordinateSecondMonomial x a b
        ∂(circularGaussianVector k)) = kroneckerDelta a b := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    coordinateSecondMonomial_eq_mixedComplexMultiMonomial x a b)]
  unfold circularGaussianVector
  rw [integral_mixedComplexMultiMonomial_iid]
  simp_rw [integral_mixedComplexMonomial_circularGaussian _ _
    (singleExponent_le_two a _) (singleExponent_le_two b _)]
  classical
  by_cases hab : a = b
  · subst b
    unfold kroneckerDelta
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    rw [if_pos rfl]
    by_cases hia : i = a <;> simp [singleExponent, hia]
  · unfold kroneckerDelta
    rw [if_neg hab]
    rw [Finset.prod_eq_zero (Finset.mem_univ a)]
    simp [singleExponent, hab, Ne.symm hab]

def columnSecondIntegrand
    (g h x : Fin k → ℂ) : ℂ :=
  complexColumnForm g x * conjugateColumnForm h x

def expandedColumnSecond (g h x : Fin k → ℂ) : ℂ :=
  ∑ b, ∑ a, (g a * h b) * coordinateSecondMonomial x a b

theorem columnSecondIntegrand_eq_expanded (g h x : Fin k → ℂ) :
    columnSecondIntegrand g h x = expandedColumnSecond g h x := by
  classical
  unfold columnSecondIntegrand expandedColumnSecond complexColumnForm
    conjugateColumnForm coordinateSecondMonomial
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem reverseSecondContraction_eq_bilinearDot (g h : Fin k → ℂ) :
    (∑ b, ∑ a, (g a * h b) * kroneckerDelta a b) =
      bilinearDot g h := by
  classical
  unfold bilinearDot kroneckerDelta
  simp

theorem integral_columnSecondIntegrand_circularGaussianVector
    (g h : Fin k → ℂ) :
    ∫ x, columnSecondIntegrand g h x ∂(circularGaussianVector k) =
      bilinearDot g h := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (columnSecondIntegrand_eq_expanded g h))]
  calc
    (∫ x, expandedColumnSecond g h x ∂circularGaussianVector k) =
        ∑ b, ∑ a, (g a * h b) *
          (∫ x, coordinateSecondMonomial x a b
            ∂circularGaussianVector k) := by
      unfold expandedColumnSecond
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro b _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro a _
          rw [integral_const_mul]
        · intro a _
          exact (integrable_coordinateSecondMonomial_circularGaussianVector a b).const_mul _
      · intro b _
        exact integrable_finsetSum _ fun a _ ↦
          (integrable_coordinateSecondMonomial_circularGaussianVector a b).const_mul _
    _ = ∑ b, ∑ a, (g a * h b) * kroneckerDelta a b := by
      simp_rw [integral_coordinateSecondMonomial_circularGaussianVector]
    _ = bilinearDot g h := reverseSecondContraction_eq_bilinearDot g h

def columnSecondProduct
    (g h : Fin k → ℂ)
    (X : Fin (2 * n) → (Fin k → ℂ)) : ℂ :=
  ∏ i, columnSecondIntegrand g h (X i)

theorem integral_columnSecondProduct_circularGaussianVector
    (g h : Fin k → ℂ) :
    ∫ X, columnSecondProduct (n := n) g h X
        ∂(Measure.pi fun _ : Fin (2 * n) ↦ circularGaussianVector k) =
      bilinearDot g h ^ (2 * n) := by
  unfold columnSecondProduct
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_columnSecondIntegrand_circularGaussianVector]
  simp

end

end LogdetLean.GramHafnian
