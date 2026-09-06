import LogdetLean.GramHafnian.ComplexProductMoments
/-!
# One-column circular Wick reduction

This module proves the exact bridge used in the fourth-moment argument.  Its
input is only the literal fourth coordinate tensor and integrability of its
entries.  For an actual iid circular Gaussian law these are finite scalar
Gaussian computations; all expansion, integration, and tensor contraction
after that endpoint are proved here.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian

variable {k : ℕ}

/-- Complex bilinear form between a coefficient vector and one column. -/
def complexColumnForm (g x : Fin k → ℂ) : ℂ :=
  ∑ i, g i * x i

/-- Complex bilinear form against the conjugated column. -/
def conjugateColumnForm (h x : Fin k → ℂ) : ℂ :=
  ∑ i, h i * conj (x i)

/-- One coordinate monomial in the circular fourth tensor. -/
def coordinateFourthMonomial (x : Fin k → ℂ) (a b c d : Fin k) : ℂ :=
  x a * x b * conj (x c) * conj (x d)

/-- The four-linear one-column integrand. -/
def columnFourthIntegrand (g₁ g₂ h₁ h₂ x : Fin k → ℂ) : ℂ :=
  complexColumnForm g₁ x * complexColumnForm g₂ x *
    conjugateColumnForm h₁ x * conjugateColumnForm h₂ x

/-- Expanded form, ordered as produced by distributivity from the
left-associated four-factor product. -/
def expandedColumnFourth (g₁ g₂ h₁ h₂ x : Fin k → ℂ) : ℂ :=
  ∑ d, ∑ c, ∑ b, ∑ a,
    (g₁ a * g₂ b * h₁ c * h₂ d) * coordinateFourthMonomial x a b c d

theorem columnFourthIntegrand_eq_expanded
    (g₁ g₂ h₁ h₂ x : Fin k → ℂ) :
    columnFourthIntegrand g₁ g₂ h₁ h₂ x =
      expandedColumnFourth g₁ g₂ h₁ h₂ x := by
  classical
  simp only [columnFourthIntegrand, expandedColumnFourth, complexColumnForm,
    conjugateColumnForm, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  unfold coordinateFourthMonomial
  ring

/-- Integrating the finite expansion commutes with all four sums once the
coordinate fourth monomials are integrable. -/
theorem integral_expandedColumnFourth
    [MeasurableSpace (Fin k → ℂ)] (mu : Measure (Fin k → ℂ))
    (g₁ g₂ h₁ h₂ : Fin k → ℂ)
    (hInt : ∀ a b c d,
      Integrable (fun x ↦ coordinateFourthMonomial x a b c d) mu) :
    (∫ x, expandedColumnFourth g₁ g₂ h₁ h₂ x ∂mu) =
      ∑ d, ∑ c, ∑ b, ∑ a,
        (g₁ a * g₂ b * h₁ c * h₂ d) *
          (∫ x, coordinateFourthMonomial x a b c d ∂mu) := by
  classical
  unfold expandedColumnFourth
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro d _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro c _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro b _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro a _
          rw [integral_const_mul]
        · intro a _
          exact (hInt a b c d).const_mul _
      · intro b _
        exact integrable_finsetSum _
          (fun a _ ↦ (hInt a b c d).const_mul _)
    · intro c _
      exact integrable_finsetSum _ (fun b _ ↦
        integrable_finsetSum _ (fun a _ ↦ (hInt a b c d).const_mul _))
  · intro d _
    exact integrable_finsetSum _ (fun c _ ↦
      integrable_finsetSum _ (fun b _ ↦
        integrable_finsetSum _ (fun a _ ↦ (hInt a b c d).const_mul _)))

/-- The reverse-ordered tensor sum produced by the integral expansion. -/
def reverseFourthTensorContraction (g₁ g₂ h₁ h₂ : Fin k → ℂ) : ℂ :=
  ∑ d, ∑ c, ∑ b, ∑ a,
    (g₁ a * g₂ b * h₁ c * h₂ d) * circularFourthKernel a b c d

theorem reverseFourthTensorContraction_eq_rankTwoBilinear
    (g₁ g₂ h₁ h₂ : Fin k → ℂ) :
    reverseFourthTensorContraction g₁ g₂ h₁ h₂ =
      rankTwoBilinear g₁ g₂ h₁ h₂ := by
  classical
  unfold reverseFourthTensorContraction circularFourthKernel kroneckerDelta
    rankTwoBilinear bilinearDot
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply congrArg₂ (.+.)
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- **One-column Wick bridge.** If a complex vector has the standard
circular fourth tensor, then the expectation of the four linear forms is
the symmetric rank-two bilinear expression. -/
theorem integral_columnFourthIntegrand_eq_rankTwoBilinear
    [MeasurableSpace (Fin k → ℂ)] (mu : Measure (Fin k → ℂ))
    (g₁ g₂ h₁ h₂ : Fin k → ℂ)
    (hInt : ∀ a b c d,
      Integrable (fun x ↦ coordinateFourthMonomial x a b c d) mu)
    (hMoment : ∀ a b c d,
      ∫ x, coordinateFourthMonomial x a b c d ∂mu =
        circularFourthKernel a b c d) :
    ∫ x, columnFourthIntegrand g₁ g₂ h₁ h₂ x ∂mu =
      rankTwoBilinear g₁ g₂ h₁ h₂ := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (columnFourthIntegrand_eq_expanded g₁ g₂ h₁ h₂))]
  rw [integral_expandedColumnFourth mu g₁ g₂ h₁ h₂ hInt]
  simp_rw [hMoment]
  exact reverseFourthTensorContraction_eq_rankTwoBilinear g₁ g₂ h₁ h₂

end LogdetLean.GramHafnian
