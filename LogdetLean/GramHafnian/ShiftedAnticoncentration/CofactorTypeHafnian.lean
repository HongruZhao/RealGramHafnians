import LogdetLean.GramHafnian.Hafnian
import LogdetLean.GramHafnian.WickRegrouping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
/-!
# A finite-type hafnian for odd cofactors

The public Gram-hafnian is indexed by `Fin (2 * n)`.  Deleting a vertex is
most naturally represented by a subtype, so this file supplies the same
finite matching sum on an arbitrary finite linearly ordered type.  On
`Fin (2 * n)` it agrees definitionally term-by-term with the existing
`hafnian` after transporting the matching type.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- The monomial of a matching on an arbitrary finite ordered vertex type. -/
def typeMatchingMonomial {α R : Type*} [Fintype α] [LinearOrder α]
    [CommMonoid R] (A : Matrix α α R) (M : TypePerfectMatching α) : R :=
  ∏ i ∈ TypePerfectMatching.genericPairReps M, A i (M i)

/-- Hafnian on an arbitrary finite linearly ordered type.  This convention
also gives the empty hafnian the value one. -/
def typeHafnian {α R : Type*} [Fintype α] [LinearOrder α]
    [CommSemiring R] (A : Matrix α α R) : R :=
  ∑ M : TypePerfectMatching α, typeMatchingMonomial A M

@[simp] theorem typeMatchingMonomial_finEquiv
    {n : ℕ} {R : Type*} [CommMonoid R]
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (M : PerfectMatching n) :
    typeMatchingMonomial A (TypePerfectMatching.finEquiv n M) =
      matchingMonomial A M := by
  rfl

/-- The finite-type definition is exactly the pre-existing literal hafnian
on its public `Fin (2*n)` domain. -/
theorem typeHafnian_fin_eq_hafnian
    {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) :
    typeHafnian A = hafnian A := by
  classical
  unfold typeHafnian hafnian
  apply Fintype.sum_equiv (TypePerfectMatching.finEquiv n).symm
  intro M
  simpa using
    (typeMatchingMonomial_finEquiv A
      ((TypePerfectMatching.finEquiv n).symm M))

/-- Every finite-type hafnian over `ℂ` is a finite polynomial in the matrix
entries, hence continuous. -/
theorem continuous_typeHafnian {α : Type*} [Fintype α] [LinearOrder α] :
    Continuous (typeHafnian : Matrix α α ℂ → ℂ) := by
  unfold typeHafnian typeMatchingMonomial
  fun_prop

/-- The empty hafnian is one on every coefficient semiring. -/
theorem typeHafnian_eq_one_of_isEmpty
    {α R : Type*} [Fintype α] [LinearOrder α] [IsEmpty α]
    [CommSemiring R] (A : Matrix α α R) : typeHafnian A = 1 := by
  classical
  have hmono : ∀ M : TypePerfectMatching α,
      typeMatchingMonomial A M = 1 := by
    intro M
    unfold typeMatchingMonomial
    have hreps : TypePerfectMatching.genericPairReps M = ∅ := by
      exact Finset.eq_empty_of_forall_notMem fun i _hi ↦ isEmptyElim i
    rw [hreps]
    simp
  unfold typeHafnian
  simp_rw [hmono]
  rw [Finset.sum_const, Finset.card_univ,
    TypePerfectMatching.card_eq_wickMultiplicity]
  simp

end

end LogdetLean.GramHafnian
