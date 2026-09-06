import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorTypeHafnian
/-!
# Cofactors and expansion at a maximal vertex

This file proves the exact finite matching identity behind expansion of a
hafnian along its last column.  No probability enters the argument.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace TypePerfectMatching

/-- Insert a selected mate and then forget the fiber proof.  This is the
inverse of splitting a matching according to the mate of `x`. -/
def joinAt {α : Type*} [DecidableEq α] (x : α) :
    (Σ y : {y : α // y ≠ x}, TypePerfectMatching (PairComplement x y.1)) ≃
      TypePerfectMatching α :=
  (Equiv.sigmaCongrRight fun y ↦ (distinguishedMateFiberEquiv x y).symm).trans
    (Equiv.sigmaFiberEquiv (distinguishedMate x))

@[simp] theorem joinAt_apply {α : Type*} [DecidableEq α] (x : α)
    (y : {y : α // y ≠ x}) (N : TypePerfectMatching (PairComplement x y.1)) :
    joinAt x ⟨y, N⟩ = insertPair x y.1 y.2.symm N := by
  rfl

/-- Pair representatives after inserting a pair whose second endpoint is
the maximal one. -/
theorem genericPairReps_insertPair_of_lt
    {α : Type*} [Fintype α] [LinearOrder α]
    (x y : α) (hyx : y < x)
    (N : TypePerfectMatching (PairComplement x y)) :
    genericPairReps (insertPair x y hyx.ne' N) =
      insert y ((genericPairReps N).image Subtype.val) := by
  classical
  ext z
  simp only [genericPairReps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_image]
  by_cases hzx : z = x
  · subst z
    constructor
    · intro hxlt
      rw [insertPair_apply_left] at hxlt
      exact ((not_lt_of_ge hyx.le) hxlt).elim
    · rintro (hxy | ⟨w, _hw, hw⟩)
      · exact (hyx.ne hxy.symm).elim
      · exact (w.2.1 hw).elim
  · by_cases hzy : z = y
    · subst z
      simp [insertPair_apply_right, hyx]
    · let w : PairComplement x y := ⟨z, hzx, hzy⟩
      rw [show insertPair x y hyx.ne' N z = (N w).1 by
        exact insertPair_apply_complement x y hyx.ne' N w]
      constructor
      · intro hzlt
        right
        refine ⟨w, ?_, rfl⟩
        exact hzlt
      · rintro (hzy' | ⟨u, hu, huz⟩)
        · exact (hzy hzy').elim
        · have huw : u = w := Subtype.ext huz
          subst u
          exact hu

/-- A matching monomial factors into the distinguished matrix entry and the
monomial of the erased matching. -/
theorem typeMatchingMonomial_insertPair_of_lt
    {α R : Type*} [Fintype α] [LinearOrder α] [CommMonoid R]
    (A : Matrix α α R) (x y : α) (hyx : y < x)
    (N : TypePerfectMatching (PairComplement x y)) :
    typeMatchingMonomial A (insertPair x y hyx.ne' N) =
      A y x * typeMatchingMonomial
        (fun i j : PairComplement x y ↦ A i.1 j.1) N := by
  classical
  unfold typeMatchingMonomial
  rw [genericPairReps_insertPair_of_lt x y hyx N]
  have hyimage : y ∉ (genericPairReps N).image Subtype.val := by
    intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨z, _hz, hzy⟩ := hy
    exact z.2.2 hzy
  rw [Finset.prod_insert hyimage]
  rw [insertPair_apply_right]
  congr 1
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro z hz
    rw [insertPair_apply_complement]
  · exact Set.injOn_of_injective Subtype.val_injective

end TypePerfectMatching

/-- The principal hafnian cofactor obtained after deleting `x` and `y`. -/
def hafnianPairCofactor {α R : Type*} [Fintype α] [LinearOrder α]
    [CommSemiring R] (A : Matrix α α R) (x : α) (y : {y : α // y ≠ x}) : R :=
  typeHafnian (fun i j : TypePerfectMatching.PairComplement x y.1 ↦
    A i.1 j.1)

/-- Exact expansion of a finite-type hafnian along a greatest vertex. -/
theorem typeHafnian_expand_greatest
    {α R : Type*} [Fintype α] [LinearOrder α] [CommSemiring R]
    (A : Matrix α α R) (x : α) (hx : ∀ y, y ≠ x → y < x) :
    typeHafnian A =
      ∑ y : {y : α // y ≠ x}, A y.1 x * hafnianPairCofactor A x y := by
  classical
  let e := TypePerfectMatching.joinAt x
  calc
    typeHafnian A = ∑ M : TypePerfectMatching α,
        typeMatchingMonomial A M := rfl
    _ = ∑ z : Σ y : {y : α // y ≠ x},
          TypePerfectMatching (TypePerfectMatching.PairComplement x y.1),
          typeMatchingMonomial A (e z) := by
      symm
      apply Fintype.sum_equiv e
      intro z
      rfl
    _ = ∑ z : Σ y : {y : α // y ≠ x},
          TypePerfectMatching (TypePerfectMatching.PairComplement x y.1),
          A z.1.1 x * typeMatchingMonomial
            (fun i j : TypePerfectMatching.PairComplement x z.1.1 ↦
              A i.1 j.1) z.2 := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [show e z = TypePerfectMatching.insertPair x z.1.1 z.1.2.symm z.2 by
        rcases z with ⟨y, N⟩
        exact TypePerfectMatching.joinAt_apply x y N]
      exact TypePerfectMatching.typeMatchingMonomial_insertPair_of_lt
        A x z.1.1 (hx z.1.1 z.1.2) z.2
    _ = ∑ y : {y : α // y ≠ x},
          A y.1 x * hafnianPairCofactor A x y := by
      unfold hafnianPairCofactor typeHafnian
      simp_rw [Finset.mul_sum]
      exact Fintype.sum_sigma'
        (fun (y : {y : α // y ≠ x})
          (N : TypePerfectMatching
            (TypePerfectMatching.PairComplement x y.1)) ↦
          (A y.1 x * typeMatchingMonomial
          (fun i j : TypePerfectMatching.PairComplement x y.1 ↦
            A i.1 j.1) N : R))

end

end LogdetLean.GramHafnian
