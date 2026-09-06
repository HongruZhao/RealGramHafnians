import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorTypeHafnian
/-!
# Order-preserving reindexing of finite hafnians

Deleted-column subtypes occur in several syntactically different orders in
the two-exposed-column argument.  Their canonical identifications preserve
the inherited linear order.  This module proves once and for all that the
finite-type hafnian is invariant under such an order isomorphism.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace TypePerfectMatching

@[simp] theorem congr_orderIso_apply
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃o β)
    (M : TypePerfectMatching α) (j : β) :
    congr e.toEquiv M j = e (M (e.symm j)) := by
  rfl

@[simp] theorem genericPairReps_congr_orderIso
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃o β)
    (M : TypePerfectMatching α) :
    genericPairReps (congr e.toEquiv M) =
      (genericPairReps M).map e.toEmbedding := by
  classical
  ext j
  simp only [genericPairReps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, congr_orderIso_apply]
  change j < e (M (e.symm j)) ↔
    ∃ a, a < M a ∧ e a = j
  constructor
  · intro hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    exact (e.lt_iff_lt).mp (by simpa using hj)
  · rintro ⟨a, ha, rfl⟩
    simpa using e.lt_iff_lt.mpr ha

end TypePerfectMatching

theorem typeMatchingMonomial_reindex_orderIso
    {α β R : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] [CommMonoid R]
    (e : α ≃o β) (A : Matrix β β R)
    (M : TypePerfectMatching α) :
    typeMatchingMonomial (fun i j ↦ A (e i) (e j)) M =
      typeMatchingMonomial A (TypePerfectMatching.congr e.toEquiv M) := by
  classical
  unfold typeMatchingMonomial
  rw [TypePerfectMatching.genericPairReps_congr_orderIso]
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _hi
  simp [TypePerfectMatching.congr]

/-- Hafnians are invariant under an order-preserving relabelling. -/
theorem typeHafnian_reindex_orderIso
    {α β R : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] [CommSemiring R]
    (e : α ≃o β) (A : Matrix β β R) :
    typeHafnian (fun i j ↦ A (e i) (e j)) = typeHafnian A := by
  classical
  unfold typeHafnian
  apply Fintype.sum_equiv (TypePerfectMatching.congr e.toEquiv)
  intro M
  exact typeMatchingMonomial_reindex_orderIso e A M

end

end LogdetLean.GramHafnian
