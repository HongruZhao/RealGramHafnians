import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseDecomposition
/-!
# Background-coordinate cofactor decomposition

For a background coordinate `j`, this file carries out the two successive
greatest-vertex expansions that separate the displayed columns `X,Y`.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

abbrev DeleteRemainingIndex (m : ℕ) (j : Fin m) :=
  {i : Fin (m + 2) // i ≠ remainingIndex m j}

def exposedYInDeleteRemaining (m : ℕ) (j : Fin m) :
    DeleteRemainingIndex m j :=
  ⟨exposedYIndex m, by
    exact (ne_exposedYIndex_of_remaining m j).symm⟩

def exposedXInDeleteRemaining (m : ℕ) (j : Fin m) :
    DeleteRemainingIndex m j :=
  ⟨exposedXIndex m, by
    exact (ne_exposedXIndex_of_remaining m j).symm⟩

def otherRemainingInDeleteRemaining (m : ℕ) (j : Fin m)
    (a : {a : Fin m // a ≠ j}) : DeleteRemainingIndex m j :=
  ⟨remainingIndex m a.1, by
    intro h
    have hv : a.1.1 = j.1 :=
      congrArg (fun z : Fin (m + 2) ↦ z.1) h
    exact a.2 (Fin.ext hv)⟩

def exposedXAfterDeleteRemainingY (m : ℕ) (j : Fin m) :
    {u : DeleteRemainingIndex m j //
      u ≠ exposedYInDeleteRemaining m j} :=
  ⟨exposedXInDeleteRemaining m j, by
    intro h
    have hv := congrArg (fun z ↦ z.1.1) h
    simp [exposedXInDeleteRemaining, exposedYInDeleteRemaining,
      exposedXIndex, exposedYIndex] at hv⟩

def otherRemainingAfterDeleteRemainingY (m : ℕ) (j : Fin m)
    (a : {a : Fin m // a ≠ j}) :
    {u : DeleteRemainingIndex m j //
      u ≠ exposedYInDeleteRemaining m j} :=
  ⟨otherRemainingInDeleteRemaining m j a, by
    intro h
    have hv := congrArg (fun z ↦ z.1.1) h
    simp [otherRemainingInDeleteRemaining, exposedYInDeleteRemaining,
      remainingIndex, exposedYIndex] at hv
    omega⟩

def deleteRemainingWithoutYMap (m : ℕ) (j : Fin m) :
    Option {a : Fin m // a ≠ j} →
      {u : DeleteRemainingIndex m j //
        u ≠ exposedYInDeleteRemaining m j}
  | none => exposedXAfterDeleteRemainingY m j
  | some a => otherRemainingAfterDeleteRemainingY m j a

theorem deleteRemainingWithoutYMap_bijective (m : ℕ) (j : Fin m) :
    Function.Bijective (deleteRemainingWithoutYMap m j) := by
  constructor
  · intro s t h
    cases s with
    | none =>
        cases t with
        | none => rfl
        | some b =>
            exfalso
            have hv := congrArg (fun z ↦ z.1.1.1) h
            simp [deleteRemainingWithoutYMap, exposedXAfterDeleteRemainingY,
              exposedXInDeleteRemaining, otherRemainingAfterDeleteRemainingY,
              otherRemainingInDeleteRemaining, exposedXIndex,
              remainingIndex] at hv
            exact (Nat.not_lt_of_ge (Nat.le_of_eq hv)) b.1.2
    | some a =>
        cases t with
        | none =>
            exfalso
            have hv := congrArg (fun z ↦ z.1.1.1) h
            simp [deleteRemainingWithoutYMap, exposedXAfterDeleteRemainingY,
              exposedXInDeleteRemaining, otherRemainingAfterDeleteRemainingY,
              otherRemainingInDeleteRemaining, exposedXIndex,
              remainingIndex] at hv
            exact (Nat.not_lt_of_ge (Nat.le_of_eq hv.symm)) a.1.2
        | some b =>
            have hab : a = b := by
              apply Subtype.ext
              apply Fin.ext
              exact congrArg (fun z ↦ z.1.1.1) h
            subst b
            rfl
  · intro u
    by_cases hx : u.1.1.1 = m
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Fin.ext
      exact hx.symm
    · have hbound := u.1.1.2
      have hy : u.1.1.1 ≠ m + 1 := by
        intro h
        apply u.2
        apply Subtype.ext
        apply Fin.ext
        exact h
      have hlt : u.1.1.1 < m := by omega
      let a : Fin m := ⟨u.1.1.1, hlt⟩
      have haj : a ≠ j := by
        intro h
        have hv : a.1 = j.1 := congrArg Fin.val h
        have hfin : u.1.1 = remainingIndex m j := by
          apply Fin.ext
          exact hv
        exact u.1.2 hfin
      refine ⟨some ⟨a, haj⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Fin.ext
      rfl

def deleteRemainingWithoutYEquiv (m : ℕ) (j : Fin m) :
    Option {a : Fin m // a ≠ j} ≃
      {u : DeleteRemainingIndex m j //
        u ≠ exposedYInDeleteRemaining m j} :=
  Equiv.ofBijective (deleteRemainingWithoutYMap m j)
    (deleteRemainingWithoutYMap_bijective m j)

theorem deleteRemaining_greatest_Y (m : ℕ) (j : Fin m)
    (u : DeleteRemainingIndex m j)
    (hu : u ≠ exposedYInDeleteRemaining m j) :
    u < exposedYInDeleteRemaining m j := by
  change u.1.1 < m + 1
  have hbound := u.1.2
  have hne : u.1.1 ≠ m + 1 := by
    intro h
    apply hu
    apply Subtype.ext
    apply Fin.ext
    exact h
  omega

/-- Deleting the displayed pair `Y,X` leaves precisely the background
indices other than `j`. -/
def remainingDeleteJOrderIsoPairComplementYX (m : ℕ) (j : Fin m) :
    {t : Fin m // t ≠ j} ≃o
      TypePerfectMatching.PairComplement
        (exposedYInDeleteRemaining m j) (exposedXInDeleteRemaining m j) where
  toFun t :=
    ⟨otherRemainingInDeleteRemaining m j t, by
      constructor
      · intro h
        have hv := congrArg (fun z ↦ z.1.1) h
        simp [otherRemainingInDeleteRemaining, exposedYInDeleteRemaining,
          remainingIndex, exposedYIndex] at hv
        omega
      · intro h
        have hv := congrArg (fun z ↦ z.1.1) h
        simp [otherRemainingInDeleteRemaining, exposedXInDeleteRemaining,
          remainingIndex, exposedXIndex] at hv
        omega⟩
  invFun u :=
    ⟨⟨u.1.1.1, by
        have hbound := u.1.1.2
        have hy : u.1.1.1 ≠ m + 1 := by
          intro h
          apply u.2.1
          apply Subtype.ext
          apply Fin.ext
          exact h
        have hx : u.1.1.1 ≠ m := by
          intro h
          apply u.2.2
          apply Subtype.ext
          apply Fin.ext
          exact h
        omega⟩, by
      intro h
      have hv : u.1.1.1 = j.1 := congrArg Fin.val h
      have hfin : u.1.1 = remainingIndex m j := by
        apply Fin.ext
        exact hv
      exact u.1.2 hfin⟩
  left_inv t := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  map_rel_iff' := by intro a b; rfl

theorem pairCofactor_deleteRemaining_Y_X_eq_deleteOne
    {m k : ℕ} (A : TwoExposedColumnFamily m k) (j : Fin m) :
    hafnianPairCofactor
        (columnTransposeGram
          (fun i : DeleteRemainingIndex m j ↦ A i.1))
        (exposedYInDeleteRemaining m j)
        (exposedXAfterDeleteRemainingY m j) =
      remainingHafnianDeleteOne A j := by
  unfold hafnianPairCofactor remainingHafnianDeleteOne
  let e := remainingDeleteJOrderIsoPairComplementYX m j
  change
    typeHafnian (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
        (exposedYInDeleteRemaining m j) (exposedXInDeleteRemaining m j) ↦
          A i.1.1)) =
    typeHafnian (columnTransposeGram
      (fun i : {i : Fin m // i ≠ j} ↦ A (remainingIndex m i.1)))
  rw [← typeHafnian_reindex_orderIso e
    (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
        (exposedYInDeleteRemaining m j) (exposedXInDeleteRemaining m j) ↦
          A i.1.1))]
  rfl

/-- `X` inside the outer cofactor obtained after pairing `Y` with `b`. -/
def exposedXInPairComplementYB (m : ℕ) (j : Fin m)
    (b : {b : Fin m // b ≠ j}) :
    TypePerfectMatching.PairComplement
      (exposedYInDeleteRemaining m j)
      (otherRemainingInDeleteRemaining m j b) :=
  ⟨exposedXInDeleteRemaining m j, by
    constructor
    · intro h
      have hv := congrArg (fun z ↦ z.1.1) h
      simp [exposedXInDeleteRemaining, exposedYInDeleteRemaining,
        exposedXIndex, exposedYIndex] at hv
    · intro h
      have hv := congrArg (fun z ↦ z.1.1) h
      simp [exposedXInDeleteRemaining, otherRemainingInDeleteRemaining,
        exposedXIndex, remainingIndex] at hv
      omega⟩

def otherRemainingInPairComplementYB (m : ℕ) (j : Fin m)
    (b : {b : Fin m // b ≠ j})
    (a : {a : Fin m // a ≠ j ∧ a ≠ b.1}) :
    TypePerfectMatching.PairComplement
      (exposedYInDeleteRemaining m j)
      (otherRemainingInDeleteRemaining m j b) :=
  ⟨otherRemainingInDeleteRemaining m j ⟨a.1, a.2.1⟩, by
    constructor
    · intro h
      have hv := congrArg (fun z ↦ z.1.1) h
      simp [otherRemainingInDeleteRemaining, exposedYInDeleteRemaining,
        remainingIndex, exposedYIndex] at hv
      omega
    · intro h
      apply a.2.2
      apply Fin.ext
      exact congrArg (fun z ↦ z.1.1) h⟩

def remainingExceptJBOrderIsoAfterYX (m : ℕ) (j : Fin m)
    (b : {b : Fin m // b ≠ j}) :
    {a : Fin m // a ≠ j ∧ a ≠ b.1} ≃o
      {u : TypePerfectMatching.PairComplement
          (exposedYInDeleteRemaining m j)
          (otherRemainingInDeleteRemaining m j b) //
        u ≠ exposedXInPairComplementYB m j b} where
  toFun a :=
    ⟨otherRemainingInPairComplementYB m j b a, by
      intro h
      have hv := congrArg (fun z ↦ z.1.1.1) h
      simp [otherRemainingInPairComplementYB,
        otherRemainingInDeleteRemaining, exposedXInPairComplementYB,
        exposedXInDeleteRemaining, remainingIndex, exposedXIndex] at hv
      omega⟩
  invFun u :=
    ⟨⟨u.1.1.1.1, by
        have hbound := u.1.1.1.2
        have hy : u.1.1.1.1 ≠ m + 1 := by
          intro h
          apply u.1.2.1
          apply Subtype.ext
          apply Fin.ext
          exact h
        have hx : u.1.1.1.1 ≠ m := by
          intro h
          apply u.2
          apply Subtype.ext
          apply Subtype.ext
          apply Fin.ext
          exact h
        omega⟩, by
      constructor
      · intro h
        have hv : u.1.1.1.1 = j.1 := congrArg Fin.val h
        have hfin : u.1.1.1 = remainingIndex m j := by
          apply Fin.ext
          exact hv
        exact u.1.1.2 hfin
      · intro h
        apply u.1.2.2
        apply Subtype.ext
        apply Fin.ext
        exact congrArg (fun z : Fin m ↦ z.1) h⟩
  left_inv a := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  map_rel_iff' := by intro a c; rfl

theorem pairComplementYB_greatest_X (m : ℕ) (j : Fin m)
    (b : {b : Fin m // b ≠ j})
    (u : TypePerfectMatching.PairComplement
      (exposedYInDeleteRemaining m j)
      (otherRemainingInDeleteRemaining m j b))
    (hu : u ≠ exposedXInPairComplementYB m j b) :
    u < exposedXInPairComplementYB m j b := by
  change u.1.1.1 < m
  have hbound := u.1.1.2
  have hy : u.1.1.1 ≠ m + 1 := by
    intro h
    apply u.2.1
    apply Subtype.ext
    apply Fin.ext
    exact h
  have hx : u.1.1.1 ≠ m := by
    intro h
    apply hu
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    exact h
  omega

/-- A background vertex after the successive choices `Y--b` and `X--a`. -/
def otherRemainingAfterYBXA (m : ℕ) (j : Fin m)
    (b : {b : Fin m // b ≠ j})
    (a : {a : Fin m // a ≠ j ∧ a ≠ b.1})
    (t : {t : Fin m // t ≠ j ∧ t ≠ a.1 ∧ t ≠ b.1}) :
    TypePerfectMatching.PairComplement
      (exposedXInPairComplementYB m j b)
      (otherRemainingInPairComplementYB m j b a) :=
  ⟨otherRemainingInPairComplementYB m j b
      ⟨t.1, t.2.1, t.2.2.2⟩, by
    constructor
    · intro h
      have hv := congrArg (fun z ↦ z.1.1.1) h
      simp [otherRemainingInPairComplementYB,
        otherRemainingInDeleteRemaining, exposedXInPairComplementYB,
        exposedXInDeleteRemaining, remainingIndex, exposedXIndex] at hv
      omega
    · intro h
      apply t.2.2.1
      apply Fin.ext
      exact congrArg (fun z ↦ z.1.1.1) h⟩

/-- Once the ordered mates `Y--b` and `X--a` have been fixed, the nested
pair complement is exactly the background set with `j,a,b` removed. -/
def remainingDeleteThreeOrderIsoAfterYBXA (m : ℕ) (j : Fin m)
    (b : {b : Fin m // b ≠ j})
    (a : {a : Fin m // a ≠ j ∧ a ≠ b.1}) :
    {t : Fin m // t ≠ j ∧ t ≠ a.1 ∧ t ≠ b.1} ≃o
      TypePerfectMatching.PairComplement
        (exposedXInPairComplementYB m j b)
        (otherRemainingInPairComplementYB m j b a) where
  toFun := otherRemainingAfterYBXA m j b a
  invFun u :=
    ⟨⟨u.1.1.1.1, by
        have hbound := u.1.1.1.2
        have hy : u.1.1.1.1 ≠ m + 1 := by
          intro h
          apply u.1.2.1
          apply Subtype.ext
          apply Fin.ext
          exact h
        have hx : u.1.1.1.1 ≠ m := by
          intro h
          apply u.2.1
          apply Subtype.ext
          apply Subtype.ext
          apply Fin.ext
          exact h
        omega⟩, by
      constructor
      · intro h
        have hv : u.1.1.1.1 = j.1 :=
          congrArg (fun z : Fin m ↦ z.1) h
        have hfin : u.1.1.1 = remainingIndex m j := by
          apply Fin.ext
          exact hv
        exact u.1.1.2 hfin
      · constructor
        · intro h
          apply u.2.2
          apply Subtype.ext
          apply Subtype.ext
          apply Fin.ext
          exact congrArg (fun z : Fin m ↦ z.1) h
        · intro h
          apply u.1.2.2
          apply Subtype.ext
          apply Fin.ext
          exact congrArg (fun z : Fin m ↦ z.1) h⟩
  left_inv t := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  map_rel_iff' := by intro s t; rfl

/-- The second-stage pair cofactor is precisely the triple-deletion
background hafnian, with the ordered mate convention used by `cofactorM`. -/
theorem pairCofactor_after_YB_XA_eq_deleteThree
    {m k : ℕ} (A : TwoExposedColumnFamily m k) (j : Fin m)
    (b : {b : Fin m // b ≠ j})
    (a : {a : Fin m // a ≠ j ∧ a ≠ b.1}) :
    hafnianPairCofactor
        (columnTransposeGram
          (fun i : TypePerfectMatching.PairComplement
              (exposedYInDeleteRemaining m j)
              (otherRemainingInDeleteRemaining m j b) ↦ A i.1.1))
        (exposedXInPairComplementYB m j b)
        (remainingExceptJBOrderIsoAfterYX m j b a) =
      remainingHafnianDeleteThree A j a.1 b.1 := by
  unfold hafnianPairCofactor remainingHafnianDeleteThree
  let e := remainingDeleteThreeOrderIsoAfterYBXA m j b a
  change
    typeHafnian (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
          (exposedXInPairComplementYB m j b)
          (otherRemainingInPairComplementYB m j b a) ↦ A i.1.1.1)) =
    typeHafnian (columnTransposeGram
      (fun i : {i : Fin m // i ≠ j ∧ i ≠ a.1 ∧ i ≠ b.1} ↦
        A (remainingIndex m i.1)))
  rw [← typeHafnian_reindex_orderIso e
    (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
          (exposedXInPairComplementYB m j b)
          (otherRemainingInPairComplementYB m j b a) ↦ A i.1.1.1))]
  rfl

/-- Expanding the cofactor left after the ordered choice `Y--b` at its
greatest remaining displayed vertex `X` gives the ordered `a`-sum. -/
theorem pairCofactor_deleteRemaining_Y_background_eq_sum_X
    {m k : ℕ} (A : TwoExposedColumnFamily m k) (j : Fin m)
    (b : {b : Fin m // b ≠ j}) :
    hafnianPairCofactor
        (columnTransposeGram
          (fun i : DeleteRemainingIndex m j ↦ A i.1))
        (exposedYInDeleteRemaining m j)
        (otherRemainingAfterDeleteRemainingY m j b) =
      ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
        transposeDot (A (remainingIndex m a.1)) (A (exposedXIndex m)) *
          remainingHafnianDeleteThree A j a.1 b.1 := by
  unfold hafnianPairCofactor
  change
    typeHafnian (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
          (exposedYInDeleteRemaining m j)
          (otherRemainingInDeleteRemaining m j b) ↦ A i.1.1)) = _
  rw [typeHafnian_expand_greatest _
    (exposedXInPairComplementYB m j b)
    (pairComplementYB_greatest_X m j b)]
  apply Fintype.sum_equiv (remainingExceptJBOrderIsoAfterYX m j b).symm
  intro y
  obtain ⟨a, rfl⟩ :=
    (remainingExceptJBOrderIsoAfterYX m j b).surjective y
  change
    columnTransposeGram
        (fun i : TypePerfectMatching.PairComplement
            (exposedYInDeleteRemaining m j)
            (otherRemainingInDeleteRemaining m j b) ↦ A i.1.1)
      (otherRemainingInPairComplementYB m j b a)
      (exposedXInPairComplementYB m j b) *
      hafnianPairCofactor
        (columnTransposeGram
          (fun i : TypePerfectMatching.PairComplement
              (exposedYInDeleteRemaining m j)
              (otherRemainingInDeleteRemaining m j b) ↦ A i.1.1))
        (exposedXInPairComplementYB m j b)
        (remainingExceptJBOrderIsoAfterYX m j b a) =
      transposeDot (A (remainingIndex m a.1)) (A (exposedXIndex m)) *
        remainingHafnianDeleteThree A j a.1 b.1
  rw [pairCofactor_after_YB_XA_eq_deleteThree]
  unfold columnTransposeGram transposeDot
  rfl

end

end LogdetLean.GramHafnian
