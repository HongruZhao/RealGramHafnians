import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseDefinitions
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorExpansion
/-!
# Exact two-exposed-column cofactor decomposition

This is the deterministic hafnian algebra used to identify the conditional
Fourier phase.  The two displayed columns occupy the final two indices, so
successive expansions always occur at a greatest vertex.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- `Y` as a vertex after deleting `X`. -/
def exposedYInDeleteX (m : ℕ) :
    {i : Fin (m + 2) // i ≠ exposedXIndex m} :=
  ⟨exposedYIndex m, (exposedXIndex_lt_exposedYIndex m).ne'⟩

/-- `X` as a vertex after deleting `Y`. -/
def exposedXInDeleteY (m : ℕ) :
    {i : Fin (m + 2) // i ≠ exposedYIndex m} :=
  ⟨exposedXIndex m, exposedXIndex_ne_exposedYIndex m⟩

/-- A background vertex after deleting `X`. -/
def remainingInDeleteX (m : ℕ) (a : Fin m) :
    {i : Fin (m + 2) // i ≠ exposedXIndex m} :=
  ⟨remainingIndex m a, ne_exposedXIndex_of_remaining m a⟩

/-- A background vertex after deleting `Y`. -/
def remainingInDeleteY (m : ℕ) (a : Fin m) :
    {i : Fin (m + 2) // i ≠ exposedYIndex m} :=
  ⟨remainingIndex m a, ne_exposedYIndex_of_remaining m a⟩

/-- Background vertices are precisely the vertices left after deleting
`X,Y`, with inherited order preserved. -/
def remainingOrderIsoDeleteXY (m : ℕ) :
    Fin m ≃o
      {u : {i : Fin (m + 2) // i ≠ exposedXIndex m} //
        u ≠ exposedYInDeleteX m} where
  toFun a :=
    ⟨remainingInDeleteX m a, by
      intro h
      have hv := congrArg (fun z ↦ z.1.1) h
      simp [remainingInDeleteX, exposedYInDeleteX,
        remainingIndex, exposedYIndex] at hv
      omega⟩
  invFun u :=
    ⟨u.1.1.1, by
      have hbound := u.1.1.2
      have hneX : u.1.1.1 ≠ m := by
        intro h
        apply u.1.2
        apply Fin.ext
        simpa [exposedXIndex] using h
      have hneY : u.1.1.1 ≠ m + 1 := by
        intro h
        apply u.2
        apply Subtype.ext
        apply Fin.ext
        simpa [exposedYInDeleteX, exposedYIndex] using h
      omega⟩
  left_inv a := by apply Fin.ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  map_rel_iff' := by intro a b; rfl

/-- After additionally choosing the mate `a`, the remaining vertices are
canonically the background indices other than `a`. -/
def remainingDeleteOneOrderIsoPairComplementX (m : ℕ) (a : Fin m) :
    {t : Fin m // t ≠ a} ≃o
      TypePerfectMatching.PairComplement
        (exposedYInDeleteX m) (remainingInDeleteX m a) where
  toFun t :=
    ⟨remainingInDeleteX m t.1, by
      constructor
      · intro h
        have hv := congrArg (fun z ↦ z.1.1) h
        simp [remainingInDeleteX, exposedYInDeleteX,
          remainingIndex, exposedYIndex] at hv
        omega
      · intro h
        apply t.2
        apply Fin.ext
        exact congrArg (fun z ↦ z.1.1) h⟩
  invFun u :=
    ⟨⟨u.1.1.1, by
        have hbound := u.1.1.2
        have hneX : u.1.1.1 ≠ m := by
          intro h
          apply u.1.2
          apply Fin.ext
          simpa [exposedXIndex] using h
        have hneY : u.1.1.1 ≠ m + 1 := by
          intro h
          apply u.2.1
          apply Subtype.ext
          apply Fin.ext
          simpa [exposedYInDeleteX, exposedYIndex] using h
        omega⟩, by
      intro h
      have hv : u.1.1.1 = a.1 := congrArg Fin.val h
      have hfin : u.1.1 = remainingIndex m a := by
        apply Fin.ext
        exact hv
      exact u.2.2 (Subtype.ext hfin)⟩
  left_inv t := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  map_rel_iff' := by intro s t; rfl

theorem pairCofactor_deleteX_Y_background_eq
    {m k : ℕ} (A : TwoExposedColumnFamily m k) (a : Fin m) :
    hafnianPairCofactor
        (columnTransposeGram
          (fun i : {i : Fin (m + 2) // i ≠ exposedXIndex m} ↦ A i.1))
        (exposedYInDeleteX m) (remainingOrderIsoDeleteXY m a) =
      remainingHafnianDeleteOne A a := by
  unfold hafnianPairCofactor remainingHafnianDeleteOne
  let e := remainingDeleteOneOrderIsoPairComplementX m a
  change
    typeHafnian (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
        (exposedYInDeleteX m) (remainingInDeleteX m a) ↦ A i.1.1)) =
    typeHafnian (columnTransposeGram
      (fun i : {i : Fin m // i ≠ a} ↦ A (remainingIndex m i.1)))
  rw [← typeHafnian_reindex_orderIso e
    (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
        (exposedYInDeleteX m) (remainingInDeleteX m a) ↦ A i.1.1))]
  rfl

theorem deleteX_greatest_Y (m : ℕ)
    (u : {i : Fin (m + 2) // i ≠ exposedXIndex m})
    (hu : u ≠ exposedYInDeleteX m) :
    u < exposedYInDeleteX m := by
  change u.1.1 < m + 1
  have hbound := u.1.2
  have hne : u.1.1 ≠ m + 1 := by
    intro h
    apply hu
    apply Subtype.ext
    apply Fin.ext
    exact h
  omega

/-- First endpoint identity: `C_X = Yᵀ q_R`. -/
theorem twoExposedCofactor_X_eq_transposeDot_Y_q
    {m k : ℕ} (A : TwoExposedColumnFamily m k) :
    twoExposedCofactorVector A (exposedXIndex m) =
      transposeDot (A (exposedYIndex m)) (cofactorQ A) := by
  unfold twoExposedCofactorVector finiteGramCofactorVector
  rw [typeHafnian_expand_greatest _ (exposedYInDeleteX m)
    (deleteX_greatest_Y m)]
  calc
    (∑ y : {y : {i : Fin (m + 2) // i ≠ exposedXIndex m} //
        y ≠ exposedYInDeleteX m},
        columnTransposeGram
            (fun i : {i : Fin (m + 2) // i ≠ exposedXIndex m} ↦ A i.1)
          y.1 (exposedYInDeleteX m) *
          hafnianPairCofactor
            (columnTransposeGram
              (fun i : {i : Fin (m + 2) // i ≠ exposedXIndex m} ↦ A i.1))
            (exposedYInDeleteX m) y) =
        ∑ a : Fin m,
          transposeDot (A (remainingIndex m a)) (A (exposedYIndex m)) *
            remainingHafnianDeleteOne A a := by
      apply Fintype.sum_equiv (remainingOrderIsoDeleteXY m).symm
      intro y
      obtain ⟨a, rfl⟩ := (remainingOrderIsoDeleteXY m).surjective y
      change
        columnTransposeGram
            (fun i : {i : Fin (m + 2) // i ≠ exposedXIndex m} ↦ A i.1)
          (remainingInDeleteX m a) (exposedYInDeleteX m) *
          hafnianPairCofactor
            (columnTransposeGram
              (fun i : {i : Fin (m + 2) // i ≠ exposedXIndex m} ↦ A i.1))
            (exposedYInDeleteX m) (remainingOrderIsoDeleteXY m a) =
          transposeDot (A (remainingIndex m a)) (A (exposedYIndex m)) *
            remainingHafnianDeleteOne A a
      rw [pairCofactor_deleteX_Y_background_eq]
      unfold columnTransposeGram transposeDot
      rfl
    _ = transposeDot (A (exposedYIndex m)) (cofactorQ A) := by
      unfold transposeDot cofactorQ
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _hp
      apply Finset.sum_congr rfl
      intro a _ha
      ring

/-- Background vertices after deleting `Y,X`, in inherited order. -/
def remainingOrderIsoDeleteYX (m : ℕ) :
    Fin m ≃o
      {u : {i : Fin (m + 2) // i ≠ exposedYIndex m} //
        u ≠ exposedXInDeleteY m} where
  toFun a :=
    ⟨remainingInDeleteY m a, by
      intro h
      have hv := congrArg (fun z ↦ z.1.1) h
      simp [remainingInDeleteY, exposedXInDeleteY,
        remainingIndex, exposedXIndex] at hv
      omega⟩
  invFun u :=
    ⟨u.1.1.1, by
      have hbound := u.1.1.2
      have hneY : u.1.1.1 ≠ m + 1 := by
        intro h
        apply u.1.2
        apply Fin.ext
        simpa [exposedYIndex] using h
      have hneX : u.1.1.1 ≠ m := by
        intro h
        apply u.2
        apply Subtype.ext
        apply Fin.ext
        simpa [exposedXInDeleteY, exposedXIndex] using h
      omega⟩
  left_inv a := by apply Fin.ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  map_rel_iff' := by intro a b; rfl

def remainingDeleteOneOrderIsoPairComplementY (m : ℕ) (a : Fin m) :
    {t : Fin m // t ≠ a} ≃o
      TypePerfectMatching.PairComplement
        (exposedXInDeleteY m) (remainingInDeleteY m a) where
  toFun t :=
    ⟨remainingInDeleteY m t.1, by
      constructor
      · intro h
        have hv := congrArg (fun z ↦ z.1.1) h
        simp [remainingInDeleteY, exposedXInDeleteY,
          remainingIndex, exposedXIndex] at hv
        omega
      · intro h
        apply t.2
        apply Fin.ext
        exact congrArg (fun z ↦ z.1.1) h⟩
  invFun u :=
    ⟨⟨u.1.1.1, by
        have hbound := u.1.1.2
        have hneY : u.1.1.1 ≠ m + 1 := by
          intro h
          apply u.1.2
          apply Fin.ext
          simpa [exposedYIndex] using h
        have hneX : u.1.1.1 ≠ m := by
          intro h
          apply u.2.1
          apply Subtype.ext
          apply Fin.ext
          simpa [exposedXInDeleteY, exposedXIndex] using h
        omega⟩, by
      intro h
      have hv : u.1.1.1 = a.1 := congrArg Fin.val h
      have hfin : u.1.1 = remainingIndex m a := by
        apply Fin.ext
        exact hv
      exact u.2.2 (Subtype.ext hfin)⟩
  left_inv t := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  map_rel_iff' := by intro s t; rfl

theorem pairCofactor_deleteY_X_background_eq
    {m k : ℕ} (A : TwoExposedColumnFamily m k) (a : Fin m) :
    hafnianPairCofactor
        (columnTransposeGram
          (fun i : {i : Fin (m + 2) // i ≠ exposedYIndex m} ↦ A i.1))
        (exposedXInDeleteY m) (remainingOrderIsoDeleteYX m a) =
      remainingHafnianDeleteOne A a := by
  unfold hafnianPairCofactor remainingHafnianDeleteOne
  let e := remainingDeleteOneOrderIsoPairComplementY m a
  change
    typeHafnian (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
        (exposedXInDeleteY m) (remainingInDeleteY m a) ↦ A i.1.1)) =
    typeHafnian (columnTransposeGram
      (fun i : {i : Fin m // i ≠ a} ↦ A (remainingIndex m i.1)))
  rw [← typeHafnian_reindex_orderIso e
    (columnTransposeGram
      (fun i : TypePerfectMatching.PairComplement
        (exposedXInDeleteY m) (remainingInDeleteY m a) ↦ A i.1.1))]
  rfl

theorem deleteY_greatest_X (m : ℕ)
    (u : {i : Fin (m + 2) // i ≠ exposedYIndex m})
    (hu : u ≠ exposedXInDeleteY m) :
    u < exposedXInDeleteY m := by
  change u.1.1 < m
  have hbound := u.1.2
  have hneY : u.1.1 ≠ m + 1 := by
    intro h
    apply u.2
    apply Fin.ext
    exact h
  have hneX : u.1.1 ≠ m := by
    intro h
    apply hu
    apply Subtype.ext
    apply Fin.ext
    exact h
  omega

/-- Second endpoint identity: `C_Y = Xᵀ q_R`, with exactly the same `q_R`. -/
theorem twoExposedCofactor_Y_eq_transposeDot_X_q
    {m k : ℕ} (A : TwoExposedColumnFamily m k) :
    twoExposedCofactorVector A (exposedYIndex m) =
      transposeDot (A (exposedXIndex m)) (cofactorQ A) := by
  unfold twoExposedCofactorVector finiteGramCofactorVector
  rw [typeHafnian_expand_greatest _ (exposedXInDeleteY m)
    (deleteY_greatest_X m)]
  calc
    (∑ y : {y : {i : Fin (m + 2) // i ≠ exposedYIndex m} //
        y ≠ exposedXInDeleteY m},
        columnTransposeGram
            (fun i : {i : Fin (m + 2) // i ≠ exposedYIndex m} ↦ A i.1)
          y.1 (exposedXInDeleteY m) *
          hafnianPairCofactor
            (columnTransposeGram
              (fun i : {i : Fin (m + 2) // i ≠ exposedYIndex m} ↦ A i.1))
            (exposedXInDeleteY m) y) =
        ∑ a : Fin m,
          transposeDot (A (remainingIndex m a)) (A (exposedXIndex m)) *
            remainingHafnianDeleteOne A a := by
      apply Fintype.sum_equiv (remainingOrderIsoDeleteYX m).symm
      intro y
      obtain ⟨a, rfl⟩ := (remainingOrderIsoDeleteYX m).surjective y
      change
        columnTransposeGram
            (fun i : {i : Fin (m + 2) // i ≠ exposedYIndex m} ↦ A i.1)
          (remainingInDeleteY m a) (exposedXInDeleteY m) *
          hafnianPairCofactor
            (columnTransposeGram
              (fun i : {i : Fin (m + 2) // i ≠ exposedYIndex m} ↦ A i.1))
            (exposedXInDeleteY m) (remainingOrderIsoDeleteYX m a) =
          transposeDot (A (remainingIndex m a)) (A (exposedXIndex m)) *
            remainingHafnianDeleteOne A a
      rw [pairCofactor_deleteY_X_background_eq]
      unfold columnTransposeGram transposeDot
      rfl
    _ = transposeDot (A (exposedXIndex m)) (cofactorQ A) := by
      unfold transposeDot cofactorQ
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _hp
      apply Finset.sum_congr rfl
      intro a _ha
      ring

end

end LogdetLean.GramHafnian
