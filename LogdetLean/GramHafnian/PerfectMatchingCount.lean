import LogdetLean.GramHafnian.PerfectMatching
/-!
# Counting perfect matchings

This module develops a transportable version of a perfect matching and uses
it to count the concrete matchings on `Fin (2 * n)`.
-/

open scoped Nat

namespace LogdetLean.GramHafnian

/-- A perfect matching on an arbitrary type. -/
structure TypePerfectMatching (α : Type*) where
  mate : Equiv.Perm α
  mate_ne : ∀ i, mate i ≠ i
  mate_mate : ∀ i, mate (mate i) = i

namespace TypePerfectMatching

instance {α : Type*} : CoeFun (TypePerfectMatching α) (fun _ ↦ α → α) :=
  ⟨fun M ↦ M.mate⟩

@[ext] theorem ext {α : Type*} {M N : TypePerfectMatching α}
    (h : ∀ i, M i = N i) : M = N := by
  cases M with
  | mk M hneM hinvM =>
    cases N with
    | mk N hneN hinvN =>
      have hMN : M = N := Equiv.ext h
      cases hMN
      rfl

noncomputable instance {α : Type*} : DecidableEq (TypePerfectMatching α) :=
  Classical.decEq _

instance {α : Type*} [Finite α] : Finite (TypePerfectMatching α) := by
  let f : TypePerfectMatching α → Equiv.Perm α := fun M ↦ M.mate
  exact Finite.of_injective f (by
    intro M N h
    apply TypePerfectMatching.ext
    intro i
    exact Equiv.congr_fun h i)

noncomputable instance {α : Type*} [Finite α] : Fintype (TypePerfectMatching α) :=
  Fintype.ofFinite _

/-- Transport a perfect matching through a relabelling equivalence. -/
def congr {α β : Type*} (e : α ≃ β) :
    TypePerfectMatching α ≃ TypePerfectMatching β where
  toFun M :=
    { mate := e.symm.trans (M.mate.trans e)
      mate_ne := by
        intro i h
        apply M.mate_ne (e.symm i)
        simpa using congrArg e.symm h
      mate_mate := by
        intro i
        simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
        rw [M.mate_mate]
        exact e.apply_symm_apply i }
  invFun M :=
    { mate := e.trans (M.mate.trans e.symm)
      mate_ne := by
        intro i h
        apply M.mate_ne (e i)
        simpa using congrArg e h
      mate_mate := by
        intro i
        simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
        rw [M.mate_mate]
        exact e.symm_apply_apply i }
  left_inv M := by ext i; simp
  right_inv M := by ext i; simp

/-- The concrete `Fin (2*n)` representation is equivalent to the generic one. -/
def finEquiv (n : ℕ) : PerfectMatching n ≃ TypePerfectMatching (Fin (2 * n)) where
  toFun M := ⟨M.mate, M.mate_ne, M.mate_mate⟩
  invFun M := ⟨M.mate, M.mate_ne, M.mate_mate⟩
  left_inv M := by cases M; rfl
  right_inv M := by cases M; rfl

/-- The vertices left after deleting a prescribed pair. -/
abbrev PairComplement {α : Type*} (x y : α) :=
  {z : α // z ≠ x ∧ z ≠ y}

/-- Restrict a matching to the complement of one of its pairs. -/
def erasePair {α : Type*} (M : TypePerfectMatching α) (x y : α)
    (hxy : M x = y) : TypePerfectMatching (PairComplement x y) := by
  let f : PairComplement x y → PairComplement x y := fun z ↦
    ⟨M z.1, by
      constructor
      · intro hz
        have h := congrArg M hz
        rw [M.mate_mate z.1, hxy] at h
        exact z.2.2 h
      · intro hz
        have h : M z.1 = M x := hz.trans hxy.symm
        exact z.2.1 (M.mate.injective h)⟩
  have hf : Function.Involutive f := by
    intro z
    apply Subtype.ext
    exact M.mate_mate z.1
  exact
    { mate := hf.toPerm
      mate_ne := by
        intro z hz
        apply M.mate_ne z.1
        exact congrArg Subtype.val hz
      mate_mate := hf }

/-- Insert a distinguished pair into a matching of its complement. -/
def insertPair {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    (N : TypePerfectMatching (PairComplement x y)) :
    TypePerfectMatching α := by
  let f : α → α := fun z ↦
    if hzx : z = x then y
    else if hzy : z = y then x
    else N ⟨z, hzx, hzy⟩
  have hf : Function.Involutive f := by
    intro z
    by_cases hzx : z = x
    · subst z
      simp [f, hxy, hxy.symm]
    · by_cases hzy : z = y
      · subst z
        simp [f, hxy, hxy.symm]
      · have hNx : (N ⟨z, hzx, hzy⟩).1 ≠ x :=
          (N ⟨z, hzx, hzy⟩).2.1
        have hNy : (N ⟨z, hzx, hzy⟩).1 ≠ y :=
          (N ⟨z, hzx, hzy⟩).2.2
        simp only [f, hzx, hzy, ↓reduceDIte, hNx, hNy]
        exact congrArg Subtype.val (N.mate_mate ⟨z, hzx, hzy⟩)
  exact
    { mate := hf.toPerm
      mate_ne := by
        intro z
        change f z ≠ z
        by_cases hzx : z = x
        · subst z
          simpa [f, hxy] using hxy.symm
        · by_cases hzy : z = y
          · subst z
            simpa [f, hxy, hxy.symm] using hxy
          · simp only [f, hzx, hzy, ↓reduceDIte]
            intro hz
            apply N.mate_ne ⟨z, hzx, hzy⟩
            exact Subtype.ext hz
      mate_mate := hf }

@[simp] theorem insertPair_apply_left {α : Type*} [DecidableEq α]
    (x y : α) (hxy : x ≠ y) (N : TypePerfectMatching (PairComplement x y)) :
    insertPair x y hxy N x = y := by
  simp [insertPair]

@[simp] theorem insertPair_apply_right {α : Type*} [DecidableEq α]
    (x y : α) (hxy : x ≠ y) (N : TypePerfectMatching (PairComplement x y)) :
    insertPair x y hxy N y = x := by
  simp [insertPair, hxy, hxy.symm]

@[simp] theorem insertPair_apply_complement {α : Type*} [DecidableEq α]
    (x y : α) (hxy : x ≠ y) (N : TypePerfectMatching (PairComplement x y))
    (z : PairComplement x y) :
    insertPair x y hxy N z.1 = (N z).1 := by
  simp [insertPair, z.2.1, z.2.2]

/-- Matchings whose distinguished point is paired with `y` are equivalent
to matchings on the complement of the two points. -/
def fiberEquivErasePair {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y) :
    {M : TypePerfectMatching α // M x = y} ≃
      TypePerfectMatching (PairComplement x y) where
  toFun M := erasePair M.1 x y M.2
  invFun N := ⟨insertPair x y hxy N, insertPair_apply_left x y hxy N⟩
  left_inv M := by
    apply Subtype.ext
    ext z
    by_cases hzx : z = x
    · subst z
      change insertPair x y hxy (erasePair M.1 x y M.2) x = M.1 x
      rw [insertPair_apply_left, M.2]
    · by_cases hzy : z = y
      · subst z
        change insertPair x y hxy (erasePair M.1 x y M.2) y = M.1 y
        rw [insertPair_apply_right]
        have h := congrArg M.1 M.2
        rw [M.1.mate_mate] at h
        exact h
      · change insertPair x y hxy (erasePair M.1 x y M.2) z = M.1 z
        rw [insertPair_apply_complement (z := ⟨z, hzx, hzy⟩)]
        rfl
  right_inv N := by
    apply TypePerfectMatching.ext
    intro z
    apply Subtype.ext
    exact insertPair_apply_complement x y hxy N z

/-- The mate of a distinguished vertex, bundled with the proof that it is
not the vertex itself. -/
def distinguishedMate {α : Type*} (x : α) (M : TypePerfectMatching α) :
    {y : α // y ≠ x} :=
  ⟨M x, M.mate_ne x⟩

/-- Sigma-fiber form of `fiberEquivErasePair`. -/
def distinguishedMateFiberEquiv {α : Type*} [DecidableEq α]
    (x : α) (y : {y : α // y ≠ x}) :
    {M : TypePerfectMatching α // distinguishedMate x M = y} ≃
      TypePerfectMatching (PairComplement x y.1) :=
  (Equiv.subtypeEquivProp (by
    funext M
    apply propext
    change (⟨M x, M.mate_ne x⟩ : {z : α // z ≠ x}) = y ↔ M x = y.1
    exact Subtype.ext_iff)).trans
      (fiberEquivErasePair x y.1 y.2.symm)

theorem card_pairComplement {α : Type*} [Fintype α] [DecidableEq α]
    (x y : α) (hxy : x ≠ y) :
    Fintype.card (PairComplement x y) = Fintype.card α - 2 := by
  have hpairs : Fintype.card {z : α // z = x ∨ z = y} = 2 :=
    Fintype.card_subtype_eq_or_eq_of_ne hxy
  simpa [PairComplement, not_or, hpairs] using
    (Fintype.card_subtype_compl (fun z : α ↦ z = x ∨ z = y))

/-- Deleting the pair containing `0` gives the matching-count recurrence. -/
theorem card_typePerfectMatching_fin_succ (n : ℕ) :
    Fintype.card (TypePerfectMatching (Fin (2 * (n + 1)))) =
      (2 * n + 1) * Fintype.card (TypePerfectMatching (Fin (2 * n))) := by
  classical
  let α := Fin (2 * (n + 1))
  let x : α := ⟨0, by omega⟩
  calc
    Fintype.card (TypePerfectMatching α) =
        Fintype.card
          (Σ y : {y : α // y ≠ x},
            {M : TypePerfectMatching α // distinguishedMate x M = y}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv (distinguishedMate x)).symm
    _ = ∑ y : {y : α // y ≠ x},
          Fintype.card
            {M : TypePerfectMatching α // distinguishedMate x M = y} := by
      rw [Fintype.card_sigma]
    _ = ∑ y : {y : α // y ≠ x},
          Fintype.card
            (TypePerfectMatching (PairComplement x y.1)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact Fintype.card_congr (distinguishedMateFiberEquiv x y)
    _ = ∑ _y : {y : α // y ≠ x},
          Fintype.card (TypePerfectMatching (Fin (2 * n))) := by
      apply Finset.sum_congr rfl
      intro y _
      have hc : Fintype.card (PairComplement x y.1) = 2 * n := by
        rw [card_pairComplement x y.1 y.2.symm]
        simp only [α, Fintype.card_fin]
        omega
      let e : PairComplement x y.1 ≃ Fin (2 * n) :=
        Fintype.equivOfCardEq (by simpa using hc)
      exact Fintype.card_congr (TypePerfectMatching.congr e)
    _ = (2 * n + 1) *
          Fintype.card (TypePerfectMatching (Fin (2 * n))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hcard : Fintype.card {y : α // y ≠ x} = 2 * n + 1 := by
        rw [Fintype.card_subtype_compl]
        have hone : Fintype.card {y : α // y = x} = 1 := by simp
        rw [hone]
        simp only [α, Fintype.card_fin]
        omega
      exact hcard

/-- Recurrence for the concrete `PerfectMatching` representation. -/
theorem card_perfectMatching_succ (n : ℕ) :
    Fintype.card (PerfectMatching (n + 1)) =
      (2 * n + 1) * Fintype.card (PerfectMatching n) := by
  rw [Fintype.card_congr (TypePerfectMatching.finEquiv (n + 1)),
    Fintype.card_congr (TypePerfectMatching.finEquiv n)]
  exact card_typePerfectMatching_fin_succ n

/-- The number of perfect matchings on `2*n` labelled vertices is the odd
double factorial `(2*n-1)‼` (with the empty matching counted once). -/
theorem card_perfectMatching (n : ℕ) :
    Fintype.card (PerfectMatching n) = (2 * n - 1)‼ := by
  induction n with
  | zero =>
      have hsubsingleton : Subsingleton (PerfectMatching 0) := by
        constructor
        intro M N
        cases M with
        | mk M hneM hinvM =>
          cases N with
          | mk N hneN hinvN =>
            have hMN : M = N := Equiv.ext (fun i ↦ Fin.elim0 i)
            cases hMN
            rfl
      have hnonempty : Nonempty (PerfectMatching 0) := by
        exact ⟨
          { mate := Equiv.refl _
            mate_ne := fun i ↦ Fin.elim0 i
            mate_mate := fun i ↦ Fin.elim0 i }⟩
      letI : Unique (PerfectMatching 0) :=
        { default := Classical.choice hnonempty
          uniq := fun M ↦ hsubsingleton.elim M (Classical.choice hnonempty) }
      simpa using (Fintype.card_unique : Fintype.card (PerfectMatching 0) = 1)
  | succ n ih =>
      rw [card_perfectMatching_succ, ih]
      cases n with
      | zero => norm_num
      | succ r =>
          rw [show 2 * (r + 1 + 1) - 1 = (2 * (r + 1) - 1) + 2 by omega,
            Nat.doubleFactorial_add_two]
          congr 1 <;> omega

end TypePerfectMatching

end LogdetLean.GramHafnian
