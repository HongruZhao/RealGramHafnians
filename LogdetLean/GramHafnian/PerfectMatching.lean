import Mathlib
/-!
# Perfect matchings on `Fin (2 * n)`

This file gives a literal, finite representation of an undirected perfect
matching: its fixed-point-free involution.  This representation has no
quotient and is therefore convenient for finite hafnian sums.
-/

namespace LogdetLean.GramHafnian

/-- A perfect matching of `Fin (2 * n)`, represented by its mate involution. -/
structure PerfectMatching (n : ℕ) where
  mate : Equiv.Perm (Fin (2 * n))
  mate_ne : ∀ i, mate i ≠ i
  mate_mate : ∀ i, mate (mate i) = i

namespace PerfectMatching

instance (n : ℕ) : CoeFun (PerfectMatching n) (fun _ ↦ Fin (2 * n) → Fin (2 * n)) :=
  ⟨fun M ↦ M.mate⟩

noncomputable instance (n : ℕ) : DecidableEq (PerfectMatching n) := Classical.decEq _

instance (n : ℕ) : Finite (PerfectMatching n) := by
  let f : PerfectMatching n → Equiv.Perm (Fin (2 * n)) := fun M ↦ M.mate
  exact Finite.of_injective f (by
    intro M N h
    cases M
    cases N
    simp only [f] at h
    cases h
    rfl)

noncomputable instance (n : ℕ) : Fintype (PerfectMatching n) := Fintype.ofFinite _

@[simp] theorem apply_ne (M : PerfectMatching n) (i : Fin (2 * n)) : M i ≠ i :=
  M.mate_ne i

@[simp] theorem apply_apply (M : PerfectMatching n) (i : Fin (2 * n)) : M (M i) = i :=
  M.mate_mate i

/-- The smaller endpoint of each matched pair. -/
def pairReps (M : PerfectMatching n) : Finset (Fin (2 * n)) :=
  Finset.univ.filter fun i ↦ i < M i

/-- The larger endpoint of each matched pair. -/
def upperReps (M : PerfectMatching n) : Finset (Fin (2 * n)) :=
  Finset.univ.filter fun i ↦ M i < i

@[simp] theorem mem_pairReps_iff (M : PerfectMatching n) (i : Fin (2 * n)) :
    i ∈ M.pairReps ↔ i < M i := by
  simp [pairReps]

theorem mate_mem_pairReps_iff (M : PerfectMatching n) (i : Fin (2 * n)) :
    M i ∈ M.pairReps ↔ M i < i := by
  simp [pairReps]

@[simp] theorem mem_upperReps_iff (M : PerfectMatching n) (i : Fin (2 * n)) :
    i ∈ M.upperReps ↔ M i < i := by
  simp [upperReps]

theorem exactly_one_mem_pairReps (M : PerfectMatching n) (i : Fin (2 * n)) :
    (i ∈ M.pairReps ∨ M i ∈ M.pairReps) ∧
      ¬ (i ∈ M.pairReps ∧ M i ∈ M.pairReps) := by
  have hne : M i ≠ i := M.apply_ne i
  rw [M.mem_pairReps_iff, M.mate_mem_pairReps_iff]
  exact ⟨lt_or_gt_of_ne hne.symm, fun h ↦ (lt_asymm h.1 h.2)⟩

theorem image_mate_pairReps (M : PerfectMatching n) :
    M.pairReps.image M = M.upperReps := by
  classical
  ext i
  constructor
  · intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [M.mem_upperReps_iff, M.apply_apply]
    exact (M.mem_pairReps_iff j).mp hj
  · intro hi
    rw [M.mem_upperReps_iff] at hi
    rw [Finset.mem_image]
    refine ⟨M i, ?_, M.apply_apply i⟩
    rw [M.mem_pairReps_iff, M.apply_apply]
    exact hi

theorem pairReps_disjoint_upperReps (M : PerfectMatching n) :
    Disjoint M.pairReps M.upperReps := by
  classical
  rw [Finset.disjoint_left]
  intro i hlo hiup
  exact (lt_asymm ((M.mem_pairReps_iff i).mp hlo)
    ((M.mem_upperReps_iff i).mp hiup))

theorem pairReps_union_upperReps (M : PerfectMatching n) :
    M.pairReps ∪ M.upperReps = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_union, M.mem_pairReps_iff, M.mem_upperReps_iff,
    Finset.mem_univ, iff_true]
  exact lt_or_gt_of_ne (M.apply_ne i).symm

/-- A perfect matching on `2n` vertices has exactly `n` pairs. -/
theorem card_pairReps (M : PerfectMatching n) : M.pairReps.card = n := by
  classical
  have himage : M.upperReps.card = M.pairReps.card := by
    rw [← M.image_mate_pairReps]
    exact Finset.card_image_of_injective _ M.mate.injective
  have hcard := Finset.card_union_of_disjoint M.pairReps_disjoint_upperReps
  rw [M.pairReps_union_upperReps, Finset.card_univ, Fintype.card_fin,
    himage] at hcard
  omega

end PerfectMatching

end LogdetLean.GramHafnian
