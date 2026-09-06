import LogdetLean.Coherence.ColumnPermutation
import Mathlib.Tactic
/-!
# Permuting right-nested iid tuples

The Bartlett development represents a finite list of Gaussian columns by
`NestedTuple E p`, whereas column exchangeability is most convenient on the
ordinary family type `Fin p → E`.  The existing map `nestedTupleToFin` was
one-way.  This file supplies its measurable inverse and packages column
permutation as a measure-preserving self-map of the nested representation.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory

/-- Rebuild a right-nested tuple from an ordinary finite family. -/
def finFamilyToNestedTuple {E : Type*} :
    (p : ℕ) → (Fin p → E) → NestedTuple E p
  | 0, _ => ULift.up Unit.unit
  | p + 1, v =>
      (finFamilyToNestedTuple p (fun i => v i.castSucc), v (Fin.last p))

@[simp]
theorem nestedTupleToFin_finFamilyToNestedTuple
    {E : Type*} : ∀ (p : ℕ) (v : Fin p → E),
    nestedTupleToFin p (finFamilyToNestedTuple p v) = v := by
  intro p
  induction p with
  | zero =>
      intro v
      funext i
      exact Fin.elim0 i
  | succ p ih =>
      intro v
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [finFamilyToNestedTuple, nestedTupleToFin]
      · simp [finFamilyToNestedTuple, nestedTupleToFin, ih]

@[simp]
theorem finFamilyToNestedTuple_nestedTupleToFin
    {E : Type*} : ∀ (p : ℕ) (z : NestedTuple E p),
    finFamilyToNestedTuple p (nestedTupleToFin p z) = z := by
  intro p
  induction p with
  | zero =>
      intro z
      rcases z with ⟨u⟩
      cases u
      rfl
  | succ p ih =>
      intro z
      rcases z with ⟨z, y⟩
      simp [finFamilyToNestedTuple, nestedTupleToFin, ih]

theorem nestedTupleToFin_injective
    {E : Type*} (p : ℕ) :
    Function.Injective (nestedTupleToFin (α := E) p) := by
  intro z w hzw
  rw [← finFamilyToNestedTuple_nestedTupleToFin p z,
    ← finFamilyToNestedTuple_nestedTupleToFin p w, hzw]

/-- The inverse conversion is measurable for the coordinatewise product
measurable structures. -/
theorem measurable_finFamilyToNestedTuple
    {E : Type*} [MeasurableSpace E] : ∀ p : ℕ,
    Measurable (finFamilyToNestedTuple (E := E) p) := by
  intro p
  induction p with
  | zero => exact measurable_const
  | succ p ih =>
      have hprior : Measurable
          (fun v : Fin (p + 1) → E => fun i : Fin p => v i.castSucc) := by
        exact measurable_pi_lambda _ fun i => measurable_pi_apply i.castSucc
      exact (ih.comp hprior).prodMk (measurable_pi_apply (Fin.last p))

/-- `NestedTuple E p` and `Fin p → E` are measurably equivalent. -/
def nestedTupleFinMeasurableEquiv
    (E : Type*) [MeasurableSpace E] (p : ℕ) :
    NestedTuple E p ≃ᵐ (Fin p → E) where
  toFun := nestedTupleToFin p
  invFun := finFamilyToNestedTuple p
  left_inv := finFamilyToNestedTuple_nestedTupleToFin p
  right_inv := nestedTupleToFin_finFamilyToNestedTuple p
  measurable_toFun := measurable_nestedTupleToFin p
  measurable_invFun := measurable_finFamilyToNestedTuple p

/-- The inverse conversion carries the ordinary finite iid product measure
back to the right-nested iid product measure. -/
theorem measurePreserving_finFamilyToNestedTuple
    {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [SigmaFinite mu] (p : ℕ) :
    MeasurePreserving (finFamilyToNestedTuple (E := E) p)
      (Measure.pi fun _ : Fin p => mu) (nestedProductMeasure mu p) := by
  refine ⟨measurable_finFamilyToNestedTuple p, ?_⟩
  have hread := map_nestedTupleToFin_nestedProductMeasure mu p
  calc
    Measure.map (finFamilyToNestedTuple (E := E) p)
        (Measure.pi fun _ : Fin p => mu) =
      Measure.map (finFamilyToNestedTuple (E := E) p)
        (Measure.map (nestedTupleToFin (α := E) p)
          (nestedProductMeasure mu p)) := by rw [hread]
    _ = Measure.map
        (finFamilyToNestedTuple (E := E) p ∘ nestedTupleToFin p)
        (nestedProductMeasure mu p) := by
      rw [Measure.map_map (measurable_finFamilyToNestedTuple p)
        (measurable_nestedTupleToFin p)]
    _ = nestedProductMeasure mu p := by
      rw [show finFamilyToNestedTuple (E := E) p ∘ nestedTupleToFin p = id by
        funext z
        exact finFamilyToNestedTuple_nestedTupleToFin p z]
      exact Measure.map_id

/-- Relabel a nested tuple by first reading it as a finite family and then
rebuilding the nested representation. -/
def permuteNestedTuple {p : ℕ} {E : Type*}
    (sigma : Equiv.Perm (Fin p)) (z : NestedTuple E p) : NestedTuple E p :=
  finFamilyToNestedTuple p (permuteColumns sigma (nestedTupleToFin p z))

theorem measurable_permuteNestedTuple
    {p : ℕ} {E : Type*} [MeasurableSpace E]
    (sigma : Equiv.Perm (Fin p)) :
    Measurable (permuteNestedTuple (E := E) sigma) := by
  unfold permuteNestedTuple
  exact (measurable_finFamilyToNestedTuple p).comp
    ((measurable_permuteColumns sigma).comp (measurable_nestedTupleToFin p))

@[simp]
theorem nestedTupleToFin_permuteNestedTuple
    {p : ℕ} {E : Type*} (sigma : Equiv.Perm (Fin p))
    (z : NestedTuple E p) :
    nestedTupleToFin p (permuteNestedTuple sigma z) =
      permuteColumns sigma (nestedTupleToFin p z) := by
  simp [permuteNestedTuple]

@[simp]
theorem permuteNestedTuple_refl
    {p : ℕ} {E : Type*} (z : NestedTuple E p) :
    permuteNestedTuple (Equiv.refl (Fin p)) z = z := by
  apply nestedTupleToFin_injective p
  rw [nestedTupleToFin_permuteNestedTuple]
  funext i
  rfl

@[simp]
theorem permuteNestedTuple_symm_apply
    {p : ℕ} {E : Type*} (sigma : Equiv.Perm (Fin p))
    (z : NestedTuple E p) :
    permuteNestedTuple sigma.symm (permuteNestedTuple sigma z) = z := by
  apply nestedTupleToFin_injective p
  rw [nestedTupleToFin_permuteNestedTuple,
    nestedTupleToFin_permuteNestedTuple]
  funext i
  simp [permuteColumns]

/-- Every iid right-nested product law is invariant under a finite column
permutation. -/
theorem measurePreserving_permuteNestedTuple
    {p : ℕ} {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [SigmaFinite mu] (sigma : Equiv.Perm (Fin p)) :
    MeasurePreserving (permuteNestedTuple (E := E) sigma)
      (nestedProductMeasure mu p) (nestedProductMeasure mu p) := by
  have hread := measurePreserving_nestedTupleToFin mu p
  have hperm := measurePreserving_permuteColumns_pi mu sigma
  have hbuild := measurePreserving_finFamilyToNestedTuple mu p
  exact hbuild.comp (hperm.comp hread)

theorem map_permuteNestedTuple
    {p : ℕ} {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [SigmaFinite mu] (sigma : Equiv.Perm (Fin p)) :
    Measure.map (permuteNestedTuple (E := E) sigma)
        (nestedProductMeasure mu p) = nestedProductMeasure mu p :=
  (measurePreserving_permuteNestedTuple mu sigma).map_eq

end

end LogdetLean.Coherence
