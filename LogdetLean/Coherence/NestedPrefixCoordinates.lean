import LogdetLean.Coherence.ConditionedJointLaw
/-!
# Coordinates of a retained nested prefix

These elementary identities connect the right-nested representation used by
the Bartlett construction with the ordinary finite-family representation
used for column permutations.
-/

namespace LogdetLean.Coherence

noncomputable section

/-- Reading one of the first `q` coordinates from a tuple with `r` appended
coordinates agrees with first retaining the `q`-coordinate prefix. -/
theorem nestedTupleToFin_castAdd_eq_prefix
    {α : Type} (q : ℕ) : ∀ r (z : NestedTuple α (q + r)) (i : Fin q),
    nestedTupleToFin (q + r) z (Fin.castAdd r i) =
      nestedTupleToFin q (nestedTuplePrefix q r z) i := by
  intro r
  induction r with
  | zero =>
      intro z i
      rfl
  | succ r ih =>
      rintro ⟨z, x⟩ i
      rw [show Fin.castAdd (r + 1) i =
          (Fin.castAdd r i).castSucc by
        apply Fin.ext
        rfl]
      simp only [nestedTupleToFin, Fin.snoc_castSucc, nestedTuplePrefix]
      convert ih z i using 1
      rfl

/-- The lifted raw prefix event is simply membership of the centered nested
prefix in the original prefix event. -/
theorem mem_centeredGaussianPrefixEvent_iff
    (m q r : ℕ)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (z : NestedTuple (ObservationSpace (m + 1)) (q + r)) :
    z ∈ centeredGaussianPrefixEvent m q r s ↔
      nestedTuplePrefix q r (centerNested (m + 1) (q + r) z) ∈ s := by
  unfold centeredGaussianPrefixEvent
  change centeredRetainedPrefixTailFactors (m + 1) q r z ∈
      retainedPrefixEvent (β := ℝ) q r s ↔ _
  have hmem : ∀ r
      (w : RetainedPrefixTailTuple (centeredSubspace (m + 1)) ℝ q r),
      w ∈ retainedPrefixEvent (β := ℝ) q r s ↔
        retainedPrefixProjection q r w ∈ s := by
    intro r
    induction r with
    | zero =>
        intro w
        rfl
    | succ r ih =>
        rintro ⟨w, b⟩
        simpa [retainedPrefixEvent, retainedPrefixProjection] using ih w
  rw [hmem]
  rw [retainedPrefixProjection_centeredRetainedPrefixTailFactors]

end

end LogdetLean.Coherence
