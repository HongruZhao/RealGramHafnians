import LogdetLean.Coherence.ColumnPermutation
import LogdetLean.Coherence.OrderedForestPower
import LogdetLean.Coherence.MatchingAndOverlap
import Mathlib.Tactic
/-!
# Relabeled ordered-forest certificates

This file isolates the deterministic interface between an arbitrary tuple of
correlation edges and the exact ordered-forest probability calculation.

A certificate consists of a permutation listing the original vertices in a
forest order and an `OrderedForest` whose genuine edges all occur in the
given tuple.  The all-tuple exceedance event is therefore contained in the
pullback of the ordered-forest event.  Gaussian column exchangeability and
`gaussianPi_orderedForest_jointExceedanceReal_eq_betaTail_pow` then give the
required beta-tail power bound.

No existence of a certificate is assumed as an axiom: the structure is data.
The remaining purely finite graph task is to construct one with sufficiently
many edges for every nonmatching tuple.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set

/-- Local symmetry lemma, kept under a distinct name so this module remains
independent of the much larger prefix-control development. -/
private theorem squaredNormalizedInner_swap
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) :
    squaredNormalizedInner u v = squaredNormalizedInner v u := by
  unfold squaredNormalizedInner
  rw [real_inner_comm]
  ring

/-- The parent rank `i : Fin n` viewed as a rank in a `p`-vertex family. -/
def orderedForestParentRank {p : ℕ} (n : Fin p) (i : Fin n.val) : Fin p :=
  i.castLT (lt_trans i.isLt n.isLt)

/-- All edges in an ordered distinct tuple exceed a common threshold. -/
def orderedEdgeTupleFamilyExceedanceEvent
    {p k : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (edges : OrderedDistinctEdgeTuple p k) (t : ℝ) : Set (Fin p → E) :=
  {v | ∀ j : Fin k,
    t < squaredNormalizedInner (v (edges j).1.1) (v (edges j).1.2)}

theorem measurableSet_orderedEdgeTupleFamilyExceedanceEvent
    {p k : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (edges : OrderedDistinctEdgeTuple p k) (t : ℝ) :
    MeasurableSet
      (orderedEdgeTupleFamilyExceedanceEvent (E := E) edges t) := by
  have hset : MeasurableSet
      (⋂ j : Fin k,
        {v : Fin p → E |
          t < squaredNormalizedInner (v (edges j).1.1) (v (edges j).1.2)}) := by
    apply MeasurableSet.iInter
    intro j
    have hpair : Measurable (fun v : Fin p → E ↦
        (v (edges j).1.1, v (edges j).1.2)) :=
      (measurable_pi_apply (edges j).1.1).prodMk
        (measurable_pi_apply (edges j).1.2)
    exact measurableSet_lt measurable_const
      ((measurable_uncurry_squaredNormalizedInner (E := E)).comp hpair)
  convert hset using 1
  ext v
  simp [orderedEdgeTupleFamilyExceedanceEvent]

/-- A relabeling which exhibits a subset of a tuple as an ordered forest.

`vertexOrder n` is the original vertex occupying rank `n`.  If rank `n` has
parent `i`, the corresponding unordered original edge must occur in the
tuple.  The disjunction records its two possible orientations. -/
structure TupleOrderedForestCertificate {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) where
  vertexOrder : Equiv.Perm (Fin p)
  forest : OrderedForest
  edgeWitness : ∀ (n : Fin p) (i : Fin n.val),
    forest.parent n.val = some i →
      ∃ j : Fin k,
        (vertexOrder (orderedForestParentRank n i), vertexOrder n) =
            (edges j).1 ∨
          (vertexOrder n, vertexOrder (orderedForestParentRank n i)) =
            (edges j).1

/-- The all-tuple event implies the certified ordered-forest event after the
certificate's column relabeling. -/
theorem orderedEdgeTupleFamilyExceedanceEvent_subset_certificatePreimage
    {p k : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (edges : OrderedDistinctEdgeTuple p k)
    (C : TupleOrderedForestCertificate edges) (t : ℝ) :
    orderedEdgeTupleFamilyExceedanceEvent (E := E) edges t ⊆
      permuteColumns (E := E) C.vertexOrder.symm ⁻¹'
        orderedForestFamilyJointExceedanceEvent (E := E) C.forest t p := by
  intro v hv
  intro n
  cases hparent : C.forest.parent n.val with
  | none => trivial
  | some i =>
      obtain ⟨j, hedge | hedge⟩ := C.edgeWitness n i hparent
      · have hleft : C.vertexOrder (orderedForestParentRank n i) =
            (edges j).1.1 := by
          simpa using congrArg Prod.fst hedge
        have hright : C.vertexOrder n = (edges j).1.2 := by
          simpa using congrArg Prod.snd hedge
        change t < squaredNormalizedInner
          (v (C.vertexOrder (orderedForestParentRank n i)))
          (v (C.vertexOrder n))
        rw [hleft, hright]
        exact hv j
      · have hleft : C.vertexOrder n = (edges j).1.1 := by
          simpa using congrArg Prod.fst hedge
        have hright : C.vertexOrder (orderedForestParentRank n i) =
            (edges j).1.2 := by
          simpa using congrArg Prod.snd hedge
        change t < squaredNormalizedInner
          (v (C.vertexOrder (orderedForestParentRank n i)))
          (v (C.vertexOrder n))
        rw [squaredNormalizedInner_swap, hleft, hright]
        exact hv j

/-- Exact configurationwise probability bound supplied by any relabeled
ordered-forest certificate. -/
theorem gaussianTuple_jointExceedanceReal_le_betaTail_pow_of_certificate
    {p k : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (edges : OrderedDistinctEdgeTuple p k)
    (C : TupleOrderedForestCertificate edges)
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m) (t : ℝ) :
    (Measure.pi fun _ : Fin p ↦ stdGaussian E).real
        (orderedEdgeTupleFamilyExceedanceEvent (E := E) edges t) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Set.Ioi t)).toReal ^ orderedForestEdgeCount C.forest p := by
  let μ : Measure (Fin p → E) := Measure.pi fun _ : Fin p ↦ stdGaussian E
  let forestEvent : Set (Fin p → E) :=
    orderedForestFamilyJointExceedanceEvent (E := E) C.forest t p
  have hsubset : orderedEdgeTupleFamilyExceedanceEvent (E := E) edges t ⊆
      permuteColumns (E := E) C.vertexOrder.symm ⁻¹' forestEvent :=
    orderedEdgeTupleFamilyExceedanceEvent_subset_certificatePreimage
      edges C t
  have hforestMeas : MeasurableSet forestEvent :=
    measurableSet_orderedForestFamilyJointExceedanceEvent C.forest t p
  have hpres := measurePreserving_permuteGaussianColumns
    (E := E) C.vertexOrder.symm
  have hpreimage : μ
      (permuteColumns (E := E) C.vertexOrder.symm ⁻¹' forestEvent) =
        μ forestEvent := hpres.measure_preimage hforestMeas.nullMeasurableSet
  calc
    μ.real (orderedEdgeTupleFamilyExceedanceEvent (E := E) edges t) ≤
        μ.real
          (permuteColumns (E := E) C.vertexOrder.symm ⁻¹' forestEvent) :=
      measureReal_mono hsubset
    _ = μ.real forestEvent := by
      rw [measureReal_def, measureReal_def, hpreimage]
    _ = (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Set.Ioi t)).toReal ^ orderedForestEdgeCount C.forest p := by
      exact gaussianPi_orderedForest_jointExceedanceReal_eq_betaTail_pow
        C.forest m hdim hm t p

/-- If the certificate contains at least `r` genuine forest edges, its
configuration probability is at most the `r`-th beta-tail power. -/
theorem gaussianTuple_jointExceedanceReal_le_betaTail_pow_of_certificate_count
    {p k : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (edges : OrderedDistinctEdgeTuple p k)
    (C : TupleOrderedForestCertificate edges)
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m) (t : ℝ)
    (r : ℕ) (hr : r ≤ orderedForestEdgeCount C.forest p) :
    (Measure.pi fun _ : Fin p ↦ stdGaussian E).real
        (orderedEdgeTupleFamilyExceedanceEvent (E := E) edges t) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Set.Ioi t)).toReal ^ r := by
  let q : ℝ := (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
    (Set.Ioi t)).toReal
  letI : IsProbabilityMeasure
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasureBeta (by norm_num)
      (div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num))
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := measureReal_le_one
  calc
    (Measure.pi fun _ : Fin p ↦ stdGaussian E).real
        (orderedEdgeTupleFamilyExceedanceEvent (E := E) edges t) ≤
      q ^ orderedForestEdgeCount C.forest p :=
        gaussianTuple_jointExceedanceReal_le_betaTail_pow_of_certificate
          edges C m hdim hm t
    _ ≤ q ^ r := pow_le_pow_of_le_one hq0 hq1 hr

end

end LogdetLean.Coherence
