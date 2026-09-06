import LogdetLean.Coherence.MatchingAndOverlap
import Mathlib.Data.LawfulXor.Equiv
import Mathlib.Tactic
/-!
# Exact number of ordered matchings

An embedding of the `2*k` labeled endpoint slots into `Fin p` is the same
thing as

1. an ordered `k`-tuple of disjoint unordered edges, and
2. one Boolean orientation choice for each edge.

This file constructs that equivalence explicitly and derives the exact
identity

`(orderedMatchingTuples p k).card * 2^k = p.descFactorial (2*k)`.
-/

namespace LogdetLean.Coherence

noncomputable section

open scoped BigOperators

private lemma orderedMatchingTuples_mem_iff
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k) :
    edges ∈ orderedMatchingTuples p k ↔ edges.IsMatching := by
  simp [orderedMatchingTuples, orderedDistinctEdgeTuples]

/-- Flip the Boolean endpoint slot at edge `i` precisely when `o i` is true. -/
def orientEndpointSlot {k : ℕ} (o : MatchingOrientations k)
    (ib : Fin k × Bool) : Fin k × Bool :=
  (ib.1, Bool.xor (o ib.1) ib.2)

@[simp]
theorem orientEndpointSlot_fst {k : ℕ} (o : MatchingOrientations k)
    (ib : Fin k × Bool) :
    (orientEndpointSlot o ib).1 = ib.1 := rfl

/-- Flipping the selected endpoint slots twice restores the original slots. -/
theorem orientEndpointSlot_involutive {k : ℕ} (o : MatchingOrientations k) :
    Function.Involutive (orientEndpointSlot o) := by
  rintro ⟨i, b⟩
  cases h : o i <;> cases b <;> simp [orientEndpointSlot, h]

theorem orientEndpointSlot_injective {k : ℕ} (o : MatchingOrientations k) :
    Function.Injective (orientEndpointSlot o) :=
  (orientEndpointSlot_involutive o).injective

/-- Give every edge of an unordered ordered matching the prescribed Boolean
orientation, producing an embedding of all labeled endpoint slots. -/
def orientedOfMatchingData {p k : ℕ}
    (data : (↑(orderedMatchingTuples p k)) × MatchingOrientations k) :
    OrientedOrderedMatching p k where
  toFun ib := orderedEdgeEndpointMap data.1.1
    (orientEndpointSlot data.2 ib)
  inj' := by
    have hm : data.1.1.IsMatching :=
      (orderedMatchingTuples_mem_iff data.1.1).mp data.1.2
    exact hm.comp (orientEndpointSlot_injective data.2)

private lemma oriented_slots_ne
    {p k : ℕ} (f : OrientedOrderedMatching p k) (i : Fin k) :
    f (i, false) ≠ f (i, true) := by
  intro h
  have hpairs := f.injective h
  exact Bool.false_ne_true (congrArg Prod.snd hpairs)

/-- Canonically sort two distinct endpoints into a correlation edge. -/
def canonicalCorrelationEdge {p : ℕ} (a b : Fin p) (hab : a ≠ b) :
    CorrelationEdge p :=
  ⟨(min a b, max a b), min_lt_max.mpr hab⟩

/-- Forget the orientations of an endpoint embedding, sorting the two
endpoints belonging to each labeled edge. -/
def canonicalEdgesOfOriented {p k : ℕ}
    (f : OrientedOrderedMatching p k) : OrderedDistinctEdgeTuple p k where
  toFun i := canonicalCorrelationEdge
    (f (i, false)) (f (i, true)) (oriented_slots_ne f i)
  inj' := by
    intro i j hij
    have hmin := congrArg (fun e : CorrelationEdge p ↦ e.1.1) hij
    change min (f (i, false)) (f (i, true)) =
      min (f (j, false)) (f (j, true)) at hmin
    by_cases hi : f (i, false) ≤ f (i, true)
    · by_cases hj : f (j, false) ≤ f (j, true)
      · rw [min_eq_left hi, min_eq_left hj] at hmin
        exact congrArg Prod.fst (f.injective hmin)
      · have hj' : f (j, true) ≤ f (j, false) := le_of_not_ge hj
        rw [min_eq_left hi, min_eq_right hj'] at hmin
        exact congrArg Prod.fst (f.injective hmin)
    · have hi' : f (i, true) ≤ f (i, false) := le_of_not_ge hi
      by_cases hj : f (j, false) ≤ f (j, true)
      · rw [min_eq_right hi', min_eq_left hj] at hmin
        exact congrArg Prod.fst (f.injective hmin)
      · have hj' : f (j, true) ≤ f (j, false) := le_of_not_ge hj
        rw [min_eq_right hi', min_eq_right hj'] at hmin
        exact congrArg Prod.fst (f.injective hmin)

/-- The orientation bit remembered while sorting the endpoints.  It is true
exactly when the endpoint in the `false` slot was the larger endpoint. -/
def orientationsOfOriented {p k : ℕ}
    (f : OrientedOrderedMatching p k) : MatchingOrientations k :=
  fun i ↦ decide (f (i, true) < f (i, false))

private lemma canonical_oriented_endpoint
    {p k : ℕ} (f : OrientedOrderedMatching p k) (ib : Fin k × Bool) :
    orderedEdgeEndpointMap (canonicalEdgesOfOriented f)
        (orientEndpointSlot (orientationsOfOriented f) ib) = f ib := by
  rcases ib with ⟨i, side⟩
  have hne := oriented_slots_ne f i
  by_cases hlt : f (i, false) < f (i, true)
  · have hrev : ¬f (i, true) < f (i, false) := not_lt_of_ge hlt.le
    cases side <;>
      simp [orderedEdgeEndpointMap, correlationEdgeEndpoint,
        canonicalEdgesOfOriented, canonicalCorrelationEdge,
        orientEndpointSlot, orientationsOfOriented, hrev,
        min_eq_left hlt.le, max_eq_right hlt.le]
  · have hle : f (i, true) ≤ f (i, false) := le_of_not_gt hlt
    have hrev : f (i, true) < f (i, false) :=
      lt_of_le_of_ne hle hne.symm
    cases side <;>
      simp [orderedEdgeEndpointMap, correlationEdgeEndpoint,
        canonicalEdgesOfOriented, canonicalCorrelationEdge,
        orientEndpointSlot, orientationsOfOriented, hrev,
        min_eq_right hle, max_eq_left hle]

private theorem canonicalEdgesOfOriented_isMatching
    {p k : ℕ} (f : OrientedOrderedMatching p k) :
    (canonicalEdgesOfOriented f).IsMatching := by
  intro a b hab
  let o := orientationsOfOriented f
  have ha := canonical_oriented_endpoint f (orientEndpointSlot o a)
  have hb := canonical_oriented_endpoint f (orientEndpointSlot o b)
  rw [orientEndpointSlot_involutive o a] at ha
  rw [orientEndpointSlot_involutive o b] at hb
  have hf : f (orientEndpointSlot o a) = f (orientEndpointSlot o b) := by
    rw [← ha, ← hb, hab]
  exact orientEndpointSlot_injective o (f.injective hf)

/-- Recover the unordered matching and all `k` orientation bits from an
oriented endpoint embedding. -/
def matchingDataOfOriented {p k : ℕ} (f : OrientedOrderedMatching p k) :
    (↑(orderedMatchingTuples p k)) × MatchingOrientations k :=
  (⟨canonicalEdgesOfOriented f,
      (orderedMatchingTuples_mem_iff _).mpr
        (canonicalEdgesOfOriented_isMatching f)⟩,
    orientationsOfOriented f)

private theorem orientedOfMatchingData_matchingDataOfOriented
    {p k : ℕ} (f : OrientedOrderedMatching p k) :
    orientedOfMatchingData (matchingDataOfOriented f) = f := by
  apply Function.Embedding.ext
  intro ib
  exact canonical_oriented_endpoint f ib

private lemma canonicalEdges_orientedOfMatchingData
    {p k : ℕ}
    (data : (↑(orderedMatchingTuples p k)) × MatchingOrientations k) :
    canonicalEdgesOfOriented (orientedOfMatchingData data) = data.1.1 := by
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  have hedge := (data.1.1 i).2
  cases ho : data.2 i <;>
    simp [canonicalEdgesOfOriented, canonicalCorrelationEdge,
      orientedOfMatchingData, orientEndpointSlot, orderedEdgeEndpointMap,
      correlationEdgeEndpoint, ho, hedge.le]

private lemma orientations_orientedOfMatchingData
    {p k : ℕ}
    (data : (↑(orderedMatchingTuples p k)) × MatchingOrientations k) :
    orientationsOfOriented (orientedOfMatchingData data) = data.2 := by
  funext i
  have hedge := (data.1.1 i).2
  cases ho : data.2 i <;>
    simp [orientationsOfOriented, orientedOfMatchingData,
      orientEndpointSlot, orderedEdgeEndpointMap, correlationEdgeEndpoint,
      ho, hedge, not_lt_of_ge hedge.le]

private theorem matchingDataOfOriented_orientedOfMatchingData
    {p k : ℕ}
    (data : (↑(orderedMatchingTuples p k)) × MatchingOrientations k) :
    matchingDataOfOriented (orientedOfMatchingData data) = data := by
  apply Prod.ext
  · apply Subtype.ext
    exact canonicalEdges_orientedOfMatchingData data
  · exact orientations_orientedOfMatchingData data

/-- Explicit equivalence between oriented endpoint embeddings and an ordered
matching together with one orientation bit per edge. -/
def orientedOrderedMatchingEquivMatchingData (p k : ℕ) :
    OrientedOrderedMatching p k ≃
      (↑(orderedMatchingTuples p k)) × MatchingOrientations k where
  toFun := matchingDataOfOriented
  invFun := orientedOfMatchingData
  left_inv := orientedOfMatchingData_matchingDataOfOriented
  right_inv := matchingDataOfOriented_orientedOfMatchingData

/-- Exact ordered-matching count. -/
theorem card_orderedMatchingTuples_mul_pow_two (p k : ℕ) :
    (orderedMatchingTuples p k).card * 2 ^ k =
      p.descFactorial (2 * k) := by
  calc
    (orderedMatchingTuples p k).card * 2 ^ k =
        Fintype.card
          ((↑(orderedMatchingTuples p k)) × MatchingOrientations k) := by
      simp
    _ = Fintype.card (OrientedOrderedMatching p k) :=
      Fintype.card_congr
        (orientedOrderedMatchingEquivMatchingData p k).symm
    _ = p.descFactorial (2 * k) := card_orientedOrderedMatching p k

/-- Divided form of the exact matching count. -/
theorem card_orderedMatchingTuples_eq_descFactorial_div_pow_two (p k : ℕ) :
    (orderedMatchingTuples p k).card =
      p.descFactorial (2 * k) / 2 ^ k := by
  have hmul : 2 ^ k * (orderedMatchingTuples p k).card =
      p.descFactorial (2 * k) := by
    simpa [Nat.mul_comm] using card_orderedMatchingTuples_mul_pow_two p k
  exact Nat.eq_div_of_mul_eq_right
    (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)) hmul

end

end LogdetLean.Coherence
