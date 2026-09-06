import LogdetLean.Coherence.OrderedForestIndependence
import Mathlib.Data.Fintype.CardEmbedding
/-!
# Matching and overlap combinatorics for coherence exceedances

This module records the exact finite combinatorics used when expanding a
falling factorial of the exceedance count.

* ordered selections of distinct edges are embeddings;
* a matching is characterized by injectivity of its endpoint map;
* nonmatchings use at most `2*k - 1` vertices;
* oriented ordered matchings have cardinality `(p)_(2k)`; forgetting the two
  orientations of each edge accounts for the familiar factor `2^k`;
* a graph event is dominated by every spanning-forest subevent, so no cycle
  independence is ever assumed;
* a finite weighted overlap sum is reduced to deterministic graph-type fiber
  counts and one probability bound per graph type.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- One canonically oriented unordered edge: its first endpoint is smaller
than its second endpoint. -/
abbrev CorrelationEdge (p : ℕ) :=
  {e : Fin p × Fin p // e.1 < e.2}

/-- An ordered `k`-tuple of pairwise distinct correlation edges. -/
abbrev OrderedDistinctEdgeTuple (p k : ℕ) :=
  Fin k ↪ CorrelationEdge p

/-- The endpoint selected by a Boolean side label. -/
def correlationEdgeEndpoint {p : ℕ} (e : CorrelationEdge p) (side : Bool) : Fin p :=
  if side then e.1.2 else e.1.1

/-- The endpoint map of an ordered edge tuple. -/
def orderedEdgeEndpointMap {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k) :
    Fin k × Bool → Fin p :=
  fun ib ↦ correlationEdgeEndpoint (edges ib.1) ib.2

/-- A distinct ordered edge tuple is a matching precisely when all of its
`2*k` endpoint slots contain different vertices. -/
def OrderedDistinctEdgeTuple.IsMatching
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k) : Prop :=
  Function.Injective (orderedEdgeEndpointMap edges)

/-- The finite set of all ordered distinct edge tuples. -/
def orderedDistinctEdgeTuples (p k : ℕ) :
    Finset (OrderedDistinctEdgeTuple p k) := Finset.univ

/-- The matching part of the ordered distinct edge tuples. -/
def orderedMatchingTuples (p k : ℕ) :
    Finset (OrderedDistinctEdgeTuple p k) := by
  classical
  exact (orderedDistinctEdgeTuples p k).filter fun edges ↦ edges.IsMatching

/-- The overlapping (nonmatching) part of the ordered distinct edge tuples. -/
def orderedOverlapTuples (p k : ℕ) :
    Finset (OrderedDistinctEdgeTuple p k) := by
  classical
  exact (orderedDistinctEdgeTuples p k).filter fun edges ↦ ¬edges.IsMatching

/-- Exact matching/overlap partition of every weighted factorial expansion. -/
theorem sum_orderedDistinct_eq_matching_add_overlap
    {M : Type*} [AddCommMonoid M]
    (p k : ℕ) (w : OrderedDistinctEdgeTuple p k → M) :
    ∑ edges ∈ orderedDistinctEdgeTuples p k, w edges =
      (∑ edges ∈ orderedMatchingTuples p k, w edges) +
        ∑ edges ∈ orderedOverlapTuples p k, w edges := by
  classical
  unfold orderedMatchingTuples orderedOverlapTuples
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := orderedDistinctEdgeTuples p k)
    (p := fun edges ↦ edges.IsMatching) w]

/-- The vertices used by an ordered edge tuple. -/
def orderedEdgeVertexSet {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k) :
    Finset (Fin p) :=
  Finset.univ.image (orderedEdgeEndpointMap edges)

/-- Every ordered `k`-edge tuple uses at most `2*k` vertices. -/
theorem orderedEdgeVertexSet_card_le {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) :
    (orderedEdgeVertexSet edges).card ≤ 2 * k := by
  classical
  calc
    (orderedEdgeVertexSet edges).card ≤
        (Finset.univ : Finset (Fin k × Bool)).card := by
      exact Finset.card_image_le
    _ = 2 * k := by simp [Nat.mul_comm]

/-- A nonmatching `k`-tuple loses at least one of its `2*k` possible distinct
vertices.  This is the first deterministic saving in the overlap estimate. -/
theorem orderedEdgeVertexSet_card_le_pred_of_not_matching
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k)
    (hoverlap : ¬edges.IsMatching) :
    (orderedEdgeVertexSet edges).card ≤ 2 * k - 1 := by
  classical
  have hle := orderedEdgeVertexSet_card_le edges
  have hne : (orderedEdgeVertexSet edges).card ≠ 2 * k := by
    intro hcard
    have hinjOn : Set.InjOn (orderedEdgeEndpointMap edges)
        (Finset.univ : Finset (Fin k × Bool)) := by
      apply (Finset.card_image_iff.mp ?_)
      simpa [orderedEdgeVertexSet, Nat.mul_comm] using hcard
    apply hoverlap
    intro a b hab
    exact hinjOn (by simp) (by simp) hab
  omega

/-- Lean-friendly oriented representation of an ordered matching.  There are
two endpoint orientations per edge. -/
abbrev OrientedOrderedMatching (p k : ℕ) :=
  (Fin k × Bool) ↪ Fin p

/-- Exact canonical oriented-matching count `(p)_(2k)`. -/
theorem card_orientedOrderedMatching (p k : ℕ) :
    Fintype.card (OrientedOrderedMatching p k) =
      p.descFactorial (2 * k) := by
  rw [Fintype.card_embedding_eq]
  simp [Nat.mul_comm]

/-- The `2^k` independent choices of endpoint orientation attached to `k`
unordered ordered edges. -/
abbrev MatchingOrientations (k : ℕ) := Fin k → Bool

theorem card_matchingOrientations (k : ℕ) :
    Fintype.card (MatchingOrientations k) = 2 ^ k := by
  simp [MatchingOrientations]

/-- General counting identity behind a falling factorial: `(s.card)_k` is
the number of ordered embeddings of `Fin k` into the active finite set `s`. -/
theorem descFactorial_card_eq_card_orderedSelections
    { α : Type* } [DecidableEq α] (s : Finset α) (k : ℕ) :
    s.card.descFactorial k = Fintype.card (Fin k ↪ ↑s) := by
  simpa using (Fintype.card_embedding_eq ( α := Fin k) ( β := ↑s)).symm

/-! ## Spanning-forest domination -/

/-- Intersection of a finite family of events. -/
def finiteIntersectionEvent
    { Ω ι : Type* } (edges : Finset ι) (event : ι → Set Ω) : Set Ω :=
  { ω | ∀ e ∈ edges, ω ∈ event e }

/-- Adding graph edges can only shrink the joint event. -/
theorem finiteIntersectionEvent_anti
    { Ω ι : Type* } {forest graph : Finset ι} (event : ι → Set Ω)
    (hsub : forest ⊆ graph) :
    finiteIntersectionEvent graph event ⊆ finiteIntersectionEvent forest event := by
  intro ω hω e he
  exact hω e (hsub he)

/-- A graph exceedance probability is bounded by the probability for any
chosen spanning-forest subset. -/
theorem measure_finiteIntersectionEvent_le_of_forest_subset
    { Ω ι : Type* } [MeasurableSpace Ω]
    ( μ : Measure Ω) {forest graph : Finset ι} (event : ι → Set Ω)
    (hsub : forest ⊆ graph) :
    μ (finiteIntersectionEvent graph event) ≤
      μ (finiteIntersectionEvent forest event) :=
  measure_mono (finiteIntersectionEvent_anti event hsub)

/-- Spanning-forest probability bound in the exponent form used in the
overlap argument.  The hypothesis `hforestLaw` is supplied by
`OrderedForestIndependence`; the conclusion does not assume independence on
the additional cycle edges. -/
theorem measure_graphEvent_le_spanningForest_power
    { Ω ι : Type* } [MeasurableSpace Ω]
    ( μ : Measure Ω) {forest graph : Finset ι} (event : ι → Set Ω)
    (q : ENNReal) (v c : ℕ)
    (hsub : forest ⊆ graph)
    (hcard : forest.card = v - c)
    (hforestLaw : μ (finiteIntersectionEvent forest event) = q ^ forest.card) :
    μ (finiteIntersectionEvent graph event) ≤ q ^ (v - c) := by
  calc
    μ (finiteIntersectionEvent graph event) ≤
        μ (finiteIntersectionEvent forest event) :=
      measure_finiteIntersectionEvent_le_of_forest_subset μ event hsub
    _ = q ^ forest.card := hforestLaw
    _ = q ^ (v - c) := by rw [hcard]

/-! ## Reduction of overlap sums to deterministic graph counts -/

/-- A weighted finite sum is bounded by graph-type fiber cardinalities times
a uniform bound for each type.  This is the exact finite reduction used after
the spanning-forest probability inequality. -/
theorem sum_le_graphType_fiberBound
    { τ γ : Type* } [DecidableEq τ] [DecidableEq γ]
    (configurations : Finset τ) (types : Finset γ)
    (graphType : τ → γ) (typeBound : γ → ℝ)
    (configurationWeight : τ → ℝ)
    (hmaps : ∀ t ∈ configurations, graphType t ∈ types)
    (hbound : ∀ t ∈ configurations,
      configurationWeight t ≤ typeBound (graphType t)) :
    ∑ t ∈ configurations, configurationWeight t ≤
      ∑ g ∈ types,
        ((configurations.filter fun t ↦ graphType t = g).card : ℝ) *
          typeBound g := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro g hg
  have hfiber : ∀ t ∈ configurations.filter (fun t ↦ graphType t = g),
      configurationWeight t ≤ typeBound g := by
    intro t ht
    have htconfig : t ∈ configurations := (Finset.mem_filter.mp ht).1
    have htype : graphType t = g := (Finset.mem_filter.mp ht).2
    simpa [htype] using hbound t htconfig
  calc
    ∑ t ∈ configurations.filter (fun t ↦ graphType t = g),
        configurationWeight t ≤
      (configurations.filter (fun t ↦ graphType t = g)).card • typeBound g :=
        Finset.sum_le_card_nsmul _ _ _ hfiber
    _ = ((configurations.filter fun t ↦ graphType t = g).card : ℝ) *
          typeBound g := by simp

/-- Specialization of the preceding reduction to the nonmatching part of the
ordered edge tuples.  Supplying deterministic fiber counts and a
spanning-forest bound for each graph type is now sufficient to control the
entire overlap contribution. -/
theorem overlapContribution_le_graphType_fiberBound
    { γ : Type* } [DecidableEq γ]
    (p k : ℕ) (types : Finset γ)
    (graphType : OrderedDistinctEdgeTuple p k → γ)
    (typeBound : γ → ℝ)
    (configurationWeight : OrderedDistinctEdgeTuple p k → ℝ)
    (hmaps : ∀ t ∈ orderedOverlapTuples p k, graphType t ∈ types)
    (hbound : ∀ t ∈ orderedOverlapTuples p k,
      configurationWeight t ≤ typeBound (graphType t)) :
    ∑ t ∈ orderedOverlapTuples p k, configurationWeight t ≤
      ∑ g ∈ types,
        (((orderedOverlapTuples p k).filter fun t ↦ graphType t = g).card : ℝ) *
          typeBound g := by
  classical
  exact sum_le_graphType_fiberBound
    (orderedOverlapTuples p k) types graphType typeBound configurationWeight
    hmaps hbound

end

end LogdetLean.Coherence
