import LogdetLean.Coherence.OrderedForestCertificate
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic
/-!
# The finite graph carried by an ordered edge tuple

This module translates the endpoint-map combinatorics into mathlib's
`SimpleGraph` language.  The graph has exactly the tuple's distinct edges,
and its support is exactly `orderedEdgeVertexSet`.
-/

namespace LogdetLean.Coherence

noncomputable section

open SimpleGraph

/-- Forget the canonical orientation of a correlation edge. -/
def correlationEdgeToSym2 {p : ℕ} (e : CorrelationEdge p) : Sym2 (Fin p) :=
  s(e.1.1, e.1.2)

theorem correlationEdgeToSym2_injective {p : ℕ} :
    Function.Injective (correlationEdgeToSym2 (p := p)) := by
  intro e f hef
  apply Subtype.ext
  rcases Sym2.eq_iff.mp hef with h | h
  · exact Prod.ext h.1 h.2
  · exfalso
    have he : e.1.1 < e.1.2 := e.2
    have hf : f.1.1 < f.1.2 := f.2
    rw [h.1, h.2] at he
    omega

/-- The unoriented-edge embedding induced by an ordered distinct tuple. -/
def orderedEdgeSym2Embedding {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) : Fin k ↪ Sym2 (Fin p) :=
  edges.trans
    ⟨correlationEdgeToSym2, correlationEdgeToSym2_injective⟩

@[simp]
theorem orderedEdgeSym2Embedding_apply {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) (j : Fin k) :
    orderedEdgeSym2Embedding edges j =
      s((edges j).1.1, (edges j).1.2) := rfl

/-- The finite unoriented edge set of a tuple. -/
def orderedEdgeSym2Finset {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) : Finset (Sym2 (Fin p)) :=
  Finset.univ.map (orderedEdgeSym2Embedding edges)

@[simp]
theorem mem_orderedEdgeSym2Finset {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) (e : Sym2 (Fin p)) :
    e ∈ orderedEdgeSym2Finset edges ↔
      ∃ j : Fin k, s((edges j).1.1, (edges j).1.2) = e := by
  simp [orderedEdgeSym2Finset]

@[simp]
theorem card_orderedEdgeSym2Finset {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) :
    (orderedEdgeSym2Finset edges).card = k := by
  simp [orderedEdgeSym2Finset]

/-- The simple graph whose edge set is the tuple. -/
def orderedEdgeTupleGraph {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) : SimpleGraph (Fin p) :=
  SimpleGraph.fromEdgeSet (orderedEdgeSym2Finset edges : Set (Sym2 (Fin p)))

instance orderedEdgeTupleGraph_adj_decidable {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) :
    DecidableRel (orderedEdgeTupleGraph edges).Adj := by
  unfold orderedEdgeTupleGraph
  infer_instance

@[simp]
theorem orderedEdgeTupleGraph_adj {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) (u v : Fin p) :
    (orderedEdgeTupleGraph edges).Adj u v ↔
      ∃ j : Fin k,
        (u = (edges j).1.1 ∧ v = (edges j).1.2) ∨
          (u = (edges j).1.2 ∧ v = (edges j).1.1) := by
  simp only [orderedEdgeTupleGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq, Finset.mem_coe, mem_orderedEdgeSym2Finset,
    Sym2.eq_iff]
  constructor
  · rintro ⟨⟨j, h | h⟩, _hne⟩
    · exact ⟨j, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
    · exact ⟨j, Or.inr ⟨h.2.symm, h.1.symm⟩⟩
  · rintro ⟨j, h | h⟩
    · refine ⟨⟨j, Or.inl ⟨h.1.symm, h.2.symm⟩⟩, ?_⟩
      rw [h.1, h.2]
      exact ne_of_lt (edges j).2
    · refine ⟨⟨j, Or.inr ⟨h.2.symm, h.1.symm⟩⟩, ?_⟩
      rw [h.1, h.2]
      exact ne_of_gt (edges j).2

theorem orderedEdgeTupleGraph_support {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) :
    (orderedEdgeTupleGraph edges).support =
      (orderedEdgeVertexSet edges : Set (Fin p)) := by
  ext u
  simp only [SimpleGraph.mem_support, orderedEdgeTupleGraph_adj,
    Finset.mem_coe]
  constructor
  · rintro ⟨v, j, h | h⟩
    · rw [h.1]
      simp only [orderedEdgeVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨(j, false), by
        simp [orderedEdgeEndpointMap, correlationEdgeEndpoint]⟩
    · rw [h.1]
      simp only [orderedEdgeVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨(j, true), by
        simp [orderedEdgeEndpointMap, correlationEdgeEndpoint]⟩
  · intro hu
    simp only [orderedEdgeVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hu
    obtain ⟨⟨j, side⟩, rfl⟩ := hu
    cases side
    · exact ⟨(edges j).1.2, j, Or.inl ⟨by
        simp [orderedEdgeEndpointMap, correlationEdgeEndpoint], by rfl⟩⟩
    · exact ⟨(edges j).1.1, j, Or.inr ⟨by
        simp [orderedEdgeEndpointMap, correlationEdgeEndpoint], by rfl⟩⟩

instance orderedEdgeTupleGraph_edgeSet_fintype {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) :
    Fintype (orderedEdgeTupleGraph edges).edgeSet := by
  unfold orderedEdgeTupleGraph
  infer_instance

@[simp]
theorem orderedEdgeTupleGraph_edgeFinset {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) :
    (orderedEdgeTupleGraph edges).edgeFinset = orderedEdgeSym2Finset edges := by
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset, orderedEdgeTupleGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun h ↦ h.1
  · intro he
    refine ⟨he, ?_⟩
    obtain ⟨j, hj⟩ := (mem_orderedEdgeSym2Finset edges e).mp he
    rw [← hj]
    simpa [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] using
      (ne_of_lt (edges j).2)

@[simp]
theorem card_orderedEdgeTupleGraph_edgeFinset {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) :
    (orderedEdgeTupleGraph edges).edgeFinset.card = k := by
  rw [orderedEdgeTupleGraph_edgeFinset,
    card_orderedEdgeSym2Finset]

/-! ## A nonmatching tuple contains a genuine two-edge overlap -/

/-- The endpoint opposite a chosen Boolean side of an edge. -/
def correlationEdgeOtherEndpoint {p : ℕ}
    (e : CorrelationEdge p) (side : Bool) : Fin p :=
  correlationEdgeEndpoint e (!side)

theorem correlationEdgeEndpoint_ne_other {p : ℕ}
    (e : CorrelationEdge p) (side : Bool) :
    correlationEdgeEndpoint e side ≠ correlationEdgeOtherEndpoint e side := by
  cases side <;>
    simp [correlationEdgeEndpoint, correlationEdgeOtherEndpoint,
      ne_of_lt e.2, ne_of_gt e.2]

/-- Failure of endpoint injectivity gives two distinct tuple edges, a shared
vertex, and two distinct opposite endpoints. -/
theorem exists_sharedVertex_two_distinct_neighbors_of_not_matching
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k)
    (hoverlap : ¬edges.IsMatching) :
    ∃ (u v w : Fin p), v ≠ w ∧
      (orderedEdgeTupleGraph edges).Adj u v ∧
      (orderedEdgeTupleGraph edges).Adj u w := by
  rw [OrderedDistinctEdgeTuple.IsMatching,
    Function.not_injective_iff] at hoverlap
  obtain ⟨a, b, hab, habne⟩ := hoverlap
  rcases a with ⟨ia, sa⟩
  rcases b with ⟨ib, sb⟩
  have hij : ia ≠ ib := by
    intro hij
    subst ib
    cases sa <;> cases sb <;>
      simp [orderedEdgeEndpointMap, correlationEdgeEndpoint] at hab habne
    · exact (edges ia).2.ne hab
    · exact (edges ia).2.ne' hab
  let u := orderedEdgeEndpointMap edges (ia, sa)
  let v := correlationEdgeOtherEndpoint (edges ia) sa
  let w := correlationEdgeOtherEndpoint (edges ib) sb
  have huv : (orderedEdgeTupleGraph edges).Adj u v := by
    cases sa
    · exact (orderedEdgeTupleGraph_adj edges u v).2
        ⟨ia, Or.inl ⟨by
          simp [u, orderedEdgeEndpointMap, correlationEdgeEndpoint], by
          simp [v, correlationEdgeOtherEndpoint,
            correlationEdgeEndpoint]⟩⟩
    · exact (orderedEdgeTupleGraph_adj edges u v).2
        ⟨ia, Or.inr ⟨by
          simp [u, orderedEdgeEndpointMap, correlationEdgeEndpoint], by
          simp [v, correlationEdgeOtherEndpoint,
            correlationEdgeEndpoint]⟩⟩
  have huw : (orderedEdgeTupleGraph edges).Adj u w := by
    cases sb
    · exact (orderedEdgeTupleGraph_adj edges u w).2
        ⟨ib, Or.inl ⟨by
          simpa [u, orderedEdgeEndpointMap, correlationEdgeEndpoint] using
            hab, by
          simp [w, correlationEdgeOtherEndpoint,
            correlationEdgeEndpoint]⟩⟩
    · exact (orderedEdgeTupleGraph_adj edges u w).2
        ⟨ib, Or.inr ⟨by
          simpa [u, orderedEdgeEndpointMap, correlationEdgeEndpoint] using
            hab, by
          simp [w, correlationEdgeOtherEndpoint,
            correlationEdgeEndpoint]⟩⟩
  refine ⟨u, v, w, ?_, huv, huw⟩
  intro hvw
  apply hij
  apply edges.injective
  apply Subtype.ext
  have hia := (edges ia).2
  have hib := (edges ib).2
  cases sa <;> cases sb <;>
    simp [u, v, w, orderedEdgeEndpointMap, correlationEdgeEndpoint,
      correlationEdgeOtherEndpoint] at hab hvw hia hib ⊢
  · exact Prod.ext hab hvw
  · omega
  · omega
  · exact Prod.ext hvw hab

theorem exists_degree_two_of_not_matching
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k)
    (hoverlap : ¬edges.IsMatching) :
    ∃ u : Fin p, 2 ≤ (orderedEdgeTupleGraph edges).degree u := by
  obtain ⟨u, v, w, hvw, huv, huw⟩ :=
    exists_sharedVertex_two_distinct_neighbors_of_not_matching edges hoverlap
  refine ⟨u, ?_⟩
  change 2 ≤ ((orderedEdgeTupleGraph edges).neighborFinset u).card
  rw [show 2 = ({v, w} : Finset (Fin p)).card by simp [hvw]]
  apply Finset.card_le_card
  intro x hx
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact huv
  · exact huw

/-! ## Spanning forests preserve the used vertices and the overlap saving -/

theorem support_eq_of_le_of_reachable_eq
    {V : Type*} {F G : SimpleGraph V}
    (hFG : F ≤ G) (hreach : F.Reachable = G.Reachable) :
    F.support = G.support := by
  apply Set.Subset.antisymm (SimpleGraph.support_mono hFG)
  intro u hu
  obtain ⟨v, huv⟩ := G.mem_support.mp hu
  apply SimpleGraph.mem_support_of_reachable (G.ne_of_adj huv)
  rw [hreach]
  exact huv.reachable

/-- If a graph contains a vertex with two distinct neighbors, then every
acyclic subgraph with the same reachability relation also contains such a
vertex.  Equivalently, the nontrivial connected component cannot collapse to
a matching. -/
theorem exists_two_distinct_neighbors_of_spanningForest
    {p : ℕ} {F G : SimpleGraph (Fin p)}
    (hFG : F ≤ G) (hacyclic : F.IsAcyclic)
    (hreach : F.Reachable = G.Reachable)
    {u v w : Fin p} (hvw : v ≠ w)
    (huv : G.Adj u v) (huw : G.Adj u w) :
    ∃ (a b c : Fin p), b ≠ c ∧ F.Adj a b ∧ F.Adj a c := by
  classical
  by_contra hnone
  have hunique : ∀ ⦃a b c : Fin p⦄,
      F.Adj a b → F.Adj a c → b = c := by
    intro a b c hab hac
    by_contra hbc
    exact hnone ⟨a, b, c, hbc, hab, hac⟩
  have hFuv : F.Reachable u v := by
    rw [hreach]
    exact huv.reachable
  have hFuw : F.Reachable u w := by
    rw [hreach]
    exact huw.reachable
  let C : F.ConnectedComponent := F.connectedComponentMk u
  have huC : u ∈ C := by
    simpa [C] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        (G := F) (v := u))
  have hvC : v ∈ C := by
    change F.connectedComponentMk v = C
    simpa [C] using (SimpleGraph.ConnectedComponent.sound hFuv).symm
  have hwC : w ∈ C := by
    change F.connectedComponentMk w = C
    simpa [C] using (SimpleGraph.ConnectedComponent.sound hFuw).symm
  let uc : C := ⟨u, huC⟩
  let vc : C := ⟨v, hvC⟩
  let wc : C := ⟨w, hwC⟩
  have huvne : u ≠ v := G.ne_of_adj huv
  have huwne : u ≠ w := G.ne_of_adj huw
  have hucvc : uc ≠ vc := by
    intro h
    exact huvne (congrArg Subtype.val h)
  have hucwc : uc ≠ wc := by
    intro h
    exact huwne (congrArg Subtype.val h)
  have hvcwc : vc ≠ wc := by
    intro h
    exact hvw (congrArg Subtype.val h)
  have hcardC : 3 ≤ Fintype.card C := by
    have hthree : ({uc, vc, wc} : Finset C).card = 3 := by
      simp [hucvc, hucwc, hvcwc]
    calc
      3 = ({uc, vc, wc} : Finset C).card := hthree.symm
      _ ≤ (Finset.univ : Finset C).card :=
        Finset.card_le_card (by simp)
      _ = Fintype.card C := Finset.card_univ
  let H : SimpleGraph C := C.toSimpleGraph
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have htree : H.IsTree := by
    exact hacyclic.isTree_connectedComponent C
  have hdeg : ∀ x : C, H.degree x ≤ 1 := by
    intro x
    by_contra hx
    have hcard : 1 < (H.neighborFinset x).card := by
      change ¬(H.neighborFinset x).card ≤ 1 at hx
      omega
    obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp hcard
    have hxy : H.Adj x y := by simpa using hy
    have hxz : H.Adj x z := by simpa using hz
    apply hyz
    apply Subtype.ext
    apply hunique
    · exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C x.2 y.2).mp hxy
    · exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C x.2 z.2).mp hxz
  have hsumle : (∑ x : C, H.degree x) ≤ ∑ _x : C, 1 := by
    exact Finset.sum_le_sum fun x _hx ↦ hdeg x
  have hdegreeSum := H.sum_degrees_eq_twice_card_edges
  have hedgeCard := htree.card_edgeFinset
  rw [hdegreeSum] at hsumle
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one] at hsumle
  omega

/-- Every nonmatching tuple has a spanning forest which still contains a
two-edge overlap. -/
theorem exists_spanningForest_with_overlap
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k)
    (hoverlap : ¬edges.IsMatching) :
    ∃ F : SimpleGraph (Fin p),
      F ≤ orderedEdgeTupleGraph edges ∧
      F.IsAcyclic ∧
      F.Reachable = (orderedEdgeTupleGraph edges).Reachable ∧
      ∃ (a b c : Fin p), b ≠ c ∧ F.Adj a b ∧ F.Adj a c := by
  obtain ⟨F, hFG, hacyclic, hreach⟩ :=
    (orderedEdgeTupleGraph edges).exists_isAcyclic_reachable_eq_le
  obtain ⟨u, v, w, hvw, huv, huw⟩ :=
    exists_sharedVertex_two_distinct_neighbors_of_not_matching edges hoverlap
  exact ⟨F, hFG, hacyclic, hreach,
    exists_two_distinct_neighbors_of_spanningForest
      hFG hacyclic hreach hvw huv huw⟩

/-- A finite graph with no isolated vertices in its support and with one
vertex incident to two distinct edges has strictly more than half as many
edges as support vertices.  This is just the handshake identity. -/
theorem support_card_div_two_add_one_le_edge_card_of_two_neighbors
    {V : Type*} [Fintype V] (F : SimpleGraph V)
    {a b c : V} (hbc : b ≠ c) (hab : F.Adj a b) (hac : F.Adj a c) :
    F.support.ncard / 2 + 1 ≤ Nat.card F.edgeSet := by
  classical
  letI : DecidableRel F.Adj := Classical.decRel F.Adj
  let supportFinset : Finset V := F.support.toFinset
  have haSupport : a ∈ supportFinset := by
    simp [supportFinset, hab.mem_support_left]
  have hdegLower : ∀ x ∈ supportFinset, 1 ≤ F.degree x := by
    intro x hx
    exact (F.degree_pos_iff_mem_support x).2 (by
      simpa [supportFinset] using hx)
  have hdegA : 1 < F.degree a := by
    change 1 < (F.neighborFinset a).card
    rw [Finset.one_lt_card]
    exact ⟨b, by simpa using hab, c, by simpa using hac, hbc⟩
  have hsumStrict : supportFinset.card <
      ∑ x ∈ supportFinset, F.degree x := by
    have h := Finset.sum_lt_sum
      (s := supportFinset)
      (f := fun _x : V ↦ 1)
      (g := fun x ↦ F.degree x)
      hdegLower ⟨a, haSupport, hdegA⟩
    simpa using h
  have hsumEq := F.sum_degrees_support_eq_twice_card_edges
  change F.support.toFinset.card <
      ∑ x ∈ F.support.toFinset, F.degree x at hsumStrict
  rw [hsumEq] at hsumStrict
  have hncard : F.support.ncard = F.support.toFinset.card :=
    Set.ncard_eq_toFinset_card' F.support
  have hsumStrictN : F.support.ncard < 2 * F.edgeFinset.card := by
    rw [hncard]
    exact hsumStrict
  have hbound : F.support.ncard / 2 + 1 ≤
      F.edgeFinset.card := by
    omega
  have hedgeCard : Nat.card F.edgeSet = F.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact SimpleGraph.card_edgeSet
  rw [hedgeCard]
  exact hbound

/-- Quantitative spanning-forest extraction for an overlapping tuple.  The
forest uses exactly the tuple's support and has at least
`support.card / 2 + 1` edges. -/
theorem exists_large_spanningForest_of_not_matching
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k)
    (hoverlap : ¬edges.IsMatching) :
    ∃ F : SimpleGraph (Fin p),
      F ≤ orderedEdgeTupleGraph edges ∧
      F.IsAcyclic ∧
      F.Reachable = (orderedEdgeTupleGraph edges).Reachable ∧
      (orderedEdgeVertexSet edges).card / 2 + 1 ≤ Nat.card F.edgeSet := by
  obtain ⟨F, hFG, hacyclic, hreach, a, b, c, hbc, hab, hac⟩ :=
    exists_spanningForest_with_overlap edges hoverlap
  have hsupport := support_eq_of_le_of_reachable_eq hFG hreach
  have hcard := support_card_div_two_add_one_le_edge_card_of_two_neighbors
    F hbc hab hac
  have hsuppCard : F.support.ncard = (orderedEdgeVertexSet edges).card := by
    rw [hsupport, orderedEdgeTupleGraph_support]
    exact Set.ncard_coe_finset _
  rw [hsuppCard] at hcard
  exact ⟨F, hFG, hacyclic, hreach, hcard⟩

end

end LogdetLean.Coherence
