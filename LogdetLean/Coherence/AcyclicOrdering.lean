import LogdetLean.Coherence.OverlapGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic
/-!
# Ordering a finite acyclic graph from roots to leaves

For every connected component choose the quotient representative supplied by
`Quot.out`, call it the root, and order vertices lexicographically by

`(distance from the component root, original vertex label)`.

Every forest edge joins consecutive distance layers.  Hence its endpoint on
the smaller layer occurs earlier.  The rest of the file packages this order
as a permutation of `Fin p` and builds an `OrderedForest`.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set SimpleGraph

/-- A canonical representative of the connected component of `v`. -/
def graphComponentRoot {V : Type*} (G : SimpleGraph V) (v : V) : V :=
  (G.connectedComponentMk v).out

theorem graphComponentRoot_mem {V : Type*} (G : SimpleGraph V) (v : V) :
    graphComponentRoot G v ∈ (G.connectedComponentMk v).supp := by
  change G.connectedComponentMk (G.connectedComponentMk v).out =
    G.connectedComponentMk v
  exact Quot.out_eq _

theorem graphComponentRoot_reachable {V : Type*}
    (G : SimpleGraph V) (v : V) :
    G.Reachable (graphComponentRoot G v) v := by
  exact (G.connectedComponentMk v).reachable_of_mem_supp
    (graphComponentRoot_mem G v)
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem

theorem graphComponentRoot_eq_of_adj {V : Type*}
    {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    graphComponentRoot G u = graphComponentRoot G v := by
  unfold graphComponentRoot
  rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv]

/-- Distance from the canonical root of the vertex's component. -/
def graphRootDepth {V : Type*} (G : SimpleGraph V) (v : V) : ℕ :=
  G.dist (graphComponentRoot G v) v

theorem graphRootDepth_adjacent_layers {V : Type*}
    {G : SimpleGraph V} (hacyclic : G.IsAcyclic)
    {u v : V} (huv : G.Adj u v) :
    graphRootDepth G u = graphRootDepth G v + 1 ∨
      graphRootDepth G v = graphRootDepth G u + 1 := by
  have hroot := graphComponentRoot_eq_of_adj huv
  unfold graphRootDepth
  rw [hroot]
  exact hacyclic.dist_eq_dist_add_one_of_adj_of_reachable
    (graphComponentRoot G v) huv
    (by simpa [hroot] using graphComponentRoot_reachable G u)

/-- Every positive-depth vertex of an acyclic graph has a unique neighbor
one layer closer to its component root. -/
theorem existsUnique_adj_graphRootDepth_lt {V : Type*}
    {G : SimpleGraph V} (hacyclic : G.IsAcyclic) (v : V)
    (hv : 0 < graphRootDepth G v) :
    ∃! u : V, G.Adj u v ∧ graphRootDepth G u < graphRootDepth G v := by
  let r : V := graphComponentRoot G v
  have hrv : G.Reachable r v := graphComponentRoot_reachable G v
  obtain ⟨q, hqPath, hqLength⟩ := hrv.exists_path_of_dist
  have hqNotNil : ¬q.Nil := by
    intro hnil
    have hzero : q.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
    have : graphRootDepth G v = 0 := by
      simpa [graphRootDepth, r] using hqLength.symm.trans hzero
    omega
  let u : V := q.penultimate
  have huv : G.Adj u v := q.adj_penultimate hqNotNil
  have hrootUV : graphComponentRoot G u = graphComponentRoot G v :=
    graphComponentRoot_eq_of_adj huv
  have hdistU : G.dist r u ≤ q.dropLast.length :=
    SimpleGraph.dist_le q.dropLast
  have hdepthU : graphRootDepth G u < graphRootDepth G v := by
    have hdrop : q.dropLast.length + 1 = q.length :=
      q.length_dropLast_add_one hqNotNil
    unfold graphRootDepth
    rw [hrootUV]
    change G.dist r u < G.dist r v
    omega
  refine ⟨u, ⟨huv, hdepthU⟩, ?_⟩
  intro w hw
  rcases hw with ⟨hwv, hdepthW⟩
  have hrootWU : graphComponentRoot G w = graphComponentRoot G v :=
    graphComponentRoot_eq_of_adj hwv
  have hrw : G.Reachable r w := by
    simpa [r, hrootWU] using graphComponentRoot_reachable G w
  obtain ⟨pw, hpwPath, hpwLength⟩ := hrw.exists_path_of_dist
  have hstepW : graphRootDepth G v = graphRootDepth G w + 1 := by
    rcases graphRootDepth_adjacent_layers hacyclic hwv with h | h
    · omega
    · exact h
  have hpwConcatLength : (pw.concat hwv).length = G.dist r v := by
    rw [pw.length_concat, hpwLength]
    simpa [graphRootDepth, r, hrootWU] using hstepW.symm
  have hpwConcatPath : (pw.concat hwv).IsPath :=
    (pw.concat hwv).isPath_of_length_eq_dist hpwConcatLength
  have hpathEq : (pw.concat hwv : G.Walk r v) = q := by
    have hpathSubtype :
        (⟨pw.concat hwv, hpwConcatPath⟩ : G.Path r v) =
          ⟨q, hqPath⟩ :=
      (hacyclic.subsingleton_path r v).elim _ _
    exact congrArg Subtype.val hpathSubtype
  have hpenultimate := congrArg SimpleGraph.Walk.penultimate hpathEq
  simpa [u] using hpenultimate

/-- Wrapper used solely to put the depth-first linear order on vertices
without replacing the ordinary numerical order on `Fin p`. -/
structure RootDepthVertex {p : ℕ} (G : SimpleGraph (Fin p)) where
  val : Fin p

def rootDepthVertexEquiv {p : ℕ} (G : SimpleGraph (Fin p)) :
    RootDepthVertex G ≃ Fin p where
  toFun := RootDepthVertex.val
  invFun v := ⟨v⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance rootDepthVertexFintype {p : ℕ} (G : SimpleGraph (Fin p)) :
    Fintype (RootDepthVertex G) :=
  Fintype.ofEquiv (Fin p) (rootDepthVertexEquiv G).symm

instance rootDepthVertexDecidableEq {p : ℕ} (G : SimpleGraph (Fin p)) :
    DecidableEq (RootDepthVertex G) :=
  (rootDepthVertexEquiv G).injective.decidableEq

def rootDepthVertexKey {p : ℕ} (G : SimpleGraph (Fin p))
    (v : RootDepthVertex G) : ℕ ×ₗ ℕ :=
  toLex (graphRootDepth G v.val, v.val.val)

theorem rootDepthVertexKey_injective {p : ℕ}
    (G : SimpleGraph (Fin p)) :
    Function.Injective (rootDepthVertexKey G) := by
  intro u v huv
  apply (rootDepthVertexEquiv G).injective
  apply Fin.ext
  exact congrArg (fun z : ℕ ×ₗ ℕ ↦ (ofLex z).2) huv

instance rootDepthVertexLinearOrder {p : ℕ}
    (G : SimpleGraph (Fin p)) : LinearOrder (RootDepthVertex G) :=
  LinearOrder.lift' (rootDepthVertexKey G)
    (rootDepthVertexKey_injective G)

@[simp]
theorem card_rootDepthVertex {p : ℕ} (G : SimpleGraph (Fin p)) :
    Fintype.card (RootDepthVertex G) = p := by
  rw [Fintype.card_congr (rootDepthVertexEquiv G)]
  simp

/-- The increasing enumeration of the depth-ordered wrapper. -/
def rootDepthOrderIso {p : ℕ} (G : SimpleGraph (Fin p)) :
    Fin p ≃o {v : RootDepthVertex G // v ∈ (Finset.univ : Finset (RootDepthVertex G))} :=
  Finset.orderIsoOfFin Finset.univ (by simp)

/-- Original vertex occupying a given root-depth rank. -/
def acyclicVertexOrder {p : ℕ} (G : SimpleGraph (Fin p)) :
    Equiv.Perm (Fin p) where
  toFun n := (rootDepthOrderIso G n).val.val
  invFun v := rootDepthOrderIso G |>.symm ⟨⟨v⟩, Finset.mem_univ _⟩
  left_inv n := by
    change (rootDepthOrderIso G).symm
      ⟨⟨(rootDepthOrderIso G n).val.val⟩, Finset.mem_univ _⟩ = n
    have hwrap :
        (⟨⟨(rootDepthOrderIso G n).val.val⟩, Finset.mem_univ _⟩ :
          {v : RootDepthVertex G //
            v ∈ (Finset.univ : Finset (RootDepthVertex G))}) =
          rootDepthOrderIso G n := by
      apply Subtype.ext
      rfl
    rw [hwrap, (rootDepthOrderIso G).symm_apply_apply]
  right_inv v := by
    have h := (rootDepthOrderIso G).apply_symm_apply
      (⟨⟨v⟩, Finset.mem_univ _⟩ :
        {x : RootDepthVertex G //
          x ∈ (Finset.univ : Finset (RootDepthVertex G))})
    exact congrArg (fun x ↦ x.val.val) h

@[simp]
theorem acyclicVertexOrder_apply {p : ℕ} (G : SimpleGraph (Fin p))
    (n : Fin p) :
    acyclicVertexOrder G n = (rootDepthOrderIso G n).val.val := rfl

/-- Strictly smaller root depth implies strictly smaller numerical rank. -/
theorem acyclicVertexOrder_symm_lt_of_depth_lt {p : ℕ}
    (G : SimpleGraph (Fin p)) {u v : Fin p}
    (huv : graphRootDepth G u < graphRootDepth G v) :
    (acyclicVertexOrder G).symm u < (acyclicVertexOrder G).symm v := by
  let uw : RootDepthVertex G := ⟨u⟩
  let vw : RootDepthVertex G := ⟨v⟩
  have hkey : rootDepthVertexKey G uw < rootDepthVertexKey G vw := by
    simp [rootDepthVertexKey, Prod.Lex.toLex_lt_toLex, uw, vw, huv]
  have hwrap : uw < vw := by
    exact hkey
  have hsub :
      (⟨uw, Finset.mem_univ _⟩ :
        {x : RootDepthVertex G // x ∈ (Finset.univ : Finset (RootDepthVertex G))}) <
      ⟨vw, Finset.mem_univ _⟩ := hwrap
  have hrank := (rootDepthOrderIso G).symm.lt_iff_lt.mpr hsub
  exact hrank

/-! ## The ordered parent forest -/

/-- The unique neighbor one layer closer to the component root. -/
def acyclicParentVertex {p : ℕ} (G : SimpleGraph (Fin p))
    (hacyclic : G.IsAcyclic) (v : Fin p)
    (hv : 0 < graphRootDepth G v) : Fin p :=
  Classical.choose (existsUnique_adj_graphRootDepth_lt hacyclic v hv)

theorem acyclicParentVertex_adj {p : ℕ} (G : SimpleGraph (Fin p))
    (hacyclic : G.IsAcyclic) (v : Fin p)
    (hv : 0 < graphRootDepth G v) :
    G.Adj (acyclicParentVertex G hacyclic v hv) v :=
  (Classical.choose_spec
    (existsUnique_adj_graphRootDepth_lt hacyclic v hv)).1.1

theorem acyclicParentVertex_depth_lt {p : ℕ}
    (G : SimpleGraph (Fin p)) (hacyclic : G.IsAcyclic) (v : Fin p)
    (hv : 0 < graphRootDepth G v) :
    graphRootDepth G (acyclicParentVertex G hacyclic v hv) <
      graphRootDepth G v :=
  (Classical.choose_spec
    (existsUnique_adj_graphRootDepth_lt hacyclic v hv)).1.2

/-- Rank of the parent of a positive-depth vertex in the root-depth order. -/
def acyclicOrderedParentRank {p : ℕ} (G : SimpleGraph (Fin p))
    (hacyclic : G.IsAcyclic) (n : Fin p)
    (hn : 0 < graphRootDepth G (acyclicVertexOrder G n)) : Fin n.val :=
  ⟨((acyclicVertexOrder G).symm
      (acyclicParentVertex G hacyclic (acyclicVertexOrder G n) hn)).val,
    by
      have hlt := acyclicVertexOrder_symm_lt_of_depth_lt G
        (acyclicParentVertex_depth_lt G hacyclic
          (acyclicVertexOrder G n) hn)
      have hrank : (acyclicVertexOrder G).symm
          (acyclicVertexOrder G n) = n :=
        (acyclicVertexOrder G).symm_apply_apply n
      rw [hrank] at hlt
      exact hlt⟩

theorem acyclicOrderedParentRank_vertex {p : ℕ}
    (G : SimpleGraph (Fin p)) (hacyclic : G.IsAcyclic) (n : Fin p)
    (hn : 0 < graphRootDepth G (acyclicVertexOrder G n)) :
    acyclicVertexOrder G
        (orderedForestParentRank n
          (acyclicOrderedParentRank G hacyclic n hn)) =
      acyclicParentVertex G hacyclic (acyclicVertexOrder G n) hn := by
  apply (acyclicVertexOrder G).injective
  apply Fin.ext
  simp [orderedForestParentRank, acyclicOrderedParentRank]

/-- An arbitrary finite acyclic graph, relabeled from component roots toward
leaves, as an `OrderedForest`.  Vertices outside the finite graph order never
arise in the first `p` stages and are declared roots. -/
def acyclicOrderedForest {p : ℕ} (G : SimpleGraph (Fin p))
    (hacyclic : G.IsAcyclic) : OrderedForest where
  parent n := if hn : n < p then
      let v := acyclicVertexOrder G ⟨n, hn⟩
      if hv : 0 < graphRootDepth G v then
        some (acyclicOrderedParentRank G hacyclic ⟨n, hn⟩ hv)
      else none
    else none

theorem acyclicOrderedForest_parent_eq_some {p : ℕ}
    (G : SimpleGraph (Fin p)) (hacyclic : G.IsAcyclic) (n : Fin p)
    (hn : 0 < graphRootDepth G (acyclicVertexOrder G n)) :
    (acyclicOrderedForest G hacyclic).parent n.val =
      some (acyclicOrderedParentRank G hacyclic n hn) := by
  simp only [acyclicOrderedForest, n.isLt, dite_true]
  split
  · congr
  · contradiction

theorem acyclicOrderedForest_parent_adj {p : ℕ}
    (G : SimpleGraph (Fin p)) (hacyclic : G.IsAcyclic)
    (n : Fin p) (i : Fin n.val)
    (hparent : (acyclicOrderedForest G hacyclic).parent n.val = some i) :
    G.Adj
      (acyclicVertexOrder G (orderedForestParentRank n i))
      (acyclicVertexOrder G n) := by
  have hnpos : 0 < graphRootDepth G (acyclicVertexOrder G n) := by
    by_contra hnpos
    simp only [acyclicOrderedForest, n.isLt, dite_true] at hparent
    split at hparent
    · contradiction
    · simp at hparent
  have heq := (acyclicOrderedForest_parent_eq_some G hacyclic n hnpos).symm.trans
    hparent
  have hi : acyclicOrderedParentRank G hacyclic n hnpos = i :=
    Option.some.inj heq
  rw [← hi]
  rw [acyclicOrderedParentRank_vertex]
  exact acyclicParentVertex_adj G hacyclic (acyclicVertexOrder G n) hnpos

/-! ## Every original forest edge occurs at its higher endpoint -/

/-- The root-depth rank of the later endpoint of an unordered edge.  Taking
the maximum rank makes this definition symmetric before acyclicity is used. -/
def acyclicEdgeChildRank {p : ℕ} (G : SimpleGraph (Fin p))
    (e : Sym2 (Fin p)) : Fin p :=
  Sym2.lift
    ⟨fun u v ↦ max ((acyclicVertexOrder G).symm u)
        ((acyclicVertexOrder G).symm v),
      fun u v ↦ max_comm _ _⟩ e

@[simp]
theorem acyclicEdgeChildRank_mk {p : ℕ} (G : SimpleGraph (Fin p))
    (u v : Fin p) :
    acyclicEdgeChildRank G s(u, v) =
      max ((acyclicVertexOrder G).symm u)
        ((acyclicVertexOrder G).symm v) := by
  simp [acyclicEdgeChildRank]

theorem acyclicEdgeChildRank_eq_right_of_depth_lt {p : ℕ}
    (G : SimpleGraph (Fin p)) {u v : Fin p}
    (huv : graphRootDepth G u < graphRootDepth G v) :
    acyclicEdgeChildRank G s(u, v) = (acyclicVertexOrder G).symm v := by
  rw [acyclicEdgeChildRank_mk]
  exact max_eq_right
    (acyclicVertexOrder_symm_lt_of_depth_lt G huv).le

theorem acyclicEdgeChildRank_eq_left_of_depth_lt {p : ℕ}
    (G : SimpleGraph (Fin p)) {u v : Fin p}
    (hvu : graphRootDepth G v < graphRootDepth G u) :
    acyclicEdgeChildRank G s(u, v) = (acyclicVertexOrder G).symm u := by
  rw [acyclicEdgeChildRank_mk]
  exact max_eq_left
    (acyclicVertexOrder_symm_lt_of_depth_lt G hvu).le

/-- Every edge of an acyclic graph is exactly the parent edge attached to
its later root-depth rank.  This is the finite reindexing fact used both for
cardinality and for the tuple certificate. -/
theorem exists_orderedParent_for_edge {p : ℕ}
    (G : SimpleGraph (Fin p)) (hacyclic : G.IsAcyclic) (e : G.edgeSet) :
    ∃ i : Fin (acyclicEdgeChildRank G e.1).val,
      (acyclicOrderedForest G hacyclic).parent
          (acyclicEdgeChildRank G e.1).val = some i ∧
        e.1 = s(
          acyclicVertexOrder G
            (orderedForestParentRank (acyclicEdgeChildRank G e.1) i),
          acyclicVertexOrder G (acyclicEdgeChildRank G e.1)) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      change G.Adj u v at he
      rcases graphRootDepth_adjacent_layers hacyclic he with huv | hvu
      · have hdepth : graphRootDepth G v < graphRootDepth G u := by omega
        rw [acyclicEdgeChildRank_eq_left_of_depth_lt G hdepth]
        let n : Fin p := (acyclicVertexOrder G).symm u
        have horder : acyclicVertexOrder G n = u :=
          (acyclicVertexOrder G).apply_symm_apply u
        have hnpos : 0 < graphRootDepth G (acyclicVertexOrder G n) := by
          rw [horder]
          omega
        let i : Fin n.val := acyclicOrderedParentRank G hacyclic n hnpos
        refine ⟨i, acyclicOrderedForest_parent_eq_some G hacyclic n hnpos, ?_⟩
        have hvparent : v =
            acyclicParentVertex G hacyclic (acyclicVertexOrder G n) hnpos := by
          exact (Classical.choose_spec
            (existsUnique_adj_graphRootDepth_lt hacyclic
              (acyclicVertexOrder G n) hnpos)).2 v ⟨by simpa [horder] using he.symm,
                by simpa [horder] using hdepth⟩
        have hparentEndpoint :
            acyclicVertexOrder G (orderedForestParentRank n i) = v := by
          dsimp [i]
          change acyclicVertexOrder G
              (orderedForestParentRank n
                (acyclicOrderedParentRank G hacyclic n hnpos)) = v
          exact (acyclicOrderedParentRank_vertex G hacyclic n hnpos).trans
            hvparent.symm
        change s(u, v) =
          s(acyclicVertexOrder G (orderedForestParentRank n i),
            acyclicVertexOrder G n)
        exact Sym2.eq_iff.mpr
          (Or.inr ⟨horder.symm, hparentEndpoint.symm⟩)
      · have hdepth : graphRootDepth G u < graphRootDepth G v := by omega
        rw [acyclicEdgeChildRank_eq_right_of_depth_lt G hdepth]
        let n : Fin p := (acyclicVertexOrder G).symm v
        have horder : acyclicVertexOrder G n = v :=
          (acyclicVertexOrder G).apply_symm_apply v
        have hnpos : 0 < graphRootDepth G (acyclicVertexOrder G n) := by
          rw [horder]
          omega
        let i : Fin n.val := acyclicOrderedParentRank G hacyclic n hnpos
        refine ⟨i, acyclicOrderedForest_parent_eq_some G hacyclic n hnpos, ?_⟩
        have huparent : u =
            acyclicParentVertex G hacyclic (acyclicVertexOrder G n) hnpos := by
          exact (Classical.choose_spec
            (existsUnique_adj_graphRootDepth_lt hacyclic
              (acyclicVertexOrder G n) hnpos)).2 u ⟨by simpa [horder] using he,
                by simpa [horder] using hdepth⟩
        have hparentEndpoint :
            acyclicVertexOrder G (orderedForestParentRank n i) = u := by
          dsimp [i]
          change acyclicVertexOrder G
              (orderedForestParentRank n
                (acyclicOrderedParentRank G hacyclic n hnpos)) = u
          exact (acyclicOrderedParentRank_vertex G hacyclic n hnpos).trans
            huparent.symm
        change s(u, v) =
          s(acyclicVertexOrder G (orderedForestParentRank n i),
            acyclicVertexOrder G n)
        exact Sym2.eq_iff.mpr
          (Or.inl ⟨hparentEndpoint.symm, horder.symm⟩)

/-! ## Counting the ordered parents -/

/-- The genuine parent stages among the first `p` ranks. -/
structure OrderedForest.ActiveRank (F : OrderedForest) (p : ℕ) where
  val : Fin p
  property : ∃ i : Fin val.val, F.parent val.val = some i

noncomputable instance orderedForestActiveRankFintype
    (F : OrderedForest) (p : ℕ) : Fintype (F.ActiveRank p) :=
  Fintype.ofInjective OrderedForest.ActiveRank.val (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

/-- The parent-stage wrapper is equivalent to the corresponding subtype. -/
def orderedForestActiveRankEquivSubtype (F : OrderedForest) (p : ℕ) :
    F.ActiveRank p ≃
      {n : Fin p // ∃ i : Fin n.val, F.parent n.val = some i} where
  toFun n := ⟨n.val, n.property⟩
  invFun n := ⟨n.val, n.property⟩
  left_inv n := by cases n; rfl
  right_inv n := by cases n; rfl

theorem orderedForestEdgeCount_eq_sum (F : OrderedForest) :
    ∀ p : ℕ,
      orderedForestEdgeCount F p =
        ∑ n : Fin p,
          match F.parent n.val with
          | none => 0
          | some _ => 1 := by
  intro p
  induction p with
  | zero => simp [orderedForestEdgeCount]
  | succ p ih =>
      rw [orderedForestEdgeCount, Fin.sum_univ_castSucc, ih]
      simp only [Fin.val_castSucc, Fin.val_last]
      congr 1
      · apply Finset.sum_congr rfl
        intro n _hn
        cases F.parent n.val <;> rfl
      · cases F.parent p <;> rfl

theorem orderedForestEdgeCount_eq_card_activeRank
    (F : OrderedForest) (p : ℕ) :
    orderedForestEdgeCount F p = Fintype.card (F.ActiveRank p) := by
  classical
  rw [orderedForestEdgeCount_eq_sum]
  rw [Fintype.card_congr (orderedForestActiveRankEquivSubtype F p),
    Fintype.card_subtype]
  let P : Fin p → Prop := fun n ↦
    ∃ i : Fin n.val, F.parent n.val = some i
  calc
    (∑ n : Fin p,
        match F.parent n.val with
        | none => 0
        | some _ => 1) =
        (∑ n ∈ (Finset.univ : Finset (Fin p)),
          if P n then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro n _hn
      dsimp only [P]
      cases hparent : F.parent n.val with
      | none => simp [hparent]
      | some i => simp [hparent]
    _ = (Finset.univ.filter P).card := by
      exact Finset.sum_boole P Finset.univ

/-- An original graph edge sent to the active stage at its later endpoint. -/
def acyclicEdgeToActiveRank {p : ℕ} (G : SimpleGraph (Fin p))
    (hacyclic : G.IsAcyclic) (e : G.edgeSet) :
    (acyclicOrderedForest G hacyclic).ActiveRank p := by
  refine ⟨acyclicEdgeChildRank G e.1, ?_⟩
  obtain ⟨i, hi, _hedge⟩ := exists_orderedParent_for_edge G hacyclic e
  exact ⟨i, hi⟩

/-- The unoriented parent edge stored at a rank, with a harmless diagonal
placeholder at roots. -/
def orderedForestRankEdge {p : ℕ} (vertexOrder : Equiv.Perm (Fin p))
    (F : OrderedForest) (n : Fin p) : Sym2 (Fin p) :=
  match F.parent n.val with
  | none => s(vertexOrder n, vertexOrder n)
  | some i => s(vertexOrder (orderedForestParentRank n i), vertexOrder n)

theorem acyclicEdge_eq_rankEdge {p : ℕ}
    (G : SimpleGraph (Fin p)) (hacyclic : G.IsAcyclic) (e : G.edgeSet) :
    e.1 = orderedForestRankEdge (acyclicVertexOrder G)
      (acyclicOrderedForest G hacyclic) (acyclicEdgeChildRank G e.1) := by
  obtain ⟨i, hi, he⟩ := exists_orderedParent_for_edge G hacyclic e
  unfold orderedForestRankEdge
  rw [hi]
  exact he

theorem acyclicEdgeToActiveRank_injective {p : ℕ}
    (G : SimpleGraph (Fin p)) (hacyclic : G.IsAcyclic) :
    Function.Injective (acyclicEdgeToActiveRank G hacyclic) := by
  intro e f hef
  have hchild : acyclicEdgeChildRank G e.1 =
      acyclicEdgeChildRank G f.1 :=
    congrArg OrderedForest.ActiveRank.val hef
  apply Subtype.ext
  rw [acyclicEdge_eq_rankEdge G hacyclic e,
    acyclicEdge_eq_rankEdge G hacyclic f, hchild]

/-- An acyclic graph has no more edges than genuine stages in its ordered
parent encoding.  In fact the counts are equal, but this one-sided form is
the exact quantitative fact needed by the overlap bound. -/
theorem card_edgeSet_le_orderedForestEdgeCount {p : ℕ}
    (G : SimpleGraph (Fin p)) (hacyclic : G.IsAcyclic) :
    Nat.card G.edgeSet ≤ orderedForestEdgeCount
      (acyclicOrderedForest G hacyclic) p := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rw [Nat.card_eq_fintype_card,
    orderedForestEdgeCount_eq_card_activeRank]
  exact Fintype.card_le_of_injective
    (acyclicEdgeToActiveRank G hacyclic)
    (acyclicEdgeToActiveRank_injective G hacyclic)

/-! ## Certificates for overlapping edge tuples -/

/-- Any acyclic subgraph of the tuple graph gives a relabeled ordered-forest
certificate for the tuple. -/
def tupleOrderedForestCertificateOfAcyclicSubgraph {p k : ℕ}
    (edges : OrderedDistinctEdgeTuple p k) (F : SimpleGraph (Fin p))
    (hFG : F ≤ orderedEdgeTupleGraph edges) (hacyclic : F.IsAcyclic) :
    TupleOrderedForestCertificate edges where
  vertexOrder := acyclicVertexOrder F
  forest := acyclicOrderedForest F hacyclic
  edgeWitness := by
    intro n i hparent
    have hFadj : F.Adj
        (acyclicVertexOrder F (orderedForestParentRank n i))
        (acyclicVertexOrder F n) :=
      acyclicOrderedForest_parent_adj F hacyclic n i hparent
    obtain ⟨j, h | h⟩ :=
      (orderedEdgeTupleGraph_adj edges _ _).mp (hFG hFadj)
    · exact ⟨j, Or.inl (Prod.ext h.1 h.2)⟩
    · exact ⟨j, Or.inr (Prod.ext h.2 h.1)⟩

theorem tupleOrderedForestCertificateOfAcyclicSubgraph_count
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k)
    (F : SimpleGraph (Fin p))
    (hFG : F ≤ orderedEdgeTupleGraph edges) (hacyclic : F.IsAcyclic) :
    Nat.card F.edgeSet ≤
      orderedForestEdgeCount
        (tupleOrderedForestCertificateOfAcyclicSubgraph
          edges F hFG hacyclic).forest p := by
  exact card_edgeSet_le_orderedForestEdgeCount F hacyclic

/-- A nonmatching tuple admits a certificate with strictly more than half
as many genuine parent edges as used vertices. -/
theorem exists_large_tupleOrderedForestCertificate_of_not_matching
    {p k : ℕ} (edges : OrderedDistinctEdgeTuple p k)
    (hoverlap : ¬edges.IsMatching) :
    ∃ C : TupleOrderedForestCertificate edges,
      (orderedEdgeVertexSet edges).card / 2 + 1 ≤
        orderedForestEdgeCount C.forest p := by
  obtain ⟨F, hFG, hacyclic, _hreach, hlarge⟩ :=
    exists_large_spanningForest_of_not_matching edges hoverlap
  let C : TupleOrderedForestCertificate edges :=
    tupleOrderedForestCertificateOfAcyclicSubgraph
      edges F hFG hacyclic
  refine ⟨C, hlarge.trans ?_⟩
  exact tupleOrderedForestCertificateOfAcyclicSubgraph_count
    edges F hFG hacyclic

/-- Concrete configurationwise forest-power bound for every nonmatching
ordered distinct tuple. -/
theorem gaussianTuple_jointExceedanceReal_le_betaTail_pow_of_not_matching
    {p k : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (edges : OrderedDistinctEdgeTuple p k) (hoverlap : ¬edges.IsMatching)
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m) (t : ℝ) :
    (Measure.pi fun _ : Fin p ↦ stdGaussian E).real
        (orderedEdgeTupleFamilyExceedanceEvent (E := E) edges t) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Set.Ioi t)).toReal ^
        ((orderedEdgeVertexSet edges).card / 2 + 1) := by
  obtain ⟨C, hcount⟩ :=
    exists_large_tupleOrderedForestCertificate_of_not_matching
      edges hoverlap
  exact gaussianTuple_jointExceedanceReal_le_betaTail_pow_of_certificate_count
    edges C m hdim hm t
    ((orderedEdgeVertexSet edges).card / 2 + 1) hcount

end

end LogdetLean.Coherence
