import LogdetLean.Coherence.PoissonVoidSteinFactors
import LogdetLean.Coherence.JointBerryEsseenFinalTarget
import LogdetLean.Coherence.FactorialExpansion
import LogdetLean.Coherence.KolmogorovConcentration
import LogdetLean.Coherence.CanonicalEdgeDecoratedOrthogonalInvariant
import LogdetLean.Coherence.OneEdgeLogPrefixBounds
import LogdetLean.Coherence.ThresholdReplacement
import LogdetLean.Coherence.CompactOneEdgeConditions
import LogdetLean.Coherence.CompactMarkedRateAlgebra
import LogdetLean.Coherence.CompactFiniteIntensityBounds
import LogdetLean.Coherence.ConcreteOverlap
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic
/-!
# Finite Gaussian marked-Poisson adapter

This file specializes the generic marked Poisson-void inequality to the
complete graph of Gaussian sample-correlation edges.  It deliberately keeps
the two genuinely analytic inputs -- decorated leave-one independence and
the one-edge mark-replacement estimate -- as named hypotheses.  All event,
count, neighborhood, and local `b1`/`b2` bookkeeping is proved here.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- Two unoriented correlation edges touch if they share an endpoint. -/
def correlationEdgesTouch {p : ℕ}
    (e f : CorrelationEdge p) : Prop :=
  e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨
    e.1.2 = f.1.1 ∨ e.1.2 = f.1.2

instance correlationEdgesTouch_decidable {p : ℕ}
    (e f : CorrelationEdge p) : Decidable (correlationEdgesTouch e f) :=
  by
    unfold correlationEdgesTouch
    infer_instance

/-- The standard dependency neighborhood: all edges meeting `e`, including
`e` itself. -/
def correlationEdgeNeighborhood (p : ℕ) (e : CorrelationEdge p) :
    Finset (CorrelationEdge p) :=
  Finset.univ.filter fun f ↦ correlationEdgesTouch e f

theorem correlationEdgesTouch_refl {p : ℕ} (e : CorrelationEdge p) :
    correlationEdgesTouch e e := by
  exact Or.inl rfl

theorem correlationEdgesTouch_symm {p : ℕ} {e f : CorrelationEdge p}
    (h : correlationEdgesTouch e f) : correlationEdgesTouch f e := by
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

@[simp]
theorem mem_correlationEdgeNeighborhood_iff {p : ℕ}
    {e f : CorrelationEdge p} :
    f ∈ correlationEdgeNeighborhood p e ↔ correlationEdgesTouch e f := by
  simp [correlationEdgeNeighborhood]

theorem self_mem_correlationEdgeNeighborhood {p : ℕ}
    (e : CorrelationEdge p) : e ∈ correlationEdgeNeighborhood p e := by
  simp [correlationEdgesTouch_refl]

/-- Edges incident to one fixed vertex. -/
def correlationEdgeStar (p : ℕ) (v : Fin p) : Finset (CorrelationEdge p) :=
  Finset.univ.filter fun e ↦ e.1.1 = v ∨ e.1.2 = v

/-- The endpoint of an incident edge different from the specified vertex.
The value outside the star is harmless and never used in injectivity proofs. -/
def starOtherEndpoint {p : ℕ}
    (v : Fin p) (e : CorrelationEdge p) : Fin p :=
  if e.1.1 = v then e.1.2 else e.1.1

private theorem starOtherEndpoint_injOn_star
    {p : ℕ} (v : Fin p) :
    Set.InjOn (starOtherEndpoint v)
      (correlationEdgeStar p v : Set (CorrelationEdge p)) := by
  intro e he f hf hother
  have he' : e.1.1 = v ∨ e.1.2 = v := by
    simpa [correlationEdgeStar] using he
  have hf' : f.1.1 = v ∨ f.1.2 = v := by
    simpa [correlationEdgeStar] using hf
  apply Subtype.ext
  rcases he' with he1 | he2 <;> rcases hf' with hf1 | hf2
  · have hsecond : e.1.2 = f.1.2 := by
      simpa [starOtherEndpoint, he1, hf1] using hother
    exact Prod.ext (he1.trans hf1.symm) hsecond
  · have hcross : e.1.2 = f.1.1 := by
      simpa [starOtherEndpoint, he1,
        show f.1.1 ≠ v by
          intro hfv
          have := f.2
          rw [hfv, hf2] at this
          exact (lt_irrefl v this)] using hother
    exfalso
    have heLt : v < e.1.2 := by simpa [he1] using e.2
    have hfLt : f.1.1 < v := by simpa [hf2] using f.2
    rw [hcross] at heLt
    exact lt_asymm heLt hfLt
  · have hcross : e.1.1 = f.1.2 := by
      simpa [starOtherEndpoint, hf1,
        show e.1.1 ≠ v by
          intro hev
          have := e.2
          rw [hev, he2] at this
          exact (lt_irrefl v this)] using hother
    exfalso
    have heLt : e.1.1 < v := by simpa [he2] using e.2
    have hfLt : v < f.1.2 := by simpa [hf1] using f.2
    rw [hcross] at heLt
    exact lt_asymm heLt hfLt
  · have heFirstNe : e.1.1 ≠ v := by
      intro hev
      have := e.2
      rw [hev, he2] at this
      exact (lt_irrefl v this)
    have hfFirstNe : f.1.1 ≠ v := by
      intro hfv
      have := f.2
      rw [hfv, hf2] at this
      exact (lt_irrefl v this)
    have hfirst : e.1.1 = f.1.1 := by
      simpa [starOtherEndpoint, heFirstNe, hfFirstNe] using hother
    exact Prod.ext hfirst (he2.trans hf2.symm)

theorem card_correlationEdgeStar_le (p : ℕ) (v : Fin p) :
    (correlationEdgeStar p v).card ≤ p := by
  have hmap : Set.MapsTo (starOtherEndpoint v)
      (correlationEdgeStar p v : Set (CorrelationEdge p))
      (Finset.univ : Finset (Fin p)) := by
    intro e he
    simp
  simpa using Finset.card_le_card_of_injOn
    (starOtherEndpoint v) hmap
      (starOtherEndpoint_injOn_star v)

theorem correlationEdgeNeighborhood_subset_union_stars
    {p : ℕ} (e : CorrelationEdge p) :
    correlationEdgeNeighborhood p e ⊆
      correlationEdgeStar p e.1.1 ∪ correlationEdgeStar p e.1.2 := by
  intro f hf
  have htouch : correlationEdgesTouch e f :=
    (mem_correlationEdgeNeighborhood_iff).1 hf
  simp only [correlationEdgeStar, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rcases htouch with h | h | h | h
  · exact Or.inl (Or.inl h.symm)
  · exact Or.inl (Or.inr h.symm)
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

/-- A deliberately loose uniform neighborhood bound.  The exact cardinality
is `2*p-3`; `2*p` is enough for the sharp-order `O(1/p)` local error. -/
theorem card_correlationEdgeNeighborhood_le_two_mul
    {p : ℕ} (e : CorrelationEdge p) :
    (correlationEdgeNeighborhood p e).card ≤ 2 * p := by
  calc
    (correlationEdgeNeighborhood p e).card ≤
        (correlationEdgeStar p e.1.1 ∪
          correlationEdgeStar p e.1.2).card :=
      Finset.card_le_card (correlationEdgeNeighborhood_subset_union_stars e)
    _ ≤ (correlationEdgeStar p e.1.1).card +
        (correlationEdgeStar p e.1.2).card := Finset.card_union_le _ _
    _ ≤ p + p := Nat.add_le_add
      (card_correlationEdgeStar_le p e.1.1)
      (card_correlationEdgeStar_le p e.1.2)
    _ = 2 * p := by omega

/-- There are exactly `p choose 2` canonically oriented correlation edges. -/
theorem card_correlationEdge (p : ℕ) :
    Fintype.card (CorrelationEdge p) = p.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (@Fintype.card_product_filter_lt (Fin p) _ _)

/-! ## Concrete Gaussian events and count identities -/

/-- Raw Gaussian data space for residual dimension `m` and `p` columns. -/
abbrev GaussianCorrelationSample (m p : ℕ) :=
  NestedTuple (ObservationSpace (m + 1)) p

/-- Null product measure on the raw Gaussian data. -/
def gaussianCorrelationMeasure (m p : ℕ) :
    Measure (GaussianCorrelationSample m p) :=
  nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p

/-- The two raw sample columns attached to a correlation edge. -/
def gaussianRawEdgePair (m p : ℕ) (e : CorrelationEdge p) :
    GaussianCorrelationSample m p →
      ObservationSpace (m + 1) × ObservationSpace (m + 1) :=
  fun data ↦
    (nestedTupleToFin p data e.1.1, nestedTupleToFin p data e.1.2)

theorem measurable_gaussianRawEdgePair
    (m p : ℕ) (e : CorrelationEdge p) :
    Measurable (gaussianRawEdgePair m p e) := by
  unfold gaussianRawEdgePair
  exact (measurable_nestedTupleToFin_apply p e.1.1).prodMk
    (measurable_nestedTupleToFin_apply p e.1.2)

/-- Any two distinct coordinates of the raw iid Gaussian tuple have the
ordinary two-column product law. -/
theorem map_gaussianRawEdgePair_eq_gaussianProduct
    (m p : ℕ) (e : CorrelationEdge p) :
    Measure.map (gaussianRawEdgePair m p e)
        (gaussianCorrelationMeasure m p) =
      (stdGaussian (ObservationSpace (m + 1))).prod
        (stdGaussian (ObservationSpace (m + 1))) := by
  let E := ObservationSpace (m + 1)
  let mu : Measure (NestedTuple E p) :=
    nestedProductMeasure (stdGaussian E) p
  let nu : Measure (Fin p → E) := Measure.pi fun _ : Fin p ↦ stdGaussian E
  let read : NestedTuple E p → Fin p → E := nestedTupleToFin p
  let pair : (Fin p → E) → E × E := fun v ↦ (v e.1.1, v e.1.2)
  letI : IsProbabilityMeasure (stdGaussian E) :=
    ProbabilityTheory.isProbabilityMeasure_stdGaussian
  letI : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  have hcoord : iIndepFun (fun i (v : Fin p → E) ↦ v i) nu := by
    exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  have hindep : IndepFun (fun v : Fin p → E ↦ v e.1.1)
      (fun v : Fin p → E ↦ v e.1.2) nu := hcoord.indepFun hne
  have hpair : Measure.map pair nu =
      (stdGaussian E).prod (stdGaussian E) := by
    rw [hindep.map_prod_eq_prod_map_map
      (measurable_pi_apply e.1.1).aemeasurable
      (measurable_pi_apply e.1.2).aemeasurable]
    rw [(measurePreserving_eval (fun _ : Fin p ↦ stdGaussian E) e.1.1).map_eq,
      (measurePreserving_eval (fun _ : Fin p ↦ stdGaussian E) e.1.2).map_eq]
  have hread := (measurePreserving_nestedTupleToFin (stdGaussian E) p).map_eq
  change Measure.map (pair ∘ read) mu = _
  calc
    Measure.map (pair ∘ read) mu = Measure.map pair (Measure.map read mu) := by
      rw [Measure.map_map (by fun_prop : Measurable pair)
        (measurable_nestedTupleToFin p)]
    _ = Measure.map pair nu := by rw [hread]
    _ = (stdGaussian E).prod (stdGaussian E) := hpair

/-- The edge score is the squared Pearson correlation of the corresponding
two raw columns, multiplied by `m`. -/
theorem scaledSquaredCorrelationScore_eq_rawEdgePair
    (m p : ℕ) (e : CorrelationEdge p)
    (data : GaussianCorrelationSample m p) :
    scaledSquaredCorrelationScore m p data e.1 =
      (m : ℝ) * squaredCenteredPearson (m + 1)
        (gaussianRawEdgePair m p e data) := by
  unfold scaledSquaredCorrelationScore centeredCorrelationMatrix
    gaussianRawEdgePair squaredCenteredPearson centerGaussianPair
  rw [normalizedGram_apply_sq_eq_squaredNormalizedInner_total]
  rw [nestedTupleToFin_centerNested]
  rfl

/-- Strict exceedance event associated with one correlation edge. -/
def coherenceEdgeExceedanceEvent (m p : ℕ) (x : ℝ)
    (e : CorrelationEdge p) : Set (GaussianCorrelationSample m p) :=
  {data | classicalCoherenceThreshold m p x <
    scaledSquaredCorrelationScore m p data e.1}

theorem measurableSet_coherenceEdgeExceedanceEvent
    (m p : ℕ) (x : ℝ) (e : CorrelationEdge p) :
    MeasurableSet (coherenceEdgeExceedanceEvent m p x e) := by
  exact measurableSet_lt measurable_const
    (measurable_scaledSquaredCorrelationScore m p e.1)

/-- Exact one-edge beta-tail probability, uniformly over the edge label. -/
theorem coherenceEdgeExceedanceEvent_probability_eq_betaTail
    {m p : ℕ} (hm : 2 ≤ m) (x : ℝ) (e : CorrelationEdge p) :
    (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e) =
      betaCorrelationTailProbability m p x := by
  let pair := gaussianRawEdgePair m p e
  let S : Set (ObservationSpace (m + 1) × ObservationSpace (m + 1)) :=
    {w | classicalCoherenceThreshold m p x <
      (m : ℝ) * squaredCenteredPearson (m + 1) w}
  have hpair : Measurable pair := measurable_gaussianRawEdgePair m p e
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const
      (measurable_const.mul (measurable_squaredCenteredPearson (m + 1)))
  have hevent : coherenceEdgeExceedanceEvent m p x e = pair ⁻¹' S := by
    ext data
    simp only [coherenceEdgeExceedanceEvent, S, Set.mem_setOf_eq,
      Set.mem_preimage]
    rw [scaledSquaredCorrelationScore_eq_rawEdgePair]
  rw [hevent, measureReal_def]
  rw [← Measure.map_apply hpair hS]
  rw [map_gaussianRawEdgePair_eq_gaussianProduct]
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hset : S = squaredCenteredPearson (m + 1) ⁻¹'
      Ioi (classicalCoherenceThreshold m p x / (m : ℝ)) := by
    ext w
    change classicalCoherenceThreshold m p x <
        (m : ℝ) * squaredCenteredPearson (m + 1) w ↔
      classicalCoherenceThreshold m p x / (m : ℝ) <
        squaredCenteredPearson (m + 1) w
    constructor
    · intro h
      exact (div_lt_iff₀ hm0).2 (by simpa [mul_comm] using h)
    · intro h
      simpa [mul_comm] using (div_lt_iff₀ hm0).1 h
  rw [hset]
  rw [← Measure.map_apply (measurable_squaredCenteredPearson (m + 1))
    measurableSet_Ioi]
  rw [map_squaredCenteredPearson_rawGaussianProduct_eq_beta m hm]
  rfl

/-! ### Adjacent two-edge forest law -/

/-- The ordered two-edge tuple with entries `e,f`. -/
def orderedTwoEdgeTuple {p : ℕ} (e f : CorrelationEdge p)
    (hef : e ≠ f) : OrderedDistinctEdgeTuple p 2 where
  toFun i := Fin.cases e (fun _ ↦ f) i
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · simp only [Fin.cases_zero, Fin.cases_succ] at hij
      exact (hef hij).elim
    · simp only [Fin.cases_zero, Fin.cases_succ] at hij
      exact (hef hij.symm).elim
    · rfl

@[simp]
theorem orderedTwoEdgeTuple_zero {p : ℕ} (e f : CorrelationEdge p)
    (hef : e ≠ f) :
    orderedTwoEdgeTuple e f hef (0 : Fin 2) = e := rfl

@[simp]
theorem orderedTwoEdgeTuple_one {p : ℕ} (e f : CorrelationEdge p)
    (hef : e ≠ f) :
    orderedTwoEdgeTuple e f hef (1 : Fin 2) = f := rfl

/-- Two distinct touching edges are a nonmatching two-edge tuple. -/
theorem orderedTwoEdgeTuple_not_matching_of_touch
    {p : ℕ} {e f : CorrelationEdge p} (hef : e ≠ f)
    (htouch : correlationEdgesTouch e f) :
    ¬(orderedTwoEdgeTuple e f hef).IsMatching := by
  intro hinj
  unfold OrderedDistinctEdgeTuple.IsMatching at hinj
  rcases htouch with h | h | h | h
  · have hslots : ((0 : Fin 2), false) = ((1 : Fin 2), false) :=
      hinj (by
        change e.1.1 = f.1.1
        exact h)
    have := congrArg (fun q : Fin 2 × Bool ↦ q.1) hslots
    norm_num at this
  · have hslots : ((0 : Fin 2), false) = ((1 : Fin 2), true) :=
      hinj (by
        change e.1.1 = f.1.2
        exact h)
    have := congrArg (fun q : Fin 2 × Bool ↦ q.1) hslots
    norm_num at this
  · have hslots : ((0 : Fin 2), true) = ((1 : Fin 2), false) :=
      hinj (by
        change e.1.2 = f.1.1
        exact h)
    have := congrArg (fun q : Fin 2 × Bool ↦ q.1) hslots
    norm_num at this
  · have hslots : ((0 : Fin 2), true) = ((1 : Fin 2), true) :=
      hinj (by
        change e.1.2 = f.1.2
        exact h)
    have := congrArg (fun q : Fin 2 × Bool ↦ q.1) hslots
    norm_num at this

/-- The two endpoints of the first edge both occur in the tuple's vertex
set, hence that vertex set has cardinality at least two. -/
theorem two_le_card_orderedEdgeVertexSet_orderedTwoEdgeTuple
    {p : ℕ} (e f : CorrelationEdge p) (hef : e ≠ f) :
    2 ≤ (orderedEdgeVertexSet (orderedTwoEdgeTuple e f hef)).card := by
  have hleft : e.1.1 ∈
      orderedEdgeVertexSet (orderedTwoEdgeTuple e f hef) := by
    unfold orderedEdgeVertexSet
    simp [orderedEdgeEndpointMap, correlationEdgeEndpoint]
  have hright : e.1.2 ∈
      orderedEdgeVertexSet (orderedTwoEdgeTuple e f hef) := by
    unfold orderedEdgeVertexSet
    simp [orderedEdgeEndpointMap, correlationEdgeEndpoint]
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  have hcard : 1 <
      (orderedEdgeVertexSet (orderedTwoEdgeTuple e f hef)).card :=
    Finset.one_lt_card.mpr
      ⟨e.1.1, hleft, e.1.2, hright, hne⟩
  omega

/-- Center the raw columns and read them as a finite family. -/
def centeredGaussianFamily (m p : ℕ) :
    GaussianCorrelationSample m p → Fin p → centeredSubspace (m + 1) :=
  fun data ↦ nestedTupleToFin p (centerNested (m + 1) p data)

theorem measurable_centeredGaussianFamily (m p : ℕ) :
    Measurable (centeredGaussianFamily m p) := by
  unfold centeredGaussianFamily
  exact (measurable_nestedTupleToFin p).comp
    (measurable_centerNested (m + 1) p)

theorem map_centeredGaussianFamily_eq_pi (m p : ℕ) :
    Measure.map (centeredGaussianFamily m p)
        (gaussianCorrelationMeasure m p) =
      Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace (m + 1)) := by
  have h := (measurePreserving_permuteCenteredNestedColumns
    (m + 1) p (Equiv.refl (Fin p))).map_eq
  have hfun : (fun data : GaussianCorrelationSample m p ↦
      permuteColumns (Equiv.refl (Fin p))
        (nestedTupleToFin p (centerNested (m + 1) p data))) =
      centeredGaussianFamily m p := by
    funext data
    ext i
    simp [centeredGaussianFamily, permuteColumns]
  rw [hfun] at h
  exact h

/-- Raw scaled scores factor pointwise through the centered finite family. -/
theorem scaledSquaredCorrelationScore_eq_centeredFamily
    (m p : ℕ) (data : GaussianCorrelationSample m p)
    (i j : Fin p) :
    scaledSquaredCorrelationScore m p data (i, j) =
      (m : ℝ) * squaredNormalizedInner
        (centeredGaussianFamily m p data i)
        (centeredGaussianFamily m p data j) := by
  unfold scaledSquaredCorrelationScore centeredCorrelationMatrix
    centeredGaussianFamily
  rw [normalizedGram_apply_sq_eq_squaredNormalizedInner_total]

/-- The intersection of two raw edge events is exactly the pullback of the
corresponding two-edge finite-family forest event. -/
theorem preimage_orderedTwoEdgeFamilyEvent_eq_inter
    {m p : ℕ} (hm : 0 < m) (x : ℝ)
    (e f : CorrelationEdge p) (hef : e ≠ f) :
    centeredGaussianFamily m p ⁻¹'
        orderedEdgeTupleFamilyExceedanceEvent
          (E := centeredSubspace (m + 1))
          (orderedTwoEdgeTuple e f hef)
          (classicalCoherenceThreshold m p x / (m : ℝ)) =
      coherenceEdgeExceedanceEvent m p x e ∩
        coherenceEdgeExceedanceEvent m p x f := by
  ext data
  constructor
  · intro hall
    constructor
    · have hzero := hall (0 : Fin 2)
      change classicalCoherenceThreshold m p x <
        scaledSquaredCorrelationScore m p data e.1
      rw [scaledSquaredCorrelationScore_eq_centeredFamily]
      exact (scaledSquaredInner_exceedance_iff hm
        (classicalCoherenceThreshold m p x)
        (centeredGaussianFamily m p data e.1.1,
          centeredGaussianFamily m p data e.1.2)).mpr
        (by simpa using hzero)
    · have hone := hall (1 : Fin 2)
      change classicalCoherenceThreshold m p x <
        scaledSquaredCorrelationScore m p data f.1
      rw [scaledSquaredCorrelationScore_eq_centeredFamily]
      exact (scaledSquaredInner_exceedance_iff hm
        (classicalCoherenceThreshold m p x)
        (centeredGaussianFamily m p data f.1.1,
          centeredGaussianFamily m p data f.1.2)).mpr
        (by simpa using hone)
  · rintro ⟨hevent, fevent⟩ j
    fin_cases j
    · have h := hevent
      change classicalCoherenceThreshold m p x <
        scaledSquaredCorrelationScore m p data e.1 at h
      rw [scaledSquaredCorrelationScore_eq_centeredFamily] at h
      simpa using (scaledSquaredInner_exceedance_iff hm
        (classicalCoherenceThreshold m p x)
        (centeredGaussianFamily m p data e.1.1,
          centeredGaussianFamily m p data e.1.2)).mp h
    · have h := fevent
      change classicalCoherenceThreshold m p x <
        scaledSquaredCorrelationScore m p data f.1 at h
      rw [scaledSquaredCorrelationScore_eq_centeredFamily] at h
      simpa using (scaledSquaredInner_exceedance_iff hm
        (classicalCoherenceThreshold m p x)
        (centeredGaussianFamily m p data f.1.1,
          centeredGaussianFamily m p data f.1.2)).mp h

/-- Exact forest-power bound for any two distinct touching correlation
edges.  In fact equality holds; the one-sided form is exactly what `b2`
requires. -/
theorem coherenceAdjacentPair_probability_le_betaTail_sq
    {m p : ℕ} (hm : 2 ≤ m) (x : ℝ)
    (e f : CorrelationEdge p) (hef : e ≠ f)
    (htouch : correlationEdgesTouch e f) :
    (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e ∩
          coherenceEdgeExceedanceEvent m p x f) ≤
      betaCorrelationTailProbability m p x ^ 2 := by
  let edges := orderedTwoEdgeTuple e f hef
  let S := orderedEdgeTupleFamilyExceedanceEvent
    (E := centeredSubspace (m + 1)) edges
    (classicalCoherenceThreshold m p x / (m : ℝ))
  let nu : Measure (Fin p → centeredSubspace (m + 1)) :=
    Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace (m + 1))
  have hS : MeasurableSet S :=
    measurableSet_orderedEdgeTupleFamilyExceedanceEvent edges _
  have hpre : centeredGaussianFamily m p ⁻¹' S =
      coherenceEdgeExceedanceEvent m p x e ∩
        coherenceEdgeExceedanceEvent m p x f := by
    exact preimage_orderedTwoEdgeFamilyEvent_eq_inter
      (by omega) x e f hef
  have hdim : Module.finrank ℝ (centeredSubspace (m + 1)) = m := by
    simpa using finrank_centeredSubspace (N := m + 1) (Nat.zero_lt_succ m)
  have hoverlap : ¬edges.IsMatching :=
    orderedTwoEdgeTuple_not_matching_of_touch hef htouch
  have hforest :=
    gaussianTuple_jointExceedanceReal_le_betaTail_pow_of_not_matching
      edges hoverlap m hdim hm
        (classicalCoherenceThreshold m p x / (m : ℝ))
  let q : ℝ := betaCorrelationTailProbability m p x
  letI : IsProbabilityMeasure
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) :=
    pairBeta_isProbabilityMeasure hm
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := measureReal_le_one
  have hexp : 2 ≤ (orderedEdgeVertexSet edges).card / 2 + 1 := by
    have hcard := two_le_card_orderedEdgeVertexSet_orderedTwoEdgeTuple e f hef
    dsimp [edges]
    omega
  calc
    (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e ∩
          coherenceEdgeExceedanceEvent m p x f) =
        (Measure.map (centeredGaussianFamily m p)
          (gaussianCorrelationMeasure m p)).real S := by
      rw [measureReal_def, measureReal_def,
        Measure.map_apply (measurable_centeredGaussianFamily m p) hS,
        hpre]
    _ = nu.real S := by rw [map_centeredGaussianFamily_eq_pi]
    _ ≤ q ^ ((orderedEdgeVertexSet edges).card / 2 + 1) := by
      simpa [nu, q, betaCorrelationTailProbability, edges, S] using hforest
    _ ≤ q ^ 2 := pow_le_pow_of_le_one hq0 hq1 hexp
    _ = betaCorrelationTailProbability m p x ^ 2 := rfl

/-- Lower event for the standardized log determinant. -/
def coherenceBulkLowerEvent (m p : ℕ) (z : ℝ) :
    Set (GaussianCorrelationSample m p) :=
  {data | Z0mpStatistic m p data ≤ z}

theorem measurableSet_coherenceBulkLowerEvent
    (m p : ℕ) (z : ℝ) :
    MeasurableSet (coherenceBulkLowerEvent m p z) :=
  measurableSet_le (measurable_Z0mpStatistic m p) measurable_const

/-- Real-valued bulk mark used in the marked Stein identity. -/
def coherenceBulkLowerMark (m p : ℕ) (z : ℝ)
    (data : GaussianCorrelationSample m p) : ℝ :=
  bernoulliEventIndicator (coherenceBulkLowerEvent m p z) data

theorem measurable_coherenceBulkLowerMark (m p : ℕ) (z : ℝ) :
    Measurable (coherenceBulkLowerMark m p z) := by
  exact ((measurable_of_countable fun n : ℕ ↦ (n : ℝ)).comp
    (measurable_bernoulliEventIndicator
      (measurableSet_coherenceBulkLowerEvent m p z)))

theorem abs_coherenceBulkLowerMark_le_one
    (m p : ℕ) (z : ℝ) (data : GaussianCorrelationSample m p) :
    |coherenceBulkLowerMark m p z data| ≤ 1 := by
  rcases bernoulliEventIndicator_eq_zero_or_one
      (coherenceBulkLowerEvent m p z) data with h | h <;>
    simp [coherenceBulkLowerMark, h]

theorem integrable_coherenceBulkLowerMark (m p : ℕ) (z : ℝ) :
    Integrable (coherenceBulkLowerMark m p z)
      (gaussianCorrelationMeasure m p) := by
  letI : IsProbabilityMeasure (gaussianCorrelationMeasure m p) := by
    unfold gaussianCorrelationMeasure
    infer_instance
  exact integrable_real_bernoulliEventIndicator
    (measurableSet_coherenceBulkLowerEvent m p z)

/-- The marked count over the edge subtype is literally the coherence
exceedance count already used by the extreme statistic. -/
theorem markedBernoulliCount_coherenceEdgeExceedanceEvent
    (m p : ℕ) (x : ℝ) (data : GaussianCorrelationSample m p) :
    markedBernoulliCount (coherenceEdgeExceedanceEvent m p x) data =
      coherenceExceedanceCount m p x data := by
  unfold coherenceExceedanceCount
  rw [thresholdExceedanceCount_eq_card_activeCorrelationEdges]
  unfold markedBernoulliCount activeCorrelationEdges
    coherenceEdgeExceedanceEvent
  simp [bernoulliEventIndicator]

/-- The Poisson void indicator is exactly the lower event for the maximum. -/
theorem markedVoidIndicator_coherence_eq_extremeIndicator
    {m p : ℕ} (hp : 2 ≤ p) (x : ℝ)
    (data : GaussianCorrelationSample m p) :
    markedVoidIndicator
        (markedBernoulliCount (coherenceEdgeExceedanceEvent m p x) data) =
      bernoulliEventIndicator {d | coherenceExtreme m p d ≤ x} data := by
  rw [markedBernoulliCount_coherenceEdgeExceedanceEvent]
  have hiff := coherenceExtreme_le_iff_exceedanceCount_eq_zero hp data x
  by_cases hzero : coherenceExceedanceCount m p x data = 0
  · have hextreme : coherenceExtreme m p data ≤ x := hiff.mpr hzero
    simp [markedVoidIndicator, hzero, bernoulliEventIndicator, hextreme]
  · have hextreme : ¬coherenceExtreme m p data ≤ x := by
      exact fun h ↦ hzero (hiff.mp h)
    simp [markedVoidIndicator, hzero, bernoulliEventIndicator, hextreme]

/-- The marked expectation is exactly the desired joint lower-tail
probability; no approximation enters this identity. -/
theorem integral_coherenceBulkLowerMark_mul_void_eq_jointProbability
    {m p : ℕ} (hp : 2 ≤ p) (z x : ℝ) :
    (∫ data,
        coherenceBulkLowerMark m p z data *
          markedVoidIndicator
            (markedBernoulliCount
              (coherenceEdgeExceedanceEvent m p x) data)
      ∂gaussianCorrelationMeasure m p) =
      gaussianCoherenceJointLowerProbability m p z x := by
  let jointEvent : Set (GaussianCorrelationSample m p) :=
    {data | Z0mpStatistic m p data ≤ z ∧ coherenceExtreme m p data ≤ x}
  have hjoint : MeasurableSet jointEvent :=
    (measurableSet_coherenceBulkLowerEvent m p z).inter
      (measurableSet_le (measurable_coherenceExtreme m p) measurable_const)
  have hfun :
      (fun data : GaussianCorrelationSample m p ↦
        coherenceBulkLowerMark m p z data *
          markedVoidIndicator
            (markedBernoulliCount
              (coherenceEdgeExceedanceEvent m p x) data)) =
      fun data ↦ (bernoulliEventIndicator jointEvent data : ℝ) := by
    funext data
    rw [markedVoidIndicator_coherence_eq_extremeIndicator hp x data]
    by_cases hbulk : Z0mpStatistic m p data ≤ z <;>
      by_cases hextreme : coherenceExtreme m p data ≤ x <;>
      simp [coherenceBulkLowerMark, coherenceBulkLowerEvent, jointEvent,
        bernoulliEventIndicator, hbulk, hextreme]
  rw [hfun, integral_real_bernoulliEventIndicator
    (gaussianCorrelationMeasure m p) hjoint]
  rfl

/-- The mean of the bulk mark is the CDF of the concrete null statistic. -/
theorem integral_coherenceBulkLowerMark_eq_cdf (m p : ℕ) (z : ℝ) :
    (∫ data, coherenceBulkLowerMark m p z data
      ∂gaussianCorrelationMeasure m p) =
      cdf (Measure.map (Z0mpStatistic m p)
        (gaussianCorrelationMeasure m p)) z := by
  letI : IsProbabilityMeasure (gaussianCorrelationMeasure m p) := by
    unfold gaussianCorrelationMeasure
    infer_instance
  letI : IsProbabilityMeasure
      (Measure.map (Z0mpStatistic m p) (gaussianCorrelationMeasure m p)) :=
    Measure.isProbabilityMeasure_map
      (measurable_Z0mpStatistic m p).aemeasurable
  unfold coherenceBulkLowerMark
  rw [integral_real_bernoulliEventIndicator
    (gaussianCorrelationMeasure m p)
      (measurableSet_coherenceBulkLowerEvent m p z)]
  rw [cdf_eq_real]
  change ((gaussianCorrelationMeasure m p)
      (Z0mpStatistic m p ⁻¹' Iic z)).toReal =
    ((Measure.map (Z0mpStatistic m p)
      (gaussianCorrelationMeasure m p)) (Iic z)).toReal
  rw [Measure.map_apply (measurable_Z0mpStatistic m p) measurableSet_Iic]

/-- The proved scalar Kolmogorov envelope controls the bulk-mark mean. -/
theorem abs_integral_coherenceBulkLowerMark_sub_normal_le
    {m p : ℕ} (hadm : Admissible m p) (z : ℝ) :
    |(∫ data, coherenceBulkLowerMark m p z data
        ∂gaussianCorrelationMeasure m p) - standardNormalCDF z| ≤
      provedNullLogdetKolmogorovEnvelope m p := by
  rw [integral_coherenceBulkLowerMark_eq_cdf]
  have hpoint := LogdetLean.abs_cdf_sub_le_kolmogorovDistance
    (Measure.map (Z0mpStatistic m p) (gaussianCorrelationMeasure m p))
    (gaussianReal 0 1) z
  unfold standardNormalCDF
  exact hpoint.trans
    (kolmogorovDistance_actualZ0mp_le_provedEnvelope hadm)

/-! ## Local `b1` and `b2` bookkeeping -/

/-- Uniform marginal probabilities and a uniform neighborhood-cardinality
bound give the standard `b1` estimate. -/
theorem markedPoissonBOne_le_of_uniform
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    {q : ℝ} (hq : 0 ≤ q) (D : ℕ)
    (hprob : ∀ i, mu.real (A i) = q)
    (hcard : ∀ i, (B i).card ≤ D) :
    markedPoissonBOne mu A B ≤
      (Fintype.card I : ℝ) * (D : ℝ) * q ^ 2 := by
  unfold markedPoissonBOne
  calc
    ∑ i, mu.real (A i) * ∑ j ∈ B i, mu.real (A j) =
        ∑ i, q * ((B i).card : ℝ) * q := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hprob]
      simp_rw [hprob]
      simp
      ring
    _ ≤ ∑ _i : I, q * (D : ℝ) * q := by
      apply Finset.sum_le_sum
      intro i _hi
      have hcardReal : ((B i).card : ℝ) ≤ (D : ℝ) := by
        exact_mod_cast hcard i
      calc
        q * ((B i).card : ℝ) * q =
            ((B i).card : ℝ) * q ^ 2 := by ring
        _ ≤ (D : ℝ) * q ^ 2 :=
          mul_le_mul_of_nonneg_right hcardReal (sq_nonneg q)
        _ = q * (D : ℝ) * q := by ring
    _ = (Fintype.card I : ℝ) * (D : ℝ) * q ^ 2 := by
      simp
      ring

/-- Uniform local pair probabilities give the matching `b2` estimate. -/
theorem markedPoissonBTwo_le_of_uniform
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    {q : ℝ} (hq : 0 ≤ q) (D : ℕ)
    (hpair : ∀ i j, j ∈ (B i).erase i →
      mu.real (A i ∩ A j) ≤ q ^ 2)
    (hcard : ∀ i, (B i).card ≤ D) :
    markedPoissonBTwo mu A B ≤
      (Fintype.card I : ℝ) * (D : ℝ) * q ^ 2 := by
  unfold markedPoissonBTwo
  calc
    ∑ i, ∑ j ∈ (B i).erase i, mu.real (A i ∩ A j) ≤
        ∑ _i : I, (D : ℝ) * q ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        ∑ j ∈ (B i).erase i, mu.real (A i ∩ A j) ≤
            ∑ _j ∈ (B i).erase i, q ^ 2 := by
          exact Finset.sum_le_sum fun j hj ↦ hpair i j hj
        _ = (((B i).erase i).card : ℝ) * q ^ 2 := by simp
        _ ≤ (D : ℝ) * q ^ 2 := by
          have hcardErase : ((B i).erase i).card ≤ D :=
            (Finset.card_erase_le.trans (hcard i))
          have hcardReal : (((B i).erase i).card : ℝ) ≤ (D : ℝ) := by
            exact_mod_cast hcardErase
          exact mul_le_mul_of_nonneg_right hcardReal (sq_nonneg q)
    _ = (Fintype.card I : ℝ) * (D : ℝ) * q ^ 2 := by
      simp
      ring

/-- Complete-graph specialization of the two local error factors. -/
theorem coherence_markedPoissonBOne_add_BTwo_le
    (m p : ℕ) (x : ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hprob : ∀ e : CorrelationEdge p,
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e) = q)
    (hpair : ∀ e f : CorrelationEdge p,
      f ∈ (correlationEdgeNeighborhood p e).erase e →
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e ∩
          coherenceEdgeExceedanceEvent m p x f) ≤ q ^ 2) :
    markedPoissonBOne (gaussianCorrelationMeasure m p)
        (coherenceEdgeExceedanceEvent m p x)
        (correlationEdgeNeighborhood p) +
      markedPoissonBTwo (gaussianCorrelationMeasure m p)
        (coherenceEdgeExceedanceEvent m p x)
        (correlationEdgeNeighborhood p) ≤
      4 * (p.choose 2 : ℝ) * (p : ℝ) * q ^ 2 := by
  have hb1 := markedPoissonBOne_le_of_uniform
    (gaussianCorrelationMeasure m p)
    (coherenceEdgeExceedanceEvent m p x)
    (correlationEdgeNeighborhood p) hq (2 * p) hprob
    card_correlationEdgeNeighborhood_le_two_mul
  have hb2 := markedPoissonBTwo_le_of_uniform
    (gaussianCorrelationMeasure m p)
    (coherenceEdgeExceedanceEvent m p x)
    (correlationEdgeNeighborhood p) hq (2 * p) hpair
    card_correlationEdgeNeighborhood_le_two_mul
  rw [card_correlationEdge] at hb1 hb2
  norm_num [Nat.cast_mul] at hb1 hb2 ⊢
  have hchoose : (0 : ℝ) ≤ (p.choose 2 : ℝ) := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg q]

/-- Exact conversion of the marked intensity to the finite Beta-tail
intensity used in the theorem statement. -/
theorem markedBernoulliIntensity_coherence_eq_finiteCoherenceIntensity
    (m p : ℕ) (x : ℝ)
    (hprob : ∀ e : CorrelationEdge p,
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e) =
          betaCorrelationTailProbability m p x) :
    markedBernoulliIntensity (gaussianCorrelationMeasure m p)
        (coherenceEdgeExceedanceEvent m p x) =
      finiteCoherenceIntensity m p x := by
  unfold markedBernoulliIntensity finiteCoherenceIntensity
  simp_rw [hprob]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    card_correlationEdge]

/-! ## Uniform aggregation of one-edge mark errors -/

/-- Uniform unconditional and event-weighted one-edge replacement estimates
sum to the expected intensity times the sum of their two error envelopes. -/
theorem markedPoissonMarkReplacement_le_card_mul_of_uniform
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    {q U W : ℝ} (hq : 0 ≤ q)
    (hprob : ∀ i, mu.real (A i) = q)
    (hplain : ∀ i, (∫ omega, |h omega - hLeave i omega| ∂mu) ≤ U)
    (hevent : ∀ i, (∫ omega,
      (bernoulliEventIndicator (A i) omega : ℝ) *
        |h omega - hLeave i omega| ∂mu) ≤ q * W) :
    markedPoissonMarkReplacement mu A h hLeave ≤
      (Fintype.card I : ℝ) * q * (U + W) := by
  unfold markedPoissonMarkReplacement
  simp_rw [hprob]
  calc
    ∑ i : I,
        (q * (∫ omega, |h omega - hLeave i omega| ∂mu) +
          ∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
            |h omega - hLeave i omega| ∂mu) ≤
        ∑ _i : I, q * (U + W) := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        q * (∫ omega, |h omega - hLeave i omega| ∂mu) +
            ∫ omega, (bernoulliEventIndicator (A i) omega : ℝ) *
              |h omega - hLeave i omega| ∂mu ≤
          q * U + q * W :=
            add_le_add (mul_le_mul_of_nonneg_left (hplain i) hq) (hevent i)
        _ = q * (U + W) := by ring
    _ = (Fintype.card I : ℝ) * q * (U + W) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

/-- Multiplication by the Poisson-void Stein factor cancels a positive
intensity in a mark-replacement estimate. -/
theorem poissonVoidSteinFactor_mul_le_of_le_intensity_mul
    {lambda E R : ℝ} (hlambda : 0 < lambda) (hE : 0 ≤ E)
    (hR : R ≤ lambda * E) :
    min 1 (1 / lambda) * R ≤ E := by
  have hfactor0 : 0 ≤ min 1 (1 / lambda) :=
    poissonVoidSteinFactor_nonneg hlambda
  have hfirst : min 1 (1 / lambda) * R ≤
      min 1 (1 / lambda) * (lambda * E) :=
    mul_le_mul_of_nonneg_left hR hfactor0
  have hfactorLambda : min 1 (1 / lambda) * lambda ≤ 1 := by
    calc
      min 1 (1 / lambda) * lambda ≤ (1 / lambda) * lambda :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hlambda.le
      _ = 1 := by field_simp [hlambda.ne']
  calc
    min 1 (1 / lambda) * R ≤
        min 1 (1 / lambda) * (lambda * E) := hfirst
    _ = (min 1 (1 / lambda) * lambda) * E := by ring
    _ ≤ 1 * E := mul_le_mul_of_nonneg_right hfactorLambda hE
    _ = E := one_mul E

/-- Complete-graph specialization of the preceding two uniform mark lemmas.
The exact finite intensity cancels out of the Stein-scaled replacement cost. -/
theorem poissonVoidSteinFactor_mul_coherenceMarkReplacement_le_of_uniform
    {m p : ℕ} (x : ℝ)
    (h : GaussianCorrelationSample m p → ℝ)
    (hLeave : CorrelationEdge p → GaussianCorrelationSample m p → ℝ)
    {U W : ℝ}
    (hm : 2 ≤ m)
    (hlambda : 0 < finiteCoherenceIntensity m p x)
    (hUaddW : 0 ≤ U + W)
    (hplain : ∀ e, (∫ data, |h data - hLeave e data|
        ∂(gaussianCorrelationMeasure m p)) ≤ U)
    (hevent : ∀ e, (∫ data,
      (bernoulliEventIndicator
        (coherenceEdgeExceedanceEvent m p x e) data : ℝ) *
          |h data - hLeave e data|
        ∂(gaussianCorrelationMeasure m p)) ≤
      betaCorrelationTailProbability m p x * W) :
    min 1 (1 / finiteCoherenceIntensity m p x) *
      markedPoissonMarkReplacement
        (gaussianCorrelationMeasure m p)
        (coherenceEdgeExceedanceEvent m p x) h hLeave ≤ U + W := by
  let q := betaCorrelationTailProbability m p x
  have hprob : ∀ e : CorrelationEdge p,
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e) = q := by
    intro e
    exact coherenceEdgeExceedanceEvent_probability_eq_betaTail hm x e
  have hmark := markedPoissonMarkReplacement_le_card_mul_of_uniform
    (gaussianCorrelationMeasure m p)
    (coherenceEdgeExceedanceEvent m p x) h hLeave
    (q := q) (U := U) (W := W) measureReal_nonneg hprob hplain hevent
  rw [card_correlationEdge] at hmark
  have hintensity : finiteCoherenceIntensity m p x =
      (p.choose 2 : ℝ) * q := rfl
  apply poissonVoidSteinFactor_mul_le_of_le_intensity_mul
    hlambda hUaddW
  rw [hintensity]
  simpa [q] using hmark

/-! ## Routine bounded-mark integrability -/

/-- Measurable marks bounded by one automatically satisfy every integrability
hypothesis in the marked Poisson-void adapter.  This isolates the analytic
content from measure-theoretic bookkeeping. -/
theorem boundedMarks_markedBernoulliVoid_integrability
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I → Set Omega) (hA : ∀ i, MeasurableSet (A i))
    (B : I → Finset I) (h : Omega → ℝ)
    (hLeave : I → Omega → ℝ)
    (hlambda : 0 < markedBernoulliIntensity mu A)
    (hh : Measurable h) (hLeaveMeas : ∀ i, Measurable (hLeave i))
    (hhBound : ∀ omega, |h omega| ≤ 1)
    (hLeaveBound : ∀ i omega, |hLeave i omega| ≤ 1) :
    (∀ i, Integrable (fun omega ↦ |h omega - hLeave i omega|) mu) ∧
      MarkedBernoulliVoidChannelsIntegrable mu A B h hLeave ∧
      ∀ i, Integrable (fun omega ↦ hLeave i omega *
        poissonVoidStein (markedBernoulliIntensity mu A)
          (markedOutsideNeighborhoodCount A B i omega + 1)) mu := by
  let c := min 1 (1 / markedBernoulliIntensity mu A)
  have hc0 : 0 ≤ c := poissonVoidSteinFactor_nonneg hlambda
  have hstein : Measurable
      (poissonVoidStein (markedBernoulliIntensity mu A)) :=
    measurable_of_countable _
  have hsucc : Measurable (fun n : ℕ ↦ n + 1) :=
    measurable_of_countable _
  have hfullCount : Measurable (markedBernoulliCount A) :=
    measurable_markedBernoulliCount hA
  have hfullStein : Measurable (fun omega ↦
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedBernoulliCount A omega)) :=
    hstein.comp hfullCount
  have hfullSuccStein : Measurable (fun omega ↦
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedBernoulliCount A omega + 1)) :=
    hstein.comp (hsucc.comp hfullCount)
  have hxiMeas : ∀ i, Measurable (fun omega ↦
      (bernoulliEventIndicator (A i) omega : ℝ)) := by
    intro i
    exact (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_bernoulliEventIndicator (hA i))
  have hdiffBound : ∀ i omega, |h omega - hLeave i omega| ≤ 2 := by
    intro i omega
    calc
      |h omega - hLeave i omega| ≤ |h omega| + |hLeave i omega| :=
        abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hhBound omega) (hLeaveBound i omega)
      _ = 2 := by norm_num
  have hdiff : ∀ i,
      Integrable (fun omega ↦ |h omega - hLeave i omega|) mu := by
    intro i
    apply Integrable.of_bound
      ((hh.sub (hLeaveMeas i)).abs.aestronglyMeasurable) 2
    filter_upwards [] with omega
    simpa [Real.norm_eq_abs] using hdiffBound i omega
  have houtSteinMeas : ∀ i, Measurable (fun omega ↦
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedOutsideNeighborhoodCount A B i omega + 1)) := by
    intro i
    exact hstein.comp
      (hsucc.comp (measurable_markedOutsideNeighborhoodCount hA B i))
  have hY : ∀ i, Integrable (fun omega ↦ hLeave i omega *
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedOutsideNeighborhoodCount A B i omega + 1)) mu := by
    intro i
    apply Integrable.of_bound
      ((hLeaveMeas i).mul (houtSteinMeas i)).aestronglyMeasurable c
    filter_upwards [] with omega
    change |hLeave i omega *
      poissonVoidStein (markedBernoulliIntensity mu A)
        (markedOutsideNeighborhoodCount A B i omega + 1)| ≤ c
    rw [abs_mul]
    calc
      |hLeave i omega| *
          |poissonVoidStein (markedBernoulliIntensity mu A)
            (markedOutsideNeighborhoodCount A B i omega + 1)| ≤
          1 * c := mul_le_mul (hLeaveBound i omega)
            (abs_poissonVoidStein_le_min hlambda _) (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  refine ⟨hdiff, ?_, hY⟩
  intro i
  have hout := houtSteinMeas i
  have hxi := hxiMeas i
  have hforwardMarkMeas : Measurable
      (markedBernoulliForwardMarkTerm mu A h hLeave i) := by
    unfold markedBernoulliForwardMarkTerm
    fun_prop
  have hforwardCountMeas : Measurable
      (markedBernoulliForwardCountTerm mu A B hLeave i) := by
    unfold markedBernoulliForwardCountTerm
    fun_prop
  have hfarMeas : Measurable
      (markedBernoulliFarTerm mu A B hLeave i) := by
    unfold markedBernoulliFarTerm
    fun_prop
  have hbackwardCountMeas : Measurable
      (markedBernoulliBackwardCountTerm mu A B hLeave i) := by
    unfold markedBernoulliBackwardCountTerm
    fun_prop
  have hbackwardMarkMeas : Measurable
      (markedBernoulliBackwardMarkTerm mu A h hLeave i) := by
    unfold markedBernoulliBackwardMarkTerm
    fun_prop
  have hq0 : 0 ≤ mu.real (A i) := measureReal_nonneg
  have hq1 : mu.real (A i) ≤ 1 := measureReal_le_one
  have hxiBounds : ∀ omega,
      0 ≤ (bernoulliEventIndicator (A i) omega : ℝ) ∧
        (bernoulliEventIndicator (A i) omega : ℝ) ≤ 1 := by
    intro omega
    rcases bernoulliEventIndicator_eq_zero_or_one (A i) omega with hi | hi
    <;> simp [hi]
  have hforwardMark : Integrable
      (markedBernoulliForwardMarkTerm mu A h hLeave i) mu := by
    apply Integrable.of_bound hforwardMarkMeas.aestronglyMeasurable (4 * c)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs]
    unfold markedBernoulliForwardMarkTerm
    rw [abs_mul, abs_mul, abs_of_nonneg hq0]
    have hs := abs_poissonVoidStein_le_min hlambda
      (markedBernoulliCount A omega + 1)
    calc
      mu.real (A i) * |h omega - hLeave i omega| *
          |poissonVoidStein (markedBernoulliIntensity mu A)
            (markedBernoulliCount A omega + 1)| ≤ 1 * 2 * c := by
          gcongr
          exact hdiffBound i omega
      _ ≤ 4 * c := by nlinarith
  have hforwardCount : Integrable
      (markedBernoulliForwardCountTerm mu A B hLeave i) mu := by
    apply Integrable.of_bound hforwardCountMeas.aestronglyMeasurable (4 * c)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs]
    unfold markedBernoulliForwardCountTerm
    rw [abs_mul, abs_mul, abs_of_nonneg hq0]
    have hs1 := abs_poissonVoidStein_le_min hlambda
      (markedBernoulliCount A omega + 1)
    have hs2 := abs_poissonVoidStein_le_min hlambda
      (markedOutsideNeighborhoodCount A B i omega + 1)
    have hsdiff :
        |poissonVoidStein (markedBernoulliIntensity mu A)
              (markedBernoulliCount A omega + 1) -
            poissonVoidStein (markedBernoulliIntensity mu A)
              (markedOutsideNeighborhoodCount A B i omega + 1)| ≤
          2 * c := by
      calc
        |_ - _| ≤
            |poissonVoidStein (markedBernoulliIntensity mu A)
                (markedBernoulliCount A omega + 1)| +
              |poissonVoidStein (markedBernoulliIntensity mu A)
                (markedOutsideNeighborhoodCount A B i omega + 1)| :=
          abs_sub _ _
        _ ≤ c + c := add_le_add hs1 hs2
        _ = 2 * c := by ring
    calc
      mu.real (A i) * |hLeave i omega| * |_ - _| ≤
          1 * 1 * (2 * c) := by
            gcongr
            exact hLeaveBound i omega
      _ ≤ 4 * c := by nlinarith
  have hfar : Integrable (markedBernoulliFarTerm mu A B hLeave i) mu := by
    apply Integrable.of_bound hfarMeas.aestronglyMeasurable (4 * c)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs]
    unfold markedBernoulliFarTerm
    rw [abs_mul, abs_mul]
    have hs := abs_poissonVoidStein_le_min hlambda
      (markedOutsideNeighborhoodCount A B i omega + 1)
    have hxi0 := (hxiBounds omega).1
    have hxi1 := (hxiBounds omega).2
    have hcenter : |mu.real (A i) -
        (bernoulliEventIndicator (A i) omega : ℝ)| ≤ 2 := by
      calc
        |_ - _| ≤ |mu.real (A i)| +
            |(bernoulliEventIndicator (A i) omega : ℝ)| := abs_sub _ _
        _ ≤ 1 + 1 := by
          rw [abs_of_nonneg hq0, abs_of_nonneg hxi0]
          exact add_le_add hq1 hxi1
        _ = 2 := by norm_num
    calc
      |mu.real (A i) - (bernoulliEventIndicator (A i) omega : ℝ)| *
          |hLeave i omega| *
            |poissonVoidStein (markedBernoulliIntensity mu A)
              (markedOutsideNeighborhoodCount A B i omega + 1)| ≤
          2 * 1 * c := by
            gcongr
            exact hLeaveBound i omega
      _ ≤ 4 * c := by nlinarith
  have hbackwardCount : Integrable
      (markedBernoulliBackwardCountTerm mu A B hLeave i) mu := by
    apply Integrable.of_bound hbackwardCountMeas.aestronglyMeasurable (4 * c)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs]
    unfold markedBernoulliBackwardCountTerm
    rw [abs_mul, abs_mul]
    have hs1 := abs_poissonVoidStein_le_min hlambda
      (markedOutsideNeighborhoodCount A B i omega + 1)
    have hs2 := abs_poissonVoidStein_le_min hlambda
      (markedBernoulliCount A omega)
    have hsdiff :
        |poissonVoidStein (markedBernoulliIntensity mu A)
              (markedOutsideNeighborhoodCount A B i omega + 1) -
            poissonVoidStein (markedBernoulliIntensity mu A)
              (markedBernoulliCount A omega)| ≤ 2 * c := by
      calc
        |_ - _| ≤
            |poissonVoidStein (markedBernoulliIntensity mu A)
                (markedOutsideNeighborhoodCount A B i omega + 1)| +
              |poissonVoidStein (markedBernoulliIntensity mu A)
                (markedBernoulliCount A omega)| := abs_sub _ _
        _ ≤ c + c := add_le_add hs1 hs2
        _ = 2 * c := by ring
    have hxi0 := (hxiBounds omega).1
    have hxi1 := (hxiBounds omega).2
    rw [abs_of_nonneg hxi0]
    calc
      (bernoulliEventIndicator (A i) omega : ℝ) * |hLeave i omega| *
          |_ - _| ≤ 1 * 1 * (2 * c) := by
            gcongr
            exact hLeaveBound i omega
      _ ≤ 4 * c := by nlinarith
  have hbackwardMark : Integrable
      (markedBernoulliBackwardMarkTerm mu A h hLeave i) mu := by
    apply Integrable.of_bound hbackwardMarkMeas.aestronglyMeasurable (4 * c)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs]
    unfold markedBernoulliBackwardMarkTerm
    rw [abs_mul, abs_mul]
    have hs := abs_poissonVoidStein_le_min hlambda
      (markedBernoulliCount A omega)
    have hxi0 := (hxiBounds omega).1
    have hxi1 := (hxiBounds omega).2
    rw [abs_of_nonneg hxi0]
    calc
      (bernoulliEventIndicator (A i) omega : ℝ) *
          |hLeave i omega - h omega| *
            |poissonVoidStein (markedBernoulliIntensity mu A)
              (markedBernoulliCount A omega)| ≤
          1 * 2 * c := by
            gcongr
            simpa [abs_sub_comm] using hdiffBound i omega
      _ ≤ 4 * c := by nlinarith
  exact ⟨hforwardMark, hforwardCount, hfar, hbackwardCount, hbackwardMark⟩

/-! ## Finite marked-Stein adapter -/

/-- Fully assembled finite Gaussian adapter.  The hypotheses called
`hchannels` and `hY` are routine integrability bookkeeping for the chosen
leave-one marks.  The substantive remaining hypotheses are:

* `hindep`: decorated leave-one independence;
* `hmark`: the two one-edge mark-replacement integrals;
* `hprob`, `hpair`: the exact one-edge and adjacent two-edge forest laws.

The conclusion is already expressed relative to the exact finite intensity,
so it can be fed directly into the compact-rate assembly. -/
theorem exactIntensityJointError_le_of_gaussian_marked_adapter
    {m p : ℕ} (hadm : Admissible m p) (z x : ℝ)
    (hLeave : CorrelationEdge p → GaussianCorrelationSample m p → ℝ)
    {markError : ℝ}
    (hlambda : 0 < finiteCoherenceIntensity m p x)
    (hprob : ∀ e : CorrelationEdge p,
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e) =
          betaCorrelationTailProbability m p x)
    (hpair : ∀ e f : CorrelationEdge p,
      f ∈ (correlationEdgeNeighborhood p e).erase e →
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e ∩
          coherenceEdgeExceedanceEvent m p x f) ≤
        betaCorrelationTailProbability m p x ^ 2)
    (hLeaveBound : ∀ e data, |hLeave e data| ≤ 1)
    (hdiff : ∀ e, Integrable (fun data ↦
      |coherenceBulkLowerMark m p z data - hLeave e data|)
        (gaussianCorrelationMeasure m p))
    (hchannels : MarkedBernoulliVoidChannelsIntegrable
      (gaussianCorrelationMeasure m p)
      (coherenceEdgeExceedanceEvent m p x)
      (correlationEdgeNeighborhood p)
      (coherenceBulkLowerMark m p z) hLeave)
    (hY : ∀ e, Integrable (fun data ↦ hLeave e data *
      poissonVoidStein (finiteCoherenceIntensity m p x)
        (markedOutsideNeighborhoodCount
          (coherenceEdgeExceedanceEvent m p x)
          (correlationEdgeNeighborhood p) e data + 1))
        (gaussianCorrelationMeasure m p))
    (hindep : ∀ e, IndepFun
      (fun data ↦
        (bernoulliEventIndicator
          (coherenceEdgeExceedanceEvent m p x e) data : ℝ))
      (fun data ↦
        (hLeave e data,
          markedOutsideNeighborhoodCount
            (coherenceEdgeExceedanceEvent m p x)
            (correlationEdgeNeighborhood p) e data))
      (gaussianCorrelationMeasure m p))
    (hmark : markedPoissonMarkReplacement
      (gaussianCorrelationMeasure m p)
      (coherenceEdgeExceedanceEvent m p x)
      (coherenceBulkLowerMark m p z) hLeave ≤ markError) :
    exactIntensityJointError m p z x ≤
      provedNullLogdetKolmogorovEnvelope m p +
        min 1 (1 / finiteCoherenceIntensity m p x) *
          (markError +
            4 * (p.choose 2 : ℝ) * (p : ℝ) *
              betaCorrelationTailProbability m p x ^ 2) := by
  let mu := gaussianCorrelationMeasure m p
  let A := coherenceEdgeExceedanceEvent m p x
  let B := correlationEdgeNeighborhood p
  let h := coherenceBulkLowerMark m p z
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, gaussianCorrelationMeasure]
    infer_instance
  have hA : ∀ e, MeasurableSet (A e) := fun e ↦
    measurableSet_coherenceEdgeExceedanceEvent m p x e
  have hh : Integrable h mu := integrable_coherenceBulkLowerMark m p z
  have hiB : ∀ e, e ∈ B e := self_mem_correlationEdgeNeighborhood
  have hintensity : markedBernoulliIntensity mu A =
      finiteCoherenceIntensity m p x := by
    exact markedBernoulliIntensity_coherence_eq_finiteCoherenceIntensity
      m p x hprob
  have hagg := markedBernoulliVoid_AGG_bound
    (mu := mu) (A := A) hA B h hLeave
    (by simpa [hintensity] using hlambda) hh
    (H := 1) (by norm_num) hLeaveBound hiB hdiff hchannels
    (by simpa [hintensity] using hY) hindep
  have hlocal := coherence_markedPoissonBOne_add_BTwo_le
    m p x (measureReal_nonneg) hprob hpair
  change
    markedPoissonBOne (gaussianCorrelationMeasure m p)
        (coherenceEdgeExceedanceEvent m p x)
        (correlationEdgeNeighborhood p) +
      markedPoissonBTwo (gaussianCorrelationMeasure m p)
        (coherenceEdgeExceedanceEvent m p x)
        (correlationEdgeNeighborhood p) ≤
      4 * (p.choose 2 : ℝ) * (p : ℝ) *
        betaCorrelationTailProbability m p x ^ 2 at hlocal
  have hmarkLocal :
      markedPoissonMarkReplacement mu A h hLeave +
          (markedPoissonBOne mu A B + markedPoissonBTwo mu A B) ≤
        markError +
          4 * (p.choose 2 : ℝ) * (p : ℝ) *
            betaCorrelationTailProbability m p x ^ 2 := by
    simpa [mu, A, B, h] using add_le_add hmark hlocal
  have hfactor0 : 0 ≤ min 1 (1 / finiteCoherenceIntensity m p x) :=
    poissonVoidSteinFactor_nonneg hlambda
  have hagg' :
      |gaussianCoherenceJointLowerProbability m p z x -
        (∫ data, coherenceBulkLowerMark m p z data ∂mu) *
          Real.exp (-finiteCoherenceIntensity m p x)| ≤
        min 1 (1 / finiteCoherenceIntensity m p x) *
          (markError +
            4 * (p.choose 2 : ℝ) * (p : ℝ) *
              betaCorrelationTailProbability m p x ^ 2) := by
    rw [hintensity] at hagg
    rw [integral_coherenceBulkLowerMark_mul_void_eq_jointProbability
      hadm.1 z x] at hagg
    have haggClean := hagg
    simp only [one_mul] at haggClean
    exact haggClean.trans
      (mul_le_mul_of_nonneg_left hmarkLocal hfactor0)
  have hbulk := abs_integral_coherenceBulkLowerMark_sub_normal_le hadm z
  have hexp0 : 0 ≤ Real.exp (-finiteCoherenceIntensity m p x) :=
    (Real.exp_pos _).le
  have hexp1 : Real.exp (-finiteCoherenceIntensity m p x) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  unfold exactIntensityJointError exactIntensityJointApproximation
  have htriangle := abs_sub_le
    (gaussianCoherenceJointLowerProbability m p z x)
    ((∫ data, coherenceBulkLowerMark m p z data ∂mu) *
      Real.exp (-finiteCoherenceIntensity m p x))
    (standardNormalCDF z * Real.exp (-finiteCoherenceIntensity m p x))
  have hbulkProduct :
      |(∫ data, coherenceBulkLowerMark m p z data ∂mu) *
          Real.exp (-finiteCoherenceIntensity m p x) -
        standardNormalCDF z * Real.exp (-finiteCoherenceIntensity m p x)| ≤
      provedNullLogdetKolmogorovEnvelope m p := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hexp0]
    calc
      |(∫ data, coherenceBulkLowerMark m p z data ∂mu) -
          standardNormalCDF z| *
          Real.exp (-finiteCoherenceIntensity m p x) ≤
        provedNullLogdetKolmogorovEnvelope m p *
          Real.exp (-finiteCoherenceIntensity m p x) :=
        mul_le_mul_of_nonneg_right hbulk hexp0
      _ ≤ provedNullLogdetKolmogorovEnvelope m p * 1 :=
        mul_le_mul_of_nonneg_left hexp1
          (provedNullLogdetKolmogorovEnvelope_nonneg m p)
      _ = provedNullLogdetKolmogorovEnvelope m p := mul_one _
  calc
    |gaussianCoherenceJointLowerProbability m p z x -
        standardNormalCDF z * Real.exp (-finiteCoherenceIntensity m p x)| ≤
      |gaussianCoherenceJointLowerProbability m p z x -
        (∫ data, coherenceBulkLowerMark m p z data ∂mu) *
          Real.exp (-finiteCoherenceIntensity m p x)| +
      |(∫ data, coherenceBulkLowerMark m p z data ∂mu) *
          Real.exp (-finiteCoherenceIntensity m p x) -
        standardNormalCDF z * Real.exp (-finiteCoherenceIntensity m p x)| :=
      htriangle
    _ ≤ min 1 (1 / finiteCoherenceIntensity m p x) *
          (markError +
            4 * (p.choose 2 : ℝ) * (p : ℝ) *
              betaCorrelationTailProbability m p x ^ 2) +
        provedNullLogdetKolmogorovEnvelope m p :=
      add_le_add hagg' hbulkProduct
    _ = provedNullLogdetKolmogorovEnvelope m p +
        min 1 (1 / finiteCoherenceIntensity m p x) *
          (markError +
            4 * (p.choose 2 : ℝ) * (p : ℝ) *
              betaCorrelationTailProbability m p x ^ 2) := by ring

/-- Gaussian one-edge and adjacent-pair laws are not additional hypotheses:
they follow from the exact Beta marginal and the two-edge forest estimate.
Thus only the leave-one mark package remains in this version of the finite
adapter. -/
theorem exactIntensityJointError_le_of_gaussian_leave_adapter
    {m p : ℕ} (hadm : Admissible m p) (z x : ℝ)
    (hLeave : CorrelationEdge p → GaussianCorrelationSample m p → ℝ)
    {markError : ℝ}
    (hlambda : 0 < finiteCoherenceIntensity m p x)
    (hLeaveBound : ∀ e data, |hLeave e data| ≤ 1)
    (hdiff : ∀ e, Integrable (fun data ↦
      |coherenceBulkLowerMark m p z data - hLeave e data|)
        (gaussianCorrelationMeasure m p))
    (hchannels : MarkedBernoulliVoidChannelsIntegrable
      (gaussianCorrelationMeasure m p)
      (coherenceEdgeExceedanceEvent m p x)
      (correlationEdgeNeighborhood p)
      (coherenceBulkLowerMark m p z) hLeave)
    (hY : ∀ e, Integrable (fun data ↦ hLeave e data *
      poissonVoidStein (finiteCoherenceIntensity m p x)
        (markedOutsideNeighborhoodCount
          (coherenceEdgeExceedanceEvent m p x)
          (correlationEdgeNeighborhood p) e data + 1))
        (gaussianCorrelationMeasure m p))
    (hindep : ∀ e, IndepFun
      (fun data ↦
        (bernoulliEventIndicator
          (coherenceEdgeExceedanceEvent m p x e) data : ℝ))
      (fun data ↦
        (hLeave e data,
          markedOutsideNeighborhoodCount
            (coherenceEdgeExceedanceEvent m p x)
            (correlationEdgeNeighborhood p) e data))
      (gaussianCorrelationMeasure m p))
    (hmark : markedPoissonMarkReplacement
      (gaussianCorrelationMeasure m p)
      (coherenceEdgeExceedanceEvent m p x)
      (coherenceBulkLowerMark m p z) hLeave ≤ markError) :
    exactIntensityJointError m p z x ≤
      provedNullLogdetKolmogorovEnvelope m p +
        min 1 (1 / finiteCoherenceIntensity m p x) *
          (markError +
            4 * (p.choose 2 : ℝ) * (p : ℝ) *
              betaCorrelationTailProbability m p x ^ 2) := by
  have hm : 2 ≤ m := hadm.1.trans hadm.2
  have hprob : ∀ e : CorrelationEdge p,
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e) =
          betaCorrelationTailProbability m p x :=
    fun e ↦ coherenceEdgeExceedanceEvent_probability_eq_betaTail hm x e
  have hpair : ∀ e f : CorrelationEdge p,
      f ∈ (correlationEdgeNeighborhood p e).erase e →
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e ∩
          coherenceEdgeExceedanceEvent m p x f) ≤
        betaCorrelationTailProbability m p x ^ 2 := by
    intro e f hf
    have hfe : f ≠ e := (Finset.mem_erase.mp hf).1
    have htouch : correlationEdgesTouch e f :=
      mem_correlationEdgeNeighborhood_iff.mp (Finset.mem_of_mem_erase hf)
    exact coherenceAdjacentPair_probability_le_betaTail_sq
      hm x e f hfe.symm htouch
  exact exactIntensityJointError_le_of_gaussian_marked_adapter
    hadm z x hLeave hlambda hprob hpair hLeaveBound hdiff hchannels hY
      hindep hmark

/-- Final finite adapter form before the quantitative leave-one estimates:
measurability and boundedness of the leave mark discharge all routine
integrability obligations automatically. -/
theorem exactIntensityJointError_le_of_gaussian_measurable_leave_adapter
    {m p : ℕ} (hadm : Admissible m p) (z x : ℝ)
    (hLeave : CorrelationEdge p → GaussianCorrelationSample m p → ℝ)
    {markError : ℝ}
    (hlambda : 0 < finiteCoherenceIntensity m p x)
    (hLeaveMeas : ∀ e, Measurable (hLeave e))
    (hLeaveBound : ∀ e data, |hLeave e data| ≤ 1)
    (hindep : ∀ e, IndepFun
      (fun data ↦
        (bernoulliEventIndicator
          (coherenceEdgeExceedanceEvent m p x e) data : ℝ))
      (fun data ↦
        (hLeave e data,
          markedOutsideNeighborhoodCount
            (coherenceEdgeExceedanceEvent m p x)
            (correlationEdgeNeighborhood p) e data))
      (gaussianCorrelationMeasure m p))
    (hmark : markedPoissonMarkReplacement
      (gaussianCorrelationMeasure m p)
      (coherenceEdgeExceedanceEvent m p x)
      (coherenceBulkLowerMark m p z) hLeave ≤ markError) :
    exactIntensityJointError m p z x ≤
      provedNullLogdetKolmogorovEnvelope m p +
        min 1 (1 / finiteCoherenceIntensity m p x) *
          (markError +
            4 * (p.choose 2 : ℝ) * (p : ℝ) *
              betaCorrelationTailProbability m p x ^ 2) := by
  let mu := gaussianCorrelationMeasure m p
  let A := coherenceEdgeExceedanceEvent m p x
  let B := correlationEdgeNeighborhood p
  let h := coherenceBulkLowerMark m p z
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, gaussianCorrelationMeasure]
    infer_instance
  have hm : 2 ≤ m := hadm.1.trans hadm.2
  have hprob : ∀ e : CorrelationEdge p,
      mu.real (A e) = betaCorrelationTailProbability m p x := by
    intro e
    exact coherenceEdgeExceedanceEvent_probability_eq_betaTail hm x e
  have hintensity : markedBernoulliIntensity mu A =
      finiteCoherenceIntensity m p x := by
    exact markedBernoulliIntensity_coherence_eq_finiteCoherenceIntensity
      m p x hprob
  have hmarkedPos : 0 < markedBernoulliIntensity mu A := by
    rw [hintensity]
    exact hlambda
  have hpkg := boundedMarks_markedBernoulliVoid_integrability
    mu A (fun e ↦ measurableSet_coherenceEdgeExceedanceEvent m p x e)
      B h hLeave hmarkedPos
      (measurable_coherenceBulkLowerMark m p z) hLeaveMeas
      (abs_coherenceBulkLowerMark_le_one m p z) hLeaveBound
  rcases hpkg with ⟨hdiff, hchannels, hYmarked⟩
  have hY : ∀ e, Integrable (fun data ↦ hLeave e data *
      poissonVoidStein (finiteCoherenceIntensity m p x)
        (markedOutsideNeighborhoodCount
          (coherenceEdgeExceedanceEvent m p x)
          (correlationEdgeNeighborhood p) e data + 1))
        (gaussianCorrelationMeasure m p) := by
    intro e
    simpa [mu, A, B, hintensity] using hYmarked e
  exact exactIntensityJointError_le_of_gaussian_leave_adapter
    hadm z x hLeave hlambda hLeaveBound
      (by simpa [mu, h] using hdiff)
      (by simpa [mu, A, B, h] using hchannels)
      hY hindep hmark

/-- Quantitative finite Gaussian adapter with the intensity and complete-graph
local factors already cancelled.  Its only analytic inputs are uniform
unconditional and event-weighted one-edge mark-replacement bounds. -/
theorem exactIntensityJointError_le_of_uniform_oneEdge_replacement
    {m p : ℕ} (hadm : Admissible m p) (z x : ℝ)
    (hLeave : CorrelationEdge p → GaussianCorrelationSample m p → ℝ)
    {U W K : ℝ}
    (hlambda : 0 < finiteCoherenceIntensity m p x)
    (hlambdaK : finiteCoherenceIntensity m p x ≤ K)
    (hUaddW : 0 ≤ U + W)
    (hLeaveMeas : ∀ e, Measurable (hLeave e))
    (hLeaveBound : ∀ e data, |hLeave e data| ≤ 1)
    (hindep : ∀ e, IndepFun
      (fun data ↦
        (bernoulliEventIndicator
          (coherenceEdgeExceedanceEvent m p x e) data : ℝ))
      (fun data ↦
        (hLeave e data,
          markedOutsideNeighborhoodCount
            (coherenceEdgeExceedanceEvent m p x)
            (correlationEdgeNeighborhood p) e data))
      (gaussianCorrelationMeasure m p))
    (hplain : ∀ e, (∫ data,
      |coherenceBulkLowerMark m p z data - hLeave e data|
        ∂(gaussianCorrelationMeasure m p)) ≤ U)
    (hevent : ∀ e, (∫ data,
      (bernoulliEventIndicator
        (coherenceEdgeExceedanceEvent m p x e) data : ℝ) *
        |coherenceBulkLowerMark m p z data - hLeave e data|
        ∂(gaussianCorrelationMeasure m p)) ≤
      betaCorrelationTailProbability m p x * W) :
    exactIntensityJointError m p z x ≤
      provedNullLogdetKolmogorovEnvelope m p + (U + W) +
        16 * K / (p : ℝ) := by
  let q := betaCorrelationTailProbability m p x
  let lambda := finiteCoherenceIntensity m p x
  let markError := lambda * (U + W)
  have hm : 2 ≤ m := hadm.1.trans hadm.2
  have hprob : ∀ e : CorrelationEdge p,
      (gaussianCorrelationMeasure m p).real
        (coherenceEdgeExceedanceEvent m p x e) = q := by
    intro e
    exact coherenceEdgeExceedanceEvent_probability_eq_betaTail hm x e
  have hmarkRaw := markedPoissonMarkReplacement_le_card_mul_of_uniform
    (gaussianCorrelationMeasure m p)
    (coherenceEdgeExceedanceEvent m p x)
    (coherenceBulkLowerMark m p z) hLeave
    (q := q) (U := U) (W := W) measureReal_nonneg hprob hplain hevent
  rw [card_correlationEdge] at hmarkRaw
  have hlambdaEq : lambda = (p.choose 2 : ℝ) * q := rfl
  have hmark : markedPoissonMarkReplacement
      (gaussianCorrelationMeasure m p)
      (coherenceEdgeExceedanceEvent m p x)
      (coherenceBulkLowerMark m p z) hLeave ≤ markError := by
    change markedPoissonMarkReplacement
      (gaussianCorrelationMeasure m p)
      (coherenceEdgeExceedanceEvent m p x)
      (coherenceBulkLowerMark m p z) hLeave ≤ lambda * (U + W)
    rw [hlambdaEq]
    simpa [q] using hmarkRaw
  have hbase := exactIntensityJointError_le_of_gaussian_measurable_leave_adapter
    hadm z x hLeave (markError := markError) hlambda hLeaveMeas
      hLeaveBound hindep hmark
  have hmarkScaled : min 1 (1 / lambda) * markError ≤ U + W := by
    apply poissonVoidSteinFactor_mul_le_of_le_intensity_mul hlambda hUaddW
    exact le_rfl
  have hlocalScaled : min 1 (1 / lambda) *
      (4 * (p.choose 2 : ℝ) * (p : ℝ) * q ^ 2) ≤
        16 * K / (p : ℝ) := by
    exact min_inv_intensity_mul_completeGraphLocal_le hadm.1
      measureReal_nonneg hlambda hlambdaEq hlambdaK
  change exactIntensityJointError m p z x ≤
      provedNullLogdetKolmogorovEnvelope m p +
        min 1 (1 / lambda) *
          (markError +
            4 * (p.choose 2 : ℝ) * (p : ℝ) * q ^ 2) at hbase
  calc
    exactIntensityJointError m p z x ≤
        provedNullLogdetKolmogorovEnvelope m p +
          min 1 (1 / lambda) *
            (markError +
              4 * (p.choose 2 : ℝ) * (p : ℝ) * q ^ 2) := hbase
    _ = provedNullLogdetKolmogorovEnvelope m p +
          min 1 (1 / lambda) * markError +
          min 1 (1 / lambda) *
            (4 * (p.choose 2 : ℝ) * (p : ℝ) * q ^ 2) := by ring
    _ ≤ provedNullLogdetKolmogorovEnvelope m p + (U + W) +
          16 * K / (p : ℝ) :=
      add_le_add (add_le_add_right hmarkScaled _) hlocalScaled

end

end LogdetLean.Coherence
