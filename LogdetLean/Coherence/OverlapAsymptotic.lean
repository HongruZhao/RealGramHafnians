import LogdetLean.Coherence.FactorialExpansion
import LogdetLean.Coherence.MatchingIntensity
import LogdetLean.Coherence.OrderedForestPower
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
/-!
# The deterministic and asymptotic overlap estimate

This file closes the counting and real-analysis part of the overlap
argument.  An ordered edge tuple using exactly `v` vertices is encoded by

* an embedding of its `v` abstract vertex labels into `Fin p`, and
* a function from the `2*k` endpoint slots to `Fin v`.

Consequently there are at most

`p.descFactorial v * v ^ (2*k)`

such tuples.  Combining this bound with the spanning-forest exponent
`v / 2 + 1` for a nonmatching graph proves that the full overlap sum tends
to zero whenever the one-edge probability is of order `p⁻²`.

The model-specific task left outside this file is deliberately narrow: for
each overlapping tuple, extract and order a spanning forest and invoke
`OrderedForestIndependence` to establish the displayed per-configuration
power bound.  No graph enumeration or asymptotic summation remains after
that bound is supplied.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Module Topology
open scoped BigOperators

/-- Overlapping ordered edge tuples that use exactly `v` vertices. -/
def orderedOverlapTuplesByVertexCount (p k v : ℕ) :
    Finset (OrderedDistinctEdgeTuple p k) :=
  (orderedOverlapTuples p k).filter fun edges ↦
    (orderedEdgeVertexSet edges).card = v

/-- A tuple, together with the assertion that it uses exactly `v` vertices.
This larger type (which does not impose overlap) is convenient for the
counting injection. -/
abbrev OrderedEdgeTupleWithVertexCount (p k v : ℕ) :=
  {edges : OrderedDistinctEdgeTuple p k //
    (orderedEdgeVertexSet edges).card = v}

/-- Increasing embedding of the vertices used by a tuple into `Fin p`. -/
def tupleVertexEmbedding {p k v : ℕ}
    (edges : OrderedEdgeTupleWithVertexCount p k v) : Fin v ↪ Fin p :=
  ((orderedEdgeVertexSet edges.1).orderEmbOfFin edges.2).toEmbedding

/-- Incidence pattern of the `2*k` endpoint slots after the used vertices
have been relabeled increasingly by `Fin v`. -/
def tupleVertexPattern {p k v : ℕ}
    (edges : OrderedEdgeTupleWithVertexCount p k v) :
    Fin k × Bool → Fin v :=
  fun ib ↦
    ((orderedEdgeVertexSet edges.1).orderIsoOfFin edges.2).symm
      ⟨orderedEdgeEndpointMap edges.1 ib, by
        simp [orderedEdgeVertexSet]⟩

/-- The finite encoding used to count configurations of a fixed vertex
cardinality. -/
def tupleVertexEncoding {p k v : ℕ}
    (edges : OrderedEdgeTupleWithVertexCount p k v) :
    (Fin v ↪ Fin p) × (Fin k × Bool → Fin v) :=
  (tupleVertexEmbedding edges, tupleVertexPattern edges)

@[simp]
theorem tupleVertexEmbedding_pattern {p k v : ℕ}
    (edges : OrderedEdgeTupleWithVertexCount p k v)
    (ib : Fin k × Bool) :
    tupleVertexEmbedding edges (tupleVertexPattern edges ib) =
      orderedEdgeEndpointMap edges.1 ib := by
  have happly := ((orderedEdgeVertexSet edges.1).orderIsoOfFin edges.2).apply_symm_apply
    ⟨orderedEdgeEndpointMap edges.1 ib, by simp [orderedEdgeVertexSet]⟩
  exact congrArg Subtype.val happly

/-- The vertex-label/incidence-pattern encoding is injective. -/
theorem tupleVertexEncoding_injective {p k v : ℕ} :
    Function.Injective
      (tupleVertexEncoding : OrderedEdgeTupleWithVertexCount p k v →
        (Fin v ↪ Fin p) × (Fin k × Bool → Fin v)) := by
  intro edges edges' hencode
  have hemb : tupleVertexEmbedding edges = tupleVertexEmbedding edges' :=
    congrArg Prod.fst hencode
  have hpattern : tupleVertexPattern edges = tupleVertexPattern edges' :=
    congrArg Prod.snd hencode
  have hendpoint : orderedEdgeEndpointMap edges.1 =
      orderedEdgeEndpointMap edges'.1 := by
    funext ib
    calc
      orderedEdgeEndpointMap edges.1 ib =
          tupleVertexEmbedding edges (tupleVertexPattern edges ib) :=
        (tupleVertexEmbedding_pattern edges ib).symm
      _ = tupleVertexEmbedding edges' (tupleVertexPattern edges' ib) := by
        rw [hemb, hpattern]
      _ = orderedEdgeEndpointMap edges'.1 ib :=
        tupleVertexEmbedding_pattern edges' ib
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  apply Prod.ext
  · simpa [orderedEdgeEndpointMap, correlationEdgeEndpoint] using
      congrFun hendpoint (i, false)
  · simpa [orderedEdgeEndpointMap, correlationEdgeEndpoint] using
      congrFun hendpoint (i, true)

/-- Exact fixed-`v` configuration-count bound.  The factor
`p.descFactorial v` chooses the labeled vertices, and `v^(2*k)` bounds all
incidence patterns. -/
theorem card_orderedOverlapTuplesByVertexCount_le (p k v : ℕ) :
    (orderedOverlapTuplesByVertexCount p k v).card ≤
      p.descFactorial v * v ^ (2 * k) := by
  classical
  have hinj : Function.Injective
      (fun edges : {edges : OrderedDistinctEdgeTuple p k //
          edges ∈ orderedOverlapTuplesByVertexCount p k v} ↦
        tupleVertexEncoding
          (⟨edges.1, (Finset.mem_filter.mp edges.2).2⟩ :
            OrderedEdgeTupleWithVertexCount p k v)) := by
    intro a b hab
    have hinner := tupleVertexEncoding_injective hab
    have hval : a.1 = b.1 := congrArg
      (fun edges : OrderedEdgeTupleWithVertexCount p k v ↦ edges.1) hinner
    exact Subtype.ext hval
  calc
    (orderedOverlapTuplesByVertexCount p k v).card =
        Fintype.card {edges : OrderedDistinctEdgeTuple p k //
          edges ∈ orderedOverlapTuplesByVertexCount p k v} := by
      simp
    _ ≤ Fintype.card ((Fin v ↪ Fin p) × (Fin k × Bool → Fin v)) :=
      Fintype.card_le_of_injective _ hinj
    _ = p.descFactorial v * v ^ (2 * k) := by
      rw [Fintype.card_prod, Fintype.card_embedding_eq]
      simp [Nat.mul_comm]

/-- A slightly looser polynomial form of the configuration-count bound. -/
theorem card_orderedOverlapTuplesByVertexCount_le_pow
    {p k v : ℕ} (hv : v ≤ 2 * k) :
    (orderedOverlapTuplesByVertexCount p k v).card ≤
      p ^ v * (2 * k) ^ (2 * k) := by
  calc
    (orderedOverlapTuplesByVertexCount p k v).card ≤
        p.descFactorial v * v ^ (2 * k) :=
      card_orderedOverlapTuplesByVertexCount_le p k v
    _ ≤ p ^ v * (2 * k) ^ (2 * k) := by
      exact Nat.mul_le_mul (Nat.descFactorial_le_pow p v)
        (Nat.pow_le_pow_left hv (2 * k))

/-! ## The analytic `p^v q_p^(v/2+1)` saving -/

/-- If `p² q_p` has a finite limit, the power supplied by a nonmatching
spanning forest beats the number of `v`-vertex labelings.  The identity in
the proof exposes one or two uncancelled powers of `p` in the denominator,
depending on the parity of `v`. -/
theorem tendsto_vertexCount_mul_forestPower_zero
    (q : ℕ → ℝ) (limit : ℝ)
    (hq : Tendsto (fun p : ℕ ↦ (p : ℝ) ^ 2 * q p)
      atTop (nhds limit)) (v : ℕ) :
    Tendsto
      (fun p : ℕ ↦ (p : ℝ) ^ v * q p ^ (v / 2 + 1))
      atTop (nhds 0) := by
  let r : ℕ := v / 2 + 1
  let d : ℕ := 2 * r - v
  have hvle : v ≤ 2 * r := by
    dsimp [r]
    omega
  have hdpos : 0 < d := by
    dsimp [d, r]
    omega
  have hnum : Tendsto
      (fun p : ℕ ↦ ((p : ℝ) ^ 2 * q p) ^ r)
      atTop (nhds (limit ^ r)) := hq.pow r
  have hpcast : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun p : ℕ ↦ (p : ℝ) ^ d) atTop atTop :=
    (tendsto_pow_atTop hdpos.ne').comp hpcast
  have hratio : Tendsto
      (fun p : ℕ ↦ ((p : ℝ) ^ 2 * q p) ^ r / (p : ℝ) ^ d)
      atTop (nhds 0) := hnum.div_atTop hden
  apply hratio.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  have hvd : v + d = 2 * r := by
    dsimp [d]
    omega
  have hpowers : ((p : ℝ) ^ 2) ^ r =
      (p : ℝ) ^ v * (p : ℝ) ^ d := by
    rw [← pow_mul, ← pow_add, hvd]
  rw [mul_pow, hpowers]
  change
    ((p : ℝ) ^ v * (p : ℝ) ^ d * q p ^ r) /
        (p : ℝ) ^ d =
      (p : ℝ) ^ v * q p ^ r
  field_simp [hp0]

/-- Multiplying the preceding envelope by a fixed combinatorial constant
does not alter its zero limit. -/
theorem tendsto_vertexOverlapEnvelope_zero
    (q : ℕ → ℝ) (limit : ℝ)
    (hq : Tendsto (fun p : ℕ ↦ (p : ℝ) ^ 2 * q p)
      atTop (nhds limit)) (k v : ℕ) :
    Tendsto
      (fun p : ℕ ↦
        (p : ℝ) ^ v * ((2 * k : ℕ) : ℝ) ^ (2 * k) *
          q p ^ (v / 2 + 1))
      atTop (nhds 0) := by
  have h := tendsto_vertexCount_mul_forestPower_zero q limit hq v
  have hconst :=
    (tendsto_const_nhds : Tendsto
      (fun _p : ℕ ↦ ((2 * k : ℕ) : ℝ) ^ (2 * k))
      atTop (nhds (((2 * k : ℕ) : ℝ) ^ (2 * k))))
  have hmul := hconst.mul h
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- The finite sum of all possible vertex-count envelopes tends to zero. -/
theorem tendsto_sum_vertexOverlapEnvelope_zero
    (q : ℕ → ℝ) (limit : ℝ)
    (hq : Tendsto (fun p : ℕ ↦ (p : ℝ) ^ 2 * q p)
      atTop (nhds limit)) (k : ℕ) :
    Tendsto
      (fun p : ℕ ↦
        ∑ v ∈ Finset.range (2 * k),
          (p : ℝ) ^ v * ((2 * k : ℕ) : ℝ) ^ (2 * k) *
            q p ^ (v / 2 + 1))
      atTop (nhds 0) := by
  have hsum := tendsto_finsetSum (Finset.range (2 * k))
    (f := fun v p : ℕ ↦
      (p : ℝ) ^ v * ((2 * k : ℕ) : ℝ) ^ (2 * k) *
        q p ^ (v / 2 + 1))
    (a := fun _v ↦ (0 : ℝ))
    (fun v _hv ↦ tendsto_vertexOverlapEnvelope_zero q limit hq k v)
  simpa using hsum

/-! ## Assembly of the full overlap sum -/

/-- Once every `v`-vertex nonmatching configuration is bounded by the
spanning-forest power `q_p^(v/2+1)`, the entire ordered overlap contribution
tends to zero.  This theorem contains the complete finite counting and
asymptotic argument and applies to arbitrary nonnegative weights. -/
theorem tendsto_orderedOverlapWeight_zero_of_forestPower
    (k : ℕ) (hk : 0 < k)
    (q : ℕ → ℝ) (limit : ℝ)
    (hq : Tendsto (fun p : ℕ ↦ (p : ℝ) ^ 2 * q p)
      atTop (nhds limit))
    (w : (p : ℕ) → OrderedDistinctEdgeTuple p k → ℝ)
    (hq_nonneg : ∀ᶠ p in atTop, 0 ≤ q p)
    (hw_nonneg : ∀ᶠ p in atTop,
      ∀ edges ∈ orderedOverlapTuples p k, 0 ≤ w p edges)
    (hforest : ∀ᶠ p in atTop,
      ∀ edges ∈ orderedOverlapTuples p k,
        w p edges ≤ q p ^ ((orderedEdgeVertexSet edges).card / 2 + 1)) :
    Tendsto
      (fun p : ℕ ↦ ∑ edges ∈ orderedOverlapTuples p k, w p edges)
      atTop (nhds 0) := by
  classical
  have henvelope := tendsto_sum_vertexOverlapEnvelope_zero q limit hq k
  apply squeeze_zero'
  · filter_upwards [hw_nonneg] with p hp
    exact Finset.sum_nonneg fun edges hedges ↦ hp edges hedges
  · filter_upwards [hq_nonneg, hforest] with p hq0 hpforest
    have hmaps : ∀ edges ∈ orderedOverlapTuples p k,
        (orderedEdgeVertexSet edges).card ∈ Finset.range (2 * k) := by
      intro edges hedges
      have hoverlap : ¬edges.IsMatching :=
        (Finset.mem_filter.mp hedges).2
      have hv := orderedEdgeVertexSet_card_le_pred_of_not_matching
        edges hoverlap
      exact Finset.mem_range.mpr (by omega)
    have hgraph := overlapContribution_le_graphType_fiberBound
      p k (Finset.range (2 * k))
      (fun edges ↦ (orderedEdgeVertexSet edges).card)
      (fun v ↦ q p ^ (v / 2 + 1))
      (w p) hmaps hpforest
    calc
      (∑ edges ∈ orderedOverlapTuples p k, w p edges) ≤
          ∑ v ∈ Finset.range (2 * k),
            (((orderedOverlapTuples p k).filter fun edges ↦
                (orderedEdgeVertexSet edges).card = v).card : ℝ) *
              q p ^ (v / 2 + 1) := hgraph
      _ ≤ ∑ v ∈ Finset.range (2 * k),
          (p : ℝ) ^ v * ((2 * k : ℕ) : ℝ) ^ (2 * k) *
            q p ^ (v / 2 + 1) := by
        apply Finset.sum_le_sum
        intro v hv
        have hvle : v ≤ 2 * k :=
          (Finset.mem_range.mp hv).le
        have hcardNat :=
          card_orderedOverlapTuplesByVertexCount_le_pow
            (p := p) (k := k) hvle
        have hcardReal :
            (((orderedOverlapTuplesByVertexCount p k v).card : ℕ) : ℝ) ≤
              (p : ℝ) ^ v * ((2 * k : ℕ) : ℝ) ^ (2 * k) := by
          exact_mod_cast hcardNat
        have hpow : 0 ≤ q p ^ (v / 2 + 1) := pow_nonneg hq0 _
        change
          (((orderedOverlapTuplesByVertexCount p k v).card : ℕ) : ℝ) *
              q p ^ (v / 2 + 1) ≤
            (p : ℝ) ^ v * ((2 * k : ℕ) : ℝ) ^ (2 * k) *
              q p ^ (v / 2 + 1)
        exact mul_le_mul_of_nonneg_right hcardReal hpow
  · exact henvelope

/-- At the classical coherence threshold, the one-edge beta tail satisfies
the `p² q_p` hypothesis used by the abstract overlap theorem. -/
theorem tendsto_sq_mul_betaCorrelationTailProbability
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto
      (fun p : ℕ ↦ (p : ℝ) ^ 2 *
        betaCorrelationTailProbability (mseq p) p x)
      atTop (nhds (2 * classicalCoherenceIntensity x)) := by
  have hhalf :=
    tendsto_half_sq_mul_betaCorrelationTailProbability hadm x
  have htwo :=
    (tendsto_const_nhds : Tendsto (fun _p : ℕ ↦ (2 : ℝ))
      atTop (nhds 2)).mul hhalf
  apply htwo.congr'
  filter_upwards [] with p
  ring

/-- Model-level overlap conclusion, reduced to the sole remaining
configurationwise spanning-forest probability bound.  In particular, the
bulk event in `orderedTupleJointEvent` costs nothing here: it is already
included in the nonnegative weight and may only decrease its probability. -/
theorem tendsto_gaussianOrderedTupleJoint_overlap_zero_of_forestPower
    (k : ℕ) (hk : 0 < k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (z x : ℝ)
    (hforest : ∀ᶠ p in atTop,
      ∀ edges ∈ orderedOverlapTuples p k,
        (nestedProductMeasure
            (stdGaussian (ObservationSpace (mseq p + 1))) p).real
            (orderedTupleJointEvent classicalCoherenceThreshold
              (mseq p) p k z x edges) ≤
          betaCorrelationTailProbability (mseq p) p x ^
            ((orderedEdgeVertexSet edges).card / 2 + 1)) :
    Tendsto
      (fun p : ℕ ↦
        ∑ edges ∈ orderedOverlapTuples p k,
          (nestedProductMeasure
              (stdGaussian (ObservationSpace (mseq p + 1))) p).real
              (orderedTupleJointEvent classicalCoherenceThreshold
                (mseq p) p k z x edges))
      atTop (nhds 0) := by
  apply tendsto_orderedOverlapWeight_zero_of_forestPower
    k hk
    (fun p ↦ betaCorrelationTailProbability (mseq p) p x)
    (2 * classicalCoherenceIntensity x)
    (tendsto_sq_mul_betaCorrelationTailProbability hadm x)
    (fun p edges ↦
      (nestedProductMeasure
          (stdGaussian (ObservationSpace (mseq p + 1))) p).real
          (orderedTupleJointEvent classicalCoherenceThreshold
            (mseq p) p k z x edges))
  · exact Eventually.of_forall fun p ↦ measureReal_nonneg
  · exact Eventually.of_forall fun p edges _hedges ↦ measureReal_nonneg
  · exact hforest

end

end LogdetLean.Coherence
