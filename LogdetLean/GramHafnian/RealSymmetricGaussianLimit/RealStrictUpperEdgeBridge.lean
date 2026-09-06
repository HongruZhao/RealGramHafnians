import LogdetLean.GramHafnian.RealSymmetricGaussianLimit.RealEdgeGramCLT
/-!
# Strict-upper coordinates and unordered real edges

The central limit theorem is most conveniently proved with coordinates
indexed by ordered pairs `i < j`, whereas the independent-edge symmetric
Gaussian hafnian is defined on two-element finite subsets.  This file gives
the canonical equivalence, transports the standard Gaussian law across it,
and exposes the continuous decoded hafnian.
-/

open MeasureTheory ProbabilityTheory
open scoped Real RealInnerProductSpace

namespace LogdetLean.GramHafnian.RealSymmetricGaussianLimit

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Send an ordered strict-upper pair to its underlying unordered edge. -/
def realStrictUpperPairToEdge {N : ℕ} (p : RealStrictUpperPair N) :
    Edge (Fin N) :=
  edgeOfNe p.1.1 p.1.2 p.ne

theorem realStrictUpperPairToEdge_injective {N : ℕ} :
    Function.Injective
      (realStrictUpperPairToEdge : RealStrictUpperPair N → Edge (Fin N)) := by
  intro p q hpq
  have hval := congrArg Subtype.val hpq
  change ({p.1.1, p.1.2} : Finset (Fin N)) = {q.1.1, q.1.2} at hval
  have hset : ({p.1.1, p.1.2} : Set (Fin N)) =
      {q.1.1, q.1.2} := by
    simpa using congrArg
      (fun s : Finset (Fin N) ↦ (s : Set (Fin N))) hval
  have hcases :
      (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) ∨
        (p.1.1 = q.1.2 ∧ p.1.2 = q.1.1) := by
    exact Set.pair_eq_pair_iff.mp hset
  rcases hcases with hsame | hswap
  · apply Subtype.ext
    exact Prod.ext hsame.1 hsame.2
  · have hp := p.2
    have hq := q.2
    omega

theorem realStrictUpperPairToEdge_surjective {N : ℕ} :
    Function.Surjective
      (realStrictUpperPairToEdge : RealStrictUpperPair N → Edge (Fin N)) := by
  intro e
  rcases Finset.card_eq_two.mp e.2 with ⟨i, j, hij, he⟩
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · refine ⟨⟨(i, j), hijlt⟩, ?_⟩
    apply Subtype.ext
    simpa [realStrictUpperPairToEdge, edgeOfNe] using he.symm
  · refine ⟨⟨(j, i), hjilt⟩, ?_⟩
    apply Subtype.ext
    simpa [realStrictUpperPairToEdge, edgeOfNe, Finset.pair_comm] using he.symm

/-- The canonical equivalence between strict-upper coordinates and unordered
edges. -/
def realStrictUpperPairEdgeEquiv (N : ℕ) :
    RealStrictUpperPair N ≃ Edge (Fin N) :=
  Equiv.ofBijective realStrictUpperPairToEdge
    ⟨realStrictUpperPairToEdge_injective,
      realStrictUpperPairToEdge_surjective⟩

@[simp] theorem realStrictUpperPairEdgeEquiv_apply
    {N : ℕ} (p : RealStrictUpperPair N) :
    realStrictUpperPairEdgeEquiv N p = realStrictUpperPairToEdge p := rfl

/-- Decode a Euclidean strict-upper vector as unordered real edge data. -/
def realEdgesOfStrictUpper (N : ℕ) (y : RealStrictUpperSpace N) :
    Edge (Fin N) → ℝ :=
  fun e ↦ y ((realStrictUpperPairEdgeEquiv N).symm e)

@[fun_prop] theorem continuous_realEdgesOfStrictUpper (N : ℕ) :
    Continuous (realEdgesOfStrictUpper N) := by
  unfold realEdgesOfStrictUpper
  fun_prop

@[fun_prop] theorem measurable_realEdgesOfStrictUpper (N : ℕ) :
    Measurable (realEdgesOfStrictUpper N) :=
  (continuous_realEdgesOfStrictUpper N).measurable

/-- Decoding the standard Euclidean Gaussian produces exactly the literal
independent standard real Gaussian edge product law. -/
theorem map_stdGaussian_realEdgesOfStrictUpper (N : ℕ) :
    (stdGaussian (RealStrictUpperSpace N)).map
        (realEdgesOfStrictUpper N) =
      realEdgeGaussian (Fin N) := by
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (measurable_realEdgesOfStrictUpper N) (by fun_prop)]
  change (standardRealGaussianProduct (RealStrictUpperPair N)).map
      (fun x : RealStrictUpperPair N → ℝ ↦
        fun e ↦ x ((realStrictUpperPairEdgeEquiv N).symm e)) =
    standardRealGaussianProduct (Edge (Fin N))
  exact (measurePreserving_standardRealGaussianProduct_restrict
    (realStrictUpperPairEdgeEquiv N).symm.toEmbedding).map_eq

/-- The limiting hafnian as a continuous polynomial of strict-upper
Euclidean coordinates. -/
def realStrictUpperHafnian (n : ℕ)
    (y : RealStrictUpperSpace (2 * n)) : ℝ :=
  realEdgeHafnian (realEdgesOfStrictUpper (2 * n) y)

@[fun_prop] theorem continuous_realStrictUpperHafnian (n : ℕ) :
    Continuous (realStrictUpperHafnian n) :=
  continuous_realEdgeHafnian.comp (continuous_realEdgesOfStrictUpper (2 * n))

@[fun_prop] theorem measurable_realStrictUpperHafnian (n : ℕ) :
    Measurable (realStrictUpperHafnian n) :=
  (continuous_realStrictUpperHafnian n).measurable

/-- The pushforward law of the decoded limiting hafnian is exactly the
independent-edge real symmetric Gaussian hafnian law. -/
theorem map_stdGaussian_realStrictUpperHafnian (n : ℕ) :
    (stdGaussian (RealStrictUpperSpace (2 * n))).map
        (realStrictUpperHafnian n) =
      (realEdgeGaussian (Fin (2 * n))).map realEdgeHafnian := by
  unfold realStrictUpperHafnian
  change (stdGaussian (RealStrictUpperSpace (2 * n))).map
      (realEdgeHafnian ∘ realEdgesOfStrictUpper (2 * n)) =
    (realEdgeGaussian (Fin (2 * n))).map realEdgeHafnian
  rw [← Measure.map_map measurable_realEdgeHafnian
    (measurable_realEdgesOfStrictUpper (2 * n))]
  rw [map_stdGaussian_realEdgesOfStrictUpper]

end

end LogdetLean.GramHafnian.RealSymmetricGaussianLimit
