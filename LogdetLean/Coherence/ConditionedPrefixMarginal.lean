import LogdetLean.Coherence.ConditionedJointLaw
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
/-!
# The retained prefix marginal after prefix conditioning

The deleted-tail law is unchanged by a prefix event.  Complementarily, the
first marginal of the conditioned prefix--tail pair is exactly the original
prefix law conditioned on that event.  This module proves the identity first
for the abstract retained product and then transports it back to the centered
Gaussian sample space.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

universe u

/-- Appending probability-distributed tail coordinates and then forgetting
them leaves the retained-prefix law unchanged. -/
theorem map_retainedPrefixProjection_fromPrefix
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q : ℕ)
    (ξ : Measure (NestedTuple α q)) [SFinite ξ]
    (ν : ℕ → Measure β) [hνs : ∀ n, SFinite (ν n)] : ∀ r,
    (∀ j, j < r → IsProbabilityMeasure (ν (q + j))) →
    Measure.map (retainedPrefixProjection (α := α) (β := β) q r)
        (retainedTailProductFromPrefix q ξ ν r) = ξ := by
  intro r
  induction r with
  | zero =>
      intro _hνp
      simp [retainedPrefixProjection, retainedTailProductFromPrefix]
  | succ r ih =>
      intro hνp
      letI : IsProbabilityMeasure (ν (q + r)) := hνp r (by omega)
      change Measure.map
          (retainedPrefixProjection (α := α) (β := β) q r ∘ Prod.fst)
          ((retainedTailProductFromPrefix q ξ ν r).prod (ν (q + r))) = ξ
      rw [← Measure.map_map
        (measurable_retainedPrefixProjection (α := α) (β := β) q r)
        measurable_fst]
      rw [Measure.map_fst_prod]
      simpa using ih (fun j hj ↦ hνp j (by omega))

/-- On the exact retained product, conditioning on a lifted prefix event and
then projecting to the prefix gives the ordinary conditioned prefix law. -/
theorem map_retainedPrefixProjection_cond_prefixEvent
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ]
    (ν : ℕ → Measure β) [hνs : ∀ n, SFinite (ν n)]
    (q r : ℕ)
    (hνp : ∀ j, j < r → IsProbabilityMeasure (ν (q + j)))
    (s : Set (NestedTuple α q)) :
    Measure.map (retainedPrefixProjection (α := α) (β := β) q r)
        ((retainedPrefixTailProductMeasure μ ν q r)[|
          retainedPrefixEvent (β := β) q r s]) =
      (nestedProductMeasure μ q)[|s] := by
  rw [cond_retainedPrefixTailProductMeasure_prefixEvent μ ν q r
    hνp s]
  exact map_retainedPrefixProjection_fromPrefix q
    ((nestedProductMeasure μ q)[|s]) ν r hνp

/-- The actual centered prefix extracted from raw Gaussian columns has,
after conditioning on a prefix event, exactly the centered Gaussian product
law conditioned on that event. -/
theorem map_centeredGaussianPrefix_cond_prefixEvent
    (m q r : ℕ) (hqr : q + r ≤ m)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s) :
    Measure.map
        (fun z : NestedTuple (ObservationSpace (m + 1)) (q + r) ↦
          nestedTuplePrefix q r (centerNested (m + 1) (q + r) z))
        ((nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) (q + r))[|
            centeredGaussianPrefixEvent m q r s]) =
      (nestedProductMeasure
        (stdGaussian (centeredSubspace (m + 1))) q)[|s] := by
  let F := centeredRetainedPrefixTailFactors (m + 1) q r
  let P := retainedPrefixProjection
    (α := centeredSubspace (m + 1)) (β := ℝ) q r
  have hF : Measurable F :=
    measurable_centeredRetainedPrefixTailFactors (m + 1) q r
  have hP : Measurable P :=
    measurable_retainedPrefixProjection
      (α := centeredSubspace (m + 1)) (β := ℝ) q r
  have hS : MeasurableSet (retainedPrefixEvent (β := ℝ) q r s) :=
    measurableSet_retainedPrefixEvent q r hs
  have hcomp :
      (fun z : NestedTuple (ObservationSpace (m + 1)) (q + r) ↦
        nestedTuplePrefix q r (centerNested (m + 1) (q + r) z)) =
        P ∘ F := by
    funext z
    exact (retainedPrefixProjection_centeredRetainedPrefixTailFactors
      m q r z).symm
  rw [hcomp, ← Measure.map_map hP hF]
  change Measure.map P
      (Measure.map F
        ((nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) (q + r))[|
            F ⁻¹' retainedPrefixEvent (β := ℝ) q r s])) = _
  rw [map_cond_preimage _ hF hS]
  rw [map_centeredRetainedPrefixTailFactors_succ_eq_product m q r hqr]
  exact map_retainedPrefixProjection_cond_prefixEvent
    (stdGaussian (centeredSubspace (m + 1)))
    (gaussianGramSchmidtFactorMeasure m)
    q r
    (fun j hj ↦ isProbabilityMeasure_gaussianGramSchmidtFactorMeasure
      (by omega)) s

/-- The first marginal of the conditioned Gaussian prefix--tail pair is the
standardized retained-prefix statistic under the conditioned prefix law. -/
theorem map_fst_centeredGaussianPrefixTailPair_cond
    (m q r : ℕ) (hqr : q + r ≤ m)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    Measure.map Prod.fst
        (Measure.map (centeredGaussianPrefixTailPairStatistic m q r)
          ((conditionedCenteredGaussianPrefixProbabilityMeasure
            m q r hqr s hs hs0 : ProbabilityMeasure _) : Measure _)) =
      Measure.map (standardizedCenteredPrefixLogDetAtFullScale
          m q (q + r))
        ((nestedProductMeasure
          (stdGaussian (centeredSubspace (m + 1))) q)[|s]) := by
  rw [Measure.map_map measurable_fst
    (measurable_centeredGaussianPrefixTailPairStatistic m q r)]
  change Measure.map
      ((standardizedCenteredPrefixLogDetAtFullScale m q (q + r)) ∘
        (fun z : NestedTuple (ObservationSpace (m + 1)) (q + r) ↦
          nestedTuplePrefix q r (centerNested (m + 1) (q + r) z)))
      ((nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r))[|
          centeredGaussianPrefixEvent m q r s]) = _
  let g : NestedTuple (ObservationSpace (m + 1)) (q + r) →
      NestedTuple (centeredSubspace (m + 1)) q :=
    fun z ↦ nestedTuplePrefix q r (centerNested (m + 1) (q + r) z)
  have hg : Measurable g :=
    (measurable_nestedTuplePrefix
      (α := centeredSubspace (m + 1)) q r).comp
        (measurable_centerNested (m + 1) (q + r))
  have hf :=
    measurable_standardizedCenteredPrefixLogDetAtFullScale m q (q + r)
  change Measure.map
      (standardizedCenteredPrefixLogDetAtFullScale m q (q + r) ∘ g)
      ((nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r))[|
          centeredGaussianPrefixEvent m q r s]) = _
  calc
    _ = Measure.map (standardizedCenteredPrefixLogDetAtFullScale m q (q + r))
        (Measure.map g
          ((nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) (q + r))[|
              centeredGaussianPrefixEvent m q r s])) :=
      (Measure.map_map hf hg).symm
    _ = Measure.map (standardizedCenteredPrefixLogDetAtFullScale m q (q + r))
        ((nestedProductMeasure
          (stdGaussian (centeredSubspace (m + 1))) q)[|s]) := by
      rw [show Measure.map g
          ((nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) (q + r))[|
              centeredGaussianPrefixEvent m q r s]) =
          (nestedProductMeasure
            (stdGaussian (centeredSubspace (m + 1))) q)[|s] by
        exact map_centeredGaussianPrefix_cond_prefixEvent m q r hqr s hs]

end

end LogdetLean.Coherence
