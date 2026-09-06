import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import LogdetLean.Coherence.ConditionedRetainedTail
/-!
# Joint prefix--tail law under a prefix event

This module packages the exact finite-dimensional law that will feed the
varying-law Slutsky theorem.  The first coordinate is the retained-prefix
log determinant at the full normalization; the second coordinate is the
deleted Bartlett tail.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

universe u

/-- A lifted prefix event has exactly the mass of the original prefix event.
All appended coordinates have probability laws. -/
theorem retainedPrefixTailProductMeasure_apply_prefixEvent
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ]
    (ν : ℕ → Measure β) [hνs : ∀ n, SFinite (ν n)]
    (q r : ℕ)
    (hνp : ∀ j, j < r → IsProbabilityMeasure (ν (q + j)))
    (s : Set (NestedTuple α q)) (hs : MeasurableSet s) :
    retainedPrefixTailProductMeasure μ ν q r
        (retainedPrefixEvent (β := β) q r s) =
      nestedProductMeasure μ q s := by
  induction r with
  | zero => rfl
  | succ r ih =>
      letI : IsProbabilityMeasure (ν (q + r)) := hνp r (by omega)
      rw [retainedPrefixTailProductMeasure, retainedPrefixEvent,
        Measure.prod_prod]
      rw [ih (fun j hj ↦ hνp j (by omega))]
      simp

/-- The event in the original raw Gaussian space obtained by requiring a
measurable condition on the first `q` centered columns. -/
def centeredGaussianPrefixEvent
    (m q r : ℕ)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q)) :
    Set (NestedTuple (ObservationSpace (m + 1)) (q + r)) :=
  centeredRetainedPrefixTailFactors (m + 1) q r ⁻¹'
    retainedPrefixEvent (β := ℝ) q r s

theorem measurableSet_centeredGaussianPrefixEvent
    (m q r : ℕ)
    {s : Set (NestedTuple (centeredSubspace (m + 1)) q)}
    (hs : MeasurableSet s) :
    MeasurableSet (centeredGaussianPrefixEvent m q r s) :=
  (measurableSet_retainedPrefixEvent q r hs).preimage
    (measurable_centeredRetainedPrefixTailFactors (m + 1) q r)

/-- The raw lifted event has exactly the probability of its centered
Gaussian prefix event. -/
theorem centeredGaussianPrefixEvent_probability
    (m q r : ℕ) (hqr : q + r ≤ m)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s) :
    nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r)
        (centeredGaussianPrefixEvent m q r s) =
      nestedProductMeasure
        (stdGaussian (centeredSubspace (m + 1))) q s := by
  let F := centeredRetainedPrefixTailFactors (m + 1) q r
  let S := retainedPrefixEvent (β := ℝ) q r s
  have hF : Measurable F :=
    measurable_centeredRetainedPrefixTailFactors (m + 1) q r
  have hS : MeasurableSet S := measurableSet_retainedPrefixEvent q r hs
  calc
    nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r)
        (centeredGaussianPrefixEvent m q r s) =
      Measure.map F
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) (q + r)) S := by
        rw [Measure.map_apply hF hS]
        rfl
    _ = retainedPrefixTailProductMeasure
          (stdGaussian (centeredSubspace (m + 1)))
          (gaussianGramSchmidtFactorMeasure m) q r S := by
        rw [map_centeredRetainedPrefixTailFactors_succ_eq_product m q r hqr]
    _ = nestedProductMeasure
          (stdGaussian (centeredSubspace (m + 1))) q s := by
        apply retainedPrefixTailProductMeasure_apply_prefixEvent
        · intro j hj
          exact isProbabilityMeasure_gaussianGramSchmidtFactorMeasure
            (by omega)
        · exact hs

/-- The conditional raw Gaussian law, bundled as a probability measure.
Positivity is checked on the lower-dimensional prefix law. -/
def conditionedCenteredGaussianPrefixProbabilityMeasure
    (m q r : ℕ) (hqr : q + r ≤ m)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    ProbabilityMeasure
      (NestedTuple (ObservationSpace (m + 1)) (q + r)) := by
  let μ := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) (q + r)
  let A := centeredGaussianPrefixEvent m q r s
  have hA0 : μ A ≠ 0 := by
    rw [centeredGaussianPrefixEvent_probability m q r hqr s hs]
    exact hs0
  exact ⟨μ[|A], cond_isProbabilityMeasure hA0⟩

/-- Recover the retained prefix from a prefix followed by `r` tail
coordinates. -/
def retainedPrefixProjection
    {α β : Type u} (q : ℕ) :
    (r : ℕ) → RetainedPrefixTailTuple α β q r → NestedTuple α q
  | 0, z => z
  | r + 1, z => retainedPrefixProjection q r z.1

theorem measurable_retainedPrefixProjection
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q : ℕ) : ∀ r,
    Measurable (retainedPrefixProjection (α := α) (β := β) q r) := by
  intro r
  induction r with
  | zero => exact measurable_id
  | succ r ih => exact ih.comp measurable_fst

theorem retainedPrefixProjection_centeredRetainedPrefixTailFactors
    (m q : ℕ) : ∀ r
      (z : NestedTuple (ObservationSpace (m + 1)) (q + r)),
    retainedPrefixProjection q r
        (centeredRetainedPrefixTailFactors (m + 1) q r z) =
      nestedTuplePrefix q r (centerNested (m + 1) (q + r) z) := by
  intro r
  induction r with
  | zero => intro z; rfl
  | succ r ih =>
      intro z
      exact ih z.1

/-- The two coordinates used in the conditional Slutsky step. -/
def centeredGaussianPrefixTailPairStatistic
    (m q r : ℕ) :
    NestedTuple (ObservationSpace (m + 1)) (q + r) → ℝ × ℝ :=
  fun z ↦
    (standardizedCenteredPrefixLogDetAtFullScale m q (q + r)
        (nestedTuplePrefix q r (centerNested (m + 1) (q + r) z)),
      standardizedGaussianRetainedTailStatistic m q r z)

/-- Measurability of the normalized retained-prefix statistic. -/
theorem measurable_standardizedCenteredPrefixLogDetAtFullScale
    (m q p : ℕ) :
    Measurable (standardizedCenteredPrefixLogDetAtFullScale m q p) := by
  unfold standardizedCenteredPrefixLogDetAtFullScale nestedNormalizedGramDet
  exact ((((measurable_det_normalizedGram
    (E := centeredSubspace (m + 1)) q).comp
      (measurable_nestedTupleToFin q)).log.sub measurable_const).div_const _)

/-- The prefix operation on ordinary nested tuples is measurable. -/
theorem measurable_nestedTuplePrefix
    {α : Type} [MeasurableSpace α] (q : ℕ) : ∀ r,
    Measurable (nestedTuplePrefix (E := α) q r) := by
  intro r
  induction r with
  | zero => exact measurable_id
  | succ r ih => exact ih.comp measurable_fst

theorem measurable_centeredGaussianPrefixTailPairStatistic
    (m q r : ℕ) :
    Measurable (centeredGaussianPrefixTailPairStatistic m q r) := by
  unfold centeredGaussianPrefixTailPairStatistic
  apply Measurable.prodMk
  · exact (measurable_standardizedCenteredPrefixLogDetAtFullScale m q (q + r)).comp
      ((measurable_nestedTuplePrefix
        (α := centeredSubspace (m + 1)) q r).comp
          (measurable_centerNested (m + 1) (q + r)))
  · unfold standardizedGaussianRetainedTailStatistic
    exact (measurable_standardizedRetainedTailLogStatistic m q r).comp
      (measurable_centeredRetainedPrefixTailFactors (m + 1) q r)

/-- Under prefix conditioning, the second marginal of the joint
prefix--tail statistic is exactly the deleted-tail law. -/
theorem map_snd_centeredGaussianPrefixTailPair_cond
    (m q r : ℕ) (hq : 1 ≤ q) (hqr : q + r ≤ m)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    Measure.map Prod.snd
        (Measure.map (centeredGaussianPrefixTailPairStatistic m q r)
          ((conditionedCenteredGaussianPrefixProbabilityMeasure
            m q r hqr s hs hs0 : ProbabilityMeasure _) : Measure _)) =
      standardizedDeletedTailLaw m q (q + r) := by
  rw [Measure.map_map measurable_snd
    (measurable_centeredGaussianPrefixTailPairStatistic m q r)]
  change Measure.map (standardizedGaussianRetainedTailStatistic m q r)
      ((nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r))[|
          centeredGaussianPrefixEvent m q r s]) = _
  exact map_standardizedGaussianRetainedTailStatistic_cond_prefixEvent
    m q r hq hqr s hs hs0

/-- Adding the two coordinates of the conditional joint law gives exactly
the conditional law of the actual standardized log determinant. -/
theorem map_add_centeredGaussianPrefixTailPair_cond_eq_map_Z0mp
    (m q r : ℕ) (hqr : q + r ≤ m)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    Measure.map (fun x : ℝ × ℝ ↦ x.1 + x.2)
        (Measure.map (centeredGaussianPrefixTailPairStatistic m q r)
          ((conditionedCenteredGaussianPrefixProbabilityMeasure
            m q r hqr s hs hs0 : ProbabilityMeasure _) : Measure _)) =
      Measure.map (Z0mpStatistic m (q + r))
        ((conditionedCenteredGaussianPrefixProbabilityMeasure
          m q r hqr s hs hs0 : ProbabilityMeasure _) : Measure _) := by
  let μ : Measure
      (NestedTuple (ObservationSpace (m + 1)) (q + r)) :=
    (conditionedCenteredGaussianPrefixProbabilityMeasure
      m q r hqr s hs hs0 : ProbabilityMeasure _)
  calc
    Measure.map (fun x : ℝ × ℝ ↦ x.1 + x.2)
        (Measure.map (centeredGaussianPrefixTailPairStatistic m q r) μ) =
      Measure.map
        ((fun x : ℝ × ℝ ↦ x.1 + x.2) ∘
          centeredGaussianPrefixTailPairStatistic m q r) μ :=
        Measure.map_map (measurable_fst.add measurable_snd)
          (measurable_centeredGaussianPrefixTailPairStatistic m q r)
    _ = Measure.map (Z0mpStatistic m (q + r)) μ := by
      apply Measure.map_congr
      have h := ae_Z0mpStatistic_eq_prefix_add_tail_cond hqr
        (centeredGaussianPrefixEvent m q r s)
      filter_upwards [h] with z hz
      simpa [centeredGaussianPrefixTailPairStatistic,
        Function.comp_apply] using hz.symm

end

end LogdetLean.Coherence
