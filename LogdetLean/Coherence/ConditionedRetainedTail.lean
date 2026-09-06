import LogdetLean.Coherence.ConditionalProduct
import LogdetLean.Coherence.PrefixTailDeterminantDecomposition
import LogdetLean.WishartLogDetMoments
/-!
# Conditioning a retained prefix leaves the deleted tail unchanged

The retained-prefix Bartlett theorem gives an iterated product whose first
coordinate is the actual Gaussian prefix and whose later coordinates are the
independent beta factors.  This file makes the conditioning consequence
fully explicit.

We first replace the prefix law by an arbitrary measure, lift a prefix event
through all later product coordinates, and prove the exact conditional
measure identity.  We then project away the prefix.  If the conditioning
event has positive probability, the projected tail law is exactly unchanged.
The final corollary applies this fact to the standardized deleted log-beta
tail used in `FiniteDeletionCLT`.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

universe u w

/-- Build the retained-tail product over an arbitrary law for the already
assembled prefix.  The later coordinates have laws `ν q, ..., ν (q+r-1)`.
-/
def retainedTailProductFromPrefix
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q : ℕ) (ξ : Measure (NestedTuple α q)) (ν : ℕ → Measure β) :
    (r : ℕ) → Measure (RetainedPrefixTailTuple α β q r)
  | 0 => ξ
  | r + 1 => (retainedTailProductFromPrefix q ξ ν r).prod (ν (q + r))

instance retainedTailProductFromPrefix_sFinite
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q : ℕ)
    (ξ : Measure (NestedTuple α q)) [SFinite ξ]
    (ν : ℕ → Measure β) [hν : ∀ n, SFinite (ν n)] (r : ℕ) :
    SFinite (retainedTailProductFromPrefix q ξ ν r) := by
  induction r with
  | zero =>
      simp only [retainedTailProductFromPrefix]
      infer_instance
  | succ r ih =>
      let _ : SFinite (retainedTailProductFromPrefix q ξ ν r) := ih
      let _ : SFinite (ν (q + r)) := hν (q + r)
      simp only [retainedTailProductFromPrefix]
      infer_instance

instance retainedTailProductFromPrefix_isProbability
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q : ℕ)
    (ξ : Measure (NestedTuple α q)) [IsProbabilityMeasure ξ]
    (ν : ℕ → Measure β) [hν : ∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ) : IsProbabilityMeasure
      (retainedTailProductFromPrefix q ξ ν r) := by
  induction r with
  | zero =>
      simp only [retainedTailProductFromPrefix]
      infer_instance
  | succ r ih =>
      let _ : IsProbabilityMeasure
          (retainedTailProductFromPrefix q ξ ν r) := ih
      let _ : IsProbabilityMeasure (ν (q + r)) := hν (q + r)
      simp only [retainedTailProductFromPrefix]
      infer_instance

/-- The original retained-prefix product is the construction above with the
ordinary `q`-fold product as its prefix law. -/
theorem retainedPrefixTailProductMeasure_eq_fromPrefix
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : ℕ → Measure β) (q r : ℕ) :
    retainedPrefixTailProductMeasure μ ν q r =
      retainedTailProductFromPrefix q (nestedProductMeasure μ q) ν r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [retainedPrefixTailProductMeasure,
        retainedTailProductFromPrefix, ih]

/-- Lift an event depending only on the retained prefix through `r` appended
tail coordinates. -/
def retainedPrefixEvent
    {α β : Type u} (q : ℕ) :
    (r : ℕ) → Set (NestedTuple α q) →
      Set (RetainedPrefixTailTuple α β q r)
  | 0, s => s
  | r + 1, s => retainedPrefixEvent q r s ×ˢ Set.univ

/-- A measurable prefix event remains measurable after it is lifted through
any finite number of tail coordinates. -/
theorem measurableSet_retainedPrefixEvent
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q r : ℕ) {s : Set (NestedTuple α q)} (hs : MeasurableSet s) :
    MeasurableSet (retainedPrefixEvent (β := β) q r s) := by
  induction r with
  | zero => exact hs
  | succ r ih =>
      simpa only [retainedPrefixEvent] using ih.prod MeasurableSet.univ

/-- Conditioning the retained product on a lifted prefix event changes only
the prefix law.  This identity is exact even for a null event; in that case
both sides use mathlib's totalized zero conditional measure. -/
theorem cond_retainedPrefixTailProductMeasure_prefixEvent
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ]
    (ν : ℕ → Measure β) [hνs : ∀ n, SFinite (ν n)]
    (q r : ℕ)
    (hνp : ∀ j, j < r → IsProbabilityMeasure (ν (q + j)))
    (s : Set (NestedTuple α q)) :
    (retainedPrefixTailProductMeasure μ ν q r)[|
        retainedPrefixEvent (β := β) q r s] =
      retainedTailProductFromPrefix
        q ((nestedProductMeasure μ q)[|s]) ν r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      letI : IsProbabilityMeasure (ν (q + r)) := hνp r (by omega)
      rw [retainedPrefixTailProductMeasure, retainedPrefixEvent,
        cond_prod_prod_univ]
      rw [ih (fun j hj ↦ hνp j (by omega))]
      rfl

/-- Forget the retained prefix and keep only the `r` appended tail
coordinates. -/
def retainedTailProjection
    {α β : Type u} (q : ℕ) :
    (r : ℕ) → RetainedPrefixTailTuple α β q r → NestedTuple β r
  | 0, _ => ULift.up Unit.unit
  | r + 1, z => (retainedTailProjection q r z.1, z.2)

/-- The tail projection is measurable. -/
theorem measurable_retainedTailProjection
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q : ℕ) : ∀ r, Measurable (retainedTailProjection (α := α) (β := β) q r) := by
  intro r
  induction r with
  | zero => exact measurable_const
  | succ r ih => exact (ih.comp measurable_fst).prodMk measurable_snd

/-- Projecting away a probability-distributed prefix gives exactly the
iterated product law of the tail coordinates. -/
theorem map_retainedTailProjection_fromPrefix
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q : ℕ)
    (ξ : Measure (NestedTuple α q)) [SFinite ξ] [IsProbabilityMeasure ξ]
    (ν : ℕ → Measure β) [hνs : ∀ n, SFinite (ν n)]
    : ∀ r,
    Measure.map (retainedTailProjection (α := α) (β := β) q r)
        (retainedTailProductFromPrefix q ξ ν r) =
      nestedProductMeasureFamily (fun j ↦ ν (q + j)) r := by
  intro r
  induction r with
  | zero =>
      rw [retainedTailProductFromPrefix, nestedProductMeasureFamily]
      simp only [retainedTailProjection]
      rw [Measure.map_const]
      simp
  | succ r ih =>
      change Measure.map
          (Prod.map (retainedTailProjection (α := α) (β := β) q r) id)
          ((retainedTailProductFromPrefix q ξ ν r).prod (ν (q + r))) = _
      rw [← Measure.map_prod_map _ _
        (measurable_retainedTailProjection
          (α := α) (β := β) q r) measurable_id]
      simp only [Measure.map_id, ih, nestedProductMeasureFamily]

/-- Every measurable tail-only statistic has the same law after conditioning
on a positive-probability prefix event. -/
theorem map_tailOnly_cond_prefixEvent_eq_unconditioned
    {α β : Type u} {γ : Type w}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ] [IsProbabilityMeasure μ]
    (ν : ℕ → Measure β) [hνs : ∀ n, SFinite (ν n)]
    (q r : ℕ)
    (hνp : ∀ j, j < r → IsProbabilityMeasure (ν (q + j)))
    (s : Set (NestedTuple α q))
    (hs0 : nestedProductMeasure μ q s ≠ 0)
    (f : NestedTuple β r → γ) (hf : Measurable f) :
    Measure.map (f ∘ retainedTailProjection (α := α) (β := β) q r)
        ((retainedPrefixTailProductMeasure μ ν q r)[|
          retainedPrefixEvent (β := β) q r s]) =
      Measure.map (f ∘ retainedTailProjection (α := α) (β := β) q r)
        (retainedPrefixTailProductMeasure μ ν q r) := by
  haveI : IsProbabilityMeasure ((nestedProductMeasure μ q)[|s]) :=
    cond_isProbabilityMeasure hs0
  rw [cond_retainedPrefixTailProductMeasure_prefixEvent μ ν q r hνp s]
  rw [retainedPrefixTailProductMeasure_eq_fromPrefix]
  rw [show f ∘ retainedTailProjection (α := α) (β := β) q r =
      f ∘ retainedTailProjection (α := α) (β := β) q r by rfl]
  rw [← Measure.map_map hf
      (measurable_retainedTailProjection (α := α) (β := β) q r),
    map_retainedTailProjection_fromPrefix q]
  rw [← Measure.map_map hf
      (measurable_retainedTailProjection (α := α) (β := β) q r),
    map_retainedTailProjection_fromPrefix q]

/-- Logarithmic sum on a tuple containing only the tail coordinates. -/
def tailCoordinateLogSum : (r : ℕ) → NestedTuple ℝ r → ℝ
  | 0, _ => 0
  | r + 1, z => tailCoordinateLogSum r z.1 + Real.log z.2

/-- The logarithmic sum of the tail coordinates is measurable. -/
theorem measurable_tailCoordinateLogSum : ∀ r,
    Measurable (tailCoordinateLogSum r) := by
  intro r
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
      exact (ih.comp measurable_fst).add (Real.measurable_log.comp measurable_snd)

/-- The retained-tail log sum factors exactly through the tail projection. -/
theorem retainedTailLogSum_eq_tailCoordinateLogSum_projection
    {α : Type} (q : ℕ) : ∀ r (z : RetainedPrefixTailTuple α ℝ q r),
    retainedTailLogSum q r z =
      tailCoordinateLogSum r (retainedTailProjection q r z) := by
  intro r
  induction r with
  | zero => intro z; rfl
  | succ r ih =>
      intro z
      simp only [retainedTailLogSum, tailCoordinateLogSum,
        retainedTailProjection, ih z.1]

/-- The standardized retained-tail statistic also factors through the tail
projection. -/
theorem standardizedRetainedTailLogStatistic_eq_comp_projection
    (m q r : ℕ) :
    standardizedRetainedTailLogStatistic m q r =
      (fun y : NestedTuple ℝ r ↦
        (tailCoordinateLogSum r y - deletedTailCenter m q (q + r)) /
          Real.sqrt (nullVariance m (q + r))) ∘
        retainedTailProjection q r := by
  funext z
  unfold standardizedRetainedTailLogStatistic
  simp only [Function.comp_apply]
  rw [retainedTailLogSum_eq_tailCoordinateLogSum_projection]

/-- **Exact conditional deleted-tail law.**  Conditioning the retained
Gaussian prefix on any positive-probability event leaves the standardized
deleted log-beta tail law exactly unchanged. -/
theorem map_standardizedRetainedTailLogStatistic_cond_prefixEvent
    (m q r : ℕ) (hq : 1 ≤ q) (hqr : q + r ≤ m)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs0 : nestedProductMeasure
        (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    Measure.map (standardizedRetainedTailLogStatistic m q r)
        ((retainedPrefixTailProductMeasure
          (stdGaussian (centeredSubspace (m + 1)))
          (gaussianGramSchmidtFactorMeasure m) q r)[|
            retainedPrefixEvent (β := ℝ) q r s]) =
      standardizedDeletedTailLaw m q (q + r) := by
  rw [standardizedRetainedTailLogStatistic_eq_comp_projection]
  rw [map_tailOnly_cond_prefixEvent_eq_unconditioned
    (μ := stdGaussian (centeredSubspace (m + 1)))
    (ν := gaussianGramSchmidtFactorMeasure m) (q := q) (r := r)
    (hνp := fun j hj ↦ isProbabilityMeasure_gaussianGramSchmidtFactorMeasure
      (by omega)) (s := s) (hs0 := hs0)
    (f := fun y : NestedTuple ℝ r ↦
      (tailCoordinateLogSum r y - deletedTailCenter m q (q + r)) /
        Real.sqrt (nullVariance m (q + r)))
    (hf := ((measurable_tailCoordinateLogSum r).sub measurable_const).div_const _)]
  rw [← standardizedRetainedTailLogStatistic_eq_comp_projection]
  exact map_standardizedRetainedTailLogStatistic_eq_deletedTailLaw
    m q r hq hqr

/-- Raw-Gaussian-space form of the exact conditional deleted-tail law.  The
conditioning event is the preimage of a measurable retained-prefix event
under the centered Bartlett factorization map. -/
theorem map_standardizedGaussianRetainedTailStatistic_cond_prefixEvent
    (m q r : ℕ) (hq : 1 ≤ q) (hqr : q + r ≤ m)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s)
    (hs0 : nestedProductMeasure
        (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    Measure.map (standardizedGaussianRetainedTailStatistic m q r)
        ((nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) (q + r))[|
            centeredRetainedPrefixTailFactors (m + 1) q r ⁻¹'
              retainedPrefixEvent (β := ℝ) q r s]) =
      standardizedDeletedTailLaw m q (q + r) := by
  unfold standardizedGaussianRetainedTailStatistic
  rw [← Measure.map_map
    (measurable_standardizedRetainedTailLogStatistic m q r)
    (measurable_centeredRetainedPrefixTailFactors (m + 1) q r)]
  rw [map_cond_preimage _
    (measurable_centeredRetainedPrefixTailFactors (m + 1) q r)
    (measurableSet_retainedPrefixEvent q r hs)]
  rw [map_centeredRetainedPrefixTailFactors_succ_eq_product m q r hqr]
  exact map_standardizedRetainedTailLogStatistic_cond_prefixEvent
    m q r hq hqr s hs0

/-- The exact additive decomposition of the full standardized log determinant
continues to hold almost surely under conditioning on any event, because a
conditional measure is absolutely continuous with respect to its source. -/
theorem ae_Z0mpStatistic_eq_prefix_add_tail_cond
    {m q r : ℕ} (hqr : q + r ≤ m)
    (s : Set (NestedTuple (ObservationSpace (m + 1)) (q + r))) :
    ∀ᵐ z ∂(nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r))[|s],
      Z0mpStatistic m (q + r) z =
        standardizedCenteredPrefixLogDetAtFullScale m q (q + r)
          (nestedTuplePrefix q r (centerNested (m + 1) (q + r) z)) +
        standardizedGaussianRetainedTailStatistic m q r z :=
  cond_absolutelyContinuous.ae_le
    (ae_Z0mpStatistic_eq_prefix_add_standardizedGaussianRetainedTail hqr)

end

end LogdetLean.Coherence
