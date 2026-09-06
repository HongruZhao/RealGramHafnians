import LogdetLean.Coherence.ConditionedPrefixMarginal
import LogdetLean.Coherence.ModelAndTargets
import Mathlib.Probability.Independence.Basic
/-!
# Canonical-edge versus decorated-tail independence

This module isolates the exact finite-dimensional independence statement
needed by a decorated Stein--Chen argument.  The canonical edge uses the
first two Gaussian columns.  The decoration consists of the standardized
Bartlett tail after those columns and the exceedance count formed only from
the remaining columns.

The elementary prefix/tail splitting and the abstract constant-conditional-
law bridge are proved without assumptions.  The one genuinely geometric
input is named separately: the joint law of the Bartlett tail and the remote
count must be independent of the particular two-dimensional Gaussian prefix.
This is stronger than either marginal invariance and is the exact adapter to
be supplied by orthogonal invariance.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-! ## Splitting a right-nested iid tuple -/

/-- Append a right-nested tail to a retained prefix. -/
def nestedTupleAppend {α : Type} (q : ℕ)
    (pref : NestedTuple α q) :
    ∀ r : ℕ, NestedTuple α r → NestedTuple α (q + r)
  | 0, _ => pref
  | r + 1, z => (nestedTupleAppend q pref r z.1, z.2)

/-- Extract the final `r` coordinates after a prefix of length `q`. -/
def nestedTupleTail {α : Type} (q : ℕ) :
    ∀ r : ℕ, NestedTuple α (q + r) → NestedTuple α r
  | 0, _ => ULift.up Unit.unit
  | r + 1, z => (nestedTupleTail q r z.1, z.2)

theorem measurable_nestedTupleAppend
    {α : Type} [MeasurableSpace α] (q : ℕ)
    (pref : NestedTuple α q) :
    ∀ r : ℕ, Measurable (nestedTupleAppend q pref r) := by
  intro r
  induction r with
  | zero => exact measurable_const
  | succ r ih => exact (ih.comp measurable_fst).prodMk measurable_snd

/-- Joint measurability when both the prefix and the tail vary. -/
theorem measurable_uncurry_nestedTupleAppend
    {α : Type} [MeasurableSpace α] (q : ℕ) :
    ∀ r : ℕ, Measurable (fun z : NestedTuple α q × NestedTuple α r ↦
      nestedTupleAppend q z.1 r z.2) := by
  intro r
  induction r with
  | zero => exact measurable_fst
  | succ r ih =>
      exact (ih.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_snd)

theorem measurable_nestedTupleTail
    {α : Type} [MeasurableSpace α] (q : ℕ) :
    ∀ r : ℕ, Measurable (nestedTupleTail (α := α) q r) := by
  intro r
  induction r with
  | zero => exact measurable_const
  | succ r ih => exact (ih.comp measurable_fst).prodMk measurable_snd

@[simp] theorem nestedTupleAppend_prefix_tail
    {α : Type} (q : ℕ) :
    ∀ r : ℕ, ∀ z : NestedTuple α (q + r),
      nestedTupleAppend q (nestedTuplePrefix q r z) r
          (nestedTupleTail q r z) = z := by
  intro r
  induction r with
  | zero => intro z; rfl
  | succ r ih =>
      rintro ⟨z, x⟩
      simp only [nestedTuplePrefix, nestedTupleTail, nestedTupleAppend]
      rw [ih z]

/-- The measurable prefix/tail splitting map. -/
def nestedTupleSplit {α : Type} (q r : ℕ) :
    NestedTuple α (q + r) → NestedTuple α q × NestedTuple α r :=
  fun z ↦ (nestedTuplePrefix q r z, nestedTupleTail q r z)

theorem measurable_nestedTupleSplit
    {α : Type} [MeasurableSpace α] (q r : ℕ) :
    Measurable (nestedTupleSplit (α := α) q r) := by
  exact (measurable_nestedTuplePrefix q r).prodMk
    (measurable_nestedTupleTail q r)

/-- Splitting an iid nested tuple gives the ordinary product of its prefix
and tail laws. -/
theorem map_nestedTupleSplit_nestedProductMeasure
    {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (q : ℕ) :
    ∀ r : ℕ,
      Measure.map (nestedTupleSplit (α := α) q r)
          (nestedProductMeasure μ (q + r)) =
        (nestedProductMeasure μ q).prod (nestedProductMeasure μ r) := by
  intro r
  induction r with
  | zero =>
      simp only [nestedTupleSplit, nestedTuplePrefix, nestedTupleTail,
        Nat.add_zero, nestedProductMeasure]
      exact (Measure.prod_dirac
        (μ := nestedProductMeasure μ q) (ULift.up Unit.unit)).symm
  | succ r ih =>
      let split : NestedTuple α (q + r) →
          NestedTuple α q × NestedTuple α r := nestedTupleSplit q r
      have hsplit : Measurable split := measurable_nestedTupleSplit q r
      have hfun :
          nestedTupleSplit (α := α) q (r + 1) =
            MeasurableEquiv.prodAssoc ∘ Prod.map split id := by
        funext z
        rcases z with ⟨z, x⟩
        rfl
      rw [hfun, ← Measure.map_map
        MeasurableEquiv.prodAssoc.measurable (hsplit.prodMap measurable_id)]
      change Measure.map MeasurableEquiv.prodAssoc
          (Measure.map (Prod.map split id)
            ((nestedProductMeasure μ (q + r)).prod μ)) =
        (nestedProductMeasure μ q).prod
          ((nestedProductMeasure μ r).prod μ)
      rw [← Measure.map_prod_map _ _ hsplit measurable_id]
      rw [ih, Measure.map_id, Measure.prodAssoc_prod]

/-! ## An abstract constant-conditional-law bridge -/

/-- If the conditional law of a decorated tail is the same for almost every
prefix, then every measurable prefix statistic is independent of that
decoration.  This is the exact skew-product principle used below. -/
theorem indepFun_prefix_decorated_of_ae_map_eq
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (X : α → γ) (Y : α → β → δ)
    (hX : Measurable X) (hY : Measurable (Function.uncurry Y))
    (κ : ProbabilityMeasure δ)
    (hmap : ∀ᵐ a ∂μ, Measure.map (Y a) ν = κ) :
    IndepFun (fun z : α × β ↦ X z.1)
      (fun z : α × β ↦ Y z.1 z.2) (μ.prod ν) := by
  let ξ : Measure γ := Measure.map X μ
  letI : IsProbabilityMeasure ξ :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hXmp : MeasurePreserving X μ ξ := ⟨hX, rfl⟩
  have hpair : Measurable
      (fun z : α × β ↦ (X z.1, Y z.1 z.2)) :=
    (hX.comp measurable_fst).prodMk hY
  have hjoint : Measure.map
      (fun z : α × β ↦ (X z.1, Y z.1 z.2)) (μ.prod ν) =
        ξ.prod κ := (hXmp.skew_product hY hmap).map_eq
  have hfirst : Measure.map (fun z : α × β ↦ X z.1) (μ.prod ν) = ξ := by
    calc
      Measure.map (fun z : α × β ↦ X z.1) (μ.prod ν) =
          Measure.map X (Measure.map Prod.fst (μ.prod ν)) := by
            rw [Measure.map_map hX measurable_fst]
            rfl
      _ = Measure.map X μ := by rw [Measure.map_fst_prod]; simp
      _ = ξ := rfl
  have hsecond : Measure.map (fun z : α × β ↦ Y z.1 z.2) (μ.prod ν) = κ := by
    calc
      Measure.map (fun z : α × β ↦ Y z.1 z.2) (μ.prod ν) =
          Measure.map
            (Prod.snd ∘ fun z : α × β ↦ (X z.1, Y z.1 z.2))
            (μ.prod ν) := by rfl
      _ =
          Measure.map Prod.snd
            (Measure.map (fun z : α × β ↦ (X z.1, Y z.1 z.2))
              (μ.prod ν)) := by
            exact (Measure.map_map measurable_snd hpair).symm
      _ = Measure.map Prod.snd (ξ.prod κ) := by rw [hjoint]
      _ = κ := by rw [Measure.map_snd_prod]; simp
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hX.comp measurable_fst).aemeasurable hY.aemeasurable).2
  change Measure.map (fun z : α × β ↦ (X z.1, Y z.1 z.2)) (μ.prod ν) =
    (Measure.map (fun z : α × β ↦ X z.1) (μ.prod ν)).prod
      (Measure.map (fun z : α × β ↦ Y z.1 z.2) (μ.prod ν))
  rw [hfirst, hsecond]
  exact hjoint

/-- Independence transports backward through a measurable map with the
specified pushforward law. -/
theorem IndepFun.comp_of_map_eq
    {Ω α β γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure α} [IsProbabilityMeasure ν]
    {F : Ω → α} {X : α → β} {Y : α → γ}
    (hXY : IndepFun X Y ν)
    (hF : Measurable F) (hX : Measurable X) (hY : Measurable Y)
    (hmap : Measure.map F μ = ν) :
    IndepFun (X ∘ F) (Y ∘ F) μ := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hX.comp hF).aemeasurable (hY.comp hF).aemeasurable).2
  calc
    Measure.map (fun ω ↦ ((X ∘ F) ω, (Y ∘ F) ω)) μ =
        Measure.map (fun a ↦ (X a, Y a)) (Measure.map F μ) := by
          rw [Measure.map_map (hX.prodMk hY) hF]
          rfl
    _ = Measure.map (fun a ↦ (X a, Y a)) ν := by rw [hmap]
    _ = (Measure.map X ν).prod (Measure.map Y ν) :=
      hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
    _ = (Measure.map X (Measure.map F μ)).prod
          (Measure.map Y (Measure.map F μ)) := by rw [hmap]
    _ = (Measure.map (X ∘ F) μ).prod (Measure.map (Y ∘ F) μ) := by
      rw [Measure.map_map hX hF, Measure.map_map hY hF]

/-! ## Model-specific canonical edge and remote decoration -/

/-- The canonical edge `(0,1)` in a two-column prefix. -/
def canonicalEdgeInTwo : Fin 2 × Fin 2 :=
  (⟨0, by omega⟩, ⟨1, by omega⟩)

/-- Indicator that the canonical first edge crosses the full
`p=2+r` coherence threshold. -/
def canonicalEdgeExceedanceIndicatorOnPrefix
    (m r : ℕ) (x : ℝ)
    (pref : NestedTuple (ObservationSpace (m + 1)) 2) : ℕ :=
  if classicalCoherenceThreshold m (2 + r) x <
      scaledSquaredCorrelationScore m 2 pref canonicalEdgeInTwo
    then 1 else 0

theorem measurable_canonicalEdgeExceedanceIndicatorOnPrefix
    (m r : ℕ) (x : ℝ) :
    Measurable (canonicalEdgeExceedanceIndicatorOnPrefix m r x) := by
  unfold canonicalEdgeExceedanceIndicatorOnPrefix
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      (measurable_scaledSquaredCorrelationScore m 2 canonicalEdgeInTwo)
  · exact measurable_const
  · exact measurable_const

/-- The canonical edge indicator on all `2+r` raw columns. -/
def canonicalEdgeExceedanceIndicator
    (m r : ℕ) (x : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) (2 + r)) : ℕ :=
  canonicalEdgeExceedanceIndicatorOnPrefix m r x
    (nestedTuplePrefix 2 r data)

theorem measurable_canonicalEdgeExceedanceIndicator
    (m r : ℕ) (x : ℝ) :
    Measurable (canonicalEdgeExceedanceIndicator m r x) :=
  (measurable_canonicalEdgeExceedanceIndicatorOnPrefix m r x).comp
    (measurable_nestedTuplePrefix 2 r)

/-- Number of coherence-threshold exceedances using only the `r` columns
whose full indices are at least two.  The score is local to those columns,
while the threshold retains the full dimension `2+r`. -/
def remoteCoherenceExceedanceCount
    (m r : ℕ) (x : ℝ)
    (tail : NestedTuple (ObservationSpace (m + 1)) r) : ℕ :=
  ∑ e ∈ correlationEdges r,
    if classicalCoherenceThreshold m (2 + r) x <
        scaledSquaredCorrelationScore m r tail e then 1 else 0

theorem measurable_remoteCoherenceExceedanceCount
    (m r : ℕ) (x : ℝ) :
    Measurable (remoteCoherenceExceedanceCount m r x) := by
  unfold remoteCoherenceExceedanceCount
  apply Finset.measurable_sum
  intro e he
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      (measurable_scaledSquaredCorrelationScore m r e)
  · exact measurable_const
  · exact measurable_const

/-- Remote count read from the last `r` coordinates of the complete data. -/
def remoteCoherenceExceedanceCountOnFull
    (m r : ℕ) (x : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) (2 + r)) : ℕ :=
  remoteCoherenceExceedanceCount m r x (nestedTupleTail 2 r data)

theorem measurable_remoteCoherenceExceedanceCountOnFull
    (m r : ℕ) (x : ℝ) :
    Measurable (remoteCoherenceExceedanceCountOnFull m r x) :=
  (measurable_remoteCoherenceExceedanceCount m r x).comp
    (measurable_nestedTupleTail 2 r)

/-- The canonical edge is unconditionally independent of the remote count.
This is the easy marginal statement: the two variables use disjoint blocks
of iid Gaussian columns. -/
theorem canonicalEdgeExceedanceIndicator_indep_remoteCount
    (m r : ℕ) (x : ℝ) :
    IndepFun (canonicalEdgeExceedanceIndicator m r x)
      (remoteCoherenceExceedanceCountOnFull m r x)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) := by
  let μpref := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) 2
  let μtail := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) r
  letI : IsProbabilityMeasure
      (stdGaussian (ObservationSpace (m + 1))) :=
    ProbabilityTheory.isProbabilityMeasure_stdGaussian
  letI : IsProbabilityMeasure μpref := by
    dsimp [μpref]
    exact nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) 2
  letI : IsProbabilityMeasure μtail := by
    dsimp [μtail]
    exact nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) r
  letI : IsProbabilityMeasure
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) :=
    nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) (2 + r)
  have hprod : IndepFun
      (fun z : NestedTuple (ObservationSpace (m + 1)) 2 ×
          NestedTuple (ObservationSpace (m + 1)) r ↦
        canonicalEdgeExceedanceIndicatorOnPrefix m r x z.1)
      (fun z ↦ remoteCoherenceExceedanceCount m r x z.2)
      (μpref.prod μtail) :=
    indepFun_prod
      (measurable_canonicalEdgeExceedanceIndicatorOnPrefix m r x)
      (measurable_remoteCoherenceExceedanceCount m r x)
  let F := nestedTupleSplit
    (α := ObservationSpace (m + 1)) 2 r
  have hF : Measurable F := measurable_nestedTupleSplit 2 r
  have hmap : Measure.map F
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) =
      μpref.prod μtail :=
    map_nestedTupleSplit_nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) 2 r
  have hcomp := IndepFun.comp_of_map_eq hprod hF
    ((measurable_canonicalEdgeExceedanceIndicatorOnPrefix m r x).comp
      measurable_fst)
    ((measurable_remoteCoherenceExceedanceCount m r x).comp
      measurable_snd) hmap
  change IndepFun
    (fun data ↦ canonicalEdgeExceedanceIndicatorOnPrefix m r x
      (nestedTuplePrefix 2 r data))
    (fun data ↦ remoteCoherenceExceedanceCount m r x
      (nestedTupleTail 2 r data))
    (nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) (2 + r))
  simpa [F, μpref, μtail, nestedTupleSplit, Function.comp_def]
    using hcomp

/-- The requested decoration: retained standardized Bartlett tail paired
with the remote exceedance count. -/
def canonicalDecoratedTail
    (m r : ℕ) (x : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) (2 + r)) : ℝ × ℕ :=
  (standardizedGaussianRetainedTailStatistic m 2 r data,
    remoteCoherenceExceedanceCountOnFull m r x data)

theorem measurable_canonicalDecoratedTail
    (m r : ℕ) (x : ℝ) :
    Measurable (canonicalDecoratedTail m r x) := by
  apply Measurable.prodMk
  · unfold standardizedGaussianRetainedTailStatistic
    exact (measurable_standardizedRetainedTailLogStatistic m 2 r).comp
      (measurable_centeredRetainedPrefixTailFactors (m + 1) 2 r)
  · exact measurable_remoteCoherenceExceedanceCountOnFull m r x

/-- Decorated tail with the two raw prefix columns held fixed. -/
def canonicalDecoratedTailGivenPrefix
    (m r : ℕ) (x : ℝ)
    (pref : NestedTuple (ObservationSpace (m + 1)) 2)
    (tail : NestedTuple (ObservationSpace (m + 1)) r) : ℝ × ℕ :=
  (standardizedGaussianRetainedTailStatistic m 2 r
      (nestedTupleAppend 2 pref r tail),
    remoteCoherenceExceedanceCount m r x tail)

theorem measurable_uncurry_canonicalDecoratedTailGivenPrefix
    (m r : ℕ) (x : ℝ) :
    Measurable (Function.uncurry
      (canonicalDecoratedTailGivenPrefix m r x)) := by
  apply Measurable.prodMk
  · unfold standardizedGaussianRetainedTailStatistic
    exact ((measurable_standardizedRetainedTailLogStatistic m 2 r).comp
      (measurable_centeredRetainedPrefixTailFactors (m + 1) 2 r)).comp
        (measurable_uncurry_nestedTupleAppend 2 r)
  · exact (measurable_remoteCoherenceExceedanceCount m r x).comp measurable_snd

/-- For almost every two-column Gaussian prefix, the joint law of the
Bartlett tail and the remote count is the same probability law.  This is a
proposition to prove, not an axiom. -/
def CanonicalDecoratedTailLawInvariant (m r : ℕ) (x : ℝ) : Prop :=
  ∃ κ : ProbabilityMeasure (ℝ × ℕ),
    ∀ᵐ pref ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) 2,
      Measure.map (canonicalDecoratedTailGivenPrefix m r x pref)
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) r) = κ

/-! ## Reduction of the geometric adapter to the centered space -/

/-- The scaled squared-correlation score written directly on centered
columns. -/
def centeredScaledSquaredCorrelationScore
    (m r : ℕ)
    (tail : NestedTuple (centeredSubspace (m + 1)) r)
    (e : Fin r × Fin r) : ℝ :=
  (m : ℝ) *
    (normalizedGram (nestedTupleToFin r tail) e.1 e.2) ^ 2

theorem measurable_centeredScaledSquaredCorrelationScore
    (m r : ℕ) (e : Fin r × Fin r) :
    Measurable (fun tail ↦
      centeredScaledSquaredCorrelationScore m r tail e) := by
  unfold centeredScaledSquaredCorrelationScore
  have hentry : Measurable (fun tail :
      NestedTuple (centeredSubspace (m + 1)) r ↦
      normalizedGram (nestedTupleToFin r tail) e.1 e.2) :=
    (measurable_pi_apply e.2).comp
      ((measurable_pi_apply e.1).comp
        (measurable_normalizedGramFamily.comp
          (measurable_nestedTupleToFin r)))
  exact measurable_const.mul (hentry.pow_const 2)

/-- The remote count after all columns have already been centered. -/
def centeredRemoteCoherenceExceedanceCount
    (m r : ℕ) (x : ℝ)
    (tail : NestedTuple (centeredSubspace (m + 1)) r) : ℕ :=
  ∑ e ∈ correlationEdges r,
    if classicalCoherenceThreshold m (2 + r) x <
        centeredScaledSquaredCorrelationScore m r tail e then 1 else 0

theorem measurable_centeredRemoteCoherenceExceedanceCount
    (m r : ℕ) (x : ℝ) :
    Measurable (centeredRemoteCoherenceExceedanceCount m r x) := by
  unfold centeredRemoteCoherenceExceedanceCount
  apply Finset.measurable_sum
  intro e he
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      (measurable_centeredScaledSquaredCorrelationScore m r e)
  · exact measurable_const
  · exact measurable_const

/-- The raw remote count factors pointwise through coordinatewise
centering. -/
theorem remoteCoherenceExceedanceCount_eq_centered
    (m r : ℕ) (x : ℝ)
    (tail : NestedTuple (ObservationSpace (m + 1)) r) :
    remoteCoherenceExceedanceCount m r x tail =
      centeredRemoteCoherenceExceedanceCount m r x
        (centerNested (m + 1) r tail) := by
  rfl

/-- Centering commutes with appending a tail to a retained prefix. -/
theorem centerNested_nestedTupleAppend
    (N q : ℕ) : ∀ r
    (pref : NestedTuple (ObservationSpace N) q)
    (tail : NestedTuple (ObservationSpace N) r),
    centerNested N (q + r) (nestedTupleAppend q pref r tail) =
      nestedTupleAppend q (centerNested N q pref) r
        (centerNested N r tail) := by
  intro r
  induction r with
  | zero =>
      intro pref tail
      rfl
  | succ r ih =>
      intro pref tail
      rcases tail with ⟨tail, y⟩
      simp only [nestedTupleAppend, centerNested]
      apply Prod.ext
      · exact ih pref tail
      · rfl

/-- The same decorated statistic entirely inside the centered Gaussian
subspace.  This is the natural object on which orthogonal invariance acts. -/
def centeredCanonicalDecoratedTailGivenPrefix
    (m r : ℕ) (x : ℝ)
    (pref : NestedTuple (centeredSubspace (m + 1)) 2)
    (tail : NestedTuple (centeredSubspace (m + 1)) r) : ℝ × ℕ :=
  (standardizedRetainedTailLogStatistic m 2 r
      (retainedPrefixTailStatistic
        (nestedNormalizedGramFactor
          (E := centeredSubspace (m + 1))) 2 r
        (nestedTupleAppend 2 pref r tail)),
    centeredRemoteCoherenceExceedanceCount m r x tail)

theorem measurable_centeredCanonicalDecoratedTailGivenPrefix
    (m r : ℕ) (x : ℝ)
    (pref : NestedTuple (centeredSubspace (m + 1)) 2) :
    Measurable (centeredCanonicalDecoratedTailGivenPrefix m r x pref) := by
  apply Measurable.prodMk
  · exact (measurable_standardizedRetainedTailLogStatistic m 2 r).comp
      ((measurable_retainedPrefixTailStatistic
        (nestedNormalizedGramFactor
          (E := centeredSubspace (m + 1)))
        measurable_uncurry_nestedNormalizedGramFactor 2 r).comp
          (measurable_nestedTupleAppend 2 pref r))
  · exact measurable_centeredRemoteCoherenceExceedanceCount m r x

/-- Holding the raw prefix fixed and then centering the random tail gives
exactly the centered-space decoration. -/
theorem canonicalDecoratedTailGivenPrefix_eq_centered
    (m r : ℕ) (x : ℝ)
    (pref : NestedTuple (ObservationSpace (m + 1)) 2)
    (tail : NestedTuple (ObservationSpace (m + 1)) r) :
    canonicalDecoratedTailGivenPrefix m r x pref tail =
      centeredCanonicalDecoratedTailGivenPrefix m r x
        (centerNested (m + 1) 2 pref)
        (centerNested (m + 1) r tail) := by
  apply Prod.ext
  · unfold canonicalDecoratedTailGivenPrefix
    unfold centeredCanonicalDecoratedTailGivenPrefix
    unfold standardizedGaussianRetainedTailStatistic
    unfold centeredRetainedPrefixTailFactors
    simp only [Function.comp_apply, Prod.fst]
    rw [centerNested_nestedTupleAppend]
  · exact remoteCoherenceExceedanceCount_eq_centered m r x tail

/-- Exact pushforward reduction from a raw fixed prefix to its centered
prefix. -/
theorem map_canonicalDecoratedTailGivenPrefix_eq_centered
    (m r : ℕ) (x : ℝ)
    (pref : NestedTuple (ObservationSpace (m + 1)) 2) :
    Measure.map (canonicalDecoratedTailGivenPrefix m r x pref)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) r) =
      Measure.map
        (centeredCanonicalDecoratedTailGivenPrefix m r x
          (centerNested (m + 1) 2 pref))
        (nestedProductMeasure
          (stdGaussian (centeredSubspace (m + 1))) r) := by
  let g := centeredCanonicalDecoratedTailGivenPrefix m r x
    (centerNested (m + 1) 2 pref)
  have hg : Measurable g :=
    measurable_centeredCanonicalDecoratedTailGivenPrefix m r x _
  have hc : Measurable (centerNested (m + 1) r) :=
    measurable_centerNested (m + 1) r
  rw [show canonicalDecoratedTailGivenPrefix m r x pref =
      g ∘ centerNested (m + 1) r by
    funext tail
    exact canonicalDecoratedTailGivenPrefix_eq_centered m r x pref tail]
  rw [← Measure.map_map hg hc]
  rw [map_centerNested_nestedProductMeasure]

/-- Pure centered-space version of the remaining orthogonal-invariance
adapter. -/
def CenteredCanonicalDecoratedTailLawInvariant
    (m r : ℕ) (x : ℝ) : Prop :=
  ∃ κ : ProbabilityMeasure (ℝ × ℕ),
    ∀ᵐ pref ∂nestedProductMeasure
        (stdGaussian (centeredSubspace (m + 1))) 2,
      Measure.map
          (centeredCanonicalDecoratedTailGivenPrefix m r x pref)
          (nestedProductMeasure
            (stdGaussian (centeredSubspace (m + 1))) r) = κ

/-- The centered geometric adapter implies the raw adapter used by the
canonical-edge independence theorem. -/
theorem canonicalDecoratedTailLawInvariant_of_centered
    {m r : ℕ} {x : ℝ}
    (hcentered : CenteredCanonicalDecoratedTailLawInvariant m r x) :
    CanonicalDecoratedTailLawInvariant m r x := by
  obtain ⟨κ, hκ⟩ := hcentered
  refine ⟨κ, ?_⟩
  have hc : Measurable (centerNested (m + 1) 2) :=
    measurable_centerNested (m + 1) 2
  have hmap := map_centerNested_nestedProductMeasure (m + 1) 2
  rw [← hmap] at hκ
  have hpulled := ae_of_ae_map hc.aemeasurable hκ
  filter_upwards [hpulled] with pref hpref
  rw [map_canonicalDecoratedTailGivenPrefix_eq_centered]
  exact hpref

/-- Exact canonical-edge/decorated-tail independence, reduced to the named
orthogonal-invariance adapter above. -/
theorem canonicalEdgeExceedanceIndicator_indep_canonicalDecoratedTail
    {m r : ℕ} {x : ℝ}
    (hinv : CanonicalDecoratedTailLawInvariant m r x) :
    IndepFun (canonicalEdgeExceedanceIndicator m r x)
      (canonicalDecoratedTail m r x)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) := by
  obtain ⟨κ, hκ⟩ := hinv
  let μpref := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) 2
  let μtail := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) r
  letI : IsProbabilityMeasure
      (stdGaussian (ObservationSpace (m + 1))) :=
    ProbabilityTheory.isProbabilityMeasure_stdGaussian
  letI : IsProbabilityMeasure μpref := by
    dsimp [μpref]
    exact nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) 2
  letI : IsProbabilityMeasure μtail := by
    dsimp [μtail]
    exact nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) r
  letI : IsProbabilityMeasure
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) :=
    nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) (2 + r)
  have hprod : IndepFun
      (fun z : NestedTuple (ObservationSpace (m + 1)) 2 ×
          NestedTuple (ObservationSpace (m + 1)) r ↦
        canonicalEdgeExceedanceIndicatorOnPrefix m r x z.1)
      (fun z ↦ canonicalDecoratedTailGivenPrefix m r x z.1 z.2)
      (μpref.prod μtail) := by
    exact indepFun_prefix_decorated_of_ae_map_eq
      μpref μtail
      (canonicalEdgeExceedanceIndicatorOnPrefix m r x)
      (canonicalDecoratedTailGivenPrefix m r x)
      (measurable_canonicalEdgeExceedanceIndicatorOnPrefix m r x)
      (measurable_uncurry_canonicalDecoratedTailGivenPrefix m r x)
      κ hκ
  let F := nestedTupleSplit
    (α := ObservationSpace (m + 1)) 2 r
  have hF : Measurable F := measurable_nestedTupleSplit 2 r
  have hmap : Measure.map F
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) =
      μpref.prod μtail := by
    exact map_nestedTupleSplit_nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) 2 r
  have hcomp := IndepFun.comp_of_map_eq hprod hF
    ((measurable_canonicalEdgeExceedanceIndicatorOnPrefix m r x).comp
      measurable_fst)
    (measurable_uncurry_canonicalDecoratedTailGivenPrefix m r x) hmap
  change IndepFun
    (fun data ↦ canonicalEdgeExceedanceIndicatorOnPrefix m r x
      (nestedTuplePrefix 2 r data))
    (fun data ↦
      (standardizedGaussianRetainedTailStatistic m 2 r data,
        remoteCoherenceExceedanceCount m r x
          (nestedTupleTail 2 r data)))
    (nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) (2 + r))
  simpa [F, μpref, μtail, canonicalEdgeExceedanceIndicator,
    canonicalDecoratedTail, canonicalDecoratedTailGivenPrefix,
    remoteCoherenceExceedanceCountOnFull, nestedTupleSplit,
    Function.comp_def] using hcomp

end

end LogdetLean.Coherence
