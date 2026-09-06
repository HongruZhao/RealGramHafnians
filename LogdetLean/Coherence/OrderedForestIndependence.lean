import LogdetLean.Coherence.PairBeta
import LogdetLean.GaussianColumnProduct
/-!
# Exact independence of Gaussian correlations along an ordered forest

An ordered rooted forest is encoded by giving every vertex `n` either no
parent (a root) or a parent in `Fin n`.  Thus every parent is strictly earlier
and directed cycles are impossible.  Every finite rooted forest admits such
an encoding after ordering roots before their descendants.

For iid standard Gaussian vectors, this module proves that the squared
normalized inner products on all forest edges are mutually independent and
have law `Beta(1/2,(m-1)/2)`.  Root stages carry the harmless deterministic
value zero.  The proof is a direct application of the sequential
skew-product theorem: conditionally on the past, a new edge uses a fresh
Gaussian vector and one fixed nonzero parent vector.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace

/-- A parent ordering for a rooted forest.  At stage `n`, `none` marks a root
and `some i` chooses the strictly earlier parent `i : Fin n`. -/
structure OrderedForest where
  parent : (n : ℕ) → Option (Fin n)

/-- The one-step squared correlation attached to an ordered-forest stage.
Root stages are assigned zero. -/
def orderedForestScore
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : OrderedForest) (n : ℕ)
    (past : NestedTuple E n) (fresh : E) : ℝ :=
  match F.parent n with
  | none => 0
  | some i => squaredNormalizedInner (nestedTupleToFin (α := E) n past i) fresh

/-- The prescribed one-step law: a root is deterministic zero, while every
edge has the common squared-correlation Beta law. -/
def orderedForestFactorMeasure (F : OrderedForest) (m n : ℕ) : Measure ℝ :=
  match F.parent n with
  | none => Measure.dirac 0
  | some _ => betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)

instance orderedForestFactorMeasure_sFinite
    (F : OrderedForest) (m n : ℕ) :
    SFinite (orderedForestFactorMeasure F m n) := by
  unfold orderedForestFactorMeasure
  split
  · infer_instance
  · unfold betaMeasure
    infer_instance

/-- All forest-stage scores, stored in their construction order. -/
def orderedForestScores
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : OrderedForest) (p : ℕ) :
    NestedTuple E p → NestedTuple ℝ p :=
  sequentialStatistic (orderedForestScore (E := E) F) p

/-- Joint measurability of a forest's one-step score. -/
theorem measurable_uncurry_orderedForestScore
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (n : ℕ) :
    Measurable (Function.uncurry (orderedForestScore (E := E) F n)) := by
  unfold orderedForestScore Function.uncurry
  cases hparent : F.parent n with
  | none =>
      simp only [hparent]
      exact measurable_const
  | some i =>
      simp only [hparent]
      exact (measurable_uncurry_squaredNormalizedInner (E := E)).comp
        (((measurable_nestedTupleToFin_apply (α := E) n i).comp measurable_fst).prodMk
          measurable_snd)

/-- Every fixed coordinate in an iid nested Gaussian past is nonzero almost
surely. -/
theorem ae_nestedGaussian_coordinate_ne_zero
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 1 ≤ m)
    (n : ℕ) (i : Fin n) :
    ∀ᵐ past ∂nestedProductMeasure (stdGaussian E) n,
      nestedTupleToFin (α := E) n past i ≠ 0 := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  have hgaussian : ∀ᵐ u ∂stdGaussian E, u ≠ 0 := by
    simpa [ae_iff] using stdGaussian_zero_singleton (E := E)
  have hcoordinate : MeasurePreserving
      (fun past : NestedTuple E n ↦ nestedTupleToFin (α := E) n past i)
      (nestedProductMeasure (stdGaussian E) n) (stdGaussian E) := by
    have htuple := measurePreserving_nestedTupleToFin (stdGaussian E) n
    have heval := MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin n ↦ stdGaussian E) i
    exact heval.comp htuple
  exact hcoordinate.quasiMeasurePreserving.tendsto_ae hgaussian

/-- Conditional one-step forest law.  The law is constant in the past almost
surely, including the deterministic root case. -/
theorem ae_map_orderedForestScore_eq_factorMeasure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (n : ℕ) :
    ∀ᵐ past ∂nestedProductMeasure (stdGaussian E) n,
      Measure.map (orderedForestScore (E := E) F n past) (stdGaussian E) =
        orderedForestFactorMeasure F m n := by
  cases hparent : F.parent n with
  | none =>
      filter_upwards [] with past
      have hscore : orderedForestScore (E := E) F n past =
          (fun _ : E ↦ (0 : ℝ)) := by
        funext fresh
        simp [orderedForestScore, hparent]
      rw [hscore, Measure.map_const]
      simp [orderedForestFactorMeasure, hparent]
  | some i =>
      filter_upwards [ae_nestedGaussian_coordinate_ne_zero
        m hdim (by omega) n i] with past hpast
      have hscore : orderedForestScore (E := E) F n past =
          squaredNormalizedInner (nestedTupleToFin (α := E) n past i) := by
        funext fresh
        simp [orderedForestScore, hparent]
      rw [hscore]
      simpa [orderedForestFactorMeasure, hparent] using
        map_squaredNormalizedInner_stdGaussian_fixed m hdim hm
          (nestedTupleToFin (α := E) n past i) hpast

/-- **Ordered-forest product law.**  The full vector of forest-edge squared
correlations has the iterated product of the prescribed laws.  Consequently,
all genuine edge coordinates are mutually independent Beta variables. -/
theorem map_orderedForestScores_eq_nestedProduct
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (p : ℕ) :
    Measure.map (orderedForestScores (E := E) F p)
        (nestedProductMeasure (stdGaussian E) p) =
      nestedProductMeasureFamily (orderedForestFactorMeasure F m) p := by
  exact map_sequentialStatistic_eq_nestedProduct
    (stdGaussian E) (orderedForestFactorMeasure F m)
    (orderedForestScore (E := E) F)
    (measurable_uncurry_orderedForestScore F)
    (ae_map_orderedForestScore_eq_factorMeasure F m hdim hm) p

/-! ## Threshold-exceedance corollaries -/

/-- Code a strict threshold exceedance by `1`, and nonexceedance by `0`. -/
def strictExceedanceCode (t r : ℝ) : ℕ := if t < r then 1 else 0

/-- Threshold coding is measurable. -/
theorem measurable_strictExceedanceCode (t : ℝ) :
    Measurable (strictExceedanceCode t) := by
  unfold strictExceedanceCode
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

/-- One-step forest exceedance indicator.  Roots remain zero for every
threshold. -/
def orderedForestExceedanceIndicator
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : OrderedForest) (t : ℝ) (n : ℕ)
    (past : NestedTuple E n) (fresh : E) : ℕ :=
  match F.parent n with
  | none => 0
  | some i => strictExceedanceCode t
      (squaredNormalizedInner (nestedTupleToFin (α := E) n past i) fresh)

/-- Prescribed law of one forest exceedance indicator. -/
def orderedForestExceedanceMeasure
    (F : OrderedForest) (m : ℕ) (t : ℝ) (n : ℕ) : Measure ℕ :=
  match F.parent n with
  | none => Measure.dirac 0
  | some _ => Measure.map (strictExceedanceCode t)
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2))

instance orderedForestExceedanceMeasure_sFinite
    (F : OrderedForest) (m : ℕ) (t : ℝ) (n : ℕ) :
    SFinite (orderedForestExceedanceMeasure F m t n) := by
  unfold orderedForestExceedanceMeasure
  split
  · infer_instance
  · unfold betaMeasure
    infer_instance

/-- Joint measurability of the one-step exceedance indicator. -/
theorem measurable_uncurry_orderedForestExceedanceIndicator
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (t : ℝ) (n : ℕ) :
    Measurable (Function.uncurry
      (orderedForestExceedanceIndicator (E := E) F t n)) := by
  unfold orderedForestExceedanceIndicator Function.uncurry
  cases hparent : F.parent n with
  | none =>
      simp only [hparent]
      exact measurable_const
  | some i =>
      simp only [hparent]
      exact (measurable_strictExceedanceCode t).comp
        ((measurable_uncurry_squaredNormalizedInner (E := E)).comp
          (((measurable_nestedTupleToFin_apply (α := E) n i).comp measurable_fst).prodMk
            measurable_snd))

/-- Conditional one-step law of the forest exceedance indicator. -/
theorem ae_map_orderedForestExceedanceIndicator_eq
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (t : ℝ) (n : ℕ) :
    ∀ᵐ past ∂nestedProductMeasure (stdGaussian E) n,
      Measure.map (orderedForestExceedanceIndicator (E := E) F t n past)
          (stdGaussian E) =
        orderedForestExceedanceMeasure F m t n := by
  cases hparent : F.parent n with
  | none =>
      filter_upwards [] with past
      have hindicator : orderedForestExceedanceIndicator (E := E) F t n past =
          (fun _ : E ↦ (0 : ℕ)) := by
        funext fresh
        simp [orderedForestExceedanceIndicator, hparent]
      rw [hindicator, Measure.map_const]
      simp [orderedForestExceedanceMeasure, hparent]
  | some i =>
      filter_upwards [ae_nestedGaussian_coordinate_ne_zero
        m hdim (by omega) n i] with past hpast
      have hsquare : Measurable
          (squaredNormalizedInner (nestedTupleToFin (α := E) n past i)) :=
        (measurable_uncurry_squaredNormalizedInner (E := E)).comp
          (measurable_const.prodMk measurable_id)
      have hlaw := map_squaredNormalizedInner_stdGaussian_fixed
        m hdim hm (nestedTupleToFin (α := E) n past i) hpast
      have hindicator : orderedForestExceedanceIndicator (E := E) F t n past =
          fun fresh ↦ strictExceedanceCode t
            (squaredNormalizedInner (nestedTupleToFin (α := E) n past i) fresh) := by
        funext fresh
        simp [orderedForestExceedanceIndicator, hparent]
      rw [hindicator]
      simp only [orderedForestExceedanceMeasure, hparent]
      calc
        Measure.map
            (fun fresh ↦ strictExceedanceCode t
              (squaredNormalizedInner (nestedTupleToFin (α := E) n past i) fresh))
            (stdGaussian E) =
          Measure.map (strictExceedanceCode t)
            (Measure.map (squaredNormalizedInner (nestedTupleToFin (α := E) n past i))
              (stdGaussian E)) := by
                simpa [Function.comp_def] using
                  (Measure.map_map (measurable_strictExceedanceCode t) hsquare).symm
        _ = Measure.map (strictExceedanceCode t)
            (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) := by
              rw [hlaw]

/-- **Threshold-event product corollary.**  The strict-exceedance indicators
on all ordered-forest edges are mutually independent.  Each edge indicator
is the threshold pushforward of the common Beta law, while roots are zero. -/
theorem map_orderedForestExceedanceIndicators_eq_nestedProduct
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (t : ℝ) (p : ℕ) :
    Measure.map
        (sequentialStatistic
          (orderedForestExceedanceIndicator (E := E) F t) p)
        (nestedProductMeasure (stdGaussian E) p) =
      nestedProductMeasureFamily
        (orderedForestExceedanceMeasure F m t) p := by
  exact map_sequentialStatistic_eq_nestedProduct
    (stdGaussian E) (orderedForestExceedanceMeasure F m t)
    (orderedForestExceedanceIndicator (E := E) F t)
    (measurable_uncurry_orderedForestExceedanceIndicator F t)
    (ae_map_orderedForestExceedanceIndicator_eq F m hdim hm t) p

/-- Probability of exceeding a fixed threshold along one nonzero-parent
Gaussian edge, expressed exactly as a Beta upper tail. -/
theorem gaussian_edge_exceedanceProbability_eq_beta_Ioi
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (u : E) (hu : u ≠ 0) (t : ℝ) :
    (stdGaussian E) {v | t < squaredNormalizedInner u v} =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) (Set.Ioi t) := by
  have hsquare : Measurable (squaredNormalizedInner u) :=
    (measurable_uncurry_squaredNormalizedInner (E := E)).comp
      (measurable_const.prodMk measurable_id)
  calc
    (stdGaussian E) {v | t < squaredNormalizedInner u v} =
        Measure.map (squaredNormalizedInner u) (stdGaussian E) (Set.Ioi t) := by
      rw [Measure.map_apply hsquare measurableSet_Ioi]
      rfl
    _ = betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) (Set.Ioi t) := by
      rw [map_squaredNormalizedInner_stdGaussian_fixed m hdim hm u hu]

end

end LogdetLean.Coherence
