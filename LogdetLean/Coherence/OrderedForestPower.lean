import LogdetLean.Coherence.OrderedForestIndependence
import Mathlib.Tactic
/-!
# Exact joint exceedance probability for an ordered forest

`OrderedForestIndependence` identifies the full vector law of forest-edge
exceedance indicators.  This file evaluates that product law on the single
success rectangle: roots have indicator zero and genuine forest edges have
indicator one.  The resulting probability is exactly the one-edge beta tail
raised to the number of forest edges.

This is the probability-theoretic half of the overlap bound.  Applying it to
an arbitrary nonmatching configuration still requires a finite relabeling
that exhibits a sufficiently large spanning forest in earlier-parent order.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set

/-- Number of genuine edges among the first `p` stages of an ordered
forest. -/
def orderedForestEdgeCount (F : OrderedForest) : ℕ → ℕ
  | 0 => 0
  | n + 1 => orderedForestEdgeCount F n +
      match F.parent n with
      | none => 0
      | some _ => 1

/-- Successful indicator value at one ordered-forest stage: zero for a root
and one for a genuine edge. -/
def orderedForestStageSuccess (F : OrderedForest) (n : ℕ) : Set ℕ :=
  match F.parent n with
  | none => {0}
  | some _ => {1}

/-- Rectangle on which all genuine ordered-forest edges exceed the
threshold. -/
def orderedForestSuccessSet (F : OrderedForest) :
    (p : ℕ) → Set (NestedTuple ℕ p)
  | 0 => Set.univ
  | n + 1 => orderedForestSuccessSet F n ×ˢ orderedForestStageSuccess F n

theorem measurableSet_orderedForestStageSuccess
    (F : OrderedForest) (n : ℕ) :
    MeasurableSet (orderedForestStageSuccess F n) := by
  unfold orderedForestStageSuccess
  split <;> exact MeasurableSet.singleton _

theorem measurableSet_orderedForestSuccessSet (F : OrderedForest) :
    ∀ p : ℕ, MeasurableSet (orderedForestSuccessSet F p) := by
  intro p
  induction p with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
      exact ih.prod (measurableSet_orderedForestStageSuccess F n)

@[simp]
theorem strictExceedanceCode_preimage_singleton_one (t : ℝ) :
    strictExceedanceCode t ⁻¹' ({1} : Set ℕ) = Set.Ioi t := by
  ext r
  simp [strictExceedanceCode]

/-- One factor assigns the success set probability one at a root and the
common beta upper-tail probability at a genuine edge. -/
theorem orderedForestExceedanceMeasure_stageSuccess
    (F : OrderedForest) (m : ℕ) (t : ℝ) (n : ℕ) :
    orderedForestExceedanceMeasure F m t n
        (orderedForestStageSuccess F n) =
      match F.parent n with
      | none => 1
      | some _ =>
          betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) (Set.Ioi t) := by
  cases hparent : F.parent n with
  | none =>
      simp [orderedForestExceedanceMeasure,
        orderedForestStageSuccess, hparent]
  | some i =>
      simp only [orderedForestExceedanceMeasure,
        orderedForestStageSuccess, hparent]
      rw [Measure.map_apply (measurable_strictExceedanceCode t)
        (MeasurableSet.singleton 1)]
      rw [strictExceedanceCode_preimage_singleton_one]

/-- Direct evaluation of the nested independent-factor measure on the
all-success rectangle. -/
theorem nestedProductMeasureFamily_orderedForestSuccessSet
    (F : OrderedForest) (m : ℕ) (t : ℝ) :
    ∀ p : ℕ,
      nestedProductMeasureFamily
          (orderedForestExceedanceMeasure F m t) p
          (orderedForestSuccessSet F p) =
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) (Set.Ioi t)) ^
          orderedForestEdgeCount F p := by
  intro p
  induction p with
  | zero =>
      simp [nestedProductMeasureFamily, orderedForestSuccessSet,
        orderedForestEdgeCount]
  | succ n ih =>
      rw [nestedProductMeasureFamily, orderedForestSuccessSet,
        Measure.prod_prod, ih,
        orderedForestExceedanceMeasure_stageSuccess]
      cases hparent : F.parent n with
      | none =>
          simp [orderedForestEdgeCount, hparent]
      | some i =>
          simp [orderedForestEdgeCount, hparent, pow_succ]

/-- Source-space event corresponding to success at every ordered-forest
stage. -/
def orderedForestJointExceedanceEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : OrderedForest) (t : ℝ) (p : ℕ) : Set (NestedTuple E p) :=
  sequentialStatistic
      (orderedForestExceedanceIndicator (E := E) F t) p ⁻¹'
    orderedForestSuccessSet F p

theorem measurableSet_orderedForestJointExceedanceEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (t : ℝ) (p : ℕ) :
    MeasurableSet (orderedForestJointExceedanceEvent (E := E) F t p) := by
  exact (measurableSet_orderedForestSuccessSet F p).preimage
    (measurable_sequentialStatistic
      (orderedForestExceedanceIndicator (E := E) F t)
      (measurable_uncurry_orderedForestExceedanceIndicator F t) p)

/-- Exact ENNReal-valued ordered-forest joint exceedance probability. -/
theorem gaussian_orderedForest_jointExceedance_eq_betaTail_pow
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (t : ℝ) (p : ℕ) :
    nestedProductMeasure (stdGaussian E) p
        (orderedForestJointExceedanceEvent (E := E) F t p) =
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) (Set.Ioi t)) ^
        orderedForestEdgeCount F p := by
  let indicatorMap : NestedTuple E p → NestedTuple ℕ p :=
    sequentialStatistic
      (orderedForestExceedanceIndicator (E := E) F t) p
  have hmeas : Measurable indicatorMap :=
    measurable_sequentialStatistic
      (orderedForestExceedanceIndicator (E := E) F t)
      (measurable_uncurry_orderedForestExceedanceIndicator F t) p
  have hset := measurableSet_orderedForestSuccessSet F p
  change nestedProductMeasure (stdGaussian E) p
      (indicatorMap ⁻¹' orderedForestSuccessSet F p) = _
  rw [← Measure.map_apply hmeas hset,
    map_orderedForestExceedanceIndicators_eq_nestedProduct
      F m hdim hm t p,
    nestedProductMeasureFamily_orderedForestSuccessSet]

/-- Real-valued form used by factorial-moment estimates. -/
theorem gaussian_orderedForest_jointExceedanceReal_eq_betaTail_pow
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (t : ℝ) (p : ℕ) :
    (nestedProductMeasure (stdGaussian E) p).real
        (orderedForestJointExceedanceEvent (E := E) F t p) =
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Set.Ioi t)).toReal ^ orderedForestEdgeCount F p := by
  rw [measureReal_def,
    gaussian_orderedForest_jointExceedance_eq_betaTail_pow
      F m hdim hm t p,
    ENNReal.toReal_pow]

/-! ## The same event on ordinary finite families -/

/-- Joint exceedance event on a `Fin p`-indexed family.  At stage `n`, an
earlier parent `i : Fin n` is cast into `Fin p`; roots impose no condition. -/
def orderedForestFamilyJointExceedanceEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : OrderedForest) (t : ℝ) (p : ℕ) : Set (Fin p → E) :=
  {v | ∀ n : Fin p,
    match F.parent n.val with
    | none => True
    | some i => t < squaredNormalizedInner
        (v (i.castLT (lt_trans i.isLt n.isLt))) (v n)}

theorem measurableSet_orderedForestFamilyJointExceedanceEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (t : ℝ) (p : ℕ) :
    MeasurableSet (orderedForestFamilyJointExceedanceEvent (E := E) F t p) := by
  let S : Fin p → Set (Fin p → E) := fun n ↦
    {v |
      match F.parent n.val with
      | none => True
      | some i => t < squaredNormalizedInner
          (v (i.castLT (lt_trans i.isLt n.isLt))) (v n)}
  have hS : ∀ n, MeasurableSet (S n) := by
    intro n
    cases hparent : F.parent n.val with
    | none =>
        simp [S, hparent]
    | some i =>
        simp only [S, hparent]
        have hpair : Measurable (fun v : Fin p → E ↦
            (v (i.castLT (lt_trans i.isLt n.isLt)), v n)) :=
          (measurable_pi_apply
              (i.castLT (lt_trans i.isLt n.isLt))).prodMk
            (measurable_pi_apply n)
        exact measurableSet_lt measurable_const
          ((measurable_uncurry_squaredNormalizedInner (E := E)).comp hpair)
  have hall : MeasurableSet (⋂ n, S n) :=
    MeasurableSet.iInter hS
  convert hall using 1
  ext v
  simp [S, orderedForestFamilyJointExceedanceEvent]

/-- Reading a nested tuple as a finite family identifies the two definitions
of the all-forest-edge exceedance event. -/
theorem preimage_orderedForestFamilyJointExceedanceEvent_nestedTupleToFin
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : OrderedForest) (t : ℝ) :
    ∀ p : ℕ,
      nestedTupleToFin (α := E) p ⁻¹'
          orderedForestFamilyJointExceedanceEvent (E := E) F t p =
        orderedForestJointExceedanceEvent (E := E) F t p := by
  intro p
  induction p with
  | zero =>
      ext z
      simp [orderedForestFamilyJointExceedanceEvent,
        orderedForestJointExceedanceEvent, orderedForestSuccessSet,
        sequentialStatistic]
  | succ n ih =>
      ext z
      rcases z with ⟨past, fresh⟩
      have ihmem :
          nestedTupleToFin n past ∈
              orderedForestFamilyJointExceedanceEvent (E := E) F t n ↔
            past ∈ orderedForestJointExceedanceEvent (E := E) F t n := by
        exact Set.ext_iff.mp ih past
      have ihprior :
          (∀ j : Fin n,
            match F.parent j.val with
            | none => True
            | some i => t < squaredNormalizedInner
                (nestedTupleToFin n past
                  (i.castLT (lt_trans i.isLt j.isLt)))
                (nestedTupleToFin n past j)) ↔
          sequentialStatistic
              (orderedForestExceedanceIndicator (E := E) F t) n past ∈
            orderedForestSuccessSet F n := by
        simpa [orderedForestFamilyJointExceedanceEvent,
          orderedForestJointExceedanceEvent] using ihmem
      have hcastPrior (j : Fin n) (i : Fin j.val) :
          i.castLT (lt_trans i.isLt j.castSucc.isLt) =
            (i.castLT (lt_trans i.isLt j.isLt)).castSucc := by
        apply Fin.ext
        rfl
      have hcastLast (i : Fin n) :
          i.castLT (lt_trans i.isLt (Fin.last n).isLt) = i.castSucc := by
        apply Fin.ext
        rfl
      change
        nestedTupleToFin (n + 1) (past, fresh) ∈
              orderedForestFamilyJointExceedanceEvent (E := E) F t (n + 1) ↔
          sequentialStatistic
              (orderedForestExceedanceIndicator (E := E) F t) (n + 1)
              (past, fresh) ∈ orderedForestSuccessSet F (n + 1)
      simp only [nestedTupleToFin]
      unfold orderedForestFamilyJointExceedanceEvent
      simp only [Set.mem_setOf_eq]
      cases hparent : F.parent n with
      | none =>
          rw [Fin.forall_fin_succ']
          simp [orderedForestFamilyJointExceedanceEvent,
            orderedForestJointExceedanceEvent, orderedForestSuccessSet,
            orderedForestStageSuccess, orderedForestExceedanceIndicator,
            sequentialStatistic, nestedTupleToFin, hparent,
            hcastPrior, hcastLast, ihprior]
          convert ihprior using 1
          apply forall_congr'
          intro j
          cases hj : F.parent j.val with
          | none => simp [hj]
          | some i =>
              simp only [hj]
      | some parent =>
          rw [Fin.forall_fin_succ']
          simp [orderedForestFamilyJointExceedanceEvent,
            orderedForestJointExceedanceEvent, orderedForestSuccessSet,
            orderedForestStageSuccess, orderedForestExceedanceIndicator,
            strictExceedanceCode, sequentialStatistic, nestedTupleToFin,
            hparent, hcastPrior, hcastLast, ihprior]
          intro _hnew
          convert ihprior using 1
          apply forall_congr'
          intro j
          cases hj : F.parent j.val with
          | none => simp [hj]
          | some i =>
              simp only [hj]

/-- Exact ordered-forest probability under the ordinary finite iid Gaussian
product measure. -/
theorem gaussianPi_orderedForest_jointExceedance_eq_betaTail_pow
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (t : ℝ) (p : ℕ) :
    (Measure.pi fun _ : Fin p ↦ stdGaussian E)
        (orderedForestFamilyJointExceedanceEvent (E := E) F t p) =
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) (Set.Ioi t)) ^
        orderedForestEdgeCount F p := by
  have hread := measurePreserving_nestedTupleToFin (stdGaussian E) p
  have hset :=
    measurableSet_orderedForestFamilyJointExceedanceEvent
      (E := E) F t p
  have happly := hread.map_eq ▸
    Measure.map_apply (measurable_nestedTupleToFin (α := E) p) hset
  rw [preimage_orderedForestFamilyJointExceedanceEvent_nestedTupleToFin]
    at happly
  rw [happly]
  exact gaussian_orderedForest_jointExceedance_eq_betaTail_pow
    F m hdim hm t p

/-- Real-valued finite-family form. -/
theorem gaussianPi_orderedForest_jointExceedanceReal_eq_betaTail_pow
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : OrderedForest) (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (t : ℝ) (p : ℕ) :
    (Measure.pi fun _ : Fin p ↦ stdGaussian E).real
        (orderedForestFamilyJointExceedanceEvent (E := E) F t p) =
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Set.Ioi t)).toReal ^ orderedForestEdgeCount F p := by
  rw [measureReal_def,
    gaussianPi_orderedForest_jointExceedance_eq_betaTail_pow
      F m hdim hm t p,
    ENNReal.toReal_pow]

end

end LogdetLean.Coherence
