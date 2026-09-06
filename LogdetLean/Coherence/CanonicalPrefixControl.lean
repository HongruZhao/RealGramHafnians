import LogdetLean.Coherence.OrderedForestIndependence
import LogdetLean.Coherence.BetaFirstMoment
import LogdetLean.Coherence.BetaOvershoot
import LogdetLean.Coherence.PrefixDeterminantBound
import LogdetLean.Coherence.PrefixScale
import LogdetLean.Coherence.ColumnPermutation
import LogdetLean.WishartSequentialKernel
import LogdetLean.MatrixSphericalExtension
/-!
# Canonical matching control for a fixed Gaussian prefix

This module begins the model-specific conditional-prefix argument without
introducing regular conditional probabilities.  Conditioning is represented
by a quotient of ordinary probabilities.  The canonical matching occupies
the consecutive pairs `(0,1), (2,3), ...`; its squared correlations are the
odd-stage scores of an ordered forest.

The first part below proves a reusable exact product calculation.  In
particular, the relative probability that at least one selected correlation
overshoots a fixed multiple of the base threshold is bounded by the number
of selected edges times the corresponding one-edge Beta-tail ratio.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Module
open scoped Topology RealInnerProductSpace

/-- Ordered forest whose genuine edges are the consecutive pairs
`(0,1), (2,3), ...`. -/
def canonicalMatchingForest : OrderedForest where
  parent n :=
    if h : n % 2 = 1 then
      some ⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩
    else none

@[simp]
theorem canonicalMatchingForest_parent_even (j : ℕ) :
    canonicalMatchingForest.parent (2 * j) = none := by
  simp [canonicalMatchingForest]

theorem canonicalMatchingForest_parent_odd_isSome (j : ℕ) :
    (canonicalMatchingForest.parent (2 * j + 1)).isSome := by
  simp [canonicalMatchingForest]

@[simp]
theorem canonicalMatching_factorMeasure_even (m j : ℕ) :
    orderedForestFactorMeasure canonicalMatchingForest m (2 * j) =
      Measure.dirac 0 := by
  simp [orderedForestFactorMeasure]

@[simp]
theorem canonicalMatching_factorMeasure_odd (m j : ℕ) :
    orderedForestFactorMeasure canonicalMatchingForest m (2 * j + 1) =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
  unfold orderedForestFactorMeasure
  have hsome := canonicalMatchingForest_parent_odd_isSome j
  cases h : canonicalMatchingForest.parent (2 * j + 1) with
  | none => simp [h] at hsome
  | some i => simp [h]

/-- All selected odd-stage forest scores exceed `t`.  The even stages are
roots and are unconstrained. -/
def canonicalMatchingScoreEvent (t : ℝ) :
    (k : ℕ) → Set (NestedTuple ℝ (2 * k))
  | 0 => Set.univ
  | k + 1 =>
      ((canonicalMatchingScoreEvent t k) ×ˢ Set.univ) ×ˢ Set.Ioi t

/-- Within the matching event, at least one selected score exceeds `c*t`.
The recursion records either an earlier bad selected edge or a bad newest
edge. -/
def canonicalMatchingSelectedOvershootScoreEvent (t c : ℝ) :
    (k : ℕ) → Set (NestedTuple ℝ (2 * k))
  | 0 => ∅
  | k + 1 =>
      (((canonicalMatchingSelectedOvershootScoreEvent t c k) ×ˢ Set.univ) ×ˢ
          Set.Ioi t) ∪
        (((canonicalMatchingScoreEvent t k) ×ˢ Set.univ) ×ˢ Set.Ioi (c * t))

theorem measurableSet_canonicalMatchingScoreEvent (t : ℝ) :
    ∀ k, MeasurableSet (canonicalMatchingScoreEvent t k) := by
  intro k
  induction k with
  | zero => simp [canonicalMatchingScoreEvent]
  | succ k ih =>
      simpa [canonicalMatchingScoreEvent] using
        ((ih.prod MeasurableSet.univ).prod measurableSet_Ioi)

theorem measurableSet_canonicalMatchingSelectedOvershootScoreEvent
    (t c : ℝ) :
    ∀ k, MeasurableSet
      (canonicalMatchingSelectedOvershootScoreEvent t c k) := by
  intro k
  induction k with
  | zero => simp [canonicalMatchingSelectedOvershootScoreEvent]
  | succ k ih =>
      exact (((ih.prod MeasurableSet.univ).prod measurableSet_Ioi).union
        (((measurableSet_canonicalMatchingScoreEvent t k).prod
          MeasurableSet.univ).prod measurableSet_Ioi))

/-- Exact product probability of the canonical matching score event under
the forest factor law. -/
theorem canonicalMatchingScoreEvent_probability
    (m k : ℕ) (t : ℝ) :
    (nestedProductMeasureFamily
      (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).real
        (canonicalMatchingScoreEvent t k) =
      ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^ k := by
  induction k with
  | zero =>
      simp [canonicalMatchingScoreEvent, nestedProductMeasureFamily]
  | succ k ih =>
      change
        ((((nestedProductMeasureFamily
            (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).prod
              (orderedForestFactorMeasure canonicalMatchingForest m (2 * k))).prod
                (orderedForestFactorMeasure canonicalMatchingForest m (2 * k + 1))).real
          (((canonicalMatchingScoreEvent t k) ×ˢ Set.univ) ×ˢ Set.Ioi t)) = _
      simp only [measureReal_prod_prod]
      rw [ih, canonicalMatching_factorMeasure_even,
        canonicalMatching_factorMeasure_odd]
      simp [pow_succ]

/-- Finite union bound for selected-edge overshoots under the exact forest
product law. -/
theorem canonicalMatchingSelectedOvershootScoreEvent_probability_le
    (m k : ℕ) (t c : ℝ) :
    (nestedProductMeasureFamily
      (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).real
        (canonicalMatchingSelectedOvershootScoreEvent t c k) ≤
      (k : ℝ) *
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t)) *
        ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^
          (k - 1) := by
  let q : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)
  let qc : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t))
  have hq : 0 ≤ q := measureReal_nonneg
  have hqc : 0 ≤ qc := measureReal_nonneg
  induction k with
  | zero =>
      simp [canonicalMatchingSelectedOvershootScoreEvent]
  | succ k ih =>
      change
        ((((nestedProductMeasureFamily
            (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).prod
              (orderedForestFactorMeasure canonicalMatchingForest m (2 * k))).prod
                (orderedForestFactorMeasure canonicalMatchingForest m (2 * k + 1))).real
          ((((canonicalMatchingSelectedOvershootScoreEvent t c k) ×ˢ Set.univ) ×ˢ
              Set.Ioi t) ∪
            (((canonicalMatchingScoreEvent t k) ×ˢ Set.univ) ×ˢ
              Set.Ioi (c * t)))) ≤ _
      calc
        (((nestedProductMeasureFamily
              (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).prod
            (orderedForestFactorMeasure canonicalMatchingForest m (2 * k))).prod
            (orderedForestFactorMeasure canonicalMatchingForest m (2 * k + 1))).real
            (canonicalMatchingSelectedOvershootScoreEvent t c (k + 1)) ≤
          (((nestedProductMeasureFamily
              (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).prod
            (orderedForestFactorMeasure canonicalMatchingForest m (2 * k))).prod
            (orderedForestFactorMeasure canonicalMatchingForest m (2 * k + 1))).real
              (((canonicalMatchingSelectedOvershootScoreEvent t c k ×ˢ Set.univ) ×ˢ
                  Set.Ioi t)) +
          (((nestedProductMeasureFamily
              (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).prod
            (orderedForestFactorMeasure canonicalMatchingForest m (2 * k))).prod
            (orderedForestFactorMeasure canonicalMatchingForest m (2 * k + 1))).real
              (((canonicalMatchingScoreEvent t k ×ˢ Set.univ) ×ˢ
                  Set.Ioi (c * t))) := by
            simpa [canonicalMatchingSelectedOvershootScoreEvent] using
              measureReal_union_le
                (μ := ((nestedProductMeasureFamily
                  (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).prod
                    (orderedForestFactorMeasure canonicalMatchingForest m (2 * k))).prod
                    (orderedForestFactorMeasure canonicalMatchingForest m (2 * k + 1)))
                (((canonicalMatchingSelectedOvershootScoreEvent t c k ×ˢ Set.univ) ×ˢ
                  Set.Ioi t))
                (((canonicalMatchingScoreEvent t k ×ˢ Set.univ) ×ˢ
                  Set.Ioi (c * t)))
        _ =
          (nestedProductMeasureFamily
            (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).real
              (canonicalMatchingSelectedOvershootScoreEvent t c k) * q +
          (nestedProductMeasureFamily
            (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).real
              (canonicalMatchingScoreEvent t k) * qc := by
            rw [measureReal_prod_prod, measureReal_prod_prod,
              measureReal_prod_prod, measureReal_prod_prod]
            simp [q, qc]
        _ ≤ ((k : ℝ) * qc * q ^ (k - 1)) * q + q ^ k * qc := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_right _ hq
              simpa [q, qc] using ih
            · apply mul_le_mul_of_nonneg_right _ hqc
              exact (canonicalMatchingScoreEvent_probability m k t).le
        _ = ((k + 1 : ℕ) : ℝ) * qc * q ^ ((k + 1) - 1) := by
            by_cases hk : k = 0
            · subst k
              simp
            · have hpow : q ^ (k - 1) * q = q ^ k := by
                calc
                  q ^ (k - 1) * q = q ^ ((k - 1) + 1) := by
                    rw [pow_succ]
                  _ = q ^ k := by congr 1 <;> omega
              rw [Nat.add_sub_cancel]
              calc
                (k : ℝ) * qc * q ^ (k - 1) * q + q ^ k * qc =
                    (k : ℝ) * qc * (q ^ (k - 1) * q) + q ^ k * qc := by ring
                _ = (k : ℝ) * qc * q ^ k + q ^ k * qc := by rw [hpow]
                _ = ((k + 1 : ℕ) : ℝ) * qc * q ^ k := by
                  push_cast
                  ring

/-- Pull the canonical matching event back to the Gaussian tuple space. -/
def canonicalGaussianMatchingEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (t : ℝ) : Set (NestedTuple E (2 * k)) :=
  orderedForestScores (E := E) canonicalMatchingForest (2 * k) ⁻¹'
    canonicalMatchingScoreEvent t k

theorem measurableSet_canonicalGaussianMatchingEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) (t : ℝ) :
    MeasurableSet (canonicalGaussianMatchingEvent (E := E) k t) := by
  exact (measurableSet_canonicalMatchingScoreEvent t k).preimage
    (measurable_sequentialStatistic
      (orderedForestScore (E := E) canonicalMatchingForest)
      (measurable_uncurry_orderedForestScore canonicalMatchingForest)
      (2 * k))

/-- Pull the selected-overshoot event back to the same Gaussian space. -/
def canonicalGaussianSelectedOvershootEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (t c : ℝ) : Set (NestedTuple E (2 * k)) :=
  orderedForestScores (E := E) canonicalMatchingForest (2 * k) ⁻¹'
    canonicalMatchingSelectedOvershootScoreEvent t c k

/-! ### The same events on ordinary finite families -/

/-- The first endpoint of the `j`-th canonical pair. -/
def canonicalEvenIndex (k : ℕ) (j : Fin k) : Fin (2 * k) :=
  ⟨2 * j.1, by omega⟩

/-- The second endpoint of the `j`-th canonical pair. -/
def canonicalOddIndex (k : ℕ) (j : Fin k) : Fin (2 * k) :=
  ⟨2 * j.1 + 1, by omega⟩

@[simp]
theorem canonicalEvenIndex_val (k : ℕ) (j : Fin k) :
    (canonicalEvenIndex k j).1 = 2 * j.1 := rfl

@[simp]
theorem canonicalOddIndex_val (k : ℕ) (j : Fin k) :
    (canonicalOddIndex k j).1 = 2 * j.1 + 1 := rfl

/-- Squared normalized inner product is symmetric. -/
theorem squaredNormalizedInner_comm
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) :
    squaredNormalizedInner u v = squaredNormalizedInner v u := by
  unfold squaredNormalizedInner
  rw [real_inner_comm]
  ring

theorem canonicalEvenIndex_injective (k : ℕ) :
    Function.Injective (canonicalEvenIndex k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [canonicalEvenIndex_val] at hv
  omega

theorem canonicalOddIndex_injective (k : ℕ) :
    Function.Injective (canonicalOddIndex k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [canonicalOddIndex_val] at hv
  omega

theorem canonicalEvenIndex_ne_oddIndex
    (k : ℕ) (i j : Fin k) :
    canonicalEvenIndex k i ≠ canonicalOddIndex k j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [canonicalEvenIndex_val, canonicalOddIndex_val] at hv
  omega

theorem canonicalOddIndex_ne_evenIndex
    (k : ℕ) (i j : Fin k) :
    canonicalOddIndex k i ≠ canonicalEvenIndex k j :=
  Ne.symm (canonicalEvenIndex_ne_oddIndex k j i)

/-- Select the first (`false`) or second (`true`) endpoint of a canonical
pair. -/
def canonicalEndpointIndex (k : ℕ) (j : Fin k) : Bool → Fin (2 * k)
  | false => canonicalEvenIndex k j
  | true => canonicalOddIndex k j

@[simp]
theorem canonicalEndpointIndex_false (k : ℕ) (j : Fin k) :
    canonicalEndpointIndex k j false = canonicalEvenIndex k j := rfl

@[simp]
theorem canonicalEndpointIndex_true (k : ℕ) (j : Fin k) :
    canonicalEndpointIndex k j true = canonicalOddIndex k j := rfl

/-- Optionally swap the two endpoints of one canonical pair. -/
def canonicalOptionalPairSwap (k : ℕ) (j : Fin k) (e : Bool) :
    Equiv.Perm (Fin (2 * k)) :=
  if e then Equiv.swap (canonicalEvenIndex k j) (canonicalOddIndex k j)
  else Equiv.refl _

@[simp]
theorem canonicalOptionalPairSwap_false (k : ℕ) (j : Fin k) :
    canonicalOptionalPairSwap k j false = Equiv.refl _ := rfl

@[simp]
theorem canonicalOptionalPairSwap_true (k : ℕ) (j : Fin k) :
    canonicalOptionalPairSwap k j true =
      Equiv.swap (canonicalEvenIndex k j) (canonicalOddIndex k j) := rfl

@[simp]
theorem canonicalOptionalPairSwap_symm_even
    (k : ℕ) (j : Fin k) (e : Bool) :
    (canonicalOptionalPairSwap k j e).symm (canonicalEvenIndex k j) =
      canonicalEndpointIndex k j e := by
  cases e <;> simp [canonicalOptionalPairSwap, canonicalEndpointIndex]

@[simp]
theorem canonicalOptionalPairSwap_symm_odd
    (k : ℕ) (j : Fin k) (e : Bool) :
    (canonicalOptionalPairSwap k j e).symm (canonicalOddIndex k j) =
      canonicalEndpointIndex k j (!e) := by
  cases e <;> simp [canonicalOptionalPairSwap, canonicalEndpointIndex]

@[simp]
theorem canonicalOptionalPairSwap_symm_even_of_ne
    (k : ℕ) {i j : Fin k} (hij : i ≠ j) (e : Bool) :
    (canonicalOptionalPairSwap k j e).symm (canonicalEvenIndex k i) =
      canonicalEvenIndex k i := by
  cases e
  · simp
  · change (Equiv.swap (canonicalEvenIndex k j) (canonicalOddIndex k j))
        (canonicalEvenIndex k i) = canonicalEvenIndex k i
    exact Equiv.swap_apply_of_ne_of_ne
      ((canonicalEvenIndex_injective k).ne hij)
      (canonicalEvenIndex_ne_oddIndex k i j)

@[simp]
theorem canonicalOptionalPairSwap_symm_odd_of_ne
    (k : ℕ) {i j : Fin k} (hij : i ≠ j) (e : Bool) :
    (canonicalOptionalPairSwap k j e).symm (canonicalOddIndex k i) =
      canonicalOddIndex k i := by
  cases e
  · simp
  · change (Equiv.swap (canonicalEvenIndex k j) (canonicalOddIndex k j))
        (canonicalOddIndex k i) = canonicalOddIndex k i
    exact Equiv.swap_apply_of_ne_of_ne
      (canonicalOddIndex_ne_evenIndex k i j)
      ((canonicalOddIndex_injective k).ne hij)

@[simp]
theorem canonicalOptionalPairSwap_symm_endpoint_of_ne
    (k : ℕ) {i j : Fin k} (hij : i ≠ j) (e f : Bool) :
    (canonicalOptionalPairSwap k j e).symm
        (canonicalEndpointIndex k i f) =
      canonicalEndpointIndex k i f := by
  cases f <;> simp [hij]

@[simp]
theorem nestedTupleToFin_pair_even_castSucc
    {E : Type} {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E)
    (j : Fin k) :
    nestedTupleToFin (2 * (k + 1)) ((past, u), v)
        (canonicalEvenIndex (k + 1) j.castSucc) =
      nestedTupleToFin (2 * k) past (canonicalEvenIndex k j) := by
  simp only [Nat.mul_succ, nestedTupleToFin]
  rw [show (canonicalEvenIndex (k + 1) j.castSucc) =
      (canonicalEvenIndex k j).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp

@[simp]
theorem nestedTupleToFin_pair_odd_castSucc
    {E : Type} {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E)
    (j : Fin k) :
    nestedTupleToFin (2 * (k + 1)) ((past, u), v)
        (canonicalOddIndex (k + 1) j.castSucc) =
      nestedTupleToFin (2 * k) past (canonicalOddIndex k j) := by
  simp only [Nat.mul_succ, nestedTupleToFin]
  rw [show (canonicalOddIndex (k + 1) j.castSucc) =
      (canonicalOddIndex k j).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp

@[simp]
theorem nestedTupleToFin_pair_even_last
    {E : Type} {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E) :
    nestedTupleToFin (2 * (k + 1)) ((past, u), v)
        (canonicalEvenIndex (k + 1) (Fin.last k)) = u := by
  simp only [Nat.mul_succ, nestedTupleToFin]
  rw [show (canonicalEvenIndex (k + 1) (Fin.last k)) =
      (Fin.last (2 * k)).castSucc by
    apply Fin.ext
    simp [canonicalEvenIndex]]
  simp

@[simp]
theorem nestedTupleToFin_pair_odd_last
    {E : Type} {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E) :
    nestedTupleToFin (2 * (k + 1)) ((past, u), v)
        (canonicalOddIndex (k + 1) (Fin.last k)) = v := by
  simp only [Nat.mul_succ, nestedTupleToFin]
  rw [show (canonicalOddIndex (k + 1) (Fin.last k)) = Fin.last (2 * k + 1) by
    apply Fin.ext
    simp [canonicalOddIndex]]
  simp

@[simp]
theorem orderedForestScores_canonicalMatching_pair_succ
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E) :
    orderedForestScores (E := E) canonicalMatchingForest (2 * (k + 1))
        ((past, u), v) =
      ((orderedForestScores (E := E) canonicalMatchingForest (2 * k) past, 0),
        squaredNormalizedInner u v) := by
  simp only [orderedForestScores, Nat.mul_succ, sequentialStatistic]
  simp [orderedForestScore, canonicalMatchingForest, nestedTupleToFin]
  rw [show (⟨2 * k, by omega⟩ : Fin (2 * k + 1)) = Fin.last (2 * k) by
    apply Fin.ext
    rfl]
  simp

/-- All canonical pair correlations exceed `t`, now expressed directly on a
`Fin (2*k)`-indexed family. -/
def canonicalFamilyMatchingEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (t : ℝ) : Set (Fin (2 * k) → E) :=
  {v | ∀ j : Fin k,
    t < squaredNormalizedInner
      (v (canonicalEvenIndex k j)) (v (canonicalOddIndex k j))}

/-- One cross-edge exceedance between endpoints `i` and `j`. -/
def canonicalFamilyCrossEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (i j : Fin (2 * k)) (s : ℝ) : Set (Fin (2 * k) → E) :=
  {v | s < squaredNormalizedInner (v i) (v j)}

/-- At least one selected canonical matching edge exceeds `s`. -/
def canonicalFamilySelectedEdgeFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (s : ℝ) : Set (Fin (2 * k) → E) :=
  ⋃ j : Fin k,
    canonicalFamilyCrossEvent
      (canonicalEvenIndex k j) (canonicalOddIndex k j) s

/-- The matching event together with an overshoot of at least one selected
edge. -/
def canonicalFamilySelectedOvershootFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (t c : ℝ) : Set (Fin (2 * k) → E) :=
  canonicalFamilyMatchingEvent k t ∩
    canonicalFamilySelectedEdgeFailure k (c * t)

theorem measurableSet_canonicalFamilyMatchingEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) (t : ℝ) :
    MeasurableSet (canonicalFamilyMatchingEvent (E := E) k t) := by
  rw [show canonicalFamilyMatchingEvent (E := E) k t =
      ⋂ j : Fin k,
        {v | t < squaredNormalizedInner
          (v (canonicalEvenIndex k j)) (v (canonicalOddIndex k j))} by
    ext v
    simp [canonicalFamilyMatchingEvent]]
  refine MeasurableSet.iInter fun j ↦ ?_
  have hpair : Measurable (fun v : Fin (2 * k) → E ↦
      (v (canonicalEvenIndex k j), v (canonicalOddIndex k j))) :=
    (measurable_pi_apply (canonicalEvenIndex k j)).prodMk
      (measurable_pi_apply (canonicalOddIndex k j))
  have hscore : Measurable (fun v : Fin (2 * k) → E ↦
      squaredNormalizedInner
        (v (canonicalEvenIndex k j)) (v (canonicalOddIndex k j))) := by
    change Measurable
      ((Function.uncurry (squaredNormalizedInner (E := E))) ∘
        fun v : Fin (2 * k) → E ↦
          (v (canonicalEvenIndex k j), v (canonicalOddIndex k j)))
    exact (measurable_uncurry_squaredNormalizedInner (E := E)).comp hpair
  exact measurableSet_lt measurable_const hscore

theorem measurableSet_canonicalFamilyCrossEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} (i j : Fin (2 * k)) (s : ℝ) :
    MeasurableSet (canonicalFamilyCrossEvent (E := E) i j s) := by
  have hpair : Measurable (fun v : Fin (2 * k) → E ↦ (v i, v j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hscore : Measurable (fun v : Fin (2 * k) → E ↦
      squaredNormalizedInner (v i) (v j)) := by
    change Measurable
      ((Function.uncurry (squaredNormalizedInner (E := E))) ∘
        fun v : Fin (2 * k) → E ↦ (v i, v j))
    exact (measurable_uncurry_squaredNormalizedInner (E := E)).comp hpair
  exact measurableSet_lt measurable_const hscore

theorem measurableSet_canonicalFamilySelectedEdgeFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) (s : ℝ) :
    MeasurableSet (canonicalFamilySelectedEdgeFailure (E := E) k s) :=
  MeasurableSet.iUnion fun j ↦
    measurableSet_canonicalFamilyCrossEvent
      (E := E) (canonicalEvenIndex k j) (canonicalOddIndex k j) s

theorem measurableSet_canonicalFamilySelectedOvershootFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) (t c : ℝ) :
    MeasurableSet (canonicalFamilySelectedOvershootFailure (E := E) k t c) :=
  (measurableSet_canonicalFamilyMatchingEvent (E := E) k t).inter
    (measurableSet_canonicalFamilySelectedEdgeFailure (E := E) k (c * t))

/-- Swapping the two endpoints of any one canonical pair preserves the
whole matching event. -/
theorem preimage_canonicalFamilyMatchingEvent_optionalPairSwap
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (j : Fin k) (e : Bool) (t : ℝ) :
    permuteColumns (E := E) (canonicalOptionalPairSwap k j e) ⁻¹'
        canonicalFamilyMatchingEvent (E := E) k t =
      canonicalFamilyMatchingEvent (E := E) k t := by
  ext v
  simp only [Set.mem_preimage]
  unfold canonicalFamilyMatchingEvent
  have hedge : ∀ i : Fin k,
      t < squaredNormalizedInner
          ((permuteColumns (canonicalOptionalPairSwap k j e) v)
            (canonicalEvenIndex k i))
          ((permuteColumns (canonicalOptionalPairSwap k j e) v)
            (canonicalOddIndex k i)) ↔
        t < squaredNormalizedInner
          (v (canonicalEvenIndex k i)) (v (canonicalOddIndex k i)) := by
    intro i
    by_cases hij : i = j
    · subst i
      cases e
      · simp [permuteColumns]
      · simp [permuteColumns, squaredNormalizedInner_comm]
    · rw [show (permuteColumns (canonicalOptionalPairSwap k j e) v)
            (canonicalEvenIndex k i) = v (canonicalEvenIndex k i) by
          simp [permuteColumns, hij],
        show (permuteColumns (canonicalOptionalPairSwap k j e) v)
            (canonicalOddIndex k i) = v (canonicalOddIndex k i) by
          simp [permuteColumns, hij]]
  constructor
  · intro h i
    exact (hedge i).mp (h i)
  · intro h i
    exact (hedge i).mpr (h i)

/-- Swapping the first pair transports a root-to-root cross edge to the
chosen endpoint of that pair. -/
theorem preimage_matching_inter_rootCross_optionalPairSwap_first
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (a b : Fin k) (hab : a ≠ b) (e : Bool) (t s : ℝ) :
    permuteColumns (E := E) (canonicalOptionalPairSwap k a e) ⁻¹'
        (canonicalFamilyMatchingEvent (E := E) k t ∩
          canonicalFamilyCrossEvent
            (canonicalEvenIndex k a) (canonicalEvenIndex k b) s) =
      canonicalFamilyMatchingEvent (E := E) k t ∩
        canonicalFamilyCrossEvent
          (canonicalEndpointIndex k a e) (canonicalEvenIndex k b) s := by
  rw [preimage_inter,
    preimage_canonicalFamilyMatchingEvent_optionalPairSwap]
  congr 1
  ext v
  unfold canonicalFamilyCrossEvent
  change
    (s < squaredNormalizedInner
      ((permuteColumns (canonicalOptionalPairSwap k a e) v)
        (canonicalEvenIndex k a))
      ((permuteColumns (canonicalOptionalPairSwap k a e) v)
        (canonicalEvenIndex k b))) ↔
      s < squaredNormalizedInner
        (v (canonicalEndpointIndex k a e)) (v (canonicalEvenIndex k b))
  simp [permuteColumns, hab.symm]

/-- Swapping the second pair transports the remaining root endpoint while
leaving an endpoint of a distinct first pair fixed. -/
theorem preimage_matching_inter_endpointRoot_optionalPairSwap_second
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (a b : Fin k) (hab : a ≠ b) (ea eb : Bool) (t s : ℝ) :
    permuteColumns (E := E) (canonicalOptionalPairSwap k b eb) ⁻¹'
        (canonicalFamilyMatchingEvent (E := E) k t ∩
          canonicalFamilyCrossEvent
            (canonicalEndpointIndex k a ea) (canonicalEvenIndex k b) s) =
      canonicalFamilyMatchingEvent (E := E) k t ∩
        canonicalFamilyCrossEvent
          (canonicalEndpointIndex k a ea) (canonicalEndpointIndex k b eb) s := by
  rw [preimage_inter,
    preimage_canonicalFamilyMatchingEvent_optionalPairSwap]
  congr 1
  ext v
  unfold canonicalFamilyCrossEvent
  change
    (s < squaredNormalizedInner
      ((permuteColumns (canonicalOptionalPairSwap k b eb) v)
        (canonicalEndpointIndex k a ea))
      ((permuteColumns (canonicalOptionalPairSwap k b eb) v)
        (canonicalEvenIndex k b))) ↔
      s < squaredNormalizedInner
        (v (canonicalEndpointIndex k a ea))
        (v (canonicalEndpointIndex k b eb))
  simp [permuteColumns, hab]

/-- The recursive forest definition of the canonical matching is exactly the
direct finite-family matching event. -/
theorem preimage_canonicalFamilyMatchingEvent_nestedTupleToFin
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (t : ℝ) :
    nestedTupleToFin (α := E) (2 * k) ⁻¹'
        canonicalFamilyMatchingEvent (E := E) k t =
      canonicalGaussianMatchingEvent (E := E) k t := by
  ext z
  induction k with
  | zero =>
      simp [canonicalFamilyMatchingEvent, canonicalGaussianMatchingEvent,
        canonicalMatchingScoreEvent, orderedForestScores, sequentialStatistic]
  | succ k ih =>
      rcases z with ⟨⟨past, u⟩, v⟩
      unfold canonicalFamilyMatchingEvent canonicalGaussianMatchingEvent
      simp only [Set.mem_preimage]
      rw [orderedForestScores_canonicalMatching_pair_succ]
      change
        (∀ j : Fin (k + 1),
          t < squaredNormalizedInner
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalEvenIndex (k + 1) j))
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalOddIndex (k + 1) j))) ↔
          ((orderedForestScores (E := E) canonicalMatchingForest (2 * k) past ∈
              canonicalMatchingScoreEvent t k ∧ (0 : ℝ) ∈ Set.univ) ∧
            squaredNormalizedInner u v ∈ Set.Ioi t)
      simp only [Set.mem_univ, and_true, Set.mem_Ioi]
      change
        (∀ j : Fin (k + 1),
          t < squaredNormalizedInner
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalEvenIndex (k + 1) j))
            (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
              (canonicalOddIndex (k + 1) j))) ↔
          (past ∈ canonicalGaussianMatchingEvent (E := E) k t ∧
            t < squaredNormalizedInner u v)
      rw [← ih past]
      simp only [Set.mem_preimage]
      constructor
      · intro h
        constructor
        · intro j
          have hj := h j.castSucc
          rw [nestedTupleToFin_pair_even_castSucc past u v j,
            nestedTupleToFin_pair_odd_castSucc past u v j] at hj
          exact hj
        · have hlast := h (Fin.last k)
          rw [nestedTupleToFin_pair_even_last past u v,
            nestedTupleToFin_pair_odd_last past u v] at hlast
          exact hlast
      · rintro ⟨hold, hlast⟩ j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · rw [nestedTupleToFin_pair_even_last past u v,
            nestedTupleToFin_pair_odd_last past u v]
          exact hlast
        · rw [nestedTupleToFin_pair_even_castSucc past u v i,
            nestedTupleToFin_pair_odd_castSucc past u v i]
          exact hold i

/-- Direct recursion for membership in the finite-family matching event. -/
theorem nestedTupleToFin_mem_canonicalFamilyMatchingEvent_pair_iff
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E) (t : ℝ) :
    nestedTupleToFin (2 * (k + 1)) ((past, u), v) ∈
        canonicalFamilyMatchingEvent (E := E) (k + 1) t ↔
      (nestedTupleToFin (2 * k) past ∈
          canonicalFamilyMatchingEvent (E := E) k t ∧
        t < squaredNormalizedInner u v) := by
  unfold canonicalFamilyMatchingEvent
  constructor
  · intro h
    constructor
    · intro j
      have hj := h j.castSucc
      rw [nestedTupleToFin_pair_even_castSucc past u v j,
        nestedTupleToFin_pair_odd_castSucc past u v j] at hj
      exact hj
    · have hlast := h (Fin.last k)
      rw [nestedTupleToFin_pair_even_last past u v,
        nestedTupleToFin_pair_odd_last past u v] at hlast
      exact hlast
  · rintro ⟨hold, hlast⟩ j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · rw [nestedTupleToFin_pair_even_last past u v,
        nestedTupleToFin_pair_odd_last past u v]
      exact hlast
    · rw [nestedTupleToFin_pair_even_castSucc past u v i,
        nestedTupleToFin_pair_odd_castSucc past u v i]
      exact hold i

/-- A cross edge between two old canonical roots is unchanged after a new
pair is appended. -/
theorem nestedTupleToFin_mem_canonicalFamilyCrossEvent_pair_castSucc_iff
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E)
    (i j : Fin k) (s : ℝ) :
    nestedTupleToFin (2 * (k + 1)) ((past, u), v) ∈
        canonicalFamilyCrossEvent
          (canonicalEvenIndex (k + 1) i.castSucc)
          (canonicalEvenIndex (k + 1) j.castSucc) s ↔
      nestedTupleToFin (2 * k) past ∈
        canonicalFamilyCrossEvent
          (canonicalEvenIndex k i) (canonicalEvenIndex k j) s := by
  unfold canonicalFamilyCrossEvent
  change
    (s < squaredNormalizedInner
      (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
        (canonicalEvenIndex (k + 1) i.castSucc))
      (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
        (canonicalEvenIndex (k + 1) j.castSucc))) ↔
      s < squaredNormalizedInner
        (nestedTupleToFin (2 * k) past (canonicalEvenIndex k i))
        (nestedTupleToFin (2 * k) past (canonicalEvenIndex k j))
  rw [nestedTupleToFin_pair_even_castSucc past u v i,
    nestedTupleToFin_pair_even_castSucc past u v j]

/-- A cross edge from an old root to the newly appended root has the stated
squared-normalized-inner-product form. -/
theorem nestedTupleToFin_mem_canonicalFamilyCrossEvent_pair_last_iff
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E)
    (i : Fin k) (s : ℝ) :
    nestedTupleToFin (2 * (k + 1)) ((past, u), v) ∈
        canonicalFamilyCrossEvent
          (canonicalEvenIndex (k + 1) i.castSucc)
          (canonicalEvenIndex (k + 1) (Fin.last k)) s ↔
      s < squaredNormalizedInner
        (nestedTupleToFin (2 * k) past (canonicalEvenIndex k i)) u := by
  unfold canonicalFamilyCrossEvent
  change
    (s < squaredNormalizedInner
      (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
        (canonicalEvenIndex (k + 1) i.castSucc))
      (nestedTupleToFin (2 * (k + 1)) ((past, u), v)
        (canonicalEvenIndex (k + 1) (Fin.last k)))) ↔ _
  rw [nestedTupleToFin_pair_even_castSucc past u v i,
    nestedTupleToFin_pair_even_last past u v]

/-- Appending one pair splits the selected-edge union into an old failure or
a failure of the newest selected edge. -/
theorem nestedTupleToFin_mem_canonicalFamilySelectedEdgeFailure_pair_iff
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (past : NestedTuple E (2 * k)) (u v : E) (s : ℝ) :
    nestedTupleToFin (2 * (k + 1)) ((past, u), v) ∈
        canonicalFamilySelectedEdgeFailure (E := E) (k + 1) s ↔
      (nestedTupleToFin (2 * k) past ∈
          canonicalFamilySelectedEdgeFailure (E := E) k s ∨
        s < squaredNormalizedInner u v) := by
  unfold canonicalFamilySelectedEdgeFailure canonicalFamilyCrossEvent
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj⟩
    revert hj
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · intro hj
      right
      rw [nestedTupleToFin_pair_even_last past u v,
        nestedTupleToFin_pair_odd_last past u v] at hj
      exact hj
    · intro hj
      left
      refine ⟨i, ?_⟩
      rw [nestedTupleToFin_pair_even_castSucc past u v i,
        nestedTupleToFin_pair_odd_castSucc past u v i] at hj
      exact hj
  · rintro (hold | hlast)
    · rcases hold with ⟨i, hi⟩
      refine ⟨i.castSucc, ?_⟩
      rw [nestedTupleToFin_pair_even_castSucc past u v i,
        nestedTupleToFin_pair_odd_castSucc past u v i]
      exact hi
    · refine ⟨Fin.last k, ?_⟩
      rw [nestedTupleToFin_pair_even_last past u v,
        nestedTupleToFin_pair_odd_last past u v]
      exact hlast

/-- Under the natural overshoot condition `t ≤ c*t`, the recursive Gaussian
selected-overshoot event is exactly the direct finite-family event. -/
theorem preimage_canonicalFamilySelectedOvershootFailure_nestedTupleToFin
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (t c : ℝ) (htc : t ≤ c * t) :
    nestedTupleToFin (α := E) (2 * k) ⁻¹'
        canonicalFamilySelectedOvershootFailure (E := E) k t c =
      canonicalGaussianSelectedOvershootEvent (E := E) k t c := by
  ext z
  induction k with
  | zero =>
      simp [canonicalFamilySelectedOvershootFailure,
        canonicalFamilyMatchingEvent, canonicalFamilySelectedEdgeFailure,
        canonicalGaussianSelectedOvershootEvent,
        canonicalMatchingSelectedOvershootScoreEvent]
  | succ k ih =>
      rcases z with ⟨⟨past, u⟩, v⟩
      unfold canonicalFamilySelectedOvershootFailure
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      rw [nestedTupleToFin_mem_canonicalFamilyMatchingEvent_pair_iff,
        nestedTupleToFin_mem_canonicalFamilySelectedEdgeFailure_pair_iff]
      unfold canonicalGaussianSelectedOvershootEvent
      simp only [Set.mem_preimage]
      rw [orderedForestScores_canonicalMatching_pair_succ]
      simp only [canonicalMatchingSelectedOvershootScoreEvent]
      change
        ((nestedTupleToFin (2 * k) past ∈
              canonicalFamilyMatchingEvent (E := E) k t ∧
            t < squaredNormalizedInner u v) ∧
          (nestedTupleToFin (2 * k) past ∈
              canonicalFamilySelectedEdgeFailure (E := E) k (c * t) ∨
            c * t < squaredNormalizedInner u v)) ↔
        ((((orderedForestScores (E := E) canonicalMatchingForest (2 * k) past ∈
              canonicalMatchingSelectedOvershootScoreEvent t c k) ∧
            (0 : ℝ) ∈ Set.univ) ∧
              squaredNormalizedInner u v ∈ Set.Ioi t) ∨
          (((orderedForestScores (E := E) canonicalMatchingForest (2 * k) past ∈
              canonicalMatchingScoreEvent t k) ∧
            (0 : ℝ) ∈ Set.univ) ∧
              squaredNormalizedInner u v ∈ Set.Ioi (c * t)))
      simp only [Set.mem_univ, and_true, Set.mem_Ioi]
      have hsel := ih past
      simp only [Set.mem_preimage] at hsel
      unfold canonicalGaussianSelectedOvershootEvent at hsel
      simp only [Set.mem_preimage] at hsel
      have hmatch := Set.ext_iff.mp
        (preimage_canonicalFamilyMatchingEvent_nestedTupleToFin
          (E := E) k t) past
      simp only [Set.mem_preimage] at hmatch
      unfold canonicalGaussianMatchingEvent at hmatch
      simp only [Set.mem_preimage] at hmatch
      rw [← hsel, ← hmatch]
      unfold canonicalFamilySelectedOvershootFailure
      constructor
      · rintro ⟨⟨hM, hT⟩, hB | hC⟩
        · exact Or.inl ⟨⟨hM, hB⟩, hT⟩
        · exact Or.inr ⟨hM, hC⟩
      · rintro (hB | hC)
        · rcases hB with ⟨⟨hM, hB⟩, hT⟩
          exact ⟨⟨hM, hT⟩, Or.inl hB⟩
        · rcases hC with ⟨hM, hC⟩
          exact ⟨⟨hM, htc.trans_lt hC⟩, Or.inr hC⟩

private theorem measurable_orderedForestScores
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (p : ℕ) :
    Measurable (orderedForestScores (E := E) canonicalMatchingForest p) := by
  exact measurable_sequentialStatistic
    (orderedForestScore (E := E) canonicalMatchingForest)
    (measurable_uncurry_orderedForestScore canonicalMatchingForest) p

/-- Exact probability of the canonical Gaussian matching event. -/
theorem canonicalGaussianMatchingEvent_probability
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (k : ℕ) (t : ℝ) :
    (nestedProductMeasure (stdGaussian E) (2 * k)).real
        (canonicalGaussianMatchingEvent (E := E) k t) =
      ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^ k := by
  have hmeas := measurable_orderedForestScores (E := E) (2 * k)
  have hset := measurableSet_canonicalMatchingScoreEvent t k
  unfold canonicalGaussianMatchingEvent
  rw [measureReal_def, ← Measure.map_apply hmeas hset,
    map_orderedForestScores_eq_nestedProduct
      canonicalMatchingForest m hdim hm (2 * k)]
  exact canonicalMatchingScoreEvent_probability m k t

/-- Exact probability of the same matching event on the ordinary finite
Gaussian product space. -/
theorem canonicalFamilyMatchingEvent_probability
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (k : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (canonicalFamilyMatchingEvent (E := E) k t) =
      ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^ k := by
  have hread := measurePreserving_nestedTupleToFin (stdGaussian E) (2 * k)
  have hset := measurableSet_canonicalFamilyMatchingEvent (E := E) k t
  rw [← hread.map_eq, measureReal_def,
    Measure.map_apply (measurable_nestedTupleToFin (2 * k)) hset,
    ← measureReal_def,
    preimage_canonicalFamilyMatchingEvent_nestedTupleToFin]
  exact canonicalGaussianMatchingEvent_probability m hdim hm k t

/-- Finite Gaussian probability bound for a selected-edge overshoot. -/
theorem canonicalGaussianSelectedOvershootEvent_probability_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (k : ℕ) (t c : ℝ) :
    (nestedProductMeasure (stdGaussian E) (2 * k)).real
        (canonicalGaussianSelectedOvershootEvent (E := E) k t c) ≤
      (k : ℝ) *
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t)) *
        ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^
          (k - 1) := by
  have hmeas := measurable_orderedForestScores (E := E) (2 * k)
  have hset :=
    measurableSet_canonicalMatchingSelectedOvershootScoreEvent t c k
  unfold canonicalGaussianSelectedOvershootEvent
  rw [measureReal_def, ← Measure.map_apply hmeas hset,
    map_orderedForestScores_eq_nestedProduct
      canonicalMatchingForest m hdim hm (2 * k)]
  exact canonicalMatchingSelectedOvershootScoreEvent_probability_le m k t c

/-- Positivity of an interior Beta half-tail, recorded in the real-valued
measure convention used by the relative-probability estimates. -/
theorem betaMeasure_half_Ioi_real_pos
    {b t : ℝ} (hb : 1 < b) (ht : 0 < t) (ht1 : t < 1) :
    0 < (betaMeasure (1 / 2) b).real (Ioi t) := by
  rw [betaMeasure_half_Ioi_real_eq_tailIntegral_div hb ht ht1]
  exact div_pos (betaHalfTailIntegral_pos hb ht ht1)
    (beta_pos (by norm_num) (zero_lt_one.trans hb))

/-- Relative selected-overshoot probability, stated entirely as a quotient
of ordinary event probabilities. -/
theorem canonicalGaussianSelectedOvershoot_relative_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 4 ≤ m)
    (k : ℕ) (hk : 1 ≤ k) {t c : ℝ}
    (ht : 0 < t) (ht1 : t < 1) :
    (nestedProductMeasure (stdGaussian E) (2 * k)).real
        (canonicalGaussianSelectedOvershootEvent (E := E) k t c) /
      (nestedProductMeasure (stdGaussian E) (2 * k)).real
        (canonicalGaussianMatchingEvent (E := E) k t) ≤
      (k : ℝ) *
        ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t)) /
          (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) := by
  let q : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)
  let qc : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t))
  have hm2 : 2 ≤ m := by omega
  have hb : 1 < (((m - 1 : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hq : 0 < q := betaMeasure_half_Ioi_real_pos hb ht ht1
  have hnum := canonicalGaussianSelectedOvershootEvent_probability_le
    m hdim hm2 k t c
  rw [canonicalGaussianMatchingEvent_probability m hdim hm2 k t]
  apply (div_le_iff₀ (pow_pos hq k)).2
  calc
    (nestedProductMeasure (stdGaussian E) (2 * k)).real
          (canonicalGaussianSelectedOvershootEvent (E := E) k t c) ≤
        (k : ℝ) * qc * q ^ (k - 1) := by simpa [q, qc] using hnum
    _ = ((k : ℝ) * (qc / q)) * q ^ k := by
      have hpow : q ^ k = q ^ (k - 1) * q := by
        calc
          q ^ k = q ^ ((k - 1) + 1) := by congr 1 <;> omega
          _ = q ^ (k - 1) * q := by rw [pow_succ]
      rw [hpow]
      field_simp [hq.ne']
    _ = ((k : ℝ) *
          ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t)) /
            (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t))) *
          q ^ k := by rfl

/-- Finite-family version of the selected-overshoot numerator bound. -/
theorem canonicalFamilySelectedOvershootFailure_probability_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (k : ℕ) (t c : ℝ) (htc : t ≤ c * t) :
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (canonicalFamilySelectedOvershootFailure (E := E) k t c) ≤
      (k : ℝ) *
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t)) *
        ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^
          (k - 1) := by
  have hread := measurePreserving_nestedTupleToFin (stdGaussian E) (2 * k)
  have hset := measurableSet_canonicalFamilySelectedOvershootFailure
    (E := E) k t c
  rw [← hread.map_eq, measureReal_def,
    Measure.map_apply (measurable_nestedTupleToFin (2 * k)) hset,
    ← measureReal_def,
    preimage_canonicalFamilySelectedOvershootFailure_nestedTupleToFin
      k t c htc]
  exact canonicalGaussianSelectedOvershootEvent_probability_le
    m hdim hm k t c

/-- Finite relative selected-overshoot bound on the ordinary product space. -/
theorem canonicalFamilySelectedOvershoot_relative_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 4 ≤ m)
    (k : ℕ) (hk : 1 ≤ k) {t c : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (htc : t ≤ c * t) :
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (canonicalFamilySelectedOvershootFailure (E := E) k t c) /
      (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (canonicalFamilyMatchingEvent (E := E) k t) ≤
      (k : ℝ) *
        ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t)) /
          (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) := by
  let q : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)
  let qc : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t))
  have hm2 : 2 ≤ m := by omega
  have hb : 1 < (((m - 1 : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hq : 0 < q := betaMeasure_half_Ioi_real_pos hb ht ht1
  have hnum := canonicalFamilySelectedOvershootFailure_probability_le
    (E := E) m hdim hm2 k t c htc
  rw [canonicalFamilyMatchingEvent_probability m hdim hm2 k t]
  apply (div_le_iff₀ (pow_pos hq k)).2
  calc
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
          (canonicalFamilySelectedOvershootFailure (E := E) k t c) ≤
        (k : ℝ) * qc * q ^ (k - 1) := by simpa [q, qc] using hnum
    _ = ((k : ℝ) * (qc / q)) * q ^ k := by
      have hpow : q ^ k = q ^ (k - 1) * q := by
        calc
          q ^ k = q ^ ((k - 1) + 1) := by congr 1 <;> omega
          _ = q ^ (k - 1) * q := by rw [pow_succ]
      rw [hpow]
      field_simp [hq.ne']
    _ = ((k : ℝ) *
          ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi (c * t)) /
            (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t))) *
          q ^ k := by rfl

/-- Relative selected-overshoot probability in the canonical
`m`-dimensional Euclidean residual model. -/
def canonicalResidualSelectedOvershootRelative
    (k m p : ℕ) (x c : ℝ) : ℝ :=
  let t := classicalCoherenceThreshold m p x / (m : ℝ)
  (nestedProductMeasure
      (stdGaussian (EuclideanSpace ℝ (Fin m))) (2 * k)).real
      (canonicalGaussianSelectedOvershootEvent k t c) /
    (nestedProductMeasure
      (stdGaussian (EuclideanSpace ℝ (Fin m))) (2 * k)).real
      (canonicalGaussianMatchingEvent k t)

/-- Along every all-gap sequence, the relative bad probability that a
selected edge exceeds `c>1` times the matching threshold tends to zero. -/
theorem tendsto_canonicalResidualSelectedOvershootRelative_zero
    (k : ℕ) (hk : 1 ≤ k)
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {c : ℝ} (hc : 1 < c) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalResidualSelectedOvershootRelative k (mseq p) p x c)
      atTop (nhds 0) := by
  have hratio := tendsto_betaCorrelationOvershootRatio_zero hadm hc x
  have hupper : Tendsto (fun p : ℕ ↦
      (k : ℝ) * betaCorrelationOvershootRatio c (mseq p) p x)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hratio)
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ by
      unfold canonicalResidualSelectedOvershootRelative
      dsimp only
      exact div_nonneg measureReal_nonneg measureReal_nonneg
  · filter_upwards [hadm, eventually_ge_atTop 4,
      ha.eventually (eventually_gt_atTop 0),
      ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with p hp hp4 hapos ht1
    have hm4 : 4 ≤ mseq p := hp4.trans hp.2
    have hm0 : (0 : ℝ) < (mseq p : ℝ) := by positivity
    have hthreshold : 0 < classicalCoherenceThreshold (mseq p) p x := by
      simpa [classicalCoherenceThreshold] using hapos
    have hfinite := canonicalGaussianSelectedOvershoot_relative_le
      (E := EuclideanSpace ℝ (Fin (mseq p)))
      (mseq p) (by simp) hm4 k hk
      (div_pos hthreshold hm0) ht1
      (c := c)
    simpa [canonicalResidualSelectedOvershootRelative,
      betaCorrelationOvershootRatio] using hfinite
  · simpa [betaCorrelationOvershootRatio] using hupper

/-- The same selected-overshoot relative probability on the ordinary finite
Gaussian product space. -/
def canonicalResidualFamilySelectedOvershootRelative
    (k m p : ℕ) (x c : ℝ) : ℝ :=
  let t := classicalCoherenceThreshold m p x / (m : ℝ)
  (Measure.pi fun _ : Fin (2 * k) ↦
      stdGaussian (EuclideanSpace ℝ (Fin m))).real
      (canonicalFamilySelectedOvershootFailure k t c) /
    (Measure.pi fun _ : Fin (2 * k) ↦
      stdGaussian (EuclideanSpace ℝ (Fin m))).real
      (canonicalFamilyMatchingEvent k t)

/-- Family-space selected overshoots also have vanishing relative
probability along every all-gap sequence. -/
theorem tendsto_canonicalResidualFamilySelectedOvershootRelative_zero
    (k : ℕ) (hk : 1 ≤ k)
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    {c : ℝ} (hc : 1 < c) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalResidualFamilySelectedOvershootRelative k (mseq p) p x c)
      atTop (nhds 0) := by
  have hratio := tendsto_betaCorrelationOvershootRatio_zero hadm hc x
  have hupper : Tendsto (fun p : ℕ ↦
      (k : ℝ) * betaCorrelationOvershootRatio c (mseq p) p x)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hratio)
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ by
      unfold canonicalResidualFamilySelectedOvershootRelative
      dsimp only
      exact div_nonneg measureReal_nonneg measureReal_nonneg
  · filter_upwards [hadm, eventually_ge_atTop 4,
      ha.eventually (eventually_gt_atTop 0),
      ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with p hp hp4 hapos ht1
    have hm4 : 4 ≤ mseq p := hp4.trans hp.2
    have hm0 : (0 : ℝ) < (mseq p : ℝ) := by positivity
    have hthreshold : 0 < classicalCoherenceThreshold (mseq p) p x := by
      simpa [classicalCoherenceThreshold] using hapos
    have htpos : 0 < classicalCoherenceThreshold (mseq p) p x /
        (mseq p : ℝ) := div_pos hthreshold hm0
    have htc : classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ) ≤
        c * (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) := by
      nlinarith [hc]
    have hfinite := canonicalFamilySelectedOvershoot_relative_le
      (E := EuclideanSpace ℝ (Fin (mseq p)))
      (mseq p) (by simp) hm4 k hk htpos ht1 htc
    simpa [canonicalResidualFamilySelectedOvershootRelative,
      betaCorrelationOvershootRatio] using hfinite
  · simpa [betaCorrelationOvershootRatio] using hupper

/-! ## Cross-edge union calculus -/

/-- A finite union of bad events remains small relative to a conditioning
event whenever every one-event intersection has the corresponding product
bound.  This is the exact no-RCP form used for cross edges. -/
theorem relative_inter_iUnion_le_card_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (M : Set Ω) (C : ι → Set Ω)
    {q r : ℝ} (hq : 0 < q) (_hr : 0 ≤ r)
    (hM : μ.real M = q)
    (hinter : ∀ i, μ.real (M ∩ C i) ≤ q * r) :
    μ.real (M ∩ ⋃ i, C i) / μ.real M ≤
      (Fintype.card ι : ℝ) * r := by
  have hset : M ∩ ⋃ i, C i = ⋃ i, (M ∩ C i) := by
    ext ω
    simp only [mem_inter_iff, mem_iUnion]
    aesop
  rw [hset, hM]
  apply (div_le_iff₀ hq).2
  calc
    μ.real (⋃ i, M ∩ C i) ≤ ∑ i, μ.real (M ∩ C i) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, q * r := by
      gcongr with i
      exact hinter i
    _ = q * ((Fintype.card ι : ℝ) * r) := by
      simp
      ring
    _ = ((Fintype.card ι : ℝ) * r) * q := by ring

/-- The one-edge Beta Markov envelope at the coherence threshold is exactly
the reciprocal threshold. -/
theorem betaCorrelationTailProbability_le_inv_threshold
    {m p : ℕ} {x : ℝ} (hm : 2 ≤ m)
    (hthreshold : 0 < classicalCoherenceThreshold m p x) :
    betaCorrelationTailProbability m p x ≤
      1 / classicalCoherenceThreshold m p x := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hmarkov := betaMeasure_half_sub_half_Ioi_real_le
    hm (t := classicalCoherenceThreshold m p x / (m : ℝ))
      (div_pos hthreshold hm0)
  unfold betaCorrelationTailProbability
  change (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
      (Ioi (classicalCoherenceThreshold m p x / (m : ℝ))) ≤ _
  calc
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
        (Ioi (classicalCoherenceThreshold m p x / (m : ℝ))) ≤
      1 / ((m : ℝ) *
        (classicalCoherenceThreshold m p x / (m : ℝ))) := hmarkov
    _ = 1 / classicalCoherenceThreshold m p x := by
      field_simp [hm0.ne']

/-- The reciprocal classical threshold vanishes. -/
theorem tendsto_inv_classicalCoherenceThreshold_zero (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      1 / classicalCoherenceThreshold 0 p x) atTop (nhds 0) :=
  (tendsto_classicalCoherenceThreshold_atTop x).const_div_atTop 1

/-- Consequently the single cross-edge Markov envelope vanishes uniformly
in every all-gap dimension sequence. -/
theorem tendsto_betaCorrelationTailProbability_zero_of_markov
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      betaCorrelationTailProbability (mseq p) p x) atTop (nhds 0) := by
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have hupper := tendsto_inv_classicalCoherenceThreshold_zero x
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ measureReal_nonneg
  · filter_upwards [hadm,
      ha.eventually (eventually_gt_atTop 0)] with p hp hapos
    exact betaCorrelationTailProbability_le_inv_threshold (hp.1.trans hp.2)
      (by simpa [classicalCoherenceThreshold] using hapos)
  · simpa [classicalCoherenceThreshold] using hupper

/-- Abstract all-gap cross-edge assembly.  Once forest independence supplies
the displayed one-cross-edge intersection bound, the finite union of all
cross-edge failures has vanishing relative probability.  The sample space is
allowed to vary with `p`, as it does for Euclidean residual dimension
`mseq p`. -/
theorem tendsto_relative_cross_iUnion_zero_of_intersection_bound
    {ι : Type*} [Fintype ι]
    {Ω : ℕ → Type} [∀ p, MeasurableSpace (Ω p)]
    (μ : ∀ p, Measure (Ω p))
    (M : ∀ p, Set (Ω p)) (C : ∀ p, ι → Set (Ω p))
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ)
    (hMpos : ∀ᶠ p in atTop, 0 < (μ p).real (M p))
    (hinter : ∀ᶠ p in atTop, ∀ i,
      (μ p).real (M p ∩ C p i) ≤
        (μ p).real (M p) *
          betaCorrelationTailProbability (mseq p) p x) :
    Tendsto (fun p : ℕ ↦
      (μ p).real (M p ∩ ⋃ i, C p i) / (μ p).real (M p))
      atTop (nhds 0) := by
  have htail := tendsto_betaCorrelationTailProbability_zero_of_markov hadm x
  have hupper : Tendsto (fun p : ℕ ↦
      (Fintype.card ι : ℝ) *
        betaCorrelationTailProbability (mseq p) p x)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul htail)
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦
      div_nonneg measureReal_nonneg measureReal_nonneg
  · filter_upwards [hMpos, hinter] with p hp hinterp
    exact relative_inter_iUnion_le_card_mul
      (μ p) (M p) (C p) hp measureReal_nonneg rfl hinterp
  · exact hupper

/-! ### An exact matching-plus-root-cross forest -/

/-- Modify the canonical matching forest by adding the cross edge between
the first endpoints `2*a` and `2*b` of two distinct canonical pairs. -/
def canonicalMatchingRootCrossForest (a b : ℕ) : OrderedForest where
  parent n :=
    if hodd : n % 2 = 1 then
      some ⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩
    else if hcross : n = 2 * b ∧ a < b then
      some ⟨2 * a, by omega⟩
    else none

@[simp]
theorem canonicalMatchingRootCross_factorMeasure_odd
    (m a b j : ℕ) :
    orderedForestFactorMeasure (canonicalMatchingRootCrossForest a b) m
        (2 * j + 1) =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
  simp [orderedForestFactorMeasure, canonicalMatchingRootCrossForest]

@[simp]
theorem canonicalMatchingRootCross_factorMeasure_special
    (m a b : ℕ) (hab : a < b) :
    orderedForestFactorMeasure (canonicalMatchingRootCrossForest a b) m
        (2 * b) =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
  simp [orderedForestFactorMeasure, canonicalMatchingRootCrossForest, hab]

@[simp]
theorem canonicalMatchingRootCross_factorMeasure_even_other
    (m a b j : ℕ) (hjb : j ≠ b) :
    orderedForestFactorMeasure (canonicalMatchingRootCrossForest a b) m
        (2 * j) = Measure.dirac 0 := by
  simp [orderedForestFactorMeasure, canonicalMatchingRootCrossForest, hjb]

@[simp]
theorem orderedForestScores_canonicalMatchingRootCross_pair_succ_special
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k a : ℕ} (ha : a < k)
    (past : NestedTuple E (2 * k)) (u v : E) :
    orderedForestScores (E := E) (canonicalMatchingRootCrossForest a k)
        (2 * (k + 1)) ((past, u), v) =
      ((orderedForestScores (E := E) (canonicalMatchingRootCrossForest a k)
          (2 * k) past,
        squaredNormalizedInner
          (nestedTupleToFin (2 * k) past
            (canonicalEvenIndex k ⟨a, ha⟩)) u),
        squaredNormalizedInner u v) := by
  simp only [orderedForestScores, Nat.mul_succ, sequentialStatistic]
  congr 1
  · simp only [orderedForestScore]
    rw [show (canonicalMatchingRootCrossForest a k).parent (2 * k) =
        some (canonicalEvenIndex k ⟨a, ha⟩) by
      simp [canonicalMatchingRootCrossForest, canonicalEvenIndex, ha]]
  · simp [orderedForestScore, canonicalMatchingRootCrossForest,
      nestedTupleToFin]
    rw [show (⟨2 * k, by omega⟩ : Fin (2 * k + 1)) = Fin.last (2 * k) by
      apply Fin.ext
      rfl]
    simp

@[simp]
theorem orderedForestScores_canonicalMatchingRootCross_pair_succ_other
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k a b : ℕ} (hbk : b ≠ k)
    (past : NestedTuple E (2 * k)) (u v : E) :
    orderedForestScores (E := E) (canonicalMatchingRootCrossForest a b)
        (2 * (k + 1)) ((past, u), v) =
      ((orderedForestScores (E := E) (canonicalMatchingRootCrossForest a b)
          (2 * k) past, 0), squaredNormalizedInner u v) := by
  simp only [orderedForestScores, Nat.mul_succ, sequentialStatistic]
  congr 1
  · have hkb : k ≠ b := fun h ↦ hbk h.symm
    simp [orderedForestScore, canonicalMatchingRootCrossForest, hkb]
  · simp [orderedForestScore, canonicalMatchingRootCrossForest,
      nestedTupleToFin]
    rw [show (⟨2 * k, by omega⟩ : Fin (2 * k + 1)) = Fin.last (2 * k) by
      apply Fin.ext
      rfl]
    simp

/-- Before the distinguished cross vertex `2*b` appears, the modified
forest produces exactly the canonical matching scores. -/
theorem orderedForestScores_canonicalMatchingRootCross_before
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : ℕ) : ∀ (k : ℕ), k ≤ b →
      ∀ past : NestedTuple E (2 * k),
        orderedForestScores (E := E) (canonicalMatchingRootCrossForest a b)
            (2 * k) past =
          orderedForestScores (E := E) canonicalMatchingForest (2 * k) past := by
  intro k hkb past
  induction k with
  | zero => rfl
  | succ k ih =>
      rcases past with ⟨⟨past, u⟩, v⟩
      have hne : b ≠ k := by omega
      rw [orderedForestScores_canonicalMatchingRootCross_pair_succ_other
          hne past u v,
        orderedForestScores_canonicalMatching_pair_succ past u v,
        ih (by omega)]

/-- Score-space event requiring all `k` matching edges to exceed `t` and,
when the pair indexed by `b` has appeared, the root cross edge to exceed
`s`. -/
def canonicalMatchingRootCrossScoreEvent (t s : ℝ) (b : ℕ) :
    (k : ℕ) → Set (NestedTuple ℝ (2 * k))
  | 0 => Set.univ
  | k + 1 =>
      ((canonicalMatchingRootCrossScoreEvent t s b k) ×ˢ
        (if b = k then Set.Ioi s else Set.univ)) ×ˢ Set.Ioi t

/-- Before pair `b` is present, the score-space cross event is just the
matching event. -/
theorem canonicalMatchingRootCrossScoreEvent_eq_before
    (t s : ℝ) (b : ℕ) : ∀ (k : ℕ), k ≤ b →
      canonicalMatchingRootCrossScoreEvent t s b k =
        canonicalMatchingScoreEvent t k := by
  intro k hkb
  induction k with
  | zero => rfl
  | succ k ih =>
      have hne : b ≠ k := by omega
      simp [canonicalMatchingRootCrossScoreEvent,
        canonicalMatchingScoreEvent, hne, ih (by omega)]

theorem measurableSet_canonicalMatchingRootCrossScoreEvent
    (t s : ℝ) (b : ℕ) :
    ∀ k, MeasurableSet (canonicalMatchingRootCrossScoreEvent t s b k) := by
  intro k
  induction k with
  | zero => simp [canonicalMatchingRootCrossScoreEvent]
  | succ k ih =>
      by_cases hbk : b = k
      · simpa [canonicalMatchingRootCrossScoreEvent, hbk] using
          ((ih.prod measurableSet_Ioi).prod measurableSet_Ioi)
      · simpa [canonicalMatchingRootCrossScoreEvent, hbk] using
          ((ih.prod MeasurableSet.univ).prod measurableSet_Ioi)

/-- Exact probability of the matching-plus-one-root-cross score event. -/
theorem canonicalMatchingRootCrossScoreEvent_probability
    (m a b k : ℕ) (hab : a < b) (t s : ℝ) :
    (nestedProductMeasureFamily
      (orderedForestFactorMeasure (canonicalMatchingRootCrossForest a b) m)
      (2 * k)).real
        (canonicalMatchingRootCrossScoreEvent t s b k) =
      ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^ k *
        (if b < k then
          (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi s)
        else 1) := by
  let q : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)
  let r : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi s)
  induction k with
  | zero =>
      simp [canonicalMatchingRootCrossScoreEvent,
        nestedProductMeasureFamily]
  | succ k ih =>
      change
        ((((nestedProductMeasureFamily
            (orderedForestFactorMeasure (canonicalMatchingRootCrossForest a b) m)
              (2 * k)).prod
              (orderedForestFactorMeasure (canonicalMatchingRootCrossForest a b) m
                (2 * k))).prod
              (orderedForestFactorMeasure (canonicalMatchingRootCrossForest a b) m
                (2 * k + 1))).real
          ((canonicalMatchingRootCrossScoreEvent t s b k ×ˢ
            (if b = k then Set.Ioi s else Set.univ)) ×ˢ Set.Ioi t)) = _
      rw [measureReal_prod_prod, measureReal_prod_prod, ih,
        canonicalMatchingRootCross_factorMeasure_odd]
      by_cases hbk : b = k
      · subst k
        rw [canonicalMatchingRootCross_factorMeasure_special m a b hab]
        simp [q, r, pow_succ]
        ring
      · rw [canonicalMatchingRootCross_factorMeasure_even_other m a b k
          (fun h ↦ hbk h.symm)]
        have hlt : b < k + 1 ↔ b < k := by omega
        by_cases hbklt : b < k
        · simp [hbk, hlt, hbklt, q, r, pow_succ]
          ring
        · simp [hbk, hlt, hbklt, q, r, pow_succ]

/-- Pull the matching-plus-root-cross event back to Gaussian tuples. -/
def canonicalGaussianMatchingRootCrossEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b k : ℕ) (t s : ℝ) : Set (NestedTuple E (2 * k)) :=
  orderedForestScores (E := E) (canonicalMatchingRootCrossForest a b) (2 * k) ⁻¹'
    canonicalMatchingRootCrossScoreEvent t s b k

/-- The forest event is exactly the direct matching event intersected with
the root-to-root cross exceedance. -/
theorem preimage_canonicalFamilyMatching_inter_rootCross_nestedTupleToFin
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b k : ℕ) (hab : a < b) (hbk : b < k) (t s : ℝ) :
    nestedTupleToFin (α := E) (2 * k) ⁻¹'
        (canonicalFamilyMatchingEvent (E := E) k t ∩
          canonicalFamilyCrossEvent
            (canonicalEvenIndex k ⟨a, hab.trans hbk⟩)
            (canonicalEvenIndex k ⟨b, hbk⟩) s) =
      canonicalGaussianMatchingRootCrossEvent (E := E) a b k t s := by
  induction k generalizing a b with
  | zero => omega
  | succ k ih =>
      ext z
      rcases z with ⟨⟨past, u⟩, v⟩
      by_cases hb : b = k
      · subst b
        have ha : a < k := hab
        unfold canonicalGaussianMatchingRootCrossEvent
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
        rw [orderedForestScores_canonicalMatchingRootCross_pair_succ_special
          ha past u v]
        rw [orderedForestScores_canonicalMatchingRootCross_before
            (E := E) a k k le_rfl past]
        simp only [canonicalMatchingRootCrossScoreEvent, if_pos rfl]
        change
          (nestedTupleToFin (2 * (k + 1)) ((past, u), v) ∈
                canonicalFamilyMatchingEvent (E := E) (k + 1) t ∧
              nestedTupleToFin (2 * (k + 1)) ((past, u), v) ∈
                canonicalFamilyCrossEvent
                  (canonicalEvenIndex (k + 1) ⟨a, hab.trans hbk⟩)
                  (canonicalEvenIndex (k + 1) ⟨k, hbk⟩) s) ↔
            ((orderedForestScores (E := E) canonicalMatchingForest (2 * k) past ∈
                  canonicalMatchingRootCrossScoreEvent t s k k ∧
                squaredNormalizedInner
                    (nestedTupleToFin (2 * k) past
                      (canonicalEvenIndex k ⟨a, ha⟩)) u ∈ Set.Ioi s) ∧
              squaredNormalizedInner u v ∈ Set.Ioi t)
        rw [canonicalMatchingRootCrossScoreEvent_eq_before t s k k le_rfl]
        simp only [Set.mem_Ioi]
        have hmatch := Set.ext_iff.mp
          (preimage_canonicalFamilyMatchingEvent_nestedTupleToFin
            (E := E) k t) past
        simp only [Set.mem_preimage] at hmatch
        unfold canonicalGaussianMatchingEvent at hmatch
        simp only [Set.mem_preimage] at hmatch
        rw [← hmatch,
          nestedTupleToFin_mem_canonicalFamilyMatchingEvent_pair_iff]
        have hia : canonicalEvenIndex (k + 1) ⟨a, hab.trans hbk⟩ =
            canonicalEvenIndex (k + 1) (⟨a, ha⟩ : Fin k).castSucc := by
          apply Fin.ext
          rfl
        have hib : canonicalEvenIndex (k + 1) ⟨k, hbk⟩ =
            canonicalEvenIndex (k + 1) (Fin.last k) := by
          apply Fin.ext
          rfl
        rw [hia, hib,
          nestedTupleToFin_mem_canonicalFamilyCrossEvent_pair_last_iff]
        aesop
      · have hbk' : b < k := by omega
        unfold canonicalGaussianMatchingRootCrossEvent
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
        rw [orderedForestScores_canonicalMatchingRootCross_pair_succ_other
          hb past u v]
        simp only [canonicalMatchingRootCrossScoreEvent, if_neg hb]
        change
          (nestedTupleToFin (2 * (k + 1)) ((past, u), v) ∈
                canonicalFamilyMatchingEvent (E := E) (k + 1) t ∧
              nestedTupleToFin (2 * (k + 1)) ((past, u), v) ∈
                canonicalFamilyCrossEvent
                  (canonicalEvenIndex (k + 1) ⟨a, hab.trans hbk⟩)
                  (canonicalEvenIndex (k + 1) ⟨b, hbk⟩) s) ↔
            ((orderedForestScores (E := E)
                  (canonicalMatchingRootCrossForest a b) (2 * k) past ∈
                canonicalMatchingRootCrossScoreEvent t s b k ∧
              (0 : ℝ) ∈ Set.univ) ∧
              squaredNormalizedInner u v ∈ Set.Ioi t)
        simp only [Set.mem_univ, and_true, Set.mem_Ioi]
        have hroot := Set.ext_iff.mp (ih a b hab hbk') past
        simp only [Set.mem_preimage] at hroot
        unfold canonicalGaussianMatchingRootCrossEvent at hroot
        simp only [Set.mem_preimage] at hroot
        rw [← hroot,
          nestedTupleToFin_mem_canonicalFamilyMatchingEvent_pair_iff]
        have ha' : a < k := hab.trans hbk'
        have hia : canonicalEvenIndex (k + 1) ⟨a, hab.trans hbk⟩ =
            canonicalEvenIndex (k + 1) (⟨a, ha'⟩ : Fin k).castSucc := by
          apply Fin.ext
          rfl
        have hib : canonicalEvenIndex (k + 1) ⟨b, hbk⟩ =
            canonicalEvenIndex (k + 1) (⟨b, hbk'⟩ : Fin k).castSucc := by
          apply Fin.ext
          rfl
        rw [hia, hib,
          nestedTupleToFin_mem_canonicalFamilyCrossEvent_pair_castSucc_iff]
        aesop

/-- Exact Gaussian probability of a canonical matching together with one
root-to-root cross exceedance. -/
theorem canonicalGaussianMatchingRootCrossEvent_probability
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (a b k : ℕ) (hab : a < b) (hbk : b < k) (t s : ℝ) :
    (nestedProductMeasure (stdGaussian E) (2 * k)).real
        (canonicalGaussianMatchingRootCrossEvent (E := E) a b k t s) =
      ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^ k *
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi s) := by
  have hmeas : Measurable
      (orderedForestScores (E := E) (canonicalMatchingRootCrossForest a b)
        (2 * k)) :=
    measurable_sequentialStatistic
      (orderedForestScore (E := E) (canonicalMatchingRootCrossForest a b))
      (measurable_uncurry_orderedForestScore
        (canonicalMatchingRootCrossForest a b)) (2 * k)
  have hset := measurableSet_canonicalMatchingRootCrossScoreEvent t s b k
  unfold canonicalGaussianMatchingRootCrossEvent
  rw [measureReal_def, ← Measure.map_apply hmeas hset,
    map_orderedForestScores_eq_nestedProduct
      (canonicalMatchingRootCrossForest a b) m hdim hm (2 * k)]
  change
    (nestedProductMeasureFamily
      (orderedForestFactorMeasure (canonicalMatchingRootCrossForest a b) m)
      (2 * k)).real (canonicalMatchingRootCrossScoreEvent t s b k) = _
  rw [canonicalMatchingRootCrossScoreEvent_probability m a b k hab t s,
    if_pos hbk]

/-- Exact ordinary-product-space probability of the matching together with
one root-to-root cross exceedance. -/
theorem canonicalFamilyMatching_inter_rootCross_probability
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (a b k : ℕ) (hab : a < b) (hbk : b < k) (t s : ℝ) :
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (canonicalFamilyMatchingEvent (E := E) k t ∩
          canonicalFamilyCrossEvent
            (canonicalEvenIndex k ⟨a, hab.trans hbk⟩)
            (canonicalEvenIndex k ⟨b, hbk⟩) s) =
      ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^ k *
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi s) := by
  have hread := measurePreserving_nestedTupleToFin (stdGaussian E) (2 * k)
  have hset : MeasurableSet
      (canonicalFamilyMatchingEvent (E := E) k t ∩
        canonicalFamilyCrossEvent
          (canonicalEvenIndex k ⟨a, hab.trans hbk⟩)
          (canonicalEvenIndex k ⟨b, hbk⟩) s) :=
    (measurableSet_canonicalFamilyMatchingEvent (E := E) k t).inter
      (measurableSet_canonicalFamilyCrossEvent
        (E := E) (canonicalEvenIndex k ⟨a, hab.trans hbk⟩)
          (canonicalEvenIndex k ⟨b, hbk⟩) s)
  rw [← hread.map_eq, measureReal_def,
    Measure.map_apply (measurable_nestedTupleToFin (2 * k)) hset,
    ← measureReal_def,
    preimage_canonicalFamilyMatching_inter_rootCross_nestedTupleToFin
      a b k hab hbk t s]
  exact canonicalGaussianMatchingRootCrossEvent_probability
    m hdim hm a b k hab hbk t s

/-- Invariance of real-valued Gaussian product probabilities under one
optional within-pair swap. -/
theorem gaussianPi_real_preimage_optionalPairSwap
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} (j : Fin k) (e : Bool) (A : Set (Fin (2 * k) → E))
    (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (permuteColumns (E := E) (canonicalOptionalPairSwap k j e) ⁻¹' A) =
      (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real A := by
  have hmp := measurePreserving_permuteGaussianColumns
    (E := E) (canonicalOptionalPairSwap k j e)
  rw [measureReal_def,
    ← Measure.map_apply hmp.measurable hA, hmp.map_eq, ← measureReal_def]

/-- Exact probability for every one of the four endpoint choices between
two distinct canonical pairs.  This closes the within-pair relabeling bridge
needed by the cross-edge union bound. -/
theorem canonicalFamilyMatching_inter_endpointCross_probability
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    {k : ℕ} (a b : Fin k) (hab : a.1 < b.1)
    (ea eb : Bool) (t s : ℝ) :
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (canonicalFamilyMatchingEvent (E := E) k t ∩
          canonicalFamilyCrossEvent
            (canonicalEndpointIndex k a ea)
            (canonicalEndpointIndex k b eb) s) =
      ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^ k *
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi s) := by
  have habne : a ≠ b := by
    intro h
    subst b
    omega
  let M : Set (Fin (2 * k) → E) :=
    canonicalFamilyMatchingEvent (E := E) k t
  let Croot : Set (Fin (2 * k) → E) :=
    canonicalFamilyCrossEvent (canonicalEvenIndex k a)
      (canonicalEvenIndex k b) s
  let Cfirst : Set (Fin (2 * k) → E) :=
    canonicalFamilyCrossEvent (canonicalEndpointIndex k a ea)
      (canonicalEvenIndex k b) s
  let Cboth : Set (Fin (2 * k) → E) :=
    canonicalFamilyCrossEvent (canonicalEndpointIndex k a ea)
      (canonicalEndpointIndex k b eb) s
  have hM : MeasurableSet M :=
    measurableSet_canonicalFamilyMatchingEvent (E := E) k t
  have hroot : MeasurableSet (M ∩ Croot) := hM.inter
    (measurableSet_canonicalFamilyCrossEvent
      (E := E) (canonicalEvenIndex k a) (canonicalEvenIndex k b) s)
  have hfirst : MeasurableSet (M ∩ Cfirst) := hM.inter
    (measurableSet_canonicalFamilyCrossEvent
      (E := E) (canonicalEndpointIndex k a ea)
        (canonicalEvenIndex k b) s)
  have hswapFirst := gaussianPi_real_preimage_optionalPairSwap
    (E := E) a ea (M ∩ Croot) hroot
  have hswapSecond := gaussianPi_real_preimage_optionalPairSwap
    (E := E) b eb (M ∩ Cfirst) hfirst
  rw [preimage_matching_inter_rootCross_optionalPairSwap_first
      (E := E) a b habne ea t s] at hswapFirst
  rw [preimage_matching_inter_endpointRoot_optionalPairSwap_second
      (E := E) a b habne ea eb t s] at hswapSecond
  change
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real (M ∩ Cboth) = _
  calc
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real (M ∩ Cboth) =
        (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real (M ∩ Cfirst) :=
      hswapSecond
    _ = (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real (M ∩ Croot) :=
      hswapFirst
    _ = ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)) ^ k *
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi s) := by
      simpa [M, Croot] using
        (canonicalFamilyMatching_inter_rootCross_probability
          (E := E) m hdim hm a.1 b.1 k hab b.isLt t s)

/-! ### All cross edges of the canonical prefix -/

/-- A cross edge is specified by two distinct canonical pairs, in increasing
order, and one of the two endpoints in each pair. -/
structure CanonicalCrossIndex (k : ℕ) where
  first : Fin k
  second : Fin k
  first_lt_second : first.1 < second.1
  firstEndpoint : Bool
  secondEndpoint : Bool
deriving Fintype, DecidableEq

/-- The squared-correlation exceedance event associated with one canonical
cross-edge index. -/
def canonicalFamilyCrossFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (c : CanonicalCrossIndex k) (s : ℝ) :
    Set (Fin (2 * k) → E) :=
  canonicalFamilyCrossEvent
    (canonicalEndpointIndex k c.first c.firstEndpoint)
    (canonicalEndpointIndex k c.second c.secondEndpoint) s

theorem measurableSet_canonicalFamilyCrossFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} (c : CanonicalCrossIndex k) (s : ℝ) :
    MeasurableSet (canonicalFamilyCrossFailure (E := E) c s) :=
  measurableSet_canonicalFamilyCrossEvent _ _ _

/-- Finite, fully model-specific relative union bound for every cross edge in
the fixed canonical prefix. -/
theorem canonicalFamilyCrossFailure_relative_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 4 ≤ m)
    (k : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (s : ℝ) :
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (canonicalFamilyMatchingEvent (E := E) k t ∩
          ⋃ c : CanonicalCrossIndex k,
            canonicalFamilyCrossFailure (E := E) c s) /
      (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E).real
        (canonicalFamilyMatchingEvent (E := E) k t) ≤
      (Fintype.card (CanonicalCrossIndex k) : ℝ) *
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi s) := by
  let q : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)
  let r : ℝ :=
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi s)
  have hm2 : 2 ≤ m := by omega
  have hb : 1 < (((m - 1 : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hq : 0 < q := betaMeasure_half_Ioi_real_pos hb ht ht1
  have hM := canonicalFamilyMatchingEvent_probability
    (E := E) m hdim hm2 k t
  apply relative_inter_iUnion_le_card_mul
    (Measure.pi fun _ : Fin (2 * k) ↦ stdGaussian E)
    (canonicalFamilyMatchingEvent (E := E) k t)
    (fun c : CanonicalCrossIndex k ↦
      canonicalFamilyCrossFailure (E := E) c s)
    (pow_pos hq k) measureReal_nonneg
  · simpa [q] using hM
  · intro c
    rcases c with ⟨a, b, hab, ea, eb⟩
    have hexact := canonicalFamilyMatching_inter_endpointCross_probability
      (E := E) m hdim hm2 a b hab ea eb t s
    simpa [canonicalFamilyCrossFailure, q, r] using hexact.le

/-- Relative all-cross-edge failure probability in the ordinary Euclidean
residual product model. -/
def canonicalResidualCrossFailureRelative
    (k m p : ℕ) (x : ℝ) : ℝ :=
  let t := classicalCoherenceThreshold m p x / (m : ℝ)
  (Measure.pi fun _ : Fin (2 * k) ↦
      stdGaussian (EuclideanSpace ℝ (Fin m))).real
      (canonicalFamilyMatchingEvent k t ∩
        ⋃ c : CanonicalCrossIndex k,
          canonicalFamilyCrossFailure c t) /
    (Measure.pi fun _ : Fin (2 * k) ↦
      stdGaussian (EuclideanSpace ℝ (Fin m))).real
      (canonicalFamilyMatchingEvent k t)

/-- Along every all-gap sequence, conditioned on the canonical matching,
the relative probability that any cross edge in the fixed prefix exceeds
the base threshold tends to zero. -/
theorem tendsto_canonicalResidualCrossFailureRelative_zero
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalResidualCrossFailureRelative k (mseq p) p x)
      atTop (nhds 0) := by
  have htail := tendsto_betaCorrelationTailProbability_zero_of_markov hadm x
  have hupper : Tendsto (fun p : ℕ ↦
      (Fintype.card (CanonicalCrossIndex k) : ℝ) *
        betaCorrelationTailProbability (mseq p) p x)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul htail)
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ by
      unfold canonicalResidualCrossFailureRelative
      dsimp only
      exact div_nonneg measureReal_nonneg measureReal_nonneg
  · filter_upwards [hadm, eventually_ge_atTop 4,
      ha.eventually (eventually_gt_atTop 0),
      ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with p hp hp4 hapos ht1
    have hm4 : 4 ≤ mseq p := hp4.trans hp.2
    have hm0 : (0 : ℝ) < (mseq p : ℝ) := by positivity
    have hthreshold : 0 < classicalCoherenceThreshold (mseq p) p x := by
      simpa [classicalCoherenceThreshold] using hapos
    have hfinite := canonicalFamilyCrossFailure_relative_le
      (E := EuclideanSpace ℝ (Fin (mseq p)))
      (mseq p) (by simp) hm4 k
      (div_pos hthreshold hm0) ht1
      (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ))
    simpa [canonicalResidualCrossFailureRelative,
      betaCorrelationTailProbability] using hfinite
  · simpa [betaCorrelationTailProbability, measureReal_def] using hupper

/-- Union of the two structural prefix failures: a selected edge overshoots
`2*t`, or a cross edge overshoots `t`. -/
def canonicalFamilyPrefixStructuralFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (t : ℝ) : Set (Fin (2 * k) → E) :=
  canonicalFamilySelectedOvershootFailure k t 2 ∪
    (canonicalFamilyMatchingEvent k t ∩
      ⋃ c : CanonicalCrossIndex k, canonicalFamilyCrossFailure c t)

theorem measurableSet_canonicalFamilyPrefixStructuralFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) (t : ℝ) :
    MeasurableSet (canonicalFamilyPrefixStructuralFailure (E := E) k t) :=
  (measurableSet_canonicalFamilySelectedOvershootFailure (E := E) k t 2).union
    ((measurableSet_canonicalFamilyMatchingEvent (E := E) k t).inter
      (MeasurableSet.iUnion fun c ↦
        measurableSet_canonicalFamilyCrossFailure (E := E) c t))

/-- The structural-failure relative mass is bounded by the sum of the two
component relative masses. -/
theorem canonicalFamilyPrefixStructuralFailure_relative_le_sum
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (k : ℕ) (t : ℝ) (mu : Measure (Fin (2 * k) → E)) :
    mu.real (canonicalFamilyPrefixStructuralFailure k t) /
        mu.real (canonicalFamilyMatchingEvent k t) ≤
      mu.real (canonicalFamilySelectedOvershootFailure k t 2) /
          mu.real (canonicalFamilyMatchingEvent k t) +
        mu.real (canonicalFamilyMatchingEvent k t ∩
            ⋃ c : CanonicalCrossIndex k, canonicalFamilyCrossFailure c t) /
          mu.real (canonicalFamilyMatchingEvent k t) := by
  calc
    mu.real (canonicalFamilyPrefixStructuralFailure k t) /
          mu.real (canonicalFamilyMatchingEvent k t) ≤
        (mu.real (canonicalFamilySelectedOvershootFailure k t 2) +
          mu.real (canonicalFamilyMatchingEvent k t ∩
            ⋃ c : CanonicalCrossIndex k, canonicalFamilyCrossFailure c t)) /
          mu.real (canonicalFamilyMatchingEvent k t) := by
      apply div_le_div_of_nonneg_right _ measureReal_nonneg
      simpa [canonicalFamilyPrefixStructuralFailure] using
        (measureReal_union_le
          (μ := mu)
          (canonicalFamilySelectedOvershootFailure k t 2)
          (canonicalFamilyMatchingEvent k t ∩
            ⋃ c : CanonicalCrossIndex k, canonicalFamilyCrossFailure c t))
    _ = mu.real (canonicalFamilySelectedOvershootFailure k t 2) /
          mu.real (canonicalFamilyMatchingEvent k t) +
        mu.real (canonicalFamilyMatchingEvent k t ∩
            ⋃ c : CanonicalCrossIndex k, canonicalFamilyCrossFailure c t) /
          mu.real (canonicalFamilyMatchingEvent k t) := by ring

/-- Relative structural-failure mass in the Euclidean residual product
model. -/
def canonicalResidualPrefixStructuralFailureRelative
    (k m p : ℕ) (x : ℝ) : ℝ :=
  let t := classicalCoherenceThreshold m p x / (m : ℝ)
  (Measure.pi fun _ : Fin (2 * k) ↦
      stdGaussian (EuclideanSpace ℝ (Fin m))).real
      (canonicalFamilyPrefixStructuralFailure k t) /
    (Measure.pi fun _ : Fin (2 * k) ↦
      stdGaussian (EuclideanSpace ℝ (Fin m))).real
      (canonicalFamilyMatchingEvent k t)

/-- For fixed positive matching size, the full structural-failure relative
mass vanishes along every all-gap sequence. -/
theorem tendsto_canonicalResidualPrefixStructuralFailureRelative_zero
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalResidualPrefixStructuralFailureRelative k (mseq p) p x)
      atTop (nhds 0) := by
  have hselected :=
    tendsto_canonicalResidualFamilySelectedOvershootRelative_zero
      k hk hadm (c := (2 : ℝ)) (by norm_num) x
  have hcross := tendsto_canonicalResidualCrossFailureRelative_zero k hadm x
  have hupper := hselected.add hcross
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ by
      unfold canonicalResidualPrefixStructuralFailureRelative
      dsimp only
      exact div_nonneg measureReal_nonneg measureReal_nonneg
  · exact Eventually.of_forall fun p ↦ by
      simpa [canonicalResidualPrefixStructuralFailureRelative,
        canonicalResidualFamilySelectedOvershootRelative,
        canonicalResidualCrossFailureRelative] using
          canonicalFamilyPrefixStructuralFailure_relative_le_sum
            k (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ))
            (Measure.pi fun _ : Fin (2 * k) ↦
              stdGaussian (EuclideanSpace ℝ (Fin (mseq p))))
  · simpa [canonicalResidualFamilySelectedOvershootRelative,
      canonicalResidualCrossFailureRelative] using hupper

/-! ## Deterministic conversion to a prefix log-determinant bound -/

/-- Every vertex of a `2*k` prefix is one of the two endpoints of a unique
canonical pair.  Only existence is needed below. -/
theorem exists_canonicalEndpointIndex_eq
    (k : ℕ) (i : Fin (2 * k)) :
    ∃ (a : Fin k) (e : Bool), i = canonicalEndpointIndex k a e := by
  have ha : i.1 / 2 < k := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 2)]
    simpa [mul_comm] using i.isLt
  let a : Fin k := ⟨i.1 / 2, ha⟩
  rcases Nat.mod_two_eq_zero_or_one i.1 with hmod | hmod
  · refine ⟨a, false, ?_⟩
    apply Fin.ext
    simp only [canonicalEndpointIndex_false, canonicalEvenIndex_val]
    have hdiv := Nat.mod_add_div i.1 2
    dsimp [a]
    omega
  · refine ⟨a, true, ?_⟩
    apply Fin.ext
    simp only [canonicalEndpointIndex_true, canonicalOddIndex_val]
    have hdiv := Nat.mod_add_div i.1 2
    dsimp [a]
    omega

/-- Outside the selected-overshoot and all-cross failure events, every
off-diagonal squared correlation is at most `2*t`. -/
theorem squaredNormalizedInner_le_two_threshold_of_no_prefix_failures
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (v : Fin (2 * k) → E) {t : ℝ} (ht : 0 ≤ t)
    (hM : v ∈ canonicalFamilyMatchingEvent k t)
    (hselected : v ∉ canonicalFamilySelectedOvershootFailure k t 2)
    (hcross : v ∉
      (canonicalFamilyMatchingEvent k t ∩
        ⋃ c : CanonicalCrossIndex k, canonicalFamilyCrossFailure c t))
    (i j : Fin (2 * k)) (hij : i ≠ j) :
    squaredNormalizedInner (v i) (v j) ≤ 2 * t := by
  have hnoSelected : v ∉ canonicalFamilySelectedEdgeFailure k (2 * t) := by
    intro hbad
    exact hselected ⟨hM, by simpa using hbad⟩
  have hnoCross : v ∉ ⋃ c : CanonicalCrossIndex k,
      canonicalFamilyCrossFailure c t := by
    intro hbad
    exact hcross ⟨hM, hbad⟩
  rcases exists_canonicalEndpointIndex_eq k i with ⟨a, ea, rfl⟩
  rcases exists_canonicalEndpointIndex_eq k j with ⟨b, eb, rfl⟩
  by_cases hab : a = b
  · subst b
    cases ea <;> cases eb
    · exact (hij rfl).elim
    · apply le_of_not_gt
      intro hbad
      apply hnoSelected
      unfold canonicalFamilySelectedEdgeFailure
      simp only [Set.mem_iUnion]
      refine ⟨a, ?_⟩
      exact hbad
    · apply le_of_not_gt
      intro hbad
      apply hnoSelected
      unfold canonicalFamilySelectedEdgeFailure canonicalFamilyCrossEvent
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      refine ⟨a, ?_⟩
      simpa [squaredNormalizedInner_comm] using hbad
    · exact (hij rfl).elim
  · have hpairs : a.1 < b.1 ∨ b.1 < a.1 := by
      omega
    have hle : squaredNormalizedInner
        (v (canonicalEndpointIndex k a ea))
        (v (canonicalEndpointIndex k b eb)) ≤ t := by
      apply le_of_not_gt
      intro hbad
      apply hnoCross
      simp only [Set.mem_iUnion]
      rcases hpairs with hablt | hbalt
      · refine ⟨⟨a, b, hablt, ea, eb⟩, ?_⟩
        exact hbad
      · refine ⟨⟨b, a, hbalt, eb, ea⟩, ?_⟩
        unfold canonicalFamilyCrossFailure canonicalFamilyCrossEvent
        simpa [squaredNormalizedInner_comm] using hbad
    linarith

/-- Squaring an off-diagonal normalized Gram entry gives the squared
normalized inner product used throughout the coherence development. -/
theorem normalizedGram_apply_sq_eq_squaredNormalizedInner
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (i j : ι) (hi : v i ≠ 0) (hj : v j ≠ 0) :
    (normalizedGram v i j) ^ 2 = squaredNormalizedInner (v i) (v j) := by
  have hni : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
  have hnj : ‖v j‖ ≠ 0 := norm_ne_zero_iff.mpr hj
  unfold normalizedGram normalizeVector squaredNormalizedInner
  simp only [Matrix.gram, real_inner_smul_left, real_inner_smul_right]
  change (‖v j‖⁻¹ * (‖v i‖⁻¹ * inner ℝ (v i) (v j))) ^ 2 =
    (inner ℝ (v i) (v j)) ^ 2 / (‖v i‖ ^ 2 * ‖v j‖ ^ 2)
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [hni, hnj]

/-- If every squared off-diagonal correlation of a linearly independent
fixed prefix is at most `D`, its log determinant is bounded by a fixed
multiple of `D`. -/
theorem abs_log_det_normalizedGram_le_of_squaredInner_le
    {q : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Fin q → E) (hv : LinearIndependent ℝ v)
    {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hoff : ∀ i j, i ≠ j → squaredNormalizedInner (v i) (v j) ≤ D)
    (hsmall : (Nat.factorial q : ℝ) * D ≤ (1 / 2 : ℝ)) :
    |Real.log (normalizedGram v).det| ≤
      2 * (Nat.factorial q : ℝ) * D := by
  let δ : ℝ := √D
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg D
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa using (Real.sqrt_le_sqrt hD1)
  have hdiag : ∀ i, normalizedGram v i i = 1 := fun i ↦
    normalizedGram_apply_self v i (hv.ne_zero i)
  have hoff' : ∀ i j, i ≠ j → |normalizedGram v i j| ≤ δ := by
    intro i j hij
    apply Real.abs_le_sqrt
    rw [normalizedGram_apply_sq_eq_squaredNormalizedInner v i j
      (hv.ne_zero i) (hv.ne_zero j)]
    exact hoff i j hij
  have hdet : 0 < (normalizedGram v).det :=
    det_normalizedGram_pos_of_linearIndependent v hv
  have hδsq : δ ^ 2 = D := Real.sq_sqrt hD0
  have hlog := abs_log_det_le_two_factorial_mul_sq
    (normalizedGram v) δ hdiag hoff' hδ0 hδ1 hdet
    (by simpa [hδsq] using hsmall)
  simpa [hδsq] using hlog

/-- On the event that selected squared correlations are at most `2u` and
all remaining squared correlations are at most `u`, the whole fixed prefix
obeys the simpler uniform envelope `2u`, hence its log determinant is
`O_k(u)`. -/
theorem abs_log_det_normalizedGram_le_of_selected_cross_bounds
    {q : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Fin q → E) (hv : LinearIndependent ℝ v)
    (selected : Fin q → Fin q → Prop)
    {u : ℝ} (hu0 : 0 ≤ u) (hu2 : 2 * u ≤ 1)
    (hselected : ∀ i j, i ≠ j → selected i j →
      squaredNormalizedInner (v i) (v j) ≤ 2 * u)
    (hcross : ∀ i j, i ≠ j → ¬selected i j →
      squaredNormalizedInner (v i) (v j) ≤ u)
    (hsmall : (Nat.factorial q : ℝ) * (2 * u) ≤ (1 / 2 : ℝ)) :
    |Real.log (normalizedGram v).det| ≤
      4 * (Nat.factorial q : ℝ) * u := by
  have hall : ∀ i j, i ≠ j →
      squaredNormalizedInner (v i) (v j) ≤ 2 * u := by
    intro i j hij
    by_cases hs : selected i j
    · exact hselected i j hij hs
    · exact (hcross i j hij hs).trans (by linarith)
  have h := abs_log_det_normalizedGram_le_of_squaredInner_le
    v hv (D := 2 * u) (by linarith) hu2 hall hsmall
  convert h using 1 <;> ring

/-- Deterministic log-determinant radius outside the full structural failure
event. -/
theorem abs_log_det_normalizedGram_le_of_not_prefixStructuralFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (v : Fin (2 * k) → E) (hv : LinearIndependent ℝ v)
    {t : ℝ} (ht : 0 ≤ t) (ht2 : 2 * t ≤ 1)
    (hsmall : (Nat.factorial (2 * k) : ℝ) * (2 * t) ≤ (1 / 2 : ℝ))
    (hM : v ∈ canonicalFamilyMatchingEvent k t)
    (hgood : v ∉ canonicalFamilyPrefixStructuralFailure k t) :
    |Real.log (normalizedGram v).det| ≤
      4 * (Nat.factorial (2 * k) : ℝ) * t := by
  have hselected : v ∉ canonicalFamilySelectedOvershootFailure k t 2 := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hcross : v ∉
      (canonicalFamilyMatchingEvent k t ∩
        ⋃ c : CanonicalCrossIndex k, canonicalFamilyCrossFailure c t) := by
    intro hbad
    exact hgood (Or.inr hbad)
  have hall : ∀ i j, i ≠ j →
      squaredNormalizedInner (v i) (v j) ≤ 2 * t :=
    squaredNormalizedInner_le_two_threshold_of_no_prefix_failures
      v ht hM hselected hcross
  have h := abs_log_det_normalizedGram_le_of_squaredInner_le
    v hv (D := 2 * t) (by linarith) ht2 hall hsmall
  convert h using 1 <;> ring

/-- Explicit globally standardized radius for the uncentered prefix log
determinant. -/
def canonicalPrefixStandardizedLogdetRadius
    (k m p : ℕ) (x : ℝ) : ℝ :=
  (4 * (Nat.factorial (2 * k) : ℝ) *
      (classicalCoherenceThreshold m p x / (m : ℝ))) /
    Real.sqrt (nullVSeries m p)

/-- Pointwise standardized form of the preceding deterministic bound. -/
theorem abs_standardized_log_det_normalizedGram_le_of_not_prefixStructuralFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k m p : ℕ}
    (v : Fin (2 * k) → E) (hv : LinearIndependent ℝ v)
    {t : ℝ} (ht : 0 ≤ t) (ht2 : 2 * t ≤ 1)
    (hsmall : (Nat.factorial (2 * k) : ℝ) * (2 * t) ≤ (1 / 2 : ℝ))
    (hM : v ∈ canonicalFamilyMatchingEvent k t)
    (hgood : v ∉ canonicalFamilyPrefixStructuralFailure k t) :
    |Real.log (normalizedGram v).det / Real.sqrt (nullVSeries m p)| ≤
      (4 * (Nat.factorial (2 * k) : ℝ) * t) /
        Real.sqrt (nullVSeries m p) := by
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right
    (abs_log_det_normalizedGram_le_of_not_prefixStructuralFailure
      v hv ht ht2 hsmall hM hgood)
    (Real.sqrt_nonneg _)

/-- Failure of the explicit standardized uncentered-prefix radius. -/
def canonicalFamilyStandardizedPrefixLogdetFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k m p : ℕ) (x : ℝ) : Set (Fin (2 * k) → E) :=
  {v | canonicalPrefixStandardizedLogdetRadius k m p x <
    |Real.log (normalizedGram v).det / Real.sqrt (nullVSeries m p)|}

theorem measurableSet_canonicalFamilyStandardizedPrefixLogdetFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (k m p : ℕ) (x : ℝ) :
    MeasurableSet
      (canonicalFamilyStandardizedPrefixLogdetFailure (E := E) k m p x) := by
  have hlog : Measurable (fun v : Fin (2 * k) → E ↦
      Real.log (normalizedGram v).det) := by
    exact (measurable_det_normalizedGram (E := E) (2 * k)).log
  exact measurableSet_lt measurable_const
    ((hlog.div_const (Real.sqrt (nullVSeries m p))).abs)

/-- The explicit standardized prefix radius tends to zero in every all-gap
regime. -/
theorem tendsto_canonicalPrefixStandardizedLogdetRadius_zero
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalPrefixStandardizedLogdetRadius k (mseq p) p x)
      atTop (nhds 0) := by
  have hscale := tendsto_classicalThreshold_over_globalNullScale_zero hadm x
  let C : ℝ := 4 * (Nat.factorial (2 * k) : ℝ)
  have hC : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C) :=
    tendsto_const_nhds
  have hmul := hC.mul hscale
  convert hmul using 1
  · funext p
    simp only [canonicalPrefixStandardizedLogdetRadius]
    dsimp only [C]
    ring
  · simp

/-- Relative failure mass for the uncentered standardized prefix log
determinant. -/
def canonicalResidualPrefixUncenteredStandardizedFailureRelative
    (k m p : ℕ) (x : ℝ) : ℝ :=
  let t := classicalCoherenceThreshold m p x / (m : ℝ)
  let mu := Measure.pi fun _ : Fin (2 * k) ↦
    stdGaussian (EuclideanSpace ℝ (Fin m))
  mu.real (canonicalFamilyMatchingEvent k t ∩
      canonicalFamilyStandardizedPrefixLogdetFailure k m p x) /
    mu.real (canonicalFamilyMatchingEvent k t)

/-- **Event-weighted prefix concentration.**  For fixed positive matching
size, the uncentered prefix log determinant divided by the global null
standard deviation lies in the explicit shrinking interval with conditional
relative probability tending to one. -/
theorem tendsto_canonicalResidualPrefixUncenteredStandardizedFailureRelative_zero
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalResidualPrefixUncenteredStandardizedFailureRelative
        k (mseq p) p x) atTop (nhds 0) := by
  have hstruct :=
    tendsto_canonicalResidualPrefixStructuralFailureRelative_zero
      k hk hadm x
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  let F : ℝ := (Nat.factorial (2 * k) : ℝ)
  have hFpos : 0 < F := by
    dsimp [F]
    positivity
  have hdelta : 0 < 1 / (4 * F) := by positivity
  have htsmall := ht.eventually (eventually_lt_nhds hdelta)
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ by
      unfold canonicalResidualPrefixUncenteredStandardizedFailureRelative
      dsimp only
      exact div_nonneg measureReal_nonneg measureReal_nonneg
  · filter_upwards [hadm, eventually_ge_atTop (2 * k),
      ha.eventually (eventually_ge_atTop 0), htsmall]
      with p hp hpk hapos htupper
    let tp : ℝ := classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)
    let mu : Measure (Fin (2 * k) → EuclideanSpace ℝ (Fin (mseq p))) :=
      Measure.pi fun _ : Fin (2 * k) ↦
        stdGaussian (EuclideanSpace ℝ (Fin (mseq p)))
    let M : Set (Fin (2 * k) → EuclideanSpace ℝ (Fin (mseq p))) :=
      canonicalFamilyMatchingEvent k tp
    let S : Set (Fin (2 * k) → EuclideanSpace ℝ (Fin (mseq p))) :=
      canonicalFamilyPrefixStructuralFailure k tp
    let B : Set (Fin (2 * k) → EuclideanSpace ℝ (Fin (mseq p))) :=
      M ∩ canonicalFamilyStandardizedPrefixLogdetFailure
        k (mseq p) p x
    let N : Set (Fin (2 * k) → EuclideanSpace ℝ (Fin (mseq p))) :=
      {v | ¬ LinearIndependent ℝ v}
    have hm0 : (0 : ℝ) < (mseq p : ℝ) := by
      have : 2 ≤ mseq p := hp.1.trans hp.2
      positivity
    have ht0 : 0 ≤ tp := by
      dsimp [tp]
      exact div_nonneg
        (by simpa [classicalCoherenceThreshold] using hapos) hm0.le
    have hscaled : tp * (4 * F) < 1 := by
      exact (lt_div_iff₀ (by positivity : 0 < 4 * F)).mp htupper
    have hFge : 1 ≤ F := by
      dsimp [F]
      exact_mod_cast (Nat.factorial_pos (2 * k))
    have ht2 : 2 * tp ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hFge) ht0]
    have hsmall : (Nat.factorial (2 * k) : ℝ) * (2 * tp) ≤
        (1 / 2 : ℝ) := by
      change F * (2 * tp) ≤ (1 / 2 : ℝ)
      nlinarith
    have hdim : 2 * k ≤ mseq p := hpk.trans hp.2
    have haeLI : ∀ᵐ v ∂mu, LinearIndependent ℝ v := by
      dsimp [mu]
      exact ae_linearIndependent_pi_stdGaussian
        (E := EuclideanSpace ℝ (Fin (mseq p))) (2 * k) (by simpa using hdim)
    have hnull : mu N = 0 := by
      rw [← ae_iff]
      simpa [N] using haeLI
    have hnullReal : mu.real N = 0 := by
      rw [measureReal_def, hnull]
      simp
    have hsub : B ⊆ S ∪ N := by
      intro v hv
      rcases hv with ⟨hM, hbad⟩
      by_cases hS : v ∈ S
      · exact Or.inl hS
      by_cases hLI : LinearIndependent ℝ v
      · exfalso
        have hbound :=
          abs_standardized_log_det_normalizedGram_le_of_not_prefixStructuralFailure
            (m := mseq p) (p := p) v hLI ht0 ht2 hsmall hM hS
        change canonicalPrefixStandardizedLogdetRadius k (mseq p) p x <
          |Real.log (normalizedGram v).det /
            Real.sqrt (nullVSeries (mseq p) p)| at hbad
        apply (not_lt_of_ge ?_) hbad
        simpa [canonicalPrefixStandardizedLogdetRadius, tp, F] using hbound
      · exact Or.inr hLI
    have hnumer : mu.real B ≤ mu.real S := by
      calc
        mu.real B ≤ mu.real (S ∪ N) := measureReal_mono hsub
        _ ≤ mu.real S + mu.real N := measureReal_union_le S N
        _ = mu.real S := by rw [hnullReal]; ring
    have hden : 0 ≤ mu.real M := measureReal_nonneg
    have hratio : mu.real B / mu.real M ≤ mu.real S / mu.real M :=
      div_le_div_of_nonneg_right hnumer hden
    simpa [canonicalResidualPrefixUncenteredStandardizedFailureRelative,
      canonicalResidualPrefixStructuralFailureRelative, tp, mu, M, S, B]
      using hratio
  · exact hstruct

/-! ## Transport to the centered nested-prefix model -/

/-- Squared correlations are unchanged by a linear isometry. -/
theorem squaredNormalizedInner_linearIsometry
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (u v : E) :
    squaredNormalizedInner (T u) (T v) = squaredNormalizedInner u v := by
  unfold squaredNormalizedInner
  rw [T.inner_map_map, T.norm_map, T.norm_map]

/-- The canonical matching event is invariant under a columnwise linear
isometry. -/
theorem preimage_canonicalFamilyMatchingEvent_mapColumnIsometry
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (k : ℕ) (t : ℝ) :
    mapColumnIsometry (p := 2 * k) T ⁻¹'
        canonicalFamilyMatchingEvent (E := F) k t =
      canonicalFamilyMatchingEvent (E := E) k t := by
  ext v
  simp only [Set.mem_preimage, canonicalFamilyMatchingEvent,
    Set.mem_setOf_eq]
  constructor <;> intro h j
  · simpa [mapColumnIsometry, squaredNormalizedInner_linearIsometry]
      using h j
  · simpa [mapColumnIsometry, squaredNormalizedInner_linearIsometry]
      using h j

/-- The uncentered standardized prefix-logdet failure event is invariant
under a columnwise linear isometry. -/
theorem preimage_canonicalFamilyStandardizedPrefixLogdetFailure_mapColumnIsometry
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (k m p : ℕ) (x : ℝ) :
    mapColumnIsometry (p := 2 * k) T ⁻¹'
        canonicalFamilyStandardizedPrefixLogdetFailure (E := F) k m p x =
      canonicalFamilyStandardizedPrefixLogdetFailure (E := E) k m p x := by
  ext v
  change canonicalPrefixStandardizedLogdetRadius k m p x <
      |Real.log (normalizedGram
        (mapColumnIsometry (p := 2 * k) T v)).det /
          Real.sqrt (nullVSeries m p)| ↔
    canonicalPrefixStandardizedLogdetRadius k m p x <
      |Real.log (normalizedGram v).det / Real.sqrt (nullVSeries m p)|
  rw [show normalizedGram (mapColumnIsometry (p := 2 * k) T v) =
      normalizedGram v by
    exact normalizedGram_linearIsometry T v]

/-- The corresponding bad event on the right-nested centered Gaussian
prefix. -/
def canonicalGaussianStandardizedPrefixLogdetFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k m p : ℕ) (x : ℝ) : Set (NestedTuple E (2 * k)) :=
  nestedTupleToFin (2 * k) ⁻¹'
    canonicalFamilyStandardizedPrefixLogdetFailure (E := E) k m p x

theorem measurableSet_canonicalGaussianStandardizedPrefixLogdetFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (k m p : ℕ) (x : ℝ) :
    MeasurableSet
      (canonicalGaussianStandardizedPrefixLogdetFailure (E := E)
        k m p x) :=
  (measurableSet_canonicalFamilyStandardizedPrefixLogdetFailure
    (E := E) k m p x).preimage (measurable_nestedTupleToFin (2 * k))

/-- Relative bad mass in the exact centered-subspace nested prefix used by
the conditional prefix--tail factorization. -/
def canonicalCenteredGaussianPrefixUncenteredFailureRelative
    (k m p : ℕ) (x : ℝ) : ℝ :=
  let t := classicalCoherenceThreshold m p x / (m : ℝ)
  let nu := nestedProductMeasure
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  nu.real (canonicalGaussianMatchingEvent k t ∩
      canonicalGaussianStandardizedPrefixLogdetFailure k m p x) /
    nu.real (canonicalGaussianMatchingEvent k t)

/-- Columnwise centered coordinates preserve the numerator of the
uncentered prefix-failure ratio exactly. -/
theorem centeredFamily_matching_inter_standardizedFailure_probability_eq_residual
    (k m p : ℕ) (t x : ℝ) :
    (Measure.pi fun _ : Fin (2 * k) ↦
      stdGaussian (centeredSubspace (m + 1))).real
        (canonicalFamilyMatchingEvent k t ∩
          canonicalFamilyStandardizedPrefixLogdetFailure k m p x) =
      (Measure.pi fun _ : Fin (2 * k) ↦
        stdGaussian (ObservationSpace m)).real
          (canonicalFamilyMatchingEvent k t ∩
            canonicalFamilyStandardizedPrefixLogdetFailure k m p x) := by
  let T := centeredCoordinateIsometry m
  have hT : Measurable
      (mapColumnIsometry (p := 2 * k) T.toLinearIsometry) :=
    measurable_mapColumnIsometry T.toLinearIsometry
  have hset : MeasurableSet
      (canonicalFamilyMatchingEvent
          (E := ObservationSpace m) k t ∩
        canonicalFamilyStandardizedPrefixLogdetFailure
          (E := ObservationSpace m) k m p x) :=
    (measurableSet_canonicalFamilyMatchingEvent
      (E := ObservationSpace m) k t).inter
        (measurableSet_canonicalFamilyStandardizedPrefixLogdetFailure
          (E := ObservationSpace m) k m p x)
  have hmap := map_mapColumnIsometry_pi_stdGaussian
    (p := 2 * k) T
  symm
  rw [← hmap, measureReal_def, Measure.map_apply hT hset,
    ← measureReal_def, preimage_inter,
    preimage_canonicalFamilyMatchingEvent_mapColumnIsometry,
    preimage_canonicalFamilyStandardizedPrefixLogdetFailure_mapColumnIsometry]

/-- Columnwise centered coordinates preserve the denominator matching mass
exactly. -/
theorem centeredFamily_matching_probability_eq_residual
    (k m : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin (2 * k) ↦
      stdGaussian (centeredSubspace (m + 1))).real
        (canonicalFamilyMatchingEvent k t) =
      (Measure.pi fun _ : Fin (2 * k) ↦
        stdGaussian (ObservationSpace m)).real
          (canonicalFamilyMatchingEvent k t) := by
  let T := centeredCoordinateIsometry m
  have hT : Measurable
      (mapColumnIsometry (p := 2 * k) T.toLinearIsometry) :=
    measurable_mapColumnIsometry T.toLinearIsometry
  have hset : MeasurableSet
      (canonicalFamilyMatchingEvent (E := ObservationSpace m) k t) :=
    measurableSet_canonicalFamilyMatchingEvent (E := ObservationSpace m) k t
  have hmap := map_mapColumnIsometry_pi_stdGaussian
    (p := 2 * k) T
  symm
  rw [← hmap, measureReal_def, Measure.map_apply hT hset,
    ← measureReal_def,
    preimage_canonicalFamilyMatchingEvent_mapColumnIsometry]

/-- Reading the nested prefix as a finite family preserves the joint
matching-and-failure numerator exactly. -/
theorem nested_matching_inter_standardizedFailure_probability_eq_centeredFamily
    (k m p : ℕ) (t x : ℝ) :
    (nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)).real
        (canonicalGaussianMatchingEvent k t ∩
          canonicalGaussianStandardizedPrefixLogdetFailure k m p x) =
      (Measure.pi fun _ : Fin (2 * k) ↦
        stdGaussian (centeredSubspace (m + 1))).real
          (canonicalFamilyMatchingEvent k t ∩
            canonicalFamilyStandardizedPrefixLogdetFailure k m p x) := by
  let read := nestedTupleToFin
    (n := 2 * k) (α := centeredSubspace (m + 1))
  have hread := measurePreserving_nestedTupleToFin
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  have hset : MeasurableSet
      (canonicalFamilyMatchingEvent
          (E := centeredSubspace (m + 1)) k t ∩
        canonicalFamilyStandardizedPrefixLogdetFailure
          (E := centeredSubspace (m + 1)) k m p x) :=
    (measurableSet_canonicalFamilyMatchingEvent
      (E := centeredSubspace (m + 1)) k t).inter
        (measurableSet_canonicalFamilyStandardizedPrefixLogdetFailure
          (E := centeredSubspace (m + 1)) k m p x)
  have hpre : read ⁻¹'
      (canonicalFamilyMatchingEvent
          (E := centeredSubspace (m + 1)) k t ∩
        canonicalFamilyStandardizedPrefixLogdetFailure
          (E := centeredSubspace (m + 1)) k m p x) =
      canonicalGaussianMatchingEvent k t ∩
        canonicalGaussianStandardizedPrefixLogdetFailure k m p x := by
    rw [preimage_inter,
      preimage_canonicalFamilyMatchingEvent_nestedTupleToFin]
    rfl
  symm
  rw [← hread.map_eq, measureReal_def,
    Measure.map_apply (measurable_nestedTupleToFin (2 * k)) hset,
    ← measureReal_def, hpre]

/-- Reading the nested prefix as a finite family preserves the canonical
matching denominator exactly. -/
theorem nested_matching_probability_eq_centeredFamily
    (k m : ℕ) (t : ℝ) :
    (nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)).real
        (canonicalGaussianMatchingEvent k t) =
      (Measure.pi fun _ : Fin (2 * k) ↦
        stdGaussian (centeredSubspace (m + 1))).real
          (canonicalFamilyMatchingEvent k t) := by
  have hread := measurePreserving_nestedTupleToFin
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  have hset : MeasurableSet
      (canonicalFamilyMatchingEvent
        (E := centeredSubspace (m + 1)) k t) :=
    measurableSet_canonicalFamilyMatchingEvent
      (E := centeredSubspace (m + 1)) k t
  symm
  rw [← hread.map_eq, measureReal_def,
    Measure.map_apply (measurable_nestedTupleToFin (2 * k)) hset,
    ← measureReal_def,
    preimage_canonicalFamilyMatchingEvent_nestedTupleToFin]

/-- The centered nested-prefix relative failure mass is exactly the
Euclidean residual-family relative failure mass at every finite index. -/
theorem canonicalCenteredGaussianPrefixUncenteredFailureRelative_eq_residual
    (k m p : ℕ) (x : ℝ) :
    canonicalCenteredGaussianPrefixUncenteredFailureRelative k m p x =
      canonicalResidualPrefixUncenteredStandardizedFailureRelative
        k m p x := by
  unfold canonicalCenteredGaussianPrefixUncenteredFailureRelative
    canonicalResidualPrefixUncenteredStandardizedFailureRelative
  dsimp only
  rw [nested_matching_inter_standardizedFailure_probability_eq_centeredFamily,
    nested_matching_probability_eq_centeredFamily,
    centeredFamily_matching_inter_standardizedFailure_probability_eq_residual,
    centeredFamily_matching_probability_eq_residual]

/-- Exact canonical matching mass in the centered nested-prefix model. -/
theorem canonicalCenteredGaussianMatchingEvent_probability
    (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (t : ℝ) :
    (nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)).real
        (canonicalGaussianMatchingEvent k t) =
      ((betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
        (Ioi t)) ^ k := by
  apply canonicalGaussianMatchingEvent_probability m _ hm k t
  simpa using finrank_centeredSubspace (N := m + 1)
    (Nat.zero_lt_succ m)

/-- The canonical centered matching event has nonzero mass eventually along
every all-gap sequence. -/
theorem eventually_canonicalCenteredGaussianMatchingEvent_ne_zero
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    ∀ᶠ p in atTop,
      nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)
        (canonicalGaussianMatchingEvent k
          (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ))) ≠ 0 := by
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have ht := tendsto_classicalCoherenceThreshold_div_mseq_zero hadm x
  filter_upwards [hadm, eventually_ge_atTop 4,
      ha.eventually (eventually_gt_atTop 0),
      ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with p hp hp4 hapos ht1
  have hm4 : 4 ≤ mseq p := hp4.trans hp.2
  have hm0 : (0 : ℝ) < (mseq p : ℝ) := by positivity
  have hthreshold : 0 < classicalCoherenceThreshold (mseq p) p x := by
    simpa [classicalCoherenceThreshold] using hapos
  have ht0 : 0 <
      classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ) :=
    div_pos hthreshold hm0
  have hb : 1 < (((mseq p - 1 : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_sub (by omega : 1 ≤ mseq p), Nat.cast_one]
    have hmR : (4 : ℝ) ≤ (mseq p : ℝ) := by exact_mod_cast hm4
    linarith
  have hq : 0 <
      (betaMeasure (1 / 2) (((mseq p - 1 : ℕ) : ℝ) / 2)).real
        (Ioi (classicalCoherenceThreshold (mseq p) p x /
          (mseq p : ℝ))) :=
    betaMeasure_half_Ioi_real_pos hb ht0 ht1
  have hreal : 0 <
      (nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)).real
        (canonicalGaussianMatchingEvent k
          (classicalCoherenceThreshold (mseq p) p x /
            (mseq p : ℝ))) := by
    rw [canonicalCenteredGaussianMatchingEvent_probability
      (mseq p) (by omega) k]
    exact pow_pos hq k
  intro hzero
  have hzeroReal :
      (nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)).real
        (canonicalGaussianMatchingEvent k
          (classicalCoherenceThreshold (mseq p) p x /
            (mseq p : ℝ))) = 0 := by
    rw [measureReal_def, hzero]
    simp
  linarith

/-- Along every all-gap sequence, the exact centered nested-prefix
uncentered failure ratio vanishes. -/
theorem tendsto_canonicalCenteredGaussianPrefixUncenteredFailureRelative_zero
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalCenteredGaussianPrefixUncenteredFailureRelative
        k (mseq p) p x) atTop (nhds 0) := by
  apply (tendsto_canonicalResidualPrefixUncenteredStandardizedFailureRelative_zero
    k hk hadm x).congr'
  exact Eventually.of_forall fun p ↦
    (canonicalCenteredGaussianPrefixUncenteredFailureRelative_eq_residual
      k (mseq p) p x).symm

end

end LogdetLean.Coherence
