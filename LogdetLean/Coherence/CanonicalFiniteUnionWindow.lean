import LogdetLean.Coherence.FiniteUnionScoreWindow
import LogdetLean.Coherence.CanonicalMatchingWindow
/-!
# Canonical matching in a finite union of disjoint score windows

This module lifts a finite disjoint union of normalized half-open intervals
to the canonical Gaussian matching.  It proves exact one-edge Beta mass,
the corresponding fixed-`k` product probability, and domination by a common
lower-threshold matching event.

The results are finite-sample identities only.  No multibin or point-process
convergence is claimed.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set
open scoped BigOperators RealInnerProductSpace

/-- Normalized location corresponding to an unscaled squared correlation. -/
def normalizedLocationFromSquaredCorrelation
    (m p : ℕ) (r : ℝ) : ℝ :=
  (m : ℝ) * r - classicalCoherenceThreshold m p 0

/-- Rescaling by a positive residual dimension identifies a raw squared-
correlation interval with its normalized score interval. -/
theorem mem_canonicalMatchingRawWindow_iff
    {m p : ℕ} (hm : 2 ≤ m) (a b r : ℝ) :
    r ∈ Set.Ioc (canonicalMatchingWindowEndpoint m p a)
        (canonicalMatchingWindowEndpoint m p b) ↔
      normalizedLocationFromSquaredCorrelation m p r ∈ Set.Ioc a b := by
  have hmR : (0 : ℝ) < (m : ℝ) := by positivity
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' := (div_lt_iff₀ hmR).1 hlo
    have hhi' := (le_div_iff₀ hmR).1 hhi
    unfold classicalCoherenceThreshold at hlo' hhi'
    unfold normalizedLocationFromSquaredCorrelation classicalCoherenceThreshold
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_lt_iff₀ hmR).2
      unfold classicalCoherenceThreshold
      unfold normalizedLocationFromSquaredCorrelation
        classicalCoherenceThreshold at hlo
      nlinarith
    · apply (le_div_iff₀ hmR).2
      unfold classicalCoherenceThreshold
      unfold normalizedLocationFromSquaredCorrelation
        classicalCoherenceThreshold at hhi
      nlinarith

/-- Raw squared-correlation set corresponding to the normalized finite
union. -/
def canonicalMatchingRawFiniteWindowUnion
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) : Set ℝ :=
  ⋃ i, Set.Ioc
    (canonicalMatchingWindowEndpoint m p (W.lower i))
    (canonicalMatchingWindowEndpoint m p (W.upper i))

theorem measurableSet_canonicalMatchingRawFiniteWindowUnion
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) :
    MeasurableSet (canonicalMatchingRawFiniteWindowUnion W m p) := by
  exact MeasurableSet.iUnion fun i ↦ measurableSet_Ioc

/-- Pairwise disjoint normalized windows remain pairwise disjoint after the
raw squared-correlation rescaling. -/
theorem pairwise_disjoint_canonicalMatchingRawWindows
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p : ℕ} (hm : 2 ≤ m) :
    Pairwise fun i j ↦ Disjoint
      (Set.Ioc
        (canonicalMatchingWindowEndpoint m p (W.lower i))
        (canonicalMatchingWindowEndpoint m p (W.upper i)))
      (Set.Ioc
        (canonicalMatchingWindowEndpoint m p (W.lower j))
        (canonicalMatchingWindowEndpoint m p (W.upper j))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro r hri hrj
  have hni := (mem_canonicalMatchingRawWindow_iff
    hm (W.lower i) (W.upper i) r).1 hri
  have hnj := (mem_canonicalMatchingRawWindow_iff
    hm (W.lower j) (W.upper j) r).1 hrj
  exact (Set.disjoint_left.mp (W.pairwiseDisjoint hij)) hni hnj

/-- Exact Beta mass of the raw finite union. -/
theorem pairBeta_canonicalMatchingRawFiniteWindowUnion_probability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p : ℕ} (hm : 2 ≤ m) :
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
        (canonicalMatchingRawFiniteWindowUnion W m p) =
      finiteUnionBetaProbability W m p := by
  let _ : IsProbabilityMeasure
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) :=
    pairBeta_isProbabilityMeasure hm
  unfold canonicalMatchingRawFiniteWindowUnion finiteUnionBetaProbability
  rw [measureReal_iUnion_fintype
    (pairwise_disjoint_canonicalMatchingRawWindows W hm)
    (fun i ↦ measurableSet_Ioc)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact pairBeta_window_probability_eq_betaCorrelationWindowProbability
    hm (W.ordered i)

/-- A common lower endpoint dominates the whole raw finite union. -/
theorem canonicalMatchingRawFiniteWindowUnion_subset_lowerTail
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p : ℕ} (hm : 2 ≤ m) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) :
    canonicalMatchingRawFiniteWindowUnion W m p ⊆
      Set.Ioi (canonicalMatchingWindowEndpoint m p c) := by
  intro r hr
  rcases Set.mem_iUnion.mp hr with ⟨i, hi⟩
  have hmR : (0 : ℝ) < (m : ℝ) := by positivity
  have hthreshold :
      classicalCoherenceThreshold m p c ≤
        classicalCoherenceThreshold m p (W.lower i) := by
    unfold classicalCoherenceThreshold
    linarith [hc i]
  have hendpoint :
      canonicalMatchingWindowEndpoint m p c ≤
        canonicalMatchingWindowEndpoint m p (W.lower i) := by
    unfold canonicalMatchingWindowEndpoint
    exact (div_le_div_iff_of_pos_right hmR).2 hthreshold
  exact hendpoint.trans_lt hi.1

/-- Canonical score rectangle in which every selected odd-stage score lies
in the same finite union. -/
def canonicalMatchingScoreFiniteUnionEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) : (k : ℕ) → Set (NestedTuple ℝ (2 * k))
  | 0 => Set.univ
  | k + 1 =>
      ((canonicalMatchingScoreFiniteUnionEvent W m p k) ×ˢ Set.univ) ×ˢ
        canonicalMatchingRawFiniteWindowUnion W m p

theorem measurableSet_canonicalMatchingScoreFiniteUnionEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) :
    ∀ k, MeasurableSet (canonicalMatchingScoreFiniteUnionEvent W m p k) := by
  intro k
  induction k with
  | zero => simp [canonicalMatchingScoreFiniteUnionEvent]
  | succ k ih =>
      simpa [canonicalMatchingScoreFiniteUnionEvent] using
        ((ih.prod MeasurableSet.univ).prod
          (measurableSet_canonicalMatchingRawFiniteWindowUnion W m p))

/-- The canonical finite-union rectangle is contained in the ordinary
matching rectangle at any common lower endpoint. -/
theorem canonicalMatchingScoreFiniteUnionEvent_subset_lowerMatching
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p : ℕ} (hm : 2 ≤ m) (c : ℝ)
    (hc : ∀ i, c ≤ W.lower i) :
    ∀ k,
      canonicalMatchingScoreFiniteUnionEvent W m p k ⊆
        canonicalMatchingScoreEvent
          (canonicalMatchingWindowEndpoint m p c) k := by
  intro k
  induction k with
  | zero => simp [canonicalMatchingScoreFiniteUnionEvent,
      canonicalMatchingScoreEvent]
  | succ k ih =>
      rintro ⟨⟨past, root⟩, score⟩ h
      change
        ((past ∈ canonicalMatchingScoreFiniteUnionEvent W m p k ∧
            root ∈ Set.univ) ∧
          score ∈ canonicalMatchingRawFiniteWindowUnion W m p) at h
      change
        ((past ∈ canonicalMatchingScoreEvent
              (canonicalMatchingWindowEndpoint m p c) k ∧
            root ∈ Set.univ) ∧
          score ∈ Set.Ioi (canonicalMatchingWindowEndpoint m p c))
      exact ⟨⟨ih h.1.1, Set.mem_univ root⟩,
        canonicalMatchingRawFiniteWindowUnion_subset_lowerTail
          W hm c hc h.2⟩

/-- Exact product mass of the canonical finite-union score rectangle under
the ordered-forest factor law. -/
theorem canonicalMatchingScoreFiniteUnionEvent_probability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p k : ℕ) (hm : 2 ≤ m) :
    (nestedProductMeasureFamily
      (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).real
        (canonicalMatchingScoreFiniteUnionEvent W m p k) =
      (finiteUnionBetaProbability W m p) ^ k := by
  induction k with
  | zero =>
      simp [canonicalMatchingScoreFiniteUnionEvent,
        nestedProductMeasureFamily]
  | succ k ih =>
      change
        ((((nestedProductMeasureFamily
            (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).prod
              (orderedForestFactorMeasure canonicalMatchingForest m (2 * k))).prod
                (orderedForestFactorMeasure canonicalMatchingForest m
                  (2 * k + 1))).real
          (((canonicalMatchingScoreFiniteUnionEvent W m p k) ×ˢ Set.univ) ×ˢ
            canonicalMatchingRawFiniteWindowUnion W m p)) = _
      simp only [measureReal_prod_prod]
      rw [ih, canonicalMatching_factorMeasure_even,
        canonicalMatching_factorMeasure_odd,
        pairBeta_canonicalMatchingRawFiniteWindowUnion_probability W hm]
      simp [pow_succ]

/-- Pull the canonical finite-union rectangle back to independent Gaussian
columns. -/
def canonicalGaussianMatchingFiniteUnionEvent
    {ι : Type*} {E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : FiniteScoreWindowFamily ι) (m p k : ℕ) :
    Set (NestedTuple E (2 * k)) :=
  orderedForestScores (E := E) canonicalMatchingForest (2 * k) ⁻¹'
    canonicalMatchingScoreFiniteUnionEvent W m p k

theorem measurableSet_canonicalGaussianMatchingFiniteUnionEvent
    {ι : Type*} {E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : FiniteScoreWindowFamily ι) (m p k : ℕ) :
    MeasurableSet
      (canonicalGaussianMatchingFiniteUnionEvent (E := E) W m p k) := by
  exact (measurableSet_canonicalMatchingScoreFiniteUnionEvent
    W m p k).preimage
      (measurable_sequentialStatistic
        (orderedForestScore (E := E) canonicalMatchingForest)
        (measurable_uncurry_orderedForestScore canonicalMatchingForest)
        (2 * k))

/-- Gaussian canonical finite-union event is dominated by the common lower
matching event. -/
theorem canonicalGaussianMatchingFiniteUnionEvent_subset_lowerMatching
    {ι : Type*} {E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : FiniteScoreWindowFamily ι) {m p : ℕ} (hm : 2 ≤ m)
    (k : ℕ) (c : ℝ) (hc : ∀ i, c ≤ W.lower i) :
    canonicalGaussianMatchingFiniteUnionEvent (E := E) W m p k ⊆
      canonicalGaussianMatchingEvent (E := E) k
        (canonicalMatchingWindowEndpoint m p c) := by
  exact Set.preimage_mono
    (canonicalMatchingScoreFiniteUnionEvent_subset_lowerMatching
      W hm c hc k)

/-- Exact finite-sample canonical matching probability for a finite disjoint
union of score windows. -/
theorem canonicalGaussianMatchingFiniteUnionEvent_probability
    {ι : Type*} {E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m) (k : ℕ) :
    (nestedProductMeasure (stdGaussian E) (2 * k)).real
        (canonicalGaussianMatchingFiniteUnionEvent (E := E) W m p k) =
      (finiteUnionBetaProbability W m p) ^ k := by
  have hmeas : Measurable
      (orderedForestScores (E := E) canonicalMatchingForest (2 * k)) :=
    measurable_sequentialStatistic
      (orderedForestScore (E := E) canonicalMatchingForest)
      (measurable_uncurry_orderedForestScore canonicalMatchingForest)
      (2 * k)
  have hset := measurableSet_canonicalMatchingScoreFiniteUnionEvent
    W m p k
  unfold canonicalGaussianMatchingFiniteUnionEvent
  rw [measureReal_def, ← Measure.map_apply hmeas hset,
    map_orderedForestScores_eq_nestedProduct
      canonicalMatchingForest m hdim hm (2 * k)]
  exact canonicalMatchingScoreFiniteUnionEvent_probability W m p k hm

end

end LogdetLean.Coherence
