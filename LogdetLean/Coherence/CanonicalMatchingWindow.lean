import LogdetLean.Coherence.ScoreWindow
import LogdetLean.Coherence.CanonicalPrefixControl
/-!
# Bounded windows on a canonical Gaussian matching

For the canonical matching `(0,1), (2,3), ...`, this file requires every
selected squared correlation to have normalized location in one common
half-open window `(a,b]`.  It proves the finite-sample product formula

`P(all k selected locations lie in (a,b]) = (q(a) - q(b)) ^ k`.

This is a fixed finite matching calculation.  It does not assert convergence
of counts or of a point process.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set
open scoped RealInnerProductSpace

/-- The lower endpoint for the unscaled squared-correlation variable. -/
def canonicalMatchingWindowEndpoint (m p : ℕ) (x : ℝ) : ℝ :=
  classicalCoherenceThreshold m p x / (m : ℝ)

/-- Rectangle in the ordered-forest score space on which every selected
odd-stage squared correlation has normalized location in `(a,b]`.  Even
stages are roots and remain unrestricted. -/
def canonicalMatchingScoreWindowEvent (m p : ℕ) (a b : ℝ) :
    (k : ℕ) → Set (NestedTuple ℝ (2 * k))
  | 0 => Set.univ
  | k + 1 =>
      ((canonicalMatchingScoreWindowEvent m p a b k) ×ˢ Set.univ) ×ˢ
        Set.Ioc (canonicalMatchingWindowEndpoint m p a)
          (canonicalMatchingWindowEndpoint m p b)

/-- The canonical bounded score rectangle is measurable. -/
theorem measurableSet_canonicalMatchingScoreWindowEvent
    (m p : ℕ) (a b : ℝ) :
    ∀ k, MeasurableSet (canonicalMatchingScoreWindowEvent m p a b k) := by
  intro k
  induction k with
  | zero => simp [canonicalMatchingScoreWindowEvent]
  | succ k ih =>
      simpa [canonicalMatchingScoreWindowEvent] using
        ((ih.prod MeasurableSet.univ).prod measurableSet_Ioc)

/-- Membership in `(a,b]` implies exceedance of its lower endpoint, so the
bounded rectangle is contained in the usual common-threshold canonical
matching rectangle. -/
theorem canonicalMatchingScoreWindowEvent_subset_lowerMatching
    (m p : ℕ) (a b : ℝ) :
    ∀ k,
      canonicalMatchingScoreWindowEvent m p a b k ⊆
        canonicalMatchingScoreEvent
          (canonicalMatchingWindowEndpoint m p a) k := by
  intro k
  induction k with
  | zero => simp [canonicalMatchingScoreWindowEvent,
      canonicalMatchingScoreEvent]
  | succ k ih =>
      rintro ⟨⟨past, root⟩, score⟩ h
      change
        ((past ∈ canonicalMatchingScoreWindowEvent m p a b k ∧
            root ∈ Set.univ) ∧
          score ∈ Set.Ioc (canonicalMatchingWindowEndpoint m p a)
            (canonicalMatchingWindowEndpoint m p b)) at h
      change
        ((past ∈ canonicalMatchingScoreEvent
              (canonicalMatchingWindowEndpoint m p a) k ∧
            root ∈ Set.univ) ∧
          score ∈ Set.Ioi (canonicalMatchingWindowEndpoint m p a))
      exact ⟨⟨ih h.1.1, Set.mem_univ root⟩, h.2.1⟩

/-- The Beta mass of one normalized bounded window is the difference of the
two classical upper tails. -/
theorem pairBeta_window_probability_eq_betaCorrelationWindowProbability
    {m p : ℕ} (hm : 2 ≤ m) {a b : ℝ} (hab : a ≤ b) :
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
        (Set.Ioc (canonicalMatchingWindowEndpoint m p a)
          (canonicalMatchingWindowEndpoint m p b)) =
      betaCorrelationWindowProbability m p a b := by
  let _ : IsProbabilityMeasure
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) :=
    pairBeta_isProbabilityMeasure hm
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  have hthreshold :
      classicalCoherenceThreshold m p a ≤
        classicalCoherenceThreshold m p b := by
    unfold classicalCoherenceThreshold
    linarith
  have hendpoint :
      canonicalMatchingWindowEndpoint m p a ≤
        canonicalMatchingWindowEndpoint m p b := by
    unfold canonicalMatchingWindowEndpoint
    exact (div_le_div_iff_of_pos_right hmR).2 hthreshold
  have hsubset :
      Set.Ioi (canonicalMatchingWindowEndpoint m p b) ⊆
        Set.Ioi (canonicalMatchingWindowEndpoint m p a) := by
    intro x hx
    exact hendpoint.trans_lt hx
  rw [show Set.Ioc (canonicalMatchingWindowEndpoint m p a)
      (canonicalMatchingWindowEndpoint m p b) =
      Set.Ioi (canonicalMatchingWindowEndpoint m p a) \
        Set.Ioi (canonicalMatchingWindowEndpoint m p b) by
      ext x
      simp]
  rw [measureReal_sdiff hsubset measurableSet_Ioi]
  rfl

/-- Exact product mass of the canonical matching score rectangle under the
ordered-forest factor law. -/
theorem canonicalMatchingScoreWindowEvent_probability
    (m p k : ℕ) (a b : ℝ) (hm : 2 ≤ m) (hab : a ≤ b) :
    (nestedProductMeasureFamily
      (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).real
        (canonicalMatchingScoreWindowEvent m p a b k) =
      (betaCorrelationWindowProbability m p a b) ^ k := by
  induction k with
  | zero =>
      simp [canonicalMatchingScoreWindowEvent, nestedProductMeasureFamily]
  | succ k ih =>
      change
        ((((nestedProductMeasureFamily
            (orderedForestFactorMeasure canonicalMatchingForest m) (2 * k)).prod
              (orderedForestFactorMeasure canonicalMatchingForest m (2 * k))).prod
                (orderedForestFactorMeasure canonicalMatchingForest m
                  (2 * k + 1))).real
          (((canonicalMatchingScoreWindowEvent m p a b k) ×ˢ Set.univ) ×ˢ
            Set.Ioc (canonicalMatchingWindowEndpoint m p a)
              (canonicalMatchingWindowEndpoint m p b))) = _
      simp only [measureReal_prod_prod]
      rw [ih, canonicalMatching_factorMeasure_even,
        canonicalMatching_factorMeasure_odd,
        pairBeta_window_probability_eq_betaCorrelationWindowProbability
          hm hab]
      simp [pow_succ]

/-- Pull the bounded matching rectangle back to the independent Gaussian
column space. -/
def canonicalGaussianMatchingWindowEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m p k : ℕ) (a b : ℝ) : Set (NestedTuple E (2 * k)) :=
  orderedForestScores (E := E) canonicalMatchingForest (2 * k) ⁻¹'
    canonicalMatchingScoreWindowEvent m p a b k

/-- The canonical Gaussian bounded-matching event is measurable. -/
theorem measurableSet_canonicalGaussianMatchingWindowEvent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m p k : ℕ) (a b : ℝ) :
    MeasurableSet
      (canonicalGaussianMatchingWindowEvent (E := E) m p k a b) := by
  exact (measurableSet_canonicalMatchingScoreWindowEvent m p a b k).preimage
    (measurable_sequentialStatistic
      (orderedForestScore (E := E) canonicalMatchingForest)
      (measurable_uncurry_orderedForestScore canonicalMatchingForest)
      (2 * k))

/-- The bounded canonical Gaussian event is contained in the usual matching
event at the common lower threshold. -/
theorem canonicalGaussianMatchingWindowEvent_subset_lowerMatching
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m p k : ℕ) (a b : ℝ) :
    canonicalGaussianMatchingWindowEvent (E := E) m p k a b ⊆
      canonicalGaussianMatchingEvent (E := E) k
        (canonicalMatchingWindowEndpoint m p a) := by
  exact Set.preimage_mono
    (canonicalMatchingScoreWindowEvent_subset_lowerMatching m p a b k)

/-- Exact finite-sample probability that all `k` canonical squared
correlations have normalized locations in `(a,b]`. -/
theorem canonicalGaussianMatchingWindowEvent_probability
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m p : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (nestedProductMeasure (stdGaussian E) (2 * k)).real
        (canonicalGaussianMatchingWindowEvent (E := E) m p k a b) =
      (betaCorrelationWindowProbability m p a b) ^ k := by
  have hmeas : Measurable
      (orderedForestScores (E := E) canonicalMatchingForest (2 * k)) :=
    measurable_sequentialStatistic
      (orderedForestScore (E := E) canonicalMatchingForest)
      (measurable_uncurry_orderedForestScore canonicalMatchingForest)
      (2 * k)
  have hset := measurableSet_canonicalMatchingScoreWindowEvent m p a b k
  unfold canonicalGaussianMatchingWindowEvent
  rw [measureReal_def, ← Measure.map_apply hmeas hset,
    map_orderedForestScores_eq_nestedProduct
      canonicalMatchingForest m hdim hm (2 * k)]
  exact canonicalMatchingScoreWindowEvent_probability m p k a b hm hab

end

end LogdetLean.Coherence
