import LogdetLean.Coherence.FiniteDeletionCLT
import LogdetLean.WishartSequentialKernel
/-!
# Pointwise prefix--tail determinant decomposition

The retained-prefix product law is distributional.  This file records the
matching pointwise identity: on the linearly-independent event, the full
normalized-Gram log determinant is the retained-prefix log determinant plus
the sum of the logarithms of all later Bartlett ratios.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cleaner recursive characterization of the retained source prefix. -/
def nestedTuplePrefix (q : ℕ) :
    (r : ℕ) → NestedTuple E (q + r) → NestedTuple E q
  | 0, z => z
  | r + 1, z => nestedTuplePrefix q r z.1

/-- The tail product attached to a retained prefix. -/
def retainedTailProduct {α : Type} (q : ℕ) :
    (r : ℕ) → RetainedPrefixTailTuple α ℝ q r → ℝ
  | 0, _ => 1
  | r + 1, z => retainedTailProduct q r z.1 * z.2

/-- Successive determinant ratios telescope from the retained prefix to the
full normalized-Gram determinant. -/
theorem nestedNormalizedGramDet_eq_prefix_mul_retainedTailProduct
    (q : ℕ) : ∀ r (z : NestedTuple E (q + r)),
    LinearIndependent ℝ (nestedTupleToFin (q + r) z) →
    nestedNormalizedGramDet (q + r) z =
      nestedNormalizedGramDet q (nestedTuplePrefix q r z) *
        retainedTailProduct q r
          (retainedPrefixTailStatistic
            (nestedNormalizedGramFactor (E := E)) q r z) := by
  intro r
  induction r with
  | zero =>
      intro z hz
      simp [nestedTuplePrefix, retainedTailProduct]
  | succ r ih =>
      rintro ⟨past, x⟩ hfull
      have hpast : LinearIndependent ℝ
          (nestedTupleToFin (q + r) past) :=
        (linearIndependent_finSnoc.mp hfull).1
      have hdetPast : nestedNormalizedGramDet (q + r) past ≠ 0 :=
        det_normalizedGram_ne_zero_of_linearIndependent _ hpast
      have hratio :
          nestedNormalizedGramDet (q + r + 1) (past, x) =
            nestedNormalizedGramDet (q + r) past *
              nestedNormalizedGramFactor (q + r) past x := by
        unfold nestedNormalizedGramFactor
        field_simp [hdetPast]
      change nestedNormalizedGramDet (q + r + 1) (past, x) =
        nestedNormalizedGramDet q (nestedTuplePrefix q r past) *
          (retainedTailProduct q r
            (retainedPrefixTailStatistic
              (nestedNormalizedGramFactor (E := E)) q r past) *
            nestedNormalizedGramFactor (q + r) past x)
      rw [hratio, ih past hpast]
      ring

/-- Logarithmic version of the telescoping identity. -/
theorem log_nestedNormalizedGramDet_eq_log_prefix_add_retainedTailLogSum
    [FiniteDimensional ℝ E]
    (q : ℕ) : ∀ r (z : NestedTuple E (q + r)),
    LinearIndependent ℝ (nestedTupleToFin (q + r) z) →
    Real.log (nestedNormalizedGramDet (q + r) z) =
      Real.log (nestedNormalizedGramDet q (nestedTuplePrefix q r z)) +
        retainedTailLogSum q r
          (retainedPrefixTailStatistic
            (nestedNormalizedGramFactor (E := E)) q r z) := by
  intro r
  induction r with
  | zero =>
      intro z hz
      simp [nestedTuplePrefix, retainedTailLogSum]
  | succ r ih =>
      rintro ⟨past, x⟩ hfull
      have hpast : LinearIndependent ℝ
          (nestedTupleToFin (q + r) past) :=
        (linearIndependent_finSnoc.mp hfull).1
      have hdetPastPos : 0 < nestedNormalizedGramDet (q + r) past :=
        det_normalizedGram_pos_of_linearIndependent _ hpast
      have hfactorPos : 0 < nestedNormalizedGramFactor (q + r) past x :=
        nestedNormalizedGramFactor_pos_of_linearIndependent past x hfull
      have hratio :
          nestedNormalizedGramDet (q + r + 1) (past, x) =
            nestedNormalizedGramDet (q + r) past *
              nestedNormalizedGramFactor (q + r) past x := by
        unfold nestedNormalizedGramFactor
        field_simp [hdetPastPos.ne']
      change Real.log (nestedNormalizedGramDet (q + r + 1) (past, x)) =
        Real.log (nestedNormalizedGramDet q (nestedTuplePrefix q r past)) +
          (retainedTailLogSum q r
            (retainedPrefixTailStatistic
              (nestedNormalizedGramFactor (E := E)) q r past) +
            Real.log (nestedNormalizedGramFactor (q + r) past x))
      rw [hratio, Real.log_mul hdetPastPos.ne' hfactorPos.ne', ih past hpast]
      ring

/-! ## Centered sample-correlation specialization -/

/-- Centered Gaussian columns are linearly independent almost surely through
the full admissible range. -/
theorem ae_linearIndependent_centerNested
    {m p : ℕ} (hpm : p ≤ m) :
    ∀ᵐ z ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p,
      LinearIndependent ℝ
        (nestedTupleToFin p (centerNested (m + 1) p z)) := by
  let E := centeredSubspace (m + 1)
  have hcentered :
      ∀ᵐ w ∂nestedProductMeasure (stdGaussian E) p,
        LinearIndependent ℝ (nestedTupleToFin p w) := by
    exact ae_linearIndependent_nested_stdGaussian p
      (by
        rw [show finrank ℝ E = m by
          simpa [E] using finrank_centeredSubspace (Nat.zero_lt_succ m)]
        exact hpm)
  have hset : MeasurableSet
      {w : NestedTuple E p |
        LinearIndependent ℝ (nestedTupleToFin p w)} :=
    (measurableSet_linearlyIndependentTuples (E := E) p).preimage
      (measurable_nestedTupleToFin (α := E) p)
  have hmapped :
      ∀ᵐ w ∂Measure.map (centerNested (m + 1) p)
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) p),
        LinearIndependent ℝ (nestedTupleToFin p w) := by
    rw [map_centerNested_nestedProductMeasure]
    exact hcentered
  exact (ae_map_iff
    (measurable_centerNested (m + 1) p).aemeasurable hset).mp hmapped

/-- Almost-sure prefix--tail decomposition of the ordinary centered sample
correlation log determinant. -/
theorem ae_log_centeredSampleCorrelationDet_eq_prefix_add_retainedTail
    {m q r : ℕ} (hqr : q + r ≤ m) :
    ∀ᵐ z ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r),
      Real.log (centeredSampleCorrelationDet (m + 1) (q + r) z) =
        Real.log (nestedNormalizedGramDet q
          (nestedTuplePrefix q r (centerNested (m + 1) (q + r) z))) +
        retainedTailLogSum q r
          (centeredRetainedPrefixTailFactors (m + 1) q r z) := by
  filter_upwards [ae_linearIndependent_centerNested hqr] with z hz
  rw [centeredSampleCorrelationDet_eq_nestedCenteredNormalizedGramDet
    (Nat.zero_lt_succ m)]
  unfold nestedCenteredNormalizedGramDet
  exact log_nestedNormalizedGramDet_eq_log_prefix_add_retainedTailLogSum
    (E := centeredSubspace (m + 1)) q r
      (centerNested (m + 1) (q + r) z) hz

/-- The retained-prefix log determinant, centered by its own exact mean and
divided by the standard deviation of the full `p`-dimensional statistic. -/
def standardizedCenteredPrefixLogDetAtFullScale
    (m q p : ℕ) (w : NestedTuple (centeredSubspace (m + 1)) q) : ℝ :=
  (Real.log (nestedNormalizedGramDet q w) - nullCenter m q) /
    Real.sqrt (nullVariance m p)

/-- Almost-sure additive decomposition of the actual standardized centered
log determinant into its retained-prefix perturbation and its standardized
independent tail statistic. -/
theorem ae_Z0mpStatistic_eq_prefix_add_standardizedGaussianRetainedTail
    {m q r : ℕ} (hqr : q + r ≤ m) :
    ∀ᵐ z ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (q + r),
      Z0mpStatistic m (q + r) z =
        standardizedCenteredPrefixLogDetAtFullScale m q (q + r)
          (nestedTuplePrefix q r (centerNested (m + 1) (q + r) z)) +
        standardizedGaussianRetainedTailStatistic m q r z := by
  filter_upwards
      [ae_log_centeredSampleCorrelationDet_eq_prefix_add_retainedTail hqr]
      with z hlog
  unfold Z0mpStatistic standardizedCenteredPrefixLogDetAtFullScale
  unfold standardizedGaussianRetainedTailStatistic
    standardizedRetainedTailLogStatistic
  simp only [Function.comp_apply]
  rw [hlog]
  rw [← nullCenter_eq_nullCenterDigammaSeries hqr]
  rw [← nullVariance_eq_nullVSeries hqr]
  unfold deletedTailCenter
  ring

end

end LogdetLean.Coherence
