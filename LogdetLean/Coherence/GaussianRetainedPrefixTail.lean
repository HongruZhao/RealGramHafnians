import LogdetLean.Coherence.RetainedPrefixTail
import LogdetLean.FixedPastBeta
import LogdetLean.SampleCorrelationBeta
/-!
# Exact Gaussian prefix--tail factorization

This file proves the strengthened finite form of Bartlett's normalized-Gram
decomposition needed by the coherence argument.  The first `q` Gaussian
columns themselves are retained.  Every subsequent normalized-Gram
determinant ratio is independent of that entire prefix and of all other tail
ratios, with its exact stage-dependent Beta law.

The final theorem transports the statement through ordinary sample centering:
with `m + 1` raw observations, the centered columns live in an
`m`-dimensional Gaussian subspace.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Exact retained-prefix Bartlett theorem.**  For `q + r ≤ m`, the first
`q` independent standard Gaussian vectors and the next `r` normalized-Gram
factors have the iterated product law.  Thus the tail factors are mutually
independent and jointly independent of the actual prefix vectors, not merely
of the earlier factors. -/
theorem map_gaussianRetainedPrefixTailFactors_eq_product
    (m q r : ℕ) (hdim : finrank ℝ E = m) (hqr : q + r ≤ m) :
    Measure.map
        (retainedPrefixTailStatistic
          (nestedNormalizedGramFactor (E := E)) q r)
        (nestedProductMeasure (stdGaussian E) (q + r)) =
      retainedPrefixTailProductMeasure (stdGaussian E)
        (gaussianGramSchmidtFactorMeasure m) q r := by
  apply map_retainedPrefixTailStatistic_eq_product_of_lt
    (stdGaussian E) (gaussianGramSchmidtFactorMeasure m)
    (nestedNormalizedGramFactor (E := E))
    measurable_uncurry_nestedNormalizedGramFactor q r
  intro s hsr
  have hstage : q + s < m := by omega
  have hrank : q + s ≤ finrank ℝ E := by omega
  filter_upwards
      [ae_linearIndependent_nested_stdGaussian (q + s) hrank]
      with past hpast
  exact map_nestedNormalizedGramFactor_stdGaussian_fixedPast
    m (q + s) hdim past hpast hstage

/-- Center every raw observation column and then retain the first `q`
centered Gaussian vectors together with the later normalized-Gram factors. -/
def centeredRetainedPrefixTailFactors (N q r : ℕ) :
    NestedTuple (ObservationSpace N) (q + r) →
      RetainedPrefixTailTuple (centeredSubspace N) ℝ q r :=
  retainedPrefixTailStatistic
      (nestedNormalizedGramFactor (E := centeredSubspace N)) q r ∘
    centerNested N (q + r)

/-- The centered retained-prefix/tail statistic is measurable. -/
theorem measurable_centeredRetainedPrefixTailFactors (N q r : ℕ) :
    Measurable (centeredRetainedPrefixTailFactors N q r) := by
  exact (measurable_retainedPrefixTailStatistic
    (nestedNormalizedGramFactor (E := centeredSubspace N))
    measurable_uncurry_nestedNormalizedGramFactor q r).comp
      (measurable_centerNested N (q + r))

/-- Exact sample-correlation form.  Starting from `m + 1` raw observations,
the first `q` centered Gaussian columns and the next `r` determinant ratios
factor into their product law whenever `q + r ≤ m`. -/
theorem map_centeredRetainedPrefixTailFactors_succ_eq_product
    (m q r : ℕ) (hqr : q + r ≤ m) :
    Measure.map (centeredRetainedPrefixTailFactors (m + 1) q r)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) (q + r)) =
      retainedPrefixTailProductMeasure
        (stdGaussian (centeredSubspace (m + 1)))
        (gaussianGramSchmidtFactorMeasure m) q r := by
  unfold centeredRetainedPrefixTailFactors
  have htail : Measurable
      (retainedPrefixTailStatistic
        (nestedNormalizedGramFactor (E := centeredSubspace (m + 1))) q r) :=
    measurable_retainedPrefixTailStatistic
      (nestedNormalizedGramFactor (E := centeredSubspace (m + 1)))
      measurable_uncurry_nestedNormalizedGramFactor q r
  rw [← Measure.map_map htail (measurable_centerNested (m + 1) (q + r))]
  rw [map_centerNested_nestedProductMeasure]
  exact map_gaussianRetainedPrefixTailFactors_eq_product
    (E := centeredSubspace (m + 1)) m q r
      (finrank_centeredSubspace (Nat.zero_lt_succ m)) hqr

end

end LogdetLean.Coherence
