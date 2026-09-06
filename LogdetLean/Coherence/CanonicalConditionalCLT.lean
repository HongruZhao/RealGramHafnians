import LogdetLean.Coherence.CanonicalPrefixControl
import LogdetLean.Coherence.ConditionedPrefixMarginal
import LogdetLean.Coherence.PrefixCenterScale
import LogdetLean.Coherence.ConditionalPrefixCLT
import LogdetLean.Coherence.ConditionalProbabilityReal
/-!
# Conditional Gaussian limit for a canonical coherence matching

This module combines the model-specific canonical-prefix estimate with the
abstract conditional prefix--tail central limit theorem.  The conditioning
event requires the `k` disjoint correlations `(0,1), (2,3), ...` to exceed
the classical coherence threshold.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology ProbabilityTheory ENNReal

/-- Canonical matching event on the centered right-nested prefix. -/
def canonicalCenteredMatchingPrefixEvent
    (k m p : ℕ) (x : ℝ) :
    Set (NestedTuple (centeredSubspace (m + 1)) (2 * k)) :=
  canonicalGaussianMatchingEvent k
    (classicalCoherenceThreshold m p x / (m : ℝ))

theorem measurableSet_canonicalCenteredMatchingPrefixEvent
    (k m p : ℕ) (x : ℝ) :
    MeasurableSet (canonicalCenteredMatchingPrefixEvent k m p x) :=
  measurableSet_canonicalGaussianMatchingEvent _ _

/-- Radius controlling the centered fixed-prefix contribution at the global
null standard-deviation scale. -/
def canonicalCenteredPrefixTotalRadius
    (k m p : ℕ) (x : ℝ) : ℝ :=
  canonicalPrefixStandardizedLogdetRadius k m p x +
    |nullCenter m (2 * k)| / Real.sqrt (nullVariance m p)

/-- The bundled prefix--tail joint law for the canonical matching event. -/
def canonicalConditionedPrefixTailJointOrGaussian
    (k m p : ℕ) (x : ℝ) : ProbabilityMeasure (ℝ × ℝ) :=
  conditionedPrefixTailJointOrGaussian m (2 * k) p
    (canonicalCenteredMatchingPrefixEvent k m p x)
    (measurableSet_canonicalCenteredMatchingPrefixEvent k m p x)

/-- The combined stochastic-plus-centering radius is eventually
nonnegative. -/
theorem eventually_canonicalCenteredPrefixTotalRadius_nonneg
    (k : ℕ) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    ∀ᶠ p in atTop,
      0 ≤ canonicalCenteredPrefixTotalRadius k (mseq p) p x := by
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  filter_upwards [hadm, ha.eventually (eventually_ge_atTop 0)]
    with p hp hthreshold
  have hm0 : (0 : ℝ) ≤ (mseq p : ℝ) := by positivity
  have ht0 : 0 ≤
      classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ) :=
    div_nonneg (by
      simpa [classicalCoherenceThreshold] using hthreshold) hm0
  unfold canonicalCenteredPrefixTotalRadius
    canonicalPrefixStandardizedLogdetRadius
  positivity

/-- The combined centered-prefix radius shrinks to zero in every all-gap
regime. -/
theorem tendsto_canonicalCenteredPrefixTotalRadius_zero
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalCenteredPrefixTotalRadius k (mseq p) p x)
      atTop (nhds 0) := by
  have hraw := tendsto_canonicalPrefixStandardizedLogdetRadius_zero
    k hadm x
  have hcenter :=
    tendsto_abs_fixedPrefix_nullCenter_over_sqrt_nullVariance_zero
      (2 * k) (by omega) mseq hadm
  simpa [canonicalCenteredPrefixTotalRadius] using hraw.add hcenter

/-- At a valid finite index, the centered-prefix bad mass under the
conditioned prefix law is bounded by the previously proved uncentered
relative-failure quotient. -/
theorem conditionedCenteredPrefix_badMass_le_uncenteredFailureRelative
    (k m p : ℕ) (hp : Admissible m p) (x : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingPrefixEvent k m p x) ≠ 0) :
    ((nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k))[|
        canonicalCenteredMatchingPrefixEvent k m p x]).real
      ((standardizedCenteredPrefixLogDetAtFullScale m (2 * k) p) ⁻¹'
        (Icc (-(canonicalCenteredPrefixTotalRadius k m p x))
          (canonicalCenteredPrefixTotalRadius k m p x))ᶜ) ≤
      canonicalCenteredGaussianPrefixUncenteredFailureRelative
        k m p x := by
  let xi := nestedProductMeasure
    (stdGaussian (centeredSubspace (m + 1))) (2 * k)
  let s := canonicalCenteredMatchingPrefixEvent k m p x
  let G := canonicalGaussianStandardizedPrefixLogdetFailure
    (E := centeredSubspace (m + 1)) k m p x
  let R := canonicalCenteredPrefixTotalRadius k m p x
  let P := standardizedCenteredPrefixLogDetAtFullScale m (2 * k) p
  have hsub : P ⁻¹' (Icc (-R) R)ᶜ ⊆ G := by
    intro w hw
    by_contra hwG
    have hraw :
        |Real.log (nestedNormalizedGramDet (2 * k) w) /
            Real.sqrt (nullVSeries m p)| ≤
          canonicalPrefixStandardizedLogdetRadius k m p x := by
      apply le_of_not_gt
      intro hgt
      apply hwG
      change canonicalPrefixStandardizedLogdetRadius k m p x <
        |Real.log (normalizedGram (nestedTupleToFin (2 * k) w)).det /
          Real.sqrt (nullVSeries m p)|
      simpa [nestedNormalizedGramDet] using hgt
    have hV : nullVariance m p = nullVSeries m p :=
      nullVariance_eq_nullVSeries hp.2
    have hraw' :
        |Real.log (nestedNormalizedGramDet (2 * k) w) /
            Real.sqrt (nullVariance m p)| ≤
          canonicalPrefixStandardizedLogdetRadius k m p x := by
      simpa [hV] using hraw
    have hP :
        |P w| ≤ R := by
      calc
        |P w| =
            |Real.log (nestedNormalizedGramDet (2 * k) w) /
                Real.sqrt (nullVariance m p) -
              nullCenter m (2 * k) /
                Real.sqrt (nullVariance m p)| := by
              congr 1
              dsimp [P, standardizedCenteredPrefixLogDetAtFullScale]
              ring
        _ ≤
            |Real.log (nestedNormalizedGramDet (2 * k) w) /
                Real.sqrt (nullVariance m p)| +
              |nullCenter m (2 * k) /
                Real.sqrt (nullVariance m p)| := abs_sub _ _
        _ =
            |Real.log (nestedNormalizedGramDet (2 * k) w) /
                Real.sqrt (nullVariance m p)| +
              |nullCenter m (2 * k)| /
                Real.sqrt (nullVariance m p) := by
              congr 1
              rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ R := by
              exact add_le_add hraw' le_rfl
    apply hw
    exact (abs_le.mp hP)
  have hmono : (xi[|s]).real (P ⁻¹' (Icc (-R) R)ᶜ) ≤
      (xi[|s]).real G := measureReal_mono hsub
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_canonicalCenteredMatchingPrefixEvent k m p x
  have hden : xi.real s ≠ 0 :=
    (measureReal_ne_zero_iff (by finiteness)).2 hs0
  have hmul := measureReal_inter_eq_measureReal_mul_cond xi s G hs
  have hcond : (xi[|s]).real G = xi.real (s ∩ G) / xi.real s := by
    apply (eq_div_iff hden).2
    calc
      (xi[|s]).real G * xi.real s =
          xi.real s * (xi[|s]).real G := mul_comm _ _
      _ = xi.real (s ∩ G) := hmul.symm
  calc
    ((nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k))[|
        canonicalCenteredMatchingPrefixEvent k m p x]).real
      ((standardizedCenteredPrefixLogDetAtFullScale m (2 * k) p) ⁻¹'
        (Icc (-(canonicalCenteredPrefixTotalRadius k m p x))
          (canonicalCenteredPrefixTotalRadius k m p x))ᶜ) ≤
        (xi[|s]).real G := by simpa [xi, s, G, R, P] using hmono
    _ = xi.real (s ∩ G) / xi.real s := hcond
    _ = canonicalCenteredGaussianPrefixUncenteredFailureRelative
          k m p x := by
      rfl

/-- Under canonical matching conditioning, the first coordinate of the
bundled prefix--tail law concentrates in the combined shrinking interval. -/
theorem tendsto_canonicalConditionedPrefixTail_first_badMass_zero
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto
      (fun p : ℕ ↦
        (canonicalConditionedPrefixTailJointOrGaussian
          k (mseq p) p x : Measure (ℝ × ℝ)).real
          (((fun y : ℝ × ℝ ↦ y.1) ⁻¹'
            Icc (-(canonicalCenteredPrefixTotalRadius k (mseq p) p x))
              (canonicalCenteredPrefixTotalRadius k (mseq p) p x))ᶜ))
      atTop (nhds 0) := by
  have hupper :=
    tendsto_canonicalCenteredGaussianPrefixUncenteredFailureRelative_zero
      k hk hadm x
  have hs0 := eventually_canonicalCenteredGaussianMatchingEvent_ne_zero
    k hadm x
  apply squeeze_zero'
    (g := fun p : ℕ ↦
      canonicalCenteredGaussianPrefixUncenteredFailureRelative
        k (mseq p) p x)
  · exact Eventually.of_forall fun p ↦ measureReal_nonneg
  · filter_upwards [hadm, hs0, eventually_ge_atTop (2 * k)]
      with p hp hs0p hqp
    let s : Set (NestedTuple (centeredSubspace (mseq p + 1)) (2 * k)) :=
      canonicalCenteredMatchingPrefixEvent k (mseq p) p x
    let hs : MeasurableSet s :=
      measurableSet_canonicalCenteredMatchingPrefixEvent k (mseq p) p x
    let R : ℝ := canonicalCenteredPrefixTotalRadius k (mseq p) p x
    let D : Set ℝ := (Icc (-R) R)ᶜ
    let xi := nestedProductMeasure
      (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)
    have hs0' : xi s ≠ 0 := by
      simpa [xi, s, canonicalCenteredMatchingPrefixEvent] using hs0p
    have hpm : p ≤ mseq p := hp.2
    have hqr : 2 * k + (p - 2 * k) ≤ mseq p := by
      rw [Nat.add_sub_of_le hqp]
      exact hpm
    have hD : MeasurableSet D := measurableSet_Icc.compl
    have hmap := map_fst_centeredGaussianPrefixTailPair_cond
      (mseq p) (2 * k) (p - 2 * k) hqr
      s hs hs0'
    have hmapReal := congrArg (fun mu : Measure ℝ ↦ mu.real D) hmap
    have hfirst :
        (Measure.map Prod.fst
          (Measure.map
            (centeredGaussianPrefixTailPairStatistic
              (mseq p) (2 * k) (p - 2 * k))
            ((conditionedCenteredGaussianPrefixProbabilityMeasure
              (mseq p) (2 * k) (p - 2 * k) hqr
              s hs hs0' : ProbabilityMeasure _) : Measure _))).real D =
          (xi[|s]).real
            ((standardizedCenteredPrefixLogDetAtFullScale
              (mseq p) (2 * k) p) ⁻¹' D) := by
      calc
        _ = (Measure.map
            (standardizedCenteredPrefixLogDetAtFullScale
              (mseq p) (2 * k) p) (xi[|s])).real D := by
              simpa [xi, Nat.add_sub_of_le hqp] using hmapReal
        _ = (xi[|s]).real
            ((standardizedCenteredPrefixLogDetAtFullScale
              (mseq p) (2 * k) p) ⁻¹' D) := by
              rw [measureReal_def,
                Measure.map_apply
                  (measurable_standardizedCenteredPrefixLogDetAtFullScale
                    (mseq p) (2 * k) p) hD,
                ← measureReal_def]
    have hjoint :
        (canonicalConditionedPrefixTailJointOrGaussian
          k (mseq p) p x : Measure (ℝ × ℝ)).real
          (((fun y : ℝ × ℝ ↦ y.1) ⁻¹' Icc (-R) R)ᶜ) =
        (xi[|s]).real
          ((standardizedCenteredPrefixLogDetAtFullScale
            (mseq p) (2 * k) p) ⁻¹' D) := by
      rw [show canonicalConditionedPrefixTailJointOrGaussian
          k (mseq p) p x =
          conditionedPrefixTailJointOrGaussian
            (mseq p) (2 * k) p s hs by rfl]
      rw [conditionedPrefixTailJointOrGaussian_eq_of_valid
        (mseq p) (2 * k) p s hs hqp hpm hs0']
      change
        (Measure.map
          (centeredGaussianPrefixTailPairStatistic
            (mseq p) (2 * k) (p - 2 * k))
          ((conditionedCenteredGaussianPrefixProbabilityMeasure
            (mseq p) (2 * k) (p - 2 * k) hqr
            s hs hs0' : ProbabilityMeasure _) : Measure _)).real
          (((fun y : ℝ × ℝ ↦ y.1) ⁻¹' Icc (-R) R)ᶜ) = _
      rw [show ((fun y : ℝ × ℝ ↦ y.1) ⁻¹' Icc (-R) R)ᶜ =
          Prod.fst ⁻¹' D by
        simp only [D, preimage_compl]]
      calc
        _ = (Measure.map Prod.fst
            (Measure.map
              (centeredGaussianPrefixTailPairStatistic
                (mseq p) (2 * k) (p - 2 * k))
              ((conditionedCenteredGaussianPrefixProbabilityMeasure
                (mseq p) (2 * k) (p - 2 * k) hqr
                s hs hs0' : ProbabilityMeasure _) : Measure _))).real D := by
              have happly := Measure.map_apply
                (μ := Measure.map
                  (centeredGaussianPrefixTailPairStatistic
                    (mseq p) (2 * k) (p - 2 * k))
                  ((conditionedCenteredGaussianPrefixProbabilityMeasure
                    (mseq p) (2 * k) (p - 2 * k) hqr
                    s hs hs0' : ProbabilityMeasure _) : Measure _))
                measurable_fst hD
              have hreal := congrArg ENNReal.toReal happly
              simpa [measureReal_def] using hreal.symm
        _ = _ := hfirst
    rw [show canonicalCenteredPrefixTotalRadius k (mseq p) p x = R by rfl,
      hjoint]
    exact conditionedCenteredPrefix_badMass_le_uncenteredFailureRelative
      k (mseq p) p hp x hs0'
  · exact hupper

/-- Canonical conditional CDF, with the harmless standard-Gaussian fallback
at the finitely many indices where the dimensional conditions need not hold. -/
def canonicalConditionedZ0mpCDFOrGaussian
    (k m p : ℕ) (x z : ℝ) : ℝ :=
  (((canonicalConditionedPrefixTailJointOrGaussian k m p x).map
      (measurable_fst.add measurable_snd).aemeasurable :
        ProbabilityMeasure ℝ) : Measure ℝ).real (Iic z)

/-- At every valid index, the bundled canonical conditional CDF is exactly
the CDF of the actual standardized centered sample-correlation log
determinant under canonical matching conditioning. -/
theorem canonicalConditionedZ0mpCDFOrGaussian_eq_actual
    (k m p : ℕ) (hqp : 2 * k ≤ p) (hpm : p ≤ m)
    (x z : ℝ)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) (2 * k)
      (canonicalCenteredMatchingPrefixEvent k m p x) ≠ 0) :
    canonicalConditionedZ0mpCDFOrGaussian k m p x z =
      (Measure.map (Z0mpStatistic m (2 * k + (p - 2 * k)))
        ((conditionedCenteredGaussianPrefixProbabilityMeasure
          m (2 * k) (p - 2 * k) (by omega)
          (canonicalCenteredMatchingPrefixEvent k m p x)
          (measurableSet_canonicalCenteredMatchingPrefixEvent k m p x)
          hs0 : ProbabilityMeasure _) : Measure _)).real (Iic z) := by
  have h := conditionedPrefixTail_sum_CDF_eq_Z0mp_cond
    m (2 * k) p
    (canonicalCenteredMatchingPrefixEvent k m p x)
    (measurableSet_canonicalCenteredMatchingPrefixEvent k m p x)
    hqp hpm hs0 z
  simpa [canonicalConditionedZ0mpCDFOrGaussian,
    canonicalConditionedPrefixTailJointOrGaussian] using h

/-- **Canonical conditional CLT.**  For every fixed positive matching size,
the conditional CDF of the actual standardized log determinant converges to
the standard normal CDF along every all-gap sequence.  The definition uses a
fallback only before the eventually valid range; the preceding theorem gives
the exact actual conditional law at every valid index. -/
theorem tendsto_canonicalConditionedZ0mpCDFOrGaussian
    (k : ℕ) (hk : 1 ≤ k) {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (x z : ℝ) :
    Tendsto (fun p : ℕ ↦
      canonicalConditionedZ0mpCDFOrGaussian k (mseq p) p x z)
      atTop (nhds (standardNormalCDF z)) := by
  let s : (p : ℕ) →
      Set (NestedTuple (centeredSubspace (mseq p + 1)) (2 * k)) :=
    fun p ↦ canonicalCenteredMatchingPrefixEvent k (mseq p) p x
  let hs : ∀ p, MeasurableSet (s p) := fun p ↦
    measurableSet_canonicalCenteredMatchingPrefixEvent k (mseq p) p x
  have hs0 : ∀ᶠ p in atTop,
      nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) (2 * k)
        (s p) ≠ 0 := by
    simpa [s, canonicalCenteredMatchingPrefixEvent] using
      eventually_canonicalCenteredGaussianMatchingEvent_ne_zero k hadm x
  have hr := eventually_canonicalCenteredPrefixTotalRadius_nonneg
    k hadm x
  have hr0 := tendsto_canonicalCenteredPrefixTotalRadius_zero
    k hk hadm x
  have hbad := tendsto_canonicalConditionedPrefixTail_first_badMass_zero
    k hk hadm x
  have hmain := tendsto_conditionedPrefixTail_sum_CDF
    (2 * k) (by omega) mseq s hs hadm hs0
    (fun p ↦ canonicalCenteredPrefixTotalRadius k (mseq p) p x)
    hr hr0 (by
      simpa [s, hs, canonicalConditionedPrefixTailJointOrGaussian] using hbad)
    z
  simpa [canonicalConditionedZ0mpCDFOrGaussian,
    canonicalConditionedPrefixTailJointOrGaussian, s, hs] using hmain

end

end LogdetLean.Coherence
