import LogdetLean.Coherence.ConditionedJointLaw
import LogdetLean.Coherence.VaryingSpaceSlutsky
import LogdetLean.Coherence.FiniteDeletionCLT
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
/-!
# Conditional prefix CLT with finite-index fallback

For asymptotic statements, the dimensional inequalities and positivity of
the matching event hold only eventually.  This module bundles the genuine
conditional prefix--tail pair law at valid indices and uses the harmless law
`δ₀ ⊗ N(0,1)` before those conditions hold.  The resulting object is a
probability measure for every natural index and is therefore convenient for
weak-convergence statements.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

/-- Harmless fallback joint law: a deterministic zero perturbation and a
standard Gaussian tail. -/
def zeroGaussianPairProbabilityMeasure : ProbabilityMeasure (ℝ × ℝ) :=
  (diracProba (0 : ℝ)).prod
    (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)

/-- The genuine conditional prefix--tail pair law whenever `q ≤ p ≤ m` and
the prefix event has positive probability; otherwise the fallback law. -/
def conditionedPrefixTailJointOrGaussian
    (m q p : ℕ)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s) : ProbabilityMeasure (ℝ × ℝ) := by
  classical
  if hqp : q ≤ p then
    if hpm : p ≤ m then
      if hs0 : nestedProductMeasure
          (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0 then
        let r := p - q
        have hqr : q + r ≤ m := by omega
        exact (conditionedCenteredGaussianPrefixProbabilityMeasure
          m q r hqr s hs hs0).map
            (measurable_centeredGaussianPrefixTailPairStatistic
              m q r).aemeasurable
      else
        exact zeroGaussianPairProbabilityMeasure
    else
      exact zeroGaussianPairProbabilityMeasure
  else
    exact zeroGaussianPairProbabilityMeasure

theorem conditionedPrefixTailJointOrGaussian_eq_of_valid
    (m q p : ℕ)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s)
    (hqp : q ≤ p) (hpm : p ≤ m)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    conditionedPrefixTailJointOrGaussian m q p s hs =
      (conditionedCenteredGaussianPrefixProbabilityMeasure
        m q (p - q) (by omega) s hs hs0).map
          (measurable_centeredGaussianPrefixTailPairStatistic
            m q (p - q)).aemeasurable := by
  classical
  unfold conditionedPrefixTailJointOrGaussian
  rw [dif_pos hqp, dif_pos hpm, dif_pos hs0]

/-- At every valid index, the second marginal of the bundled joint law is
the exact standardized deleted-tail law. -/
theorem map_snd_conditionedPrefixTailJointOrGaussian_eq_deletedTail
    (m q p : ℕ) (hq : 1 ≤ q)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s)
    (hqp : q ≤ p) (hpm : p ≤ m)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0) :
    Measure.map Prod.snd
        (conditionedPrefixTailJointOrGaussian m q p s hs :
          Measure (ℝ × ℝ)) =
      standardizedDeletedTailLaw m q p := by
  rw [conditionedPrefixTailJointOrGaussian_eq_of_valid
    m q p s hs hqp hpm hs0]
  change Measure.map Prod.snd
      (Measure.map (centeredGaussianPrefixTailPairStatistic m q (p - q))
        ((conditionedCenteredGaussianPrefixProbabilityMeasure
          m q (p - q) (by omega) s hs hs0 : ProbabilityMeasure _) :
            Measure _)) = _
  have hmap := map_snd_centeredGaussianPrefixTailPair_cond
    m q (p - q) hq (by omega) s hs hs0
  simpa [Nat.add_sub_of_le hqp] using hmap

/-- The second marginal of the bundled law has the all-gap Gaussian limit
for any measurable positive prefix events eventually. -/
theorem tendsto_map_snd_conditionedPrefixTailJointOrGaussian
    (q : ℕ) (hq : 2 ≤ q) (mseq : ℕ → ℕ)
    (s : (p : ℕ) →
      Set (NestedTuple (centeredSubspace (mseq p + 1)) q))
    (hs : ∀ p, MeasurableSet (s p))
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hs0 : ∀ᶠ p in atTop,
      nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) q (s p) ≠ 0) :
    Tendsto
      (fun p ↦ (conditionedPrefixTailJointOrGaussian
        (mseq p) q p (s p) (hs p)).map measurable_snd.aemeasurable)
      atTop
      (nhds (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have htail :=
    tendsto_standardizedDeletedTailProbabilityMeasureOrGaussian
      q hq mseq hadm
  apply htail.congr'
  filter_upwards [hadm, hs0, eventually_ge_atTop q] with p hp hs0p hqp
  apply Subtype.ext
  symm
  change Measure.map Prod.snd
      (conditionedPrefixTailJointOrGaussian
        (mseq p) q p (s p) (hs p) : Measure (ℝ × ℝ)) =
    standardizedDeletedTailMeasureOrGaussian (mseq p) q p
  rw [map_snd_conditionedPrefixTailJointOrGaussian_eq_deletedTail
    (mseq p) q p (by omega) (s p) (hs p) hqp hp.2 hs0p]
  rw [standardizedDeletedTailMeasureOrGaussian,
    if_pos ⟨hq, hqp, hp.2⟩]

/-- Abstract conditional Gaussian CDF limit.  The only model-specific input
left is the displayed shrinking-interval control of the first marginal. -/
theorem tendsto_conditionedPrefixTail_sum_CDF
    (q : ℕ) (hq : 2 ≤ q) (mseq : ℕ → ℕ)
    (s : (p : ℕ) →
      Set (NestedTuple (centeredSubspace (mseq p + 1)) q))
    (hs : ∀ p, MeasurableSet (s p))
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hs0 : ∀ᶠ p in atTop,
      nestedProductMeasure
        (stdGaussian (centeredSubspace (mseq p + 1))) q (s p) ≠ 0)
    (radius : ℕ → ℝ)
    (hr : ∀ᶠ p in atTop, 0 ≤ radius p)
    (hr0 : Tendsto radius atTop (nhds 0))
    (hbad : Tendsto
      (fun p ↦
        (conditionedPrefixTailJointOrGaussian
          (mseq p) q p (s p) (hs p) : Measure (ℝ × ℝ)).real
          (((fun x : ℝ × ℝ ↦ x.1) ⁻¹'
            Icc (-(radius p)) (radius p))ᶜ))
      atTop (nhds 0))
    (z : ℝ) :
    Tendsto
      (fun p ↦
        (((conditionedPrefixTailJointOrGaussian
            (mseq p) q p (s p) (hs p)).map
              (measurable_fst.add measurable_snd).aemeasurable :
                ProbabilityMeasure ℝ) : Measure ℝ).real (Iic z))
      atTop (nhds (standardNormalCDF z)) := by
  apply tendsto_map_add_CDF_of_first_shrinks
    (fun p ↦ conditionedPrefixTailJointOrGaussian
      (mseq p) q p (s p) (hs p)) radius hr hr0 hbad
  exact tendsto_map_snd_conditionedPrefixTailJointOrGaussian
    q hq mseq s hs hadm hs0

/-- At a valid index, the sum CDF of the bundled pair is exactly the
conditional CDF of the actual standardized log determinant. -/
theorem conditionedPrefixTail_sum_CDF_eq_Z0mp_cond
    (m q p : ℕ)
    (s : Set (NestedTuple (centeredSubspace (m + 1)) q))
    (hs : MeasurableSet s)
    (hqp : q ≤ p) (hpm : p ≤ m)
    (hs0 : nestedProductMeasure
      (stdGaussian (centeredSubspace (m + 1))) q s ≠ 0)
    (z : ℝ) :
    (((conditionedPrefixTailJointOrGaussian m q p s hs).map
        (measurable_fst.add measurable_snd).aemeasurable :
          ProbabilityMeasure ℝ) : Measure ℝ).real (Iic z) =
      (Measure.map (Z0mpStatistic m (q + (p - q)))
        ((conditionedCenteredGaussianPrefixProbabilityMeasure
          m q (p - q) (by omega) s hs hs0 : ProbabilityMeasure _) :
            Measure _)).real (Iic z) := by
  rw [conditionedPrefixTailJointOrGaussian_eq_of_valid
    m q p s hs hqp hpm hs0]
  change (Measure.map (fun x : ℝ × ℝ ↦ x.1 + x.2)
      (Measure.map (centeredGaussianPrefixTailPairStatistic m q (p - q))
        ((conditionedCenteredGaussianPrefixProbabilityMeasure
          m q (p - q) (by omega) s hs hs0 : ProbabilityMeasure _) :
            Measure _))).real (Iic z) = _
  rw [map_add_centeredGaussianPrefixTailPair_cond_eq_map_Z0mp]

end

end LogdetLean.Coherence
