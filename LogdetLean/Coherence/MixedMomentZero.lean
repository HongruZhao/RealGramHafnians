import LogdetLean.Coherence.ModelAndTargets
import LogdetLean.Coherence.WeakCDF
import LogdetLean.NullWeakCLT
/-!
# The zeroth mixed factorial moment

The central mixed factorial-moment theorem includes `k = 0`.  At that
index the descending factorial is identically one, so the mixed moment is
exactly the lower-tail probability of the standardized log determinant.
This module records that exact identity and obtains its all-gap limit from
the already proved null CLT.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

/-- At order zero, the coherence mixed factorial moment is exactly the CDF
of the actual standardized Gaussian log-determinant statistic. -/
theorem gaussianCoherenceMixedFactorialMoment_zero_eq_map_Iic
    (m p : ℕ) (z x : ℝ) :
    gaussianCoherenceMixedFactorialMoment m p 0 z x =
      (Measure.map (Z0mpStatistic m p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p)).real (Iic z) := by
  unfold gaussianCoherenceMixedFactorialMoment thresholdMixedFactorialMoment
  simp only [Nat.descFactorial_zero, Nat.cast_one]
  let A : Set (NestedTuple (ObservationSpace (m + 1)) p) :=
    {data | Z0mpStatistic m p data ≤ z}
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_Z0mpStatistic m p) measurable_const
  calc
    (∫ data : NestedTuple (ObservationSpace (m + 1)) p,
        if Z0mpStatistic m p data ≤ z then (1 : ℝ) else 0
      ∂nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) =
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p).real A := by
      have hindicator :
          (fun data : NestedTuple (ObservationSpace (m + 1)) p ↦
            if Z0mpStatistic m p data ≤ z then (1 : ℝ) else 0) =
          A.indicator (fun _ ↦ (1 : ℝ)) := by
        funext data
        by_cases h : Z0mpStatistic m p data ≤ z
        · simp [A, h]
        · simp [A, h]
      rw [hindicator]
      exact integral_indicator_one hA
    _ = (Measure.map (Z0mpStatistic m p)
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) p)).real (Iic z) := by
      have hmap :
          Measure.map (Z0mpStatistic m p)
              (nestedProductMeasure
                (stdGaussian (ObservationSpace (m + 1))) p) (Iic z) =
            nestedProductMeasure
              (stdGaussian (ObservationSpace (m + 1))) p
              ((Z0mpStatistic m p) ⁻¹' Iic z) :=
        Measure.map_apply (measurable_Z0mpStatistic m p) measurableSet_Iic
      have hreal := congrArg ENNReal.toReal hmap
      have hpre : (Z0mpStatistic m p) ⁻¹' Iic z = A := by
        ext data
        simp [A]
      simpa [Measure.real, hpre] using hreal.symm

/-- The order-zero mixed moment has the standard-normal limit along every
eventually admissible all-gap sequence. -/
theorem tendsto_gaussianCoherenceMixedFactorialMoment_zero
    (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (z x : ℝ) :
    Tendsto
      (fun p ↦ gaussianCoherenceMixedFactorialMoment
        (mseq p) p 0 z x)
      atTop (nhds (standardNormalCDF z)) := by
  have hweak := tendsto_actual_Z0mp_gaussian mseq hadm
  have hcdf := tendsto_measureReal_Iic_standardGaussian_of_weak hweak z
  apply hcdf.congr'
  filter_upwards [hadm] with p hp
  rw [gaussianCoherenceMixedFactorialMoment_zero_eq_map_Iic]
  change
    (actualZ0mpMeasureOrGaussian (mseq p) p).real (Iic z) =
      (Measure.map (Z0mpStatistic (mseq p) p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (mseq p + 1))) p)).real (Iic z)
  unfold actualZ0mpMeasureOrGaussian
  rw [if_pos hp]

end

end LogdetLean.Coherence
