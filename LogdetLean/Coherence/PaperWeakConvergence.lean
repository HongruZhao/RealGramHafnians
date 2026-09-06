import LogdetLean.Coherence.RectangleCDFToWeak
import LogdetLean.Coherence.StandardGumbelCoordinate
import LogdetLean.Coherence.FisherMapping
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
/-!
# Weak convergence form of the paper's joint limit

The main paper proves convergence of all lower rectangle probabilities.  This
file constructs the standard Gumbel probability measure and applies the
convergence determining class theorem from `RectangleCDFToWeak` to obtain
weak convergence of the pair.  No statistical assumption beyond the paper's
admissibility condition is introduced.
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

/-- Lebesgue probability measure restricted to the open unit interval. -/
def openUnitUniformMeasure : Measure ℝ :=
  volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure openUnitUniformMeasure := by
  refine ⟨?_⟩
  simp [openUnitUniformMeasure, Real.volume_Ioo]

/-- The usual quantile representation of a standard Gumbel random variable. -/
def standardGumbelQuantile (u : ℝ) : ℝ :=
  -Real.log (-Real.log u)

theorem measurable_standardGumbelQuantile : Measurable standardGumbelQuantile := by
  unfold standardGumbelQuantile
  fun_prop

/-- The standard Gumbel law, constructed as the image of an open unit
uniform law under its quantile function. -/
def standardGumbelMeasure : Measure ℝ :=
  Measure.map standardGumbelQuantile openUnitUniformMeasure

instance : IsProbabilityMeasure standardGumbelMeasure := by
  unfold standardGumbelMeasure
  exact Measure.isProbabilityMeasure_map
    measurable_standardGumbelQuantile.aemeasurable

/-- On the open unit interval, the standard Gumbel quantile has the expected
lower level sets. -/
theorem standardGumbelQuantile_le_iff
    {u x : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    standardGumbelQuantile u ≤ x ↔
      u ≤ Real.exp (-Real.exp (-x)) := by
  have hL : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu0 hu1)
  have hc0 : 0 < Real.exp (-Real.exp (-x)) := Real.exp_pos _
  constructor
  · intro hq
    have hlog : -x ≤ Real.log (-Real.log u) := by
      unfold standardGumbelQuantile at hq
      linarith
    have hexp : Real.exp (-x) ≤ -Real.log u :=
      (Real.le_log_iff_exp_le hL).mp hlog
    have hlu : Real.log u ≤ -Real.exp (-x) := by linarith
    have hlu' : Real.log u ≤ Real.log (Real.exp (-Real.exp (-x))) := by
      simpa only [Real.log_exp] using hlu
    exact (Real.log_le_log_iff hu0 hc0).mp hlu'
  · intro hu
    have hlu' : Real.log u ≤ Real.log (Real.exp (-Real.exp (-x))) :=
      (Real.log_le_log_iff hu0 hc0).mpr hu
    have hlu : Real.log u ≤ -Real.exp (-x) := by
      simpa only [Real.log_exp] using hlu'
    have hexp : Real.exp (-x) ≤ -Real.log u := by linarith
    have hlog : -x ≤ Real.log (-Real.log u) :=
      (Real.le_log_iff_exp_le hL).mpr hexp
    unfold standardGumbelQuantile
    linarith

/-- Exact standard Gumbel distribution function. -/
theorem standardGumbelMeasure_Iic (x : ℝ) :
    standardGumbelMeasure (Iic x) =
      ENNReal.ofReal (Real.exp (-Real.exp (-x))) := by
  have hc0 : 0 < Real.exp (-Real.exp (-x)) := Real.exp_pos _
  have hc1 : Real.exp (-Real.exp (-x)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (Real.exp_pos (-x))
  unfold standardGumbelMeasure openUnitUniformMeasure
  rw [Measure.map_apply measurable_standardGumbelQuantile measurableSet_Iic]
  rw [Measure.restrict_apply
    (measurableSet_Iic.preimage measurable_standardGumbelQuantile)]
  have hset :
      standardGumbelQuantile ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 =
        Ioc 0 (Real.exp (-Real.exp (-x))) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨hq, hu0, hu1⟩
      exact ⟨hu0, (standardGumbelQuantile_le_iff hu0 hu1).mp hq⟩
    · rintro ⟨hu0, huc⟩
      have hu1 : u < 1 := huc.trans_lt hc1
      exact ⟨(standardGumbelQuantile_le_iff hu0 hu1).mpr huc, hu0, hu1⟩
  rw [hset, Real.volume_Ioc]
  simp only [sub_zero]

/-- Real valued form of the exact standard Gumbel distribution function. -/
theorem standardGumbelMeasure_real_Iic (x : ℝ) :
    standardGumbelMeasure.real (Iic x) = Real.exp (-Real.exp (-x)) := by
  rw [Measure.real, standardGumbelMeasure_Iic]
  exact ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-- Standard normal probability measure, bundled for weak convergence. -/
def standardNormalProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- Standard Gumbel probability measure, bundled for weak convergence. -/
def standardGumbelProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨standardGumbelMeasure, inferInstance⟩

/-- Product of independent standard normal and standard Gumbel laws. -/
def normalGumbelProductProbabilityMeasure : ProbabilityMeasure (ℝ × ℝ) :=
  standardNormalProbabilityMeasure.prod standardGumbelProbabilityMeasure

/-- The lower rectangle probabilities of the bundled product law are exactly
the product of the standard normal and standard Gumbel distribution
functions. -/
theorem normalGumbelProductProbabilityMeasure_real_Iic_prod_Iic
    (z t : ℝ) :
    (normalGumbelProductProbabilityMeasure : Measure (ℝ × ℝ)).real
        (Iic z ×ˢ Iic t) =
      standardNormalCDF z * Real.exp (-Real.exp (-t)) := by
  unfold normalGumbelProductProbabilityMeasure
    standardNormalProbabilityMeasure standardGumbelProbabilityMeasure
  change (Measure.prod (gaussianReal 0 1) standardGumbelMeasure).real
      (Iic z ×ˢ Iic t) = _
  rw [MeasureTheory.measureReal_prod_prod]
  rw [← ProbabilityTheory.cdf_eq_real]
  rw [standardGumbelMeasure_real_Iic]
  rfl

/-- Law of the paper's standardized log determinant and standard Gumbel
coherence coordinate at fixed `m,p`. -/
def gaussianGumbelPairLaw (m p : ℕ) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨Measure.map
      (fun data ↦
        (Z0mpStatistic m p data, standardGumbelCoordinate m p data))
      (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p),
    Measure.isProbabilityMeasure_map
      ((measurable_Z0mpStatistic m p).prodMk
        (by
          unfold standardGumbelCoordinate
          exact ((measurable_coherenceExtreme m p).div_const 2).add
            measurable_const)).aemeasurable⟩

theorem measurable_gaussianGumbelPair (m p : ℕ) :
    Measurable (fun data ↦
      (Z0mpStatistic m p data, standardGumbelCoordinate m p data)) := by
  apply (measurable_Z0mpStatistic m p).prodMk
  unfold standardGumbelCoordinate
  exact ((measurable_coherenceExtreme m p).div_const 2).add measurable_const

/-- A lower rectangle under the pair law is the joint lower probability used
in the paper. -/
theorem gaussianGumbelPairLaw_real_Iic_prod_Iic
    (m p : ℕ) (z t : ℝ) :
    (gaussianGumbelPairLaw m p : Measure (ℝ × ℝ)).real
        (Iic z ×ˢ Iic t) =
      gaussianGumbelJointLowerProbability m p z t := by
  unfold gaussianGumbelPairLaw gaussianGumbelJointLowerProbability
  change (Measure.map
      (fun data ↦
        (Z0mpStatistic m p data, standardGumbelCoordinate m p data))
      (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p)).real
      (Iic z ×ˢ Iic t) = _
  unfold Measure.real
  rw [Measure.map_apply (measurable_gaussianGumbelPair m p)
    (measurableSet_Iic.prod measurableSet_Iic)]
  congr 2

/-- The paper's lower rectangle joint limit, converted without additional
assumptions into weak convergence of the pair law. -/
theorem tendsto_gaussianGumbelPairLaw
    (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p ↦ gaussianGumbelPairLaw (mseq p) p) atTop
      (nhds normalGumbelProductProbabilityMeasure) := by
  apply tendsto_probabilityMeasure_of_tendsto_lowerLeftRectangle
  intro z t
  rw [normalGumbelProductProbabilityMeasure_real_Iic_prod_Iic]
  simpa only [gaussianGumbelPairLaw_real_Iic_prod_Iic] using
    allGapGaussianStandardGumbelJointLimit mseq hadm z t

/-- Random variable form of the weak joint convergence theorem. -/
theorem tendstoInDistribution_gaussianGumbelPair
    (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    TendstoInDistribution
      (fun p data ↦
        (Z0mpStatistic (mseq p) p data,
          standardGumbelCoordinate (mseq p) p data))
      atTop (fun y : ℝ × ℝ ↦ y)
      (fun p ↦ nestedProductMeasure
        (stdGaussian (ObservationSpace (mseq p + 1))) p)
      (normalGumbelProductProbabilityMeasure : Measure (ℝ × ℝ)) := by
  refine ⟨fun p ↦ (measurable_gaussianGumbelPair (mseq p) p).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  let targetMap : ProbabilityMeasure (ℝ × ℝ) :=
    ⟨Measure.map (fun y : ℝ × ℝ ↦ y)
      (normalGumbelProductProbabilityMeasure : Measure (ℝ × ℝ)),
      Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩
  have htarget : targetMap = normalGumbelProductProbabilityMeasure := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [targetMap]
  have hseq :
      (fun n ↦
        (⟨Measure.map
          (fun data ↦
            (Z0mpStatistic (mseq n) n data,
              standardGumbelCoordinate (mseq n) n data))
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (mseq n + 1))) n),
          Measure.isProbabilityMeasure_map
            (measurable_gaussianGumbelPair (mseq n) n).aemeasurable⟩ :
          ProbabilityMeasure (ℝ × ℝ))) =
        (fun n ↦ gaussianGumbelPairLaw (mseq n) n) := by
    funext n
    rfl
  change Tendsto _ atTop (nhds targetMap)
  rw [hseq, htarget]
  exact tendsto_gaussianGumbelPairLaw mseq hadm

end

end LogdetLean.Coherence
