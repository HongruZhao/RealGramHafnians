import LogdetLean.Coherence.StableMatchingPlantedFrameProduct
import LogdetLean.Coherence.ResidualFiniteUnionNormalPoisson
import Mathlib.Tactic
/-!
# Clean background edges and exact planted separation

The clean background consists of edges between singleton population blocks.
Its scores retain the ambient `p` normalization.  Together with the frame
log determinant it is a measurable function of the frame data and is exactly
independent of every planted-block Ruben coordinate.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators RealInnerProductSpace

attribute [local instance] Classical.propDecidable

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Ambient-normalized score of an edge among the `r` clean singleton
columns. -/
def stableMatchingCleanPointScore (m p : ℕ) (v : Fin r → E)
    (e : CorrelationEdge r) : ℝ :=
  (m : ℝ) * (normalizedGram v e.1.1 e.1.2) ^ 2 -
    4 * Real.log (p : ℝ) + Real.log (Real.log (p : ℝ))

theorem measurable_stableMatchingCleanPointScore (m p : ℕ)
    (e : CorrelationEdge r) :
    Measurable (fun v : Fin r → E ↦ stableMatchingCleanPointScore m p v e) := by
  unfold stableMatchingCleanPointScore
  have hgram := measurable_normalizedGramFamily (p := r) (E := E)
  have hentry : Measurable (fun v : Fin r → E ↦
      normalizedGram v e.1.1 e.1.2) :=
    (measurable_pi_apply e.1.2).comp
      ((measurable_pi_apply e.1.1).comp hgram)
  exact (((measurable_const.mul (hentry.pow_const 2)).sub
    measurable_const).add measurable_const)

/-- Number of clean singleton--singleton scores in the finite window union. -/
def stableMatchingCleanFiniteUnionCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) (v : Fin r → E) : ℕ :=
  ∑ e : CorrelationEdge r,
    if stableMatchingCleanPointScore m p v e ∈ finiteScoreWindowUnion W
    then 1 else 0

theorem measurable_stableMatchingCleanFiniteUnionCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) :
    Measurable (stableMatchingCleanFiniteUnionCount (E := E) W m p r) := by
  unfold stableMatchingCleanFiniteUnionCount
  apply Finset.measurable_sum
  intro e _he
  exact Measurable.ite
    ((measurableSet_finiteScoreWindowUnion W).preimage
      (measurable_stableMatchingCleanPointScore m p e))
    measurable_const measurable_const

/-- Frame standardized coordinate evaluated directly on abstract frame data. -/
def stableMatchingFrameZ0FromData (m s r : ℕ)
    (d : (Fin s → E × E) × (Fin r → E)) : ℝ :=
  (Real.log (normalizedGram (stableMatchingFrameColumns s r d)).det -
      nullCenter m (2 * s + r) -
      (s : ℝ) * oneEdgeLogMean (1 / 2)
        (((m - 1 : ℕ) : ℝ) / 2)) /
    Real.sqrt (nullVSeries m (2 * s + r))

theorem measurable_stableMatchingFrameZ0FromData (m s r : ℕ) :
    Measurable (stableMatchingFrameZ0FromData (E := E) m s r) := by
  unfold stableMatchingFrameZ0FromData
  exact (((((measurable_det_normalizedGram_stableMatchingIndex
    (E := E) s r).comp (measurable_stableMatchingFrameColumns s r)).log).sub
      measurable_const).sub measurable_const).div measurable_const

theorem stableMatchingFrameZ0FromData_frameData
    (m s r : ℕ) (w : StableMatchingBaseSample E s r) :
    stableMatchingFrameZ0FromData m s r (stableMatchingFrameData s r w) =
      stableMatchingFrameZ0 m s r w := by
  rfl

/-- The frame coordinate and clean background count, as one function of the
frame data. -/
def stableMatchingCleanFrameOutput
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s r : ℕ) (d : (Fin s → E × E) × (Fin r → E)) : ℝ × ℕ :=
  (stableMatchingFrameZ0FromData m s r d,
    stableMatchingCleanFiniteUnionCount W m p r d.2)

theorem measurable_stableMatchingCleanFrameOutput
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s r : ℕ) :
    Measurable (stableMatchingCleanFrameOutput (E := E) W m p s r) := by
  exact (measurable_stableMatchingFrameZ0FromData m s r).prodMk
    ((measurable_stableMatchingCleanFiniteUnionCount W m p r).comp measurable_snd)

theorem indepFun_stableMatchingCleanFrameOutput_rubenData
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s r : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun
      (stableMatchingCleanFrameOutput (E := E) W m p s r ∘
        stableMatchingFrameData (E := E) s r)
      (stableMatchingRubenData (E := E) s r)
      (stableMatchingBaseMeasure E s r) := by
  exact (indepFun_stableMatchingFrameData_rubenData
    (E := E) s r m hdim hm).comp
      (measurable_stableMatchingCleanFrameOutput W m p s r) measurable_id

/-- Exact product of the clean decorated event and the planted Ruben void. -/
theorem measureReal_cleanFrameEvent_inter_rubenPlantedVoid_eq_mul
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p s r count : ℕ} (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m)
    (rho z : ℝ) :
    (stableMatchingBaseMeasure E s r).real
      (((stableMatchingCleanFrameOutput (E := E) W m p s r ∘
          stableMatchingFrameData (E := E) s r) ⁻¹'
            (Set.Iic z ×ˢ ({count} : Set ℕ))) ∩
        (stableMatchingRubenData (E := E) s r ⁻¹'
          plantedRubenFiniteUnionVoid W m p s rho)) =
      (stableMatchingBaseMeasure E s r).real
          ((stableMatchingCleanFrameOutput (E := E) W m p s r ∘
            stableMatchingFrameData (E := E) s r) ⁻¹'
              (Set.Iic z ×ˢ ({count} : Set ℕ))) *
        (stableMatchingBaseMeasure E s r).real
          (stableMatchingRubenData (E := E) s r ⁻¹'
            plantedRubenFiniteUnionVoid W m p s rho) := by
  have h := (indepFun_stableMatchingCleanFrameOutput_rubenData
    (E := E) W m p s r hdim hm).measure_inter_preimage_eq_mul
      (Set.Iic z ×ˢ ({count} : Set ℕ))
      (plantedRubenFiniteUnionVoid W m p s rho)
      (measurableSet_Iic.prod (measurableSet_singleton count))
      (measurableSet_plantedRubenFiniteUnionVoid W m p s rho)
  change ((stableMatchingBaseMeasure E s r)
      (((stableMatchingCleanFrameOutput (E := E) W m p s r ∘
          stableMatchingFrameData (E := E) s r) ⁻¹'
            (Set.Iic z ×ˢ ({count} : Set ℕ))) ∩
        (stableMatchingRubenData (E := E) s r ⁻¹'
          plantedRubenFiniteUnionVoid W m p s rho))).toReal = _
  rw [h, ENNReal.toReal_mul]
  rfl

end

end LogdetLean.Coherence
