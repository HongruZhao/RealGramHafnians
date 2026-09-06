import LogdetLean.Coherence.FiniteUnionNormalPoisson
import LogdetLean.MatrixSphericalExtension
import Mathlib.Tactic
/-!
# Null finite-window theorem in residual Gaussian coordinates

The null point-process development is stated on `m+1` raw centered
observations.  The stable-matching coupling is most naturally stated on `m`
independent residual coordinates.  This file proves that the decorated
finite-window output has exactly the same law in those two presentations.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- Normalized coherence score written on an arbitrary finite family of
residual columns. -/
def residualFamilyPointScore (m p : ℕ) (v : Fin p → E)
    (e : CorrelationEdge p) : ℝ :=
  (m : ℝ) * (normalizedGram v e.1.1 e.1.2) ^ 2 -
    4 * Real.log (p : ℝ) + Real.log (Real.log (p : ℝ))

theorem measurable_residualFamilyPointScore (m p : ℕ)
    (e : CorrelationEdge p) :
    Measurable (fun v : Fin p → E ↦ residualFamilyPointScore m p v e) := by
  unfold residualFamilyPointScore
  have hgram := measurable_normalizedGramFamily (p := p) (E := E)
  have hentry : Measurable (fun v : Fin p → E ↦
      normalizedGram v e.1.1 e.1.2) :=
    (measurable_pi_apply e.1.2).comp
      ((measurable_pi_apply e.1.1).comp hgram)
  exact (((measurable_const.mul (hentry.pow_const 2)).sub
    measurable_const).add measurable_const)

/-- Number of residual-family scores in a finite disjoint window union. -/
def residualFamilyFiniteUnionCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (v : Fin p → E) : ℕ :=
  ∑ e : CorrelationEdge p,
    if residualFamilyPointScore m p v e ∈ finiteScoreWindowUnion W
    then 1 else 0

theorem measurable_residualFamilyFiniteUnionCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) : Measurable (residualFamilyFiniteUnionCount (E := E) W m p) := by
  unfold residualFamilyFiniteUnionCount
  apply Finset.measurable_sum
  intro e _he
  exact Measurable.ite
    ((measurableSet_finiteScoreWindowUnion W).preimage
      (measurable_residualFamilyPointScore m p e))
    measurable_const measurable_const

/-- Standardized null log determinant on residual columns. -/
def residualFamilyZ0 (m p : ℕ) (v : Fin p → E) : ℝ :=
  (Real.log (normalizedGram v).det - nullCenterDigammaSeries m p) /
    Real.sqrt (nullVSeries m p)

theorem measurable_residualFamilyZ0 (m p : ℕ) :
    Measurable (residualFamilyZ0 (E := E) m p) := by
  unfold residualFamilyZ0
  exact (((measurable_det_normalizedGram (E := E) p).log.sub
    measurable_const).div measurable_const)

/-- Decorated scalar output used to transport the null theorem. -/
def residualFamilyDecoratedOutput
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (v : Fin p → E) : ℝ × ℕ :=
  (residualFamilyZ0 m p v, residualFamilyFiniteUnionCount W m p v)

theorem measurable_residualFamilyDecoratedOutput
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) : Measurable (residualFamilyDecoratedOutput (E := E) W m p) := by
  exact (measurable_residualFamilyZ0 m p).prodMk
    (measurable_residualFamilyFiniteUnionCount W m p)

/-- Both determinant and edge scores are unchanged by a columnwise linear
isometry. -/
theorem residualFamilyDecoratedOutput_linearIsometry
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (T : E →ₗᵢ[ℝ] F) (m p : ℕ) (v : Fin p → E) :
    residualFamilyDecoratedOutput (E := F) W m p
        (mapColumnIsometry T v) =
      residualFamilyDecoratedOutput (E := E) W m p v := by
  have hgram := normalizedGram_linearIsometry T v
  have hgram' : normalizedGram (mapColumnIsometry T v) =
      normalizedGram v := by
    change normalizedGram (fun i ↦ T (v i)) = normalizedGram v
    exact hgram
  unfold residualFamilyDecoratedOutput residualFamilyZ0
    residualFamilyFiniteUnionCount residualFamilyPointScore
  rw [hgram']

/-- Centering raw observations and then evaluating the residual-family
output agrees pointwise with the original raw statistic and count. -/
theorem residualFamilyDecoratedOutput_centeredGaussianFamily
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (data : GaussianCorrelationSample m p) :
    residualFamilyDecoratedOutput (E := centeredSubspace (m + 1))
        W m p (centeredGaussianFamily m p data) =
      (Z0mpStatistic m p data,
        coherenceFiniteUnionWindowCount W m p data) := by
  apply Prod.ext
  · change centeredFamilyZ0mpStatistic m p
        (nestedTupleToFin p (centerNested (m + 1) p data)) = _
    exact centeredFamilyZ0mpStatistic_centeredNested m p data
  · change residualFamilyFiniteUnionCount W m p
        (centeredGaussianFamily m p data) =
      coherenceFiniteUnionWindowCount W m p data
    unfold residualFamilyFiniteUnionCount coherenceFiniteUnionWindowCount
    apply Finset.sum_congr rfl
    intro e _he
    have hs := scaledSquaredCorrelationScore_eq_centeredFamily
      m p data e.1.1 e.1.2
    unfold residualFamilyPointScore coherencePointScore
    rw [normalizedGram_apply_sq_eq_squaredNormalizedInner_total, hs]

/-- Exact law identity between the raw centered presentation and the
`m`-dimensional residual-coordinate presentation. -/
theorem map_residualFamilyDecoratedOutput_eq_raw
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) :
    Measure.map
        (residualFamilyDecoratedOutput
          (E := ObservationSpace m) W m p)
        (Measure.pi fun _ : Fin p ↦ stdGaussian (ObservationSpace m)) =
      Measure.map
        (fun data : GaussianCorrelationSample m p ↦
          (Z0mpStatistic m p data,
            coherenceFiniteUnionWindowCount W m p data))
        (gaussianCorrelationMeasure m p) := by
  let T := centeredCoordinateIsometry m
  let FC := residualFamilyDecoratedOutput
    (E := centeredSubspace (m + 1)) W m p
  let FE := residualFamilyDecoratedOutput
    (E := ObservationSpace m) W m p
  let raw := fun data : GaussianCorrelationSample m p ↦
    (Z0mpStatistic m p data, coherenceFiniteUnionWindowCount W m p data)
  have hFC : Measurable FC := measurable_residualFamilyDecoratedOutput W m p
  have hFE : Measurable FE := measurable_residualFamilyDecoratedOutput W m p
  have hT : Measurable
      (mapColumnIsometry (p := p) T.toLinearIsometry) :=
    measurable_mapColumnIsometry T.toLinearIsometry
  have hcenter : Measurable (centeredGaussianFamily m p) :=
    measurable_centeredGaussianFamily m p
  calc
    Measure.map FE
        (Measure.pi fun _ : Fin p ↦ stdGaussian (ObservationSpace m)) =
      Measure.map FE
        (Measure.map (mapColumnIsometry (p := p) T.toLinearIsometry)
          (Measure.pi fun _ : Fin p ↦
            stdGaussian (centeredSubspace (m + 1)))) := by
          rw [map_mapColumnIsometry_pi_stdGaussian T]
    _ = Measure.map (FE ∘
          mapColumnIsometry (p := p) T.toLinearIsometry)
        (Measure.pi fun _ : Fin p ↦
          stdGaussian (centeredSubspace (m + 1))) := by
          rw [Measure.map_map hFE hT]
    _ = Measure.map FC
        (Measure.pi fun _ : Fin p ↦
          stdGaussian (centeredSubspace (m + 1))) := by
          apply Measure.map_congr
          filter_upwards with v
          exact residualFamilyDecoratedOutput_linearIsometry
            W T.toLinearIsometry m p v
    _ = Measure.map FC
        (Measure.map (centeredGaussianFamily m p)
          (gaussianCorrelationMeasure m p)) := by
          rw [map_centeredGaussianFamily_eq_pi]
    _ = Measure.map (FC ∘ centeredGaussianFamily m p)
        (gaussianCorrelationMeasure m p) := by
          rw [Measure.map_map hFC hcenter]
    _ = Measure.map raw (gaussianCorrelationMeasure m p) := by
          apply Measure.map_congr
          filter_upwards with data
          exact residualFamilyDecoratedOutput_centeredGaussianFamily
            W m p data

/-- Joint exact-count probability under residual iid Gaussian columns. -/
def residualGaussianFiniteUnionJointExactCountProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) (z : ℝ) : ℝ :=
  (Measure.map
      (residualFamilyDecoratedOutput
        (E := ObservationSpace m) W m p)
      (Measure.pi fun _ : Fin p ↦ stdGaussian (ObservationSpace m))).real
    (Set.Iic z ×ˢ ({r} : Set ℕ))

theorem residualGaussianFiniteUnionJointExactCountProbability_eq_raw
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p r : ℕ) (z : ℝ) :
    residualGaussianFiniteUnionJointExactCountProbability W m p r z =
      gaussianCoherenceFiniteUnionJointExactCountProbability W m p r z := by
  rw [residualGaussianFiniteUnionJointExactCountProbability,
    map_residualFamilyDecoratedOutput_eq_raw]
  rw [gaussianCoherenceFiniteUnionJointExactCountProbability_eq_measureReal]
  rw [Measure.real, Measure.map_apply]
  · congr 1
  · exact (measurable_Z0mpStatistic m p).prodMk
      (measurable_coherenceFiniteUnionWindowCount W m p)
  · exact measurableSet_Iic.prod (measurableSet_singleton r)

/-- Residual-coordinate form of the all-gap decorated exact-count theorem. -/
theorem tendsto_residualGaussianFiniteUnionJointExactCountProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (r : ℕ) (c : ℝ) (hc : ∀ i, c ≤ W.lower i)
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hnu : 0 < finiteUnionClassicalCoherenceIntensity W) (z : ℝ) :
    Tendsto
      (fun p ↦ residualGaussianFiniteUnionJointExactCountProbability
        W (mseq p) p r z)
      atTop
      (nhds (standardNormalCDF z *
        poissonExactMass (finiteUnionClassicalCoherenceIntensity W) r)) := by
  apply (tendsto_gaussianCoherenceFiniteUnionJointExactCountProbability
    W r c hc hadm hnu z).congr'
  filter_upwards with p
  exact (residualGaussianFiniteUnionJointExactCountProbability_eq_raw
    W (mseq p) p r z).symm

end

end LogdetLean.Coherence
