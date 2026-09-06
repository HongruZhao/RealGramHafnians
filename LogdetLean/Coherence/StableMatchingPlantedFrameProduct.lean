import LogdetLean.Coherence.StableMatchingPlantedFiniteUnion
import LogdetLean.Coherence.StableMatchingLogdetDecomposition
import Mathlib.Tactic
/-!
# Exact frame/planted-event separation

The frame coordinate is independent of the complete Ruben coordinate array.
This file expresses the planted finite-window event as a measurable function
of that array and obtains the exact finite-sample product formula used by the
stable-matching joint theorem.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators RealInnerProductSpace

attribute [local instance] Classical.propDecidable

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Pearson height written directly in Ruben coordinates. -/
def plantedRubenHeight (m p : ℕ) (rho : ℝ)
    (u : ℝ × (ℝ × ℝ)) : ℝ :=
  (m : ℝ) * squaredRubenCoordinateStatistic m rho u /
      (((m : ℝ) - 1) + squaredRubenCoordinateStatistic m rho u) -
    classicalCoherenceThreshold m p 0

theorem measurable_plantedRubenHeight (m p : ℕ) (rho : ℝ) :
    Measurable (plantedRubenHeight m p rho) := by
  unfold plantedRubenHeight
  exact ((measurable_const.mul
    (measurable_squaredRubenCoordinateStatistic m rho)).div
      (measurable_const.add
        (measurable_squaredRubenCoordinateStatistic m rho))).sub
          measurable_const

/-- Every planted block avoids the prescribed score union, expressed only
through the complete Ruben coordinate array. -/
def plantedRubenFiniteUnionCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s : ℕ) (rho : ℝ) (u : Fin s → ℝ × (ℝ × ℝ)) : ℕ :=
  ∑ e, if plantedRubenHeight m p rho (u e) ∈ finiteScoreWindowUnion W
    then 1 else 0

theorem measurable_plantedRubenFiniteUnionCount
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s : ℕ) (rho : ℝ) :
    Measurable (plantedRubenFiniteUnionCount W m p s rho) := by
  unfold plantedRubenFiniteUnionCount
  apply Finset.measurable_sum
  intro e _he
  exact Measurable.ite
    ((measurableSet_finiteScoreWindowUnion W).preimage
      ((measurable_plantedRubenHeight m p rho).comp
        (measurable_pi_apply e : Measurable
          (fun u : Fin s → ℝ × (ℝ × ℝ) ↦ u e))))
    measurable_const measurable_const

def plantedRubenFiniteUnionVoid
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s : ℕ) (rho : ℝ) : Set (Fin s → ℝ × (ℝ × ℝ)) :=
  plantedRubenFiniteUnionCount W m p s rho ⁻¹' {0}

theorem measurableSet_plantedRubenFiniteUnionVoid
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s : ℕ) (rho : ℝ) :
    MeasurableSet (plantedRubenFiniteUnionVoid W m p s rho) := by
  unfold plantedRubenFiniteUnionVoid
  exact measurableSet_singleton 0 |>.preimage
    (measurable_plantedRubenFiniteUnionCount W m p s rho)

/-- The squared signed statistic is the algebraic squared-Pearson statistic. -/
theorem correlatedSignedPearsonT_sq_eq_correlatedSquaredPearsonT
    (m : ℕ) (rho : ℝ) (z : E × E) :
    correlatedSignedPearsonT (E := E) m rho z ^ 2 =
      correlatedSquaredPearsonT (E := E) m rho z := by
  have hdet : 0 ≤ twoColumnGramDet z.1
      (correlatedSecondColumn rho z.1 z.2) := by
    unfold twoColumnGramDet
    have hcs := abs_real_inner_le_norm z.1
      (correlatedSecondColumn rho z.1 z.2)
    have hprod : 0 ≤ ‖z.1‖ * ‖correlatedSecondColumn rho z.1 z.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsquare : inner ℝ z.1 (correlatedSecondColumn rho z.1 z.2) ^ 2 ≤
        (‖z.1‖ * ‖correlatedSecondColumn rho z.1 z.2‖) ^ 2 :=
      by
        have := (sq_le_sq₀ (abs_nonneg _) hprod).2 hcs
        simpa [sq_abs] using this
    nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖correlatedSecondColumn rho z.1 z.2‖]
  unfold correlatedSignedPearsonT signedPearsonT
    correlatedSquaredPearsonT squaredPearsonT
  rw [div_pow, mul_pow, Real.sq_sqrt]
  · rw [Real.sq_sqrt hdet]
  · exact_mod_cast Nat.zero_le (m - 1)

/-- Pointwise Ruben factorization of the planted height whenever the first
Gaussian column is nonzero. -/
theorem plantedPearsonHeight_eq_plantedRubenHeight
    (m p : ℕ) (rho : ℝ) (hrho : |rho| < 1)
    (z : E × E) (hz : z.1 ≠ 0) :
    plantedPearsonHeight (E := E) m p rho z =
      plantedRubenHeight m p rho (gaussianRubenCoordinates z) := by
  unfold plantedPearsonHeight pearsonHeightFromStudentized
    plantedRubenHeight
  rw [correlatedSignedPearsonT_sq_eq_correlatedSquaredPearsonT]
  rw [correlatedSquaredPearsonT,
    squaredPearsonT_correlatedSecondColumn_eq_squaredRubenT
      m rho z.1 z.2 hrho hz,
    squaredRubenT_eq_squaredRubenCoordinateStatistic]

/-- Almost-sure equality between the raw planted void and its Ruben-only
representation on the grouped stable-matching base sample. -/
theorem ae_rawPlantedVoid_iff_rubenPlantedVoid
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p s r : ℕ} (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) :
    ∀ᵐ w : StableMatchingBaseSample E s r ∂stableMatchingBaseMeasure E s r,
      (∀ e : Fin s,
        w.1 e ∉ plantedPearsonFiniteUnionEvent (E := E) W m p rho) ↔
      stableMatchingRubenData s r w ∈
        plantedRubenFiniteUnionVoid W m p s rho := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have hnonzeroPair : ∀ᵐ z ∂((stdGaussian E).prod (stdGaussian E)), z.1 ≠ 0 := by
    exact (Measure.quasiMeasurePreserving_fst
      (μ := stdGaussian E) (ν := stdGaussian E)).ae
        (p := fun x : E ↦ x ≠ 0)
        (by simpa [ae_iff] using LogdetLean.stdGaussian_zero_singleton (E := E))
  have hnonzeroArray : ∀ᵐ v ∂Measure.pi (fun _ : Fin s ↦
      (stdGaussian E).prod (stdGaussian E)), ∀ e, (v e).1 ≠ 0 := by
    apply ae_all_iff.2
    intro e
    exact (measurePreserving_eval
      (fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) e).quasiMeasurePreserving.ae
        hnonzeroPair
  have hbase : ∀ᵐ w ∂stableMatchingBaseMeasure E s r,
      ∀ e, (w.1 e).1 ≠ 0 := by
    unfold stableMatchingBaseMeasure
    exact (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E))
      (ν := Measure.pi fun _ : Fin r ↦ stdGaussian E)).ae hnonzeroArray
  filter_upwards [hbase] with w hw
  have heq : ∀ e : Fin s,
      (w.1 e ∈ plantedPearsonFiniteUnionEvent (E := E) W m p rho) ↔
        plantedRubenHeight m p rho
            (stableMatchingRubenData s r w e) ∈ finiteScoreWindowUnion W := by
    intro e
    unfold plantedPearsonFiniteUnionEvent stableMatchingRubenData
      gaussianRubenCoordinateArray
    rw [Set.mem_preimage]
    rw [plantedPearsonHeight_eq_plantedRubenHeight
      m p rho hrho (w.1 e) (hw e)]
  unfold plantedRubenFiniteUnionVoid plantedRubenFiniteUnionCount
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    apply Finset.sum_eq_zero
    intro e _he
    rw [if_neg]
    exact fun he ↦ h e ((heq e).mpr he)
  · intro h e hevent
    have hterm := Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ ↦ Nat.zero_le _) |>.mp h e (Finset.mem_univ e)
    rw [if_pos ((heq e).mp hevent)] at hterm
    exact one_ne_zero hterm

/-- Exact finite-sample factorization of a frame half-line and the planted
Ruben void event. -/
theorem measureReal_frameIic_inter_rubenPlantedVoid_eq_mul
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p s r : ℕ} (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m)
    (rho z : ℝ) :
    (stableMatchingBaseMeasure E s r).real
      ((stableMatchingFrameZ0 (E := E) m s r ⁻¹' Set.Iic z) ∩
        (stableMatchingRubenData (E := E) s r ⁻¹'
          plantedRubenFiniteUnionVoid W m p s rho)) =
      (stableMatchingBaseMeasure E s r).real
          (stableMatchingFrameZ0 (E := E) m s r ⁻¹' Set.Iic z) *
        (stableMatchingBaseMeasure E s r).real
          (stableMatchingRubenData (E := E) s r ⁻¹'
            plantedRubenFiniteUnionVoid W m p s rho) := by
  have h := (indepFun_stableMatchingFrameZ0_rubenData
    (E := E) s r m hdim hm).measure_inter_preimage_eq_mul
      (Set.Iic z) (plantedRubenFiniteUnionVoid W m p s rho)
      measurableSet_Iic
      (measurableSet_plantedRubenFiniteUnionVoid W m p s rho)
  change ((stableMatchingBaseMeasure E s r)
      ((stableMatchingFrameZ0 (E := E) m s r ⁻¹' Set.Iic z) ∩
        (stableMatchingRubenData (E := E) s r ⁻¹'
          plantedRubenFiniteUnionVoid W m p s rho))).toReal = _
  rw [h, ENNReal.toReal_mul]
  rfl

end

end LogdetLean.Coherence
