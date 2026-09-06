import LogdetLean.Coherence.HomogeneousPlantedIntensity
import LogdetLean.Coherence.FiniteUnionScoreWindow
import Mathlib.Tactic
/-!
# Finite score unions for homogeneous planted matching blocks

This module converts the exact studentized Pearson statistic back to the
normalized squared-correlation height.  It then proves the one-block
finite-union probability formula needed for the planted Poisson component.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Inverse Student transform, expressed as the normalized Pearson height.
If `t²=(m-1)r²/(1-r²)`, this is exactly
`m r²-(4 log p-log log p)`. -/
def pearsonHeightFromStudentized (m p : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) * t ^ 2 / (((m : ℝ) - 1) + t ^ 2) -
    classicalCoherenceThreshold m p 0

theorem measurable_pearsonHeightFromStudentized (m p : ℕ) :
    Measurable (pearsonHeightFromStudentized m p) := by
  unfold pearsonHeightFromStudentized
  fun_prop

/-- Normalized planted height of one Gaussian pair. -/
def plantedPearsonHeight (m p : ℕ) (rho : ℝ) (z : E × E) : ℝ :=
  pearsonHeightFromStudentized m p
    (correlatedSignedPearsonT (E := E) m rho z)

theorem measurable_plantedPearsonHeight (m p : ℕ) (rho : ℝ) :
    Measurable (plantedPearsonHeight (E := E) m p rho) := by
  exact (measurable_pearsonHeightFromStudentized m p).comp
    (measurable_correlatedSignedPearsonT m rho)

/-- Exact inversion of the Student transform at a coherence-score level. -/
theorem pearsonHeightFromStudentized_gt_iff
    {m p : ℕ} (hm : 2 ≤ m) {x t : ℝ}
    (hlevel0 : 0 ≤ classicalCoherenceThreshold m p x)
    (hlevelm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    x < pearsonHeightFromStudentized m p t ↔
      pearsonExactThresholdSq m p x < t ^ 2 := by
  have hm1 : 0 < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hdenT : 0 < ((m : ℝ) - 1) + t ^ 2 :=
    add_pos_of_pos_of_nonneg hm1 (sq_nonneg t)
  have hdenX : 0 < (m : ℝ) - classicalCoherenceThreshold m p x :=
    sub_pos.mpr hlevelm
  have hleft :
      x < (m : ℝ) * t ^ 2 / (((m : ℝ) - 1) + t ^ 2) -
          classicalCoherenceThreshold m p 0 ↔
        classicalCoherenceThreshold m p x <
          (m : ℝ) * t ^ 2 / (((m : ℝ) - 1) + t ^ 2) := by
    have hcx := classicalCoherenceThreshold_eq_zero_add m p x
    constructor <;> intro h <;> nlinarith
  unfold pearsonHeightFromStudentized
  rw [hleft]
  unfold pearsonExactThresholdSq
  rw [lt_div_iff₀ hdenT, div_lt_iff₀ hdenX]
  constructor <;> intro h <;> nlinarith

/-- The exact squared threshold is the square of its nonnegative root. -/
theorem pearsonExactThreshold_sq_of_scoreRange
    {m p : ℕ} (hm : 2 ≤ m) {x : ℝ}
    (hlevel0 : 0 ≤ classicalCoherenceThreshold m p x)
    (hlevelm : classicalCoherenceThreshold m p x < (m : ℝ)) :
    pearsonExactThreshold m p x ^ 2 = pearsonExactThresholdSq m p x := by
  unfold pearsonExactThreshold
  rw [Real.sq_sqrt]
  unfold pearsonExactThresholdSq
  exact div_nonneg
    (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ m by omega))) hlevel0)
    (sub_nonneg.mpr hlevelm.le)

/-- Crossing a normalized planted height is exactly the two-sided
studentized Pearson exceedance event. -/
theorem plantedPearsonHeight_gt_iff_exceedance
    {m p : ℕ} (hm : 2 ≤ m) {rho x : ℝ}
    (hlevel0 : 0 ≤ classicalCoherenceThreshold m p x)
    (hlevelm : classicalCoherenceThreshold m p x < (m : ℝ))
    (z : E × E) :
    x < plantedPearsonHeight m p rho z ↔
      z ∈ plantedPearsonExceedanceEvent (E := E) m rho
        (pearsonExactThreshold m p x) := by
  rw [plantedPearsonHeight, pearsonHeightFromStudentized_gt_iff hm hlevel0 hlevelm,
    ← pearsonExactThreshold_sq_of_scoreRange hm hlevel0 hlevelm]
  have hq : 0 ≤ pearsonExactThreshold m p x := Real.sqrt_nonneg _
  unfold plantedPearsonExceedanceEvent
  change pearsonExactThreshold m p x ^ 2 <
      correlatedSignedPearsonT (E := E) m rho z ^ 2 ↔ _
  rw [sq_lt_sq, abs_of_nonneg hq]
  constructor
  · intro h
    by_cases ht : 0 ≤ correlatedSignedPearsonT (E := E) m rho z
    · left
      simpa [abs_of_nonneg ht] using h
    · right
      rw [abs_of_nonpos (le_of_not_ge ht)] at h
      exact (lt_neg).mp h
  · intro h
    rcases h with h | h
    · exact h.trans_le (le_abs_self _)
    · exact (lt_neg.mpr h).trans_le (neg_le_abs _)

/-- One planted block has height in the finite disjoint score union. -/
def plantedPearsonFiniteUnionEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (rho : ℝ) : Set (E × E) :=
  plantedPearsonHeight (E := E) m p rho ⁻¹' finiteScoreWindowUnion W

theorem measurableSet_plantedPearsonFiniteUnionEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (rho : ℝ) :
    MeasurableSet (plantedPearsonFiniteUnionEvent (E := E) W m p rho) := by
  exact (measurableSet_finiteScoreWindowUnion W).preimage
    (measurable_plantedPearsonHeight m p rho)

/-- Limiting planted intensity assigned to a finite score union. -/
def finiteUnionPlantedIntensity
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (kappa : ℝ) : ℝ :=
  ∑ i, (kappa * Real.exp (-W.lower i / (2 * Real.sqrt 2)) -
    kappa * Real.exp (-W.upper i / (2 * Real.sqrt 2)))

/-- Exact one-block probability as a finite sum of two-sided tail
differences. -/
theorem real_plantedPearsonFiniteUnionEvent_eq_tailSum
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p : ℕ} (hm : 2 ≤ m) (rho : ℝ)
    (hrange : ∀ i,
      0 ≤ classicalCoherenceThreshold m p (W.lower i) ∧
        classicalCoherenceThreshold m p (W.upper i) < (m : ℝ)) :
    ((stdGaussian E).prod (stdGaussian E)).real
        (plantedPearsonFiniteUnionEvent (E := E) W m p rho) =
      ∑ i, (gaussianPearsonTwoSidedTail (E := E) m rho
          (pearsonExactThreshold m p (W.lower i)) -
        gaussianPearsonTwoSidedTail (E := E) m rho
          (pearsonExactThreshold m p (W.upper i))) := by
  let mu : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let H := plantedPearsonHeight (E := E) m p rho
  have hpair : Pairwise fun i j ↦
      Disjoint (H ⁻¹' Set.Ioc (W.lower i) (W.upper i))
        (H ⁻¹' Set.Ioc (W.lower j) (W.upper j)) := by
    intro i j hij
    exact (W.pairwiseDisjoint hij).preimage H
  unfold plantedPearsonFiniteUnionEvent finiteScoreWindowUnion
  rw [preimage_iUnion]
  rw [measureReal_iUnion_fintype hpair (fun i ↦
    measurableSet_Ioc.preimage (measurable_plantedPearsonHeight m p rho))]
  apply Finset.sum_congr rfl
  intro i _hi
  let A := plantedPearsonExceedanceEvent (E := E) m rho
    (pearsonExactThreshold m p (W.lower i))
  let B := plantedPearsonExceedanceEvent (E := E) m rho
    (pearsonExactThreshold m p (W.upper i))
  have hlowerM :
      classicalCoherenceThreshold m p (W.lower i) < (m : ℝ) := by
    have hlo := classicalCoherenceThreshold_eq_zero_add m p (W.lower i)
    have hhi := classicalCoherenceThreshold_eq_zero_add m p (W.upper i)
    nlinarith [W.ordered i, (hrange i).2]
  have hupper0 :
      0 ≤ classicalCoherenceThreshold m p (W.upper i) := by
    have hlo := classicalCoherenceThreshold_eq_zero_add m p (W.lower i)
    have hhi := classicalCoherenceThreshold_eq_zero_add m p (W.upper i)
    nlinarith [W.ordered i, (hrange i).1]
  have hpre : H ⁻¹' Set.Ioc (W.lower i) (W.upper i) = A \ B := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_diff]
    have hlo := plantedPearsonHeight_gt_iff_exceedance
      (E := E) hm (rho := rho) (x := W.lower i)
      (hrange i).1 hlowerM z
    have hhi := plantedPearsonHeight_gt_iff_exceedance
      (E := E) hm (rho := rho) (x := W.upper i)
      hupper0 (hrange i).2 z
    change (W.lower i < H z ∧ H z ≤ W.upper i) ↔
      (z ∈ plantedPearsonExceedanceEvent (E := E) m rho
          (pearsonExactThreshold m p (W.lower i)) ∧
        z ∉ plantedPearsonExceedanceEvent (E := E) m rho
          (pearsonExactThreshold m p (W.upper i)))
    rw [hlo, ← not_congr hhi, not_lt]
  have hBsubA : B ⊆ A := by
    intro z hz
    have hlo := (plantedPearsonHeight_gt_iff_exceedance
      (E := E) hm (rho := rho) (x := W.lower i)
      (hrange i).1 hlowerM z).mp
    have hhi := (plantedPearsonHeight_gt_iff_exceedance
      (E := E) hm (rho := rho) (x := W.upper i)
      hupper0 (hrange i).2 z).mpr
    exact hlo ((W.ordered i).trans_lt (hhi hz))
  rw [hpre, measureReal_sdiff hBsubA
    (measurableSet_plantedPearsonExceedanceEvent m rho
      (pearsonExactThreshold m p (W.upper i)))]
  rw [real_plantedPearsonExceedanceEvent_eq,
    real_plantedPearsonExceedanceEvent_eq]
  all_goals exact Real.sqrt_nonneg _

/-- The exact one-block probability, written in the tail-difference form
used by the asymptotic calculation. -/
def homogeneousPlantedFiniteUnionProbability
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p : ℕ) (rho : ℝ) : ℝ :=
  ∑ i, (gaussianPearsonTwoSidedTail
      (E := EuclideanSpace ℝ (Fin m)) m rho
        (pearsonExactThreshold m p (W.lower i)) -
    gaussianPearsonTwoSidedTail
      (E := EuclideanSpace ℝ (Fin m)) m rho
        (pearsonExactThreshold m p (W.upper i)))

/-- Exact product formula for avoiding a finite score union in every
homogeneous planted block. -/
theorem real_pi_all_plantedPearson_noFiniteUnion_eq_pow
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p s : ℕ} (hm : 2 ≤ m) (rho : ℝ)
    (hrange : ∀ i,
      0 ≤ classicalCoherenceThreshold m p (W.lower i) ∧
        classicalCoherenceThreshold m p (W.upper i) < (m : ℝ)) :
    (Measure.pi (fun _ : Fin s ↦
        (stdGaussian (EuclideanSpace ℝ (Fin m))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin m))))).real
      (Set.univ.pi fun _ : Fin s ↦
        (plantedPearsonFiniteUnionEvent
          (E := EuclideanSpace ℝ (Fin m)) W m p rho)ᶜ) =
      (1 - homogeneousPlantedFiniteUnionProbability W m p rho) ^ s := by
  let E := EuclideanSpace ℝ (Fin m)
  let mu : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let A : Set (E × E) := plantedPearsonFiniteUnionEvent W m p rho
  letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hA : MeasurableSet A :=
    measurableSet_plantedPearsonFiniteUnionEvent W m p rho
  rw [Measure.real, Measure.pi_pi]
  rw [ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprob : mu.real A = homogeneousPlantedFiniteUnionProbability W m p rho := by
    simpa [mu, A, homogeneousPlantedFiniteUnionProbability] using
      real_plantedPearsonFiniteUnionEvent_eq_tailSum
        (E := E) W hm rho hrange
  have hcompl : mu.real Aᶜ =
      1 - homogeneousPlantedFiniteUnionProbability W m p rho := by
    rw [measureReal_compl hA, probReal_univ, hprob]
  have htoReal : (mu Aᶜ).toReal = mu.real Aᶜ := rfl
  rw [htoReal, hcompl]

/-- Summed one-block intensity over an arbitrary fixed finite union. -/
theorem tendsto_homogeneousPlantedFiniteUnionIntensity
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hgap : C ^ 2 / 2 < L)
    {mseq sseq : ℕ → ℕ} {rhoSeq tseq : ℕ → ℝ} {kappa : ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hrho : ∀ᶠ p in atTop, |rhoSeq p| < 1)
    (hlambda : ∀ᶠ p in atTop,
      pearsonRubenNoncentrality (mseq p) (rhoSeq p) =
        pearsonExactThreshold (mseq p) p 0 - tseq p)
    (hscaleLower : ∀ i, ∀ᶠ p in atTop,
      pearsonExactThreshold (mseq p) p (W.lower i) +
          |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ)))
    (hscaleUpper : ∀ i, ∀ᶠ p in atTop,
      pearsonExactThreshold (mseq p) p (W.upper i) +
          |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ)))
    (htRatio : Tendsto (fun p : ℕ ↦
      tseq p / pearsonExactThreshold (mseq p) p 0)
      atTop (nhds (1 / Real.sqrt 2)))
    (hbase : Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) * standardGaussianUpperTail (tseq p))
      atTop (nhds kappa)) :
    Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) *
        homogeneousPlantedFiniteUnionProbability
          W (mseq p) p (rhoSeq p))
      atTop (nhds (finiteUnionPlantedIntensity W kappa)) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _hi ↦
    tendsto_homogeneousPlantedPearsonWindowIntensity
      hC hL hgap hadm hrho hlambda (W.lower i) (W.upper i)
        (hscaleLower i) (hscaleUpper i) htRatio hbase)
  apply hsum.congr'
  filter_upwards with p
  simp only [homogeneousPlantedFiniteUnionProbability,
    finiteUnionPlantedIntensity]
  rw [Finset.mul_sum]

/-- The planted finite-union void probability has the predicted Poisson
limit. -/
theorem tendsto_homogeneousPlantedFiniteUnionVoid
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hgap : C ^ 2 / 2 < L)
    {mseq sseq : ℕ → ℕ} {rhoSeq tseq : ℕ → ℝ} {kappa : ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hs : Tendsto (fun p ↦ (sseq p : ℝ)) atTop atTop)
    (hrho : ∀ᶠ p in atTop, |rhoSeq p| < 1)
    (hlambda : ∀ᶠ p in atTop,
      pearsonRubenNoncentrality (mseq p) (rhoSeq p) =
        pearsonExactThreshold (mseq p) p 0 - tseq p)
    (hscaleLower : ∀ i, ∀ᶠ p in atTop,
      pearsonExactThreshold (mseq p) p (W.lower i) +
          |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ)))
    (hscaleUpper : ∀ i, ∀ᶠ p in atTop,
      pearsonExactThreshold (mseq p) p (W.upper i) +
          |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ)))
    (htRatio : Tendsto (fun p : ℕ ↦
      tseq p / pearsonExactThreshold (mseq p) p 0)
      atTop (nhds (1 / Real.sqrt 2)))
    (hbase : Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) * standardGaussianUpperTail (tseq p))
      atTop (nhds kappa)) :
    Tendsto (fun p : ℕ ↦
      (Measure.pi (fun _ : Fin (sseq p) ↦
          (stdGaussian (EuclideanSpace ℝ (Fin (mseq p)))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin (mseq p)))))).real
        (Set.univ.pi fun _ : Fin (sseq p) ↦
          (plantedPearsonFiniteUnionEvent
            (E := EuclideanSpace ℝ (Fin (mseq p)))
            W (mseq p) p (rhoSeq p))ᶜ))
      atTop
      (nhds (Real.exp (-(finiteUnionPlantedIntensity W kappa)))) := by
  let qprob : ℕ → ℝ := fun p ↦
    homogeneousPlantedFiniteUnionProbability W (mseq p) p (rhoSeq p)
  have hintensity : Tendsto (fun p ↦ (sseq p : ℝ) * qprob p)
      atTop (nhds (finiteUnionPlantedIntensity W kappa)) := by
    exact tendsto_homogeneousPlantedFiniteUnionIntensity W
      hC hL hgap hadm hrho hlambda hscaleLower hscaleUpper htRatio hbase
  have hqzero := tendsto_rareBernoulliProbability_zero hs hintensity
  have hrange : ∀ᶠ p in atTop, ∀ i,
      0 ≤ classicalCoherenceThreshold (mseq p) p (W.lower i) ∧
        classicalCoherenceThreshold (mseq p) p (W.upper i) < (mseq p : ℝ) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards
      [eventually_classicalCoherenceThreshold_scoreRange hadm (W.lower i),
        eventually_classicalCoherenceThreshold_scoreRange hadm (W.upper i)]
      with p hlo hhi
    exact ⟨hlo.1.le, hhi.2⟩
  have hq0 : ∀ᶠ p in atTop, 0 ≤ qprob p := by
    filter_upwards [hrange, hadm] with p hp hadmp
    change 0 ≤ homogeneousPlantedFiniteUnionProbability
      W (mseq p) p (rhoSeq p)
    unfold homogeneousPlantedFiniteUnionProbability
    rw [← real_plantedPearsonFiniteUnionEvent_eq_tailSum
      (E := EuclideanSpace ℝ (Fin (mseq p))) W
      (hadmp.1.trans hadmp.2) (rhoSeq p) hp]
    exact measureReal_nonneg
  have hq1 : ∀ᶠ p in atTop, qprob p < 1 :=
    hqzero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hvoid := tendsto_rareBernoulliVoid hs hintensity hq0 hq1
  apply hvoid.congr'
  filter_upwards [hrange, hadm] with p hp hadmp
  have hm : 2 ≤ mseq p := hadmp.1.trans hadmp.2
  exact (real_pi_all_plantedPearson_noFiniteUnion_eq_pow
    W hm (rhoSeq p) hp).symm

end

end LogdetLean.Coherence
