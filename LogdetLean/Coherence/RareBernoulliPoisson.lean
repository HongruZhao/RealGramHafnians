import LogdetLean.Coherence.GammaChernoff
import LogdetLean.Coherence.NoncentralPearsonFiniteMD
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic
/-!
# A triangular rare-Bernoulli void limit

Unlike the standard binomial limit theorem indexed by the number of trials,
this version permits an arbitrary diverging trial-count sequence.  It is the
form needed when the number of planted blocks is `s_p` while the ambient
dimension is `p`.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real
open MeasureTheory ProbabilityTheory Set
open scoped Topology

theorem tendsto_rareBernoulliProbability_zero
    {sseq : ℕ → ℕ} {qseq : ℕ → ℝ} {lambda : ℝ}
    (hs : Tendsto (fun p ↦ (sseq p : ℝ)) atTop atTop)
    (hintensity : Tendsto (fun p ↦ (sseq p : ℝ) * qseq p)
      atTop (nhds lambda)) :
    Tendsto qseq atTop (nhds 0) := by
  have hdiv := hintensity.div_atTop hs
  apply hdiv.congr'
  filter_upwards [hs.eventually (eventually_ne_atTop (0 : ℝ))]
    with p hp
  field_simp [hp]

/-- If `s_p q_p → lambda`, `s_p → ∞`, and `q_p` is eventually a
probability, then the probability of no success tends to `exp(-lambda)`. -/
theorem tendsto_rareBernoulliVoid
    {sseq : ℕ → ℕ} {qseq : ℕ → ℝ} {lambda : ℝ}
    (hs : Tendsto (fun p ↦ (sseq p : ℝ)) atTop atTop)
    (hintensity : Tendsto (fun p ↦ (sseq p : ℝ) * qseq p)
      atTop (nhds lambda))
    (hq0 : ∀ᶠ p in atTop, 0 ≤ qseq p)
    (hq1 : ∀ᶠ p in atTop, qseq p < 1) :
    Tendsto (fun p ↦ (1 - qseq p) ^ sseq p)
      atTop (nhds (Real.exp (-lambda))) := by
  have hq := tendsto_rareBernoulliProbability_zero hs hintensity
  have hqhalf : ∀ᶠ p in atTop, qseq p ≤ 1 / 2 :=
    hq.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hsq : Tendsto (fun p ↦
      ((sseq p : ℝ) * qseq p) * qseq p)
      atTop (nhds 0) := by
    simpa using hintensity.mul hq
  let err : ℕ → ℝ := fun p ↦
    (sseq p : ℝ) * (-Real.log (1 - qseq p) - qseq p)
  have herr0 : ∀ᶠ p in atTop, 0 ≤ err p := by
    filter_upwards [hq0, hq1] with p hp0 hp1
    have hpos : 0 < 1 - qseq p := sub_pos.mpr hp1
    have hlog := Real.log_le_sub_one_of_pos hpos
    dsimp [err]
    have hs0 : 0 ≤ (sseq p : ℝ) := Nat.cast_nonneg _
    apply mul_nonneg hs0
    linarith
  have herrUpper : ∀ᶠ p in atTop,
      err p ≤ ((sseq p : ℝ) * qseq p) * qseq p := by
    filter_upwards [hq0, hqhalf] with p hp0 hphalf
    have hlog := neg_log_one_sub_le_add_sq hp0 hphalf
    dsimp [err]
    have hs0 : 0 ≤ (sseq p : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left
      (show -Real.log (1 - qseq p) - qseq p ≤ qseq p ^ 2 by linarith) hs0
    nlinarith
  have herr : Tendsto err atTop (nhds 0) := by
    exact squeeze_zero' herr0 herrUpper hsq
  have hlog : Tendsto (fun p ↦
      (sseq p : ℝ) * Real.log (1 - qseq p))
      atTop (nhds (-lambda)) := by
    have hneg := hintensity.neg.sub herr
    have hneg' : Tendsto (fun p ↦
        -((sseq p : ℝ) * qseq p) - err p)
        atTop (nhds (-lambda)) := by simpa using hneg
    apply hneg'.congr'
    filter_upwards with p
    dsimp [err]
    ring
  have hexp : Tendsto (fun p ↦ Real.exp
      ((sseq p : ℝ) * Real.log (1 - qseq p)))
      atTop (nhds (Real.exp (-lambda))) :=
    (Real.continuous_exp.tendsto (-lambda)).comp hlog
  apply hexp.congr'
  filter_upwards [hq1] with p hp1
  have hpos : 0 < 1 - qseq p := sub_pos.mpr hp1
  rw [Real.exp_nat_mul]
  rw [Real.exp_log hpos]

/-! ## Exact planted-block void probability -/

/-- Two-sided exceedance event for a single correlated Gaussian pair. -/
def plantedPearsonExceedanceEvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) (rho q : ℝ) : Set (E × E) :=
  {z | q < correlatedSignedPearsonT (E := E) m rho z} ∪
    {z | correlatedSignedPearsonT (E := E) m rho z < -q}

theorem measurableSet_plantedPearsonExceedanceEvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (rho q : ℝ) :
    MeasurableSet (plantedPearsonExceedanceEvent (E := E) m rho q) := by
  unfold plantedPearsonExceedanceEvent
  exact (measurableSet_lt measurable_const
    (measurable_correlatedSignedPearsonT m rho)).union
      (measurableSet_lt (measurable_correlatedSignedPearsonT m rho)
        measurable_const)

theorem plantedPearsonExceedanceEvent_disjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) (rho q : ℝ) (hq : 0 ≤ q) :
    Disjoint
      {z : E × E | q < correlatedSignedPearsonT (E := E) m rho z}
      {z : E × E | correlatedSignedPearsonT (E := E) m rho z < -q} := by
  rw [Set.disjoint_left]
  intro z hzUpper hzLower
  dsimp at hzUpper hzLower
  linarith

theorem real_plantedPearsonExceedanceEvent_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (rho q : ℝ) (hq : 0 ≤ q) :
    ((stdGaussian E).prod (stdGaussian E)).real
        (plantedPearsonExceedanceEvent (E := E) m rho q) =
      gaussianPearsonTwoSidedTail (E := E) m rho q := by
  unfold plantedPearsonExceedanceEvent gaussianPearsonTwoSidedTail
  rw [measureReal_union
    (plantedPearsonExceedanceEvent_disjoint m rho q hq)
    (measurableSet_lt (measurable_correlatedSignedPearsonT m rho)
      measurable_const)]

/-- Exact product formula for avoiding the exceedance in every one of `s`
independent, homogeneous Gaussian pair blocks. -/
theorem real_pi_all_plantedPearson_noExceedance_eq_pow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m s : ℕ) (rho q : ℝ) (hq : 0 ≤ q) :
    (Measure.pi (fun _ : Fin s ↦
        (stdGaussian E).prod (stdGaussian E))).real
      (Set.univ.pi fun _ : Fin s ↦
        (plantedPearsonExceedanceEvent (E := E) m rho q)ᶜ) =
      (1 - gaussianPearsonTwoSidedTail (E := E) m rho q) ^ s := by
  let μ : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let A : Set (E × E) := plantedPearsonExceedanceEvent (E := E) m rho q
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hA : MeasurableSet A :=
    measurableSet_plantedPearsonExceedanceEvent m rho q
  rw [Measure.real, Measure.pi_pi]
  rw [ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcompl : μ.real Aᶜ = 1 - gaussianPearsonTwoSidedTail (E := E) m rho q := by
    rw [measureReal_compl hA, probReal_univ]
    exact congrArg (fun u : ℝ ↦ 1 - u)
      (real_plantedPearsonExceedanceEvent_eq m rho q hq)
  have htoReal : (μ Aᶜ).toReal = μ.real Aᶜ := rfl
  rw [htoReal, hcompl]

end

end LogdetLean.Coherence
