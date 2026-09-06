import RealGramHafnians.Proofs.RowSuspensionInverseRecursion
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian
noncomputable section

/-- Laplace domination transfers absence of an atom at zero. This avoids a
rank assumption in the row-suspension induction. -/
theorem review_ae_pos_of_laplace_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (U : Ω → ℝ) (V : Ω' → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (hUn : ∀ x, 0 ≤ U x) (hVn : ∀ x, 0 ≤ V x)
    (hVp : ∀ᵐ x ∂ν, 0 < V x)
    (hLap : ∀ t : ℝ, 0 ≤ t → ennLaplaceTransform μ U t ≤ ennLaplaceTransform ν V t) :
    ∀ᵐ x ∂μ, 0 < U x := by
  let F : ℕ → Ω' → ℝ≥0∞ := fun n x ↦ ENNReal.ofReal (Real.exp (-(n : ℝ) * V x))
  have hlim : Tendsto (fun n ↦ ∫⁻ x, F n x ∂ν) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence (μ := ν) (F := F) (f := fun _ ↦ 0) (fun _ : Ω' ↦ (1 : ℝ≥0∞))
      (fun n ↦ by dsimp [F]; fun_prop)
      (fun n ↦ Filter.Eventually.of_forall fun x ↦ by
        dsimp [F]
        exact (ENNReal.ofReal_le_one).2 (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (hVn x))))
      (by simp)
      (by
        filter_upwards [hVp] with x hx
        have ht : Tendsto (fun n : ℕ ↦ -(n : ℝ) * V x) atTop atBot := by
          convert (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hx)) using 1
          funext n
          simp only [Function.comp_apply, neg_mul]
        simpa [F, Function.comp_def, neg_mul] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (Real.tendsto_exp_atBot.comp ht))
    simpa using h
  have hz : μ {x | U x = 0} = 0 := by
    apply le_antisymm _ (bot_le)
    apply ge_of_tendsto hlim
    filter_upwards with n
    apply le_trans _ (hLap n (Nat.cast_nonneg n))
    unfold ennLaplaceTransform
    rw [← lintegral_indicator_one ((hU.eq_const 0).setOf)]
    apply lintegral_mono
    intro x
    by_cases hx : U x = 0
    · simp [hx, Set.indicator_of_mem]
    · simp [hx, Set.indicator_of_notMem]
  have hne : ∀ᵐ x ∂μ, U x ≠ 0 := by simpa [ae_iff] using hz
  filter_upwards [hne] with x hx
  exact lt_of_le_of_ne (hUn x) (Ne.symm hx)

end
end LogdetLean.GramHafnian
