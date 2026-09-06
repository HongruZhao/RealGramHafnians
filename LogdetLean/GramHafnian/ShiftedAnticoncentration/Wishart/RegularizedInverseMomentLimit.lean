import LogdetLean.GramHafnian.ShiftedAnticoncentration.LaplaceOrder
/-!
# Removing a scalar inverse-moment regularization

This module isolates the final measure-theoretic limit used by the
conditional-Wishart argument.  A regularized real-integral identity, together
with the deterministic quadratic comparison `W^2 ≤ V * A`, yields the desired
`ENNReal` inverse-moment inequality.  Fatou's lemma is applied along the
explicit sequence `δ_n = 1 / (n + 1)`; no finiteness assumption is imposed on
the limiting inverse moments.
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A regularized scalar integral identity implies the corresponding
unregularized inverse-moment comparison.  The conclusion is stated in
`ENNReal`, so it remains meaningful when either inverse moment is infinite.

The hypotheses are tailored to the conditional-Wishart application:
`W^2 ≤ V*A` is the pointwise matrix Cauchy--Schwarz comparison, while the
identity at every `δ > 0` is supplied by the bounded regularized score test. -/
theorem ennInverseMoment_le_of_regularized_integral_identity
    (μ : Measure Ω) (V W A : Ω → ℝ)
    (hV : Measurable V) (hW : Measurable W) (hA : Measurable A)
    (hVpos : ∀ᵐ ω ∂μ, 0 < V ω)
    (hWpos : ∀ᵐ ω ∂μ, 0 < W ω)
    (hAnonneg : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    (hquadratic : ∀ᵐ ω ∂μ, W ω ^ 2 ≤ V ω * A ω)
    (c : ℝ) (hc : 0 ≤ c)
    (hregularized : ∀ δ : ℝ, 0 < δ →
      Integrable (fun ω ↦ A ω / (W ω + δ) ^ 2) μ ∧
      Integrable (fun ω ↦ W ω / (W ω + δ) ^ 2) μ ∧
      (∫ ω, A ω / (W ω + δ) ^ 2 ∂μ) =
        c * ∫ ω, W ω / (W ω + δ) ^ 2 ∂μ) :
    ennInverseMoment μ V ≤
      ENNReal.ofReal c * ennInverseMoment μ W := by
  let δseq : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let F : ℕ → Ω → ENNReal := fun n ω ↦
    ENNReal.ofReal (A ω / (W ω + δseq n) ^ 2)
  have hδpos (n : ℕ) : 0 < δseq n := by
    dsimp only [δseq]
    positivity
  have hFmeas (n : ℕ) : Measurable (F n) := by
    dsimp only [F]
    exact (hA.div ((hW.add_const _).pow_const 2)).ennreal_ofReal
  have hδtendsto : Tendsto δseq atTop (𝓝 0) := by
    dsimp only [δseq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hFlimit : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ F n ω) atTop
        (𝓝 (ENNReal.ofReal (A ω / W ω ^ 2))) := by
    filter_upwards [hWpos] with ω hω
    have hden : Tendsto (fun n ↦ (W ω + δseq n) ^ 2) atTop
        (𝓝 (W ω ^ 2)) := by
      simpa using
        ((tendsto_const_nhds :
            Tendsto (fun _ : ℕ ↦ W ω) atTop (𝓝 (W ω))).add hδtendsto).pow 2
    have hquot : Tendsto (fun n ↦ A ω / (W ω + δseq n) ^ 2) atTop
        (𝓝 (A ω / W ω ^ 2)) :=
      tendsto_const_nhds.div hden (pow_ne_zero 2 hω.ne')
    exact ENNReal.tendsto_ofReal hquot
  have hFatou :
      (∫⁻ ω, ENNReal.ofReal (A ω / W ω ^ 2) ∂μ) ≤
        liminf (fun n ↦ ∫⁻ ω, F n ω ∂μ) atTop := by
    calc
      (∫⁻ ω, ENNReal.ofReal (A ω / W ω ^ 2) ∂μ) =
          ∫⁻ ω, liminf (fun n ↦ F n ω) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hFlimit] with ω hlim
        exact hlim.liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ ω, F n ω ∂μ) atTop :=
        lintegral_liminf_le hFmeas
  have hFbound (n : ℕ) :
      (∫⁻ ω, F n ω ∂μ) ≤
        ENNReal.ofReal c * ennInverseMoment μ W := by
    obtain ⟨hfint, hgint, heq⟩ := hregularized (δseq n) (hδpos n)
    have hfnonneg : 0 ≤ᵐ[μ]
        (fun ω ↦ A ω / (W ω + δseq n) ^ 2) := by
      filter_upwards [hAnonneg] with ω hAω
      positivity
    have hgnonneg : 0 ≤ᵐ[μ]
        (fun ω ↦ W ω / (W ω + δseq n) ^ 2) := by
      filter_upwards [hWpos] with ω hWω
      positivity
    have hlinEq :
        (∫⁻ ω, F n ω ∂μ) =
          ENNReal.ofReal c *
            ∫⁻ ω, ENNReal.ofReal
              (W ω / (W ω + δseq n) ^ 2) ∂μ := by
      dsimp only [F]
      rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnonneg,
        ← ofReal_integral_eq_lintegral_ofReal hgint hgnonneg,
        heq, ENNReal.ofReal_mul hc]
    rw [hlinEq]
    refine mul_le_mul' le_rfl ?_
    unfold ennInverseMoment
    apply lintegral_mono_ae
    filter_upwards [hWpos] with ω hWω
    apply ENNReal.ofReal_le_ofReal
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos (add_pos hWω (hδpos n))) hWω).2
    nlinarith [mul_pos hWω (hδpos n), sq_nonneg (δseq n)]
  have hliminfBound :
      liminf (fun n ↦ ∫⁻ ω, F n ω ∂μ) atTop ≤
        ENNReal.ofReal c * ennInverseMoment μ W := by
    exact Filter.liminf_le_of_frequently_le'
      (Filter.Frequently.of_forall hFbound)
  have hbase : ennInverseMoment μ V ≤
      ∫⁻ ω, ENNReal.ofReal (A ω / W ω ^ 2) ∂μ := by
    unfold ennInverseMoment
    apply lintegral_mono_ae
    filter_upwards [hVpos, hWpos, hquadratic] with ω hVω hWω hquad
    apply ENNReal.ofReal_le_ofReal
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hVω (sq_pos_of_pos hWω)).2
    simpa only [one_mul, mul_one, mul_comm] using hquad
  exact hbase.trans (hFatou.trans hliminfBound)

end Wishart

end

end LogdetLean.GramHafnian
