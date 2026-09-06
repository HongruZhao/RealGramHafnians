import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.Multivariate
/-!
# A finite dimensional central limit theorem

This is the real-Hilbert-space CLT used by the fixed-degree real Gram-to-
symmetric-Gaussian limit.  It is copied into the present self-contained
project from the already audited complex symmetric-Gaussian limit package.
The moment hypotheses say that one summand is centered and isotropic.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace LogdetLean.GramHafnian.RealSymmetricGaussianLimit

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The normalized sum of the first `k` members of a sequence. -/
def normalizedPartialSum (X : ℕ → Omega → E) (k : ℕ) (omega : Omega) : E :=
  (√k)⁻¹ • ∑ a ∈ Finset.range k, X a omega

/-- Fixed dimensional CLT in an arbitrary finite dimensional real inner
product space. -/
theorem tendstoInDistribution_normalizedPartialSum_stdGaussian
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → E)
    (hX : ∀ a, AEMeasurable (X a) P)
    (hindep : iIndepFun X P)
    (hident : ∀ a, IdentDistrib (X a) (X 0) P P)
    (hmean : ∀ t : E, ∫ omega, inner ℝ t (X 0 omega) ∂P = 0)
    (hsecond : ∀ t : E, ∫ omega, inner ℝ t (X 0 omega) ^ 2 ∂P = ‖t‖ ^ 2) :
    TendstoInDistribution
      (normalizedPartialSum X) atTop id (fun _ ↦ P) (stdGaussian E) := by
  refine ⟨?_, by fun_prop, ?_⟩
  · intro k
    change AEMeasurable
      (fun omega ↦ (√k)⁻¹ • ∑ a ∈ Finset.range k, X a omega) P
    exact (Finset.aemeasurable_fun_sum (Finset.range k) fun a _ ↦ hX a).const_smul (√k)⁻¹
  · refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    by_cases ht : t = 0
    · subst t
      have hSn (k : ℕ) : AEMeasurable (normalizedPartialSum X k) P := by
        change AEMeasurable
          (fun omega ↦ (√k)⁻¹ • ∑ a ∈ Finset.range k, X a omega) P
        exact (Finset.aemeasurable_fun_sum (Finset.range k) fun a _ ↦ hX a).const_smul (√k)⁻¹
      letI (k : ℕ) : IsProbabilityMeasure (P.map (normalizedPartialSum X k)) :=
        Measure.isProbabilityMeasure_map (hSn k)
      simp
    simp only [ProbabilityMeasure.coe_mk, Measure.map_id]
    rw [charFun_stdGaussian]
    let u : E := ‖t‖⁻¹ • t
    have htNorm : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
    have huNorm : ‖u‖ = 1 := by
      simp [u, norm_smul, htNorm]
    have ht_eq : t = ‖t‖ • u := by
      simp [u, smul_smul, htNorm]
    let Y : Omega → ℝ := fun omega ↦ inner ℝ u (X 0 omega)
    have hYmeas : AEMeasurable Y P := by
      exact (by fun_prop : Continuous fun x : E ↦ inner ℝ u x).aemeasurable.comp_aemeasurable
        (hX 0)
    have hYmean : ∫ omega, Y omega ∂P = 0 := by
      simpa [Y] using hmean u
    have hYsecond : ∫ omega, Y omega ^ 2 ∂P = 1 := by
      simpa [Y, huNorm] using hsecond u
    have hscalar := tendsto_charFun_inv_sqrt_mul_pow
      hYmeas hYmean hYsecond ‖t‖
    have heq :
        (fun k ↦ charFun (P.map (normalizedPartialSum X k)) t) =
          (fun k : ℕ ↦ charFun (P.map Y) ((√k)⁻¹ * ‖t‖) ^ k) := by
      funext k
      unfold normalizedPartialSum
      have hsum : AEMeasurable
          (fun omega ↦ ∑ a ∈ Finset.range k, X a omega) P :=
        Finset.aemeasurable_fun_sum _ fun a _ ↦ hX a
      rw [charFun_map_smul_comp hsum]
      rw [(hindep.restrict (Finset.range k)).charFun_map_fun_finsetSum_eq_prod
        (fun a _ ↦ hX a)]
      simp_rw [(hident _).map_eq]
      rw [Finset.prod_const, Finset.card_range]
      simp only [Pi.pow_apply]
      congr 1
      have harg : (√k)⁻¹ • t = (((√k)⁻¹ * ‖t‖) • u) := by
        calc
          (√k)⁻¹ • t = (√k)⁻¹ • (‖t‖ • u) := congrArg ((√k)⁻¹ • ·) ht_eq
          _ = ((√k)⁻¹ * ‖t‖) • u := by rw [smul_smul]
      rw [harg]
      change charFun (P.map (X 0)) (((√k)⁻¹ * ‖t‖) • u) = _
      rw [charFun_apply, charFun_apply, integral_map (hX 0), integral_map hYmeas]
      all_goals try fun_prop
      simp only [Y, real_inner_smul_right, RCLike.inner_apply, conj_trivial,
        real_inner_comm (X 0 _) u]
    rw [heq]
    exact hscalar

end

end LogdetLean.GramHafnian.RealSymmetricGaussianLimit
