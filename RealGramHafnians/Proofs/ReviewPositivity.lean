import RealGramHafnians.Proofs.ReviewLaplacePositivity
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian.Review
noncomputable section
set_option maxHeartbeats 1000000

/-- Positivity sufficient for the enlarged theorem. The formal proof uses
Laplace comparison, independently of the polynomial argument in the text. -/
theorem ae_pastRealCofactorV_pos_standardRealGaussian
    {r k : ℕ} (hr : 1 ≤ r) (hk : r ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k), 0 < pastRealCofactorV hr A := by
  induction r using Nat.strong_induction_on generalizing k with
  | h r ih =>
    by_cases hr1 : r = 1
    · subst r
      exact LogdetLean.GramHafnian.ae_pastRealCofactorV_pos_standardRealGaussian hr
        (by omega)
    have hr2 : 2 ≤ r := by omega
    have hk2 : 2 ≤ k := by omega
    have hrl : 1 ≤ r - 1 := by omega
    let ν₀ := Measure.pi fun _ : OddCofactorIndex (r - 1) hrl ↦
      standardRealGaussianVectorMeasure (k - 1)
    let ν := ν₀.prod (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))
    let μ := finiteRealGramCofactorCombinationEuclideanLaw (2 * r - 1) k
    let V := rowSuspensionLowerProductVariance (k := k - 1) hr2
    have hlow : ∀ᵐ A ∂ν₀, 0 < pastRealCofactorV hrl A :=
      ih (r - 1) (by omega) hrl (by omega)
    have hVp : ∀ᵐ p ∂ν, 0 < V p := by
      have hA := (Measure.quasiMeasurePreserving_fst (μ := ν₀)
        (ν := stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))).ae hlow
      have hG : ∀ᵐ g ∂(stdGaussian (RealGaussianEuclideanSpace (2 * r - 1))), g ≠ 0 := by
        let _ : Nonempty (Fin (2 * r - 1)) := Fin.pos_iff_nonempty.mp (by omega)
        let _ : Nontrivial (RealGaussianEuclideanSpace (2 * r - 1)) := inferInstance
        simpa [ae_iff] using LogdetLean.stdGaussian_zero_singleton
          (E := RealGaussianEuclideanSpace (2 * r - 1))
      have hB := (Measure.quasiMeasurePreserving_snd (μ := ν₀)
        (ν := stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))).ae hG
      filter_upwards [hA, hB] with p hp hq
      exact mul_pos hp (by dsimp [realAuxiliaryNormSq]; positivity)
    have hc : ∀ ξ : RealGaussianEuclideanSpace k,
        (charFun μ ξ).re ≤ ∫ p, Real.exp (-(V p * ‖ξ‖ ^ 2) / 2) ∂ν := by
      have hh := physicalCofactorCombination_charFun_re_le_rowSuspension_product
        (k := k - 1) (by omega) hr2
      have heq : k - 1 + 1 = k := by omega
      rw [heq] at hh
      exact hh
    have hprod : ∀ᵐ p ∂(ν.prod (stdGaussian (RealGaussianEuclideanSpace k))),
        0 < V p.1 * realAuxiliaryNormSq p.2 := by
      have hA := (Measure.quasiMeasurePreserving_fst (μ := ν)
        (ν := stdGaussian (RealGaussianEuclideanSpace k))).ae hVp
      have hG : ∀ᵐ g ∂(stdGaussian (RealGaussianEuclideanSpace k)), g ≠ 0 := by
        let _ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
        let _ : Nontrivial (RealGaussianEuclideanSpace k) := inferInstance
        simpa [ae_iff] using LogdetLean.stdGaussian_zero_singleton
          (E := RealGaussianEuclideanSpace k)
      have hB := (Measure.quasiMeasurePreserving_snd (μ := ν)
        (ν := stdGaussian (RealGaussianEuclideanSpace k))).ae hG
      filter_upwards [hA, hB] with p hp hq
      exact mul_pos hp (by dsimp [realAuxiliaryNormSq]; positivity)
    have hpos : ∀ᵐ x ∂μ, 0 < ‖x‖ ^ 2 := by
      apply review_ae_pos_of_laplace_le μ
        (ν.prod (stdGaussian (RealGaussianEuclideanSpace k)))
        (fun x ↦ ‖x‖ ^ 2) (fun p ↦ V p.1 * realAuxiliaryNormSq p.2)
        (by fun_prop) (by dsimp [V]; fun_prop)
        (fun _ ↦ sq_nonneg _) (fun p ↦ mul_nonneg
          (rowSuspensionLowerProductVariance_nonneg hr2 p.1) (sq_nonneg _)) hprod
      intro t ht
      exact ennLaplace_norm_sq_le_mul_realAuxiliaryNormSq_of_compression μ ν V
        (measurable_rowSuspensionLowerProductVariance hr2)
        (rowSuspensionLowerProductVariance_nonneg hr2) hc t ht
    rw [show μ = pastRealCofactorCombinationEuclideanLaw r k hr from
      finiteRealGramCofactorCombinationEuclideanLaw_eq_literal r k hr] at hpos
    have hpull := (ae_map_iff
      (measurable_pastRealCofactorCombinationEuclidean hr).aemeasurable
      (measurableSet_lt measurable_const (by fun_prop))).mp hpos
    simpa [norm_sq_pastRealCofactorCombinationEuclidean] using hpull

end
end LogdetLean.GramHafnian.Review
