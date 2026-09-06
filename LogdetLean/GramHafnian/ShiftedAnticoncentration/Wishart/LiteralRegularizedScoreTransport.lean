import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralRegularizedLimit
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RegularizedRealifiedScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralPastRealification
/-!
# Transporting the regularized realified score to literal past columns

The iid circular past-column law maps exactly to the split half-Gaussian
realification.  This module identifies all three scalar integrands and
transports their integrability and integral equality back to the literal
probability space.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

@[simp] theorem realifiedCofactorVector_pastRealifiedMatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    realifiedCofactorVector (pastRealifiedMatrix hr A) =
      pastHafnianCofactorVector hr A := by
  exact (pastHafnianCofactorVector_eq_preservedRealGram hr A).symm

@[simp] theorem realifiedCofactorW_pastRealifiedMatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    realifiedCofactorW (pastRealifiedMatrix hr A) =
      pastCofactorW hr A := by
  exact (pastCofactorW_eq_preservedRealGram hr A).symm

@[simp] theorem realifiedCoupledCofactorQuadratic_pastRealifiedMatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    realifiedCoupledCofactorQuadratic (pastRealifiedMatrix hr A) =
      pastCoupledInverseQuadratic hr A := by
  unfold realifiedCoupledCofactorQuadratic pastCoupledInverseQuadratic
  rw [complexOfRealMatrix_pastRealifiedMatrix,
    realifiedCofactorVector_pastRealifiedMatrix]
  rfl

@[simp] theorem realifiedRegularizedCofactorWeight_pastRealifiedMatrix
    {r k : ℕ} (hr : 1 ≤ r) (δ : ℝ)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    realifiedRegularizedCofactorWeight δ (pastRealifiedMatrix hr A) =
      (pastCofactorW hr A + δ)⁻¹ ^ 2 := by
  change (realifiedCofactorW (pastRealifiedMatrix hr A) + δ)⁻¹ ^ 2 = _
  rw [realifiedCofactorW_pastRealifiedMatrix]

/-- One regularized identity on the split real matrix law transports
verbatim to the literal circular past-column law. -/
theorem literal_regularized_score_data_of_realified
    {r k : ℕ} (hr : 1 ≤ r) (δ c : ℝ)
    (hAint : Integrable (fun R : Matrix (Fin k)
        (OddCofactorIndex r hr ⊕ OddCofactorIndex r hr) ℝ ↦
      realifiedCoupledCofactorQuadratic R /
        (realifiedCofactorW R + δ) ^ 2)
      (halfGaussianMatrixSum k (OddCofactorIndex r hr)))
    (hWint : Integrable (fun R : Matrix (Fin k)
        (OddCofactorIndex r hr ⊕ OddCofactorIndex r hr) ℝ ↦
      realifiedCofactorW R / (realifiedCofactorW R + δ) ^ 2)
      (halfGaussianMatrixSum k (OddCofactorIndex r hr)))
    (heq :
      (∫ R, realifiedCoupledCofactorQuadratic R /
          (realifiedCofactorW R + δ) ^ 2
          ∂halfGaussianMatrixSum k (OddCofactorIndex r hr)) =
        c * ∫ R, realifiedCofactorW R /
          (realifiedCofactorW R + δ) ^ 2
          ∂halfGaussianMatrixSum k (OddCofactorIndex r hr)) :
    let μ := Measure.pi fun _ : OddCofactorIndex r hr ↦
      circularGaussianVector k
    Integrable (fun A ↦ pastCoupledInverseQuadratic hr A /
      (pastCofactorW hr A + δ) ^ 2) μ ∧
    Integrable (fun A ↦ pastCofactorW hr A /
      (pastCofactorW hr A + δ) ^ 2) μ ∧
    (∫ A, pastCoupledInverseQuadratic hr A /
        (pastCofactorW hr A + δ) ^ 2 ∂μ) =
      c * ∫ A, pastCofactorW hr A /
        (pastCofactorW hr A + δ) ^ 2 ∂μ := by
  dsimp only
  let f : Matrix (Fin k)
      (OddCofactorIndex r hr ⊕ OddCofactorIndex r hr) ℝ → ℝ := fun R ↦
    realifiedCoupledCofactorQuadratic R /
      (realifiedCofactorW R + δ) ^ 2
  let g : Matrix (Fin k)
      (OddCofactorIndex r hr ⊕ OddCofactorIndex r hr) ℝ → ℝ := fun R ↦
    realifiedCofactorW R / (realifiedCofactorW R + δ) ^ 2
  let μ := Measure.pi fun _ : OddCofactorIndex r hr ↦
    circularGaussianVector k
  have hmp := measurePreserving_pastRealifiedMatrix (n := k) hr
  have hfcomp : Integrable (fun A ↦ f (pastRealifiedMatrix hr A)) μ :=
    hmp.integrable_comp_of_integrable hAint
  have hgcomp : Integrable (fun A ↦ g (pastRealifiedMatrix hr A)) μ :=
    hmp.integrable_comp_of_integrable hWint
  have hf : Integrable (fun A ↦ pastCoupledInverseQuadratic hr A /
      (pastCofactorW hr A + δ) ^ 2) μ := by
    apply hfcomp.congr
    filter_upwards [] with A
    simp [f]
  have hg : Integrable (fun A ↦ pastCofactorW hr A /
      (pastCofactorW hr A + δ) ^ 2) μ := by
    apply hgcomp.congr
    filter_upwards [] with A
    simp [g]
  refine ⟨hf, hg, ?_⟩
  calc
    (∫ A, pastCoupledInverseQuadratic hr A /
        (pastCofactorW hr A + δ) ^ 2 ∂μ) =
        ∫ A, f (pastRealifiedMatrix hr A) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with A
      simp [f]
    _ = ∫ R, f R
        ∂halfGaussianMatrixSum k (OddCofactorIndex r hr) :=
      hmp.integral_comp' f
    _ = c * ∫ R, g R
        ∂halfGaussianMatrixSum k (OddCofactorIndex r hr) := heq
    _ = c * ∫ A, g (complexColumnsRealification k A) ∂μ := by
      congr 1
      simpa [complexColumnsRealificationMeasurableEquiv] using
        (hmp.integral_comp' g).symm
    _ = c * ∫ A, g (pastRealifiedMatrix hr A) ∂μ := rfl
    _ = c * ∫ A, pastCofactorW hr A /
        (pastCofactorW hr A + δ) ^ 2 ∂μ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with A
      simp [g]

/-- Public literal H2 follows once the regularized score data have been
proved on the exact split realification law. -/
theorem pastCofactorVInverseMoment_le_of_realified_regularized_identity
    (k r : ℕ) (hr : 1 ≤ r) (hk : 4 * r ≤ k)
    (hregularized : ∀ δ : ℝ, 0 < δ →
      Integrable (fun R : Matrix (Fin k)
          (OddCofactorIndex r hr ⊕ OddCofactorIndex r hr) ℝ ↦
        realifiedCoupledCofactorQuadratic R /
          (realifiedCofactorW R + δ) ^ 2)
        (halfGaussianMatrixSum k (OddCofactorIndex r hr)) ∧
      Integrable (fun R : Matrix (Fin k)
          (OddCofactorIndex r hr ⊕ OddCofactorIndex r hr) ℝ ↦
        realifiedCofactorW R / (realifiedCofactorW R + δ) ^ 2)
        (halfGaussianMatrixSum k (OddCofactorIndex r hr)) ∧
      (∫ R, realifiedCoupledCofactorQuadratic R /
          (realifiedCofactorW R + δ) ^ 2
          ∂halfGaussianMatrixSum k (OddCofactorIndex r hr)) =
        (((k : ℝ) - 4 * r + 1)⁻¹) *
          ∫ R, realifiedCofactorW R /
            (realifiedCofactorW R + δ) ^ 2
            ∂halfGaussianMatrixSum k (OddCofactorIndex r hr)) :
    pastCofactorVInverseMoment k r ≤
      pastCofactorWInverseMoment k r *
        ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹) := by
  apply pastCofactorVInverseMoment_le_of_regularized_coupled_identity
    k r hr hk
  intro δ hδ
  obtain ⟨hA, hW, heq⟩ := hregularized δ hδ
  exact literal_regularized_score_data_of_realified hr δ
    (((k : ℝ) - 4 * r + 1)⁻¹) hA hW heq

end Wishart

end

end LogdetLean.GramHafnian
