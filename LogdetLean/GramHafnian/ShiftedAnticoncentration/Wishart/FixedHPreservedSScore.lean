import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.PreservedSWeight
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SumColumnScoreTransport
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.InverseTraceIntegrability
/-!
# Fixed-direction preserved-coordinate Wishart score

This file packages the exact fixed-H score wrapper used by the conditional
Wishart argument, and records full rank and inverse-trace integrability for
the split (`I ⊕ I`) column Gaussian law.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- A differentiable scalar test of the preserved complex coordinate plugs
directly into the fixed-H integrated score theorem. -/
theorem integral_preservedSWeight_inverseGram_scoreDelta_eq
    {k m : Type*} [Fintype k] [Fintype m]
    [DecidableEq k] [DecidableEq m]
    [MeasurableSpace (Matrix k (m ⊕ m) ℝ)]
    (μ : Measure (Matrix k (m ⊕ m) ℝ))
    (psi : Matrix m m ℂ → ℝ)
    (dpsi : Matrix m m ℂ → Matrix m m ℂ →L[ℝ] ℝ)
    (hpsi : ∀ S, HasFDerivAt psi (dpsi S) S)
    {H : Matrix m m ℂ} (hH : H.IsHermitian)
    (hfull : ∀ᵐ R ∂μ, IsUnit (realWishartGram R).det)
    (hIBP :
      (∫ R, weightedSteinCoordinateDivergence
          (preservedSWeight psi) R (scoreDeltaM H) ∂μ) =
        ∫ R, 2 * realFrobeniusInner R
          (preservedSWeight psi R •
            steinVectorFieldValue R (scoreDeltaM H)) ∂μ) :
    (∫ R, preservedSWeight psi R *
        (inverseGramScoreCoefficient k (m ⊕ m) *
          Matrix.trace
            ((realWishartGram R)⁻¹ * scoreDeltaM H)) ∂μ) =
      ∫ R, preservedSWeight psi R *
        Matrix.trace (scoreDeltaM H) ∂μ := by
  apply integral_preservedS_inverseGram_scoreDelta_eq
    μ (preservedSWeight psi) (preservedSWeightDerivative dpsi)
    (fun R ↦ dpsi (preservedSCoordinate R)) hH
  · exact hasFDerivAt_preservedSWeight psi dpsi hpsi
  · intro R F
    exact preservedSWeightDerivative_factor dpsi R F
  · exact hfull
  · exact hIBP

/-- The split-column half-Gaussian matrix has full column rank almost
surely whenever the number of real columns does not exceed the row count. -/
theorem ae_isUnit_det_realWishartGram_halfGaussianMatrixSum
    (k m : ℕ) (hkm : 2 * m ≤ k) :
    ∀ᵐ R ∂halfGaussianMatrixSum k (Fin m),
      IsUnit (realWishartGram R).det := by
  let e := sumColumnsToFinMeasurableEquiv k m
  have hnum : ∀ᵐ R ∂halfGaussianMatrix k (2 * m),
      IsUnit (realWishartGram R).det :=
    ae_isUnit_det_realWishartGram_halfGaussianMatrix k (2 * m) hkm
  have hpull :=
    (measurePreserving_sumColumnsToFin_halfGaussianMatrixSum k m).quasiMeasurePreserving.ae
      hnum
  filter_upwards [hpull] with R hR
  apply (isUnit_det_realWishartGram_reindexSplitColumns_iff R).mp
  simpa [reindexSplitColumns_eq_sumColumnsToFin] using hR

/-- First inverse-Wishart trace integrability transported from numeric
`Fin (2*m)` columns to the split-column law. -/
theorem integrable_trace_nonsingInv_realWishartGram_halfGaussianMatrixSum
    {k m : ℕ} (hgap : 2 * m + 1 < k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        Matrix.trace (realWishartGram R)⁻¹)
      (halfGaussianMatrixSum k (Fin m)) := by
  have hnum :=
    integrable_trace_nonsingInv_realWishartGram_halfGaussianMatrix hgap
  have hpull :=
    (measurePreserving_sumColumnsToFin_halfGaussianMatrixSum k m).integrable_comp_of_integrable
      hnum
  apply hpull.congr
  filter_upwards [] with R
  change Matrix.trace
      (realWishartGram (reindexSplitColumns k m R))⁻¹ =
    Matrix.trace (realWishartGram R)⁻¹
  rw [realWishartGram_reindexSplitColumns,
    inv_reindexSplitSquare, trace_reindexSplitSquare]

/-- Sum-column specialization of the preserved-S fixed-H score wrapper.
Only the genuine Gaussian divergence identity remains as an analytic
premise. -/
theorem integral_preservedSWeight_inverseGram_scoreDelta_halfGaussianMatrixSum
    {k m : ℕ}
    (psi : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (dpsi : Matrix (Fin m) (Fin m) ℂ →
      Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℝ)
    (hpsi : ∀ S, HasFDerivAt psi (dpsi S) S)
    {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (hgap : 2 * m < k)
    (hIBP :
      (∫ R, weightedSteinCoordinateDivergence
          (preservedSWeight psi) R (scoreDeltaM H)
          ∂halfGaussianMatrixSum k (Fin m)) =
        ∫ R, 2 * realFrobeniusInner R
          (preservedSWeight psi R •
            steinVectorFieldValue R (scoreDeltaM H))
          ∂halfGaussianMatrixSum k (Fin m)) :
    (∫ R, preservedSWeight psi R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace
            ((realWishartGram R)⁻¹ * scoreDeltaM H))
        ∂halfGaussianMatrixSum k (Fin m)) =
      ∫ R, preservedSWeight psi R *
        Matrix.trace (scoreDeltaM H)
        ∂halfGaussianMatrixSum k (Fin m) := by
  apply integral_preservedSWeight_inverseGram_scoreDelta_eq
    (halfGaussianMatrixSum k (Fin m)) psi dpsi hpsi hH
  · exact ae_isUnit_det_realWishartGram_halfGaussianMatrixSum
      k m (by omega)
  · exact hIBP

end Wishart

end

end LogdetLean.GramHafnian
