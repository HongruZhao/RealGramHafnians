import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.BoundedPreservedSScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericRegularizedRealifiedScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericHalfGaussianFullRank
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralRegularizedScoreTransport
/-!
# The literal conditional-Wishart inverse-moment step

This module specializes the bounded fixed-direction Stein--Haff identity to
the real and imaginary matrix units of the literal odd hafnian cofactor
vector, performs the finite rank-one assembly, and transports the resulting
regularized identity back to the iid circular past-column law.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- The generic real-Wishart residual degrees of freedom simplify to the
literal hafnian coefficient. -/
theorem oddCofactor_realWishart_residual_eq
    (k r : ℕ) (hr : 1 ≤ r) :
    (k : ℝ) - 2 * Fintype.card (OddCofactorIndex r hr) - 1 =
      (k : ℝ) - 4 * r + 1 := by
  rw [card_oddCofactorIndex]
  have htwo : 1 ≤ 2 * r := by omega
  rw [Nat.cast_sub htwo]
  push_cast
  ring

/-- All analytic score inputs imply the exact literal H2 inequality.  The
almost-sure full-rank premise is separated so that its Gaussian proof can be
reused independently of the score calculation. -/
theorem pastCofactorVInverseMoment_le_wishart_of_ae_full_rank
    (k r : ℕ) (hr : 1 ≤ r) (hk : 4 * r ≤ k)
    (hfull : ∀ᵐ R
        ∂halfGaussianMatrixSum k (OddCofactorIndex r hr),
      IsUnit (realWishartGram R).det) :
    pastCofactorVInverseMoment k r ≤
      pastCofactorWInverseMoment k r *
        ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹) := by
  let I := OddCofactorIndex r hr
  have hgap : Fintype.card (I ⊕ I) + 1 < k := by
    dsimp only [I]
    rw [Fintype.card_sum, card_oddCofactorIndex]
    omega
  have hcoeff : (k : ℝ) - 2 * Fintype.card I - 1 ≠ 0 := by
    rw [show (k : ℝ) - 2 * Fintype.card I - 1 =
        (k : ℝ) - 4 * r + 1 by
      simpa only [I] using oddCofactor_realWishart_residual_eq k r hr]
    have hkR : (4 : ℝ) * r ≤ k := by exact_mod_cast hk
    linarith
  apply pastCofactorVInverseMoment_le_of_realified_regularized_identity
    k r hr hk
  intro δ hδ
  have hRe (i j : I) :
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        rankOneRealCoordinateWeight
            (realifiedRegularizedCofactorWeight δ)
            realifiedCofactorVector i j R *
          (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
            Matrix.trace ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianRealCoordinateDirection i j))))
        (halfGaussianMatrixSum k I) ∧
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        rankOneRealCoordinateWeight
            (realifiedRegularizedCofactorWeight δ)
            realifiedCofactorVector i j R *
          Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)))
        (halfGaussianMatrixSum k I) ∧
      ((∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          rankOneRealCoordinateWeight
              (realifiedRegularizedCofactorWeight δ)
              realifiedCofactorVector i j R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace ((realWishartGram R)⁻¹ *
                scoreDeltaM (hermitianRealCoordinateDirection i j)))
          ∂halfGaussianMatrixSum k I) =
        ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          rankOneRealCoordinateWeight
              (realifiedRegularizedCofactorWeight δ)
              realifiedCofactorVector i j R *
            Matrix.trace
              (scoreDeltaM (hermitianRealCoordinateDirection i j))
          ∂halfGaussianMatrixSum k I) := by
    simpa only [rankOneRealCoordinateWeight_realified_fintype] using
      (bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
        (regularizedCofactorRealCoordinateWeight δ i j)
        (measurable_regularizedCofactorRealCoordinateWeight hδ i j)
        δ⁻¹ (abs_regularizedCofactorRealCoordinateWeight_le hδ i j)
        (hermitianRealCoordinateDirection_isHermitian i j) hgap)
  have hIm (i j : I) :
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        rankOneImagCoordinateWeight
            (realifiedRegularizedCofactorWeight δ)
            realifiedCofactorVector i j R *
          (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
            Matrix.trace ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianImagCoordinateDirection i j))))
        (halfGaussianMatrixSum k I) ∧
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        rankOneImagCoordinateWeight
            (realifiedRegularizedCofactorWeight δ)
            realifiedCofactorVector i j R *
          Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)))
        (halfGaussianMatrixSum k I) ∧
      ((∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          rankOneImagCoordinateWeight
              (realifiedRegularizedCofactorWeight δ)
              realifiedCofactorVector i j R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace ((realWishartGram R)⁻¹ *
                scoreDeltaM (hermitianImagCoordinateDirection i j)))
          ∂halfGaussianMatrixSum k I) =
        ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          rankOneImagCoordinateWeight
              (realifiedRegularizedCofactorWeight δ)
              realifiedCofactorVector i j R *
            Matrix.trace
              (scoreDeltaM (hermitianImagCoordinateDirection i j))
          ∂halfGaussianMatrixSum k I) := by
    simpa only [rankOneImagCoordinateWeight_realified_fintype] using
      (bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
        (regularizedCofactorImagCoordinateWeight δ i j)
        (measurable_regularizedCofactorImagCoordinateWeight hδ i j)
        δ⁻¹ (abs_regularizedCofactorImagCoordinateWeight_le hδ i j)
        (hermitianImagCoordinateDirection_isHermitian i j) hgap)
  have hscore :=
    regularized_coupled_score_of_coordinate_scores_fintype
      δ hfull
      (fun i j ↦ (hRe i j).1)
      (fun i j ↦ (hIm i j).1)
      (fun i j ↦ (hRe i j).2.1)
      (fun i j ↦ (hIm i j).2.1)
      (fun i j ↦ (hRe i j).2.2)
      (fun i j ↦ (hIm i j).2.2)
  have hA :=
    integrable_regularized_realifiedCoupledCofactorQuadratic_fintype
      δ hcoeff hfull
      (fun i j ↦ (hRe i j).1)
      (fun i j ↦ (hIm i j).1)
  have hW := integrable_regularized_realifiedCofactorW_fintype
      δ (fun i j ↦ (hRe i j).2.1) (fun i j ↦ (hIm i j).2.1)
  have heq := regularized_realified_integral_identity_fintype
    δ hcoeff hscore
  refine ⟨hA, hW, ?_⟩
  simpa only [I, oddCofactor_realWishart_residual_eq] using heq

/-- **Literal conditional-Wishart inverse-moment inequality (H2).**

For the exact iid circular past-column model used by the hafnian recurrence,
the inverse moment of the last-column conditional variance is bounded by the
inverse cofactor-energy moment with the sharp residual-degree coefficient.
Every hafnian-specific and analytic step is derived internally.  The
fixed-direction Stein--Haff identity is obtained from scalar half-Gaussian
integration by parts, deleted-coordinate full rank, and inverse-trace
integrability before the preserved-coordinate specialization is applied. -/
theorem pastCofactorVInverseMoment_le_wishart
    (k r : ℕ) (hr2 : 2 ≤ r) (hk : 4 * r ≤ k) :
    pastCofactorVInverseMoment k r ≤
      pastCofactorWInverseMoment k r *
        ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹) := by
  have hr : 1 ≤ r := by omega
  apply pastCofactorVInverseMoment_le_wishart_of_ae_full_rank k r hr hk
  apply ae_isUnit_det_realWishartGram_halfGaussianMatrixSum_generic
  rw [Fintype.card_sum, card_oddCofactorIndex]
  omega

end Wishart

end

end LogdetLean.GramHafnian
