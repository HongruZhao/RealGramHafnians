import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.GammaFactor
/-!
# Inverse-moment recurrence from Fourier coordinate compression

This file combines the auxiliary-Gaussian Fourier-to-Laplace comparison
with the exact inverse moment of the auxiliary `Gamma(d,1)` radius.  It is
the analytic interface used at each odd-hafnian cofactor level.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- If the characteristic function of an `E = ℂ^d`-valued random vector is
radially dominated by the Gaussian mixture with variance variable `V`, then
its inverse squared-norm moment is at most `1 / (d - 1)` times the inverse
moment of `V`.  The factor is exact: it is the inverse moment of an
independent `Gamma(d,1)` variable. -/
theorem ennInverse_norm_sq_le_auxiliaryGamma_factor
    {d : ℕ} (hd : 2 ≤ d)
    (mu : Measure (CircularEuclideanSpace d)) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega -> ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (hcompression : ∀ xi : CircularEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 4) ∂nu)
    (hnormpos : ∀ᵐ x ∂mu, 0 < ‖x‖ ^ 2) :
    ennInverseMoment mu (fun x => ‖x‖ ^ 2) ≤
      ennInverseMoment nu V * ENNReal.ofReal ((d : ℝ) - 1)⁻¹ := by
  have hVpos_prod :
      ∀ᵐ p ∂(nu.prod (stdGaussian (CircularEuclideanSpace d))),
        0 < V p.1 := by
    exact (Measure.quasiMeasurePreserving_fst
      (μ := nu) (ν := stdGaussian (CircularEuclideanSpace d))).ae hVpos
  have hGpos_prod :
      ∀ᵐ p ∂(nu.prod (stdGaussian (CircularEuclideanSpace d))),
        0 < auxiliaryGammaRadius p.2 := by
    exact (Measure.quasiMeasurePreserving_snd
      (μ := nu) (ν := stdGaussian (CircularEuclideanSpace d))).ae
        (auxiliaryGammaRadius_pos_ae (show 0 < d by omega))
  have hprodpos :
      ∀ᵐ p ∂(nu.prod (stdGaussian (CircularEuclideanSpace d))),
        0 < V p.1 * ‖p.2‖ ^ 2 / 2 := by
    filter_upwards [hVpos_prod, hGpos_prod] with p hpV hpG
    rw [show V p.1 * ‖p.2‖ ^ 2 / 2 =
      V p.1 * auxiliaryGammaRadius p.2 by
        unfold auxiliaryGammaRadius
        ring]
    exact mul_pos hpV hpG
  calc
    ennInverseMoment mu (fun x => ‖x‖ ^ 2) ≤
        ennInverseMoment
          (nu.prod (stdGaussian (CircularEuclideanSpace d)))
          (fun p => V p.1 * ‖p.2‖ ^ 2 / 2) :=
      ennInverse_norm_sq_le_prod_of_charFun_compression
        mu nu V hV hVnonneg hcompression hnormpos hprodpos
    _ = ennInverseMoment nu V *
        ENNReal.ofReal ((d : ℝ) - 1)⁻¹ := by
      convert ennInverseMoment_mul_auxiliaryGammaRadius
        nu V hV hVnonneg hd using 1 <;>
        simp only [auxiliaryGammaRadius] <;> ring

end

end LogdetLean.GramHafnian
