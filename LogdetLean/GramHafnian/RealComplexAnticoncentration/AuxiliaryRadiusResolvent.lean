import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealFourierGammaFactor
import Mathlib.MeasureTheory.Integral.Prod
/-!
# Thresholding the auxiliary chi-square radius

The beta-one Fourier step introduces an independent standard real Gaussian
radius.  Thresholding that radius converts the product resolvent back to the
lower-level energy resolvent, paying only the lower-tail probability of the
chi-square radius.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A product with an independent real Gaussian radius is controlled by a
rescaled base resolvent plus the radius lower-tail probability. -/
theorem ennHalfResolvent_mul_realAuxiliaryNormSq_le_threshold
    {d : ℕ}
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (a lambda : ℝ) (ha : 0 < a) (hlambda : 0 < lambda) :
    ennHalfResolvent
        (nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
        (fun p ↦ V p.1 * realAuxiliaryNormSq p.2) lambda ≤
      ennHalfResolvent nu V (lambda / a) +
        (stdGaussian (RealGaussianEuclideanSpace d))
          {g | realAuxiliaryNormSq g < a} := by
  let gamma := stdGaussian (RealGaussianEuclideanSpace d)
  let s : Set (Omega × RealGaussianEuclideanSpace d) :=
    {p | a ≤ realAuxiliaryNormSq p.2}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_le measurable_const
      (measurable_realAuxiliaryNormSq.comp measurable_snd)
  have hsplit := ennHalfResolvent_le_rescaled_add_compl
    (mu := nu.prod gamma)
    (U := fun p : Omega × RealGaussianEuclideanSpace d ↦
      V p.1 * realAuxiliaryNormSq p.2)
    (W := fun p : Omega × RealGaussianEuclideanSpace d ↦ V p.1)
    (by fun_prop) (by fun_prop) s hs
    (Filter.Eventually.of_forall fun p ↦
      mul_nonneg (hVnonneg p.1) (sq_nonneg _))
    (Filter.Eventually.of_forall fun p ↦ hVnonneg p.1)
    a lambda ha hlambda (Filter.Eventually.of_forall fun p hp ↦ by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left hp (hVnonneg p.1)))
  have hfst :
      ennHalfResolvent (nu.prod gamma)
          (fun p : Omega × RealGaussianEuclideanSpace d ↦ V p.1)
          (lambda / a) =
        ennHalfResolvent nu V (lambda / a) := by
    unfold ennHalfResolvent
    rw [lintegral_prod _ (by fun_prop)]
    simp [gamma]
  have hcompl :
      (nu.prod gamma) sᶜ =
        gamma {g | realAuxiliaryNormSq g < a} := by
    have hscompl : MeasurableSet sᶜ := hs.compl
    rw [Measure.prod_apply hscompl]
    have hsection : ∀ w : Omega,
        (Prod.mk w ⁻¹' sᶜ) =
          {g : RealGaussianEuclideanSpace d |
            realAuxiliaryNormSq g < a} := by
      intro w
      ext g
      simp [s]
    simp_rw [hsection]
    simp [gamma]
  simpa only [hfst, hcompl, gamma] using hsplit

/-- End-to-end bounded-resolvent consequence of a beta-one radial Fourier
majorant, after thresholding the independent auxiliary radius. -/
theorem ennHalfResolvent_norm_sq_le_threshold_of_compression
    {d : ℕ}
    (mu : Measure (RealGaussianEuclideanSpace d)) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hcompression : ∀ xi : RealGaussianEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 2) ∂nu)
    (a lambda : ℝ) (ha : 0 < a) (hlambda : 0 < lambda) :
    ennHalfResolvent mu (fun x ↦ ‖x‖ ^ 2) lambda ≤
      ennHalfResolvent nu V (lambda / a) +
        (stdGaussian (RealGaussianEuclideanSpace d))
          {g | realAuxiliaryNormSq g < a} := by
  exact (ennHalfResolvent_norm_sq_le_mul_realAuxiliaryNormSq_of_compression
      mu nu V hV hVnonneg hcompression lambda hlambda).trans
    (ennHalfResolvent_mul_realAuxiliaryNormSq_le_threshold
      nu V hV hVnonneg a lambda ha hlambda)

end

end LogdetLean.GramHafnian
