import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealFourierGammaFactor
import Mathlib.MeasureTheory.Integral.Prod
/-!
# Exact auxiliary-Gamma transfer for beta one

The real Fourier step introduces an independent chi-square radius.  This
file integrates that radius exactly, without thresholding it.  Its main
theorem propagates an affine `sqrt lambda` envelope for the half-resolvent;
the constant term is unchanged and the square-root coefficient acquires
the exact negative-half Gamma moment.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The exact negative-half moment of a chi-square variable of dimension
`d`, in the scale convention used by `stdGaussian`. -/
def realAuxiliaryGammaHalfFactor (d : ℕ) : ENNReal :=
  ENNReal.ofReal
    ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) *
      Real.Gamma (((d : ℝ) - 1) / 2) /
      Real.Gamma ((d : ℝ) / 2))

theorem lintegral_inv_sqrt_realAuxiliaryNormSq_stdGaussian_eq_factor
    {d : ℕ} (hd : 2 ≤ d) :
    ∫⁻ g : RealGaussianEuclideanSpace d,
        ENNReal.ofReal (Real.sqrt (realAuxiliaryNormSq g))⁻¹
          ∂(stdGaussian (RealGaussianEuclideanSpace d)) =
      realAuxiliaryGammaHalfFactor d := by
  exact lintegral_inv_sqrt_realAuxiliaryNormSq_stdGaussian hd

/-- For a positive auxiliary radius, multiplying the energy by that radius
can only rescale the spectral parameter by its reciprocal. -/
theorem ennHalfResolventKernel_mul_le_div
    {lambda x g : ℝ} (hlambda : 0 < lambda) (hx : 0 ≤ x) (hg : 0 < g) :
    ennHalfResolventKernel lambda (x * g) ≤
      ennHalfResolventKernel (lambda / g) x := by
  exact ennHalfResolventKernel_le_of_mul_le
    hlambda hg (mul_nonneg hx hg.le) hx (by simpa [mul_comm])

/-- Exact square-root rescaling identity in `ENNReal`. -/
theorem ennreal_ofReal_sqrt_div
    {lambda g : ℝ} (hlambda : 0 < lambda) (hg : 0 < g) :
    ENNReal.ofReal (Real.sqrt (lambda / g)) =
      ENNReal.ofReal (Real.sqrt lambda) *
        ENNReal.ofReal (Real.sqrt g)⁻¹ := by
  rw [Real.sqrt_div hlambda.le]
  rw [ENNReal.ofReal_div_of_pos (Real.sqrt_pos.2 hg)]
  rw [div_eq_mul_inv]
  rw [ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 hg)]

/-- Integrating the independent auxiliary radius propagates an affine
`sqrt lambda` envelope and multiplies only its square-root coefficient by
the exact chi-square negative-half moment.  There is no auxiliary-radius
bad event in this statement. -/
theorem ennHalfResolvent_mul_realAuxiliaryNormSq_le_of_sqrt_envelope
    {d : ℕ} (hd : 2 ≤ d)
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (E C : ENNReal)
    (henvelope : ∀ t : ℝ, 0 < t →
      ennHalfResolvent nu V t ≤
        E + C * ENNReal.ofReal (Real.sqrt t))
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ennHalfResolvent
        (nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
        (fun p ↦ V p.1 * realAuxiliaryNormSq p.2) lambda ≤
      E + C * ENNReal.ofReal (Real.sqrt lambda) *
        realAuxiliaryGammaHalfFactor d := by
  let gamma := stdGaussian (RealGaussianEuclideanSpace d)
  have hGpos : ∀ᵐ g ∂gamma, 0 < realAuxiliaryNormSq g := by
    let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
    let _ : Nontrivial (RealGaussianEuclideanSpace d) := inferInstance
    have hne : ∀ᵐ g ∂gamma, g ≠ 0 := by
      simpa [gamma, ae_iff] using
        LogdetLean.stdGaussian_zero_singleton
          (E := RealGaussianEuclideanSpace d)
    filter_upwards [hne] with g hg
    unfold realAuxiliaryNormSq
    positivity
  unfold ennHalfResolvent
  rw [lintegral_prod_symm' _ (by fun_prop)]
  calc
    (∫⁻ g, ∫⁻ w, ennHalfResolventKernel lambda
          (V w * realAuxiliaryNormSq g) ∂nu ∂gamma) ≤
        ∫⁻ g, E + C * ENNReal.ofReal
          (Real.sqrt (lambda / realAuxiliaryNormSq g)) ∂gamma := by
      apply lintegral_mono_ae
      filter_upwards [hGpos] with g hg
      calc
        (∫⁻ w, ennHalfResolventKernel lambda
              (V w * realAuxiliaryNormSq g) ∂nu) ≤
            ∫⁻ w, ennHalfResolventKernel
              (lambda / realAuxiliaryNormSq g) (V w) ∂nu := by
          apply lintegral_mono
          intro w
          exact ennHalfResolventKernel_mul_le_div
            hlambda (hVnonneg w) hg
        _ = ennHalfResolvent nu V
              (lambda / realAuxiliaryNormSq g) := rfl
        _ ≤ E + C * ENNReal.ofReal
              (Real.sqrt (lambda / realAuxiliaryNormSq g)) :=
          henvelope _ (div_pos hlambda hg)
    _ = ∫⁻ g, E + C * ENNReal.ofReal (Real.sqrt lambda) *
          ENNReal.ofReal (Real.sqrt (realAuxiliaryNormSq g))⁻¹
          ∂gamma := by
      apply lintegral_congr_ae
      filter_upwards [hGpos] with g hg
      rw [ennreal_ofReal_sqrt_div hlambda hg]
      ac_rfl
    _ = E + C * ENNReal.ofReal (Real.sqrt lambda) *
          realAuxiliaryGammaHalfFactor d := by
      rw [lintegral_add_left (by fun_prop)]
      rw [lintegral_const_mul]
      · simp only [lintegral_const, measure_univ, mul_one]
        rw [lintegral_inv_sqrt_realAuxiliaryNormSq_stdGaussian_eq_factor hd]
      · fun_prop

end

end LogdetLean.GramHafnian
