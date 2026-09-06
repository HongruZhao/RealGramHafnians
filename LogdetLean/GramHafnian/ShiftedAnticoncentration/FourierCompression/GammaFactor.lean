import LogdetLean.GaussianSubspace
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.AuxiliaryAveraging
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianNormGamma
/-!
# Exact auxiliary-Gaussian inverse factor

For a real standard Gaussian on a complex Euclidean space of complex
dimension `d`, the paper's radial variable is `||g||^2 / 2`, hence has the
rate-one `Gamma(d,1)` law.  This file proves the exact inverse moment and its
Tonelli factorization against an arbitrary independent nonnegative random
variable.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The auxiliary radial variable in complex dimension `d`. -/
def auxiliaryGammaRadius {d : ℕ} (g : CircularEuclideanSpace d) : ℝ :=
  ‖g‖ ^ 2 / 2

@[fun_prop]
theorem measurable_auxiliaryGammaRadius {d : ℕ} :
    Measurable (auxiliaryGammaRadius (d := d)) := by
  unfold auxiliaryGammaRadius
  fun_prop

theorem integral_inv_auxiliaryGammaRadius_stdGaussian
    {d : ℕ} (hd : 2 ≤ d) :
    ∫ g : CircularEuclideanSpace d,
        (auxiliaryGammaRadius g)⁻¹ ∂(stdGaussian (CircularEuclideanSpace d)) =
      ((d : ℝ) - 1)⁻¹ := by
  have hcirc := integral_inv_circularVectorNormSq_iid_circular hd
  rw [map_toLp_pi_circularGaussian_eq_scaled_stdGaussian] at hcirc
  rw [integral_map (measurable_const_smul ((Real.sqrt 2)⁻¹ : ℝ)).aemeasurable
      (by fun_prop)] at hcirc
  rw [← hcirc]
  apply integral_congr_ae
  filter_upwards [] with g
  unfold auxiliaryGammaRadius circularVectorNormSq
  rw [norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)),
    mul_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem integrable_inv_auxiliaryGammaRadius_stdGaussian
    {d : ℕ} (hd : 2 ≤ d) :
    Integrable (fun g : CircularEuclideanSpace d =>
      (auxiliaryGammaRadius g)⁻¹) (stdGaussian (CircularEuclideanSpace d)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_inv_auxiliaryGammaRadius_stdGaussian hd]
  have hdR : (1 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show (1 : ℕ) < d by omega)
  exact inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hdR))

theorem lintegral_ofReal_inv_auxiliaryGammaRadius_stdGaussian
    {d : ℕ} (hd : 2 ≤ d) :
    ∫⁻ g : CircularEuclideanSpace d,
        ENNReal.ofReal (auxiliaryGammaRadius g)⁻¹
          ∂(stdGaussian (CircularEuclideanSpace d)) =
      ENNReal.ofReal ((d : ℝ) - 1)⁻¹ := by
  have hnonneg : 0 ≤ᵐ[stdGaussian (CircularEuclideanSpace d)]
      (fun g => (auxiliaryGammaRadius g)⁻¹) := by
    filter_upwards [] with g
    exact inv_nonneg.mpr (by unfold auxiliaryGammaRadius; positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_inv_auxiliaryGammaRadius_stdGaussian hd) hnonneg]
  rw [integral_inv_auxiliaryGammaRadius_stdGaussian hd]

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Exact Tonelli factorization of the inverse moment of `V * Gamma(d,1)`. -/
theorem ennInverseMoment_mul_auxiliaryGammaRadius
    (nu : Measure Omega) [SFinite nu]
    (V : Omega -> ℝ) (hV : Measurable V) (hVnonneg : ∀ w, 0 ≤ V w)
    {d : ℕ} (hd : 2 ≤ d) :
    ennInverseMoment
        (nu.prod (stdGaussian (CircularEuclideanSpace d)))
        (fun p : Omega × CircularEuclideanSpace d =>
          V p.1 * auxiliaryGammaRadius p.2) =
      ennInverseMoment nu V * ENNReal.ofReal ((d : ℝ) - 1)⁻¹ := by
  unfold ennInverseMoment
  have hf : AEMeasurable (fun w : Omega => ENNReal.ofReal (V w)⁻¹) nu :=
    hV.inv.ennreal_ofReal.aemeasurable
  have hg : AEMeasurable
      (fun g : CircularEuclideanSpace d =>
        ENNReal.ofReal (auxiliaryGammaRadius g)⁻¹)
      (stdGaussian (CircularEuclideanSpace d)) :=
    measurable_auxiliaryGammaRadius.inv.ennreal_ofReal.aemeasurable
  simp_rw [mul_inv]
  have hfactor (w : Omega) (g : CircularEuclideanSpace d) :
      ENNReal.ofReal ((V w)⁻¹ * (auxiliaryGammaRadius g)⁻¹) =
        ENNReal.ofReal (V w)⁻¹ *
          ENNReal.ofReal (auxiliaryGammaRadius g)⁻¹ := by
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (hVnonneg w))]
  simp_rw [hfactor]
  rw [lintegral_prod_mul hf hg,
    lintegral_ofReal_inv_auxiliaryGammaRadius_stdGaussian hd]

/-- The auxiliary Gaussian is nonzero almost surely in positive complex
dimension, hence its radial Gamma variable is strictly positive almost
surely. -/
theorem auxiliaryGammaRadius_pos_ae {d : ℕ} (hd : 0 < d) :
    ∀ᵐ g ∂(stdGaussian (CircularEuclideanSpace d)),
      0 < auxiliaryGammaRadius g := by
  let _ : Nontrivial (CircularEuclideanSpace d) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_real_of_complex]
      simp [CircularEuclideanSpace]
      omega)
  have hne : ∀ᵐ g ∂(stdGaussian (CircularEuclideanSpace d)), g ≠ 0 := by
    simpa [ae_iff] using
      LogdetLean.stdGaussian_zero_singleton
        (E := CircularEuclideanSpace d)
  filter_upwards [hne] with g hg
  unfold auxiliaryGammaRadius
  positivity

end

end LogdetLean.GramHafnian
