import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.GeneralBilinearGaussian
/-!
# Positive-weight bilinear Gaussian compression

In a symmetric edge-Gaussian cofactor expansion, the edge joining the two
exposed vertices contributes an independent scalar Gaussian.  Integrating
that scalar supplies the positive weight `exp (-|ell|^2 / 4)`.  This weight
is unchanged by compression of the two exposed Fourier coefficients.

The results below prove that an arbitrary common positive weight preserves
the exact pointwise interpolation identity and the integrated two-endpoint
bound.  They are analytic lemmas, not assertions that an arbitrary input
family has the symmetric Gaussian hafnian law.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 1000000

section Pointwise

variable {E A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- The bilinear characteristic integral, including the positive factor
produced by an additional independent scalar Gaussian. -/
def weightedBilinearGaussianIntegral
    (weight : ℝ) (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) : ℂ :=
  (weight : ℂ) * bilinearGaussianIntegral T L a b

/-- Absorbing the same positive factor into both endpoints is exact:
the exponents add to one. -/
theorem positive_weight_geometric_interpolation
    {weight left right theta : ℝ}
    (hweight : 0 < weight) (hleft : 0 ≤ left) (hright : 0 ≤ right) :
    weight * (left ^ theta * right ^ (1 - theta)) =
      (weight * left) ^ theta * (weight * right) ^ (1 - theta) := by
  rw [Real.mul_rpow hweight.le hleft,
    Real.mul_rpow hweight.le hright]
  calc
    weight * (left ^ theta * right ^ (1 - theta)) =
        weight ^ (theta + (1 - theta)) *
          (left ^ theta * right ^ (1 - theta)) := by
      rw [show theta + (1 - theta) = 1 by ring, Real.rpow_one]
    _ = _ := by
      rw [Real.rpow_add hweight]
      ring

/-- The exact weighted pointwise interpolation identity.  In particular,
the scalar Gaussian factor is not dropped or replaced by a larger bound. -/
theorem norm_weightedBilinearGaussianIntegral_sqrt_interpolation
    (weight : ℝ) (hweight : 0 < weight)
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1) :
    ‖weightedBilinearGaussianIntegral weight T L
        (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)‖ =
      (weight * (bilinearGaussianIntegral T L a 0).re) ^ theta *
        (weight * (bilinearGaussianIntegral T L 0 b).re) ^ (1 - theta) := by
  have hpos := bilinearGaussianIntegral_endpoints_pos
    (n := Module.finrank ℝ E) rfl T L a b
  rw [weightedBilinearGaussianIntegral, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hweight,
    norm_bilinearGaussianIntegral_sqrt_interpolation
      (n := Module.finrank ℝ E) rfl T L a b htheta htheta_one]
  exact positive_weight_geometric_interpolation hweight hpos.1.le hpos.2.le

/-- Both weighted endpoint kernels are strictly positive real numbers. -/
theorem weightedBilinearGaussianIntegral_endpoints
    (weight : ℝ) (hweight : 0 < weight)
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) :
    (weightedBilinearGaussianIntegral weight T L a 0).im = 0 ∧
      (weightedBilinearGaussianIntegral weight T L 0 b).im = 0 ∧
      0 < (weightedBilinearGaussianIntegral weight T L a 0).re ∧
      0 < (weightedBilinearGaussianIntegral weight T L 0 b).re := by
  have hpos := bilinearGaussianIntegral_endpoints_pos
    (n := Module.finrank ℝ E) rfl T L a b
  have hleft := bilinearGaussianIntegral_left_endpoint_im T L a
  have hright := bilinearGaussianIntegral_right_endpoint_im T L b
  simp only [weightedBilinearGaussianIntegral, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.mul_re, sub_zero, hleft, hright, mul_zero]
  exact ⟨trivial, trivial, mul_pos hweight hpos.1, mul_pos hweight hpos.2⟩

end Pointwise

section Averaging

variable {Omega E A : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Weighted Hölder averaging for a background-dependent Gaussian phase.
The endpoint functions are required to be measurable, but no integrability
or finiteness of an inverse moment is presumed. -/
theorem lintegral_norm_weightedBilinearGaussianIntegral_sqrt_le
    (mu : Measure Omega) (weight : Omega → ℝ)
    (hweight : ∀ omega, 0 < weight omega)
    (T : Omega → E →L[ℝ] E) (L : Omega → A →L[ℝ] E) (a b : A)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (hleft : AEMeasurable (fun omega ↦ ENNReal.ofReal
      (weight omega * (bilinearGaussianIntegral (T omega) (L omega) a 0).re)) mu)
    (hright : AEMeasurable (fun omega ↦ ENNReal.ofReal
      (weight omega * (bilinearGaussianIntegral (T omega) (L omega) 0 b).re)) mu) :
    (∫⁻ omega, ENNReal.ofReal
      ‖weightedBilinearGaussianIntegral (weight omega) (T omega) (L omega)
        (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)‖ ∂mu) ≤
      (∫⁻ omega, ENNReal.ofReal
        (weight omega * (bilinearGaussianIntegral (T omega) (L omega) a 0).re)
        ∂mu) ^ theta *
      (∫⁻ omega, ENNReal.ofReal
        (weight omega * (bilinearGaussianIntegral (T omega) (L omega) 0 b).re)
        ∂mu) ^ (1 - theta) := by
  let f : Omega → ENNReal := fun omega ↦ ENNReal.ofReal
    (weight omega * (bilinearGaussianIntegral (T omega) (L omega) a 0).re)
  let g : Omega → ENNReal := fun omega ↦ ENNReal.ofReal
    (weight omega * (bilinearGaussianIntegral (T omega) (L omega) 0 b).re)
  calc
    (∫⁻ omega, ENNReal.ofReal
      ‖weightedBilinearGaussianIntegral (weight omega) (T omega) (L omega)
        (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)‖ ∂mu) =
        ∫⁻ omega, f omega ^ theta * g omega ^ (1 - theta) ∂mu := by
      apply lintegral_congr
      intro omega
      have hp := bilinearGaussianIntegral_endpoints_pos
        (n := Module.finrank ℝ E) rfl (T omega) (L omega) a b
      have hfl : 0 ≤ weight omega *
          (bilinearGaussianIntegral (T omega) (L omega) a 0).re :=
        mul_nonneg (hweight omega).le hp.1.le
      have hgr : 0 ≤ weight omega *
          (bilinearGaussianIntegral (T omega) (L omega) 0 b).re :=
        mul_nonneg (hweight omega).le hp.2.le
      rw [norm_weightedBilinearGaussianIntegral_sqrt_interpolation
        (weight omega) (hweight omega) (T omega) (L omega) a b htheta htheta_one,
        ENNReal.ofReal_mul (Real.rpow_nonneg hfl theta),
        ENNReal.ofReal_rpow_of_nonneg hfl htheta,
        ENNReal.ofReal_rpow_of_nonneg hgr (sub_nonneg.mpr htheta_one)]
    _ ≤ (∫⁻ omega, f omega ∂mu) ^ theta *
        (∫⁻ omega, g omega ∂mu) ^ (1 - theta) :=
      lintegral_geometric_interpolation_le mu f g theta hleft hright
        htheta htheta_one

/-- The weighted geometric mean of two extended nonnegative numbers is
bounded by their maximum, including the zero and infinite cases. -/
theorem ennreal_geometric_interpolation_le_max
    (left right : ENNReal) {theta : ℝ}
    (htheta : 0 < theta) (htheta_one : theta < 1) :
    left ^ theta * right ^ (1 - theta) ≤ max left right := by
  let M := max left right
  have hLM : left ≤ M := le_max_left _ _
  have hRM : right ≤ M := le_max_right _ _
  by_cases hM0 : M = 0
  · have hL0 : left = 0 := le_antisymm (hLM.trans_eq hM0) bot_le
    have hR0 : right = 0 := le_antisymm (hRM.trans_eq hM0) bot_le
    simp [hL0, hR0, sub_pos.mpr htheta_one]
  · by_cases hMtop : M = ∞
    · change max left right = ∞ at hMtop
      rw [hMtop]
      exact le_top
    · calc
        left ^ theta * right ^ (1 - theta) ≤
            M ^ theta * M ^ (1 - theta) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hLM htheta.le)
            (ENNReal.rpow_le_rpow hRM (sub_nonneg.mpr htheta_one.le))
        _ = M ^ (theta + (1 - theta)) :=
          (ENNReal.rpow_add _ _ hM0 hMtop).symm
        _ = M := by rw [show theta + (1 - theta) = 1 by ring]; simp

/-- For an integrable nonnegative real-valued complex function, taking the
norm after integration is the same as integrating its real part. -/
theorem ofReal_norm_integral_eq_lintegral_re
    (mu : Measure Omega) (f : Omega → ℂ) (hf : Integrable f mu)
    (him : ∀ omega, (f omega).im = 0)
    (hre : ∀ omega, 0 ≤ (f omega).re) :
    ENNReal.ofReal ‖∫ omega, f omega ∂mu‖ =
      ∫⁻ omega, ENNReal.ofReal (f omega).re ∂mu := by
  have hreal : (∫ omega, f omega ∂mu) =
      ((∫ omega, (f omega).re ∂mu : ℝ) : ℂ) := by
    calc
      (∫ omega, f omega ∂mu) =
          ∫ omega, (((f omega).re : ℝ) : ℂ) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with omega
        apply Complex.ext
        · simp
        · simpa using him omega
      _ = _ := integral_ofReal
  rw [hreal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg hre)]
  exact ofReal_integral_eq_lintegral_ofReal hf.re
    (Filter.Eventually.of_forall hre)

/-- The averaged weighted complex Gaussian kernel is bounded by the larger
of its two averaged endpoint kernels.  All positivity, triangle-inequality,
and Hölder steps are proved here; applications only establish the displayed
integral representation and elementary integrability. -/
theorem norm_integral_weightedBilinearGaussianIntegral_sqrt_le_max
    (mu : Measure Omega) (weight : Omega → ℝ)
    (hweight : ∀ omega, 0 < weight omega)
    (T : Omega → E →L[ℝ] E) (L : Omega → A →L[ℝ] E) (a b : A)
    {theta : ℝ} (htheta : 0 < theta) (htheta_one : theta < 1)
    (hint : Integrable (fun omega ↦
      weightedBilinearGaussianIntegral (weight omega) (T omega) (L omega)
        (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)) mu)
    (hleft : Integrable (fun omega ↦
      weightedBilinearGaussianIntegral (weight omega) (T omega) (L omega) a 0) mu)
    (hright : Integrable (fun omega ↦
      weightedBilinearGaussianIntegral (weight omega) (T omega) (L omega) 0 b) mu) :
    ‖∫ omega, weightedBilinearGaussianIntegral
      (weight omega) (T omega) (L omega)
      (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b) ∂mu‖ ≤
      max
        ‖∫ omega, weightedBilinearGaussianIntegral
          (weight omega) (T omega) (L omega) a 0 ∂mu‖
        ‖∫ omega, weightedBilinearGaussianIntegral
          (weight omega) (T omega) (L omega) 0 b ∂mu‖ := by
  let f : Omega → ℂ := fun omega ↦
    weightedBilinearGaussianIntegral (weight omega) (T omega) (L omega)
      (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)
  let fl : Omega → ℂ := fun omega ↦
    weightedBilinearGaussianIntegral (weight omega) (T omega) (L omega) a 0
  let fr : Omega → ℂ := fun omega ↦
    weightedBilinearGaussianIntegral (weight omega) (T omega) (L omega) 0 b
  have hp omega := weightedBilinearGaussianIntegral_endpoints
    (weight omega) (hweight omega) (T omega) (L omega) a b
  have hlval := ofReal_norm_integral_eq_lintegral_re mu fl hleft
    (fun omega ↦ (hp omega).1) (fun omega ↦ (hp omega).2.2.1.le)
  have hrval := ofReal_norm_integral_eq_lintegral_re mu fr hright
    (fun omega ↦ (hp omega).2.1) (fun omega ↦ (hp omega).2.2.2.le)
  have hleftMeas : AEMeasurable (fun omega ↦ ENNReal.ofReal
      (weight omega * (bilinearGaussianIntegral (T omega) (L omega) a 0).re)) mu := by
    simpa [weightedBilinearGaussianIntegral, Function.comp_def] using
      ENNReal.measurable_ofReal.comp_aemeasurable hleft.re.aemeasurable
  have hrightMeas : AEMeasurable (fun omega ↦ ENNReal.ofReal
      (weight omega * (bilinearGaussianIntegral (T omega) (L omega) 0 b).re)) mu := by
    simpa [weightedBilinearGaussianIntegral, Function.comp_def] using
      ENNReal.measurable_ofReal.comp_aemeasurable hright.re.aemeasurable
  have hholder := lintegral_norm_weightedBilinearGaussianIntegral_sqrt_le
    mu weight hweight T L a b htheta.le htheta_one.le hleftMeas hrightMeas
  have hholder' : (∫⁻ omega, ENNReal.ofReal ‖f omega‖ ∂mu) ≤
      (∫⁻ omega, ENNReal.ofReal (fl omega).re ∂mu) ^ theta *
        (∫⁻ omega, ENNReal.ofReal (fr omega).re ∂mu) ^ (1 - theta) := by
    simpa [f, fl, fr, weightedBilinearGaussianIntegral] using hholder
  have htriangle : ENNReal.ofReal ‖∫ omega, f omega ∂mu‖ ≤
      ∫⁻ omega, ENNReal.ofReal ‖f omega‖ ∂mu := by
    have h := ENNReal.ofReal_le_ofReal
      (norm_integral_le_integral_norm f (μ := mu))
    rw [ofReal_integral_norm_eq_lintegral_enorm hint] at h
    simpa [ofReal_norm] using h
  have hresult : ENNReal.ofReal ‖∫ omega, f omega ∂mu‖ ≤
      ENNReal.ofReal
        (max ‖∫ omega, fl omega ∂mu‖ ‖∫ omega, fr omega ∂mu‖) := by
    rw [ENNReal.ofReal_max, hlval, hrval]
    exact htriangle.trans (hholder'.trans
      (ennreal_geometric_interpolation_le_max _ _ htheta htheta_one))
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hresult

end Averaging

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
