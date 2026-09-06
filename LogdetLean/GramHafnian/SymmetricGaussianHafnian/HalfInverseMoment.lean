import LogdetLean.GramHafnian.SymmetricGaussianHafnian.GammaBenchmark
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.AuxiliaryAveraging
import LogdetLean.FixedSubspaceGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
/-!
# Half inverse moments and real auxiliary-Gaussian factors

The real symmetric-Gaussian hafnian requires the negative half moment of
the odd cofactor energy.  This file supplies the two general analytic facts
used by that argument:

× Laplace order implies order of negative half moments; and
× in real dimension `2r-1`, the exact auxiliary standard-Gaussian factor is
  `2^(-1/2) Gamma(r-1) / Gamma(r-1/2)`.

All quantities are kept in `ENNReal`, so no finiteness is assumed before
the explicit Gamma evaluation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Extended nonnegative negative-half moment.  The `Real.rpow` convention
at zero is harmless because all applications separately prove strict
positivity almost surely. -/
def ennHalfInverseMoment (mu : Measure Ω) (U : Ω → ℝ) : ENNReal :=
  ∫⁻ omega, ENNReal.ofReal ((U omega) ^ (-(1 / 2 : ℝ))) ∂mu

private lemma lintegral_halfMellinKernel_Ioi (x : ℝ) (hx : 0 < x) :
    ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal ((Real.sqrt Real.pi)⁻¹ *
          t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * x)) =
      ENNReal.ofReal (x ^ (-(1 / 2 : ℝ))) := by
  have hfun : (fun t : ℝ => (Real.sqrt Real.pi)⁻¹ *
      t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * x)) =
      (fun t : ℝ => (Real.sqrt Real.pi)⁻¹ *
        (t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(x * t)))) := by
    funext t
    have he : -t * x = -(x * t) := by ring
    rw [show -(1 / 2 : ℝ) = (1 / 2 : ℝ) - 1 by norm_num, he]
    ring
  have hIntegral :
      ∫ t : ℝ in Ioi 0,
          (Real.sqrt Real.pi)⁻¹ * t ^ (-(1 / 2 : ℝ)) *
            Real.exp (-t * x) = x ^ (-(1 / 2 : ℝ)) := by
    rw [hfun, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi
        (by norm_num : (0 : ℝ) < 1 / 2) hx,
      Real.Gamma_one_half_eq]
    have hsqrt : Real.sqrt Real.pi ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    rw [show (1 / x : ℝ) ^ (1 / 2 : ℝ) =
        x ^ (-(1 / 2 : ℝ)) by
      rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le]]
    field_simp [hsqrt]
  have hint : IntegrableOn (fun t : ℝ => (Real.sqrt Real.pi)⁻¹ *
      t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * x)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hIntegral]
    exact (Real.rpow_pos_of_pos hx _).ne'
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => (Real.sqrt Real.pi)⁻¹ *
        t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
        (Real.rpow_nonneg ht.le _))
      (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, hIntegral]

/-- Cross-space Laplace order implies negative-half-moment order. -/
theorem ennHalfInverseMoment_le_of_laplaceTransform_le_two_measures
    (mu : Measure Ω) [SFinite mu]
    (nu : Measure Ω') [SFinite nu]
    (U : Ω → ℝ) (V : Ω' → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (hUpos : ∀ᵐ w ∂mu, 0 < U w)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (hLap : ∀ t : ℝ, 0 ≤ t →
      LogdetLean.GramHafnian.ennLaplaceTransform nu V t ≤
        LogdetLean.GramHafnian.ennLaplaceTransform mu U t) :
    ennHalfInverseMoment nu V ≤ ennHalfInverseMoment mu U := by
  let c : ℝ := (Real.sqrt Real.pi)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hmeasV : Measurable (fun p : Ω' × ℝ =>
      ENNReal.ofReal (c * p.2 ^ (-(1 / 2 : ℝ)) *
        Real.exp (-p.2 * V p.1))) := by
    fun_prop
  have hmeasU : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (c * p.2 ^ (-(1 / 2 : ℝ)) *
        Real.exp (-p.2 * U p.1))) := by
    fun_prop
  unfold ennHalfInverseMoment
  calc
    (∫⁻ w, ENNReal.ofReal (V w ^ (-(1 / 2 : ℝ))) ∂nu) =
        ∫⁻ w, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (c * t ^ (-(1 / 2 : ℝ)) *
            Real.exp (-t * V w)) ∂volume ∂nu := by
      apply lintegral_congr_ae
      filter_upwards [hVpos] with w hw
      exact (lintegral_halfMellinKernel_Ioi (V w) hw).symm
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ w,
          ENNReal.ofReal (c * t ^ (-(1 / 2 : ℝ)) *
            Real.exp (-t * V w)) ∂nu ∂volume := by
      rw [lintegral_lintegral_swap hmeasV.aemeasurable]
    _ ≤ ∫⁻ t : ℝ in Ioi 0, ∫⁻ w,
          ENNReal.ofReal (c * t ^ (-(1 / 2 : ℝ)) *
            Real.exp (-t * U w)) ∂mu ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hLap' := hLap t ht.le
      unfold LogdetLean.GramHafnian.ennLaplaceTransform at hLap'
      let a : ENNReal := ENNReal.ofReal (c * t ^ (-(1 / 2 : ℝ)))
      have ha : 0 ≤ c * t ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg hc (Real.rpow_nonneg ht.le _)
      have hmul := mul_le_mul_of_nonneg_left hLap' (bot_le : 0 ≤ a)
      simp_rw [ENNReal.ofReal_mul ha]
      rw [lintegral_const_mul a (by fun_prop),
        lintegral_const_mul a (by fun_prop)]
      exact hmul
    _ = ∫⁻ w, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (c * t ^ (-(1 / 2 : ℝ)) *
            Real.exp (-t * U w)) ∂volume ∂mu := by
      symm
      rw [lintegral_lintegral_swap hmeasU.aemeasurable]
    _ = ∫⁻ w, ENNReal.ofReal (U w ^ (-(1 / 2 : ℝ))) ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hUpos] with w hw
      exact lintegral_halfMellinKernel_Ioi (U w) hw

/-- Exact negative-half moment of the squared norm of a standard real
Gaussian vector in odd dimension `2r-1`. -/
theorem integral_realStdGaussian_normSq_negativeHalf
    (r : ℕ) (hr : 2 ≤ r) :
    ∫ g : EuclideanSpace ℝ (Fin (2 * r - 1)),
        (‖g‖ ^ 2) ^ (-(1 / 2 : ℝ))
        ∂stdGaussian (EuclideanSpace ℝ (Fin (2 * r - 1))) =
      gammaNegativeFactor 1 r (1 / 2) := by
  let E := EuclideanSpace ℝ (Fin (2 * r - 1))
  have hdim : Module.finrank ℝ E = 2 * r - 1 := by simp [E]
  have hnontriv : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  let _ : Nontrivial E := hnontriv
  change ∫ g : E, (‖g‖ ^ 2) ^ (-(1 / 2 : ℝ)) ∂stdGaussian E = _
  change ∫ g : E, (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (‖g‖ ^ 2)
      ∂stdGaussian E = _
  rw [← integral_map
    (by fun_prop : AEMeasurable (fun g : E => ‖g‖ ^ 2) (stdGaussian E))
    (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
      ((stdGaussian E).map (fun g : E => ‖g‖ ^ 2)))]
  change ∫ x : ℝ, x ^ (-(1 / 2 : ℝ))
      ∂LogdetLean.stdGaussianNormSqMeasure E = _
  rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma E, hdim]
  have hshape : (((2 * r - 1 : ℕ) : ℝ) / 2) = gammaShape 1 r := by
    unfold gammaShape
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  rw [hshape]
  exact integral_gamma_negative_factor (by norm_num) hr (by norm_num)

theorem integrable_realStdGaussian_normSq_negativeHalf
    (r : ℕ) (hr : 2 ≤ r) :
    Integrable (fun g : EuclideanSpace ℝ (Fin (2 * r - 1)) =>
      (‖g‖ ^ 2) ^ (-(1 / 2 : ℝ)))
      (stdGaussian (EuclideanSpace ℝ (Fin (2 * r - 1))) ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_realStdGaussian_normSq_negativeHalf r hr]
  exact (gammaNegativeFactor_pos (by norm_num) hr (by norm_num)).ne'

theorem lintegral_realStdGaussian_normSq_negativeHalf
    (r : ℕ) (hr : 2 ≤ r) :
    ∫⁻ g : EuclideanSpace ℝ (Fin (2 * r - 1)),
        ENNReal.ofReal ((‖g‖ ^ 2) ^ (-(1 / 2 : ℝ)))
        ∂stdGaussian (EuclideanSpace ℝ (Fin (2 * r - 1))) =
      ENNReal.ofReal (gammaNegativeFactor 1 r (1 / 2)) := by
  have hnonneg : 0 ≤ᵐ[stdGaussian (EuclideanSpace ℝ (Fin (2 * r - 1)))]
      (fun g => (‖g‖ ^ 2) ^ (-(1 / 2 : ℝ))) := by
    exact Filter.Eventually.of_forall fun g => Real.rpow_nonneg (sq_nonneg _) _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_realStdGaussian_normSq_negativeHalf r hr) hnonneg,
    integral_realStdGaussian_normSq_negativeHalf r hr]

/-- Exact Tonelli factorization against the real auxiliary Gaussian. -/
theorem ennHalfInverseMoment_mul_realStdGaussian_normSq
    (nu : Measure Ω) [SFinite nu]
    (V : Ω → ℝ) (hV : Measurable V) (hVnonneg : ∀ w, 0 ≤ V w)
    (r : ℕ) (hr : 2 ≤ r) :
    ennHalfInverseMoment
        (nu.prod (stdGaussian (EuclideanSpace ℝ (Fin (2 * r - 1)))))
        (fun p => V p.1 * ‖p.2‖ ^ 2) =
      ennHalfInverseMoment nu V *
        ENNReal.ofReal (gammaNegativeFactor 1 r (1 / 2)) := by
  unfold ennHalfInverseMoment
  have hf : AEMeasurable
      (fun w : Ω => ENNReal.ofReal (V w ^ (-(1 / 2 : ℝ)))) nu :=
    by fun_prop
  have hg : AEMeasurable
      (fun g : EuclideanSpace ℝ (Fin (2 * r - 1)) =>
        ENNReal.ofReal ((‖g‖ ^ 2) ^ (-(1 / 2 : ℝ))))
      (stdGaussian (EuclideanSpace ℝ (Fin (2 * r - 1)))) := by fun_prop
  have hfactor (w : Ω) (g : EuclideanSpace ℝ (Fin (2 * r - 1))) :
      ENNReal.ofReal ((V w * ‖g‖ ^ 2) ^ (-(1 / 2 : ℝ))) =
        ENNReal.ofReal (V w ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal ((‖g‖ ^ 2) ^ (-(1 / 2 : ℝ))) := by
    rw [Real.mul_rpow (hVnonneg w) (sq_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (hVnonneg w) _)]
  simp_rw [hfactor]
  rw [lintegral_prod_mul hf hg,
    lintegral_realStdGaussian_normSq_negativeHalf r hr]

/-- Fourier compression in real dimension `2r-1` yields the exact
negative-half-moment recurrence factor. -/
theorem ennHalfInverse_normSq_le_realGammaFactor
    (r : ℕ) (hr : 2 ≤ r)
    (mu : Measure (EuclideanSpace ℝ (Fin (2 * r - 1))))
      [IsProbabilityMeasure mu]
    (nu : Measure Ω) [IsProbabilityMeasure nu]
    (W : Ω → ℝ) (hW : Measurable W)
    (hWnonneg : ∀ w, 0 ≤ W w)
    (hWpos : ∀ᵐ w ∂nu, 0 < W w)
    (hcompression : ∀ xi : EuclideanSpace ℝ (Fin (2 * r - 1)),
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(W w * ‖xi‖ ^ 2) / 2) ∂nu)
    (hnormpos : ∀ᵐ x ∂mu, 0 < ‖x‖ ^ 2) :
    ennHalfInverseMoment mu (fun x => ‖x‖ ^ 2) ≤
      ennHalfInverseMoment nu W *
        ENNReal.ofReal (gammaNegativeFactor 1 r (1 / 2)) := by
  let E := EuclideanSpace ℝ (Fin (2 * r - 1))
  let V : Ω → ℝ := fun w => 2 * W w
  have hdimE : Module.finrank ℝ E = 2 * r - 1 := by simp [E]
  have hV : Measurable V := measurable_const.mul hW
  have hVnonneg : ∀ w, 0 ≤ V w := fun w => mul_nonneg (by norm_num) (hWnonneg w)
  have hVpos : ∀ᵐ w ∂nu, 0 < V w := by
    filter_upwards [hWpos] with w hw
    dsimp [V]
    positivity
  have hprodpos : ∀ᵐ p ∂(nu.prod (stdGaussian E)),
      0 < V p.1 * ‖p.2‖ ^ 2 / 2 := by
    have hgauss : ∀ᵐ g ∂stdGaussian E, g ≠ 0 := by
      let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (by
        rw [hdimE]
        omega)
      simpa [ae_iff] using LogdetLean.stdGaussian_zero_singleton (E := E)
    have hVprod := (Measure.quasiMeasurePreserving_fst
      (μ := nu) (ν := stdGaussian E)).ae hVpos
    have hgprod := (Measure.quasiMeasurePreserving_snd
      (μ := nu) (ν := stdGaussian E)).ae hgauss
    filter_upwards [hVprod, hgprod] with p hpV hpg
    have hnorm : 0 < ‖p.2‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hpg)
    positivity
  have hLap : ∀ t : ℝ, 0 ≤ t →
      LogdetLean.GramHafnian.ennLaplaceTransform mu (fun x : E => ‖x‖ ^ 2) t ≤
        LogdetLean.GramHafnian.ennLaplaceTransform
          (nu.prod (stdGaussian E))
          (fun p : Ω × E => V p.1 * ‖p.2‖ ^ 2 / 2) t := by
    intro t ht
    refine LogdetLean.GramHafnian.ennLaplace_norm_sq_le_prod_of_charFun_compression
      mu nu V hV hVnonneg ?_ t ht
    intro xi
    have h := hcompression xi
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with w
    congr 1
    dsimp [V]
    ring
  have horder := ennHalfInverseMoment_le_of_laplaceTransform_le_two_measures
    (mu := nu.prod (stdGaussian E)) (nu := mu)
    (U := fun p : Ω × E => V p.1 * ‖p.2‖ ^ 2 / 2)
    (V := fun x : E => ‖x‖ ^ 2)
    (by fun_prop) (by fun_prop) hprodpos hnormpos hLap
  have hobs : (fun p : Ω × E => V p.1 * ‖p.2‖ ^ 2 / 2) =
      (fun p : Ω × E => W p.1 * ‖p.2‖ ^ 2) := by
    funext p
    dsimp [V]
    ring
  rw [hobs,
    ennHalfInverseMoment_mul_realStdGaussian_normSq nu W hW hWnonneg r hr] at horder
  exact horder

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
