import LogdetLean.FixedSubspaceGaussian
import LogdetLean.GramHafnian.RealComplexAnticoncentration.FractionalGamma
import LogdetLean.GramHafnian.RealComplexAnticoncentration.FractionalLaplaceOrder
import LogdetLean.GramHafnian.RealComplexAnticoncentration.FractionalResolvent
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.AuxiliaryAveraging
/-!
# The beta-one Fourier Gamma factor

For a real cofactor vector of length `d`, auxiliary Gaussian Fourier
averaging introduces an independent `chi-square(d)` factor.  This file
computes its exact inverse square-root moment and packages the abstract
Laplace-order consequence.  The literal cofactor compression theorem is a
separate algebraic input.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Squared radius of the real auxiliary standard Gaussian. -/
def realAuxiliaryNormSq {d : ℕ} (g : RealGaussianEuclideanSpace d) : ℝ :=
  ‖g‖ ^ 2

@[fun_prop]
theorem measurable_realAuxiliaryNormSq {d : ℕ} :
    Measurable (realAuxiliaryNormSq (d := d)) := by
  unfold realAuxiliaryNormSq
  fun_prop

theorem inv_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hx]

/-- Exact inverse square-root moment of a `chi-square(d)` variable. -/
theorem lintegral_inv_sqrt_realAuxiliaryNormSq_stdGaussian
    {d : ℕ} (hd : 2 ≤ d) :
    ∫⁻ g : RealGaussianEuclideanSpace d,
        ENNReal.ofReal (Real.sqrt (realAuxiliaryNormSq g))⁻¹
          ∂(stdGaussian (RealGaussianEuclideanSpace d)) =
      ENNReal.ofReal
        ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) *
          Real.Gamma (((d : ℝ) - 1) / 2) /
          Real.Gamma ((d : ℝ) / 2)) := by
  let E := RealGaussianEuclideanSpace d
  let f : ℝ → ENNReal := fun u ↦ ENNReal.ofReal (Real.sqrt u)⁻¹
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  let _ : Nontrivial E := inferInstance
  calc
    (∫⁻ g : E, ENNReal.ofReal (Real.sqrt (realAuxiliaryNormSq g))⁻¹
        ∂(stdGaussian E)) =
        ∫⁻ u : ℝ, f u ∂(LogdetLean.stdGaussianNormSqMeasure E) := by
      rw [LogdetLean.stdGaussianNormSqMeasure]
      rw [lintegral_map hf (by fun_prop)]
      rfl
    _ = ∫⁻ u : ℝ, f u
          ∂gammaMeasure ((d : ℝ) / 2) (1 / 2) := by
      rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma E]
      congr 2
      simp [E, RealGaussianEuclideanSpace]
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (u ^ (-(1 / 2 : ℝ)))
          ∂gammaMeasure ((d : ℝ) / 2) (1 / 2) := by
      apply lintegral_congr_ae
      filter_upwards [gammaMeasure_pos_ae
          (show 0 < (d : ℝ) / 2 by positivity)
          (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
      dsimp [f]
      rw [inv_sqrt_eq_rpow_neg_half hu.le]
    _ = ENNReal.ofReal
        ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) *
          Real.Gamma (((d : ℝ) - 1) / 2) /
          Real.Gamma ((d : ℝ) / 2)) := by
      have hshape : (1 / 2 : ℝ) < (d : ℝ) / 2 := by
        have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      rw [lintegral_ofReal_rpow_neg_half_gammaMeasure
        hshape (by norm_num : (0 : ℝ) < 1 / 2)]
      congr 2
      congr 2
      ring

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The Laplace-order content of the beta-one Fourier step.  Gaussian
averaging turns a radial characteristic-function majorant into domination by
the product of the conditional variance and an independent chi-square
radius. -/
theorem ennLaplace_norm_sq_le_mul_realAuxiliaryNormSq_of_compression
    {d : ℕ}
    (mu : Measure (RealGaussianEuclideanSpace d)) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hcompression : ∀ xi : RealGaussianEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 2) ∂nu)
    (t : ℝ) (ht : 0 ≤ t) :
    ennLaplaceTransform mu
        (fun x : RealGaussianEuclideanSpace d ↦ ‖x‖ ^ 2) t ≤
      ennLaplaceTransform
        (nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
        (fun p ↦ V p.1 * realAuxiliaryNormSq p.2) t := by
  let Vtwo : Omega → ℝ := fun w ↦ 2 * V w
  have hVtwo : Measurable Vtwo := measurable_const.mul hV
  have hVtwo_nonneg : ∀ w, 0 ≤ Vtwo w := fun w ↦ by
    dsimp [Vtwo]
    exact mul_nonneg (by norm_num) (hVnonneg w)
  have hcompression' : ∀ xi : RealGaussianEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(Vtwo w * ‖xi‖ ^ 2) / 4) ∂nu := by
    intro xi
    convert hcompression xi using 1
    apply integral_congr_ae
    filter_upwards [] with w
    dsimp [Vtwo]
    congr 1
    ring
  have h := ennLaplace_norm_sq_le_prod_of_charFun_compression
    mu nu Vtwo hVtwo hVtwo_nonneg hcompression' t ht
  have hobs :
      (fun p : Omega × RealGaussianEuclideanSpace d ↦
        Vtwo p.1 * ‖p.2‖ ^ 2 / 2) =
      (fun p ↦ V p.1 * realAuxiliaryNormSq p.2) := by
    funext p
    dsimp [Vtwo, realAuxiliaryNormSq]
    ring
  simpa only [hobs] using h

/-- Bounded-resolvent form of the beta-one Fourier step. -/
theorem ennHalfResolvent_norm_sq_le_mul_realAuxiliaryNormSq_of_compression
    {d : ℕ}
    (mu : Measure (RealGaussianEuclideanSpace d)) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hcompression : ∀ xi : RealGaussianEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 2) ∂nu)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ennHalfResolvent mu (fun x ↦ ‖x‖ ^ 2) lambda ≤
      ennHalfResolvent
        (nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
        (fun p ↦ V p.1 * realAuxiliaryNormSq p.2) lambda := by
  apply ennHalfResolvent_le_of_laplaceTransform_le_two_measures
    (mu := nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
    (nu := mu)
    (U := fun p ↦ V p.1 * realAuxiliaryNormSq p.2)
    (V := fun x : RealGaussianEuclideanSpace d ↦ ‖x‖ ^ 2)
    (by fun_prop) (by fun_prop)
  · filter_upwards [] with p
    exact mul_nonneg (hVnonneg p.1) (sq_nonneg _)
  · filter_upwards [] with x
    exact sq_nonneg _
  · intro t ht
    exact ennLaplace_norm_sq_le_mul_realAuxiliaryNormSq_of_compression
      mu nu V hV hVnonneg hcompression t ht
  · exact hlambda

/-- Exact Tonelli factorization for a positive random variance times an
independent real auxiliary Gaussian radius. -/
theorem ennInverseSqrtMoment_mul_realAuxiliaryNormSq
    (nu : Measure Omega) [SFinite nu]
    (V : Omega → ℝ) (hV : Measurable V) (hVnonneg : ∀ w, 0 ≤ V w)
    {d : ℕ} (hd : 2 ≤ d) :
    ennInverseSqrtMoment
        (nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
        (fun p : Omega × RealGaussianEuclideanSpace d ↦
          V p.1 * realAuxiliaryNormSq p.2) =
      ennInverseSqrtMoment nu V *
        ENNReal.ofReal
          ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) *
            Real.Gamma (((d : ℝ) - 1) / 2) /
            Real.Gamma ((d : ℝ) / 2)) := by
  unfold ennInverseSqrtMoment
  have hf : AEMeasurable
      (fun w : Omega ↦ ENNReal.ofReal (Real.sqrt (V w))⁻¹) nu :=
    hV.sqrt.inv.ennreal_ofReal.aemeasurable
  have hg : AEMeasurable
      (fun g : RealGaussianEuclideanSpace d ↦
        ENNReal.ofReal (Real.sqrt (realAuxiliaryNormSq g))⁻¹)
      (stdGaussian (RealGaussianEuclideanSpace d)) :=
    measurable_realAuxiliaryNormSq.sqrt.inv.ennreal_ofReal.aemeasurable
  have hpoint (w : Omega) (g : RealGaussianEuclideanSpace d) :
      ENNReal.ofReal (Real.sqrt (V w * realAuxiliaryNormSq g))⁻¹ =
        ENNReal.ofReal (Real.sqrt (V w))⁻¹ *
          ENNReal.ofReal (Real.sqrt (realAuxiliaryNormSq g))⁻¹ := by
    rw [Real.sqrt_mul (hVnonneg w), mul_inv]
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  simp_rw [hpoint]
  rw [lintegral_prod_mul hf hg,
    lintegral_inv_sqrt_realAuxiliaryNormSq_stdGaussian hd]

/-- Abstract beta-one Fourier step.  A radial characteristic-function
majorant with conditional variance `V` yields the exact chi-square
negative-half factor. -/
theorem ennInverseSqrt_norm_sq_le_realAuxiliaryGamma_factor
    {d : ℕ} (hd : 2 ≤ d)
    (mu : Measure (RealGaussianEuclideanSpace d)) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (hcompression : ∀ xi : RealGaussianEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 2) ∂nu)
    (hnormpos : ∀ᵐ x ∂mu, 0 < ‖x‖ ^ 2) :
    ennInverseSqrtMoment mu (fun x ↦ ‖x‖ ^ 2) ≤
      ennInverseSqrtMoment nu V *
        ENNReal.ofReal
          ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) *
            Real.Gamma (((d : ℝ) - 1) / 2) /
            Real.Gamma ((d : ℝ) / 2)) := by
  let Vtwo : Omega → ℝ := fun w ↦ 2 * V w
  have hVtwo : Measurable Vtwo := measurable_const.mul hV
  have hVtwo_nonneg : ∀ w, 0 ≤ Vtwo w := fun w ↦ by
    dsimp [Vtwo]
    exact mul_nonneg (by norm_num) (hVnonneg w)
  have hcompression' : ∀ xi : RealGaussianEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(Vtwo w * ‖xi‖ ^ 2) / 4) ∂nu := by
    intro xi
    convert hcompression xi using 1
    apply integral_congr_ae
    filter_upwards [] with w
    dsimp [Vtwo]
    congr 1
    ring
  have hprodpos :
      ∀ᵐ p ∂(nu.prod (stdGaussian (RealGaussianEuclideanSpace d))),
        0 < V p.1 * realAuxiliaryNormSq p.2 := by
    have hVprod := (Measure.quasiMeasurePreserving_fst
      (μ := nu) (ν := stdGaussian (RealGaussianEuclideanSpace d))).ae hVpos
    have hG : ∀ᵐ g ∂(stdGaussian (RealGaussianEuclideanSpace d)), g ≠ 0 := by
      let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
      let _ : Nontrivial (RealGaussianEuclideanSpace d) := inferInstance
      simpa [ae_iff] using
        LogdetLean.stdGaussian_zero_singleton
          (E := RealGaussianEuclideanSpace d)
    have hGprod := (Measure.quasiMeasurePreserving_snd
      (μ := nu) (ν := stdGaussian (RealGaussianEuclideanSpace d))).ae hG
    filter_upwards [hVprod, hGprod] with p hpV hpG
    exact mul_pos hpV (by unfold realAuxiliaryNormSq; positivity)
  have hLap : ∀ t : ℝ, 0 ≤ t →
      ennLaplaceTransform mu (fun x : RealGaussianEuclideanSpace d ↦ ‖x‖ ^ 2) t ≤
        ennLaplaceTransform
          (nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
          (fun p ↦ V p.1 * realAuxiliaryNormSq p.2) t := by
    intro t ht
    have h := ennLaplace_norm_sq_le_prod_of_charFun_compression
      mu nu Vtwo hVtwo hVtwo_nonneg hcompression' t ht
    have hobs :
        (fun p : Omega × RealGaussianEuclideanSpace d ↦
          Vtwo p.1 * ‖p.2‖ ^ 2 / 2) =
        (fun p ↦ V p.1 * realAuxiliaryNormSq p.2) := by
      funext p
      dsimp [Vtwo, realAuxiliaryNormSq]
      ring
    simpa only [hobs] using h
  calc
    ennInverseSqrtMoment mu (fun x ↦ ‖x‖ ^ 2) ≤
        ennInverseSqrtMoment
          (nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
          (fun p ↦ V p.1 * realAuxiliaryNormSq p.2) := by
      apply ennInverseSqrtMoment_le_of_laplaceTransform_le_two_measures
        (mu := nu.prod (stdGaussian (RealGaussianEuclideanSpace d)))
        (nu := mu)
        (U := fun p ↦ V p.1 * realAuxiliaryNormSq p.2)
        (V := fun x : RealGaussianEuclideanSpace d ↦ ‖x‖ ^ 2)
        (by fun_prop) (by fun_prop) hprodpos hnormpos hLap
    _ = ennInverseSqrtMoment nu V *
        ENNReal.ofReal
          ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) *
            Real.Gamma (((d : ℝ) - 1) / 2) /
            Real.Gamma ((d : ℝ) / 2)) := by
      exact ennInverseSqrtMoment_mul_realAuxiliaryNormSq
        nu V hV hVnonneg hd

end

end LogdetLean.GramHafnian
