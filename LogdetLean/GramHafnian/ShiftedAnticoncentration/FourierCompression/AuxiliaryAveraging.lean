import LogdetLean.GramHafnian.ShiftedAnticoncentration.AuxiliaryGaussian
import Mathlib.MeasureTheory.Integral.Prod
/-!
# Auxiliary-Gaussian averaging of characteristic functions

This file isolates the Fubini step which turns the pointwise Fourier
coordinate-compression inequality into a radial Laplace-transform inequality.
All measures below are finite, so the complex exponential kernels are
integrable simply because their norm is one.
-/

open MeasureTheory ProbabilityTheory Complex

namespace LogdetLean.GramHafnian

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma integrable_probChar_inner_prod
    (mu nu : Measure E) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (a : ℝ) :
    Integrable
      (fun p : E × E =>
        Complex.exp (inner ℝ p.1 (a • p.2) * Complex.I))
      (mu.prod nu) := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with p
  simp

/-- Averaging a characteristic function over an independent standard
Gaussian gives the exact radial heat kernel. -/
theorem integral_re_charFun_smul_stdGaussian
    (mu : Measure E) [IsProbabilityMeasure mu]
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ g, (charFun mu (Real.sqrt (2 * t) • g)).re ∂(stdGaussian E) =
      ∫ x, Real.exp (-t * ‖x‖ ^ 2) ∂mu := by
  let a : ℝ := Real.sqrt (2 * t)
  have hcomplexExp (x : E) :
      Complex.exp (-((t : ℂ) * (‖x‖ : ℂ) ^ 2)) =
        Complex.exp ((-(t * ‖x‖ ^ 2) : ℝ) : ℂ) := by
    congr 1
    norm_cast
  have hint := integrable_probChar_inner_prod
    (mu := mu) (nu := stdGaussian E) a
  have hswap :
      (∫ g, ∫ x,
          Complex.exp (inner ℝ x (a • g) * Complex.I) ∂mu
        ∂(stdGaussian E)) =
        ∫ x, ∫ g,
          Complex.exp (inner ℝ x (a • g) * Complex.I)
            ∂(stdGaussian E) ∂mu := by
    exact (integral_integral_swap hint).symm
  have hleft :
      (∫ g, (charFun mu (a • g)).re ∂(stdGaussian E)) =
        ((∫ g, ∫ x,
          Complex.exp (inner ℝ x (a • g) * Complex.I) ∂mu
            ∂(stdGaussian E))).re := by
    change (∫ g, (∫ x,
        Complex.exp (inner ℝ x (a • g) * Complex.I) ∂mu).re
          ∂(stdGaussian E)) = _
    exact integral_re hint.integral_prod_right
  rw [show Real.sqrt (2 * t) = a by rfl, hleft, hswap]
  have hinner (x : E) :
      (∫ g,
          Complex.exp (inner ℝ x (a • g) * Complex.I)
            ∂(stdGaussian E)) =
        Complex.exp ((-(t * ‖x‖ ^ 2) : ℝ) : ℂ) := by
    rw [show (fun g : E =>
        Complex.exp (inner ℝ x (a • g) * Complex.I)) =
        (fun g : E =>
          Complex.exp (inner ℝ g (a • x) * Complex.I)) by
          funext g
          congr 2
          norm_cast
          rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]]
    change charFun (stdGaussian E) (a • x) = _
    rw [show a = Real.sqrt (2 * t) by rfl]
    rw [← hcomplexExp x]
    exact auxiliaryGaussian_charFun_identity x t ht
  simp_rw [hinner]
  have hrad : Integrable
      (fun x : E => Complex.exp ((-(t * ‖x‖ ^ 2) : ℝ) : ℂ)) mu := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg ht (sq_nonneg _)))
  calc
    (∫ x : E, Complex.exp ((-(t * ‖x‖ ^ 2) : ℝ) : ℂ) ∂mu).re =
        ∫ x : E, (Complex.exp ((-(t * ‖x‖ ^ 2) : ℝ) : ℂ)).re ∂mu :=
      (integral_re hrad).symm
    _ = ∫ x : E, Real.exp (-t * ‖x‖ ^ 2) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Complex.exp_ofReal_re]
      congr 1
      ring

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A radial characteristic-function majorant gives the corresponding
Laplace comparison after adjoining an independent standard Gaussian.  This
is the precise finite-dimensional Fubini step used after Fourier coordinate
compression. -/
theorem integral_exp_neg_norm_sq_le_prod_of_charFun_compression
    (mu : Measure E) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega -> ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hcompression : ∀ xi : E,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 4) ∂nu)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, Real.exp (-t * ‖x‖ ^ 2) ∂mu ≤
      ∫ p : Omega × E,
        Real.exp (-t * (V p.1 * ‖p.2‖ ^ 2 / 2))
          ∂(nu.prod (stdGaussian E)) := by
  let F : Omega × E -> ℝ := fun p =>
    Real.exp (-t * (V p.1 * ‖p.2‖ ^ 2 / 2))
  have hFmeas : AEStronglyMeasurable F (nu.prod (stdGaussian E)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hVprod : ∀ᵐ p ∂(nu.prod (stdGaussian E)), 0 ≤ V p.1 := by
    exact ae_of_all _ fun p => hVnonneg p.1
  have hF : Integrable F (nu.prod (stdGaussian E)) := by
    apply Integrable.of_bound hFmeas 1
    filter_upwards [hVprod] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht)
      (div_nonneg (mul_nonneg hp (sq_nonneg ‖p.2‖))
        (by norm_num : (0 : ℝ) ≤ 2))
  have hchar : Integrable
      (fun g : E => (charFun mu (Real.sqrt (2 * t) • g)).re)
      (stdGaussian E) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with g
    calc
      ‖(charFun mu (Real.sqrt (2 * t) • g)).re‖ ≤
          ‖charFun mu (Real.sqrt (2 * t) • g)‖ := Complex.abs_re_le_norm _
      _ ≤ 1 := norm_charFun_le_one _
  have hscaled (g : E) :
      (charFun mu (Real.sqrt (2 * t) • g)).re ≤
        ∫ w, F (w, g) ∂nu := by
    calc
      (charFun mu (Real.sqrt (2 * t) • g)).re ≤
          ∫ w, Real.exp
            (-(V w * ‖Real.sqrt (2 * t) • g‖ ^ 2) / 4) ∂nu :=
        hcompression _
      _ = ∫ w, F (w, g) ∂nu := by
        apply integral_congr_ae
        filter_upwards [] with w
        dsimp [F]
        congr 1
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
          Real.sq_sqrt (by linarith : 0 ≤ 2 * t)]
        ring
  rw [← integral_re_charFun_smul_stdGaussian mu t ht]
  calc
    (∫ g, (charFun mu (Real.sqrt (2 * t) • g)).re
        ∂(stdGaussian E)) ≤
        ∫ g, ∫ w, F (w, g) ∂nu ∂(stdGaussian E) := by
      exact integral_mono hchar hF.swap.integral_prod_left hscaled
    _ = ∫ w, ∫ g, F (w, g) ∂(stdGaussian E) ∂nu := by
      exact integral_integral_swap hF.swap
    _ = ∫ p : Omega × E, F p ∂(nu.prod (stdGaussian E)) := by
      exact (integral_prod F hF).symm

/-- `ENNReal` Laplace-order form of the auxiliary-Gaussian comparison. -/
theorem ennLaplace_norm_sq_le_prod_of_charFun_compression
    (mu : Measure E) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega -> ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hcompression : ∀ xi : E,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 4) ∂nu)
    (t : ℝ) (ht : 0 ≤ t) :
    ennLaplaceTransform mu (fun x : E => ‖x‖ ^ 2) t ≤
      ennLaplaceTransform (nu.prod (stdGaussian E))
        (fun p : Omega × E => V p.1 * ‖p.2‖ ^ 2 / 2) t := by
  rw [ennLaplaceTransform_eq_ofReal_integral mu
      (fun x : E => ‖x‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _) t ht]
  rw [ennLaplaceTransform_eq_ofReal_integral
      (nu.prod (stdGaussian E))
      (fun p : Omega × E => V p.1 * ‖p.2‖ ^ 2 / 2)
      (by fun_prop) (fun p => div_nonneg
        (mul_nonneg (hVnonneg p.1) (sq_nonneg _)) (by norm_num)) t ht]
  exact ENNReal.ofReal_le_ofReal
    (integral_exp_neg_norm_sq_le_prod_of_charFun_compression
      mu nu V hV hVnonneg hcompression t ht)

/-- Inverse-moment consequence of coordinate compression, before evaluating
the auxiliary Gaussian radial factor. -/
theorem ennInverse_norm_sq_le_prod_of_charFun_compression
    (mu : Measure E) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega -> ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hcompression : ∀ xi : E,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 4) ∂nu)
    (hnormpos : ∀ᵐ x ∂mu, 0 < ‖x‖ ^ 2)
    (hprodpos : ∀ᵐ p ∂(nu.prod (stdGaussian E)),
      0 < V p.1 * ‖p.2‖ ^ 2 / 2) :
    ennInverseMoment mu (fun x : E => ‖x‖ ^ 2) ≤
      ennInverseMoment (nu.prod (stdGaussian E))
        (fun p : Omega × E => V p.1 * ‖p.2‖ ^ 2 / 2) := by
  apply ennInverseMoment_le_of_laplaceTransform_le_two_measures
    (mu := nu.prod (stdGaussian E)) (nu := mu)
    (U := fun p : Omega × E => V p.1 * ‖p.2‖ ^ 2 / 2)
    (V := fun x : E => ‖x‖ ^ 2)
    (by fun_prop) (by fun_prop) hprodpos hnormpos
  intro t ht
  exact ennLaplace_norm_sq_le_prod_of_charFun_compression
    mu nu V hV hVnonneg hcompression t ht

end

end LogdetLean.GramHafnian
