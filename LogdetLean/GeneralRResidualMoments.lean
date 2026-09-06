import LogdetLean.GeneralRRadialMoments
import Mathlib.Tactic
/-!
# Exact moments of the logarithmic radial residual

This file completes the one-column calculation in Lemma 5.2 used for the
residual-variance conclusion (5.3), stated on printed p. 11 and proved on
printed p. 12 of Zhao,
*On the Log Determinant of Sample Correlation Matrices under Gaussianity*,
arXiv:2608.00565v1.

Starting from the density-level Gamma Mellin transform (5.5), printed p. 11,
proved in
`GammaMellin`, it derives the first two Gamma moments and the mixed moment
`E[X log X]`.  These give, on the canonical Gaussian-data probability space,

`Var(e_m(G_i)) = trigammaSeries(m/2) - 2/m <= 4/m^2`.

No Hermite-series completeness or pairwise Mehler formula is used here; those
are separate from this exact one-column computation.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Topology

noncomputable section

/-! ## Scalar Gamma calculations -/

/-- Exact first raw moment of the shape-rate Gamma law. -/
theorem integral_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ∂gammaMeasure a r = a / r := by
  have h := integral_rpow_gammaMeasure (a := a) (r := r) (t := 1)
    ha hr (by linarith)
  simp only [Real.rpow_one] at h
  rw [h, Real.rpow_neg_one, Real.Gamma_add_one ha.ne']
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

/-- Exact second raw moment of the shape-rate Gamma law. -/
theorem integral_sq_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ^ 2 ∂gammaMeasure a r = a * (a + 1) / r ^ 2 := by
  have h : ∫ x, x ^ 2 ∂gammaMeasure a r =
      r ^ (-(2 : ℝ)) * Real.Gamma (a + 2) / Real.Gamma a := by
    simpa only [Real.rpow_two] using
      (integral_rpow_gammaMeasure (a := a) (r := r) (t := 2)
        ha hr (by linarith))
  rw [h, Real.rpow_neg_ofNat]
  norm_num only [Int.reduceNeg, zpow_neg, zpow_ofNat]
  rw [show a + (2 : ℝ) = (a + 1) + 1 by ring,
    Real.Gamma_add_one (by linarith : a + 1 ≠ 0),
    Real.Gamma_add_one ha.ne']
  field_simp [(Real.Gamma_pos_of_pos ha).ne', hr.ne']

/-- Multiplication by `x` shifts a Gamma density by one shape unit. -/
theorem mul_gammaPDFReal_eq_shape_shift {a r x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    x * gammaPDFReal a r x =
      (a / r) * gammaPDFReal (a + 1) r x := by
  have h := rpow_mul_gammaPDFReal (a := a) (r := r) (t := 1)
    ha hr (by linarith) hx
  simp only [Real.rpow_one] at h
  rw [Real.rpow_neg_one, Real.Gamma_add_one ha.ne'] at h
  convert h using 1
  field_simp [(Real.Gamma_pos_of_pos ha).ne', hr.ne']

/-- Exact mixed Gamma moment `E[X log X]`. -/
theorem integral_id_mul_log_gammaMeasure {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x * Real.log x ∂gammaMeasure a r =
      (a / r) * (digammaSeries (a + 1) - Real.log r) := by
  rw [gammaMeasure]
  change (∫ x, x * Real.log x ∂volume.withDensity
    (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal a r).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  have hae : (fun x ↦ gammaPDFReal a r x * (x * Real.log x)) =ᵐ[volume]
      (fun x ↦ (a / r) *
        (gammaPDFReal (a + 1) r x * Real.log x)) := by
    have hne : ∀ᵐ x ∂volume, x ≠ (0 : ℝ) := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx0
    by_cases hx : 0 < x
    · calc
        gammaPDFReal a r x * (x * Real.log x) =
            (x * gammaPDFReal a r x) * Real.log x := by ring
        _ = ((a / r) * gammaPDFReal (a + 1) r x) * Real.log x := by
          rw [mul_gammaPDFReal_eq_shape_shift ha hr hx]
        _ = (a / r) * (gammaPDFReal (a + 1) r x * Real.log x) := by ring
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      simp [gammaPDFReal, not_le.mpr hxneg]
  rw [integral_congr_ae hae, integral_const_mul]
  rw [show (∫ x, gammaPDFReal (a + 1) r x * Real.log x) =
      ∫ x, Real.log x ∂gammaMeasure (a + 1) r by
    rw [gammaMeasure]
    change _ = ∫ x, Real.log x ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (gammaPDFReal (a + 1) r x))
    rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_gammaPDFReal (a + 1) r).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ENNReal.toReal_ofReal
      (gammaPDFReal_nonneg (by linarith) hr x)]
    rfl]
  rw [integral_log_gammaMeasure_eq (by linarith) hr]

/-- The locally constructed digamma series obeys its classical unit-shift
recurrence.  This is derived from the Gamma functional equation and the
already verified identification with the derivative of `log Gamma`. -/
theorem digammaSeries_add_one {x : ℝ} (hx : 0 < x) :
    digammaSeries (x + 1) = digammaSeries x + 1 / x := by
  let f : ℝ → ℝ := Real.log ∘ Real.Gamma
  have hf (y : ℝ) (hy : 0 < y) :
      HasDerivAt f (digammaSeries y) y := by
    have hd : DifferentiableAt ℝ f y :=
      (Real.differentiableAt_Gamma (fun n ↦ by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)).log (Real.Gamma_pos_of_pos hy).ne'
    rw [← deriv_logGamma_eq_digammaSeries hy]
    exact hd.hasDerivAt
  have hleft := (hf (x + 1) (by linarith)).comp x
    ((hasDerivAt_id x).add_const 1)
  have hright := (hf x hx).add (Real.hasDerivAt_log hx.ne')
  have heq : (f ∘ (fun y : ℝ ↦ y + 1)) =ᶠ[nhds x]
      (f + Real.log) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    change f (y + 1) = f y + Real.log y
    unfold f
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hu := hleft.unique (heq.hasDerivAt_iff.mpr hright)
  simpa only [mul_one, one_div] using hu

/-! ## Transfer to a Gaussian column -/

namespace GeneralRDecomposition

variable {m p : ℕ}

/-- Exact second raw moment of `Q_i ~ chi-square_m`. -/
theorem integral_Q_sq_eq (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) :
    ∫ z, Q R z i ^ 2 ∂standardGaussianDataMeasure m p =
      (m : ℝ) * ((m : ℝ) + 2) := by
  calc
    ∫ z, Q R z i ^ 2 ∂standardGaussianDataMeasure m p =
        ∫ q, q ^ 2 ∂gammaMeasure ((m : ℝ) / 2) (1 / 2) :=
      (hasLaw_Q_gamma hm R i).integral_comp
        ((measurable_id'.pow_const 2).aestronglyMeasurable)
    _ = ((m : ℝ) / 2) * ((m : ℝ) / 2 + 1) /
        (1 / 2 : ℝ) ^ 2 :=
      integral_sq_gammaMeasure (by positivity) (by norm_num)
    _ = (m : ℝ) * ((m : ℝ) + 2) := by ring

/-- Exact mixed moment of the chi-square energy and its logarithm. -/
theorem integral_Q_mul_log_Q_eq (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, Q R z i * Real.log (Q R z i)
        ∂standardGaussianDataMeasure m p =
      (m : ℝ) * (chiSquareLogMean m + 2 / (m : ℝ)) := by
  calc
    ∫ z, Q R z i * Real.log (Q R z i)
        ∂standardGaussianDataMeasure m p =
        ∫ q, q * Real.log q
          ∂gammaMeasure ((m : ℝ) / 2) (1 / 2) :=
      (hasLaw_Q_gamma hm R i).integral_comp
        ((measurable_id'.mul measurable_id'.log).aestronglyMeasurable)
    _ = (((m : ℝ) / 2) / (1 / 2 : ℝ)) *
        (digammaSeries ((m : ℝ) / 2 + 1) - Real.log (1 / 2)) :=
      integral_id_mul_log_gammaMeasure (by positivity) (by norm_num)
    _ = (m : ℝ) * (chiSquareLogMean m + 2 / (m : ℝ)) := by
      rw [digammaSeries_add_one (by positivity),
        chiSquareLogMean_eq_digamma_add_log_two hm]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-! ## Square integrability and the residual variance -/

/-- The chi-square energy is square-integrable. -/
theorem integrable_Q_sq (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) :
    Integrable (fun z : GaussianData m p ↦ Q R z i ^ 2)
      (standardGaussianDataMeasure m p) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_Q_sq_eq hm R i]
  positivity

/-- The chi-square energy belongs to `L^2`. -/
theorem memLp_Q_two (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) :
    MemLp (fun z : GaussianData m p ↦ Q R z i) 2
      (standardGaussianDataMeasure m p) := by
  exact (memLp_two_iff_integrable_sq
    (measurable_Q R i).aestronglyMeasurable).2 (integrable_Q_sq hm R i)

/-- The log-energy belongs to `L^2`. -/
theorem memLp_log_Q_two (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) :
    MemLp (fun z : GaussianData m p ↦ Real.log (Q R z i)) 2
      (standardGaussianDataMeasure m p) := by
  exact (memLp_two_iff_integrable_sq
    ((measurable_Q R i).log.aestronglyMeasurable)).2
      (integrable_pow_log_Q hm R i 2)

/-- The mixed product `Q_i log Q_i` is integrable. -/
theorem integrable_Q_mul_log_Q (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Integrable (fun z : GaussianData m p ↦
      Q R z i * Real.log (Q R z i))
      (standardGaussianDataMeasure m p) :=
  MemLp.integrable_mul (memLp_Q_two hm R i) (memLp_log_Q_two hm R i)

/-- The centered log-energy `h_m(G_i)` belongs to `L^2`. -/
theorem memLp_h_m_G_two (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) :
    MemLp (fun z : GaussianData m p ↦ h_m m (G R z i)) 2
      (standardGaussianDataMeasure m p) := by
  exact (memLp_two_iff_integrable_sq
    ((measurable_h_m m).comp (measurable_G R i)).aestronglyMeasurable).2
      (integrable_h_m_G_sq hm R i)

/-- The linear radial fluctuation `u_m(G_i)` belongs to `L^2`. -/
theorem memLp_u_m_G_two (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) :
    MemLp (fun z : GaussianData m p ↦ u_m m (G R z i)) 2
      (standardGaussianDataMeasure m p) := by
  change MemLp (fun z : GaussianData m p ↦
    (Q R z i - (m : ℝ)) / (m : ℝ)) 2 _
  have h := ((memLp_Q_two hm R i).sub
    (memLp_const (m : ℝ))).mul_const ((m : ℝ)⁻¹)
  apply h.ae_eq
  filter_upwards [] with z
  rfl

/-- The nonlinear residual `e_m(G_i)` belongs to `L^2`. -/
theorem memLp_e_m_G_two (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) :
    MemLp (fun z : GaussianData m p ↦ e_m m (G R z i)) 2
      (standardGaussianDataMeasure m p) :=
  (memLp_h_m_G_two hm R i).sub (memLp_u_m_G_two hm R i)

/-- The normalized linear chi-square fluctuation has second moment `2/m`. -/
theorem integral_u_m_G_sq_eq (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, u_m m (G R z i) ^ 2
        ∂standardGaussianDataMeasure m p = 2 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  change ∫ z, ((Q R z i - (m : ℝ)) / (m : ℝ)) ^ 2
      ∂standardGaussianDataMeasure m p = _
  have hpoint : (fun z : GaussianData m p ↦
      ((Q R z i - (m : ℝ)) / (m : ℝ)) ^ 2) =
      (fun z ↦ (Q R z i ^ 2 -
        (2 * (m : ℝ)) * Q R z i + (m : ℝ) ^ 2) /
          (m : ℝ) ^ 2) := by
    funext z
    field_simp
    ring
  rw [hpoint, integral_div]
  rw [integral_add
    (f := fun z : GaussianData m p ↦
      Q R z i ^ 2 - (2 * (m : ℝ)) * Q R z i)
    (g := fun _z : GaussianData m p ↦ (m : ℝ) ^ 2)
    ((integrable_Q_sq hm R i).sub
      ((integrable_Q R i).const_mul (2 * (m : ℝ))))
    (integrable_const ((m : ℝ) ^ 2))]
  rw [integral_sub
    (f := fun z : GaussianData m p ↦ Q R z i ^ 2)
    (g := fun z : GaussianData m p ↦ (2 * (m : ℝ)) * Q R z i)
    (integrable_Q_sq hm R i)
    ((integrable_Q R i).const_mul (2 * (m : ℝ)))]
  rw [integral_const_mul, integral_const,
    integral_Q_sq_eq hm R i, integral_Q_eq_m]
  simp only [probReal_univ, one_smul]
  field_simp
  ring

/-- The centered log-energy and the normalized linear fluctuation have exact
inner product `2/m`.  This verifies that `u_m` is precisely the second-chaos
projection coefficient used in Lemma 5.2. -/
theorem integral_h_m_G_mul_u_m_G_eq (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, h_m m (G R z i) * u_m m (G R z i)
        ∂standardGaussianDataMeasure m p = 2 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  change ∫ z, (Real.log (Q R z i) - chiSquareLogMean m) *
      ((Q R z i - (m : ℝ)) / (m : ℝ))
      ∂standardGaussianDataMeasure m p = _
  have hpoint : (fun z : GaussianData m p ↦
      (Real.log (Q R z i) - chiSquareLogMean m) *
        ((Q R z i - (m : ℝ)) / (m : ℝ))) =
      (fun z ↦ (Q R z i * Real.log (Q R z i) -
          (m : ℝ) * Real.log (Q R z i) -
          chiSquareLogMean m * Q R z i +
          chiSquareLogMean m * (m : ℝ)) / (m : ℝ)) := by
    funext z
    field_simp
    ring
  rw [hpoint, integral_div]
  rw [integral_add
    (f := fun z : GaussianData m p ↦
      Q R z i * Real.log (Q R z i) -
        (m : ℝ) * Real.log (Q R z i) -
        chiSquareLogMean m * Q R z i)
    (g := fun _z : GaussianData m p ↦
      chiSquareLogMean m * (m : ℝ))
    (((integrable_Q_mul_log_Q hm R i).sub
      ((integrable_log_Q hm R i).const_mul (m : ℝ))).sub
      ((integrable_Q R i).const_mul (chiSquareLogMean m)))
    (integrable_const (chiSquareLogMean m * (m : ℝ)))]
  rw [integral_sub
    (f := fun z : GaussianData m p ↦
      Q R z i * Real.log (Q R z i) -
        (m : ℝ) * Real.log (Q R z i))
    (g := fun z : GaussianData m p ↦
      chiSquareLogMean m * Q R z i)
    ((integrable_Q_mul_log_Q hm R i).sub
      ((integrable_log_Q hm R i).const_mul (m : ℝ)))
    ((integrable_Q R i).const_mul (chiSquareLogMean m))]
  rw [integral_sub (integrable_Q_mul_log_Q hm R i)
    (f := fun z : GaussianData m p ↦
      Q R z i * Real.log (Q R z i))
    (g := fun z : GaussianData m p ↦
      (m : ℝ) * Real.log (Q R z i))
    ((integrable_log_Q hm R i).const_mul (m : ℝ))]
  rw [integral_const_mul, integral_const_mul, integral_const,
    integral_Q_mul_log_Q_eq hm R i,
    integral_log_Q_eq_chiSquareLogMean hm,
    integral_Q_eq_m]
  simp only [probReal_univ, one_smul]
  field_simp
  ring

/-- Exact variance of the centered log-energy. -/
theorem variance_h_m_G_eq_trigamma (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Var[fun z : GaussianData m p ↦ h_m m (G R z i);
      standardGaussianDataMeasure m p] =
      trigammaSeries ((m : ℝ) / 2) := by
  change Var[fun z : GaussianData m p ↦
    Real.log (Q R z i) - chiSquareLogMean m;
    standardGaussianDataMeasure m p] = _
  rw [variance_sub_const (measurable_Q R i).log.aestronglyMeasurable]
  exact variance_log_Q_eq_trigamma hm R i

/-- Exact variance of the normalized linear radial fluctuation. -/
theorem variance_u_m_G_eq (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Var[fun z : GaussianData m p ↦ u_m m (G R z i);
      standardGaussianDataMeasure m p] = 2 / (m : ℝ) := by
  calc
    Var[fun z : GaussianData m p ↦ u_m m (G R z i);
        standardGaussianDataMeasure m p] =
        ∫ z, u_m m (G R z i) ^ 2
          ∂standardGaussianDataMeasure m p :=
      variance_of_integral_eq_zero
        ((measurable_u_m m).comp (measurable_G R i)).aemeasurable
        (integral_u_m_G_eq_zero R i)
    _ = 2 / (m : ℝ) := integral_u_m_G_sq_eq hm R i

/-- Exact covariance between the centered log-energy and its linear radial
projection. -/
theorem covariance_h_m_G_u_m_G_eq (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    cov[fun z : GaussianData m p ↦ h_m m (G R z i),
      fun z ↦ u_m m (G R z i);
      standardGaussianDataMeasure m p] = 2 / (m : ℝ) := by
  rw [covariance_eq_sub (memLp_h_m_G_two hm R i)
    (memLp_u_m_G_two hm R i)]
  rw [integral_h_m_G_eq_zero_unconditional hm R i,
    integral_u_m_G_eq_zero R i]
  simp only [mul_zero, sub_zero]
  exact integral_h_m_G_mul_u_m_G_eq hm R i

/-- The nonlinear residual is orthogonal in `L^2` to the radial second-chaos
candidate `u_m`. -/
theorem integral_e_m_G_mul_u_m_G_eq_zero (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, e_m m (G R z i) * u_m m (G R z i)
        ∂standardGaussianDataMeasure m p = 0 := by
  change ∫ z, (h_m m (G R z i) - u_m m (G R z i)) *
      u_m m (G R z i) ∂standardGaussianDataMeasure m p = 0
  have hhu : Integrable (fun z : GaussianData m p ↦
      h_m m (G R z i) * u_m m (G R z i))
      (standardGaussianDataMeasure m p) :=
    MemLp.integrable_mul (memLp_h_m_G_two hm R i)
      (memLp_u_m_G_two hm R i)
  have huu : Integrable (fun z : GaussianData m p ↦
      u_m m (G R z i) * u_m m (G R z i))
      (standardGaussianDataMeasure m p) :=
    MemLp.integrable_mul (memLp_u_m_G_two hm R i)
      (memLp_u_m_G_two hm R i)
  have hpoint : (fun z : GaussianData m p ↦
      (h_m m (G R z i) - u_m m (G R z i)) *
        u_m m (G R z i)) =
      (fun z ↦ h_m m (G R z i) * u_m m (G R z i) -
        u_m m (G R z i) ^ 2) := by
    funext z
    ring
  rw [hpoint, integral_sub hhu (by simpa only [pow_two] using huu),
    integral_h_m_G_mul_u_m_G_eq hm R i,
    integral_u_m_G_sq_eq hm R i, sub_self]

/-- Exact one-column residual variance, equation (5.3) of Zhao. -/
theorem variance_e_m_G_eq (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Var[fun z : GaussianData m p ↦ e_m m (G R z i);
      standardGaussianDataMeasure m p] =
      trigammaSeries ((m : ℝ) / 2) - 2 / (m : ℝ) := by
  change Var[fun z : GaussianData m p ↦
      h_m m (G R z i) - u_m m (G R z i);
    standardGaussianDataMeasure m p] = _
  rw [variance_fun_sub (memLp_h_m_G_two hm R i)
    (memLp_u_m_G_two hm R i),
    variance_h_m_G_eq_trigamma hm R i,
    covariance_h_m_G_u_m_G_eq hm R i,
    variance_u_m_G_eq hm R i]
  ring

/-- The exact residual variance is nonnegative (also immediate because it is
a variance). -/
theorem residual_variance_expression_nonneg (hm : 0 < m) :
    0 ≤ trigammaSeries ((m : ℝ) / 2) - 2 / (m : ℝ) := by
  have h := one_div_le_trigammaSeries
    (show 0 < (m : ℝ) / 2 by positivity)
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  convert sub_nonneg.mpr h using 1
  field_simp

/-- Uniform one-column bound in equation (5.3). -/
theorem variance_e_m_G_le_four_div_sq (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Var[fun z : GaussianData m p ↦ e_m m (G R z i);
      standardGaussianDataMeasure m p] ≤ 4 / (m : ℝ) ^ 2 := by
  rw [variance_e_m_G_eq hm R i]
  have h := trigammaSeries_le_one_div_add_one_div_sq
    (show 0 < (m : ℝ) / 2 by positivity)
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  calc
    trigammaSeries ((m : ℝ) / 2) - 2 / (m : ℝ) ≤
        (1 / ((m : ℝ) / 2) + 1 / ((m : ℝ) / 2) ^ 2) -
          2 / (m : ℝ) := sub_le_sub_right h _
    _ = 4 / (m : ℝ) ^ 2 := by field_simp; ring

end GeneralRDecomposition

end
end LogdetLean
