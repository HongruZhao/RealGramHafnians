import LogdetLean.GammaMellin
import LogdetLean.GeneralRDecomposition
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
/-!
# Exact one-column radial moments for the general-correlation decomposition

This file removes the provisional log-integrability hypotheses from the
one-column part of `GeneralRDecomposition`.  It combines the already proved
law `Q_i ~ Gamma(m/2,1/2)` with `GammaMellin`'s density-level Mellin proof.

The mathematical identities are the one-column log-moment calculations in
Lemma 5.2, printed pp. 11--12 of Zhao, *On the Log Determinant of Sample
Correlation Matrices under Gaussianity* (arXiv:2608.00565v1).  They feed the
residual-variance conclusion (5.3); the pairwise covariance conclusion (5.4)
requires the separate Hermite/Mehler step.  The proof here derives the radial
identities from the Gamma density rather than importing the paper as an axiom.
-/

namespace LogdetLean
namespace GeneralRDecomposition

noncomputable section

open MeasureTheory ProbabilityTheory

variable {m p : ℕ}

/-- The named chi-square logarithmic mean is the explicit digamma value. -/
theorem chiSquareLogMean_eq_digamma_add_log_two (hm : 0 < m) :
    chiSquareLogMean m =
      digammaSeries ((m : ℝ) / 2) + Real.log 2 := by
  rw [chiSquareLogMean,
    integral_log_gammaMeasure_eq (by positivity) (by norm_num)]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- `log Q_i` is integrable on the canonical common probability space. -/
theorem integrable_log_Q (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) :
    Integrable (fun z : GaussianData m p ↦ Real.log (Q R z i))
      (standardGaussianDataMeasure m p) := by
  have hpres := (hasLaw_Q_gamma hm R i).measurePreserving
    (measurable_Q R i)
  simpa [Function.comp_def] using hpres.integrable_comp_of_integrable
    (integrable_pow_log_gammaMeasure (by positivity) (by norm_num) 1)

/-- All finite log-energy powers are integrable. -/
theorem integrable_pow_log_Q (hm : 0 < m) (R : CorrelationMatrix p)
    (i : Fin p) (n : ℕ) :
    Integrable (fun z : GaussianData m p ↦ Real.log (Q R z i) ^ n)
      (standardGaussianDataMeasure m p) := by
  have hpres := (hasLaw_Q_gamma hm R i).measurePreserving
    (measurable_Q R i)
  exact hpres.integrable_comp_of_integrable
    (integrable_pow_log_gammaMeasure (by positivity) (by norm_num) n)

/-- The centered log-energy has exact second moment `trigamma(m/2)`. -/
theorem integral_h_m_G_sq_eq_trigamma (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, h_m m (G R z i) ^ 2
        ∂standardGaussianDataMeasure m p =
      trigammaSeries ((m : ℝ) / 2) := by
  change ∫ z, (Real.log (Q R z i) - chiSquareLogMean m) ^ 2
      ∂standardGaussianDataMeasure m p = _
  unfold chiSquareLogMean
  calc
    ∫ z, (Real.log (Q R z i) -
          ∫ q, Real.log q ∂gammaMeasure ((m : ℝ) / 2) (1 / 2)) ^ 2
          ∂standardGaussianDataMeasure m p =
        ∫ q, (Real.log q -
          ∫ y, Real.log y ∂gammaMeasure ((m : ℝ) / 2) (1 / 2)) ^ 2
          ∂gammaMeasure ((m : ℝ) / 2) (1 / 2) := by
      exact (hasLaw_Q_gamma hm R i).integral_comp
        (((measurable_id.log.sub_const _).pow_const 2).aestronglyMeasurable)
    _ = trigammaSeries ((m : ℝ) / 2) :=
      integral_centered_sq_log_gammaMeasure_eq
        (a := (m : ℝ) / 2) (r := 1 / 2) (by positivity) (by norm_num)

/-- The centered log-energy is square-integrable. -/
theorem integrable_h_m_G_sq (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Integrable (fun z : GaussianData m p ↦ h_m m (G R z i) ^ 2)
      (standardGaussianDataMeasure m p) := by
  change Integrable (fun z : GaussianData m p ↦
    (Real.log (Q R z i) - chiSquareLogMean m) ^ 2) _
  simp_rw [sub_sq]
  have h := ((integrable_pow_log_Q hm R i 2).sub
    (((integrable_log_Q hm R i).const_mul (2 * chiSquareLogMean m)))).add
      (integrable_const (chiSquareLogMean m ^ 2))
  exact h.congr (ae_of_all _ fun z ↦ by
    simp only [Pi.add_apply, Pi.sub_apply]
    ring)

/-- The exact one-column log variance, in Mathlib's variance notation. -/
theorem variance_log_Q_eq_trigamma (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Var[(fun z : GaussianData m p ↦ Real.log (Q R z i));
      standardGaussianDataMeasure m p] =
      trigammaSeries ((m : ℝ) / 2) := by
  rw [variance_eq_integral (measurable_Q R i).log.aemeasurable]
  rw [integral_log_Q_eq_chiSquareLogMean hm]
  exact integral_h_m_G_sq_eq_trigamma hm R i

/-- The exact centering theorem from the decomposition, now without an
extra user-supplied integrability hypothesis. -/
theorem integral_h_m_G_eq_zero_unconditional (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, h_m m (G R z i) ∂standardGaussianDataMeasure m p = 0 :=
  integral_h_m_G_eq_zero hm R i (integrable_log_Q hm R i)

/-- The nonlinear one-column residual is integrable without an extra
hypothesis. -/
theorem integrable_e_m_G_unconditional (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Integrable (fun z : GaussianData m p ↦ e_m m (G R z i))
      (standardGaussianDataMeasure m p) :=
  integrable_e_m_G R i (integrable_log_Q hm R i)

/-- The nonlinear one-column residual is exactly centered. -/
theorem integral_e_m_G_eq_zero_unconditional (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    ∫ z, e_m m (G R z i) ∂standardGaussianDataMeasure m p = 0 :=
  integral_e_m_G_eq_zero hm R i (integrable_log_Q hm R i)

end
end GeneralRDecomposition
end LogdetLean
