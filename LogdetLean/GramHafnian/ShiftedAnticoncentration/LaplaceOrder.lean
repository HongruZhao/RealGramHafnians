import LogdetLean.GramHafnian.ShiftedAnticoncentration.Normalization
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
/-!
# Laplace order and inverse moments

This module proves the Tonelli step converting a Laplace-transform comparison
of positive random variables into the inverse-moment comparison used by the
hafnian induction.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Nonnegative Laplace transform, kept in `ℝ≥0∞` so no integrability
assumption is required. -/
def ennLaplaceTransform (μ : Measure Ω) (U : Ω → ℝ) (t : ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * U ω)) ∂μ

/-- Nonnegative inverse moment, likewise represented as a lintegral. -/
def ennInverseMoment (μ : Measure Ω) (U : Ω → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal ((U ω)⁻¹) ∂μ

/-- For a nonnegative observable on a probability space, the `ENNReal`
Laplace transform is the `ofReal` of the ordinary (finite) integral. -/
theorem ennLaplaceTransform_eq_ofReal_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (hU : Measurable U) (hUnonneg : ∀ ω, 0 ≤ U ω)
    (t : ℝ) (ht : 0 ≤ t) :
    ennLaplaceTransform μ U t =
      ENNReal.ofReal (∫ ω, Real.exp (-t * U ω) ∂μ) := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (-t * U ω)) μ :=
    (hU.const_mul (-t)).exp.aestronglyMeasurable
  have hint : Integrable (fun ω => Real.exp (-t * U ω)) μ := by
    apply Integrable.of_bound hmeas 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hUnonneg ω))
  have hnonneg : 0 ≤ᵐ[μ] (fun ω => Real.exp (-t * U ω)) :=
    ae_of_all _ fun _ => (Real.exp_pos _).le
  unfold ennLaplaceTransform
  exact (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm

lemma lintegral_exp_neg_mul_Ioi (x : ℝ) (hx : 0 < x) :
    ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-t * x)) = ENNReal.ofReal x⁻¹ := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t * x)) (Ioi 0) := by
    simpa [mul_comm] using
      (integrableOn_exp_mul_Ioi (a := -x) (by linarith) 0)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => Real.exp (-t * x)) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [show (fun t : ℝ => Real.exp (-t * x)) =
      (fun t : ℝ => Real.exp (-x * t)) by funext t; congr 1 <;> ring,
    integral_exp_mul_Ioi (a := -x) (by linarith) 0]
  simp only [mul_zero, Real.exp_zero, neg_div, neg_neg]
  congr 1
  field_simp

theorem ennInverseMoment_le_of_laplaceTransform_le
    (μ : Measure Ω) [SFinite μ]
    (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hUpos : ∀ᵐ ω ∂μ, 0 < U ω) (hVpos : ∀ᵐ ω ∂μ, 0 < V ω)
    (hLap : ∀ t : ℝ, 0 ≤ t →
      ennLaplaceTransform μ V t ≤ ennLaplaceTransform μ U t) :
    ennInverseMoment μ V ≤ ennInverseMoment μ U := by
  have hmeasV : Measurable
      (fun p : Ω × ℝ => ENNReal.ofReal (Real.exp (-p.2 * V p.1))) :=
    ((measurable_snd.neg.mul (hV.comp measurable_fst)).exp).ennreal_ofReal
  have hmeasU : Measurable
      (fun p : Ω × ℝ => ENNReal.ofReal (Real.exp (-p.2 * U p.1))) :=
    ((measurable_snd.neg.mul (hU.comp measurable_fst)).exp).ennreal_ofReal
  rw [ennInverseMoment, ennInverseMoment]
  calc
    (∫⁻ ω, ENNReal.ofReal (V ω)⁻¹ ∂μ) =
        ∫⁻ ω, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-t * V ω)) ∂volume ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hVpos] with ω hω
      exact (lintegral_exp_neg_mul_Ioi (V ω) hω).symm
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ ω,
          ENNReal.ofReal (Real.exp (-t * V ω)) ∂μ ∂volume := by
      rw [lintegral_lintegral_swap hmeasV.aemeasurable]
    _ ≤ ∫⁻ t : ℝ in Ioi 0, ∫⁻ ω,
          ENNReal.ofReal (Real.exp (-t * U ω)) ∂μ ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hLap t (le_of_lt ht)
    _ = ∫⁻ ω, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-t * U ω)) ∂volume ∂μ := by
      symm
      rw [lintegral_lintegral_swap hmeasU.aemeasurable]
    _ = ∫⁻ ω, ENNReal.ofReal (U ω)⁻¹ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hUpos] with ω hω
      exact lintegral_exp_neg_mul_Ioi (U ω) hω

variable {Omega' : Type*} [MeasurableSpace Omega']

/-- Cross-space form of the same Tonelli argument.  This is useful when the
larger Laplace transform is realized by adjoining an independent auxiliary
Gaussian on a product probability space. -/
theorem ennInverseMoment_le_of_laplaceTransform_le_two_measures
    (mu : Measure Ω) [SFinite mu]
    (nu : Measure Omega') [SFinite nu]
    (U : Ω -> ℝ) (V : Omega' -> ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (hUpos : ∀ᵐ w ∂mu, 0 < U w)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (hLap : ∀ t : ℝ, 0 ≤ t ->
      ennLaplaceTransform nu V t ≤ ennLaplaceTransform mu U t) :
    ennInverseMoment nu V ≤ ennInverseMoment mu U := by
  have hmeasV : Measurable
      (fun p : Omega' × ℝ => ENNReal.ofReal (Real.exp (-p.2 * V p.1))) :=
    ((measurable_snd.neg.mul (hV.comp measurable_fst)).exp).ennreal_ofReal
  have hmeasU : Measurable
      (fun p : Ω × ℝ => ENNReal.ofReal (Real.exp (-p.2 * U p.1))) :=
    ((measurable_snd.neg.mul (hU.comp measurable_fst)).exp).ennreal_ofReal
  rw [ennInverseMoment, ennInverseMoment]
  calc
    (∫⁻ w, ENNReal.ofReal (V w)⁻¹ ∂nu) =
        ∫⁻ w, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-t * V w)) ∂volume ∂nu := by
      apply lintegral_congr_ae
      filter_upwards [hVpos] with w hw
      exact (lintegral_exp_neg_mul_Ioi (V w) hw).symm
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ w,
          ENNReal.ofReal (Real.exp (-t * V w)) ∂nu ∂volume := by
      rw [lintegral_lintegral_swap hmeasV.aemeasurable]
    _ ≤ ∫⁻ t : ℝ in Ioi 0, ∫⁻ w,
          ENNReal.ofReal (Real.exp (-t * U w)) ∂mu ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hLap t (le_of_lt ht)
    _ = ∫⁻ w, ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-t * U w)) ∂volume ∂mu := by
      symm
      rw [lintegral_lintegral_swap hmeasU.aemeasurable]
    _ = ∫⁻ w, ENNReal.ofReal (U w)⁻¹ ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hUpos] with w hw
      exact lintegral_exp_neg_mul_Ioi (U w) hw

end

end LogdetLean.GramHafnian
