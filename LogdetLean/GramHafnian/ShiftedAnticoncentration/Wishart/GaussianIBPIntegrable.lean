import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GaussianIBP
/-!
# Gaussian divergence from global integrability

This module packages the Fubini bookkeeping needed to apply the coordinatewise
Gaussian integration-by-parts theorem.  Global integrability under the finite
product Gaussian law automatically supplies the three weighted slice
integrability hypotheses.
-/

open MeasureTheory ProbabilityTheory Real

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Integrability under `N(0,1/2)` implies integrability after multiplication
by its unnormalised density `exp (-x^2)` with respect to Lebesgue measure. -/
theorem integrable_halfGaussianWeight_mul_of_integrable_gaussian
    (f : ℝ → ℝ)
    (hf : Integrable f (gaussianReal 0 halfGaussianVariance)) :
    Integrable (fun x ↦ halfGaussianWeight x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 halfGaussianVariance_ne_zero] at hf
  have hd : Integrable
      (fun x ↦ gaussianPDFReal 0 halfGaussianVariance x * f x) := by
    simpa only [toReal_gaussianPDF, smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul'
        (measurable_gaussianPDF 0 halfGaussianVariance)
        (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)).1 hf
  have hc : IsUnit ((Real.sqrt Real.pi)⁻¹ : ℝ) := by
    rw [isUnit_iff_ne_zero]
    exact inv_ne_zero (Real.sqrt_ne_zero'.2 Real.pi_pos)
  have hscaled : Integrable
      (fun x ↦ (Real.sqrt Real.pi)⁻¹ *
        (halfGaussianWeight x * f x)) := by
    simpa only [gaussianPDFReal_zero_half_eq, mul_assoc] using hd
  exact (integrable_const_mul_iff hc
    (fun x ↦ halfGaussianWeight x * f x)).1 hscaled

/-- The radial weighted slice required by one-dimensional integration by
parts follows from Gaussian integrability of `2*x*f x`. -/
theorem integrable_halfGaussianWeight_radial_of_integrable_gaussian
    (f : ℝ → ℝ)
    (hf : Integrable (fun x ↦ 2 * x * f x)
      (gaussianReal 0 halfGaussianVariance)) :
    Integrable (fun x ↦ (-2 * x * halfGaussianWeight x) * f x) := by
  have h := integrable_halfGaussianWeight_mul_of_integrable_gaussian
    (fun x ↦ 2 * x * f x) hf
  refine h.neg.congr (ae_of_all _ fun x ↦ ?_)
  simp only [Pi.neg_apply]
  ring

/-- A finite-dimensional Gaussian divergence theorem whose assumptions are
only the genuine derivative identity and global integrability. -/
theorem integral_halfGaussianPi_divergence_of_integrable
    {n : ℕ}
    (F dF : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (hslice : ∀ i, ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
      HasDerivAt (fun s ↦ F i (i.insertNth s y))
        (dF i (i.insertNth t y)) t)
    (hvalue : ∀ i, Integrable (F i) (halfGaussianPi (n + 1)))
    (hderiv : ∀ i, Integrable (dF i) (halfGaussianPi (n + 1)))
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * F i x) (halfGaussianPi (n + 1))) :
    (∫ x, ∑ i, dF i x ∂halfGaussianPi (n + 1)) =
      ∫ x, ∑ i, 2 * x i * F i x ∂halfGaussianPi (n + 1) := by
  apply integral_halfGaussianPi_divergence F dF hslice
  · intro i
    let ν : Measure (Fin n → ℝ) := halfGaussianPi n
    let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
    have hem : MeasurePreserving e
        ((gaussianReal 0 halfGaussianVariance).prod ν)
        (halfGaussianPi (n + 1)) := by
      simpa [e, ν, halfGaussianPi] using
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ gaussianReal 0 halfGaussianVariance) i).symm
    have hp : Integrable (dF i ∘ e)
        ((gaussianReal 0 halfGaussianVariance).prod ν) :=
      hem.integrable_comp_of_integrable (hderiv i)
    have hs := hp.prod_left_ae
    filter_upwards [hs] with y hy
    apply integrable_halfGaussianWeight_mul_of_integrable_gaussian
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using hy
  · intro i
    let ν : Measure (Fin n → ℝ) := halfGaussianPi n
    let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
    have hem : MeasurePreserving e
        ((gaussianReal 0 halfGaussianVariance).prod ν)
        (halfGaussianPi (n + 1)) := by
      simpa [e, ν, halfGaussianPi] using
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ gaussianReal 0 halfGaussianVariance) i).symm
    have hp : Integrable ((fun x ↦ 2 * x i * F i x) ∘ e)
        ((gaussianReal 0 halfGaussianVariance).prod ν) :=
      hem.integrable_comp_of_integrable (hradial i)
    have hs := hp.prod_left_ae
    filter_upwards [hs] with y hy
    apply integrable_halfGaussianWeight_radial_of_integrable_gaussian
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using hy
  · intro i
    let ν : Measure (Fin n → ℝ) := halfGaussianPi n
    let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
    have hem : MeasurePreserving e
        ((gaussianReal 0 halfGaussianVariance).prod ν)
        (halfGaussianPi (n + 1)) := by
      simpa [e, ν, halfGaussianPi] using
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ gaussianReal 0 halfGaussianVariance) i).symm
    have hp : Integrable (F i ∘ e)
        ((gaussianReal 0 halfGaussianVariance).prod ν) :=
      hem.integrable_comp_of_integrable (hvalue i)
    have hs := hp.prod_left_ae
    filter_upwards [hs] with y hy
    apply integrable_halfGaussianWeight_mul_of_integrable_gaussian
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using hy
  · exact hderiv
  · exact hradial

end Wishart

end

end LogdetLean.GramHafnian
