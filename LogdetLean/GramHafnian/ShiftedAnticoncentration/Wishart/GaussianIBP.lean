import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.Differentiability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
/-!
# Gaussian integration by parts for the variance-one-half density

The real and imaginary parts of a standard circular complex Gaussian have
density proportional to `exp (-x^2)`.  This file establishes the exact
one-dimensional integration-by-parts identity that will be iterated over the
realified matrix coordinates.
-/

open MeasureTheory ProbabilityTheory Real

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- The unnormalised density of a centred Gaussian of variance `1/2`. -/
def halfGaussianWeight (x : ℝ) : ℝ := Real.exp (-x ^ 2)

/-- Variance parameter of each real coordinate in a standard circular
complex Gaussian. -/
def halfGaussianVariance : NNReal := ⟨1 / 2, by norm_num⟩

@[simp]
theorem halfGaussianVariance_ne_zero : halfGaussianVariance ≠ 0 := by
  intro h
  have h' := congrArg NNReal.toReal h
  change (1 / 2 : ℝ) = 0 at h'
  norm_num at h'

/-- The normalized variance-one-half Gaussian density is a fixed constant
times `halfGaussianWeight`. -/
theorem gaussianPDFReal_zero_half_eq (x : ℝ) :
    gaussianPDFReal 0 halfGaussianVariance x =
      (Real.sqrt Real.pi)⁻¹ * halfGaussianWeight x := by
  unfold gaussianPDFReal halfGaussianWeight
  change
    (Real.sqrt (2 * Real.pi * (1 / 2 : ℝ)))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * (1 / 2 : ℝ))) =
      (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2)
  ring_nf

theorem halfGaussianWeight_pos (x : ℝ) : 0 < halfGaussianWeight x := by
  exact Real.exp_pos _

@[fun_prop]
theorem continuous_halfGaussianWeight : Continuous halfGaussianWeight := by
  unfold halfGaussianWeight
  fun_prop

/-- Derivative of the variance-one-half Gaussian weight. -/
theorem hasDerivAt_halfGaussianWeight (x : ℝ) :
    HasDerivAt halfGaussianWeight
      (-2 * x * halfGaussianWeight x) x := by
  unfold halfGaussianWeight
  convert
    (Real.hasDerivAt_exp (-x ^ 2)).comp x
      (((hasDerivAt_id x).pow 2).neg) using 1 <;>
    first
    | rfl
    | simp [id, mul_comm, mul_left_comm, mul_assoc]
    | ring

/-- One-dimensional Gaussian integration by parts.  The assumptions are
exactly the three integrability conditions used by mathlib's improper
integration-by-parts theorem; no boundary limit is postulated. -/
theorem integral_halfGaussianWeight_mul_deriv_eq
    (v v' : ℝ → ℝ)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hderiv : Integrable (fun x ↦ halfGaussianWeight x * v' x))
    (hradial : Integrable
      (fun x ↦ (-2 * x * halfGaussianWeight x) * v x))
    (hvalue : Integrable (fun x ↦ halfGaussianWeight x * v x)) :
    (∫ x, halfGaussianWeight x * v' x) =
      ∫ x, 2 * x * halfGaussianWeight x * v x := by
  let u : ℝ → ℝ := halfGaussianWeight
  let u' : ℝ → ℝ := fun x ↦ -2 * x * halfGaussianWeight x
  have hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x := by
    intro x _
    exact hasDerivAt_halfGaussianWeight x
  have hv' : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x := by
    intro x _
    exact hv x
  have huv' : Integrable (u * v') := by
    change Integrable (fun x ↦ halfGaussianWeight x * v' x)
    exact hderiv
  have hu'v : Integrable (u' * v) := by
    change Integrable (fun x ↦ (-2 * x * halfGaussianWeight x) * v x)
    exact hradial
  have huv : Integrable (u * v) := by
    change Integrable (fun x ↦ halfGaussianWeight x * v x)
    exact hvalue
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (v := v) (u' := u') (v' := v')
    hu hv' huv' hu'v huv
  calc
    (∫ x, halfGaussianWeight x * v' x) =
        -(∫ x, (-2 * x * halfGaussianWeight x) * v x) := by
      simpa [u, u'] using hibp
    _ = ∫ x, 2 * x * halfGaussianWeight x * v x := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

/-- The same identity under the normalized `N(0,1/2)` probability law.
The volume-integrability hypotheses are exposed because they are exactly what
the determinant and radial cutoffs will provide coordinatewise. -/
theorem integral_gaussianReal_half_deriv_eq
    (v v' : ℝ → ℝ)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hderiv : Integrable (fun x ↦ halfGaussianWeight x * v' x))
    (hradial : Integrable
      (fun x ↦ (-2 * x * halfGaussianWeight x) * v x))
    (hvalue : Integrable (fun x ↦ halfGaussianWeight x * v x)) :
    (∫ x, v' x ∂gaussianReal 0 halfGaussianVariance) =
      ∫ x, 2 * x * v x ∂gaussianReal 0 halfGaussianVariance := by
  rw [integral_gaussianReal_eq_integral_smul halfGaussianVariance_ne_zero,
    integral_gaussianReal_eq_integral_smul halfGaussianVariance_ne_zero]
  simp_rw [smul_eq_mul, gaussianPDFReal_zero_half_eq]
  calc
    (∫ x, (Real.sqrt Real.pi)⁻¹ * halfGaussianWeight x * v' x) =
        (Real.sqrt Real.pi)⁻¹ *
          ∫ x, halfGaussianWeight x * v' x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (Real.sqrt Real.pi)⁻¹ *
          ∫ x, 2 * x * halfGaussianWeight x * v x := by
      rw [integral_halfGaussianWeight_mul_deriv_eq v v' hv hderiv hradial hvalue]
    _ = ∫ x,
          (Real.sqrt Real.pi)⁻¹ * halfGaussianWeight x * (2 * x * v x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

/-- Iid `N(0,1/2)` coordinates on a finite real coordinate space. -/
def halfGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ ↦ gaussianReal 0 halfGaussianVariance)

instance (n : ℕ) : IsProbabilityMeasure (halfGaussianPi n) := by
  unfold halfGaussianPi
  infer_instance

instance (n : ℕ) : SigmaFinite (halfGaussianPi n) := by
  infer_instance

/-- Coordinatewise Gaussian integration by parts on a finite iid product.

The slice hypotheses are deliberately explicit.  For the cutoff Wishart
field they follow from smoothness and compact support in the selected
coordinate.  The two global integrability hypotheses are exactly those
needed for Fubini. -/
theorem integral_halfGaussianPi_coordinate
    {n : ℕ} (i : Fin (n + 1))
    (f f' : (Fin (n + 1) → ℝ) → ℝ)
    (hslice : ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
      HasDerivAt (fun s ↦ f (i.insertNth s y))
        (f' (i.insertNth t y)) t)
    (hsliceDeriv : ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n,
      Integrable (fun t ↦
        halfGaussianWeight t * f' (i.insertNth t y)))
    (hsliceRadial : ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n,
      Integrable (fun t ↦
        (-2 * t * halfGaussianWeight t) * f (i.insertNth t y)))
    (hsliceValue : ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n,
      Integrable (fun t ↦
        halfGaussianWeight t * f (i.insertNth t y)))
    (hderiv : Integrable f' (halfGaussianPi (n + 1)))
    (hradial : Integrable
      (fun x ↦ 2 * x i * f x) (halfGaussianPi (n + 1))) :
    (∫ x, f' x ∂halfGaussianPi (n + 1)) =
      ∫ x, 2 * x i * f x ∂halfGaussianPi (n + 1) := by
  let μ : Fin (n + 1) → Measure ℝ :=
    fun _ ↦ gaussianReal 0 halfGaussianVariance
  let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
  let ν : Measure (Fin n → ℝ) :=
    Measure.pi (fun j ↦ μ (i.succAbove j))
  have hem : MeasurePreserving e
      ((gaussianReal 0 halfGaussianVariance).prod ν)
      (halfGaussianPi (n + 1)) := by
    simpa [e, μ, ν, halfGaussianPi] using
      (measurePreserving_piFinSuccAbove μ i).symm
  have hderivProd : Integrable (f' ∘ e)
      ((gaussianReal 0 halfGaussianVariance).prod ν) :=
    hem.integrable_comp_of_integrable hderiv
  have hradialProd : Integrable
      ((fun x ↦ 2 * x i * f x) ∘ e)
      ((gaussianReal 0 halfGaussianVariance).prod ν) :=
    hem.integrable_comp_of_integrable hradial
  have hslice' : ∀ᵐ y ∂ν, ∀ t : ℝ,
      HasDerivAt (fun s ↦ f (i.insertNth s y))
        (f' (i.insertNth t y)) t := by
    simpa [ν, μ, halfGaussianPi] using hslice
  have hsliceDeriv' : ∀ᵐ y ∂ν,
      Integrable (fun t ↦
        halfGaussianWeight t * f' (i.insertNth t y)) := by
    simpa [ν, μ, halfGaussianPi] using hsliceDeriv
  have hsliceRadial' : ∀ᵐ y ∂ν,
      Integrable (fun t ↦
        (-2 * t * halfGaussianWeight t) * f (i.insertNth t y)) := by
    simpa [ν, μ, halfGaussianPi] using hsliceRadial
  have hsliceValue' : ∀ᵐ y ∂ν,
      Integrable (fun t ↦
        halfGaussianWeight t * f (i.insertNth t y)) := by
    simpa [ν, μ, halfGaussianPi] using hsliceValue
  calc
    (∫ x, f' x ∂halfGaussianPi (n + 1)) =
        ∫ z, f' (e z)
          ∂((gaussianReal 0 halfGaussianVariance).prod ν) := by
      exact (hem.integral_comp' f').symm
    _ = ∫ y, ∫ t, f' (e (t, y))
          ∂gaussianReal 0 halfGaussianVariance ∂ν := by
      exact integral_prod_symm _ hderivProd
    _ = ∫ y, ∫ t, 2 * t * f (e (t, y))
          ∂gaussianReal 0 halfGaussianVariance ∂ν := by
      apply integral_congr_ae
      filter_upwards [hslice', hsliceDeriv', hsliceRadial', hsliceValue']
        with y hy hyD hyR hyV
      have hs := integral_gaussianReal_half_deriv_eq
        (fun t ↦ f (i.insertNth t y))
        (fun t ↦ f' (i.insertNth t y))
        hy hyD hyR hyV
      simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv] using hs
    _ = ∫ z, 2 * z.1 * f (e z)
          ∂((gaussianReal 0 halfGaussianVariance).prod ν) := by
      exact (integral_prod_symm _ (by
        simpa [Function.comp_def, e,
          MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
          hradialProd)).symm
    _ = ∫ x, 2 * x i * f x ∂halfGaussianPi (n + 1) := by
      simpa [Function.comp_def, e,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
        hem.integral_comp' (fun x ↦ 2 * x i * f x)

/-- Finite-dimensional Gaussian divergence theorem obtained by summing the
coordinate identity.  It is formulated for a family of scalar components so
no choice of norm or basis on the target vector space is hidden. -/
theorem integral_halfGaussianPi_divergence
    {n : ℕ}
    (F dF : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (hslice : ∀ i, ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
      HasDerivAt (fun s ↦ F i (i.insertNth s y))
        (dF i (i.insertNth t y)) t)
    (hsliceDeriv : ∀ i, ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n,
      Integrable (fun t ↦
        halfGaussianWeight t * dF i (i.insertNth t y)))
    (hsliceRadial : ∀ i, ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n,
      Integrable (fun t ↦
        (-2 * t * halfGaussianWeight t) * F i (i.insertNth t y)))
    (hsliceValue : ∀ i, ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n,
      Integrable (fun t ↦
        halfGaussianWeight t * F i (i.insertNth t y)))
    (hderiv : ∀ i, Integrable (dF i) (halfGaussianPi (n + 1)))
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * F i x) (halfGaussianPi (n + 1))) :
    (∫ x, ∑ i, dF i x ∂halfGaussianPi (n + 1)) =
      ∫ x, ∑ i, 2 * x i * F i x ∂halfGaussianPi (n + 1) := by
  rw [integral_finset_sum _ (fun i _ ↦ hderiv i),
    integral_finset_sum _ (fun i _ ↦ hradial i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_halfGaussianPi_coordinate i (F i) (dF i)
    (hslice i) (hsliceDeriv i) (hsliceRadial i) (hsliceValue i)
    (hderiv i) (hradial i)

end Wishart

end

end LogdetLean.GramHafnian
