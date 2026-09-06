import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.PreservedSMeasureExtension
import Mathlib.Geometry.Manifold.SmoothApprox
/-!
# Bounded coordinate tests from smooth compactly supported tests

On a finite-dimensional real normed space, smooth compactly supported
functions are uniformly dense in continuous compactly supported functions.
Consequently the measure-extension theorem in `PreservedSMeasureExtension`
only needs an identity for smooth compactly supported coordinate weights.
-/

open MeasureTheory
open scoped CompactlySupported

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {Ω X : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]

/-- An integral identity for smooth compactly supported functions of a
finite-dimensional coordinate implies the same identity for every bundled
continuous compactly supported coordinate test. -/
theorem integral_comp_mul_eq_compactlySupported_of_contDiff
    (μ : Measure Ω) (S : Ω → X) (f h : Ω → ℝ)
    (hS : Measurable S) (hf : Integrable f μ) (hh : Integrable h μ)
    (hsmooth : ∀ (g : X → ℝ), ContDiff ℝ 1 g → HasCompactSupport g →
      ((∫ ω, g (S ω) * f ω ∂μ) =
        (∫ ω, g (S ω) * h ω ∂μ))) :
    ∀ φ : C_c(X, ℝ),
      (∫ ω, φ (S ω) * f ω ∂μ) =
        ∫ ω, φ (S ω) * h ω ∂μ := by
  intro φ
  have hφmeas : AEStronglyMeasurable (fun ω ↦ φ (S ω)) μ :=
    (φ.continuous.measurable.comp hS).aestronglyMeasurable
  have hφbound : ∀ x : X, ‖φ x‖ ≤
      ‖φ.toBoundedContinuousFunction‖ :=
    fun x ↦ BoundedContinuousFunction.norm_coe_le_norm
      φ.toBoundedContinuousFunction x
  have hφf : Integrable (fun ω ↦ φ (S ω) * f ω) μ :=
    hf.bdd_mul hφmeas <|
      Filter.Eventually.of_forall fun ω ↦ hφbound (S ω)
  have hφh : Integrable (fun ω ↦ φ (S ω) * h ω) μ :=
    hh.bdd_mul hφmeas <|
      Filter.Eventually.of_forall fun ω ↦ hφbound (S ω)
  by_contra hne
  let A : ℝ :=
    (∫ ω, φ (S ω) * f ω ∂μ) -
      ∫ ω, φ (S ω) * h ω ∂μ
  have hAne : A ≠ 0 := sub_ne_zero.mpr hne
  have hApos : 0 < |A| := abs_pos.mpr hAne
  let M : ℝ := (∫ ω, |f ω| ∂μ) + ∫ ω, |h ω| ∂μ
  have hMf : 0 ≤ ∫ ω, |f ω| ∂μ :=
    integral_nonneg fun _ ↦ abs_nonneg _
  have hMh : 0 ≤ ∫ ω, |h ω| ∂μ :=
    integral_nonneg fun _ ↦ abs_nonneg _
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  let ε : ℝ := |A| / (M + 1)
  have hden : 0 < M + 1 := by linarith
  have hε : 0 < ε := div_pos hApos hden
  obtain ⟨g, hgdiff, hgapprox, hgsupp⟩ :=
    φ.continuous.exists_contDiff_approx 1 continuous_const (fun _ ↦ hε)
  have hgdiffOne : ContDiff ℝ 1 g := by simpa using hgdiff
  have hgcomp : HasCompactSupport g := φ.hasCompactSupport.mono hgsupp
  have hgmeas : AEStronglyMeasurable (fun ω ↦ g (S ω)) μ :=
    (hgdiff.continuous.measurable.comp hS).aestronglyMeasurable
  have hcoef : ∀ ω : Ω, |φ (S ω) - g (S ω)| ≤ ε := by
    intro ω
    have hw := (hgapprox (S ω)).le
    simpa [Real.dist_eq, abs_sub_comm] using hw
  have hcoefNorm : ∀ᵐ ω ∂μ,
      ‖φ (S ω) - g (S ω)‖ ≤ ε :=
    Filter.Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using hcoef ω
  have herrfint : Integrable
      (fun ω ↦ (φ (S ω) - g (S ω)) * f ω) μ :=
    hf.bdd_mul (hφmeas.sub hgmeas) hcoefNorm
  have herrhint : Integrable
      (fun ω ↦ (φ (S ω) - g (S ω)) * h ω) μ :=
    hh.bdd_mul (hφmeas.sub hgmeas) hcoefNorm
  have hgf : Integrable (fun ω ↦ g (S ω) * f ω) μ := by
    have hi := hφf.sub herrfint
    exact hi.congr <| Filter.Eventually.of_forall fun ω ↦ by
      change φ (S ω) * f ω -
        ((φ (S ω) - g (S ω)) * f ω) = g (S ω) * f ω
      ring
  have hgh : Integrable (fun ω ↦ g (S ω) * h ω) μ := by
    have hi := hφh.sub herrhint
    exact hi.congr <| Filter.Eventually.of_forall fun ω ↦ by
      change φ (S ω) * h ω -
        ((φ (S ω) - g (S ω)) * h ω) = g (S ω) * h ω
      ring
  have herrf :
      |(∫ ω, φ (S ω) * f ω ∂μ) -
          ∫ ω, g (S ω) * f ω ∂μ| ≤
        ε * ∫ ω, |f ω| ∂μ := by
    calc
      |(∫ ω, φ (S ω) * f ω ∂μ) -
          ∫ ω, g (S ω) * f ω ∂μ| =
          ‖∫ ω, φ (S ω) * f ω - g (S ω) * f ω ∂μ‖ := by
            rw [integral_sub hφf hgf, Real.norm_eq_abs]
      _ ≤ ∫ ω, ε * |f ω| ∂μ := by
        apply norm_integral_le_of_norm_le (hf.norm.const_mul ε)
        filter_upwards [] with ω
        rw [← sub_mul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hcoef ω) (abs_nonneg (f ω))
      _ = ε * ∫ ω, |f ω| ∂μ := integral_const_mul _ _
  have herrh :
      |(∫ ω, φ (S ω) * h ω ∂μ) -
          ∫ ω, g (S ω) * h ω ∂μ| ≤
        ε * ∫ ω, |h ω| ∂μ := by
    calc
      |(∫ ω, φ (S ω) * h ω ∂μ) -
          ∫ ω, g (S ω) * h ω ∂μ| =
          ‖∫ ω, φ (S ω) * h ω - g (S ω) * h ω ∂μ‖ := by
            rw [integral_sub hφh hgh, Real.norm_eq_abs]
      _ ≤ ∫ ω, ε * |h ω| ∂μ := by
        apply norm_integral_le_of_norm_le (hh.norm.const_mul ε)
        filter_upwards [] with ω
        rw [← sub_mul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hcoef ω) (abs_nonneg (h ω))
      _ = ε * ∫ ω, |h ω| ∂μ := integral_const_mul _ _
  have hgEq := hsmooth g hgdiffOne hgcomp
  have herrhRev :
      |(∫ ω, g (S ω) * h ω ∂μ) -
          ∫ ω, φ (S ω) * h ω ∂μ| ≤
        ε * ∫ ω, |h ω| ∂μ := by
    simpa only [abs_sub_comm] using herrh
  have hmain : |A| ≤ ε * M := by
    calc
      |A| = |(∫ ω, φ (S ω) * f ω ∂μ) -
          ∫ ω, φ (S ω) * h ω ∂μ| := rfl
      _ ≤ |(∫ ω, φ (S ω) * f ω ∂μ) -
            ∫ ω, g (S ω) * f ω ∂μ| +
          |(∫ ω, g (S ω) * f ω ∂μ) -
            ∫ ω, φ (S ω) * h ω ∂μ| :=
        abs_sub_le _ _ _
      _ = |(∫ ω, φ (S ω) * f ω ∂μ) -
            ∫ ω, g (S ω) * f ω ∂μ| +
          |(∫ ω, g (S ω) * h ω ∂μ) -
            ∫ ω, φ (S ω) * h ω ∂μ| := by rw [hgEq]
      _ ≤ ε * ∫ ω, |f ω| ∂μ +
          ε * ∫ ω, |h ω| ∂μ := add_le_add herrf herrhRev
      _ = ε * M := by simp only [M]; ring
  have hlt : ε * M < |A| := by
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith
  exact (not_lt_of_ge hmain) hlt

/-- The main smooth-test closure theorem: equality for every smooth compactly
supported function of a finite-dimensional measurable coordinate extends to
every bounded measurable function of that coordinate. -/
theorem integral_comp_mul_eq_of_contDiff_compactSupport
    (μ : Measure Ω) (S : Ω → X) (f h : Ω → ℝ)
    (hS : Measurable S) (hfmeas : Measurable f) (hhmeas : Measurable h)
    (hf : Integrable f μ) (hh : Integrable h μ)
    (hsmooth : ∀ (g : X → ℝ), ContDiff ℝ 1 g → HasCompactSupport g →
      ((∫ ω, g (S ω) * f ω ∂μ) =
        (∫ ω, g (S ω) * h ω ∂μ)))
    (u : X → ℝ) (hu : Measurable u)
    (C : ℝ) (huC : ∀ x, |u x| ≤ C) :
    (∫ ω, u (S ω) * f ω ∂μ) =
      ∫ ω, u (S ω) * h ω ∂μ := by
  exact integral_comp_mul_eq_of_compactlySupported
    μ S f h hS hfmeas hhmeas hf hh
    (integral_comp_mul_eq_compactlySupported_of_contDiff
      μ S f h hS hf hh hsmooth)
    u hu C huC

end Wishart

end

end LogdetLean.GramHafnian
