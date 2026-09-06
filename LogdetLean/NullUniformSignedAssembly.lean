import LogdetLean.NullUniformEdgeworthFourier
import LogdetLean.NullSignedEdgeworthAssembly
/-!
# Signed Fejer assembly at the large null Fourier cutoff

This module keeps the signed density certificate abstract.  The
Gaussian--Hermite density module supplies those certificates separately.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

noncomputable section

set_option linter.style.haveILetI false

/-- Large-window signed Esseen assembly with the full model-specific Fourier
bound. -/
theorem cdfComparatorDistance_standardizedNullLaw_signedDensity_le_largeWindow
    {m p : ℕ} (h : Admissible m p)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y))
    (hmass : ∫ y : ℝ, g y = 1)
    (hfourier : signedDensityFourier g =
      nullFirstEdgeworthCharFun m p)
    {lip B : ℝ} (hlip0 : 0 ≤ lip)
    (hlip : HasRealLipschitzBound (signedDensityCDF g) lip)
    (hGint : ∀ x, Integrable
      (fun z ↦ signedDensityCDF g
        (x - z / (nullEdgeworthSmoothingCutoff m p /
          (2 * Real.pi)))) fejerMeasure)
    (hbound : ∀ x,
      |cdf (standardizedNullLaw m p) x - signedDensityCDF g x| ≤ B) :
    cdfComparatorDistance (standardizedNullLaw m p) (signedDensityCDF g) ≤
      (1 / Real.pi) * nullFirstEdgeworthLargeFourierBound m p +
        64 * Real.pi * lip / nullEdgeworthSmoothingCutoff m p := by
  letI : IsProbabilityMeasure (standardizedNullLaw m p) :=
    isProbabilityMeasure_standardizedNullLaw h.2
  have hint : IntegrableOn
      (fourierQuotientError
        (charFun (standardizedNullLaw m p))
        (signedDensityFourier g))
      (Icc (-(nullEdgeworthSmoothingCutoff m p))
        (nullEdgeworthSmoothingCutoff m p)) := by
    rw [hfourier]
    exact integrableOn_fourierQuotientError_null_firstEdgeworth_largeWindow h
  have hsmooth := cdfComparatorDistance_signedDensity_le_fejer_esseen
    (standardizedNullLaw m p)
    (integrable_id_standardizedNullLaw h)
    g hg hyg hmass (nullEdgeworthSmoothingCutoff_pos h)
    hlip0 hlip hGint hbound hint
  calc
    cdfComparatorDistance (standardizedNullLaw m p) (signedDensityCDF g) ≤
        (1 / Real.pi) *
            truncatedFourierDiscrepancy
              (charFun (standardizedNullLaw m p))
              (signedDensityFourier g)
              (nullEdgeworthSmoothingCutoff m p) +
          64 * Real.pi * lip /
            nullEdgeworthSmoothingCutoff m p := hsmooth
    _ ≤ (1 / Real.pi) * nullFirstEdgeworthLargeFourierBound m p +
          64 * Real.pi * lip /
            nullEdgeworthSmoothingCutoff m p := by
      rw [hfourier]
      gcongr
      exact truncatedFourierDiscrepancy_null_firstEdgeworth_largeWindow_le_bound h

/-- Relative form.  The Fourier part is already `lambda` times a vanishing
ratio; only the explicit smoothing term remains. -/
theorem cdfComparatorDistance_standardizedNullLaw_signedDensity_le_largeWindow_relative
    {m p : ℕ} (h : Admissible m p)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y))
    (hmass : ∫ y : ℝ, g y = 1)
    (hfourier : signedDensityFourier g =
      nullFirstEdgeworthCharFun m p)
    {lip B : ℝ} (hlip0 : 0 ≤ lip)
    (hlip : HasRealLipschitzBound (signedDensityCDF g) lip)
    (hGint : ∀ x, Integrable
      (fun z ↦ signedDensityCDF g
        (x - z / (nullEdgeworthSmoothingCutoff m p /
          (2 * Real.pi)))) fejerMeasure)
    (hbound : ∀ x,
      |cdf (standardizedNullLaw m p) x - signedDensityCDF g x| ≤ B) :
    cdfComparatorDistance (standardizedNullLaw m p) (signedDensityCDF g) ≤
      (1 / Real.pi) *
          (nullLambdaSeries m p *
            nullFirstEdgeworthLargeFourierRatio m p) +
        64 * Real.pi * lip / (nullAnalyticScale m p) ^ 4 := by
  have hmain :=
    cdfComparatorDistance_standardizedNullLaw_signedDensity_le_largeWindow
      h g hg hyg hmass hfourier hlip0 hlip hGint hbound
  rw [nullEdgeworthSmoothingCutoff] at hmain
  exact hmain.trans (by
    gcongr
    exact nullFirstEdgeworthLargeFourierBound_le_lambda_mul_ratio h)

/-- The complete relative error after signed Fejer smoothing with Lipschitz
constant `lip`. -/
def nullSignedSmoothingRelativeRatio (m p : ℕ) (lip : ℝ) : ℝ :=
  (1 / Real.pi) * nullFirstEdgeworthLargeFourierRatio m p +
    (512 * Real.pi / 3) * lip / nullAnalyticScale m p

theorem cdfComparatorDistance_standardizedNullLaw_signedDensity_le_lambda_mul_ratio
    {m p : ℕ} (h : Admissible m p)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y))
    (hmass : ∫ y : ℝ, g y = 1)
    (hfourier : signedDensityFourier g =
      nullFirstEdgeworthCharFun m p)
    {lip B : ℝ} (hlip0 : 0 ≤ lip)
    (hlip : HasRealLipschitzBound (signedDensityCDF g) lip)
    (hGint : ∀ x, Integrable
      (fun z ↦ signedDensityCDF g
        (x - z / (nullEdgeworthSmoothingCutoff m p /
          (2 * Real.pi)))) fejerMeasure)
    (hbound : ∀ x,
      |cdf (standardizedNullLaw m p) x - signedDensityCDF g x| ≤ B) :
    cdfComparatorDistance (standardizedNullLaw m p) (signedDensityCDF g) ≤
      nullLambdaSeries m p *
        nullSignedSmoothingRelativeRatio m p lip := by
  have hmain :=
    cdfComparatorDistance_standardizedNullLaw_signedDensity_le_largeWindow_relative
      h g hg hyg hmass hfourier hlip0 hlip hGint hbound
  let D : ℝ := nullAnalyticScale m p
  let lambda : ℝ := nullLambdaSeries m p
  have hD : 0 < D := by dsimp [D]; exact nullAnalyticScale_pos h
  have hlower : (3 / 8 : ℝ) ≤ lambda * D ^ 3 := by
    simpa [D, lambda] using
      three_eighths_le_nullLambdaSeries_mul_analyticScale_cube h
  have hsmooth : 64 * Real.pi * lip / D ^ 4 ≤
      lambda * ((512 * Real.pi / 3) * lip / D) := by
    have hmul := mul_le_mul_of_nonneg_right hlower
      (show 0 ≤ (512 * Real.pi / 3) * lip / D ^ 4 by positivity)
    field_simp [hD.ne'] at hmul ⊢
    nlinarith [hmul]
  dsimp [nullSignedSmoothingRelativeRatio, D, lambda]
  dsimp [D, lambda] at hsmooth
  calc
    cdfComparatorDistance (standardizedNullLaw m p) (signedDensityCDF g) ≤
        (1 / Real.pi) *
            (nullLambdaSeries m p *
              nullFirstEdgeworthLargeFourierRatio m p) +
          64 * Real.pi * lip / nullAnalyticScale m p ^ 4 := hmain
    _ ≤ (1 / Real.pi) *
            (nullLambdaSeries m p *
              nullFirstEdgeworthLargeFourierRatio m p) +
          nullLambdaSeries m p *
            ((512 * Real.pi / 3) * lip /
              nullAnalyticScale m p) := by gcongr
    _ = nullLambdaSeries m p *
        ((1 / Real.pi) * nullFirstEdgeworthLargeFourierRatio m p +
          512 * Real.pi / 3 * lip / nullAnalyticScale m p) := by ring

/-- Any convergent sequence of comparator Lipschitz constants leaves a
vanishing relative smoothing error. -/
theorem tendsto_nullSignedSmoothingRelativeRatio_zero_of_eventually_admissible
    (m : ℕ → ℕ) (lip : ℕ → ℝ) {ell : ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p)
    (hlip : Tendsto lip atTop (nhds ell)) :
    Tendsto
      (fun p ↦ nullSignedSmoothingRelativeRatio (m p) p (lip p))
      atTop (nhds 0) := by
  have hratio :=
    tendsto_nullFirstEdgeworthLargeFourierRatio_zero_of_eventually_admissible
      m hadm
  have hD := tendsto_nullAnalyticScale_atTop_of_eventually_admissible m hadm
  have hinv : Tendsto
      (fun p ↦ 1 / nullAnalyticScale (m p) p) atTop (nhds 0) :=
    hD.const_div_atTop 1
  have hlipInv : Tendsto
      (fun p ↦ lip p / nullAnalyticScale (m p) p) atTop (nhds 0) := by
    have hmul := hlip.mul hinv
    convert hmul using 1 <;> simp [div_eq_mul_inv]
  have hsum := (hratio.const_mul (1 / Real.pi)).add
    (hlipInv.const_mul (512 * Real.pi / 3))
  convert hsum using 1
  · funext p
    simp only [nullSignedSmoothingRelativeRatio]
    ring
  · norm_num

end

end LogdetLean
