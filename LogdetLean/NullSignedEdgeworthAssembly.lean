import LogdetLean.NullEdgeworthGaussianWindow
import LogdetLean.SignedDensityFourierSmoothing
/-!
# Legal signed-density assembly for the null first Edgeworth estimate

The first Edgeworth comparator need not be a probability measure.  This
module therefore applies the signed-density Fejer--Esseen theorem, not the
probability-measure version.  All Gaussian--Hermite density certificates are
kept as explicit hypotheses until their separate algebraic module is proved.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

noncomputable section

set_option linter.style.haveILetI false

/-- The actual standardized null variable has an integrable first moment. -/
theorem integrable_id_standardizedNullLaw
    {m p : ℕ} (h : Admissible m p) :
    Integrable (fun y : ℝ ↦ y) (standardizedNullLaw m p) := by
  change Integrable id (standardizedNullLaw m p)
  apply integrable_of_mem_interior_integrableExpSet
  have hz := re_mem_interior_integrableExpSet_standardizedNullLaw_of_norm_lt h
    (z := (0 : ℂ)) (by
      simpa using nullAnalyticScale_pos h)
  simpa using hz

/-- Complete signed-density Fejer assembly on the quarter analytic window.

The only model-external inputs are the certificates that `g` is an
integrable mass-one signed density with the claimed Fourier transform, a
Lipschitz cumulative function, and the two finiteness hypotheses required by
the signed smoothing theorem. -/
theorem cdfComparatorDistance_standardizedNullLaw_signedDensity_le_of_edgeworthFourier
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
        (x - z / ((nullAnalyticScale m p / 4) /
          (2 * Real.pi)))) fejerMeasure)
    (hbound : ∀ x,
      |cdf (standardizedNullLaw m p) x - signedDensityCDF g x| ≤ B) :
    cdfComparatorDistance (standardizedNullLaw m p) (signedDensityCDF g) ≤
      (1 / Real.pi) *
        (8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
          8 * nullLambdaSeries m p ^ 2 / 3) +
        256 * Real.pi * lip / nullAnalyticScale m p := by
  letI : IsProbabilityMeasure (standardizedNullLaw m p) :=
    isProbabilityMeasure_standardizedNullLaw h.2
  let S : ℝ := nullAnalyticScale m p / 4
  have hS : 0 < S := by
    dsimp only [S]
    exact div_pos (nullAnalyticScale_pos h) (by norm_num)
  have hint : IntegrableOn
      (fourierQuotientError
        (charFun (standardizedNullLaw m p))
        (signedDensityFourier g)) (Icc (-S) S) := by
    rw [hfourier]
    dsimp [S]
    exact integrableOn_fourierQuotientError_null_firstEdgeworth_quarter_scale h
  have hfourierBound :
      truncatedFourierDiscrepancy
          (charFun (standardizedNullLaw m p))
          (signedDensityFourier g) S ≤
        8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
          8 * nullLambdaSeries m p ^ 2 / 3 := by
    rw [hfourier]
    dsimp [S]
    exact truncatedFourierDiscrepancy_null_firstEdgeworth_quarter_scale_le h
  have hsmooth := cdfComparatorDistance_signedDensity_le_fejer_esseen
    (standardizedNullLaw m p)
    (integrable_id_standardizedNullLaw h)
    g hg hyg hmass hS hlip0 hlip (by simpa [S] using hGint) hbound hint
  calc
    cdfComparatorDistance (standardizedNullLaw m p) (signedDensityCDF g) ≤
        (1 / Real.pi) *
            truncatedFourierDiscrepancy
              (charFun (standardizedNullLaw m p))
              (signedDensityFourier g) S +
          64 * Real.pi * lip / S := hsmooth
    _ ≤ (1 / Real.pi) *
          (8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
            8 * nullLambdaSeries m p ^ 2 / 3) +
        64 * Real.pi * lip / S := by
      gcongr
    _ = (1 / Real.pi) *
          (8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
            8 * nullLambdaSeries m p ^ 2 / 3) +
        256 * Real.pi * lip / nullAnalyticScale m p := by
      dsimp [S]
      field_simp [ne_of_gt (nullAnalyticScale_pos h)]
      ring

/-- The same assembly with an explicit identification of the cumulative
signed density as the usual first Edgeworth CDF. -/
theorem supDistance_standardizedNullLaw_signedFirstEdgeworth_le_of_densityCertificate
    {m p : ℕ} (h : Admissible m p)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hyg : Integrable (fun y : ℝ ↦ y * g y))
    (hmass : ∫ y : ℝ, g y = 1)
    (hfourier : signedDensityFourier g =
      nullFirstEdgeworthCharFun m p)
    (hcdf : signedDensityCDF g =
      signedFirstEdgeworthCDF (nullLambdaSeries m p / 6))
    {lip B : ℝ} (hlip0 : 0 ≤ lip)
    (hlip : HasRealLipschitzBound (signedDensityCDF g) lip)
    (hGint : ∀ x, Integrable
      (fun z ↦ signedDensityCDF g
        (x - z / ((nullAnalyticScale m p / 4) /
          (2 * Real.pi)))) fejerMeasure)
    (hbound : ∀ x,
      |cdf (standardizedNullLaw m p) x - signedDensityCDF g x| ≤ B) :
    supDistance (cdf (standardizedNullLaw m p))
        (signedFirstEdgeworthCDF (nullLambdaSeries m p / 6)) ≤
      (1 / Real.pi) *
        (8 * nullLambdaSeries m p / (9 * nullAnalyticScale m p) +
          8 * nullLambdaSeries m p ^ 2 / 3) +
        256 * Real.pi * lip / nullAnalyticScale m p := by
  have hmain :=
    cdfComparatorDistance_standardizedNullLaw_signedDensity_le_of_edgeworthFourier
      h g hg hyg hmass hfourier hlip0 hlip hGint hbound
  simpa [cdfComparatorDistance, hcdf] using hmain

end

end LogdetLean
