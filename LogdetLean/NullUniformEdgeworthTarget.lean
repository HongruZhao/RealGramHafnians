import LogdetLean.NullUniformSignedAssembly
import LogdetLean.SignedEdgeworthDensity
import LogdetLean.NullWeakCLT
/-!
# Uniform null Edgeworth and sharp Kolmogorov targets

This is the final null analytic assembly.  The cutoff is `Delta^4`; the
relative remainder tends to zero along every eventually admissible sequence,
with no exclusion of the square case `m=p`.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

noncomputable section

set_option linter.style.haveILetI false

/-- The closed Gaussian--Hermite Fourier transform agrees exactly with the
model-specific cubic comparator. -/
theorem signedFirstEdgeworthFourier_null_eq
    {m p : ℕ} :
    signedFirstEdgeworthFourier (nullLambdaSeries m p / 6) =
      nullFirstEdgeworthCharFun m p := by
  funext t
  unfold signedFirstEdgeworthFourier nullFirstEdgeworthCharFun
  congr 1
  unfold nullCubicCharacteristicTerm
  push_cast
  ring

/-- Explicit dimensionless remainder in the uniform first Edgeworth
expansion. -/
def nullUniformEdgeworthRelativeRemainder (m p : ℕ) : ℝ :=
  nullSignedSmoothingRelativeRatio m p
    (signedFirstEdgeworthLipschitzConstant
      (nullLambdaSeries m p / 6))

/-- Finite uniform first-order Edgeworth estimate for the exact standardized
null law. -/
theorem uniformNullEdgeworth_finite
    {m p : ℕ} (h : Admissible m p) :
    cdfComparatorDistance (standardizedNullLaw m p)
        (signedFirstEdgeworthCDF (nullLambdaSeries m p / 6)) ≤
      nullLambdaSeries m p *
        nullUniformEdgeworthRelativeRemainder m p := by
  let a : ℝ := nullLambdaSeries m p / 6
  let g : ℝ → ℝ := signedFirstEdgeworthDensity a
  have hfourier : signedDensityFourier g =
      nullFirstEdgeworthCharFun m p := by
    dsimp [g]
    rw [signedDensityFourier_signedFirstEdgeworthDensity_eq]
    simpa [a] using (signedFirstEdgeworthFourier_null_eq (m := m) (p := p))
  have hmain :=
    cdfComparatorDistance_standardizedNullLaw_signedDensity_le_lambda_mul_ratio
      h g
      (by dsimp [g]; exact integrable_signedFirstEdgeworthDensity a)
      (by dsimp [g]; exact integrable_id_mul_signedFirstEdgeworthDensity a)
      (by dsimp [g]; exact integral_signedFirstEdgeworthDensity a)
      hfourier
      (signedFirstEdgeworthLipschitzConstant_nonneg a)
      (by
        dsimp [g]
        exact signedDensityCDF_signedFirstEdgeworthDensity_lipschitz a)
      (fun x ↦ by
        dsimp [g]
        exact integrable_fejer_signedDensityCDF_shift a x
          (nullEdgeworthSmoothingCutoff m p / (2 * Real.pi)))
      (fun x ↦ by
        dsimp [g]
        exact cdf_sub_signedFirstEdgeworthDensityCDF_le
          (standardizedNullLaw m p) a x)
  have hG : signedDensityCDF g = signedFirstEdgeworthCDF a := by
    funext x
    dsimp [g]
    exact signedDensityCDF_signedFirstEdgeworthDensity a x
  rw [hG] at hmain
  simpa [a, nullUniformEdgeworthRelativeRemainder] using hmain

/-- The relative Edgeworth remainder tends to zero uniformly in the
sequential sense `2 <= p <= m(p)` eventually. -/
theorem tendsto_nullUniformEdgeworthRelativeRemainder_zero
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ nullUniformEdgeworthRelativeRemainder (m p) p)
      atTop (nhds 0) := by
  let lambda : ℕ → ℝ := fun p ↦ nullLambdaSeries (m p) p
  have hlambda : Tendsto lambda atTop (nhds 0) := by
    dsimp [lambda]
    exact tendsto_nullLambdaSeries_zero_of_eventually_admissible m hadm
  have ha : Tendsto (fun p ↦ lambda p / 6) atTop (nhds 0) := by
    simpa using hlambda.div_const 6
  have habs : Tendsto (fun p ↦ |lambda p / 6|) atTop (nhds 0) := by
    simpa using ha.abs
  have hlip : Tendsto
      (fun p ↦ signedFirstEdgeworthLipschitzConstant (lambda p / 6))
      atTop (nhds (1 / Real.sqrt (2 * Real.pi))) := by
    unfold signedFirstEdgeworthLipschitzConstant
    have hnum : Tendsto (fun p ↦ 1 + 11 * |lambda p / 6|)
        atTop (nhds 1) := by
      have hmul : Tendsto (fun p ↦ 11 * |lambda p / 6|)
          atTop (nhds 0) := by
        simpa using habs.const_mul 11
      simpa using tendsto_const_nhds.add hmul
    simpa using hnum.div_const (Real.sqrt (2 * Real.pi))
  dsimp [nullUniformEdgeworthRelativeRemainder]
  exact tendsto_nullSignedSmoothingRelativeRatio_zero_of_eventually_admissible
    m (fun p ↦ signedFirstEdgeworthLipschitzConstant (lambda p / 6))
      hadm hlip

/-- Finite sharp Kolmogorov estimate.  The exact leading coefficient is
`lambda /(6 sqrt(2 pi))`; the error is bounded by the uniform relative
remainder above. -/
theorem uniformNullSharpKolmogorov_finite
    {m p : ℕ} (h : Admissible m p) :
    |kolmogorovDistance (standardizedNullLaw m p) (gaussianReal 0 1) -
        nullLambdaSeries m p / (6 * Real.sqrt (2 * Real.pi))| ≤
      nullLambdaSeries m p *
        nullUniformEdgeworthRelativeRemainder m p := by
  let a : ℝ := nullLambdaSeries m p / 6
  let R : ℝ := nullLambdaSeries m p *
    nullUniformEdgeworthRelativeRemainder m p
  have hedge := uniformNullEdgeworth_finite h
  have hfinite : ∀ x,
      |cdf (standardizedNullLaw m p) x - signedFirstEdgeworthCDF a x| ≤
        2 + |a| / Real.sqrt (2 * Real.pi) := by
    intro x
    rw [← signedDensityCDF_signedFirstEdgeworthDensity a x]
    exact cdf_sub_signedFirstEdgeworthDensityCDF_le
      (standardizedNullLaw m p) a x
  have hexpansion : ∀ x,
      |(cdf (standardizedNullLaw m p) x - cdf (gaussianReal 0 1) x) +
          a * normalEdgeworthShape x| ≤ R := by
    intro x
    have hpoint := point_le_supDistance hfinite x
    have hpointR :
        |cdf (standardizedNullLaw m p) x - signedFirstEdgeworthCDF a x| ≤
          R := hpoint.trans (by
            simpa [cdfComparatorDistance, a, R] using hedge)
    rw [show
      (cdf (standardizedNullLaw m p) x - cdf (gaussianReal 0 1) x) +
          a * normalEdgeworthShape x =
        cdf (standardizedNullLaw m p) x - signedFirstEdgeworthCDF a x by
      unfold signedFirstEdgeworthCDF
      ring]
    exact hpointR
  have hsharp := normal_edgeworth_transfer
    (lambda := a) (remainder := R)
    (by
      dsimp [a]
      exact div_nonneg (nullLambdaSeries_pos h).le (by norm_num)) hexpansion
  have hlead : a / Real.sqrt (2 * Real.pi) =
      nullLambdaSeries m p / (6 * Real.sqrt (2 * Real.pi)) := by
    dsimp [a]
    ring
  rw [hlead] at hsharp
  simpa [kolmogorovDistance, R] using hsharp

/-- The sharp relative Kolmogorov error tends to zero along every eventually
admissible sequence. -/
theorem tendsto_uniformNullSharpKolmogorov_relative_error_zero
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto
      (fun p ↦
        |kolmogorovDistance (standardizedNullLaw (m p) p)
              (gaussianReal 0 1) -
            nullLambdaSeries (m p) p /
              (6 * Real.sqrt (2 * Real.pi))| /
          nullLambdaSeries (m p) p)
      atTop (nhds 0) := by
  have hrem := tendsto_nullUniformEdgeworthRelativeRemainder_zero m hadm
  apply squeeze_zero'
  · exact hadm.mono fun p hp ↦
      div_nonneg (abs_nonneg _) (nullLambdaSeries_pos hp).le
  · filter_upwards [hadm] with p hp
    have hsharp := uniformNullSharpKolmogorov_finite hp
    have hlambda : 0 < nullLambdaSeries (m p) p := nullLambdaSeries_pos hp
    calc
      |kolmogorovDistance (standardizedNullLaw (m p) p)
              (gaussianReal 0 1) -
            nullLambdaSeries (m p) p /
              (6 * Real.sqrt (2 * Real.pi))| /
          nullLambdaSeries (m p) p ≤
        (nullLambdaSeries (m p) p *
            nullUniformEdgeworthRelativeRemainder (m p) p) /
          nullLambdaSeries (m p) p :=
        div_le_div_of_nonneg_right hsharp hlambda.le
      _ = nullUniformEdgeworthRelativeRemainder (m p) p := by
        field_simp [hlambda.ne']
  · exact hrem

/-! ## Discharging the original proposition-valued targets -/

/-- Identification of the original target's correction function with the
signed Gaussian--Hermite comparator used above. -/
theorem nullEdgeworthError_eq_signedComparatorDistance
    {m p : ℕ} (hpm : p ≤ m) :
    nullEdgeworthError m p =
      cdfComparatorDistance (standardizedNullLaw m p)
        (signedFirstEdgeworthCDF (nullLambdaSeries m p / 6)) := by
  unfold nullEdgeworthError cdfComparatorDistance
  congr 1
  funext x
  unfold standardNormalCDF nullEdgeworthCorrection signedFirstEdgeworthCDF
  rw [← standardNormalDensity_eq_gaussianPDFReal]
  unfold normalEdgeworthShape
  rw [← nullSkewScale_eq_nullLambdaSeries hpm]
  unfold nullSkewScale
  ring

/-- Identification of the normalization in the original sharp target. -/
theorem nullSharpScale_eq_lambda
    {m p : ℕ} (hpm : p ≤ m) :
    nullThirdMagnitude m p /
        (6 * Real.sqrt (2 * Real.pi) *
          nullVariance m p ^ (3 / 2 : ℝ)) =
      nullLambdaSeries m p / (6 * Real.sqrt (2 * Real.pi)) := by
  rw [← nullSkewScale_eq_nullLambdaSeries hpm]
  unfold nullSkewScale
  ring

/-- The proposition `UniformNullEdgeworthTarget` declared in `FullTarget` is
now a theorem. -/
theorem uniformNullEdgeworthTarget_proved : UniformNullEdgeworthTarget := by
  intro m hadm
  have hrem := tendsto_nullUniformEdgeworthRelativeRemainder_zero m hadm
  apply squeeze_zero'
    (g := fun p ↦ nullUniformEdgeworthRelativeRemainder (m p) p)
  · filter_upwards [hadm] with p hp
    rw [nullEdgeworthError_eq_signedComparatorDistance hp.2,
      nullSkewScale_eq_nullLambdaSeries hp.2]
    apply div_nonneg
    · apply cdfComparatorDistance_nonneg
      intro x
      rw [← signedDensityCDF_signedFirstEdgeworthDensity
        (nullLambdaSeries (m p) p / 6) x]
      exact cdf_sub_signedFirstEdgeworthDensityCDF_le
        (standardizedNullLaw (m p) p)
          (nullLambdaSeries (m p) p / 6) x
    · exact (nullLambdaSeries_pos hp).le
  · filter_upwards [hadm] with p hp
    rw [nullEdgeworthError_eq_signedComparatorDistance hp.2,
      nullSkewScale_eq_nullLambdaSeries hp.2]
    have hfinite := uniformNullEdgeworth_finite hp
    have hlambda : 0 < nullLambdaSeries (m p) p := nullLambdaSeries_pos hp
    calc
      cdfComparatorDistance (standardizedNullLaw (m p) p)
            (signedFirstEdgeworthCDF
              (nullLambdaSeries (m p) p / 6)) /
          nullLambdaSeries (m p) p ≤
        (nullLambdaSeries (m p) p *
            nullUniformEdgeworthRelativeRemainder (m p) p) /
          nullLambdaSeries (m p) p :=
        div_le_div_of_nonneg_right hfinite hlambda.le
      _ = nullUniformEdgeworthRelativeRemainder (m p) p := by
        field_simp [hlambda.ne']
  · exact hrem

/-- The proposition `UniformNullSharpKolmogorovTarget` declared in
`FullTarget` is now a theorem. -/
theorem uniformNullSharpKolmogorovTarget_proved :
    UniformNullSharpKolmogorovTarget := by
  intro m hadm
  have hrem := tendsto_nullUniformEdgeworthRelativeRemainder_zero m hadm
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hupper : Tendsto
      (fun p ↦ 6 * Real.sqrt (2 * Real.pi) *
        nullUniformEdgeworthRelativeRemainder (m p) p)
      atTop (nhds 0) := by
    simpa using hrem.const_mul (6 * Real.sqrt (2 * Real.pi))
  apply squeeze_zero'
    (g := fun p ↦ 6 * Real.sqrt (2 * Real.pi) *
      nullUniformEdgeworthRelativeRemainder (m p) p)
  · exact Filter.Eventually.of_forall fun p ↦ norm_nonneg _
  · filter_upwards [hadm] with p hp
    rw [nullSharpScale_eq_lambda hp.2]
    let lambda : ℝ := nullLambdaSeries (m p) p
    let s : ℝ := Real.sqrt (2 * Real.pi)
    let d : ℝ := kolmogorovDistance
      (standardizedNullLaw (m p) p) (gaussianReal 0 1)
    have hlambda : 0 < lambda := by
      dsimp [lambda]
      exact nullLambdaSeries_pos hp
    have hs : 0 < s := by dsimp [s]; positivity
    have hlead : 0 < lambda / (6 * s) := by positivity
    have hfinite := uniformNullSharpKolmogorov_finite hp
    have hfinite' : |d - lambda / (6 * s)| ≤
        lambda * nullUniformEdgeworthRelativeRemainder (m p) p := by
      simpa [d, lambda, s] using hfinite
    change ‖d / (lambda / (6 * s)) - 1‖ ≤
      6 * s * nullUniformEdgeworthRelativeRemainder (m p) p
    rw [Real.norm_eq_abs]
    have heq : |d / (lambda / (6 * s)) - 1| =
        |d - lambda / (6 * s)| / (lambda / (6 * s)) := by
      rw [show d / (lambda / (6 * s)) - 1 =
          (d - lambda / (6 * s)) / (lambda / (6 * s)) by
        field_simp [hlead.ne']]
      rw [abs_div, abs_of_pos hlead]
    rw [heq]
    calc
      |d - lambda / (6 * s)| / (lambda / (6 * s)) ≤
          (lambda * nullUniformEdgeworthRelativeRemainder (m p) p) /
            (lambda / (6 * s)) :=
        div_le_div_of_nonneg_right hfinite' hlead.le
      _ = 6 * s * nullUniformEdgeworthRelativeRemainder (m p) p := by
        field_simp [hlambda.ne', hs.ne']
  · exact hupper

/-- The same finite theorem for the actual Gaussian sample statistic. -/
theorem UniformActualNullSharpKolmogorovTarget
    {m p : ℕ} (h : Admissible m p) :
    |kolmogorovDistance
          (Measure.map (Z0mpStatistic m p)
            (nestedProductMeasure
              (stdGaussian (ObservationSpace (m + 1))) p))
          (gaussianReal 0 1) -
        nullLambdaSeries m p / (6 * Real.sqrt (2 * Real.pi))| ≤
      nullLambdaSeries m p *
        nullUniformEdgeworthRelativeRemainder m p := by
  rw [map_Z0mpStatistic_eq_standardizedNullLaw m p h.2]
  exact uniformNullSharpKolmogorov_finite h

/-- Totalized actual-statistic formulation; the Gaussian fallback affects
only finitely many inadmissible initial indices. -/
theorem tendsto_uniformActualNullSharpKolmogorov_relative_error_zero
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto
      (fun p ↦
        |kolmogorovDistance (actualZ0mpMeasureOrGaussian (m p) p)
              (gaussianReal 0 1) -
            nullLambdaSeries (m p) p /
              (6 * Real.sqrt (2 * Real.pi))| /
          nullLambdaSeries (m p) p)
      atTop (nhds 0) := by
  have hstd := tendsto_uniformNullSharpKolmogorov_relative_error_zero m hadm
  apply hstd.congr'
  filter_upwards [hadm] with p hp
  unfold actualZ0mpMeasureOrGaussian
  rw [if_pos hp, map_Z0mpStatistic_eq_standardizedNullLaw (m p) p hp.2]

end

end LogdetLean
