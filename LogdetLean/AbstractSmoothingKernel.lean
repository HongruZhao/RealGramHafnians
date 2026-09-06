import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.CDF
import Mathlib.Tactic
import LogdetLean.KolmogorovDistance
/-!
# The distributional half of Esseen smoothing

This file proves the monotonicity/anti-concentration part of the smoothing
argument for an arbitrary probability kernel.  It is independent of the
Fourier realization of that kernel.  The proof follows the mechanism in
Feller, Volume II, Lemma XVI.3.1: central kernel mass transports a nearly
maximal CDF discrepancy, while the two tails cost at most twice their mass
times the original Kolmogorov distance and can therefore be absorbed.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- A real function is globally Lipschitz with the displayed real constant.
This unbundled form is convenient when the constant is a paper parameter. -/
def HasRealLipschitzBound (f : ℝ → ℝ) (m : ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ m * |x - y|

/-- Smoothing a CDF by adding kernel noise of size `1/T`. -/
def smoothCDF (κ : Measure ℝ) (T : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ z, cdf μ (x - z / T) ∂κ

theorem integrable_cdf_shift (κ : Measure ℝ) [IsFiniteMeasure κ]
    (T : ℝ) (μ : Measure ℝ) (x : ℝ) :
    Integrable (fun z ↦ cdf μ (x - z / T)) κ := by
  apply (integrable_const (1 : ℝ)).mono
  · exact ((monotone_cdf μ).measurable.comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg μ _), norm_one]
      exact cdf_le_one μ _

theorem integrable_cdf_shift_sub (κ : Measure ℝ) [IsFiniteMeasure κ]
    (T : ℝ) (μ ν : Measure ℝ) (x : ℝ) :
    Integrable (fun z ↦ cdf μ (x - z / T) - cdf ν (x - z / T)) κ :=
  (integrable_cdf_shift κ T μ x).sub (integrable_cdf_shift κ T ν x)

/-- Abstract kernel smoothing lemma.  The Fourier half of the argument only
needs to provide `hsmooth`; everything else is distributional. -/
theorem kolmogorovDistance_le_of_kernel_smoothing
    (κ μ ν : Measure ℝ) [IsProbabilityMeasure κ]
    {T a q m δ : ℝ}
    (hT : 0 < T) (ha : 0 ≤ a) (hq : q < 1 / 2)
    (hm : 0 ≤ m)
    (htail : κ.real (Icc (-a) a)ᶜ ≤ q)
    (hlip : HasRealLipschitzBound (cdf ν) m)
    (hsmooth : ∀ x, |smoothCDF κ T μ x - smoothCDF κ T ν x| ≤ δ) :
    kolmogorovDistance μ ν ≤
      (δ + 2 * m * a / T) / (1 - 2 * q) := by
  let D : ℝ := kolmogorovDistance μ ν
  let C : Set ℝ := Icc (-a) a
  have hC : MeasurableSet C := measurableSet_Icc
  have hD0 : 0 ≤ D := kolmogorovDistance_nonneg μ ν
  have hmass : κ.real C + κ.real Cᶜ = 1 := by
    simpa [C] using measureReal_add_measureReal_compl (μ := κ) hC
  have hcentral0 : 0 ≤ κ.real C := measureReal_nonneg
  have htail0 : 0 ≤ κ.real Cᶜ := measureReal_nonneg
  have hcentral1 : κ.real C ≤ 1 := by linarith
  have hden : 0 < 1 - 2 * q := by linarith
  have he0 : 0 ≤ 2 * m * a / T := by positivity
  have hpointD (y : ℝ) : |cdf μ y - cdf ν y| ≤ D := by
    exact point_le_supDistance (fun z ↦ abs_cdf_sub_cdf_le_one μ ν z) y
  have hpoint : ∀ x,
      |cdf μ x - cdf ν x| ≤ δ + 2 * m * a / T + 2 * q * D := by
    intro x
    by_cases hsign : cdf ν x ≤ cdf μ x
    · let Delta : ℝ := cdf μ x - cdf ν x
      let y : ℝ := x + a / T
      let H : ℝ → ℝ := fun z ↦ cdf μ (y - z / T) - cdf ν (y - z / T)
      have hDelta0 : 0 ≤ Delta := sub_nonneg.mpr hsign
      have hDeltaD : Delta ≤ D := by
        have := hpointD x
        rw [abs_of_nonneg hDelta0] at this
        exact this
      have hH : Integrable H κ := by
        simpa [H] using integrable_cdf_shift_sub κ T μ ν y
      have hcenter_point : ∀ z ∈ C,
          Delta - 2 * m * a / T ≤ H z := by
        intro z hz
        have hzlo : -a ≤ z := hz.1
        have hzhi : z ≤ a := hz.2
        have harg : x ≤ y - z / T := by
          dsimp [y]
          have := div_le_div_of_nonneg_right hzhi hT.le
          linarith
        have hargdiff0 : 0 ≤ (y - z / T) - x := sub_nonneg.mpr harg
        have hargdiff : |(y - z / T) - x| ≤ 2 * a / T := by
          rw [abs_of_nonneg hargdiff0]
          have := div_le_div_of_nonneg_right (by linarith : a - z ≤ 2 * a) hT.le
          calc
            y - z / T - x = (a - z) / T := by dsimp [y]; ring
            _ ≤ 2 * a / T := this
        have hG := hlip (y - z / T) x
        have hGup : cdf ν (y - z / T) - cdf ν x ≤ 2 * m * a / T := by
          calc
            cdf ν (y - z / T) - cdf ν x ≤
                |cdf ν (y - z / T) - cdf ν x| := le_abs_self _
            _ ≤ m * |(y - z / T) - x| := hG
            _ ≤ m * (2 * a / T) := mul_le_mul_of_nonneg_left hargdiff hm
            _ = 2 * m * a / T := by ring
        have hF := monotone_cdf μ harg
        dsimp [H, Delta]
        linarith
      have htail_point : ∀ z ∈ Cᶜ, -D ≤ H z := by
        intro z _hz
        have h := hpointD (y - z / T)
        rw [abs_le] at h
        exact h.1
      have hcenter_int : κ.real C * (Delta - 2 * m * a / T) ≤
          ∫ z in C, H z ∂κ := by
        calc
          κ.real C * (Delta - 2 * m * a / T) =
              ∫ _z in C, (Delta - 2 * m * a / T) ∂κ := by
                simp
          _ ≤ ∫ z in C, H z ∂κ := by
            apply integral_mono_ae
            · exact integrableOn_const
            · exact hH.mono_measure Measure.restrict_le_self
            · filter_upwards [ae_restrict_mem hC] with z hz
              exact hcenter_point z hz
      have htail_int : κ.real Cᶜ * (-D) ≤ ∫ z in Cᶜ, H z ∂κ := by
        calc
          κ.real Cᶜ * (-D) = ∫ _z in Cᶜ, (-D) ∂κ := by
            simp
          _ ≤ ∫ z in Cᶜ, H z ∂κ := by
            apply integral_mono_ae
            · exact integrableOn_const
            · exact hH.mono_measure Measure.restrict_le_self
            · filter_upwards [ae_restrict_mem hC.compl] with z hz
              exact htail_point z hz
      have hint_lower :
          κ.real C * (Delta - 2 * m * a / T) + κ.real Cᶜ * (-D) ≤
            ∫ z, H z ∂κ := by
        rw [← integral_add_compl hC hH]
        exact add_le_add hcenter_int htail_int
      have hsm : |∫ z, H z ∂κ| ≤ δ := by
        have hs := hsmooth y
        rw [smoothCDF, smoothCDF, ← integral_sub
          (integrable_cdf_shift κ T μ y) (integrable_cdf_shift κ T ν y)] at hs
        exact hs
      have hkernel_lower :
          Delta - 2 * m * a / T - 2 * q * D ≤
            κ.real C * (Delta - 2 * m * a / T) + κ.real Cᶜ * (-D) := by
        have htailDelta : κ.real Cᶜ * Delta ≤ κ.real Cᶜ * D :=
          mul_le_mul_of_nonneg_left hDeltaD htail0
        have hcentere : κ.real C * (2 * m * a / T) ≤ 2 * m * a / T :=
          by simpa [mul_comm] using mul_le_mul_of_nonneg_right hcentral1 he0
        have htailD : κ.real Cᶜ * D ≤ q * D :=
          mul_le_mul_of_nonneg_right htail hD0
        nlinarith
      have hDelta : Delta ≤ δ + 2 * m * a / T + 2 * q * D := by
        have hi : ∫ z, H z ∂κ ≤ δ := (le_abs_self _).trans hsm
        linarith
      rw [abs_of_nonneg hDelta0]
      exact hDelta
    · have hsign' : cdf μ x < cdf ν x := lt_of_not_ge hsign
      let Delta : ℝ := cdf ν x - cdf μ x
      let y : ℝ := x - a / T
      let H : ℝ → ℝ := fun z ↦ cdf ν (y - z / T) - cdf μ (y - z / T)
      have hDelta0 : 0 ≤ Delta := (sub_pos.mpr hsign').le
      have hDeltaD : Delta ≤ D := by
        have h := hpointD x
        rw [abs_of_neg (sub_neg.mpr hsign')] at h
        simpa [Delta] using h
      have hH : Integrable H κ := by
        exact (integrable_cdf_shift κ T ν y).sub (integrable_cdf_shift κ T μ y)
      have hcenter_point : ∀ z ∈ C,
          Delta - 2 * m * a / T ≤ H z := by
        intro z hz
        have hzlo : -a ≤ z := hz.1
        have hzhi : z ≤ a := hz.2
        have harg : y - z / T ≤ x := by
          dsimp [y]
          have := div_le_div_of_nonneg_right hzlo hT.le
          ring_nf at this ⊢
          linarith
        have hargdiff0 : 0 ≤ x - (y - z / T) := sub_nonneg.mpr harg
        have hargdiff : |x - (y - z / T)| ≤ 2 * a / T := by
          rw [abs_of_nonneg hargdiff0]
          have := div_le_div_of_nonneg_right (by linarith : z + a ≤ 2 * a) hT.le
          calc
            x - (y - z / T) = (z + a) / T := by dsimp [y]; ring
            _ ≤ 2 * a / T := this
        have hG := hlip x (y - z / T)
        have hGup : cdf ν x - cdf ν (y - z / T) ≤ 2 * m * a / T := by
          calc
            cdf ν x - cdf ν (y - z / T) ≤
                |cdf ν x - cdf ν (y - z / T)| := le_abs_self _
            _ ≤ m * |x - (y - z / T)| := hG
            _ ≤ m * (2 * a / T) := mul_le_mul_of_nonneg_left hargdiff hm
            _ = 2 * m * a / T := by ring
        have hF := monotone_cdf μ harg
        dsimp [H, Delta]
        linarith
      have htail_point : ∀ z ∈ Cᶜ, -D ≤ H z := by
        intro z _hz
        have h := hpointD (y - z / T)
        rw [abs_le] at h
        linarith
      have hcenter_int : κ.real C * (Delta - 2 * m * a / T) ≤
          ∫ z in C, H z ∂κ := by
        calc
          κ.real C * (Delta - 2 * m * a / T) =
              ∫ _z in C, (Delta - 2 * m * a / T) ∂κ := by
                simp
          _ ≤ ∫ z in C, H z ∂κ := by
            apply integral_mono_ae
            · exact integrableOn_const
            · exact hH.mono_measure Measure.restrict_le_self
            · filter_upwards [ae_restrict_mem hC] with z hz
              exact hcenter_point z hz
      have htail_int : κ.real Cᶜ * (-D) ≤ ∫ z in Cᶜ, H z ∂κ := by
        calc
          κ.real Cᶜ * (-D) = ∫ _z in Cᶜ, (-D) ∂κ := by
            simp
          _ ≤ ∫ z in Cᶜ, H z ∂κ := by
            apply integral_mono_ae
            · exact integrableOn_const
            · exact hH.mono_measure Measure.restrict_le_self
            · filter_upwards [ae_restrict_mem hC.compl] with z hz
              exact htail_point z hz
      have hint_lower :
          κ.real C * (Delta - 2 * m * a / T) + κ.real Cᶜ * (-D) ≤
            ∫ z, H z ∂κ := by
        rw [← integral_add_compl hC hH]
        exact add_le_add hcenter_int htail_int
      have hsm : |∫ z, H z ∂κ| ≤ δ := by
        have hs := hsmooth y
        rw [smoothCDF, smoothCDF, ← integral_sub
          (integrable_cdf_shift κ T μ y) (integrable_cdf_shift κ T ν y)] at hs
        have heq : (∫ z, H z ∂κ) =
            -(∫ z, cdf μ (y - z / T) - cdf ν (y - z / T) ∂κ) := by
          rw [← integral_neg]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z ↦ by dsimp [H]; ring
        rw [heq, abs_neg]
        exact hs
      have hkernel_lower :
          Delta - 2 * m * a / T - 2 * q * D ≤
            κ.real C * (Delta - 2 * m * a / T) + κ.real Cᶜ * (-D) := by
        have htailDelta : κ.real Cᶜ * Delta ≤ κ.real Cᶜ * D :=
          mul_le_mul_of_nonneg_left hDeltaD htail0
        have hcentere : κ.real C * (2 * m * a / T) ≤ 2 * m * a / T :=
          by simpa [mul_comm] using mul_le_mul_of_nonneg_right hcentral1 he0
        have htailD : κ.real Cᶜ * D ≤ q * D :=
          mul_le_mul_of_nonneg_right htail hD0
        nlinarith
      have hDelta : Delta ≤ δ + 2 * m * a / T + 2 * q * D := by
        have hi : ∫ z, H z ∂κ ≤ δ := (le_abs_self _).trans hsm
        linarith
      rw [abs_of_neg (sub_neg.mpr hsign')]
      simpa [Delta] using hDelta
  have hDbound : D ≤ δ + 2 * m * a / T + 2 * q * D := by
    exact supDistance_le_of_bound hpoint
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Convenient absorbed-tail specialization. -/
theorem kolmogorovDistance_le_of_kernel_smoothing_tail_quarter
    (κ μ ν : Measure ℝ) [IsProbabilityMeasure κ]
    {T a q m δ : ℝ}
    (hT : 0 < T) (ha : 0 ≤ a) (hq : q ≤ 1 / 4)
    (hm : 0 ≤ m)
    (htail : κ.real (Icc (-a) a)ᶜ ≤ q)
    (hlip : HasRealLipschitzBound (cdf ν) m)
    (hsmooth : ∀ x, |smoothCDF κ T μ x - smoothCDF κ T ν x| ≤ δ) :
    kolmogorovDistance μ ν ≤ 2 * δ + 4 * m * a / T := by
  have hqhalf : q < 1 / 2 := by linarith
  have h := kolmogorovDistance_le_of_kernel_smoothing κ μ ν
    hT ha hqhalf hm htail hlip hsmooth
  have hden : 0 < 1 - 2 * q := by linarith
  apply h.trans
  rw [div_le_iff₀ hden]
  have hδ0 : 0 ≤ δ := by
    have hs := hsmooth 0
    exact (abs_nonneg _).trans hs
  have he0 : 0 ≤ 2 * m * a / T := by positivity
  have hsum0 : 0 ≤ δ + 2 * m * a / T := add_nonneg hδ0 he0
  have hfactor : 1 / 2 ≤ 1 - 2 * q := by linarith
  have hprod := mul_le_mul_of_nonneg_left hfactor hsum0
  calc
    δ + 2 * m * a / T ≤
        2 * (δ + 2 * m * a / T) * (1 - 2 * q) := by nlinarith
    _ = (2 * δ + 4 * m * a / T) * (1 - 2 * q) := by ring

end

end LogdetLean
