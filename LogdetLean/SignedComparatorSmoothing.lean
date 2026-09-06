import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.CDF
import Mathlib.Tactic
import LogdetLean.AbstractSmoothingKernel
import LogdetLean.EdgeworthTransfer
/-!
# Kernel smoothing against a signed CDF comparator

An Edgeworth comparator need not be monotone and need not be the CDF of a
probability measure.  This file therefore proves the distributional half of
the smoothing argument directly for a real function `G`.  The proof uses
monotonicity only for the genuine CDF and uses only a Lipschitz bound for `G`.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set

noncomputable section

def smoothFunction (κ : Measure ℝ) (T : ℝ) (G : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, G (x - z / T) ∂κ

def cdfComparatorDistance (μ : Measure ℝ) (G : ℝ → ℝ) : ℝ :=
  supDistance (cdf μ) G

theorem cdfComparatorDistance_nonneg
    (μ : Measure ℝ) (G : ℝ → ℝ) {B : ℝ}
    (hbound : ∀ x, |cdf μ x - G x| ≤ B) :
    0 ≤ cdfComparatorDistance μ G := by
  exact (abs_nonneg (cdf μ 0 - G 0)).trans
    (point_le_supDistance hbound 0)

/-- Distributional smoothing with an arbitrary, possibly nonmonotone,
signed comparator.  `hbound` is only a finiteness certificate for the
supremum; it does not enter the numerical conclusion. -/
theorem cdfComparatorDistance_le_of_kernel_smoothing
    (κ μ : Measure ℝ) [IsProbabilityMeasure κ]
    (G : ℝ → ℝ) {T a q m δ B : ℝ}
    (hT : 0 < T) (ha : 0 ≤ a) (hq : q < 1 / 2)
    (hm : 0 ≤ m)
    (htail : κ.real (Icc (-a) a)ᶜ ≤ q)
    (hlip : HasRealLipschitzBound G m)
    (hGint : ∀ x, Integrable (fun z ↦ G (x - z / T)) κ)
    (hbound : ∀ x, |cdf μ x - G x| ≤ B)
    (hsmooth : ∀ x,
      |smoothCDF κ T μ x - smoothFunction κ T G x| ≤ δ) :
    cdfComparatorDistance μ G ≤
      (δ + 2 * m * a / T) / (1 - 2 * q) := by
  let D : ℝ := cdfComparatorDistance μ G
  let C : Set ℝ := Icc (-a) a
  have hC : MeasurableSet C := measurableSet_Icc
  have hD0 : 0 ≤ D := cdfComparatorDistance_nonneg μ G hbound
  have hmass : κ.real C + κ.real Cᶜ = 1 := by
    simpa [C] using measureReal_add_measureReal_compl (μ := κ) hC
  have hcentral0 : 0 ≤ κ.real C := measureReal_nonneg
  have htail0 : 0 ≤ κ.real Cᶜ := measureReal_nonneg
  have hcentral1 : κ.real C ≤ 1 := by linarith
  have hden : 0 < 1 - 2 * q := by linarith
  have he0 : 0 ≤ 2 * m * a / T := by positivity
  have hpointD (y : ℝ) : |cdf μ y - G y| ≤ D := by
    exact point_le_supDistance hbound y
  have hpoint : ∀ x,
      |cdf μ x - G x| ≤ δ + 2 * m * a / T + 2 * q * D := by
    intro x
    by_cases hsign : G x ≤ cdf μ x
    · let Delta : ℝ := cdf μ x - G x
      let y : ℝ := x + a / T
      let H : ℝ → ℝ := fun z ↦ cdf μ (y - z / T) - G (y - z / T)
      have hDelta0 : 0 ≤ Delta := sub_nonneg.mpr hsign
      have hDeltaD : Delta ≤ D := by
        have h := hpointD x
        rw [abs_of_nonneg hDelta0] at h
        exact h
      have hH : Integrable H κ := by
        exact (integrable_cdf_shift κ T μ y).sub (hGint y)
      have hcenter_point : ∀ z ∈ C,
          Delta - 2 * m * a / T ≤ H z := by
        intro z hz
        have hzhi : z ≤ a := hz.2
        have harg : x ≤ y - z / T := by
          dsimp [y]
          have := div_le_div_of_nonneg_right hzhi hT.le
          linarith
        have hargdiff0 : 0 ≤ (y - z / T) - x := sub_nonneg.mpr harg
        have hargdiff : |(y - z / T) - x| ≤ 2 * a / T := by
          rw [abs_of_nonneg hargdiff0]
          have := div_le_div_of_nonneg_right
            (by linarith [hz.1] : a - z ≤ 2 * a) hT.le
          calc
            y - z / T - x = (a - z) / T := by dsimp [y]; ring
            _ ≤ 2 * a / T := this
        have hG := hlip (y - z / T) x
        have hGup : G (y - z / T) - G x ≤ 2 * m * a / T := by
          calc
            G (y - z / T) - G x ≤ |G (y - z / T) - G x| := le_abs_self _
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
              ∫ _z in C, (Delta - 2 * m * a / T) ∂κ := by simp
          _ ≤ ∫ z in C, H z ∂κ := by
            apply integral_mono_ae
            · exact integrableOn_const
            · exact hH.mono_measure Measure.restrict_le_self
            · filter_upwards [ae_restrict_mem hC] with z hz
              exact hcenter_point z hz
      have htail_int : κ.real Cᶜ * (-D) ≤ ∫ z in Cᶜ, H z ∂κ := by
        calc
          κ.real Cᶜ * (-D) = ∫ _z in Cᶜ, (-D) ∂κ := by simp
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
        rw [smoothCDF, smoothFunction, ← integral_sub
          (integrable_cdf_shift κ T μ y) (hGint y)] at hs
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
    · have hsign' : cdf μ x < G x := lt_of_not_ge hsign
      let Delta : ℝ := G x - cdf μ x
      let y : ℝ := x - a / T
      let H : ℝ → ℝ := fun z ↦ G (y - z / T) - cdf μ (y - z / T)
      have hDelta0 : 0 ≤ Delta := (sub_pos.mpr hsign').le
      have hDeltaD : Delta ≤ D := by
        have h := hpointD x
        rw [abs_of_neg (sub_neg.mpr hsign')] at h
        simpa [Delta] using h
      have hH : Integrable H κ := (hGint y).sub (integrable_cdf_shift κ T μ y)
      have hcenter_point : ∀ z ∈ C,
          Delta - 2 * m * a / T ≤ H z := by
        intro z hz
        have hzlo : -a ≤ z := hz.1
        have harg : y - z / T ≤ x := by
          dsimp [y]
          have := div_le_div_of_nonneg_right hzlo hT.le
          ring_nf at this ⊢
          linarith
        have hargdiff0 : 0 ≤ x - (y - z / T) := sub_nonneg.mpr harg
        have hargdiff : |x - (y - z / T)| ≤ 2 * a / T := by
          rw [abs_of_nonneg hargdiff0]
          have := div_le_div_of_nonneg_right
            (by linarith [hz.2] : z + a ≤ 2 * a) hT.le
          calc
            x - (y - z / T) = (z + a) / T := by dsimp [y]; ring
            _ ≤ 2 * a / T := this
        have hG := hlip x (y - z / T)
        have hGup : G x - G (y - z / T) ≤ 2 * m * a / T := by
          calc
            G x - G (y - z / T) ≤ |G x - G (y - z / T)| := le_abs_self _
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
              ∫ _z in C, (Delta - 2 * m * a / T) ∂κ := by simp
          _ ≤ ∫ z in C, H z ∂κ := by
            apply integral_mono_ae
            · exact integrableOn_const
            · exact hH.mono_measure Measure.restrict_le_self
            · filter_upwards [ae_restrict_mem hC] with z hz
              exact hcenter_point z hz
      have htail_int : κ.real Cᶜ * (-D) ≤ ∫ z in Cᶜ, H z ∂κ := by
        calc
          κ.real Cᶜ * (-D) = ∫ _z in Cᶜ, (-D) ∂κ := by simp
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
        rw [smoothCDF, smoothFunction, ← integral_sub
          (integrable_cdf_shift κ T μ y) (hGint y)] at hs
        have heq : (∫ z, H z ∂κ) =
            -(∫ z, cdf μ (y - z / T) - G (y - z / T) ∂κ) := by
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
  have hDbound : D ≤ δ + 2 * m * a / T + 2 * q * D :=
    supDistance_le_of_bound hpoint
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Convenient quarter-tail form for a signed comparator. -/
theorem cdfComparatorDistance_le_of_kernel_smoothing_tail_quarter
    (κ μ : Measure ℝ) [IsProbabilityMeasure κ]
    (G : ℝ → ℝ) {T a q m δ B : ℝ}
    (hT : 0 < T) (ha : 0 ≤ a) (hq : q ≤ 1 / 4)
    (hm : 0 ≤ m)
    (htail : κ.real (Icc (-a) a)ᶜ ≤ q)
    (hlip : HasRealLipschitzBound G m)
    (hGint : ∀ x, Integrable (fun z ↦ G (x - z / T)) κ)
    (hbound : ∀ x, |cdf μ x - G x| ≤ B)
    (hsmooth : ∀ x,
      |smoothCDF κ T μ x - smoothFunction κ T G x| ≤ δ) :
    cdfComparatorDistance μ G ≤ 2 * δ + 4 * m * a / T := by
  have hqhalf : q < 1 / 2 := by linarith
  have h := cdfComparatorDistance_le_of_kernel_smoothing κ μ G
    hT ha hqhalf hm htail hlip hGint hbound hsmooth
  have hden : 0 < 1 - 2 * q := by linarith
  apply h.trans
  rw [div_le_iff₀ hden]
  have hδ0 : 0 ≤ δ := by
    exact (abs_nonneg _).trans (hsmooth 0)
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
