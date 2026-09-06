import LogdetLean.BetaMellin
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
/-!
# The first moment and a Markov bound for the coherence beta law

The Mellin identity proved in `LogdetLean.BetaMellin` immediately gives the
mean of a beta distribution.  We make that consequence explicit here and
specialize it to the squared-correlation law

`Beta(1/2, (m-1)/2)`.

The final theorem applies mathlib's measure-theoretic Markov inequality.  It
is deliberately stated with `Measure.real`, matching the real-valued tail
probabilities used by the coherence development.
-/

namespace LogdetLean.Coherence

open MeasureTheory ProbabilityTheory Real Set

noncomputable section

set_option linter.style.haveILetI false

/-- The elementary beta-function ratio appearing at Mellin exponent one. -/
private lemma beta_add_one_div_beta
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β / beta α β = α / (α + β) := by
  have hα0 : α ≠ 0 := hα.ne'
  have hαβ : 0 < α + β := add_pos hα hβ
  have hαβ0 : α + β ≠ 0 := hαβ.ne'
  have hΓα : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have hΓβ : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
  have hΓαβ : Real.Gamma (α + β) ≠ 0 :=
    (Real.Gamma_pos_of_pos hαβ).ne'
  rw [beta, beta, Real.Gamma_add_one hα0]
  rw [show α + 1 + β = (α + β) + 1 by ring,
    Real.Gamma_add_one hαβ0]
  field_simp

/-- Exact first moment of a beta distribution:
`E[X] = α / (α + β)` for positive shape parameters. -/
theorem integral_id_betaMeasure
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ∂betaMeasure α β = α / (α + β) := by
  calc
    ∫ x, x ∂betaMeasure α β =
        ∫ x, x ^ (1 : ℝ) ∂betaMeasure α β := by
      simp only [Real.rpow_one]
    _ = beta (α + 1) β / beta α β :=
      LogdetLean.integral_rpow_betaMeasure hα hβ (by linarith)
    _ = α / (α + β) := beta_add_one_div_beta hα hβ

/-- The identity function is integrable under every beta law with positive
shape parameters. -/
theorem integrable_id_betaMeasure
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (fun x : ℝ ↦ x) (betaMeasure α β) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_id_betaMeasure hα hβ]
  exact (div_pos hα (add_pos hα hβ)).ne'

/-- A beta measure is concentrated on the nonnegative half-line.  This is a
direct consequence of the support indicator in mathlib's beta density. -/
private lemma ae_nonneg_betaMeasure (α β : ℝ) :
    0 ≤ᵐ[betaMeasure α β] (fun x : ℝ ↦ x) := by
  rw [betaMeasure]
  refine (ae_withDensity_iff (μ := volume)
    (measurable_betaPDFReal α β).ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hpdf
  by_contra hx
  apply hpdf
  have hx0 : betaPDFReal α β x = 0 := by
    rw [betaPDFReal, if_neg]
    exact fun hsupp ↦ hx hsupp.1.le
  rw [hx0, ENNReal.ofReal_zero]

/-- General real-valued Markov bound for a beta upper tail. -/
theorem betaMeasure_Ioi_real_le_mean_div
    {α β t : ℝ} (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t) :
    (betaMeasure α β).real (Ioi t) ≤ (α / (α + β)) / t := by
  letI : IsProbabilityMeasure (betaMeasure α β) :=
    isProbabilityMeasureBeta hα hβ
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_nonneg_betaMeasure α β)
    (integrable_id_betaMeasure hα hβ) t
  change t * (betaMeasure α β).real (Ici t) ≤
    ∫ x, x ∂betaMeasure α β at hmarkov
  have hmono :
      (betaMeasure α β).real (Ioi t) ≤
        (betaMeasure α β).real (Ici t) := by
    apply measureReal_mono
    intro x hx
    change t < x at hx
    change t ≤ x
    exact hx.le
    exact measure_ne_top _ _
  apply (le_div_iff₀ ht).2
  calc
    (betaMeasure α β).real (Ioi t) * t =
        t * (betaMeasure α β).real (Ioi t) := by ring
    _ ≤ t * (betaMeasure α β).real (Ici t) :=
      mul_le_mul_of_nonneg_left hmono ht.le
    _ ≤ ∫ x, x ∂betaMeasure α β := hmarkov
    _ = α / (α + β) := integral_id_betaMeasure hα hβ

/-- The squared inner product of two independent directions in `ℝ^m` has
beta mean `1/m`. -/
theorem integral_id_betaMeasure_half_sub_half
    {m : ℕ} (hm : 2 ≤ m) :
    ∫ x, x ∂betaMeasure (1 / 2)
        (((m - 1 : ℕ) : ℝ) / 2) = 1 / (m : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsub : 0 < m - 1 := Nat.sub_pos_of_lt (by omega)
  have hβ : 0 < (((m - 1 : ℕ) : ℝ) / 2) := by positivity
  rw [integral_id_betaMeasure (by norm_num : (0 : ℝ) < 1 / 2) hβ]
  rw [Nat.cast_sub hm1]
  field_simp [hm0.ne']
  norm_num

/-- Clean Markov upper-tail bound for the squared-correlation beta law. -/
theorem betaMeasure_half_sub_half_Ioi_real_le
    {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : 0 < t) :
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) ≤
      1 / ((m : ℝ) * t) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsub : 0 < m - 1 := Nat.sub_pos_of_lt (by omega)
  have hβ : 0 < (((m - 1 : ℕ) : ℝ) / 2) := by positivity
  have hgeneral := betaMeasure_Ioi_real_le_mean_div
    (α := (1 / 2 : ℝ)) (β := (((m - 1 : ℕ) : ℝ) / 2))
    (t := t) (by norm_num) hβ ht
  calc
    (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t) ≤
        ((1 / 2) / (1 / 2 + (((m - 1 : ℕ) : ℝ) / 2))) / t := hgeneral
    _ = 1 / ((m : ℝ) * t) := by
      rw [Nat.cast_sub hm1]
      field_simp [hm0.ne', ht.ne']
      norm_num

end

end LogdetLean.Coherence
