import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecificLimits.Basic
import LogdetLean.Coherence.BetaTailMeasure
/-!
# The normalization constant for a `Beta(1/2,(m-1)/2)` tail

The beta half-tail Mills estimate contains the constant

`sqrt m / (((m-1)/2) * beta (1/2,(m-1)/2))`.

This file proves that it tends to `sqrt 2 / sqrt pi`.  Rather than importing
an unverified Gamma-ratio asymptotic, we derive the needed ratio estimate from
mathlib's proved log-convexity theorem for `Real.Gamma`.  For every `x > 0`,

`1 <= sqrt x * Gamma x / Gamma (x+1/2)
   <= 1 + 1/(2*x)`.

The result follows by taking `x=m/2`.  This gives an explicit error envelope
as well as the asymptotic limit.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter ProbabilityTheory Real Set
open scoped Topology Real

/-- The first midpoint consequence of log-convexity of Gamma. -/
theorem Gamma_add_half_le_sqrt_mul_Gamma
    {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1 / 2) ≤ √x * Real.Gamma x := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    hx (by linarith : 0 < x + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hG : 0 ≤ Real.Gamma x := (Real.Gamma_pos_of_pos hx).le
  have hroot : 0 ≤ √x := Real.sqrt_nonneg x
  rw [show (1 / 2 : ℝ) * x + 1 / 2 * (x + 1) = x + 1 / 2 by ring,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.Gamma_add_one hx.ne', Real.sqrt_mul hx.le] at h
  calc
    Real.Gamma (x + 1 / 2) ≤ √(Real.Gamma x) * (√x * √(Real.Gamma x)) := h
    _ = √x * Real.Gamma x := by
      rw [← mul_assoc, mul_comm (√(Real.Gamma x)) (√x), mul_assoc,
        Real.mul_self_sqrt hG]

/-- The adjacent midpoint consequence of log-convexity of Gamma. -/
theorem mul_Gamma_le_sqrt_add_half_mul_Gamma_add_half
    {x : ℝ} (hx : 0 < x) :
    x * Real.Gamma x ≤ √(x + 1 / 2) * Real.Gamma (x + 1 / 2) := by
  have hxhalf : 0 < x + 1 / 2 := by linarith
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    hxhalf (by linarith : 0 < x + 3 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hG : 0 ≤ Real.Gamma (x + 1 / 2) :=
    (Real.Gamma_pos_of_pos hxhalf).le
  rw [show (1 / 2 : ℝ) * (x + 1 / 2) + 1 / 2 * (x + 3 / 2) = x + 1 by ring,
    Real.Gamma_add_one hx.ne', ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    show x + 3 / 2 = (x + 1 / 2) + 1 by ring,
    Real.Gamma_add_one hxhalf.ne', Real.sqrt_mul hxhalf.le] at h
  calc
    x * Real.Gamma x ≤
        √(Real.Gamma (x + 1 / 2)) *
          (√(x + 1 / 2) * √(Real.Gamma (x + 1 / 2))) := h
    _ = √(x + 1 / 2) * Real.Gamma (x + 1 / 2) := by
      rw [← mul_assoc,
        mul_comm (√(Real.Gamma (x + 1 / 2))) (√(x + 1 / 2)),
        mul_assoc, Real.mul_self_sqrt hG]

/-- The normalized half-step Gamma ratio. -/
def gammaHalfRatioScale (x : ℝ) : ℝ :=
  √x * Real.Gamma x / Real.Gamma (x + 1 / 2)

/-- Explicit two-sided bounds for the normalized half-step Gamma ratio. -/
theorem gammaHalfRatioScale_bounds {x : ℝ} (hx : 0 < x) :
    1 ≤ gammaHalfRatioScale x ∧
      gammaHalfRatioScale x ≤ 1 + 1 / (2 * x) := by
  have hsqrt : 0 < √x := Real.sqrt_pos.2 hx
  have hxhalf : 0 < x + 1 / 2 := by linarith
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGh : 0 < Real.Gamma (x + 1 / 2) := Real.Gamma_pos_of_pos hxhalf
  have hmid1 := Gamma_add_half_le_sqrt_mul_Gamma hx
  have hmid2 := mul_Gamma_le_sqrt_add_half_mul_Gamma_add_half hx
  constructor
  · unfold gammaHalfRatioScale
    apply (le_div_iff₀ hGh).2
    simpa using hmid1
  · unfold gammaHalfRatioScale
    have hsqrt_mono : √x ≤ √(x + 1 / 2) := by
      exact Real.sqrt_le_sqrt (by linarith)
    have hprod : √x * √(x + 1 / 2) ≤ x + 1 / 2 := by
      calc
        √x * √(x + 1 / 2) ≤
            √(x + 1 / 2) * √(x + 1 / 2) := by
          exact mul_le_mul_of_nonneg_right hsqrt_mono (Real.sqrt_nonneg _)
        _ = x + 1 / 2 := Real.mul_self_sqrt hxhalf.le
    apply (div_le_iff₀ hGh).2
    rw [show 1 + 1 / (2 * x) = (x + 1 / 2) / x by
      field_simp [hx.ne']]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hx).2
    calc
      (√x * Real.Gamma x) * x =
          √x * (x * Real.Gamma x) := by ring
      _ ≤ √x * (√(x + 1 / 2) * Real.Gamma (x + 1 / 2)) :=
        mul_le_mul_of_nonneg_left hmid2 (Real.sqrt_nonneg _)
      _ = (√x * √(x + 1 / 2)) * Real.Gamma (x + 1 / 2) := by ring
      _ ≤ (x + 1 / 2) * Real.Gamma (x + 1 / 2) :=
        mul_le_mul_of_nonneg_right hprod hGh.le
      _ = (x + 1 / 2) * Real.Gamma (x + 1 / 2) := rfl

/-- Along positive integers, the normalized half-step Gamma ratio tends to
one.  The proof is the direct squeeze supplied by
`gammaHalfRatioScale_bounds`. -/
theorem tendsto_gammaHalfRatioScale_nat_half :
    Tendsto (fun m : ℕ ↦ gammaHalfRatioScale ((m : ℝ) / 2))
      atTop (nhds 1) := by
  have hupper : Tendsto (fun m : ℕ ↦
      1 + 1 / (2 * ((m : ℝ) / 2))) atTop (nhds 1) := by
    have hzero : Tendsto (fun m : ℕ ↦ 1 / (m : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hone := (tendsto_const_nhds : Tendsto (fun _m : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
    have hfun : (fun m : ℕ ↦ 1 + 1 / (2 * ((m : ℝ) / 2))) =
        (fun m : ℕ ↦ 1 + 1 / (m : ℝ)) := by
      funext m
      congr 2
      ring
    rw [hfun]
    simpa using hone.add hzero
  have hbounds : ∀ᶠ m : ℕ in atTop,
      1 ≤ gammaHalfRatioScale ((m : ℝ) / 2) ∧
        gammaHalfRatioScale ((m : ℝ) / 2) ≤
          1 + 1 / (2 * ((m : ℝ) / 2)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact gammaHalfRatioScale_bounds (by positivity)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper (hbounds.mono fun _ h ↦ h.1)
      (hbounds.mono fun _ h ↦ h.2)

/-- Gamma-quotient form of the endpoint normalization constant. -/
def betaHalfGammaNormalization (m : ℕ) : ℝ :=
  √(m : ℝ) * Real.Gamma ((m : ℝ) / 2) /
    (√Real.pi * Real.Gamma (((m : ℝ) + 1) / 2))

/-- The Gamma-quotient normalization is a constant multiple of the normalized
half-step Gamma ratio. -/
theorem betaHalfGammaNormalization_eq
    {m : ℕ} :
    betaHalfGammaNormalization m =
      (√2 / √Real.pi) * gammaHalfRatioScale ((m : ℝ) / 2) := by
  have hsqrt : √(m : ℝ) = √2 * √((m : ℝ) / 2) := by
    calc
      √(m : ℝ) = √(2 * ((m : ℝ) / 2)) := by congr 1; ring
      _ = √2 * √((m : ℝ) / 2) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ((m : ℝ) / 2)
  unfold betaHalfGammaNormalization gammaHalfRatioScale
  rw [hsqrt, show ((m : ℝ) + 1) / 2 = (m : ℝ) / 2 + 1 / 2 by ring]
  ring

/-- The normalization constant tends to `sqrt 2 / sqrt pi`. -/
theorem tendsto_betaHalfGammaNormalization :
    Tendsto betaHalfGammaNormalization atTop (nhds (√2 / √Real.pi)) := by
  have hscaled := (tendsto_const_nhds :
      Tendsto (fun _m : ℕ ↦ √2 / √Real.pi) atTop (nhds (√2 / √Real.pi))).mul
        tendsto_gammaHalfRatioScale_nat_half
  have heq : ∀ᶠ m : ℕ in atTop,
      betaHalfGammaNormalization m =
        (√2 / √Real.pi) * gammaHalfRatioScale ((m : ℝ) / 2) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact betaHalfGammaNormalization_eq
  simpa using hscaled.congr' (Filter.EventuallyEq.symm heq)

/-- The normalization constant in the endpoint/Mills formula, written in its
original Beta-function form. -/
def betaHalfEndpointNormalization (m : ℕ) : ℝ :=
  √(m : ℝ) /
    ((((m : ℝ) - 1) / 2) *
      beta (1 / 2) (((m : ℝ) - 1) / 2))

/-- For `m > 1`, the original Beta normalization equals its Gamma-quotient
form exactly. -/
theorem betaHalfEndpointNormalization_eq_gamma
    {m : ℕ} (hm : 1 < m) :
    betaHalfEndpointNormalization m = betaHalfGammaNormalization m := by
  let b : ℝ := ((m : ℝ) - 1) / 2
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (sub_pos.mpr (by exact_mod_cast hm)) (by norm_num)
  have hmhalf : 0 < (m : ℝ) / 2 := by positivity
  have hsum : (1 / 2 : ℝ) + b = (m : ℝ) / 2 := by
    dsimp [b]
    ring
  have hrec : Real.Gamma (((m : ℝ) + 1) / 2) = b * Real.Gamma b := by
    calc
      Real.Gamma (((m : ℝ) + 1) / 2) = Real.Gamma (b + 1) := by
        congr 1
        dsimp [b]
        ring
      _ = b * Real.Gamma b := Real.Gamma_add_one hb.ne'
  unfold betaHalfEndpointNormalization betaHalfGammaNormalization
  change √(m : ℝ) / (b * beta (1 / 2) b) = _
  rw [ProbabilityTheory.beta, Real.Gamma_one_half_eq, hsum, hrec]
  field_simp [hb.ne', (Real.Gamma_pos_of_pos hb).ne',
    (Real.Gamma_pos_of_pos hmhalf).ne',
    (Real.sqrt_pos.2 Real.pi_pos).ne']

/-- The original Beta normalization has the same asymptotic limit. -/
theorem tendsto_betaHalfEndpointNormalization :
    Tendsto betaHalfEndpointNormalization atTop (nhds (√2 / √Real.pi)) := by
  have heq : ∀ᶠ m : ℕ in atTop,
      betaHalfEndpointNormalization m = betaHalfGammaNormalization m := by
    filter_upwards [eventually_ge_atTop 2] with m hm
    exact betaHalfEndpointNormalization_eq_gamma (by omega)
  exact tendsto_betaHalfGammaNormalization.congr' (Filter.EventuallyEq.symm heq)

/-- Equivalent conventional form of the limit, `sqrt (2/pi)`. -/
theorem tendsto_betaHalfEndpointNormalization_sqrt_div :
    Tendsto betaHalfEndpointNormalization atTop (nhds (√(2 / Real.pi))) := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2) Real.pi]
  exact tendsto_betaHalfEndpointNormalization

end

end LogdetLean.Coherence
