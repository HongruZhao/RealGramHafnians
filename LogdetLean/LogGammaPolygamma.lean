import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import LogdetLean.PolygammaSeries
/-!
# The reciprocal-power series are derivatives of `log Gamma`

This file supplies the analytic bridge between the positive series developed in
`PolygammaSeries` and derivatives of the real Gamma function.  Everything is
proved from mathlib's construction of `Gamma`, the Bohr--Mollerup convexity
theorem, and elementary differentiation of normally convergent series.

Exact reference identities: NIST DLMF 5.2.2 and 5.7.6 for the logarithmic
derivative/digamma series and DLMF 5.15.1 for the trigamma series. The finite
cumulant formulas using these series are Xie--Sun (2021), equations (3)--(7),
printed pp. 430--431. This file independently derives the identities from
mathlib foundations; it does not import them as axioms. See PROVENANCE.md.
-/

namespace LogdetLean

noncomputable section

open Filter Set

/-- Euler's convergent series for the logarithmic derivative of Gamma. -/
def digammaSeries (x : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant +
    ∑' l : ℕ, (1 / ((l + 1 : ℕ) : ℝ) - 1 / (x + (l : ℝ)))

private def eulerTerm (l : ℕ) (x : ℝ) : ℝ :=
  1 / ((l + 1 : ℕ) : ℝ) - 1 / (x + (l : ℝ))

private theorem hasDerivAt_eulerTerm (l : ℕ) {x : ℝ}
    (hx : x ≠ -(l : ℝ)) :
    HasDerivAt (eulerTerm l) (1 / (x + (l : ℝ)) ^ 2) x := by
  unfold eulerTerm
  have hne : x + (l : ℝ) ≠ 0 := by
    intro h
    apply hx
    linarith
  have hinv : HasDerivAt (fun y : ℝ ↦ (y + (l : ℝ))⁻¹)
      (-1 / (x + (l : ℝ)) ^ 2) x :=
    ((hasDerivAt_id x).add_const (l : ℝ)).inv hne
  have h := hinv.const_sub (1 / ((l + 1 : ℕ) : ℝ))
  have hcoef : -(-1 / (x + (l : ℝ)) ^ 2) = 1 / (x + (l : ℝ)) ^ 2 := by ring
  simpa only [one_div] using h.congr_deriv hcoef

private theorem summable_eulerTerm {x : ℝ} (hx : 0 < x) :
    Summable (fun l : ℕ ↦ eulerTerm l x) := by
  let δ : ℝ := min x 1 / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδx : δ < x := by
    dsimp [δ]
    have hmin : min x 1 ≤ x := min_le_left _ _
    nlinarith [hδ]
  have hδ1 : δ < 1 := by
    dsimp [δ]
    have hmin : min x 1 ≤ 1 := min_le_right _ _
    nlinarith [hδ]
  apply summable_of_summable_hasDerivAt_of_isPreconnected
      (u := fun l : ℕ ↦ 1 / (δ + (l : ℝ)) ^ 2)
      (g := fun l y ↦ eulerTerm l y)
      (g' := fun l y ↦ 1 / (y + (l : ℝ)) ^ 2)
      (t := Ioi δ) (y₀ := 1) (y := x)
      (summable_trigammaSeries_terms hδ) isOpen_Ioi isPreconnected_Ioi
  · intro l y hy
    exact hasDerivAt_eulerTerm l (by
      have hy0 : 0 < y := hδ.trans hy
      have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      linarith)
  · intro l y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (y + (l : ℝ)) ^ 2)]
    exact trigammaSeries_term_antitone hδ hy.le l
  · exact mem_Ioi.mpr hδ1
  · simp [eulerTerm, Nat.cast_add, Nat.cast_one, add_comm]
  · exact mem_Ioi.mpr hδx

/-- The Euler series has derivative equal to the positive quadratic series. -/
theorem hasDerivAt_digammaSeries {x : ℝ} (hx : 0 < x) :
    HasDerivAt digammaSeries (trigammaSeries x) x := by
  let δ : ℝ := min x 1 / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδx : δ < x := by
    dsimp [δ]
    have hmin : min x 1 ≤ x := min_le_left _ _
    nlinarith [hδ]
  have hδ1 : δ < 1 := by
    dsimp [δ]
    have hmin : min x 1 ≤ 1 := min_le_right _ _
    nlinarith [hδ]
  have hseries : HasDerivAt
      (fun y : ℝ ↦ ∑' l : ℕ, eulerTerm l y)
      (∑' l : ℕ, 1 / (x + (l : ℝ)) ^ 2) x := by
    apply hasDerivAt_tsum_of_isPreconnected
        (u := fun l : ℕ ↦ 1 / (δ + (l : ℝ)) ^ 2)
        (g := fun l y ↦ eulerTerm l y)
        (g' := fun l y ↦ 1 / (y + (l : ℝ)) ^ 2)
        (t := Ioi δ) (y₀ := 1) (y := x)
        (summable_trigammaSeries_terms hδ) isOpen_Ioi isPreconnected_Ioi
    · intro l y hy
      exact hasDerivAt_eulerTerm l (by
        have hy0 : 0 < y := hδ.trans hy
        have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
        linarith)
    · intro l y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (y + (l : ℝ)) ^ 2)]
      exact trigammaSeries_term_antitone hδ hy.le l
    · exact mem_Ioi.mpr hδ1
    · simp [eulerTerm, Nat.cast_add, Nat.cast_one, add_comm]
    · exact mem_Ioi.mpr hδx
  change HasDerivAt
    (fun y : ℝ ↦ -Real.eulerMascheroniConstant + ∑' l : ℕ, eulerTerm l y)
    (∑' l : ℕ, 1 / (x + (l : ℝ)) ^ 2) x
  have h := ((hasDerivAt_const x (-Real.eulerMascheroniConstant)).add hseries).congr_deriv
    (zero_add (∑' l : ℕ, 1 / (x + (l : ℝ)) ^ 2))
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)

private theorem hasDerivAt_trigammaTerm (l : ℕ) {x : ℝ}
    (hx : x ≠ -(l : ℝ)) :
    HasDerivAt (fun y : ℝ ↦ 1 / (y + (l : ℝ)) ^ 2)
      (-2 / (x + (l : ℝ)) ^ 3) x := by
  have hne : x + (l : ℝ) ≠ 0 := by
    intro h
    apply hx
    linarith
  have hinv : HasDerivAt (fun y : ℝ ↦ (y + (l : ℝ))⁻¹)
      (-1 / (x + (l : ℝ)) ^ 2) x :=
    ((hasDerivAt_id x).add_const (l : ℝ)).inv hne
  have hcoef :
      (2 : ℝ) * (x + (l : ℝ))⁻¹ ^ (2 - 1) * (-1 / (x + (l : ℝ)) ^ 2) =
        -2 / (x + (l : ℝ)) ^ 3 := by
    norm_num
    field_simp [hne]
  have h := (hinv.fun_pow 2).congr_deriv hcoef
  simpa only [one_div, inv_pow] using h

/-- The derivative of the quadratic series is the negative cubic series. -/
theorem hasDerivAt_trigammaSeries {x : ℝ} (hx : 0 < x) :
    HasDerivAt trigammaSeries (-negPsiTwoSeries x) x := by
  let δ : ℝ := x / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδx : δ < x := by dsimp [δ]; linarith
  have hseries : HasDerivAt
      (fun y : ℝ ↦ ∑' l : ℕ, 1 / (y + (l : ℝ)) ^ 2)
      (∑' l : ℕ, -2 / (x + (l : ℝ)) ^ 3) x := by
    apply hasDerivAt_tsum_of_isPreconnected
        (u := fun l : ℕ ↦ 2 * (1 / (δ + (l : ℝ)) ^ 3))
        (g := fun l y ↦ 1 / (y + (l : ℝ)) ^ 2)
        (g' := fun l y ↦ -2 / (y + (l : ℝ)) ^ 3)
        (t := Ioi δ) (y₀ := x) (y := x)
        ((summable_negPsiTwoSeries_terms hδ).mul_left 2)
        isOpen_Ioi isPreconnected_Ioi
    · intro l y hy
      exact hasDerivAt_trigammaTerm l (by
        have hy0 : 0 < y := hδ.trans hy
        have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
        linarith)
    · intro l y hy
      have hy0 : 0 < y := hδ.trans hy
      have hden : 0 < y + (l : ℝ) :=
        add_pos_of_pos_of_nonneg hy0 (Nat.cast_nonneg l)
      calc
        ‖-2 / (y + (l : ℝ)) ^ 3‖ = 2 * (1 / (y + (l : ℝ)) ^ 3) := by
          rw [Real.norm_eq_abs, abs_of_nonpos (by
            exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))]
          ring
        _ ≤ 2 * (1 / (δ + (l : ℝ)) ^ 3) :=
          mul_le_mul_of_nonneg_left
            (negPsiTwoSeries_term_antitone hδ hy.le l) (by norm_num)
    · exact mem_Ioi.mpr hδx
    · exact summable_trigammaSeries_terms hx
    · exact mem_Ioi.mpr hδx
  unfold trigammaSeries negPsiTwoSeries
  convert hseries using 1
  have hs := summable_negPsiTwoSeries_terms hx
  calc
    -(2 * ∑' l : ℕ, 1 / (x + (l : ℝ)) ^ 3) =
        -(∑' l : ℕ, 2 * (1 / (x + (l : ℝ)) ^ 3)) := by rw [hs.tsum_mul_left]
    _ = ∑' l : ℕ, -(2 * (1 / (x + (l : ℝ)) ^ 3)) := by rw [tsum_neg]
    _ = ∑' l : ℕ, -2 / (x + (l : ℝ)) ^ 3 := by
      congr 1
      funext l
      ring

/-! ## Identification with derivatives of `log Gamma` -/

private def realLogGamma : ℝ → ℝ := Real.log ∘ Real.Gamma

private theorem differentiableAt_realLogGamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ realLogGamma x := by
  unfold realLogGamma
  exact (Real.differentiableAt_Gamma (fun m ↦ by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)).log (Real.Gamma_pos_of_pos hx).ne'

private theorem realLogGamma_add_one {x : ℝ} (hx : 0 < x) :
    realLogGamma (x + 1) = realLogGamma x + Real.log x := by
  unfold realLogGamma
  simp only [Function.comp_apply]
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

private theorem deriv_realLogGamma_add_one {x : ℝ} (hx : 0 < x) :
    deriv realLogGamma (x + 1) = deriv realLogGamma x + 1 / x := by
  rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
    ← deriv_add (differentiableAt_realLogGamma hx) (Real.differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact realLogGamma_add_one hy

private theorem deriv_realLogGamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    deriv realLogGamma (x + n) = deriv realLogGamma x +
      ∑ l ∈ Finset.range n, 1 / (x + (l : ℝ)) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [Nat.cast_succ, show x + ((n : ℝ) + 1) = (x + n) + 1 by ring,
        deriv_realLogGamma_add_one (by positivity), hn, Finset.sum_range_succ]
      ring

private theorem log_le_deriv_realLogGamma_add_one {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ deriv realLogGamma (x + 1) := by
  refine (le_of_eq ?_).trans <|
    Real.convexOn_log_Gamma.slope_le_deriv (mem_Ioi.mpr hx)
      (by positivity : 0 < x + 1) (by linarith)
      (differentiableAt_realLogGamma (by positivity))
  rw [slope_def_field, show x + 1 - x = (1 : ℝ) by ring, div_one]
  change Real.log x = realLogGamma (x + 1) - realLogGamma x
  rw [realLogGamma_add_one hx, add_sub_cancel_left]

private theorem deriv_realLogGamma_le_log {x : ℝ} (hx : 0 < x) :
    deriv realLogGamma x ≤ Real.log x := by
  refine (Real.convexOn_log_Gamma.deriv_le_slope hx (by positivity : 0 < x + 1)
      (by linarith) (differentiableAt_realLogGamma hx)).trans (le_of_eq ?_)
  rw [slope_def_field, show x + 1 - x = (1 : ℝ) by ring, div_one]
  change realLogGamma (x + 1) - realLogGamma x = Real.log x
  rw [realLogGamma_add_one hx, add_sub_cancel_left]

private theorem tendsto_deriv_realLogGamma_add_nat_sub_log (x : ℝ) :
    Tendsto (fun n : ℕ ↦ deriv realLogGamma (x + n) - Real.log n)
      atTop (nhds 0) := by
  have hl : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + (x - 1)) - Real.log n)
      atTop (nhds 0) :=
    (Real.tendsto_log_comp_add_sub_log (x - 1)).comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + x) - Real.log n)
      atTop (nhds 0) :=
    (Real.tendsto_log_comp_add_sub_log x).comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
  · filter_upwards [eventually_gt_atTop (Nat.ceil (1 - x))] with n hn
    have hpos : 0 < x + (n : ℝ) - 1 := by
      have hceil : 1 - x ≤ (Nat.ceil (1 - x) : ℝ) := Nat.le_ceil _
      have hcast : (Nat.ceil (1 - x) : ℝ) < n := by exact_mod_cast hn
      linarith
    have h := log_le_deriv_realLogGamma_add_one hpos
    have heq : (x + (n : ℝ) - 1) + 1 = x + (n : ℝ) := by ring
    rw [heq] at h
    have hlog : (n : ℝ) + (x - 1) = x + (n : ℝ) - 1 := by ring
    rw [hlog]
    exact sub_le_sub_right h (Real.log n)
  · filter_upwards [eventually_gt_atTop (Nat.ceil (-x))] with n hn
    have hpos : 0 < x + (n : ℝ) := by
      have hceil : -x ≤ (Nat.ceil (-x) : ℝ) := Nat.le_ceil _
      have hcast : (Nat.ceil (-x) : ℝ) < n := by exact_mod_cast hn
      linarith
    rw [add_comm (n : ℝ) x]
    exact sub_le_sub_right (deriv_realLogGamma_le_log hpos) (Real.log n)

/-- The finite Euler sum separates into a harmonic number and a shifted
reciprocal sum. -/
private theorem sum_range_eulerTerm (x : ℝ) (n : ℕ) :
    ∑ l ∈ Finset.range n, eulerTerm l x =
      (harmonic n : ℝ) - ∑ l ∈ Finset.range n, 1 / (x + (l : ℝ)) := by
  unfold eulerTerm harmonic
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- The Euler series is the logarithmic derivative of the real Gamma
function on the positive half-line. -/
theorem deriv_logGamma_eq_digammaSeries {x : ℝ} (hx : 0 < x) :
    deriv (Real.log ∘ Real.Gamma) x = digammaSeries x := by
  have hrec : Tendsto
      (fun n : ℕ ↦ Real.log n -
        ∑ l ∈ Finset.range n, 1 / (x + (l : ℝ)))
      atTop (nhds (deriv realLogGamma x)) := by
    have htail := tendsto_deriv_realLogGamma_add_nat_sub_log x
    have hrewrite :
        (fun n : ℕ ↦ Real.log n -
          ∑ l ∈ Finset.range n, 1 / (x + (l : ℝ))) =
        (fun n : ℕ ↦ deriv realLogGamma x -
          (deriv realLogGamma (x + n) - Real.log n)) := by
      funext n
      rw [deriv_realLogGamma_add_nat hx n]
      ring
    rw [hrewrite]
    simpa using (tendsto_const_nhds.sub htail)
  have hpartial : Tendsto
      (fun n : ℕ ↦ ∑ l ∈ Finset.range n, eulerTerm l x)
      atTop (nhds (Real.eulerMascheroniConstant + deriv realLogGamma x)) := by
    have h := Real.tendsto_harmonic_sub_log.add hrec
    convert h using 1
    · funext n
      rw [sum_range_eulerTerm]
      ring
  have hsum := (summable_eulerTerm hx).hasSum.tendsto_sum_nat
  have heq : (∑' l : ℕ, eulerTerm l x) =
      Real.eulerMascheroniConstant + deriv realLogGamma x :=
    tendsto_nhds_unique hsum hpartial
  unfold digammaSeries
  change deriv realLogGamma x =
    -Real.eulerMascheroniConstant + ∑' l : ℕ, eulerTerm l x
  rw [heq]
  ring

/-- The second derivative of `log Gamma` is the positive reciprocal-square
series. -/
theorem iteratedDeriv_two_logGamma_eq_trigammaSeries {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (Real.log ∘ Real.Gamma) x = trigammaSeries x := by
  have hevent : deriv (Real.log ∘ Real.Gamma) =ᶠ[nhds x] digammaSeries := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact deriv_logGamma_eq_digammaSeries hy
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one,
    hevent.deriv_eq]
  exact (hasDerivAt_digammaSeries hx).deriv

/-- The third derivative of `log Gamma` is minus the positive
reciprocal-cube series. -/
theorem iteratedDeriv_three_logGamma_eq_negPsiTwoSeries {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 (Real.log ∘ Real.Gamma) x = -negPsiTwoSeries x := by
  have hevent : iteratedDeriv 2 (Real.log ∘ Real.Gamma) =ᶠ[nhds x]
      trigammaSeries := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact iteratedDeriv_two_logGamma_eq_trigammaSeries hy
  rw [show 3 = 2 + 1 by omega, iteratedDeriv_succ, hevent.deriv_eq]
  exact (hasDerivAt_trigammaSeries hx).deriv

end

end LogdetLean
