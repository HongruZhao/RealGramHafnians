import LogdetLean.HigherCumulants
import Mathlib.Analysis.Calculus.SmoothSeries
/-!
# All-order derivatives of the real log-Gamma function

For `r >= 2` and `x > 0`, this file proves directly that

`(d/dx)^r log Gamma(x) = (-1)^r (r-1)! sum_l (x+l)^(-r)`.

The mathematical identity is NIST DLMF 5.15.1 together with repeated
differentiation.  Xie--Sun (2021), equation (3), printed p. 430, uses the same
series for the finite log-determinant cumulants.  The Lean proof below does
not assume a polygamma package: it differentiates the normally convergent
reciprocal-power series term by term and then inducts from the already proved
trigamma identity.
-/

namespace LogdetLean

open Filter Set

noncomputable section

/-- The shifted reciprocal-power series. -/
def reciprocalPowerSeries (r : ℕ) (x : ℝ) : ℝ :=
  ∑' l : ℕ, 1 / (x + (l : ℝ)) ^ r

/-- Its signed factorial multiple, equal to the order-`r` derivative of
`log Gamma` for `r >= 2`. -/
def signedPolygammaSeries (r : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ r * (Nat.factorial (r - 1) : ℝ) *
    reciprocalPowerSeries r x

private theorem hasDerivAt_shifted_reciprocal_pow
    {r l : ℕ} (hr : 0 < r) {x : ℝ}
    (hx : x + (l : ℝ) ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ 1 / (y + (l : ℝ)) ^ r)
      (-(r : ℝ) / (x + (l : ℝ)) ^ (r + 1)) x := by
  have hshift : HasDerivAt (fun y : ℝ ↦ y + (l : ℝ)) 1 x :=
    (hasDerivAt_id x).add_const (l : ℝ)
  simpa only [Function.comp_def, mul_one] using
    (hasDerivAt_one_div_pow hr hx).comp x hshift

/-- The reciprocal-power series can be differentiated term by term on the
positive half-line. -/
theorem hasDerivAt_reciprocalPowerSeries
    {r : ℕ} (hr : 1 < r) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (reciprocalPowerSeries r)
      (-(r : ℝ) * reciprocalPowerSeries (r + 1) x) x := by
  let δ : ℝ := x / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδx : δ < x := by dsimp [δ]; linarith
  have hsum : HasDerivAt
      (fun y : ℝ ↦ ∑' l : ℕ, 1 / (y + (l : ℝ)) ^ r)
      (∑' l : ℕ, -(r : ℝ) /
        (x + (l : ℝ)) ^ (r + 1)) x := by
    apply hasDerivAt_tsum_of_isPreconnected
        (u := fun l : ℕ ↦ (r : ℝ) *
          (1 / (δ + (l : ℝ)) ^ (r + 1)))
        (g := fun l y ↦ 1 / (y + (l : ℝ)) ^ r)
        (g' := fun l y ↦ -(r : ℝ) /
          (y + (l : ℝ)) ^ (r + 1))
        (t := Ioi δ) (y₀ := x) (y := x)
        ((summable_shifted_reciprocal_pow hδ (by omega : 1 < r + 1)).mul_left
          (r : ℝ))
        isOpen_Ioi isPreconnected_Ioi
    · intro l y hy
      exact hasDerivAt_shifted_reciprocal_pow (by omega) (by
        have hy0 : 0 < y := hδ.trans hy
        have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
        linarith)
    · intro l y hy
      have hy0 : 0 < y := hδ.trans hy
      have hden : 0 < y + (l : ℝ) :=
        add_pos_of_pos_of_nonneg hy0 (Nat.cast_nonneg l)
      have hmono :
          1 / (y + (l : ℝ)) ^ (r + 1) ≤
            1 / (δ + (l : ℝ)) ^ (r + 1) := by
        apply one_div_le_one_div_of_le
        · positivity
        · gcongr
          exact hy.le
      have hnonpos :
          -(r : ℝ) / (y + (l : ℝ)) ^ (r + 1) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (Nat.cast_nonneg r))
          (pow_nonneg hden.le (r + 1))
      rw [Real.norm_eq_abs, abs_of_nonpos hnonpos, neg_div, neg_neg]
      simpa [div_eq_mul_inv, one_div] using
        (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg r))
    · exact mem_Ioi.mpr hδx
    · exact summable_shifted_reciprocal_pow hx hr
    · exact mem_Ioi.mpr hδx
  unfold reciprocalPowerSeries
  convert hsum using 1
  have hs := summable_shifted_reciprocal_pow hx (by omega : 1 < r + 1)
  calc
    -(r : ℝ) * ∑' l : ℕ, 1 / (x + (l : ℝ)) ^ (r + 1) =
        ∑' l : ℕ, (-(r : ℝ)) *
          (1 / (x + (l : ℝ)) ^ (r + 1)) := by
      rw [hs.tsum_mul_left]
    _ = ∑' l : ℕ, -(r : ℝ) /
          (x + (l : ℝ)) ^ (r + 1) := by
      congr 1
      funext l
      ring

/-- Differentiating the signed order-`r` series gives the signed order
`r+1` series. -/
theorem hasDerivAt_signedPolygammaSeries
    {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (signedPolygammaSeries r)
      (signedPolygammaSeries (r + 1) x) x := by
  have hbase := (hasDerivAt_reciprocalPowerSeries (r := r) (by omega) hx).const_mul
    ((-1 : ℝ) ^ r * (Nat.factorial (r - 1) : ℝ))
  apply hbase.congr_deriv
  unfold signedPolygammaSeries
  have hfac : Nat.factorial r = r * Nat.factorial (r - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    rw [Nat.factorial_succ]
    simp
  have hrsimp : r + 1 - 1 = r := by omega
  rw [hrsimp]
  rw [hfac]
  push_cast
  rw [pow_succ]
  ring

/-- Base case: the signed order-two series is the trigamma series. -/
theorem signedPolygammaSeries_two (x : ℝ) :
    signedPolygammaSeries 2 x = trigammaSeries x := by
  simp [signedPolygammaSeries, reciprocalPowerSeries, trigammaSeries]

/-- All positive-half-line derivatives of `log Gamma`, from order two on. -/
theorem iteratedDeriv_logGamma_eq_signedPolygammaSeries
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (n + 2) (Real.log ∘ Real.Gamma) x =
      signedPolygammaSeries (n + 2) x := by
  induction n generalizing x with
  | zero =>
      simpa [signedPolygammaSeries_two] using
        iteratedDeriv_two_logGamma_eq_trigammaSeries hx
  | succ n ih =>
      have hevent :
          iteratedDeriv (n + 2) (Real.log ∘ Real.Gamma) =ᶠ[nhds x]
            signedPolygammaSeries (n + 2) := by
        filter_upwards [eventually_gt_nhds hx] with y hy
        exact ih hy
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        iteratedDeriv_succ, hevent.deriv_eq]
      exact (hasDerivAt_signedPolygammaSeries (by omega) hx).deriv

/-- Reindexed public form for an arbitrary order `r >= 2`. -/
theorem iteratedDeriv_logGamma_eq_signedPolygammaSeries_of_two_le
    {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv r (Real.log ∘ Real.Gamma) x =
      signedPolygammaSeries r x := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  exact iteratedDeriv_logGamma_eq_signedPolygammaSeries n hx

end

end LogdetLean
