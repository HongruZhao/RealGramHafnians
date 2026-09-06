import LogdetLean.BetaCumulantSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic
/-!
# All-order reciprocal-power coefficients and their majorant

This file defines, for every `r >= 2`, the finite sum of positive
reciprocal-power differences

`(r-1)! * sum_j sum_l ((a_j+l)^(-r) - (M+l)^(-r))`.

For orders two and three, the last two theorems identify this coefficient
with the already formalized series `V_{m,p}` and `A_{m,p}`.  The separate
CGF-derivative bridge is required before calling the order-`r` coefficient an
actual probabilistic cumulant for every `r`; that bridge is intentionally not
asserted here.

The reciprocal-power representation is motivated by the classical
polygamma series: Xie--Sun (2021), equation (3), printed p. 430.  Their
equations (4)--(7), printed pp. 430--431, give the corresponding low-order
log-determinant cumulants.  The all-order majorant proved below is a direct
Lean derivation, not an imported theorem.
-/

namespace LogdetLean

open scoped BigOperators

noncomputable section

/-- The positive reciprocal-power difference at order `r`. -/
def reciprocalPowerDifference (r : ℕ) (x y : ℝ) : ℝ :=
  ∑' l : ℕ, (1 / (x + (l : ℝ)) ^ r - 1 / (y + (l : ℝ)) ^ r)

/-- The all-order reciprocal-power coefficient.  A separate CGF-derivative
theorem is needed to identify it with the magnitude of an actual cumulant. -/
def nullCumulantMagnitudeSeries (r m p : ℕ) : ℝ :=
  (Nat.factorial (r - 1) : ℝ) *
    ∑ j ∈ Finset.Icc 2 p,
      reciprocalPowerDifference r (betaShapeA m j) (betaShapeTotal m)

/-- Standardization by the exact variance, expressed with the natural power
of `sqrt V` to avoid any ambiguity about real exponents. -/
def nullStandardizedCumulantMagnitudeSeries (r m p : ℕ) : ℝ :=
  nullCumulantMagnitudeSeries r m p /
    (Real.sqrt (nullVSeries m p)) ^ r

/-- The analytic Taylor scale `Delta = a_* sqrt(V)`. -/
def nullAnalyticScale (m p : ℕ) : ℝ :=
  betaShapeA m p * Real.sqrt (nullVSeries m p)

/-- Shifted reciprocal powers are summable in every order greater than one. -/
theorem summable_shifted_reciprocal_pow {x : ℝ} (hx : 0 < x)
    {r : ℕ} (hr : 1 < r) :
    Summable (fun l : ℕ ↦ 1 / (x + (l : ℝ)) ^ r) := by
  have hbase : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) ^ r) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr hr)
  rw [← summable_nat_add_iff 1]
  refine hbase.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  apply one_div_le_one_div_of_le (pow_pos hn r)
  gcongr
  linarith

theorem summable_reciprocalPowerDifference {r : ℕ} (hr : 1 < r)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Summable (fun l : ℕ ↦
      1 / (x + (l : ℝ)) ^ r - 1 / (y + (l : ℝ)) ^ r) :=
  (summable_shifted_reciprocal_pow hx hr).sub
    (summable_shifted_reciprocal_pow hy hr)

theorem reciprocalPowerDifference_nonneg {r : ℕ} (_hr : 0 < r)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ reciprocalPowerDifference r x y := by
  unfold reciprocalPowerDifference
  apply tsum_nonneg
  intro l
  apply sub_nonneg.mpr
  apply one_div_le_one_div_of_le
  · positivity
  · gcongr

/-- Elementary derivative of a reciprocal natural power. -/
theorem hasDerivAt_one_div_pow {r : ℕ} (hr : 0 < r) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ 1 / y ^ r)
      (-(r : ℝ) / x ^ (r + 1)) x := by
  have hinv := (hasDerivAt_id x).inv hx
  change HasDerivAt (fun y : ℝ ↦ y⁻¹) (-1 / x ^ 2) x at hinv
  have h := hinv.fun_pow r
  have hexp : r - 1 + 2 = r + 1 := by omega
  have hcoef :
      (r : ℝ) * x⁻¹ ^ (r - 1) * (-1 / x ^ 2) =
        -(r : ℝ) / x ^ (r + 1) := by
    rw [show x ^ (r + 1) = x ^ (r - 1) * x ^ 2 by
      rw [← pow_add, hexp]]
    field_simp [pow_ne_zero _ hx]
    rw [one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero (r - 1) hx)]
  have h' := h.congr_deriv hcoef
  simpa only [one_div, inv_pow] using h'

private theorem inv_cube_rpow_nat_div_three {r : ℕ} {x : ℝ} (hx : 0 < x) :
    (1 / x ^ 3) ^ ((r : ℝ) / 3) = 1 / x ^ r := by
  have hxi : 0 ≤ x⁻¹ := (inv_pos.mpr hx).le
  calc
    (1 / x ^ 3) ^ ((r : ℝ) / 3) =
        ((x⁻¹) ^ (3 : ℕ)) ^ ((r : ℝ) / 3) := by simp [one_div, inv_pow]
    _ = ((x⁻¹) ^ (3 : ℝ)) ^ ((r : ℝ) / 3) := by
      congr 1
      exact (Real.rpow_natCast (x⁻¹) 3).symm
    _ = (x⁻¹) ^ ((3 : ℝ) * ((r : ℝ) / 3)) := by
      rw [Real.rpow_mul hxi]
    _ = (x⁻¹) ^ (r : ℝ) := by
      congr 1
      ring
    _ = (x⁻¹) ^ r := by rw [Real.rpow_natCast]
    _ = 1 / x ^ r := by rw [inv_pow, one_div]

private theorem inv_cube_rpow_nat_sub_three {r : ℕ} (hr : 3 ≤ r)
    {x : ℝ} (hx : 0 < x) :
    (1 / x ^ 3) ^ ((r : ℝ) / 3 - 1) = 1 / x ^ (r - 3) := by
  have hsub : ((r : ℝ) / 3 - 1) = ((r - 3 : ℕ) : ℝ) / 3 := by
    rw [Nat.cast_sub hr]
    push_cast
    ring
  rw [hsub, inv_cube_rpow_nat_div_three hx]

/-- The elementary power-difference comparison used to dominate every
higher cumulant by the cubic coefficient. -/
theorem reciprocal_power_difference_le_cubic {r : ℕ} (hr : 3 ≤ r)
    {a u v : ℝ} (ha : 0 < a) (hau : a ≤ u) (huv : u < v) :
    1 / u ^ r - 1 / v ^ r ≤
      ((r : ℝ) / 3) * (1 / a ^ (r - 3)) *
        (1 / u ^ 3 - 1 / v ^ 3) := by
  let q : ℝ := (r : ℝ) / 3
  let U : ℝ := 1 / u ^ 3
  let W : ℝ := 1 / v ^ 3
  let B : ℝ := 1 / a ^ 3
  have hu : 0 < u := ha.trans_le hau
  have hv : 0 < v := hu.trans huv
  have hq : 1 ≤ q := by
    dsimp [q]
    have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hWU : W < U := by
    dsimp [W, U]
    exact one_div_lt_one_div_of_lt (pow_pos hu 3) (by gcongr)
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hUB : U ≤ B := by
    dsimp [U, B]
    apply one_div_le_one_div_of_le (pow_pos ha 3)
    gcongr
  have hslope := (convexOn_rpow hq).slope_le_of_hasDerivAt
    (show W ∈ Set.Ici (0 : ℝ) from hW0)
    (show U ∈ Set.Ici (0 : ℝ) from hU0) hWU
    (Real.hasDerivAt_rpow_const (Or.inr hq))
  have hdiff0 : 0 < U - W := sub_pos.mpr hWU
  have hsecant : U ^ q - W ^ q ≤ q * U ^ (q - 1) * (U - W) := by
    rw [slope_def_field] at hslope
    exact (div_le_iff₀ hdiff0).mp (by
      convert hslope using 1)
  have hq0 : 0 ≤ q - 1 := sub_nonneg.mpr hq
  have hpow : U ^ (q - 1) ≤ B ^ (q - 1) :=
    Real.rpow_le_rpow hU0 hUB hq0
  have hnonneg : 0 ≤ U - W := hdiff0.le
  have hcoef : q * U ^ (q - 1) * (U - W) ≤
      q * B ^ (q - 1) * (U - W) := by
    gcongr
  calc
    1 / u ^ r - 1 / v ^ r = U ^ q - W ^ q := by
      dsimp [U, W, q]
      rw [inv_cube_rpow_nat_div_three hu,
        inv_cube_rpow_nat_div_three hv]
    _ ≤ q * U ^ (q - 1) * (U - W) := hsecant
    _ ≤ q * B ^ (q - 1) * (U - W) := hcoef
    _ = ((r : ℝ) / 3) * (1 / a ^ (r - 3)) *
        (1 / u ^ 3 - 1 / v ^ 3) := by
      dsimp [q, B, U, W]
      rw [inv_cube_rpow_nat_sub_three hr ha]

private theorem betaShapeA_mono_index {m i j : ℕ} (hij : i ≤ j) :
    betaShapeA m j ≤ betaShapeA m i := by
  unfold betaShapeA
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  linarith

/-- Summed reciprocal-power differences are dominated by the cubic
difference with the exact factor `r/3`. -/
theorem reciprocalPowerDifference_le_cubic {r m p j : ℕ}
    (hr : 3 ≤ r) (h : Admissible m p) (hj : j ∈ Finset.Icc 2 p) :
    reciprocalPowerDifference r (betaShapeA m j) (betaShapeTotal m) ≤
      ((r : ℝ) / 3) * (1 / (betaShapeA m p) ^ (r - 3)) *
        reciprocalPowerDifference 3 (betaShapeA m j) (betaShapeTotal m) := by
  have hjb := Finset.mem_Icc.mp hj
  have haj : 0 < betaShapeA m j :=
    betaShapeA_pos_of_le (le_trans hjb.2 h.2)
  have hap : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  have htotal : 0 < betaShapeTotal m := betaShapeTotal_pos h
  have hamin : betaShapeA m p ≤ betaShapeA m j :=
    betaShapeA_mono_index hjb.2
  have hlt : betaShapeA m j < betaShapeTotal m :=
    betaShapeA_lt_total hjb.1
  let c : ℝ := ((r : ℝ) / 3) * (1 / (betaShapeA m p) ^ (r - 3))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hleft := summable_reciprocalPowerDifference
    (r := r) (by omega : 1 < r) haj htotal
  have hright0 := summable_reciprocalPowerDifference
    (r := 3) (by norm_num : 1 < 3) haj htotal
  have hright : Summable (fun l : ℕ ↦ c *
      (1 / (betaShapeA m j + (l : ℝ)) ^ 3 -
        1 / (betaShapeTotal m + (l : ℝ)) ^ 3)) :=
    hright0.mul_left c
  unfold reciprocalPowerDifference
  calc
    (∑' l : ℕ, (1 / (betaShapeA m j + (l : ℝ)) ^ r -
        1 / (betaShapeTotal m + (l : ℝ)) ^ r)) ≤
        ∑' l : ℕ, c *
          (1 / (betaShapeA m j + (l : ℝ)) ^ 3 -
            1 / (betaShapeTotal m + (l : ℝ)) ^ 3) := by
      exact hleft.tsum_le_tsum (fun l ↦ by
        apply reciprocal_power_difference_le_cubic hr hap
        · have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
          linarith
        · linarith) hright
    _ = c * ∑' l : ℕ,
          (1 / (betaShapeA m j + (l : ℝ)) ^ 3 -
            1 / (betaShapeTotal m + (l : ℝ)) ^ 3) := by
      rw [← hright0.tsum_mul_left]
    _ = ((r : ℝ) / 3) * (1 / (betaShapeA m p) ^ (r - 3)) *
        ∑' l : ℕ, (1 / (betaShapeA m j + (l : ℝ)) ^ 3 -
          1 / (betaShapeTotal m + (l : ℝ)) ^ 3) := by rfl

/-- Exact all-order reciprocal-power coefficient majorant in finite
`(m,p)` form. -/
theorem nullCumulantMagnitudeSeries_le {r m p : ℕ} (hr : 3 ≤ r)
    (h : Admissible m p) :
    nullCumulantMagnitudeSeries r m p ≤
      (Nat.factorial r : ℝ) / 6 * nullASeries m p /
        (betaShapeA m p) ^ (r - 3) := by
  have hfactorial : (Nat.factorial r : ℝ) =
      (r : ℝ) * (Nat.factorial (r - 1) : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfac0 : 0 ≤ (Nat.factorial (r - 1) : ℝ) := by positivity
  let c : ℝ := ((r : ℝ) / 3) * (1 / betaShapeA m p ^ (r - 3))
  have hsum0 :
      (∑ j ∈ Finset.Icc 2 p,
        reciprocalPowerDifference r (betaShapeA m j) (betaShapeTotal m)) ≤
      ∑ j ∈ Finset.Icc 2 p, c *
        reciprocalPowerDifference 3 (betaShapeA m j) (betaShapeTotal m) :=
    Finset.sum_le_sum fun j hj ↦ by
      dsimp [c]
      exact
    reciprocalPowerDifference_le_cubic (r := r) hr h hj
  have hsum :
      (∑ j ∈ Finset.Icc 2 p,
        reciprocalPowerDifference r (betaShapeA m j) (betaShapeTotal m)) ≤
      c * ∑ j ∈ Finset.Icc 2 p,
        reciprocalPowerDifference 3 (betaShapeA m j) (betaShapeTotal m) := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 2 p, c *
          reciprocalPowerDifference 3 (betaShapeA m j) (betaShapeTotal m) := hsum0
      _ = c * ∑ j ∈ Finset.Icc 2 p,
          reciprocalPowerDifference 3 (betaShapeA m j) (betaShapeTotal m) := by
        rw [Finset.mul_sum]
  have hmul := mul_le_mul_of_nonneg_left hsum hfac0
  have hA : nullASeries m p =
      2 * ∑ x ∈ Finset.Icc 2 p,
        reciprocalPowerDifference 3 (betaShapeA m x) (betaShapeTotal m) := by
    rw [nullASeries_eq_doubleSeries h]
    unfold reciprocalPowerDifference
    rw [Finset.mul_sum]
  rw [hA]
  unfold nullCumulantMagnitudeSeries
  rw [hfactorial]
  calc
    (Nat.factorial (r - 1) : ℝ) *
        ∑ x ∈ Finset.Icc 2 p,
          reciprocalPowerDifference r (betaShapeA m x) (betaShapeTotal m) ≤
      (Nat.factorial (r - 1) : ℝ) *
        (c * ∑ x ∈ Finset.Icc 2 p,
          reciprocalPowerDifference 3 (betaShapeA m x) (betaShapeTotal m)) := hmul
    _ = ((r : ℝ) * (Nat.factorial (r - 1) : ℝ)) / 6 *
          (2 * ∑ x ∈ Finset.Icc 2 p,
              reciprocalPowerDifference 3 (betaShapeA m x) (betaShapeTotal m)) /
          betaShapeA m p ^ (r - 3) := by
      dsimp [c]
      ring

/-- Natural-cube and real-power normalizations of `V^(3/2)` agree in the
admissible range. -/
theorem nullVSeries_rpow_three_halves {m p : ℕ} (h : Admissible m p) :
    nullVSeries m p ^ (3 / 2 : ℝ) =
      (Real.sqrt (nullVSeries m p)) ^ (3 : ℕ) := by
  have hV : 0 ≤ nullVSeries m p := (nullVSeries_pos h).le
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hV]
  norm_num

/-- Standardized all-order coefficient bound with the exact analytic scale.
Once the separate CGF-derivative bridge is supplied, this is the finite
inequality used to sum the local characteristic-function Taylor remainder. -/
theorem nullStandardizedCumulantMagnitudeSeries_le {r m p : ℕ}
    (hr : 3 ≤ r) (h : Admissible m p) :
    nullStandardizedCumulantMagnitudeSeries r m p ≤
      (Nat.factorial r : ℝ) / 6 * nullLambdaSeries m p /
        (nullAnalyticScale m p) ^ (r - 3) := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hsqrt : 0 < Real.sqrt (nullVSeries m p) := Real.sqrt_pos.2 hV
  have ha : 0 < betaShapeA m p := betaShapeA_pos_of_le h.2
  have hraw := nullCumulantMagnitudeSeries_le (r := r) hr h
  have hdiv := div_le_div_of_nonneg_right hraw
    (pow_nonneg hsqrt.le r)
  unfold nullStandardizedCumulantMagnitudeSeries
  refine hdiv.trans_eq ?_
  unfold nullLambdaSeries nullAnalyticScale
  rw [nullVSeries_rpow_three_halves h, mul_pow]
  have hsqrt_ne : Real.sqrt (nullVSeries m p) ≠ 0 := hsqrt.ne'
  have ha_ne : betaShapeA m p ≠ 0 := ha.ne'
  have hexp : 3 + (r - 3) = r := by omega
  field_simp [pow_ne_zero _ hsqrt_ne, pow_ne_zero _ ha_ne]
  rw [mul_assoc, ← pow_add, hexp]


/-- The order-two all-order coefficient is exactly `V_{m,p}`. -/
theorem nullCumulantMagnitudeSeries_two {m p : ℕ} (h : Admissible m p) :
    nullCumulantMagnitudeSeries 2 m p = nullVSeries m p := by
  rw [nullVSeries_eq_doubleSeries h]
  unfold nullCumulantMagnitudeSeries reciprocalPowerDifference
  norm_num

/-- The order-three all-order coefficient is exactly `A_{m,p}`. -/
theorem nullCumulantMagnitudeSeries_three {m p : ℕ} (h : Admissible m p) :
    nullCumulantMagnitudeSeries 3 m p = nullASeries m p := by
  rw [nullASeries_eq_doubleSeries h]
  unfold nullCumulantMagnitudeSeries reciprocalPowerDifference
  norm_num
  rw [Finset.mul_sum]

end

end LogdetLean
