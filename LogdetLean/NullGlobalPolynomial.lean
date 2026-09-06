import LogdetLean.NullCharacteristicTails
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
/-!
# Global polynomial damping for the null log-determinant law

The argument is a direct formalization of the positive Gamma-product proof
used in the accompanying manuscript.  Two elementary logarithmic inequalities
replace all differentiation under an infinite sum.  The result includes the
hard edge `m = p` because every Beta shape remains strictly positive there.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

noncomputable section

set_option linter.style.haveILetI false

/-- The decreasing logarithmic kernel in the Gamma modulus product. -/
def gammaModulusLogKernel (u x : ℝ) : ℝ :=
  Real.log (1 + u ^ 2 / x ^ 2)

/-- The positive comparison kernel used in the integral-test argument. -/
def gammaModulusSlopeKernel (u x : ℝ) : ℝ :=
  2 * u ^ 2 / (x * (x ^ 2 + u ^ 2))

theorem log_ratio_lower_symmetric {q : ℝ} (hq : 1 ≤ q) :
    2 * (q - 1) / (q + 1) ≤ Real.log q := by
  have hr : 0 ≤ q - 1 := sub_nonneg.mpr hq
  have h := Real.le_log_one_add_of_nonneg hr
  calc
    2 * (q - 1) / (q + 1) = 2 * (q - 1) / ((q - 1) + 2) := by ring
    _ ≤ Real.log (1 + (q - 1)) := h
    _ = Real.log q := by congr 1; ring

theorem log_ratio_upper_symmetric {q : ℝ} (hq : 1 ≤ q) :
    Real.log q ≤ (q - q⁻¹) / 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hq)
  rw [Real.sinh_log hq0] at h
  exact h

/-- A secant of the logarithmic kernel dominates its right-endpoint slope.
This is proved algebraically from `2(q-1)/(q+1) <= log q`. -/
theorem slope_le_gammaModulusLogKernel_sub
    {u x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (y - x) * gammaModulusSlopeKernel u y ≤
      gammaModulusLogKernel u x - gammaModulusLogKernel u y := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  have hy : 0 < y := hx.trans_le hxy
  let q := (1 + u ^ 2 / x ^ 2) / (1 + u ^ 2 / y ^ 2)
  have hq1 : 1 ≤ q := by
    dsimp [q]
    apply (le_div_iff₀ (by positivity)).2
    have : u ^ 2 / y ^ 2 ≤ u ^ 2 / x ^ 2 := by gcongr
    linarith
  have hlog := log_ratio_lower_symmetric hq1
  have hlogq : Real.log q =
      gammaModulusLogKernel u x - gammaModulusLogKernel u y := by
    dsimp [q, gammaModulusLogKernel]
    rw [Real.log_div (by positivity) (by positivity)]
  rw [hlogq] at hlog
  apply (show (y - x) * gammaModulusSlopeKernel u y ≤
      2 * (q - 1) / (q + 1) from ?_).trans hlog
  dsimp [q, gammaModulusSlopeKernel]
  field_simp [hx.ne', hy.ne']
  have haux : 0 ≤ (y - x) ^ 2 *
      (u ^ 2 * x + 2 * x * y ^ 2 + y ^ 3) := by positivity
  nlinarith

/-- On `[1, infinity)`, one unit decrement of the logarithmic kernel is at
most its left-endpoint slope. -/
theorem gammaModulusLogKernel_sub_succ_le_slope
    {u x : ℝ} (hx : 1 ≤ x) :
    gammaModulusLogKernel u x - gammaModulusLogKernel u (x + 1) ≤
      gammaModulusSlopeKernel u x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxp : 0 < x + 1 := by linarith
  let q := (1 + u ^ 2 / x ^ 2) / (1 + u ^ 2 / (x + 1) ^ 2)
  have hq1 : 1 ≤ q := by
    dsimp [q]
    apply (le_div_iff₀ (by positivity)).2
    have : u ^ 2 / (x + 1) ^ 2 ≤ u ^ 2 / x ^ 2 := by
      gcongr
      linarith
    linarith
  have hlog := log_ratio_upper_symmetric hq1
  have hlogq : Real.log q = gammaModulusLogKernel u x -
      gammaModulusLogKernel u (x + 1) := by
    dsimp [q, gammaModulusLogKernel]
    rw [Real.log_div (by positivity) (by positivity)]
  rw [hlogq] at hlog
  apply hlog.trans
  dsimp [q, gammaModulusSlopeKernel]
  field_simp [hx0.ne', hxp.ne']
  have hcoef : 0 ≤ 2 * x ^ 2 - 1 := by nlinarith [sq_nonneg x]
  have haux : 0 ≤ u ^ 2 *
      (u ^ 2 * (2 * x ^ 2 - 1) +
        6 * x ^ 4 + 16 * x ^ 3 + 14 * x ^ 2 + 4 * x) := by positivity
  nlinarith

theorem gammaModulusLogKernel_tendsto_zero {u M : ℝ} :
    Tendsto (fun n : ℕ => gammaModulusLogKernel u (M + (n : ℝ)))
      atTop (nhds 0) := by
  have hbase : Tendsto (fun n : ℕ => M + (n : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => (M + (n : ℝ)) ^ 2) atTop atTop := by
    simpa [pow_two] using hbase.atTop_mul_atTop₀ hbase
  have hdiv : Tendsto (fun n : ℕ => u ^ 2 / (M + (n : ℝ)) ^ 2)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hsq
  have hadd : Tendsto (fun n : ℕ => 1 + u ^ 2 / (M + (n : ℝ)) ^ 2)
      atTop (nhds 1) := by simpa using tendsto_const_nhds.add hdiv
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hadd
  simpa [gammaModulusLogKernel, Function.comp_def] using hlog

theorem hasSum_gammaModulusLogKernel_telescope
    {u M : ℝ} (hM : 1 ≤ M) :
    HasSum (fun l : ℕ => gammaModulusLogKernel u (M + (l : ℝ)) -
      gammaModulusLogKernel u (M + ((l + 1 : ℕ) : ℝ)))
      (gammaModulusLogKernel u M) := by
  have hnonneg : ∀ l : ℕ, 0 ≤ gammaModulusLogKernel u (M + (l : ℝ)) -
      gammaModulusLogKernel u (M + ((l + 1 : ℕ) : ℝ)) := by
    intro l
    apply sub_nonneg.mpr
    unfold gammaModulusLogKernel
    apply Real.log_le_log (by positivity)
    have hbase : 0 < M + (l : ℝ) := by positivity
    have hle : M + (l : ℝ) ≤ M + ((l + 1 : ℕ) : ℝ) := by norm_num
    have : u ^ 2 / (M + ((l + 1 : ℕ) : ℝ)) ^ 2 ≤
        u ^ 2 / (M + (l : ℝ)) ^ 2 := by gcongr
    linarith
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
  rw [show (fun n : ℕ => ∑ i ∈ Finset.range n,
      (gammaModulusLogKernel u (M + (i : ℝ)) -
        gammaModulusLogKernel u (M + ((i + 1 : ℕ) : ℝ)))) =
      (fun n : ℕ => gammaModulusLogKernel u M -
        gammaModulusLogKernel u (M + (n : ℝ))) by
        funext n
        rw [Finset.sum_range_sub']
        norm_num]
  simpa using tendsto_const_nhds.sub gammaModulusLogKernel_tendsto_zero

theorem summable_gammaModulusSlopeKernel
    {u M : ℝ} (hM : 1 ≤ M) :
    Summable (fun l : ℕ => gammaModulusSlopeKernel u (M + (l : ℝ))) := by
  unfold gammaModulusSlopeKernel
  have hs : Summable (fun l : ℕ => 2 * u ^ 2 /
      (M + (l : ℝ)) ^ 3) := by
    simpa [div_eq_mul_inv] using
      (summable_shifted_reciprocal_pow (x := M) (zero_lt_one.trans_le hM)
        (r := 3) (by norm_num)).mul_left (2 * u ^ 2)
  apply Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hs
  have hMl : 0 < M + (l : ℝ) := by positivity
  have hden : (M + (l : ℝ)) ^ 3 ≤
      (M + (l : ℝ)) * ((M + (l : ℝ)) ^ 2 + u ^ 2) := by
    nlinarith [sq_nonneg u]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- Discrete integral comparison: the slope series dominates the logarithmic
kernel. -/
theorem slopeSeries_dominates_gammaModulusLogKernel
    {u M : ℝ} (hM : 1 ≤ M) :
    gammaModulusLogKernel u M ≤
      ∑' l : ℕ, gammaModulusSlopeKernel u (M + (l : ℝ)) := by
  have htel := hasSum_gammaModulusLogKernel_telescope (u := u) hM
  have hslope := summable_gammaModulusSlopeKernel (u := u) hM
  rw [← htel.tsum_eq]
  exact htel.summable.tsum_le_tsum (fun l => by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
      (gammaModulusLogKernel_sub_succ_le_slope (u := u)
        (show 1 ≤ M + (l : ℝ) by
          exact hM.trans (le_add_of_nonneg_right (Nat.cast_nonneg l))))) hslope

/-- Global logarithmic loss for one Beta factor. -/
theorem betaModulusLogLoss_lower_global
    {a M u : ℝ} (ha : 0 < a) (haM : a ≤ M) (hM : 1 ≤ M) :
    (M - a) * gammaModulusLogKernel u M ≤ betaModulusLogLoss a M u := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hgap : 0 ≤ M - a := sub_nonneg.mpr haM
  have hslope := summable_gammaModulusSlopeKernel (u := u) hM
  have hleft := hslope.mul_left (M - a)
  have hright := summable_betaModulusLogLoss_terms ha hM0 u
  have hterm : ∀ l : ℕ,
      (M - a) * gammaModulusSlopeKernel u (M + (l : ℝ)) ≤
        Real.log (1 + u ^ 2 / (a + (l : ℝ)) ^ 2) -
          Real.log (1 + u ^ 2 / (M + (l : ℝ)) ^ 2) := by
    intro l
    have hal : 0 < a + (l : ℝ) := by positivity
    have hale : a + (l : ℝ) ≤ M + (l : ℝ) := by linarith
    simpa [gammaModulusLogKernel, add_sub_add_right_eq_sub] using
      slope_le_gammaModulusLogKernel_sub (u := u) hal hale
  unfold betaModulusLogLoss
  calc
    (M - a) * gammaModulusLogKernel u M ≤
        (M - a) * ∑' l : ℕ,
          gammaModulusSlopeKernel u (M + (l : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (slopeSeries_dominates_gammaModulusLogKernel (u := u) hM) hgap
    _ = ∑' l : ℕ, (M - a) *
          gammaModulusSlopeKernel u (M + (l : ℝ)) := by rw [tsum_mul_left]
    _ ≤ ∑' l : ℕ,
        (Real.log (1 + u ^ 2 / (a + (l : ℝ)) ^ 2) -
          Real.log (1 + u ^ 2 / (M + (l : ℝ)) ^ 2)) :=
      hleft.tsum_le_tsum hterm hright

theorem sum_Icc_two_cast_sub_one_global (p : ℕ) (hp : 2 ≤ p) :
    (∑ j ∈ Finset.Icc 2 p, ((j : ℝ) - 1)) =
      (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 + k := ⟨p - 2, by omega⟩
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 2 + (k + 1) = (2 + k) + 1 by omega]
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih (by omega)]
      push_cast
      ring

theorem sum_betaShapeTotal_sub_betaShapeA
    {m p : ℕ} (hp : 2 ≤ p) :
    (∑ j ∈ Finset.Icc 2 p,
      (betaShapeTotal m - betaShapeA m j)) =
        (p : ℝ) * ((p : ℝ) - 1) / 4 := by
  calc
    (∑ j ∈ Finset.Icc 2 p,
      (betaShapeTotal m - betaShapeA m j)) =
        ∑ j ∈ Finset.Icc 2 p, (((j : ℝ) - 1) / 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold betaShapeTotal betaShapeA
      ring
    _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 2 p, ((j : ℝ) - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (p : ℝ) * ((p : ℝ) - 1) / 4 := by
      rw [sum_Icc_two_cast_sub_one_global p hp]
      ring

/-- The complete raw logarithmic loss has a global dimension-dependent lower
bound. -/
theorem nullRawModulusLogLoss_lower_global
    {m p : ℕ} (h : Admissible m p) (u : ℝ) :
    ((p : ℝ) * ((p : ℝ) - 1) / 4) *
        Real.log (1 + (u / betaShapeTotal m) ^ 2) ≤
      nullRawModulusLogLoss m p u := by
  have hm2 : 2 ≤ m := h.1.trans h.2
  have hMone : 1 ≤ betaShapeTotal m := by
    unfold betaShapeTotal
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  unfold nullRawModulusLogLoss
  have hsum := Finset.sum_le_sum (s := Finset.Icc 2 p) (fun j hj =>
    betaModulusLogLoss_lower_global
      (betaShapeA_pos_of_mem_Icc h.2 hj)
      (betaShapeA_lt_total (Finset.mem_Icc.mp hj).1).le hMone (u := u))
  calc
    ((p : ℝ) * ((p : ℝ) - 1) / 4) *
        Real.log (1 + (u / betaShapeTotal m) ^ 2) =
      (∑ j ∈ Finset.Icc 2 p,
        (betaShapeTotal m - betaShapeA m j)) *
          gammaModulusLogKernel u (betaShapeTotal m) := by
      rw [sum_betaShapeTotal_sub_betaShapeA h.1]
      unfold gammaModulusLogKernel
      congr 3
      field_simp [ne_of_gt (zero_lt_one.trans_le hMone)]
    _ = ∑ j ∈ Finset.Icc 2 p,
        (betaShapeTotal m - betaShapeA m j) *
          gammaModulusLogKernel u (betaShapeTotal m) := by rw [Finset.sum_mul]
    _ ≤ ∑ j ∈ Finset.Icc 2 p,
        betaModulusLogLoss (betaShapeA m j) (betaShapeTotal m) u := hsum

/-- Global polynomial modulus bound at raw frequency.  The exponent is the
exact `p(p-1)/8` from the Gamma product argument. -/
theorem norm_charFun_centeredLogBetaSumLaw_le_polynomial_global
    {m p : ℕ} (h : Admissible m p) (u : ℝ) :
    ‖charFun (centeredLogBetaSumLaw m p) u‖ ≤
      (1 + (u / betaShapeTotal m) ^ 2) ^
        (-(p : ℝ) * ((p : ℝ) - 1) / 8) := by
  have hbase : 0 < 1 + (u / betaShapeTotal m) ^ 2 := by positivity
  have hloss := nullRawModulusLogLoss_lower_global h u
  have hsq := norm_charFun_centeredLogBetaSumLaw_sq_eq_nullRawModulusSqEulerProduct
    h.2 u
  rw [nullRawModulusSqEulerProduct_eq_exp_neg_logLoss h u] at hsq
  rw [Real.rpow_def_of_pos hbase]
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [hsq, pow_two, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq :
      Real.log (1 + (u / betaShapeTotal m) ^ 2) *
          (-(p : ℝ) * ((p : ℝ) - 1) / 8) +
        Real.log (1 + (u / betaShapeTotal m) ^ 2) *
          (-(p : ℝ) * ((p : ℝ) - 1) / 8) =
      -(((p : ℝ) * ((p : ℝ) - 1) / 4) *
        Real.log (1 + (u / betaShapeTotal m) ^ 2)) := by ring
  rw [heq]
  exact neg_le_neg hloss

/-- Global polynomial modulus bound for the actual standardized null law. -/
theorem norm_charFun_standardizedNullLaw_le_polynomial_global
    {m p : ℕ} (h : Admissible m p) (t : ℝ) :
    ‖charFun (standardizedNullLaw m p) t‖ ≤
      (1 + (t /
        (betaShapeTotal m * Real.sqrt (nullVSeries m p))) ^ 2) ^
          (-(p : ℝ) * ((p : ℝ) - 1) / 8) := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hs : 0 < Real.sqrt (nullVSeries m p) := Real.sqrt_pos.2 hV
  rw [charFun_standardizedNullLaw_eq_standardizedGammaProduct h.2]
  unfold standardizedLogBetaCharacteristicProduct
  rw [nullVariance_eq_nullVSeries h.2]
  rw [← charFun_centeredLogBetaSumLaw_eq_centeredGammaProduct h.2]
  have hraw := norm_charFun_centeredLogBetaSumLaw_le_polynomial_global h
    (t / Real.sqrt (nullVSeries m p))
  convert hraw using 1
  congr 3
  field_simp [hs.ne']

/-- The global polynomial majorant is integrable on the whole real line.
This is the explicit high-frequency integrability input needed by Fourier
inversion. -/
theorem integrable_standardizedNullPolynomialMajorant
    {m p : ℕ} (h : Admissible m p) (hp3 : 3 ≤ p) :
    Integrable (fun t : ℝ =>
      (1 + (t /
        (betaShapeTotal m * Real.sqrt (nullVSeries m p))) ^ 2) ^
          (-(p : ℝ) * ((p : ℝ) - 1) / 8)) := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hs : 0 < betaShapeTotal m * Real.sqrt (nullVSeries m p) :=
    mul_pos (betaShapeTotal_pos h) (Real.sqrt_pos.2 hV)
  let r : ℝ := (p : ℝ) * ((p : ℝ) - 1) / 4
  have hr : (Module.finrank ℝ ℝ : ℝ) < r := by
    rw [Module.finrank_self]
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    dsimp [r]
    nlinarith
  have hbase : Integrable (fun x : ℝ =>
      ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2)) :=
    integrable_rpow_neg_one_add_norm_sq hr
  have hscaled := hbase.comp_div hs.ne'
  apply hscaled.congr
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hs]
  have hsq : (|t| / (betaShapeTotal m * Real.sqrt (nullVSeries m p))) ^ 2 =
      (t / (betaShapeTotal m * Real.sqrt (nullVSeries m p))) ^ 2 := by
    simp only [div_pow, sq_abs]
  rw [hsq]
  rw [show -r / 2 = -(p : ℝ) * ((p : ℝ) - 1) / 8 by
    dsimp [r]
    ring]

/-- Consequently the actual standardized null characteristic function is
integrable; this statement is uniform in the sense that it has no spectral-gap
assumption and includes `m=p`. -/
theorem integrable_charFun_standardizedNullLaw
    {m p : ℕ} (h : Admissible m p) (hp3 : 3 ≤ p) :
    Integrable (fun t : ℝ => charFun (standardizedNullLaw m p) t) := by
  letI : IsProbabilityMeasure (standardizedNullLaw m p) :=
    isProbabilityMeasure_standardizedNullLaw h.2
  have hmajor := integrable_standardizedNullPolynomialMajorant h hp3
  apply hmajor.mono'
  · exact (continuous_charFun (μ := standardizedNullLaw m p)).aestronglyMeasurable
  · filter_upwards with t
    simpa only [norm_norm] using
      norm_charFun_standardizedNullLaw_le_polynomial_global h t

end

end LogdetLean
