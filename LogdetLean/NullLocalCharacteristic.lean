import LogdetLean.StandardizedCumulantBridge
import LogdetLean.ScaleSeparation
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
/-!
# A quantitative local characteristic exponent for the null model

This file is the first Fourier milestone shared by the qualitative null CLT
and the sharp Berry--Esseen project.  It constructs, without choosing a
branch of the complex logarithm, the Taylor series of the exact standardized
CGF and proves that its complex exponential is the characteristic function
on the full natural disk

`|t| < Delta_{m,p} = betaShapeA m p * sqrt (V_{m,p})`.

The tail after the Gaussian quadratic term satisfies the explicit finite
bound

`|R(t)| <= lambda * |t|^3 / (6 * (1 - |t| / Delta))`.

The proof uses mathlib's holomorphic complex MGF and identity theorem.  Thus
the displayed exponent is tied to the actual probability law; it is not a
formal cumulant series introduced as an axiom.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal Topology ComplexConjugate

noncomputable section

set_option linter.style.haveILetI false

/-! ## The natural complex-MGF disk -/

/-- Every real exponential moment of the standardized null law is finite to
the right of its first singularity `-Delta`. -/
theorem integrable_exp_mul_id_standardizedNullLaw_of_neg_analyticScale_lt
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : -nullAnalyticScale m p < t) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x))
      (standardizedNullLaw m p) := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  have hs : 0 < Real.sqrt (nullVSeries m p) := Real.sqrt_pos.2 hV
  let c : ℝ := t / Real.sqrt (nullVSeries m p)
  have hdom : NullMgfDomain m p c := by
    intro j hj
    have hjp : j ≤ p := (Finset.mem_Icc.mp hj).2
    have hmono : betaShapeA m p ≤ betaShapeA m j := by
      unfold betaShapeA
      have hjpR : (j : ℝ) ≤ (p : ℝ) := by exact_mod_cast hjp
      linarith
    have hbase : 0 < betaShapeA m p + c := by
      dsimp [c]
      unfold nullAnalyticScale at ht
      rw [show betaShapeA m p + t / Real.sqrt (nullVSeries m p) =
          (betaShapeA m p * Real.sqrt (nullVSeries m p) + t) /
            Real.sqrt (nullVSeries m p) by
        field_simp [hs.ne']]
      exact div_pos (by linarith) hs
    linarith
  have hraw : Integrable (fun x : ℝ ↦ Real.exp (c * x))
      (logBetaSumLaw m p) :=
    (integrable_exp_and_mgf_logBetaSumLaw h.2 hdom).1
  unfold standardizedNullLaw
  rw [nullVariance_eq_nullVSeries h.2]
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  let C : ℝ := Real.exp (-c * nullCenter m p)
  have hscaled : Integrable (fun x : ℝ ↦ C * Real.exp (c * x))
      (logBetaSumLaw m p) := hraw.const_mul C
  refine hscaled.congr ?_
  filter_upwards with x
  dsimp [C, c]
  rw [← Real.exp_add]
  congr 1
  field_simp [hs.ne']
  ring

/-- The open half-line to the right of `-Delta` is contained in the exact
real MGF domain of the standardized law. -/
theorem Ioi_neg_analyticScale_subset_integrableExpSet_standardizedNullLaw
    {m p : ℕ} (h : Admissible m p) :
    Ioi (-nullAnalyticScale m p) ⊆
      integrableExpSet id (standardizedNullLaw m p) := by
  intro t ht
  exact integrable_exp_mul_id_standardizedNullLaw_of_neg_analyticScale_lt
    h ht

/-- Every point of the complex disk `|z| < Delta` has real part in the
interior of the exact real MGF domain. -/
theorem re_mem_interior_integrableExpSet_standardizedNullLaw_of_norm_lt
    {m p : ℕ} (h : Admissible m p) {z : ℂ}
    (hz : ‖z‖ < nullAnalyticScale m p) :
    z.re ∈ interior (integrableExpSet id (standardizedNullLaw m p)) := by
  have hre : -nullAnalyticScale m p < z.re := by
    have hle : -‖z‖ ≤ z.re := neg_le_of_abs_le (Complex.abs_re_le_norm z)
    linarith
  exact interior_maximal
    (Ioi_neg_analyticScale_subset_integrableExpSet_standardizedNullLaw h)
    isOpen_Ioi hre

/-- The exact complex MGF of the standardized null law is holomorphic on the
full disk of radius `Delta`. -/
theorem analyticOnNhd_complexMGF_standardizedNullLaw_on_analyticDisk
    {m p : ℕ} (h : Admissible m p) :
    AnalyticOnNhd ℂ (complexMGF id (standardizedNullLaw m p))
      (Metric.ball 0 (nullAnalyticScale m p)) := by
  apply analyticOnNhd_complexMGF.mono
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact re_mem_interior_integrableExpSet_standardizedNullLaw_of_norm_lt h hz

/-! ## Exact Taylor coefficients -/

/-- The Taylor coefficient of the exact real standardized CGF. -/
def nullStandardizedCgfTaylorCoeff (r m p : ℕ) : ℝ :=
  iteratedDeriv r (cgf id (standardizedNullLaw m p)) 0 /
    (Nat.factorial r : ℝ)

/-- The same coefficients, regarded as a complex formal multilinear series. -/
def nullComplexCgfTaylorSeries (m p : ℕ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun r ↦ (nullStandardizedCgfTaylorCoeff r m p : ℂ))

/-- Its sum is the branch-free local logarithmic characteristic exponent. -/
def nullComplexCgfTaylorSum (m p : ℕ) (z : ℂ) : ℂ :=
  (nullComplexCgfTaylorSeries m p).sum z

/-- Every derivative of order at least two of the standardized law's CGF is
the signed standardized reciprocal-power coefficient. -/
theorem iteratedDeriv_cgf_standardizedNullLaw_eq_sign_mul_magnitude
    {r m p : ℕ} (hr : 2 ≤ r) (h : Admissible m p) :
    iteratedDeriv r (cgf id (standardizedNullLaw m p)) 0 =
      (-1 : ℝ) ^ r *
        nullStandardizedCumulantMagnitudeSeries r m p := by
  have hs := nullStandardizedSampleCumulant_eq_sign_mul_magnitude hr h
  unfold nullStandardizedSampleCumulant at hs
  rw [cgf_Z0mpStatistic_eq_standardizedNullLaw h.2] at hs
  exact hs

/-- The standardized reciprocal-power coefficient of order two is one. -/
theorem nullStandardizedCumulantMagnitudeSeries_two
    {m p : ℕ} (h : Admissible m p) :
    nullStandardizedCumulantMagnitudeSeries 2 m p = 1 := by
  have hV : 0 < nullVSeries m p := nullVSeries_pos h
  unfold nullStandardizedCumulantMagnitudeSeries
  rw [nullCumulantMagnitudeSeries_two h, sq_sqrt hV.le]
  exact div_self hV.ne'

/-- The quadratic coefficient of the exact standardized CGF is `1/2`. -/
theorem nullStandardizedCgfTaylorCoeff_two
    {m p : ℕ} (h : Admissible m p) :
    nullStandardizedCgfTaylorCoeff 2 m p = 1 / 2 := by
  unfold nullStandardizedCgfTaylorCoeff
  rw [iteratedDeriv_cgf_standardizedNullLaw_eq_sign_mul_magnitude
    (by norm_num) h, nullStandardizedCumulantMagnitudeSeries_two h]
  norm_num

/-- From order three onward, the coefficient has the expected alternating
sign and exact factorial normalization. -/
theorem nullStandardizedCgfTaylorCoeff_eq_sign_mul_magnitude_div_factorial
    {r m p : ℕ} (hr : 3 ≤ r) (h : Admissible m p) :
    nullStandardizedCgfTaylorCoeff r m p =
      (-1 : ℝ) ^ r *
        nullStandardizedCumulantMagnitudeSeries r m p /
          (Nat.factorial r : ℝ) := by
  unfold nullStandardizedCgfTaylorCoeff
  rw [iteratedDeriv_cgf_standardizedNullLaw_eq_sign_mul_magnitude
    (by omega) h]

/-- The standardized law is centered. -/
theorem integral_id_standardizedNullLaw_eq_zero
    {m p : ℕ} (h : Admissible m p) :
    ∫ x : ℝ, x ∂standardizedNullLaw m p = 0 := by
  letI : IsProbabilityMeasure (logBetaSumLaw m p) :=
    isProbabilityMeasure_logBetaSumLaw h.2
  have hL3 : MemLp (fun x : ℝ ↦ x) 3 (logBetaSumLaw m p) :=
    memLp_id_logBetaSumLaw h.2
  have hL1 : Integrable (fun x : ℝ ↦ x) (logBetaSumLaw m p) :=
    hL3.integrable (by norm_num)
  have hs : Real.sqrt (nullVariance m p) ≠ 0 :=
    by
      rw [nullVariance_eq_nullVSeries h.2]
      exact (sqrt_nullVSeries_pos h).ne'
  unfold standardizedNullLaw
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  rw [integral_div, integral_sub hL1 (integrable_const (nullCenter m p)),
    integral_const]
  simp [nullCenter]

/-- The exact standardized CGF has zero constant Taylor coefficient. -/
theorem nullStandardizedCgfTaylorCoeff_zero
    {m p : ℕ} (h : Admissible m p) :
    nullStandardizedCgfTaylorCoeff 0 m p = 0 := by
  letI : IsProbabilityMeasure (standardizedNullLaw m p) :=
    isProbabilityMeasure_standardizedNullLaw h.2
  simp [nullStandardizedCgfTaylorCoeff, cgf, mgf]

/-- The exact standardized CGF has zero linear Taylor coefficient. -/
theorem nullStandardizedCgfTaylorCoeff_one
    {m p : ℕ} (h : Admissible m p) :
    nullStandardizedCgfTaylorCoeff 1 m p = 0 := by
  letI : IsProbabilityMeasure (standardizedNullLaw m p) :=
    isProbabilityMeasure_standardizedNullLaw h.2
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hzero : (0 : ℝ) ∈
      interior (integrableExpSet id (standardizedNullLaw m p)) := by
    have hz : ‖(0 : ℂ)‖ < nullAnalyticScale m p := by simpa
    simpa using
      (re_mem_interior_integrableExpSet_standardizedNullLaw_of_norm_lt h hz)
  unfold nullStandardizedCgfTaylorCoeff
  rw [iteratedDeriv_one, deriv_cgf_zero hzero]
  change (∫ x : ℝ, x ∂standardizedNullLaw m p) /
      (standardizedNullLaw m p).real univ / (Nat.factorial 1 : ℝ) = 0
  rw [integral_id_standardizedNullLaw_eq_zero h]
  simp

/-- Every positive-order reciprocal-power magnitude is nonnegative. -/
theorem nullCumulantMagnitudeSeries_nonneg
    {r m p : ℕ} (hr : 0 < r) (h : Admissible m p) :
    0 ≤ nullCumulantMagnitudeSeries r m p := by
  unfold nullCumulantMagnitudeSeries
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact reciprocalPowerDifference_nonneg hr
    (betaShapeA_pos_of_le (hj.2.trans h.2))
    (le_of_lt (betaShapeA_lt_total hj.1))

/-- The corresponding standardized magnitude is nonnegative. -/
theorem nullStandardizedCumulantMagnitudeSeries_nonneg
    {r m p : ℕ} (hr : 0 < r) (h : Admissible m p) :
    0 ≤ nullStandardizedCumulantMagnitudeSeries r m p := by
  unfold nullStandardizedCumulantMagnitudeSeries
  exact div_nonneg (nullCumulantMagnitudeSeries_nonneg hr h) (by positivity)

/-- Coefficient form of the all-order analytic-scale majorant. -/
theorem abs_nullStandardizedCgfTaylorCoeff_le
    {r m p : ℕ} (hr : 3 ≤ r) (h : Admissible m p) :
    |nullStandardizedCgfTaylorCoeff r m p| ≤
      nullLambdaSeries m p /
        (6 * (nullAnalyticScale m p) ^ (r - 3)) := by
  have hmag : 0 ≤ nullStandardizedCumulantMagnitudeSeries r m p :=
    nullStandardizedCumulantMagnitudeSeries_nonneg (by omega) h
  have hfac : 0 < (Nat.factorial r : ℝ) := by positivity
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hmajor := nullStandardizedCumulantMagnitudeSeries_le hr h
  rw [nullStandardizedCgfTaylorCoeff_eq_sign_mul_magnitude_div_factorial
    hr h]
  have habs :
      |(-1 : ℝ) ^ r *
          nullStandardizedCumulantMagnitudeSeries r m p /
            (Nat.factorial r : ℝ)| =
        nullStandardizedCumulantMagnitudeSeries r m p /
          (Nat.factorial r : ℝ) := by
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg hmag, abs_of_pos hfac]
    ring
  rw [habs]
  calc
    nullStandardizedCumulantMagnitudeSeries r m p /
          (Nat.factorial r : ℝ) ≤
        ((Nat.factorial r : ℝ) / 6 * nullLambdaSeries m p /
          nullAnalyticScale m p ^ (r - 3)) /
            (Nat.factorial r : ℝ) :=
      div_le_div_of_nonneg_right hmajor hfac.le
    _ = nullLambdaSeries m p /
        (6 * nullAnalyticScale m p ^ (r - 3)) := by
      field_simp [hfac.ne', hDelta.ne']

/-! ## Convergence and the geometric tail -/

/-- The Taylor series has radius at least the exact analytic scale
`Delta_{m,p}`. -/
theorem nullComplexCgfTaylorSeries_analyticScale_le_radius
    {m p : ℕ} (h : Admissible m p) :
    ((Real.toNNReal (nullAnalyticScale m p) : ℝ≥0) : ℝ≥0∞) ≤
      (nullComplexCgfTaylorSeries m p).radius := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  let C : ℝ := 1 + nullAnalyticScale m p ^ 2 +
    nullLambdaSeries m p * nullAnalyticScale m p ^ 3
  apply (nullComplexCgfTaylorSeries m p).le_radius_of_bound C
  intro r
  rw [nullComplexCgfTaylorSeries,
    FormalMultilinearSeries.ofScalars_norm]
  simp only [Real.coe_toNNReal', max_eq_left hDelta.le]
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hr : 3 ≤ r
  · have hc := abs_nullStandardizedCgfTaylorCoeff_le hr h
    have hpow : 0 ≤ nullAnalyticScale m p ^ r := by positivity
    have hmul := mul_le_mul_of_nonneg_right hc hpow
    have hLambda : 0 < nullLambdaSeries m p := nullLambdaSeries_pos h
    calc
      |nullStandardizedCgfTaylorCoeff r m p| *
          nullAnalyticScale m p ^ r ≤
        (nullLambdaSeries m p /
            (6 * nullAnalyticScale m p ^ (r - 3))) *
          nullAnalyticScale m p ^ r := hmul
      _ = nullLambdaSeries m p * nullAnalyticScale m p ^ 3 / 6 := by
        have hexp : r - 3 + 3 = r := by omega
        rw [show nullAnalyticScale m p ^ r =
            nullAnalyticScale m p ^ (r - 3) *
              nullAnalyticScale m p ^ 3 by rw [← pow_add, hexp]]
        field_simp [hDelta.ne']
      _ ≤ C := by
        dsimp [C]
        nlinarith [sq_nonneg (nullAnalyticScale m p),
          mul_nonneg hLambda.le (by positivity :
            0 ≤ nullAnalyticScale m p ^ 3)]
  · have hrsmall : r ≤ 2 := by omega
    have hLambda : 0 ≤ nullLambdaSeries m p :=
      (nullLambdaSeries_pos h).le
    interval_cases r
    · rw [nullStandardizedCgfTaylorCoeff_zero h]
      dsimp [C]
      norm_num
      nlinarith [sq_nonneg (nullAnalyticScale m p),
        mul_nonneg hLambda (by positivity :
          0 ≤ nullAnalyticScale m p ^ 3)]
    · rw [nullStandardizedCgfTaylorCoeff_one h]
      dsimp [C]
      norm_num
      nlinarith [sq_nonneg (nullAnalyticScale m p),
        mul_nonneg hLambda (by positivity :
          0 ≤ nullAnalyticScale m p ^ 3)]
    · rw [nullStandardizedCgfTaylorCoeff_two h]
      dsimp [C]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      nlinarith [sq_nonneg (nullAnalyticScale m p),
        mul_nonneg hLambda (by positivity :
          0 ≤ nullAnalyticScale m p ^ 3)]

/-- Tail of the exact complex CGF Taylor series after orders zero, one, and
two. -/
def nullComplexCgfTaylorTail (m p : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ,
    (nullStandardizedCgfTaylorCoeff (n + 3) m p : ℂ) * z ^ (n + 3)

/-- Pointwise geometric majorant for each term of the complex Taylor tail. -/
theorem norm_nullComplexCgfTaylorTail_term_le
    {m p : ℕ} (h : Admissible m p) (z : ℂ) (n : ℕ) :
    ‖(nullStandardizedCgfTaylorCoeff (n + 3) m p : ℂ) *
        z ^ (n + 3)‖ ≤
      (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
        (‖z‖ / nullAnalyticScale m p) ^ n := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hc := abs_nullStandardizedCgfTaylorCoeff_le
    (r := n + 3) (by omega) h
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hpow : 0 ≤ ‖z‖ ^ (n + 3) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc hpow
  calc
    |nullStandardizedCgfTaylorCoeff (n + 3) m p| * ‖z‖ ^ (n + 3) ≤
        (nullLambdaSeries m p /
          (6 * nullAnalyticScale m p ^ (n + 3 - 3))) *
            ‖z‖ ^ (n + 3) := hmul
    _ = (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
        (‖z‖ / nullAnalyticScale m p) ^ n := by
      rw [show n + 3 - 3 = n by omega, pow_add, div_pow]
      field_simp [hDelta.ne']

/-- Absolute summability of the Taylor tail throughout the natural disk. -/
theorem summable_norm_nullComplexCgfTaylorTail
    {m p : ℕ} (h : Admissible m p) {z : ℂ}
    (hz : ‖z‖ < nullAnalyticScale m p) :
    Summable (fun n : ℕ ↦
      ‖(nullStandardizedCgfTaylorCoeff (n + 3) m p : ℂ) *
        z ^ (n + 3)‖) := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hq0 : 0 ≤ ‖z‖ / nullAnalyticScale m p := by positivity
  have hq1 : ‖z‖ / nullAnalyticScale m p < 1 :=
    (div_lt_one hDelta).2 hz
  have hgeom : Summable (fun n : ℕ ↦
      (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
        (‖z‖ / nullAnalyticScale m p) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  exact hgeom.of_nonneg_of_le (fun n ↦ norm_nonneg _)
    (fun n ↦ norm_nullComplexCgfTaylorTail_term_le h z n)

/-- Explicit geometric bound for the complete local logarithmic remainder. -/
theorem norm_nullComplexCgfTaylorTail_le
    {m p : ℕ} (h : Admissible m p) {z : ℂ}
    (hz : ‖z‖ < nullAnalyticScale m p) :
    ‖nullComplexCgfTaylorTail m p z‖ ≤
      nullLambdaSeries m p * ‖z‖ ^ 3 /
        (6 * (1 - ‖z‖ / nullAnalyticScale m p)) := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hq0 : 0 ≤ ‖z‖ / nullAnalyticScale m p := by positivity
  have hq1 : ‖z‖ / nullAnalyticScale m p < 1 :=
    (div_lt_one hDelta).2 hz
  have hsumNorm := summable_norm_nullComplexCgfTaylorTail h hz
  have hgeom : Summable (fun n : ℕ ↦
      (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
        (‖z‖ / nullAnalyticScale m p) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  unfold nullComplexCgfTaylorTail
  calc
    ‖∑' n : ℕ,
        (nullStandardizedCgfTaylorCoeff (n + 3) m p : ℂ) *
          z ^ (n + 3)‖ ≤
        ∑' n : ℕ,
          ‖(nullStandardizedCgfTaylorCoeff (n + 3) m p : ℂ) *
            z ^ (n + 3)‖ := norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' n : ℕ,
        (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
          (‖z‖ / nullAnalyticScale m p) ^ n :=
      hsumNorm.tsum_le_tsum
        (fun n ↦ norm_nullComplexCgfTaylorTail_term_le h z n) hgeom
    _ = (nullLambdaSeries m p * ‖z‖ ^ 3 / 6) *
        (1 - ‖z‖ / nullAnalyticScale m p)⁻¹ := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one hq0 hq1]
    _ = nullLambdaSeries m p * ‖z‖ ^ 3 /
        (6 * (1 - ‖z‖ / nullAnalyticScale m p)) := by
      have hden : 1 - ‖z‖ / nullAnalyticScale m p ≠ 0 :=
        (sub_pos.mpr hq1).ne'
      field_simp [hden]

/-- On the natural disk, the full Taylor sum is exactly its Gaussian
quadratic term plus the absolutely convergent tail. -/
theorem nullComplexCgfTaylorSum_eq_quadratic_add_tail
    {m p : ℕ} (h : Admissible m p) {z : ℂ}
    (hz : ‖z‖ < nullAnalyticScale m p) :
    nullComplexCgfTaylorSum m p z =
      z ^ 2 / 2 + nullComplexCgfTaylorTail m p z := by
  let f : ℕ → ℂ := fun r ↦
    (nullStandardizedCgfTaylorCoeff r m p : ℂ) * z ^ r
  have htailNorm := summable_norm_nullComplexCgfTaylorTail h hz
  have htail : Summable (fun n : ℕ ↦ f (n + 3)) := by
    apply Summable.of_norm
    simpa [f] using htailNorm
  have hsum : Summable f := (summable_nat_add_iff 3).1 htail
  have hsplit := hsum.sum_add_tsum_nat_add 3
  unfold nullComplexCgfTaylorSum nullComplexCgfTaylorSeries
  simp only [FormalMultilinearSeries.sum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [← hsplit]
  unfold f nullComplexCgfTaylorTail
  norm_num [Finset.sum_range_succ,
    nullStandardizedCgfTaylorCoeff_zero h,
    nullStandardizedCgfTaylorCoeff_one h,
    nullStandardizedCgfTaylorCoeff_two h]
  ring

/-! ## Identification with the actual complex MGF -/

/-- Real Taylor series underlying the complex exponent. -/
def nullRealCgfTaylorSeries (m p : ℕ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (fun r ↦ nullStandardizedCgfTaylorCoeff r m p)

/-- The exact real standardized CGF has the preceding Taylor series at
zero. -/
theorem hasFPowerSeriesAt_cgf_standardizedNullLaw
    {m p : ℕ} (h : Admissible m p) :
    HasFPowerSeriesAt (cgf id (standardizedNullLaw m p))
      (nullRealCgfTaylorSeries m p) 0 := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hzero : (0 : ℝ) ∈
      interior (integrableExpSet id (standardizedNullLaw m p)) := by
    have hz : ‖(0 : ℂ)‖ < nullAnalyticScale m p := by simpa
    simpa using
      (re_mem_interior_integrableExpSet_standardizedNullLaw_of_norm_lt h hz)
  simpa [nullRealCgfTaylorSeries, nullStandardizedCgfTaylorCoeff] using
    (analyticAt_cgf hzero).hasFPowerSeriesAt

/-- On real arguments near zero, the complex Taylor sum is the real CGF
embedded in `ℂ`. -/
theorem nullComplexCgfTaylorSum_ofReal_eventuallyEq_cgf
    {m p : ℕ} (h : Admissible m p) :
    (fun x : ℝ ↦ nullComplexCgfTaylorSum m p (x : ℂ)) =ᶠ[nhds 0]
      (fun x ↦ (cgf id (standardizedNullLaw m p) x : ℂ)) := by
  have hseries := hasFPowerSeriesAt_cgf_standardizedNullLaw h
  filter_upwards [hseries.eventually_hasSum] with x hx
  have hx' : HasSum
      (fun n : ℕ ↦
        nullStandardizedCgfTaylorCoeff n m p * x ^ n)
      (cgf id (standardizedNullLaw m p) x) := by
    simpa [nullRealCgfTaylorSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hx
  have hxc : HasSum
      (fun n : ℕ ↦
        ((nullStandardizedCgfTaylorCoeff n m p * x ^ n : ℝ) : ℂ))
      (cgf id (standardizedNullLaw m p) x : ℂ) :=
    Complex.hasSum_ofReal.mpr hx'
  unfold nullComplexCgfTaylorSum nullComplexCgfTaylorSeries
  simp only [FormalMultilinearSeries.sum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  apply HasSum.tsum_eq
  convert hxc using 1 with n
  push_cast
  ring

/-- Exponentiating the Taylor sum agrees with the exact complex MGF at all
nearby real points. -/
theorem cexp_nullComplexCgfTaylorSum_ofReal_eventuallyEq_complexMGF
    {m p : ℕ} (h : Admissible m p) :
    (fun x : ℝ ↦ Complex.exp
      (nullComplexCgfTaylorSum m p (x : ℂ))) =ᶠ[nhds 0]
      (fun x ↦ complexMGF id (standardizedNullLaw m p) (x : ℂ)) := by
  letI : IsProbabilityMeasure (standardizedNullLaw m p) :=
    isProbabilityMeasure_standardizedNullLaw h.2
  filter_upwards [nullComplexCgfTaylorSum_ofReal_eventuallyEq_cgf h,
    Ioi_mem_nhds (show -nullAnalyticScale m p < (0 : ℝ) by
      linarith [nullAnalyticScale_pos h])]
    with x hx hxt
  rw [hx, complexMGF_ofReal]
  change Complex.exp
      ((Real.log (mgf id (standardizedNullLaw m p) x) : ℝ) : ℂ) =
    (mgf id (standardizedNullLaw m p) x : ℂ)
  rw [← Complex.ofReal_exp]
  norm_cast
  exact Real.exp_log (mgf_pos
    (integrable_exp_mul_id_standardizedNullLaw_of_neg_analyticScale_lt h hxt))

/-- The complex Taylor sum is holomorphic throughout its natural disk. -/
theorem analyticOnNhd_nullComplexCgfTaylorSum_on_analyticDisk
    {m p : ℕ} (h : Admissible m p) :
    AnalyticOnNhd ℂ (nullComplexCgfTaylorSum m p)
      (Metric.ball 0 (nullAnalyticScale m p)) := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hRadius := nullComplexCgfTaylorSeries_analyticScale_le_radius h
  apply (nullComplexCgfTaylorSeries m p).analyticOnNhd.mono
  intro z hz
  rw [Metric.mem_ball] at hz
  rw [Metric.mem_eball, edist_dist]
  have hlt : ENNReal.ofReal (dist z 0) <
      ((Real.toNNReal (nullAnalyticScale m p) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_lt_coe_iff (dist_nonneg : 0 ≤ dist z 0)]
    simpa [Real.coe_toNNReal', max_eq_left hDelta.le] using hz
  exact hlt.trans_le hRadius

/-- Branch-free logarithmic identity: on the full disk, exponentiating the
explicit cumulant Taylor sum gives the actual complex MGF. -/
theorem cexp_nullComplexCgfTaylorSum_eq_complexMGF_on_analyticDisk
    {m p : ℕ} (h : Admissible m p) :
    Set.EqOn
      (fun z : ℂ ↦ Complex.exp (nullComplexCgfTaylorSum m p z))
      (complexMGF id (standardizedNullLaw m p))
      (Metric.ball 0 (nullAnalyticScale m p)) := by
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hTaylor : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ Complex.exp (nullComplexCgfTaylorSum m p z))
      (Metric.ball 0 (nullAnalyticScale m p)) :=
    (analyticOnNhd_nullComplexCgfTaylorSum_on_analyticDisk h).cexp
  have hMgf :=
    analyticOnNhd_complexMGF_standardizedNullLaw_on_analyticDisk h
  have hrealEvent : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Complex.exp (nullComplexCgfTaylorSum m p (x : ℂ)) =
        complexMGF id (standardizedNullLaw m p) (x : ℂ) :=
    (cexp_nullComplexCgfTaylorSum_ofReal_eventuallyEq_complexMGF h).filter_mono
      inf_le_left
  have hreal : ∃ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Complex.exp (nullComplexCgfTaylorSum m p (x : ℂ)) =
        complexMGF id (standardizedNullLaw m p) (x : ℂ) :=
    hrealEvent.frequently
  have hcomplex : ∃ᶠ z : ℂ in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      Complex.exp (nullComplexCgfTaylorSum m p z) =
        complexMGF id (standardizedNullLaw m p) z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := hreal
    refine ⟨fun n ↦ (xs n : ℂ), ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · convert
          (Complex.ofRealCLM.continuous.tendsto 0).comp hx_tendsto.1 using 1
        · rfl
        · simp [Complex.ofRealCLM_apply]
      · simpa using hx_tendsto.2
    · exact hx_eq n
  exact hTaylor.eqOn_of_preconnected_of_frequently_eq hMgf
    Metric.isPreconnected_ball
    (show (0 : ℂ) ∈ Metric.ball 0 (nullAnalyticScale m p) by simpa)
    hcomplex

/-- Specialization of the preceding identity to the imaginary axis: the
exact characteristic function is the exponential of the Taylor sum. -/
theorem charFun_standardizedNullLaw_eq_cexp_taylorSum
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| < nullAnalyticScale m p) :
    charFun (standardizedNullLaw m p) t =
      Complex.exp
        (nullComplexCgfTaylorSum m p ((t : ℂ) * Complex.I)) := by
  rw [← complexMGF_id_mul_I]
  symm
  apply cexp_nullComplexCgfTaylorSum_eq_complexMGF_on_analyticDisk h
  rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  exact ht

/-- The model-specific logarithmic remainder on the imaginary axis. -/
def nullLocalCharacteristicRemainder (m p : ℕ) (t : ℝ) : ℂ :=
  nullComplexCgfTaylorTail m p ((t : ℂ) * Complex.I)

/-- Exact local characteristic exponent with its Gaussian quadratic part
separated. -/
theorem charFun_standardizedNullLaw_eq_gaussian_cexp_remainder
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| < nullAnalyticScale m p) :
    charFun (standardizedNullLaw m p) t =
      Complex.exp
        (-((t ^ 2 / 2 : ℝ) : ℂ) +
          nullLocalCharacteristicRemainder m p t) := by
  rw [charFun_standardizedNullLaw_eq_cexp_taylorSum h ht,
    nullComplexCgfTaylorSum_eq_quadratic_add_tail h]
  · unfold nullLocalCharacteristicRemainder
    congr 1
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  · simpa [Complex.norm_real, Real.norm_eq_abs] using ht

/-- The explicit finite, uniform local logarithmic characteristic-function
bound.  This is the quantitative input needed by both the fixed-frequency
CLT and the later Fourier/Edgeworth argument. -/
theorem norm_nullLocalCharacteristicRemainder_le
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| < nullAnalyticScale m p) :
    ‖nullLocalCharacteristicRemainder m p t‖ ≤
      nullLambdaSeries m p * |t| ^ 3 /
        (6 * (1 - |t| / nullAnalyticScale m p)) := by
  unfold nullLocalCharacteristicRemainder
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    (norm_nullComplexCgfTaylorTail_le h
      (z := (t : ℂ) * Complex.I) (by
        simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using ht))

/-- Scalar form of the local logarithmic-remainder bound. -/
def nullLocalCharacteristicRemainderBound (m p : ℕ) (t : ℝ) : ℝ :=
  nullLambdaSeries m p * |t| ^ 3 /
    (6 * (1 - |t| / nullAnalyticScale m p))

/-- Exponential transfer from the logarithmic remainder to the difference
between the actual characteristic function and the Gaussian characteristic
function. -/
theorem norm_charFun_standardizedNullLaw_sub_gaussian_le
    {m p : ℕ} (h : Admissible m p) {t : ℝ}
    (ht : |t| < nullAnalyticScale m p) :
    ‖charFun (standardizedNullLaw m p) t -
        Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      Real.exp (-(t ^ 2 / 2)) *
        nullLocalCharacteristicRemainderBound m p t *
          Real.exp (nullLocalCharacteristicRemainderBound m p t) := by
  let r : ℂ := nullLocalCharacteristicRemainder m p t
  let B : ℝ := nullLocalCharacteristicRemainderBound m p t
  have hden : 0 < 1 - |t| / nullAnalyticScale m p := by
    exact sub_pos.mpr ((div_lt_one (nullAnalyticScale_pos h)).2 ht)
  have hB : 0 ≤ B := by
    dsimp [B, nullLocalCharacteristicRemainderBound]
    exact div_nonneg
      (mul_nonneg (nullLambdaSeries_pos h).le (by positivity))
      (mul_nonneg (by norm_num) hden.le)
  have hr : ‖r‖ ≤ B := by
    dsimp [r, B, nullLocalCharacteristicRemainderBound]
    exact norm_nullLocalCharacteristicRemainder_le h ht
  have hexp : ‖Complex.exp r - 1‖ ≤ ‖r‖ * Real.exp ‖r‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp r 1
  rw [charFun_standardizedNullLaw_eq_gaussian_cexp_remainder h ht]
  have hfactor :
      Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ) + r) -
          Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) =
        Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) *
          (Complex.exp r - 1) := by
    rw [Complex.exp_add]
    ring
  change ‖Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ) + r) -
      Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ))‖ ≤ _
  rw [hfactor, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  calc
    Real.exp (-(t ^ 2 / 2)) * ‖Complex.exp r - 1‖ ≤
        Real.exp (-(t ^ 2 / 2)) * (‖r‖ * Real.exp ‖r‖) :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    _ ≤ Real.exp (-(t ^ 2 / 2)) * (B * Real.exp B) := by
      gcongr
    _ = Real.exp (-(t ^ 2 / 2)) * B * Real.exp B := by ring

/-! ## Fixed-frequency consequence -/

/-- Along every admissible triangular array, the explicit local remainder
bound tends to zero at each fixed frequency. -/
theorem tendsto_nullLocalCharacteristicRemainderBound_zero
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) (t : ℝ) :
    Tendsto
      (fun p ↦ nullLocalCharacteristicRemainderBound (m p) p t)
      atTop (nhds 0) := by
  have hDelta :=
    tendsto_nullAnalyticScale_atTop_of_eventually_admissible m hadm
  have hLambda :=
    tendsto_nullLambdaSeries_zero_of_eventually_admissible m hadm
  have hratio : Tendsto
      (fun p ↦ |t| / nullAnalyticScale (m p) p) atTop (nhds 0) :=
    hDelta.const_div_atTop |t|
  have hden : Tendsto
      (fun p ↦ 6 * (1 - |t| / nullAnalyticScale (m p) p))
      atTop (nhds 6) := by
    have h6 : Tendsto (fun _ : ℕ ↦ (6 : ℝ)) atTop (nhds 6) :=
      tendsto_const_nhds
    have h1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using h6.mul (h1.sub hratio)
  have hnum : Tendsto
      (fun p ↦ nullLambdaSeries (m p) p * |t| ^ 3)
      atTop (nhds 0) := by
    simpa using hLambda.mul_const (|t| ^ 3)
  unfold nullLocalCharacteristicRemainderBound
  have hquot := hnum.div hden (by norm_num : (6 : ℝ) ≠ 0)
  convert hquot using 1
  · funext p
    rfl
  · norm_num

/-- Fixed-frequency convergence of the actual standardized null
characteristic function to the standard Gaussian characteristic function. -/
theorem tendsto_charFun_standardizedNullLaw_fixed_frequency
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) (t : ℝ) :
    Tendsto (fun p ↦ charFun (standardizedNullLaw (m p) p) t)
      atTop (nhds (Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)))) := by
  have hDelta :=
    tendsto_nullAnalyticScale_atTop_of_eventually_admissible m hadm
  have hB := tendsto_nullLocalCharacteristicRemainderBound_zero m hadm t
  have hfreq : ∀ᶠ p in atTop,
      |t| < nullAnalyticScale (m p) p :=
    (tendsto_atTop.1 hDelta (|t| + 1)).mono fun p hp ↦ lt_of_lt_of_le (by
      exact lt_add_one |t|) hp
  have hupper : Tendsto
      (fun p ↦ Real.exp (-(t ^ 2 / 2)) *
        nullLocalCharacteristicRemainderBound (m p) p t *
          Real.exp (nullLocalCharacteristicRemainderBound (m p) p t))
      atTop (nhds 0) := by
    have hexpB : Tendsto
        (fun p ↦ Real.exp
          (nullLocalCharacteristicRemainderBound (m p) p t))
        atTop (nhds (Real.exp 0)) :=
      (Real.continuous_exp.tendsto 0).comp hB
    simpa using
      (tendsto_const_nhds.mul hB).mul hexpB
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun p ↦ norm_nonneg _
  · filter_upwards [hadm, hfreq] with p hp htp
    exact norm_charFun_standardizedNullLaw_sub_gaussian_le hp htp
  · exact hupper

end

end LogdetLean
