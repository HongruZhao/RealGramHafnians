import LogdetLean.AllOrderCumulantBridge
import Mathlib.Analysis.Calculus.Deriv.CompMul
/-!
# Cumulants of the actual standardized null statistic

This file completes the affine-standardization step left open by the raw
all-order cumulant bridge.  For every `r >= 2`, it proves that the order-`r`
cumulant of the actual Gaussian sample statistic `Z0mpStatistic m p` is

`(-1)^r * nullStandardizedCumulantMagnitudeSeries r m p`.

The proof uses only the elementary affine transformation rule for an MGF,
the exact log-Beta law already proved in `NullCenterStandardization`, and the
raw cumulant identity in `AllOrderCumulantBridge`.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators MeasureTheory

noncomputable section

set_option linter.style.haveILetI false

/-- Iterated derivatives commute with precomposition by scalar
multiplication.  This version needs no differentiability assumption because
`deriv_comp_mul_left` is valid for Mathlib's totalized derivative. -/
theorem iteratedDeriv_comp_mul_left_any
    (r : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv r (fun t ↦ f (c * t)) x =
      c ^ r * iteratedDeriv r f (c * x) := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun : iteratedDeriv r (fun t ↦ f (c * t)) =
          fun t ↦ c ^ r * iteratedDeriv r f (c * t) := by
        funext t
        exact ih t
      rw [hfun, deriv_const_mul_field, deriv_comp_mul_left]
      simp only [smul_eq_mul, pow_succ]
      ring

/-- An affine change of a random variable changes its CGF by composition
with the scale and addition of the linear translation term. -/
theorem cgf_affine_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c d t : ℝ}
    (hInt : Integrable (fun ω ↦ Real.exp ((c * t) * X ω)) μ) :
    cgf (fun ω ↦ c * X ω + d) μ t =
      cgf X μ (c * t) + t * d := by
  unfold cgf
  rw [mgf_add_const, mgf_const_mul,
    Real.log_mul (mgf_pos hInt).ne' (Real.exp_ne_zero _), Real.log_exp]

/-- The finite explicit null CGF is smooth to every prescribed order at
zero. -/
theorem contDiffAt_nullFiniteLogCGF
    {m p r : ℕ} (h : Admissible m p) :
    ContDiffAt ℝ r (nullFiniteLogCGF m p) 0 := by
  unfold nullFiniteLogCGF
  apply ContDiffAt.sum
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact contDiffAt_betaLogCGF
    (betaShapeA_pos_of_le (hj.2.trans h.2))
    (betaShapeB_pos_of_two_le hj.1) r

/-- Near zero, the CGF of the standardized null law is the raw finite CGF
evaluated at `t / sqrt(V)`, plus the linear centering term. -/
theorem cgf_standardizedNullLaw_eventuallyEq_affineNullFiniteLogCGF
    {m p : ℕ} (h : Admissible m p) :
    cgf id (standardizedNullLaw m p) =ᶠ[nhds 0]
      (fun t ↦
        nullFiniteLogCGF m p
            ((1 / Real.sqrt (nullVSeries m p)) * t) +
          t * (-nullCenterDigammaSeries m p /
            Real.sqrt (nullVSeries m p))) := by
  have hs : 0 < Real.sqrt (nullVSeries m p) := sqrt_nullVSeries_pos h
  let c : ℝ := 1 / Real.sqrt (nullVSeries m p)
  let d : ℝ := -nullCenterDigammaSeries m p /
    Real.sqrt (nullVSeries m p)
  have hscale : Tendsto (fun t : ℝ ↦ c * t) (nhds 0) (nhds 0) := by
    have hc : Tendsto (fun _ : ℝ ↦ c) (nhds 0) (nhds c) :=
      tendsto_const_nhds
    simpa using hc.mul tendsto_id
  have hdom : ∀ᶠ t in nhds 0, NullMgfDomain m p (c * t) :=
    hscale.eventually (eventually_nullMgfDomain h)
  filter_upwards [hdom] with t ht
  haveI : IsProbabilityMeasure (logBetaSumLaw m p) :=
    isProbabilityMeasure_logBetaSumLaw h.2
  let g : ℝ → ℝ := fun x ↦
    (x - nullCenter m p) / Real.sqrt (nullVariance m p)
  have hg : AEMeasurable g (logBetaSumLaw m p) := by
    exact (by fun_prop : Measurable g).aemeasurable
  have hInt : Integrable
      (fun x : ℝ ↦ Real.exp ((c * t) * x))
      (logBetaSumLaw m p) :=
    (integrable_exp_and_mgf_logBetaSumLaw h.2 ht).1
  have hcgfMap : cgf id (standardizedNullLaw m p) t =
      cgf g (logBetaSumLaw m p) t := by
    unfold standardizedNullLaw cgf
    exact congrArg Real.log (congrFun (mgf_id_map hg) t)
  have hgAffine : g = fun x : ℝ ↦ c * x + d := by
    funext x
    dsimp [g, c, d]
    rw [nullCenter_eq_nullCenterDigammaSeries h.2,
      nullVariance_eq_nullVSeries h.2]
    field_simp [hs.ne']
    ring
  rw [hcgfMap, hgAffine, cgf_affine_eq hInt]
  have hfinite : cgf (fun x : ℝ ↦ x) (logBetaSumLaw m p) (c * t) =
      nullFiniteLogCGF m p (c * t) := by
    simpa only [Function.id_def] using
      (cgf_logBetaSumLaw_eq_nullFiniteLogCGF h.2 ht)
  rw [hfinite]

/-- The order-`r` cumulant of the actual exactly standardized Gaussian
sample-correlation log determinant. -/
def nullStandardizedSampleCumulant (r m p : ℕ) : ℝ :=
  iteratedDeriv r
    (cgf (Z0mpStatistic m p)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p)) 0

/-- The actual sample statistic and `standardizedNullLaw` have identical
CGFs. -/
theorem cgf_Z0mpStatistic_eq_standardizedNullLaw
    {m p : ℕ} (hpm : p ≤ m) :
    cgf (Z0mpStatistic m p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
      cgf id (standardizedNullLaw m p) := by
  let μ := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) p
  have hZ : AEMeasurable (Z0mpStatistic m p) μ :=
    (measurable_Z0mpStatistic m p).aemeasurable
  funext t
  unfold cgf
  rw [← mgf_id_map hZ]
  rw [map_Z0mpStatistic_eq_standardizedNullLaw m p hpm]

/-- Final standardized all-order identity.  At every order `r >= 2`, the
cumulant of the actual `Z_{0,m,p}` statistic is the signed standardized
reciprocal-power coefficient. -/
theorem nullStandardizedSampleCumulant_eq_sign_mul_magnitude
    {r m p : ℕ} (hr : 2 ≤ r) (h : Admissible m p) :
    nullStandardizedSampleCumulant r m p =
      (-1 : ℝ) ^ r *
        nullStandardizedCumulantMagnitudeSeries r m p := by
  unfold nullStandardizedSampleCumulant
  rw [cgf_Z0mpStatistic_eq_standardizedNullLaw h.2]
  rw [(cgf_standardizedNullLaw_eventuallyEq_affineNullFiniteLogCGF h).iteratedDeriv_eq r]
  let c : ℝ := 1 / Real.sqrt (nullVSeries m p)
  let d : ℝ := -nullCenterDigammaSeries m p /
    Real.sqrt (nullVSeries m p)
  have hF : ContDiffAt ℝ r
      (fun t ↦ nullFiniteLogCGF m p (c * t)) 0 := by
    have houter : ContDiffAt ℝ r (nullFiniteLogCGF m p) (c * 0) := by
      simpa using (contDiffAt_nullFiniteLogCGF (r := r) h)
    have hinner : ContDiffAt ℝ r (fun t : ℝ ↦ c * t) 0 := by
      fun_prop
    exact houter.comp 0 hinner
  have hlin : ContDiffAt ℝ r (fun t : ℝ ↦ t * d) 0 := by
    fun_prop
  change iteratedDeriv r
      (fun t ↦ nullFiniteLogCGF m p (c * t) + t * d) 0 = _
  have hadd : iteratedDeriv r
      (fun t ↦ nullFiniteLogCGF m p (c * t) + t * d) 0 =
      iteratedDeriv r (fun t ↦ nullFiniteLogCGF m p (c * t)) 0 +
        iteratedDeriv r (fun t : ℝ ↦ t * d) 0 := by
    change iteratedDeriv r
      ((fun t ↦ nullFiniteLogCGF m p (c * t)) +
        (fun t : ℝ ↦ t * d)) 0 = _
    exact iteratedDeriv_add hF hlin
  rw [hadd, iteratedDeriv_comp_mul_left_any,
    mul_zero,
    iteratedDeriv_nullFiniteLogCGF_eq_nullSignedCumulantSeries hr h,
    nullSignedCumulantSeries_eq_sign_mul_magnitude hr h,
    iteratedDeriv_mul_const_field]
  have hr1 : r ≠ 1 := by omega
  rw [iteratedDeriv_fun_id_zero, if_neg hr1, zero_mul, add_zero]
  unfold c nullStandardizedCumulantMagnitudeSeries
  rw [one_div, inv_pow, div_eq_mul_inv]
  ring

end

end LogdetLean
