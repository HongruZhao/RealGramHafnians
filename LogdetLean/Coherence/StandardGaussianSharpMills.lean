import LogdetLean.Coherence.StandardGaussianMills
import LogdetLean.Coherence.NoncentralPearsonTailMixture
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
/-!
# Sharp Mills ratio for the standard Gaussian tail

The coarse global hazard estimate used by the finite Pearson comparison is
not sharp enough to identify the planted extreme-height intensity.  This file
proves the classical two-sided Mills inequality and its asymptotic ratio.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

attribute [local instance 2000] NormedAlgebra.toNormedSpace

theorem standardGaussianUpperTail_eq_integral_Ioi (x : ℝ) :
    standardGaussianUpperTail x =
      ∫ y in Ioi x, gaussianPDFReal 0 1 y := by
  have htail : standardGaussianUpperTail x =
      (gaussianReal 0 1).real (Ioi x) := by
    rw [standardGaussianUpperTail, cdf_eq_real]
    have hcompl := measureReal_compl (μ := gaussianReal 0 1)
      (s := Iic x) measurableSet_Iic
    rw [compl_Iic, probReal_univ] at hcompl
    linarith
  rw [htail]
  rw [Measure.real]
  rw [gaussianReal_apply_eq_integral (0 : ℝ)
    (by norm_num : (1 : NNReal) ≠ 0)]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg fun _ ↦ gaussianPDFReal_nonneg 0 1 _

/-- Derivative of the standard Gaussian density. -/
theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    algebraRealHasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  have hsq : algebraRealHasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    simpa [algebraRealHasDerivAt] using (hasDerivAt_pow 2 x)
  have hnegDiv : algebraRealHasDerivAt (-fun y : ℝ ↦ y ^ 2 / 2) (-x) x :=
    (hsq.div_const 2 |>.neg).congr_deriv (by ring)
  have hquad : algebraRealHasDerivAt (fun y : ℝ ↦ -(y ^ 2 / 2)) (-x) x := by
    apply hnegDiv.congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.neg_apply]
  have hexp := hquad.exp
  have hconst := hexp.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have hd : algebraRealHasDerivAt
      (fun y : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(y ^ 2 / 2)))
      (-x * ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(x ^ 2 / 2)))) x :=
    hconst.congr_deriv (by ring)
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  simpa only [neg_div] using hd

/-- The standard Gaussian density vanishes at `+∞`. -/
theorem tendsto_standardGaussianPDF_atTop_zero :
    Tendsto (gaussianPDFReal 0 1) atTop (nhds 0) := by
  have hbase :=
    (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (1 / 2 : ℝ)) (by norm_num) (0 : ℝ)).mono_left
        atTop_le_cocompact
  have hbase' : Tendsto (fun x : ℝ ↦ Real.exp (-(x ^ 2 / 2)))
      atTop (nhds 0) := by
    apply hbase.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [abs_of_pos hx, Real.rpow_zero]
    ring_nf
  have hmul := hbase'.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  simpa only [neg_div, mul_zero] using hmul

/-- The first truncated Gaussian density moment has the exact endpoint
value `∫_x^∞ y φ(y)dy=φ(x)`. -/
theorem integral_Ioi_mul_standardGaussianPDF (x : ℝ) :
    (∫ y in Ioi x, y * gaussianPDFReal 0 1 y) =
      gaussianPDFReal 0 1 x := by
  have hderiv : ∀ y ∈ Ici x,
      algebraRealHasDerivAt (fun z : ℝ ↦ -gaussianPDFReal 0 1 z)
        (y * gaussianPDFReal 0 1 y) y := by
    intro y _hy
    have hn : algebraRealHasDerivAt (-gaussianPDFReal 0 1)
        (y * gaussianPDFReal 0 1 y) y :=
      (hasDerivAt_standardGaussianPDF y).neg.congr_deriv (by ring)
    apply hn.congr_of_eventuallyEq
    filter_upwards with z
    simp only [Pi.neg_apply]
  have hint : Integrable (fun y : ℝ ↦ y * gaussianPDFReal 0 1 y) := by
    have h := integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    have hc := h.const_mul (Real.sqrt (2 * Real.pi))⁻¹
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    convert hc using 1
    funext y
    rw [neg_div]
    ring
  have htend : Tendsto (fun y : ℝ ↦ -gaussianPDFReal 0 1 y)
      atTop (nhds 0) := by
    simpa using tendsto_standardGaussianPDF_atTop_zero.neg
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hint.integrableOn htend
  simpa using hFTC

/-- Gap in the Gaussian upper Mills inequality. -/
def standardGaussianUpperMillsGap (x : ℝ) : ℝ :=
  gaussianPDFReal 0 1 x / x - standardGaussianUpperTail x

/-- Gap in the Gaussian lower Mills inequality. -/
def standardGaussianLowerMillsGap (x : ℝ) : ℝ :=
  standardGaussianUpperTail x -
    x / (1 + x ^ 2) * gaussianPDFReal 0 1 x

theorem hasDerivAt_standardGaussianUpperMillsGap
    {x : ℝ} (hx : 0 < x) :
    algebraRealHasDerivAt standardGaussianUpperMillsGap
      (-gaussianPDFReal 0 1 x / x ^ 2) x := by
  have hid : algebraRealHasDerivAt (fun y : ℝ ↦ y) 1 x := by
    simpa [algebraRealHasDerivAt] using (hasDerivAt_pow 1 x)
  have hquot := (hasDerivAt_standardGaussianPDF x).div hid hx.ne'
  have htail := hasDerivAt_standardGaussianUpperTail x
  unfold standardGaussianUpperMillsGap
  have h := hquot.sub htail
  exact h.congr_deriv (by
    have hpdf0 := gaussianPDFReal_nonneg 0 1 x
    field_simp [hx.ne']
    ring)

theorem hasDerivAt_standardGaussianLowerMillsGap
    {x : ℝ} (hx : 0 < x) :
    algebraRealHasDerivAt standardGaussianLowerMillsGap
      (-2 * gaussianPDFReal 0 1 x / (1 + x ^ 2) ^ 2) x := by
  have hid : algebraRealHasDerivAt (fun y : ℝ ↦ y) 1 x := by
    simpa [algebraRealHasDerivAt] using (hasDerivAt_pow 1 x)
  have hone : algebraRealHasDerivAt (fun _y : ℝ ↦ (1 : ℝ)) 0 x :=
    hasDerivAt_const x 1
  have hden : algebraRealHasDerivAt (fun y : ℝ ↦ 1 + y ^ 2) (2 * x) x := by
    have hsq : algebraRealHasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
      simpa [algebraRealHasDerivAt] using (hasDerivAt_pow 2 x)
    have hadd : algebraRealHasDerivAt
        ((fun _y : ℝ ↦ (1 : ℝ)) + fun y : ℝ ↦ y ^ 2)
        (2 * x) x := (hone.add hsq).congr_deriv (by ring)
    apply hadd.congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.add_apply]
  have hden0 : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hratio := hid.div hden hden0
  have hprod := hratio.mul (hasDerivAt_standardGaussianPDF x)
  have htail := hasDerivAt_standardGaussianUpperTail x
  unfold standardGaussianLowerMillsGap
  have h := htail.sub hprod
  exact h.congr_deriv (by
    simp only [Pi.div_apply]
    field_simp [hden0]
    ring)

theorem tendsto_standardGaussianUpperTail_atTop_zero :
    Tendsto standardGaussianUpperTail atTop (nhds 0) := by
  have h := (tendsto_const_nhds : Tendsto (fun _x : ℝ ↦ (1 : ℝ))
    atTop (nhds 1)).sub (tendsto_cdf_atTop (gaussianReal 0 1))
  change Tendsto (fun x : ℝ ↦ 1 - cdf (gaussianReal 0 1) x)
    atTop (nhds 0)
  simpa only [sub_self] using h

theorem tendsto_standardGaussianUpperMillsGap_atTop_zero :
    Tendsto standardGaussianUpperMillsGap atTop (nhds 0) := by
  have hquot := tendsto_standardGaussianPDF_atTop_zero.div_atTop
    (tendsto_id : Tendsto (fun x : ℝ ↦ x) atTop atTop)
  have h := hquot.sub tendsto_standardGaussianUpperTail_atTop_zero
  change Tendsto (fun x : ℝ ↦
    gaussianPDFReal 0 1 x / x - standardGaussianUpperTail x)
    atTop (nhds 0)
  simpa only [id_eq, sub_self] using h

theorem tendsto_x_div_one_add_sq_atTop_zero :
    Tendsto (fun x : ℝ ↦ x / (1 + x ^ 2)) atTop (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hden : Tendsto (fun x : ℝ ↦ 1 + x⁻¹ ^ 2) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _x : ℝ ↦ (1 : ℝ))
      atTop (nhds 1)).add (hinv.pow 2)
  have hratio := hinv.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun x : ℝ ↦ x⁻¹ / (1 + x⁻¹ ^ 2)) =ᶠ[atTop]
      (fun x : ℝ ↦ x / (1 + x ^ 2)) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp [hx]
    ring
  simpa using hratio.congr' heq

theorem tendsto_standardGaussianLowerMillsGap_atTop_zero :
    Tendsto standardGaussianLowerMillsGap atTop (nhds 0) := by
  have hprod := tendsto_x_div_one_add_sq_atTop_zero.mul
    tendsto_standardGaussianPDF_atTop_zero
  have h := tendsto_standardGaussianUpperTail_atTop_zero.sub hprod
  change Tendsto (fun x : ℝ ↦ standardGaussianUpperTail x -
    x / (1 + x ^ 2) * gaussianPDFReal 0 1 x) atTop (nhds 0)
  simpa only [sub_self, zero_mul] using h

theorem standardGaussianUpperMillsGap_antitoneOn :
    AntitoneOn standardGaussianUpperMillsGap (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Ioi (𝕜 := ℝ) (0 : ℝ))
  · intro x hx
    exact (hasDerivAt_standardGaussianUpperMillsGap hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    simpa only [interior_Ioi] using
      (hasDerivAt_standardGaussianUpperMillsGap hx').hasDerivWithinAt
  · intro x hx
    have hpdf := gaussianPDFReal_nonneg 0 1 x
    have hsq := sq_nonneg x
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpdf) hsq

theorem standardGaussianLowerMillsGap_antitoneOn :
    AntitoneOn standardGaussianLowerMillsGap (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Ioi (𝕜 := ℝ) (0 : ℝ))
  · intro x hx
    exact (hasDerivAt_standardGaussianLowerMillsGap hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    simpa only [interior_Ioi] using
      (hasDerivAt_standardGaussianLowerMillsGap hx').hasDerivWithinAt
  · intro x hx
    have hpdf := gaussianPDFReal_nonneg 0 1 x
    have hden : 0 ≤ (1 + x ^ 2) ^ 2 := sq_nonneg _
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-2 : ℝ) ≤ 0) hpdf) hden

theorem standardGaussianUpperMillsGap_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ standardGaussianUpperMillsGap x := by
  apply le_of_tendsto tendsto_standardGaussianUpperMillsGap_atTop_zero
  filter_upwards [eventually_gt_atTop x] with y hy
  exact standardGaussianUpperMillsGap_antitoneOn hx (hx.trans hy) hy.le

theorem standardGaussianLowerMillsGap_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ standardGaussianLowerMillsGap x := by
  apply le_of_tendsto tendsto_standardGaussianLowerMillsGap_atTop_zero
  filter_upwards [eventually_gt_atTop x] with y hy
  exact standardGaussianLowerMillsGap_antitoneOn hx (hx.trans hy) hy.le

/-- The classical sharp two-sided Mills inequality. -/
theorem standardGaussian_mills_bounds {x : ℝ} (hx : 0 < x) :
    x / (1 + x ^ 2) * gaussianPDFReal 0 1 x ≤
        standardGaussianUpperTail x ∧
      standardGaussianUpperTail x ≤ gaussianPDFReal 0 1 x / x := by
  constructor
  · simpa [standardGaussianLowerMillsGap] using
      standardGaussianLowerMillsGap_nonneg hx
  · simpa [standardGaussianUpperMillsGap] using
      standardGaussianUpperMillsGap_nonneg hx

/-- The sharp Mills ratio `x Q(x) / φ(x)` tends to one. -/
theorem tendsto_standardGaussian_millsRatio_one :
    Tendsto (fun x : ℝ ↦
      x * standardGaussianUpperTail x / gaussianPDFReal 0 1 x)
      atTop (nhds 1) := by
  have hlower : Tendsto (fun x : ℝ ↦ x ^ 2 / (1 + x ^ 2))
      atTop (nhds 1) := by
    have hden : Tendsto (fun x : ℝ ↦ 1 + x ^ 2) atTop atTop := by
      have hsq : Tendsto (fun x : ℝ ↦ x ^ 2) atTop atTop := by
        simpa using (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num))
      exact tendsto_atTop_add_const_left atTop 1 hsq
    have hinv := hden.const_div_atTop 1
    have hsub := (tendsto_const_nhds : Tendsto (fun _x : ℝ ↦ (1 : ℝ))
      atTop (nhds 1)).sub hinv
    have heq : (fun x : ℝ ↦ 1 - 1 / (1 + x ^ 2)) =ᶠ[atTop]
        (fun x : ℝ ↦ x ^ 2 / (1 + x ^ 2)) := by
      filter_upwards with x
      have hden0 : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
      field_simp [hden0]
      ring
    simpa only [sub_zero] using hsub.congr' heq
  have hnonneg : ∀ᶠ x in atTop,
      x ^ 2 / (1 + x ^ 2) ≤
        x * standardGaussianUpperTail x / gaussianPDFReal 0 1 x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hmills := (standardGaussian_mills_bounds hx).1
    have hpdf := gaussianPDFReal_pos 0 1 x (by norm_num)
    have hden : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hmills' : x * gaussianPDFReal 0 1 x / (1 + x ^ 2) ≤
        standardGaussianUpperTail x := by
      convert hmills using 1 <;> ring
    have hclear := (div_le_iff₀ hden).mp hmills'
    have hmul := mul_le_mul_of_nonneg_left hclear hx.le
    rw [div_le_div_iff₀ hden hpdf]
    nlinarith
  have hupper : ∀ᶠ x in atTop,
      x * standardGaussianUpperTail x / gaussianPDFReal 0 1 x ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hmills := (standardGaussian_mills_bounds hx).2
    have hpdf := gaussianPDFReal_pos 0 1 x (by norm_num)
    rw [div_le_one hpdf]
    have hx0 := hx.le
    calc
      x * standardGaussianUpperTail x ≤ x * (gaussianPDFReal 0 1 x / x) :=
        mul_le_mul_of_nonneg_left hmills hx0
      _ = gaussianPDFReal 0 1 x := by field_simp [hx.ne']
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds hnonneg hupper

/-- Named Mills ratio used in tail-ratio calculations. -/
def standardGaussianMillsRatio (x : ℝ) : ℝ :=
  x * standardGaussianUpperTail x / gaussianPDFReal 0 1 x

theorem tendsto_standardGaussianMillsRatio_one :
    Tendsto standardGaussianMillsRatio atTop (nhds 1) := by
  change Tendsto (fun x : ℝ ↦
    x * standardGaussianUpperTail x / gaussianPDFReal 0 1 x)
    atTop (nhds 1)
  exact tendsto_standardGaussian_millsRatio_one

/-- Exact density ratio under a finite shift. -/
theorem standardGaussianPDF_add_div (x h : ℝ) :
    gaussianPDFReal 0 1 (x + h) / gaussianPDFReal 0 1 x =
      Real.exp (-x * h - h ^ 2 / 2) := by
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by
    have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
    exact inv_ne_zero hsqrt.ne'
  rw [gaussianPDFReal, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [mul_div_mul_left _ _ hc]
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Sharp shifted-tail ratio.  If `x_n→∞`, `h_n→0`, and
`x_n h_n→c`, then `Q(x_n+h_n)/Q(x_n)→exp(-c)`. -/
theorem tendsto_standardGaussianUpperTail_add_div
    {xseq hseq : ℕ → ℝ} {c : ℝ}
    (hx : Tendsto xseq atTop atTop)
    (hh : Tendsto hseq atTop (nhds 0))
    (hcross : Tendsto (fun n ↦ xseq n * hseq n) atTop (nhds c)) :
    Tendsto (fun n ↦
      standardGaussianUpperTail (xseq n + hseq n) /
        standardGaussianUpperTail (xseq n))
      atTop (nhds (Real.exp (-c))) := by
  have hy : Tendsto (fun n ↦ xseq n + hseq n) atTop atTop :=
    hx.atTop_add hh
  have hMx : Tendsto (fun n ↦ standardGaussianMillsRatio (xseq n))
      atTop (nhds 1) := tendsto_standardGaussianMillsRatio_one.comp hx
  have hMy : Tendsto (fun n ↦
      standardGaussianMillsRatio (xseq n + hseq n))
      atTop (nhds 1) := tendsto_standardGaussianMillsRatio_one.comp hy
  have hMratio : Tendsto (fun n ↦
      standardGaussianMillsRatio (xseq n + hseq n) /
        standardGaussianMillsRatio (xseq n)) atTop (nhds 1) := by
    have hraw := hMy.div hMx (by norm_num : (1 : ℝ) ≠ 0)
    have heq : ((fun n ↦ standardGaussianMillsRatio (xseq n + hseq n)) /
        (fun n ↦ standardGaussianMillsRatio (xseq n))) =ᶠ[atTop]
        (fun n ↦ standardGaussianMillsRatio (xseq n + hseq n) /
          standardGaussianMillsRatio (xseq n)) := Eventually.of_forall fun _n ↦ rfl
    simpa only [one_div, inv_one] using hraw.congr' heq
  have hexponent : Tendsto (fun n ↦
      -xseq n * hseq n - hseq n ^ 2 / 2) atTop (nhds (-c)) := by
    have hnegCross : Tendsto (fun n ↦ -(xseq n * hseq n))
        atTop (nhds (-c)) := hcross.neg
    have hsmall : Tendsto (fun n ↦ hseq n ^ 2 / 2)
        atTop (nhds 0) := by
      simpa using (hh.pow 2).div_const 2
    simpa using hnegCross.sub hsmall
  have hPDFRatio : Tendsto (fun n ↦
      gaussianPDFReal 0 1 (xseq n + hseq n) /
        gaussianPDFReal 0 1 (xseq n))
      atTop (nhds (Real.exp (-c))) := by
    have hExp : Tendsto (fun n ↦ Real.exp
        (-xseq n * hseq n - hseq n ^ 2 / 2))
        atTop (nhds (Real.exp (-c))) :=
      (Real.continuous_exp.tendsto (-c)).comp hexponent
    apply hExp.congr'
    filter_upwards with n
    exact (standardGaussianPDF_add_div (xseq n) (hseq n)).symm
  have hhdiv : Tendsto (fun n ↦ hseq n / xseq n) atTop (nhds 0) :=
    hh.div_atTop hx
  have hden : Tendsto (fun n ↦ 1 + hseq n / xseq n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).add hhdiv
  have hXratio : Tendsto (fun n ↦ xseq n / (xseq n + hseq n))
      atTop (nhds 1) := by
    have hraw := (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).div hden (by norm_num : (1 : ℝ) ≠ 0)
    have heq : ((fun _n : ℕ ↦ (1 : ℝ)) /
        (fun n ↦ 1 + hseq n / xseq n)) =ᶠ[atTop]
        (fun n ↦ xseq n / (xseq n + hseq n)) := by
      filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ))]
        with n hxn
      change 1 / (1 + hseq n / xseq n) =
        xseq n / (xseq n + hseq n)
      field_simp [hxn.ne']
    simpa only [one_div, inv_one] using hraw.congr' heq
  have hprod := (hMratio.mul hPDFRatio).mul hXratio
  have hprod' : Tendsto (fun n ↦
      (standardGaussianMillsRatio (xseq n + hseq n) /
          standardGaussianMillsRatio (xseq n)) *
        (gaussianPDFReal 0 1 (xseq n + hseq n) /
          gaussianPDFReal 0 1 (xseq n)) *
        (xseq n / (xseq n + hseq n)))
      atTop (nhds (Real.exp (-c))) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ)),
      hy.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hxn hyn
  have hQx := (standardGaussianUpperTail_pos (xseq n)).ne'
  have hQy := (standardGaussianUpperTail_pos (xseq n + hseq n)).ne'
  have hPx := (gaussianPDFReal_pos 0 1 (xseq n) (by norm_num)).ne'
  have hPy := (gaussianPDFReal_pos 0 1 (xseq n + hseq n) (by norm_num)).ne'
  unfold standardGaussianMillsRatio
  field_simp [hxn.ne', hyn.ne', hQx, hQy, hPx, hPy]

/-- If two Gaussian thresholds diverge with a limiting ratio strictly larger
than one, the upper tail at the larger threshold is negligible. -/
theorem tendsto_standardGaussianUpperTail_div_zero_of_ratio
    {xseq yseq : ℕ → ℝ} {r : ℝ}
    (hx : Tendsto xseq atTop atTop)
    (hy : Tendsto yseq atTop atTop)
    (hratio : Tendsto (fun n ↦ yseq n / xseq n) atTop (nhds r))
    (hr : 1 < r) :
    Tendsto (fun n ↦
      standardGaussianUpperTail (yseq n) /
        standardGaussianUpperTail (xseq n))
      atTop (nhds 0) := by
  let E : ℕ → ℝ := fun n ↦
    ((1 + xseq n ^ 2) / (xseq n * yseq n)) *
      Real.exp (-(yseq n ^ 2 - xseq n ^ 2) / 2)
  have hfactor : Tendsto (fun n ↦
      (1 + xseq n ^ 2) / (xseq n * yseq n))
      atTop (nhds (1 / r)) := by
    have hxinv : Tendsto (fun n ↦ (xseq n)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hx
    have hnum : Tendsto (fun n ↦ 1 + (xseq n)⁻¹ ^ 2)
        atTop (nhds 1) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (1 : ℝ))
        atTop (nhds 1)).add (hxinv.pow 2)
    have hraw := hnum.div hratio (ne_of_gt (lt_trans zero_lt_one hr))
    have heq : (fun n ↦ (1 + (xseq n)⁻¹ ^ 2) /
        (yseq n / xseq n)) =ᶠ[atTop]
        (fun n ↦ (1 + xseq n ^ 2) / (xseq n * yseq n)) := by
      filter_upwards [hx.eventually (eventually_ne_atTop (0 : ℝ))]
        with n hxn
      by_cases hyn : yseq n = 0
      · simp [hyn]
      · field_simp [hxn, hyn]
        ring
    exact hraw.congr' heq
  have hgapRatio : Tendsto (fun n ↦
      (yseq n ^ 2 - xseq n ^ 2) / xseq n ^ 2)
      atTop (nhds (r ^ 2 - 1)) := by
    have hsq := hratio.pow 2
    have hsub := hsq.sub_const 1
    apply hsub.congr'
    filter_upwards [hx.eventually (eventually_ne_atTop (0 : ℝ))]
      with n hxn
    field_simp [hxn]
  have hxSqTop : Tendsto (fun n ↦ xseq n ^ 2) atTop atTop := by
    have hpos : ∀ᶠ n in atTop, 0 ≤ xseq n :=
      hx.eventually (eventually_ge_atTop 0)
    apply Filter.tendsto_atTop_mono' atTop
      (show ∀ᶠ n in atTop, xseq n ≤ xseq n ^ 2 from by
        filter_upwards [hx.eventually (eventually_ge_atTop 1)] with n hn
        nlinarith)
      hx
  have hgapTop : Tendsto (fun n ↦ yseq n ^ 2 - xseq n ^ 2)
      atTop atTop := by
    have hpos : 0 < r ^ 2 - 1 := by nlinarith
    have hprod := hxSqTop.atTop_mul_pos hpos hgapRatio
    apply hprod.congr'
    filter_upwards [hx.eventually (eventually_ne_atTop (0 : ℝ))]
      with n hxn
    field_simp [hxn]
  have hexp : Tendsto (fun n ↦
      Real.exp (-(yseq n ^ 2 - xseq n ^ 2) / 2))
      atTop (nhds 0) := by
    have hneg : Tendsto (fun n ↦ -(yseq n ^ 2 - xseq n ^ 2) / 2)
        atTop atBot :=
      (tendsto_neg_atTop_atBot.comp hgapTop).atBot_div_const (by norm_num)
    exact Real.tendsto_exp_atBot.comp hneg
  have hE : Tendsto E atTop (nhds 0) := by
    dsimp [E]
    simpa using hfactor.mul hexp
  apply squeeze_zero'
  · filter_upwards with n
    exact div_nonneg (standardGaussianUpperTail_nonneg _)
      (standardGaussianUpperTail_nonneg _)
  · filter_upwards [hx.eventually (eventually_gt_atTop 0),
      hy.eventually (eventually_gt_atTop 0)] with n hxn hyn
    have hmx := (standardGaussian_mills_bounds hxn).1
    have hmy := (standardGaussian_mills_bounds hyn).2
    have hQx := standardGaussianUpperTail_pos (xseq n)
    have hPx := gaussianPDFReal_pos 0 1 (xseq n) (by norm_num)
    have hPy := gaussianPDFReal_pos 0 1 (yseq n) (by norm_num)
    have hden : 0 < xseq n / (1 + xseq n ^ 2) *
        gaussianPDFReal 0 1 (xseq n) :=
      mul_pos (div_pos hxn (by nlinarith [sq_nonneg (xseq n)])) hPx
    calc
      standardGaussianUpperTail (yseq n) /
          standardGaussianUpperTail (xseq n) ≤
        (gaussianPDFReal 0 1 (yseq n) / yseq n) /
          (xseq n / (1 + xseq n ^ 2) *
            gaussianPDFReal 0 1 (xseq n)) :=
        div_le_div₀ (div_nonneg hPy.le hyn.le) hmy hden hmx
      _ = E n := by
        dsimp [E]
        have hPDF : gaussianPDFReal 0 1 (yseq n) /
            gaussianPDFReal 0 1 (xseq n) =
              Real.exp (-(yseq n ^ 2 - xseq n ^ 2) / 2) := by
          convert standardGaussianPDF_add_div (xseq n) (yseq n - xseq n) using 1
          · ring
          · congr 1
            ring
        rw [← hPDF]
        field_simp [hxn.ne', hyn.ne', hPx.ne', hPy.ne']
  · exact hE

end

end LogdetLean.Coherence
