import LogdetLean.Coherence.KolmogorovConcentration
/-!
# Replacing a threshold after an independent additive perturbation

For a real threshold `z`, the indicators of `x ≤ z` and `x + r ≤ z`
can differ only when `x` lies in the interval with endpoints `z` and
`z - r`.  That interval has length `|r|`.  This elementary observation is
the measure-theoretic bridge which converts an `L¹` bound for the retained
one-edge log-determinant remainder into a CDF replacement error.

The first theorem below is pointwise.  The second integrates it under an
arbitrary probability law having a linear interval-concentration bound.
No asymptotics and no Gaussian assumption enter this module.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Real-valued lower-threshold indicator. -/
def lowerThresholdIndicator (z x : ℝ) : ℝ :=
  if x ≤ z then 1 else 0

theorem measurable_lowerThresholdIndicator (z : ℝ) :
    Measurable (lowerThresholdIndicator z) := by
  unfold lowerThresholdIndicator
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/-- The threshold indicators before and after adding `r` disagree exactly
on the interval whose endpoints are `z` and `z-r`. -/
theorem abs_lowerThresholdIndicator_add_sub_eq_indicator_Ioc
    (z r x : ℝ) :
    |lowerThresholdIndicator z (x + r) - lowerThresholdIndicator z x| =
      (Ioc (min z (z - r)) (max z (z - r))).indicator (fun _ : ℝ ↦ (1 : ℝ)) x := by
  unfold lowerThresholdIndicator
  by_cases hr : 0 ≤ r
  · have hzmin : min z (z - r) = z - r := min_eq_right (by linarith)
    have hzmax : max z (z - r) = z := max_eq_left (by linarith)
    rw [hzmin, hzmax]
    by_cases hx₁ : x + r ≤ z
    · have hx₂ : x ≤ z := by linarith
      have hxnot : x ∉ Ioc (z - r) z := by
        intro hx
        exact (not_lt_of_ge hx₁) (by linarith [hx.1])
      simp [hx₁, hx₂, Set.indicator, hxnot]
    · have hxr : z - r < x := by linarith
      by_cases hx₂ : x ≤ z
      · have hxmem : x ∈ Ioc (z - r) z := ⟨hxr, hx₂⟩
        simp [hx₁, hx₂, Set.indicator, hxmem]
      · have hxnot : x ∉ Ioc (z - r) z := by
          intro hx
          exact hx₂ hx.2
        simp [hx₁, hx₂, Set.indicator, hxnot]
  · have hr' : r < 0 := lt_of_not_ge hr
    have hzmin : min z (z - r) = z := min_eq_left (by linarith)
    have hzmax : max z (z - r) = z - r := max_eq_right (by linarith)
    rw [hzmin, hzmax]
    by_cases hx₂ : x ≤ z
    · have hx₁ : x + r ≤ z := by linarith
      have hxnot : x ∉ Ioc z (z - r) := by
        intro hx
        exact (not_lt_of_ge hx₂) hx.1
      simp [hx₁, hx₂, Set.indicator, hxnot]
    · have hzx : z < x := lt_of_not_ge hx₂
      by_cases hx₁ : x + r ≤ z
      · have hxmem : x ∈ Ioc z (z - r) := ⟨hzx, by linarith⟩
        simp [hx₁, hx₂, Set.indicator, hxmem]
      · have hxnot : x ∉ Ioc z (z - r) := by
          intro hx
          exact hx₁ (by linarith [hx.2])
        simp [hx₁, hx₂, Set.indicator, hxnot]

/-- The interval between `z` and `z-r` has length `|r|`. -/
theorem max_sub_min_z_zsub (z r : ℝ) :
    max z (z - r) - min z (z - r) = |r| := by
  rcases le_total 0 r with hr | hr
  · rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonneg hr]
    ring
  · rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonpos hr]
    ring

/-- A linear interval-concentration bound for `mu` controls the mean
threshold replacement error produced by one deterministic shift `r`. -/
theorem integral_abs_lowerThresholdIndicator_add_sub_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {c d : ℝ} (_hc : 0 ≤ c) (_hd : 0 ≤ d)
    (hinterval : ∀ (a h : ℝ), 0 ≤ h →
      mu.real (Ioc a (a + h)) ≤ c * h + d)
    (z r : ℝ) :
    (∫ x, |lowerThresholdIndicator z (x + r) -
        lowerThresholdIndicator z x| ∂mu) ≤ c * |r| + d := by
  let a : ℝ := min z (z - r)
  let b : ℝ := max z (z - r)
  have hab : a ≤ b := min_le_max
  have hlen : b - a = |r| := by
    simpa [a, b] using max_sub_min_z_zsub z r
  have hb : b = a + |r| := by linarith
  rw [show (fun x ↦ |lowerThresholdIndicator z (x + r) -
      lowerThresholdIndicator z x|) =
      (Ioc a b).indicator (fun _ : ℝ ↦ (1 : ℝ)) by
        funext x
        simpa [a, b] using
          abs_lowerThresholdIndicator_add_sub_eq_indicator_Ioc z r x]
  rw [integral_indicator measurableSet_Ioc]
  simp only [integral_const, smul_eq_mul]
  rw [measureReal_restrict_apply_univ, mul_one]
  rw [hb]
  exact hinterval a |r| (abs_nonneg r)

/-- Iterated product-law form.  This is the form used after independence has
identified the joint law of the deleted statistic and the additive remainder
with `mu.prod nu`.  The two explicit integrability hypotheses keep this lemma
agnostic about how that product law was constructed. -/
theorem integral_integral_abs_lowerThresholdIndicator_add_sub_le
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (z : ℝ)
    (hinterval : ∀ (a h : ℝ), 0 ≤ h →
      mu.real (Ioc a (a + h)) ≤ c * h + d)
    (habs : Integrable (fun r : ℝ ↦ |r|) nu)
    (hleft : Integrable (fun r : ℝ ↦
      ∫ x, |lowerThresholdIndicator z (x + r) -
        lowerThresholdIndicator z x| ∂mu) nu) :
    (∫ r, (∫ x, |lowerThresholdIndicator z (x + r) -
        lowerThresholdIndicator z x| ∂mu) ∂nu) ≤
      c * (∫ r, |r| ∂nu) + d := by
  have hright : Integrable (fun r : ℝ ↦ c * |r| + d) nu :=
    (habs.const_mul c).add (integrable_const d)
  have hmono : (∫ r, (∫ x, |lowerThresholdIndicator z (x + r) -
      lowerThresholdIndicator z x| ∂mu) ∂nu) ≤
      ∫ r, (c * |r| + d) ∂nu := by
    apply integral_mono_ae hleft hright
    filter_upwards [] with r
    exact integral_abs_lowerThresholdIndicator_add_sub_le
      mu hc hd hinterval z r
  calc
    (∫ r, (∫ x, |lowerThresholdIndicator z (x + r) -
        lowerThresholdIndicator z x| ∂mu) ∂nu) ≤
        ∫ r, (c * |r| + d) ∂nu := hmono
    _ = c * (∫ r, |r| ∂nu) + d := by
      rw [integral_add (habs.const_mul c) (integrable_const d),
        integral_const_mul, integral_const]
      simp

/-- Product-measure form of the threshold-replacement estimate.  The first
coordinate is the additive remainder and the second is the deleted statistic.
This orientation makes Fubini expose exactly the iterated integral above. -/
theorem integral_prod_abs_lowerThresholdIndicator_add_sub_le
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (z : ℝ)
    (hinterval : ∀ (a h : ℝ), 0 ≤ h →
      mu.real (Ioc a (a + h)) ≤ c * h + d)
    (habs : Integrable (fun r : ℝ ↦ |r|) nu)
    (hprod : Integrable (fun w : ℝ × ℝ ↦
      |lowerThresholdIndicator z (w.2 + w.1) -
        lowerThresholdIndicator z w.2|) (nu.prod mu)) :
    (∫ w : ℝ × ℝ,
      |lowerThresholdIndicator z (w.2 + w.1) -
        lowerThresholdIndicator z w.2| ∂(nu.prod mu)) ≤
      c * (∫ r, |r| ∂nu) + d := by
  rw [MeasureTheory.integral_prod _ hprod]
  exact integral_integral_abs_lowerThresholdIndicator_add_sub_le
    mu nu hc hd z hinterval habs hprod.integral_prod_left

/-- Concrete standard-normal comparison.  If the deleted statistic has law
`mu`, its interval concentration follows from its Kolmogorov distance to the
standard Gaussian; consequently an independent `L¹` perturbation costs at
most its mean absolute size divided by `sqrt(2*pi)`, plus twice that
Kolmogorov distance. -/
theorem integral_prod_abs_lowerThresholdIndicator_add_sub_le_kolmogorov
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (z : ℝ)
    (habs : Integrable (fun r : ℝ ↦ |r|) nu)
    (hprod : Integrable (fun w : ℝ × ℝ ↦
      |lowerThresholdIndicator z (w.2 + w.1) -
        lowerThresholdIndicator z w.2|) (nu.prod mu)) :
    (∫ w : ℝ × ℝ,
      |lowerThresholdIndicator z (w.2 + w.1) -
        lowerThresholdIndicator z w.2| ∂(nu.prod mu)) ≤
      (∫ r, |r| ∂nu) / Real.sqrt (2 * Real.pi) +
        2 * kolmogorovDistance mu (gaussianReal 0 1) := by
  have hc : 0 ≤ (1 / Real.sqrt (2 * Real.pi) : ℝ) := by positivity
  have hd : 0 ≤ 2 * kolmogorovDistance mu (gaussianReal 0 1) :=
    mul_nonneg (by norm_num) (kolmogorovDistance_nonneg _ _)
  have hinterval : ∀ (a h : ℝ), 0 ≤ h →
      mu.real (Ioc a (a + h)) ≤
        (1 / Real.sqrt (2 * Real.pi)) * h +
          2 * kolmogorovDistance mu (gaussianReal 0 1) := by
    intro a h hh
    simpa [div_eq_mul_inv, mul_comm] using
      measureReal_Ioc_le_length_add_two_kolmogorov mu hh (a := a)
  simpa [div_eq_mul_inv, mul_comm] using
    integral_prod_abs_lowerThresholdIndicator_add_sub_le
      mu nu hc hd z hinterval habs hprod

end

end LogdetLean.Coherence
