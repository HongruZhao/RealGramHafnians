import LogdetLean.Coherence.NoncentralPearsonRuben
import LogdetLean.WishartMellinLaplace
import LogdetLean.ElementaryNormalization
import Mathlib.Tactic
/-!
# Gamma Chernoff bounds and normalized chi-radius concentration

This module derives quantitative Gamma and chi-square tail bounds from the
project's proved Mellin--Laplace transform and Mathlib's general Chernoff
inequalities.  It then proves the simultaneous concentration estimate needed
for the two independent Ruben radii `U = A / sqrt(m)` and
`V = B / sqrt(m-1)`.

No concentration theorem or probability certificate is assumed.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set

/-- Exact ordinary MGF of a Gamma law, derived from the existing
Mellin--Laplace transform. -/
theorem mgf_id_gammaMeasure {a r s : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hs : s < r) :
    mgf id (gammaMeasure a r) s = (r / (r - s)) ^ a := by
  rw [mgf]
  change (∫ x : ℝ, Real.exp (s * x) ∂gammaMeasure a r) = _
  have hrate : 0 < r + (-s) := by linarith
  have h := LogdetLean.integral_rpow_mul_exp_neg_mul_gammaMeasure
    (a := a) (r := r) (t := 0) (c := -s) ha hr (by simpa using ha) hrate
  simp only [Real.rpow_zero, one_mul, neg_neg, add_zero] at h
  rw [h]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hrate0 : r - s ≠ 0 := (sub_pos.mpr hs).ne'
  rw [show r + -s = r - s by ring]
  rw [div_rpow hr.le (sub_pos.mpr hs).le]
  field_simp [hGa, hrate0]

theorem integrable_exp_mul_id_gammaMeasure {a r s : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hs : s < r) :
    Integrable (fun x : ℝ ↦ Real.exp (s * x)) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  change mgf id (gammaMeasure a r) s ≠ 0
  rw [mgf_id_gammaMeasure ha hr hs]
  exact (Real.rpow_pos_of_pos (div_pos hr (sub_pos.mpr hs)) a).ne'

/-- Raw Gamma upper-tail Chernoff inequality with the exact MGF. -/
theorem gammaMeasure_ge_le_exp_mul_rpow
    {a r s eps : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hs0 : 0 ≤ s) (hsr : s < r) :
    (gammaMeasure a r).real {x : ℝ | eps ≤ x} ≤
      Real.exp (-s * eps) * (r / (r - s)) ^ a := by
  let _ : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  have h := measure_ge_le_exp_mul_mgf
    (X := id) (μ := gammaMeasure a r) eps hs0
    (integrable_exp_mul_id_gammaMeasure ha hr hsr)
  simpa [mgf_id_gammaMeasure ha hr hsr] using h

/-- Raw Gamma lower-tail Chernoff inequality with the exact MGF. -/
theorem gammaMeasure_le_le_exp_mul_rpow
    {a r s eps : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hs0 : s ≤ 0) :
    (gammaMeasure a r).real {x : ℝ | x ≤ eps} ≤
      Real.exp (-s * eps) * (r / (r - s)) ^ a := by
  let _ : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  have hsr : s < r := lt_of_le_of_lt hs0 hr
  have h := measure_le_le_exp_mul_mgf
    (X := id) (μ := gammaMeasure a r) eps hs0
    (integrable_exp_mul_id_gammaMeasure ha hr hsr)
  simpa [mgf_id_gammaMeasure ha hr hsr] using h

/-- A second-order upper bound for `-log (1-x)` on `[0,1)`. -/
theorem neg_log_one_sub_le_add_sq_div
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x ^ 2 / (2 * (1 - x)) := by
  let y : ℝ := x / (1 - x)
  have hden : 0 < 1 - x := sub_pos.mpr hx1
  have hy0 : 0 ≤ y := div_nonneg hx0 hden.le
  have h := LogdetLean.log_one_add_le_rational hy0
  have hone : 1 + y = 1 / (1 - x) := by
    dsimp [y]
    field_simp [hden.ne']
    ring
  rw [hone, one_div, Real.log_inv] at h
  dsimp [y] at h
  convert h using 1
  field_simp [hden.ne']

/-- A convenient quadratic upper bound for `-log (1-x)` on `[0,1/2]`. -/
theorem neg_log_one_sub_le_add_sq
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + x ^ 2 := by
  have hx1 : x < 1 := lt_of_le_of_lt hxhalf (by norm_num)
  have h := neg_log_one_sub_le_add_sq_div hx0 hx1
  have hden : 0 < 2 * (1 - x) := mul_pos (by norm_num) (sub_pos.mpr hx1)
  have hfrac : x ^ 2 / (2 * (1 - x)) ≤ x ^ 2 := by
    rw [div_le_iff₀ hden]
    have hsquare : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  linarith

/-- A simple multiplicative upper-tail bound for a chi-square law. -/
theorem chiSquare_upperTail_le
    {k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real
        {x : ℝ | (k : ℝ) * (1 + delta) ≤ x} ≤
      Real.exp (-((k : ℝ) * delta ^ 2 / 8)) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha : 0 < (k : ℝ) / 2 := by positivity
  have hs0 : 0 ≤ delta / 4 := by positivity
  have hsr : delta / 4 < (1 / 2 : ℝ) := by linarith
  have hchernoff := gammaMeasure_ge_le_exp_mul_rpow
    (a := (k : ℝ) / 2) (r := 1 / 2) (s := delta / 4)
    (eps := (k : ℝ) * (1 + delta)) ha (by norm_num) hs0 hsr
  refine hchernoff.trans ?_
  have hbase : 0 < (1 / 2 : ℝ) / (1 / 2 - delta / 4) := by
    positivity
  rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hx0 : 0 ≤ delta / 2 := by positivity
  have hxhalf : delta / 2 ≤ (1 / 2 : ℝ) := by linarith
  have hlog := neg_log_one_sub_le_add_sq hx0 hxhalf
  have hbaseEq :
      (1 / 2 : ℝ) / (1 / 2 - delta / 4) =
        1 / (1 - delta / 2) := by
    have hden : 0 < 1 / 2 - delta / 4 := by linarith
    have hden' : 0 < 1 - delta / 2 := by linarith
    have hden'' : 0 < 2 - delta := by linarith
    rw [div_eq_iff hden.ne']
    field_simp [hden'.ne', hden''.ne']
    ring
  rw [hbaseEq, one_div, Real.log_inv]
  nlinarith [sq_nonneg delta]

/-- A simple multiplicative lower-tail bound for a chi-square law. -/
theorem chiSquare_lowerTail_le
    {k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) :
    (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real
        {x : ℝ | x ≤ (k : ℝ) * (1 - delta)} ≤
      Real.exp (-((k : ℝ) * delta ^ 2 / 4)) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha : 0 < (k : ℝ) / 2 := by positivity
  have hs0 : -(delta / 2) ≤ 0 := neg_nonpos.mpr (by positivity)
  have hchernoff := gammaMeasure_le_le_exp_mul_rpow
    (a := (k : ℝ) / 2) (r := 1 / 2) (s := -(delta / 2))
    (eps := (k : ℝ) * (1 - delta)) ha (by norm_num) hs0
  refine hchernoff.trans ?_
  have hdenBase : 0 < (1 / 2 : ℝ) - -(delta / 2) := by
    linarith
  have hbase : 0 < (1 / 2 : ℝ) / (1 / 2 - -(delta / 2)) :=
    div_pos (by norm_num) hdenBase
  rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog := LogdetLean.sub_half_sq_le_log_one_add hdelta0
  have hbaseEq :
      (1 / 2 : ℝ) / (1 / 2 - -(delta / 2)) =
        1 / (1 + delta) := by
    have hden : 0 < 1 / 2 - -(delta / 2) := hdenBase
    have hden' : 0 < 1 + delta := by linarith
    field_simp [hden.ne', hden'.ne']
    ring
  rw [hbaseEq, one_div, Real.log_inv]
  nlinarith [sq_nonneg delta]

/-- A Gamma random variable is strictly positive almost surely. -/
theorem ae_pos_gammaMeasure' (a r : ℝ) :
    ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [gammaMeasure]
  refine (ae_withDensity_iff
    (measurable_gammaPDFReal a r).ennreal_ofReal).2 ?_
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with x hx0
  intro hpdf
  by_contra hx
  apply hpdf
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
  rw [gammaPDFReal, if_neg (not_le.mpr hxneg), ENNReal.ofReal_zero]

/-- The normalized chi coordinate `A / sqrt(k)`. -/
def normalizedChiCoordinate (k : ℕ) (A : ℝ) : ℝ :=
  A / Real.sqrt (k : ℝ)

/-- Failure of the radius-`2u` normalized chi event. -/
def normalizedChiBadSet (k : ℕ) (u : ℝ) : Set ℝ :=
  {A : ℝ | 2 * u < |normalizedChiCoordinate k A - 1|}

theorem measurableSet_normalizedChiBadSet (k : ℕ) (u : ℝ) :
    MeasurableSet (normalizedChiBadSet k u) := by
  unfold normalizedChiBadSet normalizedChiCoordinate
  exact measurableSet_lt measurable_const
    (((measurable_id'.div_const _).sub_const _).abs)

/-- Exponential concentration for the square-root image of a chi-square
Gamma law.  The constant `2` in the exponent is deliberately conservative
and is more than enough for the later Pearson good-event truncation. -/
theorem gammaMeasure_preimage_normalizedChiBadSet_le
    {k : ℕ} (hk : 0 < k) {u : ℝ}
    (hu0 : 0 ≤ u) (huquarter : u ≤ 1 / 4) :
    (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real
        (Real.sqrt ⁻¹' normalizedChiBadSet k u) ≤
      2 * Real.exp (-2 * (k : ℝ) * u ^ 2) := by
  let mu : Measure ℝ := gammaMeasure ((k : ℝ) / 2) (1 / 2)
  let bad : Set ℝ := Real.sqrt ⁻¹' normalizedChiBadSet k u
  let lower : Set ℝ := {x : ℝ | x ≤ (k : ℝ) * (1 - 3 * u)}
  let upper : Set ℝ := {x : ℝ | (k : ℝ) * (1 + 4 * u) ≤ x}
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsqrtk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkR
  let _ : IsProbabilityMeasure mu := by
    dsimp [mu]
    exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have hpos : ∀ᵐ x ∂mu, 0 < x := by
    simpa [mu] using ae_pos_gammaMeasure' ((k : ℝ) / 2) (1 / 2)
  have hbadCongr : ∀ᵐ x ∂mu,
      (x ∈ bad) = (x ∈ bad ∩ Ici 0) := by
    filter_upwards [hpos] with x hx
    apply propext
    constructor
    · intro hxbad
      exact ⟨hxbad, hx.le⟩
    · exact fun h ↦ h.1
  have hsubset : bad ∩ Ici 0 ⊆ lower ∪ upper := by
    intro x hx
    rcases hx with ⟨hbad, hx0⟩
    change 2 * u <
      |Real.sqrt x / Real.sqrt (k : ℝ) - 1| at hbad
    have hsqrtx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hratio0 : 0 ≤ Real.sqrt x / Real.sqrt (k : ℝ) :=
      div_nonneg hsqrtx0 hsqrtk.le
    have hratioSq :
        (Real.sqrt x / Real.sqrt (k : ℝ)) ^ 2 = x / (k : ℝ) := by
      rw [div_pow, Real.sq_sqrt hx0, Real.sq_sqrt hkR.le]
    rcases (lt_abs.mp hbad) with hupper | hlower
    · right
      change (k : ℝ) * (1 + 4 * u) ≤ x
      have hratio : 1 + 2 * u <
          Real.sqrt x / Real.sqrt (k : ℝ) := by linarith
      have hbase0 : 0 ≤ 1 + 2 * u := by positivity
      have hsq : (1 + 2 * u) ^ 2 <
          (Real.sqrt x / Real.sqrt (k : ℝ)) ^ 2 :=
        (sq_lt_sq₀ hbase0 hratio0).2 hratio
      rw [hratioSq] at hsq
      have : 1 + 4 * u ≤ x / (k : ℝ) := by
        nlinarith [sq_nonneg u]
      simpa [mul_comm] using (le_div_iff₀ hkR).mp this
    · left
      change x ≤ (k : ℝ) * (1 - 3 * u)
      have hratio : Real.sqrt x / Real.sqrt (k : ℝ) <
          1 - 2 * u := by linarith
      have hright0 : 0 ≤ 1 - 2 * u := by linarith
      have hsq :
          (Real.sqrt x / Real.sqrt (k : ℝ)) ^ 2 <
            (1 - 2 * u) ^ 2 :=
        (sq_lt_sq₀ hratio0 hright0).2 hratio
      rw [hratioSq] at hsq
      have huSq : 4 * u ^ 2 ≤ u := by nlinarith
      have : x / (k : ℝ) ≤ 1 - 3 * u := by
        nlinarith
      simpa [mul_comm] using (div_le_iff₀ hkR).mp this
  have hlower := chiSquare_lowerTail_le hk
    (delta := 3 * u) (by positivity : 0 ≤ 3 * u)
  have hupper := chiSquare_upperTail_le hk
    (delta := 4 * u) (by positivity : 0 ≤ 4 * u)
    (by linarith : 4 * u ≤ 1)
  have hlowerExp :
      Real.exp (-((k : ℝ) * (3 * u) ^ 2 / 4)) ≤
        Real.exp (-2 * (k : ℝ) * u ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hkR.le (sq_nonneg u)]
  have hupperExp :
      Real.exp (-((k : ℝ) * (4 * u) ^ 2 / 8)) =
        Real.exp (-2 * (k : ℝ) * u ^ 2) := by
    congr 1
    ring
  calc
    mu.real bad = mu.real (bad ∩ Ici 0) :=
      MeasureTheory.measureReal_congr hbadCongr
    _ ≤ mu.real (lower ∪ upper) :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ mu.real lower + mu.real upper :=
      MeasureTheory.measureReal_union_le lower upper
    _ ≤ Real.exp (-((k : ℝ) * (3 * u) ^ 2 / 4)) +
          Real.exp (-((k : ℝ) * (4 * u) ^ 2 / 8)) := by
      exact add_le_add (by simpa [mu, lower] using hlower)
        (by simpa [mu, upper] using hupper)
    _ ≤ Real.exp (-2 * (k : ℝ) * u ^ 2) +
          Real.exp (-2 * (k : ℝ) * u ^ 2) := by
      exact add_le_add hlowerExp hupperExp.le
    _ = 2 * Real.exp (-2 * (k : ℝ) * u ^ 2) := by ring

/-- Normalized chi-radius concentration under the project's canonical chi
law. -/
theorem chiMeasure_normalizedChiBadSet_le
    {k : ℕ} (hk : 0 < k) {u : ℝ}
    (hu0 : 0 ≤ u) (huquarter : u ≤ 1 / 4) :
    (chiMeasure k).real (normalizedChiBadSet k u) ≤
      2 * Real.exp (-2 * (k : ℝ) * u ^ 2) := by
  rw [chiMeasure, measureReal_def,
    Measure.map_apply Real.continuous_sqrt.measurable
      (measurableSet_normalizedChiBadSet k u),
    ← measureReal_def]
  exact gammaMeasure_preimage_normalizedChiBadSet_le hk hu0 huquarter

/-- Radius parameter used simultaneously for `A/sqrt(m)` and
`B/sqrt(m-1)` in Ruben's representation. -/
def pearsonChiRadius (m : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (t / ((m : ℝ) - 1))

/-- The union of the two normalized chi bad events for independent
`A ~ chi_m` and `B ~ chi_(m-1)`. -/
def normalizedChiPairBadSet (m : ℕ) (u : ℝ) : Set (ℝ × ℝ) :=
  Prod.fst ⁻¹' normalizedChiBadSet m u ∪
    Prod.snd ⁻¹' normalizedChiBadSet (m - 1) u

theorem measurableSet_normalizedChiPairBadSet (m : ℕ) (u : ℝ) :
    MeasurableSet (normalizedChiPairBadSet m u) := by
  exact ((measurableSet_normalizedChiBadSet m u).preimage measurable_fst).union
    ((measurableSet_normalizedChiBadSet (m - 1) u).preimage measurable_snd)

/-- The first chi coordinate obeys the common Pearson radius calibrated by
the smaller degrees of freedom `m-1`. -/
theorem chiMeasure_m_pearsonChiRadius_bad_le
    {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (hradius : pearsonChiRadius m t ≤ 1 / 4) :
    (chiMeasure m).real
        (normalizedChiBadSet m (pearsonChiRadius m t)) ≤
      2 * Real.exp (-2 * t) := by
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by positivity
  have hm1R : 0 < (m : ℝ) - 1 := by
    have hmR2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hu0 : 0 ≤ pearsonChiRadius m t := Real.sqrt_nonneg _
  have hraw := chiMeasure_normalizedChiBadSet_le hm0 hu0 hradius
  refine hraw.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  apply Real.exp_le_exp.mpr
  have hsquare : pearsonChiRadius m t ^ 2 =
      t / ((m : ℝ) - 1) := by
    unfold pearsonChiRadius
    rw [Real.sq_sqrt (div_nonneg ht hm1R.le)]
  rw [hsquare]
  have hratioEq :
      (m : ℝ) * (t / ((m : ℝ) - 1)) =
        t + t / ((m : ℝ) - 1) := by
    field_simp [hm1R.ne']
    ring
  have hratio : t ≤ (m : ℝ) * (t / ((m : ℝ) - 1)) := by
    rw [hratioEq]
    exact le_add_of_nonneg_right (div_nonneg ht hm1R.le)
  nlinarith

/-- The second chi coordinate, with `m-1` degrees of freedom, obeys the
same common Pearson radius. -/
theorem chiMeasure_pred_pearsonChiRadius_bad_le
    {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (hradius : pearsonChiRadius m t ≤ 1 / 4) :
    (chiMeasure (m - 1)).real
        (normalizedChiBadSet (m - 1) (pearsonChiRadius m t)) ≤
      2 * Real.exp (-2 * t) := by
  have hpred : 0 < m - 1 := by omega
  have hm1R : 0 < (m : ℝ) - 1 := by
    have hmR2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hu0 : 0 ≤ pearsonChiRadius m t := Real.sqrt_nonneg _
  have hraw := chiMeasure_normalizedChiBadSet_le hpred hu0 hradius
  refine hraw.trans ?_
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hsquare : pearsonChiRadius m t ^ 2 =
      t / ((m : ℝ) - 1) := by
    unfold pearsonChiRadius
    rw [Real.sq_sqrt (div_nonneg ht hm1R.le)]
  rw [hcast, hsquare]
  have hprod :
      ((m : ℝ) - 1) * (t / ((m : ℝ) - 1)) = t := by
    field_simp [hm1R.ne']
  have hexponent :
      -2 * ((m : ℝ) - 1) * (t / ((m : ℝ) - 1)) =
        -2 * t := by
    rw [mul_assoc, hprod]
  rw [hexponent]

/-- Simultaneous normalized chi-radius concentration for the two independent
Ruben radii `U=A/sqrt(m)` and `V=B/sqrt(m-1)`. -/
theorem chiMeasure_prod_normalizedChiPairBadSet_le
    {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (hradius : pearsonChiRadius m t ≤ 1 / 4) :
    ((chiMeasure m).prod (chiMeasure (m - 1))).real
        (normalizedChiPairBadSet m (pearsonChiRadius m t)) ≤
      4 * Real.exp (-2 * t) := by
  let muA : Measure ℝ := chiMeasure m
  let muB : Measure ℝ := chiMeasure (m - 1)
  let badA : Set ℝ := normalizedChiBadSet m (pearsonChiRadius m t)
  let badB : Set ℝ := normalizedChiBadSet (m - 1) (pearsonChiRadius m t)
  let _ : IsProbabilityMeasure muA := by
    dsimp [muA, chiMeasure]
    let _ : IsProbabilityMeasure
        (gammaMeasure ((m : ℝ) / 2) (1 / 2)) :=
      isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
    exact Measure.isProbabilityMeasure_map
      Real.continuous_sqrt.measurable.aemeasurable
  let _ : IsProbabilityMeasure muB := by
    dsimp [muB, chiMeasure]
    have hpred : 0 < m - 1 := by omega
    let _ : IsProbabilityMeasure
        (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)) :=
      isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
    exact Measure.isProbabilityMeasure_map
      Real.continuous_sqrt.measurable.aemeasurable
  have hbadA : MeasurableSet badA := by
    simpa [badA] using
      measurableSet_normalizedChiBadSet m (pearsonChiRadius m t)
  have hbadB : MeasurableSet badB := by
    simpa [badB] using
      measurableSet_normalizedChiBadSet (m - 1) (pearsonChiRadius m t)
  have hfst : (muA.prod muB).real (Prod.fst ⁻¹' badA) = muA.real badA := by
    rw [measureReal_def, ← Measure.map_apply measurable_fst hbadA,
      Measure.map_fst_prod, measure_univ, one_smul, ← measureReal_def]
  have hsnd : (muA.prod muB).real (Prod.snd ⁻¹' badB) = muB.real badB := by
    rw [measureReal_def, ← Measure.map_apply measurable_snd hbadB,
      Measure.map_snd_prod, measure_univ, one_smul, ← measureReal_def]
  have hA := chiMeasure_m_pearsonChiRadius_bad_le hm ht hradius
  have hB := chiMeasure_pred_pearsonChiRadius_bad_le hm ht hradius
  calc
    (muA.prod muB).real
        (normalizedChiPairBadSet m (pearsonChiRadius m t)) =
        (muA.prod muB).real
          (Prod.fst ⁻¹' badA ∪ Prod.snd ⁻¹' badB) := by
      rfl
    _ ≤ (muA.prod muB).real (Prod.fst ⁻¹' badA) +
          (muA.prod muB).real (Prod.snd ⁻¹' badB) :=
      MeasureTheory.measureReal_union_le _ _
    _ = muA.real badA + muB.real badB := by rw [hfst, hsnd]
    _ ≤ 2 * Real.exp (-2 * t) + 2 * Real.exp (-2 * t) := by
      exact add_le_add (by simpa [muA, badA] using hA)
        (by simpa [muB, badB] using hB)
    _ = 4 * Real.exp (-2 * t) := by ring

end

end LogdetLean.Coherence
