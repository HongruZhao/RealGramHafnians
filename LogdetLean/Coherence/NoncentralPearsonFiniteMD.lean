import LogdetLean.Coherence.NoncentralPearsonTailMixture
import LogdetLean.Coherence.StandardGaussianMills
import LogdetLean.Coherence.GammaChernoff
import Mathlib.Tactic
/-!
# Finite-sample noncentral Pearson moderate-deviation comparison

This file combines the proved Gaussian-tail perturbation estimate with the
proved concentration of the two independent chi radii in Ruben coordinates.
The main theorem is deliberately finite-sample: it bounds the exact
two-radius Gaussian-tail mixture before any asymptotic rate algebra is used.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set

/-- The common deterministic perturbation exponent for a Gaussian upper
tail whose argument moves by at most `delta`. -/
def gaussianTailPerturbationExponent (x delta : ℝ) : ℝ :=
  Real.exp 2 * delta * (1 + |x| + delta)

theorem gaussianTailPerturbationExponent_nonneg
    {x delta : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ gaussianTailPerturbationExponent x delta := by
  unfold gaussianTailPerturbationExponent
  positivity

theorem standardGaussianUpperTail_le_one (x : ℝ) :
    standardGaussianUpperTail x ≤ 1 := by
  unfold standardGaussianUpperTail
  linarith [cdf_nonneg (gaussianReal 0 1) x]

theorem measurable_standardGaussianUpperTail :
    Measurable standardGaussianUpperTail := by
  unfold standardGaussianUpperTail
  exact measurable_const.sub (monotone_cdf (gaussianReal 0 1)).measurable

theorem integrable_standardGaussianUpperTail_comp
    {S : Type*} [MeasurableSpace S] (mu : Measure S)
    [IsFiniteMeasure mu] {f : S → ℝ} (hf : Measurable f) :
    Integrable (fun w ↦ standardGaussianUpperTail (f w)) mu := by
  apply (integrable_const (1 : ℝ)).mono
  · exact (measurable_standardGaussianUpperTail.comp hf).aestronglyMeasurable
  · filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg
      (standardGaussianUpperTail_nonneg (f w)), norm_one]
    exact standardGaussianUpperTail_le_one (f w)

/-- A bounded perturbation of a Gaussian-tail argument changes the tail by
at most the width of the corresponding proved multiplicative envelope. -/
theorem abs_standardGaussianUpperTail_add_sub_le_of_abs_le
    {x h delta : ℝ} (hdelta : 0 ≤ delta) (hh : |h| ≤ delta) :
    |standardGaussianUpperTail (x + h) - standardGaussianUpperTail x| ≤
      standardGaussianUpperTail x *
        (Real.exp (gaussianTailPerturbationExponent x delta) -
          Real.exp (-gaussianTailPerturbationExponent x delta)) := by
  let Eh : ℝ := Real.exp 2 * |h| * (1 + |x| + |h|)
  let E : ℝ := gaussianTailPerturbationExponent x delta
  have hEh0 : 0 ≤ Eh := by
    dsimp [Eh]
    positivity
  have hE0 : 0 ≤ E := by
    exact gaussianTailPerturbationExponent_nonneg hdelta
  have hfac : 1 + |x| + |h| ≤ 1 + |x| + delta := by linarith
  have hEhle : Eh ≤ E := by
    dsimp [Eh, E, gaussianTailPerturbationExponent]
    have hleft : Real.exp 2 * |h| ≤ Real.exp 2 * delta := by
      exact mul_le_mul_of_nonneg_left hh (Real.exp_pos 2).le
    exact mul_le_mul hleft hfac (by positivity) (by positivity)
  obtain ⟨hlow, hupp⟩ :=
    standardGaussianUpperTail_multiplicative_perturbation x h
  change standardGaussianUpperTail x * Real.exp (-Eh) ≤
      standardGaussianUpperTail (x + h) at hlow
  change standardGaussianUpperTail (x + h) ≤
      standardGaussianUpperTail x * Real.exp Eh at hupp
  have hlowE : standardGaussianUpperTail x * Real.exp (-E) ≤
      standardGaussianUpperTail (x + h) := by
    apply le_trans ?_ hlow
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg hEhle))
      (standardGaussianUpperTail_nonneg x)
  have huppE : standardGaussianUpperTail (x + h) ≤
      standardGaussianUpperTail x * Real.exp E := by
    exact hupp.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hEhle) (standardGaussianUpperTail_nonneg x))
  have hexpneg : Real.exp (-E) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr hE0)
  have honeexp : 1 ≤ Real.exp E := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hE0
  have hQ0 : 0 ≤ standardGaussianUpperTail x :=
    standardGaussianUpperTail_nonneg x
  rw [abs_le]
  constructor <;> nlinarith

/-- Abstract finite good-event truncation.  It is the analytic core of the
Pearson estimate: on the good event, use the proved relative Gaussian-tail
bound; on its complement, pay only its probability. -/
theorem abs_integral_standardGaussianUpperTail_sub_le_goodEvent
    {S : Type*} [MeasurableSpace S]
    (mu : Measure S) [IsProbabilityMeasure mu]
    {f : S → ℝ} (hf : Measurable f) (bad : Set S) (hbad : MeasurableSet bad)
    {x delta beta : ℝ} (hdelta : 0 ≤ delta) (_hbeta : 0 ≤ beta)
    (hbadProb : mu.real bad ≤ beta)
    (hgood : ∀ w ∉ bad, |f w - x| ≤ delta) :
    |(∫ w, standardGaussianUpperTail (f w) ∂mu) -
        standardGaussianUpperTail x| ≤
      standardGaussianUpperTail x *
          (Real.exp (gaussianTailPerturbationExponent x delta) -
            Real.exp (-gaussianTailPerturbationExponent x delta)) + beta := by
  let C : ℝ := standardGaussianUpperTail x *
    (Real.exp (gaussianTailPerturbationExponent x delta) -
      Real.exp (-gaussianTailPerturbationExponent x delta))
  have hE0 : 0 ≤ gaussianTailPerturbationExponent x delta :=
    gaussianTailPerturbationExponent_nonneg hdelta
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hexp : Real.exp (-gaussianTailPerturbationExponent x delta) ≤
        Real.exp (gaussianTailPerturbationExponent x delta) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_nonneg (standardGaussianUpperTail_nonneg x)
      (sub_nonneg.mpr hexp)
  have hQf : Integrable (fun w ↦ standardGaussianUpperTail (f w)) mu :=
    integrable_standardGaussianUpperTail_comp mu hf
  have hdiff : Integrable
      (fun w ↦ standardGaussianUpperTail (f w) -
        standardGaussianUpperTail x) mu :=
    hQf.sub (integrable_const _)
  have hmajor : Integrable (fun w ↦ C + bad.indicator (fun _ ↦ (1 : ℝ)) w) mu :=
    (integrable_const C).add ((integrable_const (1 : ℝ)).indicator hbad)
  have hindicator :
      (∫ w, bad.indicator (fun _ ↦ (1 : ℝ)) w ∂mu) = mu.real bad := by
    exact integral_indicator_one hbad
  have hpoint : ∀ w,
      |standardGaussianUpperTail (f w) - standardGaussianUpperTail x| ≤
        C + bad.indicator (fun _ ↦ (1 : ℝ)) w := by
    intro w
    by_cases hw : w ∈ bad
    · rw [indicator_of_mem hw]
      have hleft :
          |standardGaussianUpperTail (f w) - standardGaussianUpperTail x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [standardGaussianUpperTail_nonneg (f w),
            standardGaussianUpperTail_le_one x]
        · linarith [standardGaussianUpperTail_le_one (f w),
            standardGaussianUpperTail_nonneg x]
      linarith
    · rw [indicator_of_notMem hw, add_zero]
      have hpert := abs_standardGaussianUpperTail_add_sub_le_of_abs_le
        (x := x) (h := f w - x) hdelta (hgood w hw)
      simpa [C, sub_add_cancel] using hpert
  calc
    |(∫ w, standardGaussianUpperTail (f w) ∂mu) -
        standardGaussianUpperTail x| =
        |∫ w, (standardGaussianUpperTail (f w) -
          standardGaussianUpperTail x) ∂mu| := by
      rw [integral_sub hQf (integrable_const _), integral_const, probReal_univ]
      simp
    _ ≤ ∫ w, |standardGaussianUpperTail (f w) -
          standardGaussianUpperTail x| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤ ∫ w, (C + bad.indicator (fun _ ↦ (1 : ℝ)) w) ∂mu := by
      apply integral_mono_ae hdiff.abs hmajor
      filter_upwards [] with w
      exact hpoint w
    _ = C + mu.real bad := by
      rw [integral_add (integrable_const C)
        ((integrable_const (1 : ℝ)).indicator hbad), integral_const,
        probReal_univ, one_smul, hindicator]
    _ ≤ C + beta := by linarith
    _ = standardGaussianUpperTail x *
          (Real.exp (gaussianTailPerturbationExponent x delta) -
            Real.exp (-gaussianTailPerturbationExponent x delta)) + beta := rfl

/-! ## Specialization to the two Ruben chi radii -/

/-- Conditional Gaussian-tail argument written with two normalized chi
radii.  Taking `theta = -lambda` gives the upper signed Pearson tail, while
`theta = lambda` gives the reflected lower signed tail. -/
def normalizedRubenTailArgument (m : ℕ) (q theta : ℝ)
    (w : ℝ × ℝ) : ℝ :=
  q * normalizedChiCoordinate (m - 1) w.2 +
    theta * normalizedChiCoordinate m w.1

theorem measurable_normalizedRubenTailArgument (m : ℕ) (q theta : ℝ) :
    Measurable (normalizedRubenTailArgument m q theta) := by
  unfold normalizedRubenTailArgument normalizedChiCoordinate
  fun_prop

/-- On simultaneous normalized-chi concentration, the conditional Gaussian
argument is uniformly close to its deterministic noncentral limit argument. -/
theorem normalizedRubenTailArgument_sub_le_of_notMem_pairBad
    {m : ℕ} {q theta u : ℝ} {w : ℝ × ℝ}
    (hw : w ∉ normalizedChiPairBadSet m u) :
    |normalizedRubenTailArgument m q theta w - (q + theta)| ≤
      2 * u * (|q| + |theta|) := by
  have hnotA : w.1 ∉ normalizedChiBadSet m u := by
    intro hA
    exact hw (Or.inl hA)
  have hnotB : w.2 ∉ normalizedChiBadSet (m - 1) u := by
    intro hB
    exact hw (Or.inr hB)
  have hA : |normalizedChiCoordinate m w.1 - 1| ≤ 2 * u := by
    unfold normalizedChiBadSet at hnotA
    exact le_of_not_gt hnotA
  have hB : |normalizedChiCoordinate (m - 1) w.2 - 1| ≤ 2 * u := by
    unfold normalizedChiBadSet at hnotB
    exact le_of_not_gt hnotB
  have hsplit :
      normalizedRubenTailArgument m q theta w - (q + theta) =
        q * (normalizedChiCoordinate (m - 1) w.2 - 1) +
          theta * (normalizedChiCoordinate m w.1 - 1) := by
    unfold normalizedRubenTailArgument
    ring
  rw [hsplit]
  calc
    |q * (normalizedChiCoordinate (m - 1) w.2 - 1) +
        theta * (normalizedChiCoordinate m w.1 - 1)| ≤
        |q * (normalizedChiCoordinate (m - 1) w.2 - 1)| +
          |theta * (normalizedChiCoordinate m w.1 - 1)| :=
      abs_add_le _ _
    _ = |q| * |normalizedChiCoordinate (m - 1) w.2 - 1| +
          |theta| * |normalizedChiCoordinate m w.1 - 1| := by
      rw [abs_mul, abs_mul]
    _ ≤ |q| * (2 * u) + |theta| * (2 * u) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hB (abs_nonneg q))
        (mul_le_mul_of_nonneg_left hA (abs_nonneg theta))
    _ = 2 * u * (|q| + |theta|) := by ring

/-- The exact normalized two-chi Gaussian-tail mixture. -/
def normalizedRubenTailMixture (m : ℕ) (q theta : ℝ) : ℝ :=
  ∫ w, standardGaussianUpperTail
      (normalizedRubenTailArgument m q theta w)
    ∂((chiMeasure m).prod (chiMeasure (m - 1)))

theorem isProbabilityMeasure_chiMeasure_of_pos'
    (k : ℕ) (hk : 0 < k) : IsProbabilityMeasure (chiMeasure k) := by
  unfold chiMeasure
  let _ : IsProbabilityMeasure
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  exact Measure.isProbabilityMeasure_map
    Real.continuous_sqrt.measurable.aemeasurable

/-- Natural signed noncentrality in the normalized Ruben coordinates. -/
def pearsonRubenNoncentrality (m : ℕ) (rho : ℝ) : ℝ :=
  Real.sqrt (m : ℝ) * populationCorrelationOdds rho

theorem normalizedRubenTailArgument_upper_eq
    {m : ℕ} (hm : 2 ≤ m) (rho q a b2 : ℝ) :
    normalizedRubenTailArgument m q (-pearsonRubenNoncentrality m rho)
        (a, Real.sqrt b2) =
      rubenUpperTailArgument m rho q a b2 := by
  have hm0 : 0 < (m : ℝ) := by positivity
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  unfold normalizedRubenTailArgument normalizedChiCoordinate
    pearsonRubenNoncentrality rubenUpperTailArgument rubenTailScale
  have hcast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  rw [hcast]
  field_simp [hsqrtm.ne']
  ring

theorem normalizedRubenTailArgument_lower_eq
    {m : ℕ} (hm : 2 ≤ m) (rho q a b2 : ℝ) :
    normalizedRubenTailArgument m q (pearsonRubenNoncentrality m rho)
        (a, Real.sqrt b2) =
      rubenLowerTailArgument m rho q a b2 := by
  have hm0 : 0 < (m : ℝ) := by positivity
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  unfold normalizedRubenTailArgument normalizedChiCoordinate
    pearsonRubenNoncentrality rubenLowerTailArgument rubenTailScale
  have hcast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  rw [hcast]
  field_simp [hsqrtm.ne']

/-- Genuine finite-sample comparison for the normalized Ruben mixture.
The error is a relative Gaussian perturbation envelope plus the proved
probability `4 exp(-2t)` of discarding either chi radius. -/
theorem normalizedRubenTailMixture_finite_comparison
    {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (hradius : pearsonChiRadius m t ≤ 1 / 4)
    (q theta : ℝ) :
    |normalizedRubenTailMixture m q theta -
        standardGaussianUpperTail (q + theta)| ≤
      standardGaussianUpperTail (q + theta) *
        (Real.exp (gaussianTailPerturbationExponent (q + theta)
          (2 * pearsonChiRadius m t * (|q| + |theta|))) -
        Real.exp (-gaussianTailPerturbationExponent (q + theta)
          (2 * pearsonChiRadius m t * (|q| + |theta|)))) +
      4 * Real.exp (-2 * t) := by
  let muA : Measure ℝ := chiMeasure m
  let muB : Measure ℝ := chiMeasure (m - 1)
  let mu : Measure (ℝ × ℝ) := muA.prod muB
  let u : ℝ := pearsonChiRadius m t
  let bad : Set (ℝ × ℝ) := normalizedChiPairBadSet m u
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
  let _ : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hu0 : 0 ≤ u := by
    dsimp [u, pearsonChiRadius]
    positivity
  have hdelta0 : 0 ≤ 2 * u * (|q| + |theta|) := by positivity
  have hbadMeas : MeasurableSet bad := by
    simpa [bad, u] using
      measurableSet_normalizedChiPairBadSet m (pearsonChiRadius m t)
  have hbadProb : mu.real bad ≤ 4 * Real.exp (-2 * t) := by
    simpa [mu, muA, muB, bad, u] using
      chiMeasure_prod_normalizedChiPairBadSet_le hm ht hradius
  have h := abs_integral_standardGaussianUpperTail_sub_le_goodEvent
    mu (measurable_normalizedRubenTailArgument m q theta)
    bad hbadMeas hdelta0 (by positivity : 0 ≤ 4 * Real.exp (-2 * t))
    hbadProb (fun w hw ↦
      normalizedRubenTailArgument_sub_le_of_notMem_pairBad hw)
  simpa [normalizedRubenTailMixture, mu, muA, muB, bad, u] using h

private theorem integrable_normalizedRubenTailArgument_tail
    {m : ℕ} (hm : 2 ≤ m) (q theta : ℝ) :
    Integrable (fun w ↦ standardGaussianUpperTail
      (normalizedRubenTailArgument m q theta w))
      ((chiMeasure m).prod (chiMeasure (m - 1))) := by
  let _ : IsProbabilityMeasure (chiMeasure m) :=
    isProbabilityMeasure_chiMeasure_of_pos' m (by omega)
  let _ : IsProbabilityMeasure (chiMeasure (m - 1)) :=
    isProbabilityMeasure_chiMeasure_of_pos' (m - 1) (by omega)
  exact integrable_standardGaussianUpperTail_comp _
    (measurable_normalizedRubenTailArgument m q theta)

/-- Exact upper signed Ruben mixture rewritten on two chi (rather than
chi-times-chi-square) radii. -/
theorem normalizedRubenTailMixture_neg_noncentrality_eq_upperGammaMixture
    {m : ℕ} (hm : 2 ≤ m) (rho q : ℝ) :
    normalizedRubenTailMixture m q (-pearsonRubenNoncentrality m rho) =
      ∫ a, ∫ b2, standardGaussianUpperTail
        (rubenUpperTailArgument m rho q a b2)
        ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
        ∂(chiMeasure m) := by
  let muG : Measure ℝ :=
    gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)
  let f : ℝ × ℝ → ℝ := fun w ↦ standardGaussianUpperTail
    (normalizedRubenTailArgument m q (-pearsonRubenNoncentrality m rho) w)
  have hfmeas : Measurable f :=
    measurable_standardGaussianUpperTail.comp
      (measurable_normalizedRubenTailArgument m q
        (-pearsonRubenNoncentrality m rho))
  have hfint : Integrable f ((chiMeasure m).prod (chiMeasure (m - 1))) :=
    integrable_normalizedRubenTailArgument_tail hm q
      (-pearsonRubenNoncentrality m rho)
  let _ : IsProbabilityMeasure (chiMeasure m) :=
    isProbabilityMeasure_chiMeasure_of_pos' m (by omega)
  let _ : IsProbabilityMeasure (chiMeasure (m - 1)) :=
    isProbabilityMeasure_chiMeasure_of_pos' (m - 1) (by omega)
  let _ : IsProbabilityMeasure muG := by
    dsimp [muG]
    exact isProbabilityMeasure_gammaMeasure
      (by
        have hpred : 0 < m - 1 := by omega
        exact div_pos (Nat.cast_pos.2 hpred) (by norm_num))
      (by norm_num)
  rw [normalizedRubenTailMixture]
  change (∫ w, f w ∂((chiMeasure m).prod (chiMeasure (m - 1)))) = _
  rw [integral_prod _ hfint]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [chiMeasure]
  have hcompInt : Integrable (fun b2 ↦ f (a, Real.sqrt b2)) muG := by
    apply (integrable_const (1 : ℝ)).mono
    · exact (hfmeas.comp
        (measurable_const.prodMk Real.continuous_sqrt.measurable)).aestronglyMeasurable
    · filter_upwards [] with b2
      rw [Real.norm_eq_abs, abs_of_nonneg
        (standardGaussianUpperTail_nonneg _), norm_one]
      exact standardGaussianUpperTail_le_one _
  have himap :
      (∫ y, f (a, y) ∂Measure.map Real.sqrt muG) =
        ∫ b2, f (a, Real.sqrt b2) ∂muG := by
    exact integral_map Real.continuous_sqrt.measurable.aemeasurable
      ((hfmeas.comp (measurable_const.prodMk measurable_id')).aestronglyMeasurable)
  rw [show gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2) = muG by rfl,
    himap]
  apply integral_congr_ae
  filter_upwards [] with b2
  dsimp [f]
  rw [normalizedRubenTailArgument_upper_eq hm]

/-- Exact lower signed Ruben mixture rewritten on two chi radii. -/
theorem normalizedRubenTailMixture_noncentrality_eq_lowerGammaMixture
    {m : ℕ} (hm : 2 ≤ m) (rho q : ℝ) :
    normalizedRubenTailMixture m q (pearsonRubenNoncentrality m rho) =
      ∫ a, ∫ b2, standardGaussianUpperTail
        (rubenLowerTailArgument m rho q a b2)
        ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
        ∂(chiMeasure m) := by
  let muG : Measure ℝ :=
    gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)
  let f : ℝ × ℝ → ℝ := fun w ↦ standardGaussianUpperTail
    (normalizedRubenTailArgument m q (pearsonRubenNoncentrality m rho) w)
  have hfmeas : Measurable f :=
    measurable_standardGaussianUpperTail.comp
      (measurable_normalizedRubenTailArgument m q
        (pearsonRubenNoncentrality m rho))
  have hfint : Integrable f ((chiMeasure m).prod (chiMeasure (m - 1))) :=
    integrable_normalizedRubenTailArgument_tail hm q
      (pearsonRubenNoncentrality m rho)
  let _ : IsProbabilityMeasure (chiMeasure m) :=
    isProbabilityMeasure_chiMeasure_of_pos' m (by omega)
  let _ : IsProbabilityMeasure (chiMeasure (m - 1)) :=
    isProbabilityMeasure_chiMeasure_of_pos' (m - 1) (by omega)
  let _ : IsProbabilityMeasure muG := by
    dsimp [muG]
    exact isProbabilityMeasure_gammaMeasure
      (by
        have hpred : 0 < m - 1 := by omega
        exact div_pos (Nat.cast_pos.2 hpred) (by norm_num))
      (by norm_num)
  rw [normalizedRubenTailMixture]
  change (∫ w, f w ∂((chiMeasure m).prod (chiMeasure (m - 1)))) = _
  rw [integral_prod _ hfint]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [chiMeasure]
  have hcompInt : Integrable (fun b2 ↦ f (a, Real.sqrt b2)) muG := by
    apply (integrable_const (1 : ℝ)).mono
    · exact (hfmeas.comp
        (measurable_const.prodMk Real.continuous_sqrt.measurable)).aestronglyMeasurable
    · filter_upwards [] with b2
      rw [Real.norm_eq_abs, abs_of_nonneg
        (standardGaussianUpperTail_nonneg _), norm_one]
      exact standardGaussianUpperTail_le_one _
  have himap :
      (∫ y, f (a, y) ∂Measure.map Real.sqrt muG) =
        ∫ b2, f (a, Real.sqrt b2) ∂muG := by
    exact integral_map Real.continuous_sqrt.measurable.aemeasurable
      ((hfmeas.comp (measurable_const.prodMk measurable_id')).aestronglyMeasurable)
  rw [show gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2) = muG by rfl,
    himap]
  apply integral_congr_ae
  filter_upwards [] with b2
  dsimp [f]
  rw [normalizedRubenTailArgument_lower_eq hm]

/-! ## Original Gaussian Pearson probabilities -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Sum of the upper and lower signed Pearson-tail probabilities under the
correlated Gaussian construction.  For `q ≥ 0` these are disjoint and the
sum is the usual two-sided tail. -/
def gaussianPearsonTwoSidedTail (m : ℕ) (rho q : ℝ) : ℝ :=
  ((stdGaussian E).prod (stdGaussian E)).real
      {z | q < correlatedSignedPearsonT (E := E) m rho z} +
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | correlatedSignedPearsonT (E := E) m rho z < -q}

theorem correlatedSignedPearsonT_upperTail_eq_normalizedRubenTailMixture
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) (q : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | q < correlatedSignedPearsonT (E := E) m rho z} =
      normalizedRubenTailMixture m q (-pearsonRubenNoncentrality m rho) := by
  rw [correlatedSignedPearsonT_upperTail_eq_gaussianMixture
    m hdim hm rho hrho q]
  rw [normalizedRubenTailMixture_neg_noncentrality_eq_upperGammaMixture
    hm rho q]
  rfl

theorem correlatedSignedPearsonT_lowerTail_eq_normalizedRubenTailMixture
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) (q : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | correlatedSignedPearsonT (E := E) m rho z < -q} =
      normalizedRubenTailMixture m q (pearsonRubenNoncentrality m rho) := by
  rw [correlatedSignedPearsonT_lowerTail_eq_gaussianMixture
    m hdim hm rho hrho q]
  rw [normalizedRubenTailMixture_noncentrality_eq_lowerGammaMixture
    hm rho q]
  rfl

/-- Exact original-Gaussian two-sided probability identity in normalized
Ruben coordinates. -/
theorem gaussianPearsonTwoSidedTail_eq_normalizedRubenMixtures
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) (q : ℝ) :
    gaussianPearsonTwoSidedTail (E := E) m rho q =
      normalizedRubenTailMixture m q (-pearsonRubenNoncentrality m rho) +
        normalizedRubenTailMixture m q (pearsonRubenNoncentrality m rho) := by
  unfold gaussianPearsonTwoSidedTail
  rw [correlatedSignedPearsonT_upperTail_eq_normalizedRubenTailMixture
      m hdim hm rho hrho q,
    correlatedSignedPearsonT_lowerTail_eq_normalizedRubenTailMixture
      m hdim hm rho hrho q]

/-- Finite-sample probability comparison for the original correlated
Gaussian Pearson statistic.  This is the pre-asymptotic theorem: its two
explicit relative perturbation terms and its `8 exp(-2t)` discarded-radius
term are subsequently sent to zero uniformly in the moderate-deviation
window. -/
theorem gaussianPearsonTwoSidedTail_finite_comparison
    {m : ℕ} (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) {t : ℝ} (ht : 0 ≤ t)
    (hradius : pearsonChiRadius m t ≤ 1 / 4) (q : ℝ) :
    let lambda := pearsonRubenNoncentrality m rho
    let delta := 2 * pearsonChiRadius m t * (|q| + |lambda|)
    |gaussianPearsonTwoSidedTail (E := E) m rho q -
        (standardGaussianUpperTail (q - lambda) +
          standardGaussianUpperTail (q + lambda))| ≤
      standardGaussianUpperTail (q - lambda) *
          (Real.exp (gaussianTailPerturbationExponent (q - lambda) delta) -
            Real.exp (-gaussianTailPerturbationExponent (q - lambda) delta)) +
        standardGaussianUpperTail (q + lambda) *
          (Real.exp (gaussianTailPerturbationExponent (q + lambda) delta) -
            Real.exp (-gaussianTailPerturbationExponent (q + lambda) delta)) +
        8 * Real.exp (-2 * t) := by
  dsimp only
  let lambda : ℝ := pearsonRubenNoncentrality m rho
  let delta : ℝ := 2 * pearsonChiRadius m t * (|q| + |lambda|)
  have hupper := normalizedRubenTailMixture_finite_comparison
    hm ht hradius q (-lambda)
  have hlower := normalizedRubenTailMixture_finite_comparison
    hm ht hradius q lambda
  have hdeltaNeg :
      2 * pearsonChiRadius m t * (|q| + |-lambda|) = delta := by
    simp [delta]
  have hdeltaPos :
      2 * pearsonChiRadius m t * (|q| + |lambda|) = delta := rfl
  rw [gaussianPearsonTwoSidedTail_eq_normalizedRubenMixtures
    m hdim hm rho hrho q]
  rw [hdeltaNeg] at hupper
  rw [hdeltaPos] at hlower
  have htriangle :
      |(normalizedRubenTailMixture m q (-lambda) -
          standardGaussianUpperTail (q - lambda)) +
        (normalizedRubenTailMixture m q lambda -
          standardGaussianUpperTail (q + lambda))| ≤
      |normalizedRubenTailMixture m q (-lambda) -
          standardGaussianUpperTail (q - lambda)| +
        |normalizedRubenTailMixture m q lambda -
          standardGaussianUpperTail (q + lambda)| :=
    abs_add_le _ _
  calc
    |normalizedRubenTailMixture m q (-lambda) +
        normalizedRubenTailMixture m q lambda -
      (standardGaussianUpperTail (q - lambda) +
        standardGaussianUpperTail (q + lambda))| =
      |(normalizedRubenTailMixture m q (-lambda) -
          standardGaussianUpperTail (q - lambda)) +
        (normalizedRubenTailMixture m q lambda -
          standardGaussianUpperTail (q + lambda))| := by ring_nf
    _ ≤ |normalizedRubenTailMixture m q (-lambda) -
          standardGaussianUpperTail (q - lambda)| +
        |normalizedRubenTailMixture m q lambda -
          standardGaussianUpperTail (q + lambda)| := htriangle
    _ ≤ (standardGaussianUpperTail (q - lambda) *
          (Real.exp (gaussianTailPerturbationExponent (q - lambda) delta) -
            Real.exp (-gaussianTailPerturbationExponent (q - lambda) delta)) +
          4 * Real.exp (-2 * t)) +
        (standardGaussianUpperTail (q + lambda) *
          (Real.exp (gaussianTailPerturbationExponent (q + lambda) delta) -
            Real.exp (-gaussianTailPerturbationExponent (q + lambda) delta)) +
          4 * Real.exp (-2 * t)) := add_le_add hupper hlower
    _ = standardGaussianUpperTail (q - lambda) *
          (Real.exp (gaussianTailPerturbationExponent (q - lambda) delta) -
            Real.exp (-gaussianTailPerturbationExponent (q - lambda) delta)) +
        standardGaussianUpperTail (q + lambda) *
          (Real.exp (gaussianTailPerturbationExponent (q + lambda) delta) -
            Real.exp (-gaussianTailPerturbationExponent (q + lambda) delta)) +
        8 * Real.exp (-2 * t) := by ring

end

end LogdetLean.Coherence
