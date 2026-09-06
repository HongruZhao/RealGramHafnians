import LogdetLean.Coherence.NoncentralPearsonRuben
import LogdetLean.NormalScaleComparison
import Mathlib.Tactic
/-!
# Exact Gaussian-tail mixtures for noncentral Pearson correlation

This file transports the exact random-axis Ruben product law to the signed
studentized Pearson statistic and integrates out its standard-normal
coordinate.  Every identity is finite-sample and exact; no concentration or
moderate-deviation estimate is used.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The signed studentized statistic associated with two residual columns. -/
def signedPearsonT (m : ℕ) (u v : E) : ℝ :=
  Real.sqrt (((m - 1 : ℕ) : ℝ)) * inner ℝ u v /
    Real.sqrt (twoColumnGramDet u v)

/-- The signed Pearson statistic under the canonical correlated construction. -/
def correlatedSignedPearsonT (m : ℕ) (rho : ℝ) (z : E × E) : ℝ :=
  signedPearsonT m z.1 (correlatedSecondColumn rho z.1 z.2)

/-- The signed Ruben statistic on the independent `(A,Z,B²)` coordinates. -/
def signedRubenCoordinateStatistic (m : ℕ) (rho : ℝ)
    (w : ℝ × (ℝ × ℝ)) : ℝ :=
  Real.sqrt (((m - 1 : ℕ) : ℝ)) *
    (w.2.1 + populationCorrelationOdds rho * w.1) /
      Real.sqrt w.2.2

theorem measurable_correlatedSignedPearsonT (m : ℕ) (rho : ℝ) :
    Measurable (correlatedSignedPearsonT (E := E) m rho) := by
  unfold correlatedSignedPearsonT signedPearsonT twoColumnGramDet
    correlatedSecondColumn
  fun_prop

theorem measurable_signedRubenCoordinateStatistic (m : ℕ) (rho : ℝ) :
    Measurable (signedRubenCoordinateStatistic m rho) := by
  unfold signedRubenCoordinateStatistic populationCorrelationOdds
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise signed Ruben identity on the natural nondegenerate event. -/
theorem correlatedSignedPearsonT_eq_signedRubenCoordinateStatistic
    (m : ℕ) (rho : ℝ) (x e : E)
    (hrho : |rho| < 1) (hx : x ≠ 0)
    (hB : 0 < gaussianAxisResidualEnergy x e) :
    signedPearsonT m x (correlatedSecondColumn rho x e) =
      signedRubenCoordinateStatistic m rho
        (gaussianRubenCoordinates (x, e)) := by
  have hrhoSq : rho ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one rho).2 hrho
  have hgap : 0 < 1 - rho ^ 2 := sub_pos.mpr hrhoSq
  have hsqrt : 0 < Real.sqrt (1 - rho ^ 2) := Real.sqrt_pos.2 hgap
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsqrtB : 0 < Real.sqrt (gaussianAxisResidualEnergy x e) :=
    Real.sqrt_pos.2 hB
  have hinner :
      inner ℝ x (correlatedSecondColumn rho x e) =
        ‖x‖ * Real.sqrt (1 - rho ^ 2) *
          (gaussianAxisCoordinate x e +
            populationCorrelationOdds rho * ‖x‖) := by
    rw [inner_correlatedSecondColumn,
      inner_eq_norm_mul_gaussianAxisCoordinate x e hx]
    unfold populationCorrelationOdds
    field_simp [hsqrt.ne']
    ring
  have hdetSq :
      twoColumnGramDet x (correlatedSecondColumn rho x e) =
        (‖x‖ * Real.sqrt (1 - rho ^ 2) *
          Real.sqrt (gaussianAxisResidualEnergy x e)) ^ 2 := by
    rw [twoColumnGramDet_correlatedSecondColumn rho x e hx,
      mul_pow, Real.sq_sqrt hB.le]
    ring
  unfold signedPearsonT signedRubenCoordinateStatistic
    gaussianRubenCoordinates gaussianAxisCoordinates
  rw [hinner, hdetSq, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos (mul_pos hnorm hsqrt) hsqrtB)]
  field_simp [hnorm.ne', hsqrt.ne', hsqrtB.ne']

private theorem ae_pos_gammaMeasure (a r : ℝ) :
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

/-- The signed Pearson statistic has exactly the signed Ruben pushforward
law under the independent Gaussian construction. -/
theorem map_correlatedSignedPearsonT_gaussianProduct_eq_rubenProduct
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) :
    Measure.map (correlatedSignedPearsonT (E := E) m rho)
        ((stdGaussian E).prod (stdGaussian E)) =
      Measure.map (signedRubenCoordinateStatistic m rho)
        ((chiMeasure m).prod
          ((gaussianReal 0 1).prod
            (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))) := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  let muB : Measure ℝ :=
    gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)
  let muZG : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod muB
  let muR : Measure (ℝ × (ℝ × ℝ)) := (chiMeasure m).prod muZG
  have hnonzero : ∀ᵐ z ∂((stdGaussian E).prod (stdGaussian E)), z.1 ≠ 0 := by
    exact (Measure.quasiMeasurePreserving_fst
      (μ := stdGaussian E) (ν := stdGaussian E)).ae
        (p := fun x : E ↦ x ≠ 0)
        (by simpa [ae_iff] using stdGaussian_zero_singleton (E := E))
  have hBmu : ∀ᵐ b ∂muB, 0 < b := by
    exact ae_pos_gammaMeasure _ _
  have hBmuZG : ∀ᵐ z ∂muZG, 0 < z.2 := by
    exact (Measure.quasiMeasurePreserving_snd
      (μ := gaussianReal 0 1) (ν := muB)).ae hBmu
  have hBmuR : ∀ᵐ w ∂muR, 0 < w.2.2 := by
    exact (Measure.quasiMeasurePreserving_snd
      (μ := chiMeasure m) (ν := muZG)).ae hBmuZG
  have hcoords : MeasurePreserving (gaussianRubenCoordinates (E := E))
      ((stdGaussian E).prod (stdGaussian E)) muR := by
    refine ⟨measurable_gaussianRubenCoordinates, ?_⟩
    simpa [muR, muZG, muB] using
      map_gaussianRubenCoordinates_gaussianProduct
        (E := E) m hdim hm
  have hBsource :
      ∀ᵐ z ∂((stdGaussian E).prod (stdGaussian E)),
        0 < gaussianAxisResidualEnergy z.1 z.2 := by
    simpa [gaussianRubenCoordinates, gaussianAxisCoordinates] using
      hcoords.quasiMeasurePreserving.ae hBmuR
  have hfactor :
      correlatedSignedPearsonT (E := E) m rho =ᵐ[
        (stdGaussian E).prod (stdGaussian E)]
        signedRubenCoordinateStatistic m rho ∘
          gaussianRubenCoordinates (E := E) := by
    filter_upwards [hnonzero, hBsource] with z hz hBz
    exact correlatedSignedPearsonT_eq_signedRubenCoordinateStatistic
      m rho z.1 z.2 hrho hz hBz
  calc
    Measure.map (correlatedSignedPearsonT (E := E) m rho)
        ((stdGaussian E).prod (stdGaussian E)) =
        Measure.map
          (signedRubenCoordinateStatistic m rho ∘
            gaussianRubenCoordinates (E := E))
          ((stdGaussian E).prod (stdGaussian E)) :=
      Measure.map_congr hfactor
    _ = Measure.map (signedRubenCoordinateStatistic m rho)
        (Measure.map (gaussianRubenCoordinates (E := E))
          ((stdGaussian E).prod (stdGaussian E))) := by
      exact (Measure.map_map
        (measurable_signedRubenCoordinateStatistic m rho)
        measurable_gaussianRubenCoordinates).symm
    _ = Measure.map (signedRubenCoordinateStatistic m rho)
        ((chiMeasure m).prod
          ((gaussianReal 0 1).prod
            (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))) := by
      rw [map_gaussianRubenCoordinates_gaussianProduct m hdim hm]

/-! ## Exact Gaussian-tail integration -/

/-- A file-local spelling of the standard-Gaussian upper tail.  It is
definitionally equal to the shared Mills-tail function and avoids importing
analytic estimates into this exact finite-sample module. -/
private def rubenGaussianUpperTail (x : ℝ) : ℝ :=
  1 - cdf (gaussianReal 0 1) x

private theorem measurable_rubenGaussianUpperTail :
    Measurable rubenGaussianUpperTail := by
  unfold rubenGaussianUpperTail
  exact measurable_const.sub (monotone_cdf (gaussianReal 0 1)).measurable

/-- The Mills-tail function is exactly the real probability of an open
standard-Gaussian upper tail. -/
private theorem rubenGaussianUpperTail_eq_measureReal_Ioi (x : ℝ) :
    rubenGaussianUpperTail x = (gaussianReal 0 1).real (Ioi x) := by
  rw [rubenGaussianUpperTail, cdf_eq_real]
  have hcompl := measureReal_compl (μ := gaussianReal 0 1)
    (s := Iic x) measurableSet_Iic
  rw [compl_Iic, probReal_univ] at hcompl
  linarith

/-- By symmetry, a standard-Gaussian lower tail is the same shared Mills
tail evaluated at the reflected threshold. -/
private theorem gaussianReal_measureReal_Iio_neg_eq_rubenGaussianUpperTail (x : ℝ) :
    (gaussianReal 0 1).real (Iio (-x)) = rubenGaussianUpperTail x := by
  have hmap : Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) =
      gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  calc
    (gaussianReal 0 1).real (Iio (-x)) =
        (Measure.map (fun z : ℝ => -z) (gaussianReal 0 1)).real
          (Iio (-x)) := by rw [hmap]
    _ = (gaussianReal 0 1).real
          ((fun z : ℝ => -z) ⁻¹' Iio (-x)) := by
      rw [map_measureReal_apply (by fun_prop) measurableSet_Iio]
    _ = (gaussianReal 0 1).real (Ioi x) := by
      congr 1
      ext z
      simp
    _ = rubenGaussianUpperTail x :=
      (rubenGaussianUpperTail_eq_measureReal_Ioi x).symm

private theorem gaussian_middle_upperTail_mixture
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (muA : Measure A) (muB : Measure B)
    [IsProbabilityMeasure muA] [IsProbabilityMeasure muB]
    (h : A -> B -> ℝ)
    (hh : Measurable (Function.uncurry h)) :
    (muA.prod ((gaussianReal 0 1).prod muB)).real
        {w | h w.1 w.2.2 < w.2.1} =
      ∫ a, ∫ b, rubenGaussianUpperTail (h a b) ∂muB ∂muA := by
  let S : Set (A × (ℝ × B)) := {w | h w.1 w.2.2 < w.2.1}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_lt
      (hh.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      (measurable_fst.comp measurable_snd)
  have hI : Integrable (S.indicator (1 : A × (ℝ × B) -> ℝ))
      (muA.prod ((gaussianReal 0 1).prod muB)) :=
    (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_indicator_one hS, integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards [hI.prod_right_ae] with a ha
  rw [integral_prod_symm _ ha]
  apply integral_congr_ae
  filter_upwards [] with b
  have hindicator :
      (fun z : ℝ => S.indicator
        (1 : A × (ℝ × B) -> ℝ) (a, (z, b))) =
        (Ioi (h a b)).indicator (1 : ℝ -> ℝ) := by
    funext z
    simp [S, indicator_apply]
  rw [hindicator]
  rw [integral_indicator_one measurableSet_Ioi]
  exact (rubenGaussianUpperTail_eq_measureReal_Ioi _).symm

private theorem gaussian_middle_lowerTail_mixture
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (muA : Measure A) (muB : Measure B)
    [IsProbabilityMeasure muA] [IsProbabilityMeasure muB]
    (h : A -> B -> ℝ)
    (hh : Measurable (Function.uncurry h)) :
    (muA.prod ((gaussianReal 0 1).prod muB)).real
        {w | w.2.1 < -(h w.1 w.2.2)} =
      ∫ a, ∫ b, rubenGaussianUpperTail (h a b) ∂muB ∂muA := by
  let S : Set (A × (ℝ × B)) := {w | w.2.1 < -(h w.1 w.2.2)}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_lt (measurable_fst.comp measurable_snd)
      ((hh.comp (measurable_fst.prodMk
        (measurable_snd.comp measurable_snd))).neg)
  have hI : Integrable (S.indicator (1 : A × (ℝ × B) -> ℝ))
      (muA.prod ((gaussianReal 0 1).prod muB)) :=
    (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_indicator_one hS, integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards [hI.prod_right_ae] with a ha
  rw [integral_prod_symm _ ha]
  apply integral_congr_ae
  filter_upwards [] with b
  have hindicator :
      (fun z : ℝ => S.indicator
        (1 : A × (ℝ × B) -> ℝ) (a, (z, b))) =
        (Iio (-(h a b))).indicator (1 : ℝ -> ℝ) := by
    funext z
    simp [S, indicator_apply]
  rw [hindicator]
  rw [integral_indicator_one measurableSet_Iio]
  exact gaussianReal_measureReal_Iio_neg_eq_rubenGaussianUpperTail _

/-! ## Ruben thresholds and exact finite-sample identities -/

/-- The random scale multiplying a two-sided threshold after conditioning on
the Ruben residual energy. -/
def rubenTailScale (m : ℕ) (b2 : ℝ) : ℝ :=
  Real.sqrt b2 / Real.sqrt (((m - 1 : ℕ) : ℝ))

/-- Conditional standard-normal argument for the upper signed tail. -/
def rubenUpperTailArgument (m : ℕ) (rho q a b2 : ℝ) : ℝ :=
  q * rubenTailScale m b2 - populationCorrelationOdds rho * a

/-- Conditional standard-normal argument for the lower signed tail. -/
def rubenLowerTailArgument (m : ℕ) (rho q a b2 : ℝ) : ℝ :=
  q * rubenTailScale m b2 + populationCorrelationOdds rho * a

theorem measurable_uncurry_rubenUpperTailArgument (m : ℕ) (rho q : ℝ) :
    Measurable (Function.uncurry (rubenUpperTailArgument m rho q)) := by
  unfold rubenUpperTailArgument rubenTailScale populationCorrelationOdds
  fun_prop

theorem measurable_uncurry_rubenLowerTailArgument (m : ℕ) (rho q : ℝ) :
    Measurable (Function.uncurry (rubenLowerTailArgument m rho q)) := by
  unfold rubenLowerTailArgument rubenTailScale populationCorrelationOdds
  fun_prop

/-- On positive residual energy, a signed Ruben upper-tail event is exactly a
standard-normal upper-tail event. -/
theorem signedRubenCoordinateStatistic_gt_iff
    (m : ℕ) (rho q a z b2 : ℝ) (hm : 2 ≤ m) (hB : 0 < b2) :
    q < signedRubenCoordinateStatistic m rho (a, (z, b2)) ↔
      rubenUpperTailArgument m rho q a b2 < z := by
  have hdimNat : 0 < m - 1 := by omega
  have hdimReal : 0 < (((m - 1 : ℕ) : ℝ)) := by exact_mod_cast hdimNat
  have hsqrtDim : 0 < Real.sqrt (((m - 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 hdimReal
  have hsqrtB : 0 < Real.sqrt b2 := Real.sqrt_pos.2 hB
  unfold signedRubenCoordinateStatistic rubenUpperTailArgument rubenTailScale
  rw [lt_div_iff₀ hsqrtB]
  rw [mul_comm (Real.sqrt (((m - 1 : ℕ) : ℝ)))
    (z + populationCorrelationOdds rho * a)]
  rw [← div_lt_iff₀ hsqrtDim]
  rw [mul_div_assoc, sub_lt_iff_lt_add]

/-- On positive residual energy, a signed Ruben lower-tail event is exactly a
reflected standard-normal lower-tail event. -/
theorem signedRubenCoordinateStatistic_lt_neg_iff
    (m : ℕ) (rho q a z b2 : ℝ) (hm : 2 ≤ m) (hB : 0 < b2) :
    signedRubenCoordinateStatistic m rho (a, (z, b2)) < -q ↔
      z < -(rubenLowerTailArgument m rho q a b2) := by
  have hdimNat : 0 < m - 1 := by omega
  have hdimReal : 0 < (((m - 1 : ℕ) : ℝ)) := by exact_mod_cast hdimNat
  have hsqrtDim : 0 < Real.sqrt (((m - 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 hdimReal
  have hsqrtB : 0 < Real.sqrt b2 := Real.sqrt_pos.2 hB
  unfold signedRubenCoordinateStatistic rubenLowerTailArgument rubenTailScale
  rw [div_lt_iff₀ hsqrtB]
  rw [mul_comm (Real.sqrt (((m - 1 : ℕ) : ℝ)))
    (z + populationCorrelationOdds rho * a)]
  rw [← lt_div_iff₀ hsqrtDim]
  have hscale :
      (-q * Real.sqrt b2) / Real.sqrt (((m - 1 : ℕ) : ℝ)) =
        -(q * (Real.sqrt b2 / Real.sqrt (((m - 1 : ℕ) : ℝ)))) := by
    ring
  rw [hscale]
  constructor <;> intro h <;> linarith

private theorem isProbabilityMeasure_chiMeasure_of_pos
    (m : ℕ) (hm : 0 < m) : IsProbabilityMeasure (chiMeasure m) := by
  unfold chiMeasure
  letI : IsProbabilityMeasure (gammaMeasure ((m : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (div_pos (Nat.cast_pos.2 hm) (by norm_num)) (by norm_num)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private theorem ae_pos_rubenProduct_residual
    (m : ℕ) (hm : 2 ≤ m) :
    ∀ᵐ w ∂((chiMeasure m).prod
      ((gaussianReal 0 1).prod
        (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))),
      0 < w.2.2 := by
  let muB : Measure ℝ :=
    gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)
  have hB : ∀ᵐ b ∂muB, 0 < b := ae_pos_gammaMeasure _ _
  have hZB : ∀ᵐ zb ∂((gaussianReal 0 1).prod muB), 0 < zb.2 :=
    (Measure.quasiMeasurePreserving_snd
      (μ := gaussianReal 0 1) (ν := muB)).ae hB
  simpa [muB] using
    (Measure.quasiMeasurePreserving_snd
      (μ := chiMeasure m) (ν := (gaussianReal 0 1).prod muB)).ae hZB

/-- Exact conditional-Gaussian mixture formula for the upper tail of the
signed Ruben statistic. -/
theorem rubenProduct_upperTail_eq_gaussianMixture
    (m : ℕ) (hm : 2 ≤ m) (rho q : ℝ) :
    ((chiMeasure m).prod
      ((gaussianReal 0 1).prod
        (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))).real
      {w | q < signedRubenCoordinateStatistic m rho w} =
    ∫ a, ∫ b2,
      (1 - cdf (gaussianReal 0 1)
        (rubenUpperTailArgument m rho q a b2))
      ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
      ∂(chiMeasure m) := by
  let muB : Measure ℝ :=
    gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)
  let muR : Measure (ℝ × (ℝ × ℝ)) :=
    (chiMeasure m).prod ((gaussianReal 0 1).prod muB)
  letI : IsProbabilityMeasure (chiMeasure m) :=
    isProbabilityMeasure_chiMeasure_of_pos m (by omega)
  letI : IsProbabilityMeasure muB := by
    dsimp [muB]
    exact isProbabilityMeasure_gammaMeasure
      (div_pos (by exact_mod_cast (show 0 < m - 1 by omega)) (by norm_num))
      (by norm_num)
  have hevent :
      {w | q < signedRubenCoordinateStatistic m rho w} =ᵐ[muR]
        {w | rubenUpperTailArgument m rho q w.1 w.2.2 < w.2.1} := by
    have hB : ∀ᵐ w ∂muR, 0 < w.2.2 := by
      simpa [muR, muB] using ae_pos_rubenProduct_residual m hm
    filter_upwards [hB] with w hw
    apply propext
    exact signedRubenCoordinateStatistic_gt_iff
      m rho q w.1 w.2.1 w.2.2 hm hw
  calc
    ((chiMeasure m).prod
      ((gaussianReal 0 1).prod
        (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))).real
      {w | q < signedRubenCoordinateStatistic m rho w} =
        muR.real
          {w | rubenUpperTailArgument m rho q w.1 w.2.2 < w.2.1} := by
      rw [← measureReal_congr hevent]
    _ = ∫ a, ∫ b2,
        (1 - cdf (gaussianReal 0 1)
          (rubenUpperTailArgument m rho q a b2)) ∂muB ∂(chiMeasure m) := by
      simpa [muR, rubenGaussianUpperTail] using
        gaussian_middle_upperTail_mixture
          (chiMeasure m) muB (rubenUpperTailArgument m rho q)
          (measurable_uncurry_rubenUpperTailArgument m rho q)
    _ = ∫ a, ∫ b2,
        (1 - cdf (gaussianReal 0 1)
          (rubenUpperTailArgument m rho q a b2))
        ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
        ∂(chiMeasure m) := by rfl

/-- Exact conditional-Gaussian mixture formula for the lower tail of the
signed Ruben statistic. -/
theorem rubenProduct_lowerTail_eq_gaussianMixture
    (m : ℕ) (hm : 2 ≤ m) (rho q : ℝ) :
    ((chiMeasure m).prod
      ((gaussianReal 0 1).prod
        (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))).real
      {w | signedRubenCoordinateStatistic m rho w < -q} =
    ∫ a, ∫ b2,
      (1 - cdf (gaussianReal 0 1)
        (rubenLowerTailArgument m rho q a b2))
      ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
      ∂(chiMeasure m) := by
  let muB : Measure ℝ :=
    gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)
  let muR : Measure (ℝ × (ℝ × ℝ)) :=
    (chiMeasure m).prod ((gaussianReal 0 1).prod muB)
  letI : IsProbabilityMeasure (chiMeasure m) :=
    isProbabilityMeasure_chiMeasure_of_pos m (by omega)
  letI : IsProbabilityMeasure muB := by
    dsimp [muB]
    exact isProbabilityMeasure_gammaMeasure
      (div_pos (by exact_mod_cast (show 0 < m - 1 by omega)) (by norm_num))
      (by norm_num)
  have hevent :
      {w | signedRubenCoordinateStatistic m rho w < -q} =ᵐ[muR]
        {w | w.2.1 < -(rubenLowerTailArgument m rho q w.1 w.2.2)} := by
    have hB : ∀ᵐ w ∂muR, 0 < w.2.2 := by
      simpa [muR, muB] using ae_pos_rubenProduct_residual m hm
    filter_upwards [hB] with w hw
    apply propext
    exact signedRubenCoordinateStatistic_lt_neg_iff
      m rho q w.1 w.2.1 w.2.2 hm hw
  calc
    ((chiMeasure m).prod
      ((gaussianReal 0 1).prod
        (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))).real
      {w | signedRubenCoordinateStatistic m rho w < -q} =
        muR.real
          {w | w.2.1 < -(rubenLowerTailArgument m rho q w.1 w.2.2)} := by
      rw [← measureReal_congr hevent]
    _ = ∫ a, ∫ b2,
        (1 - cdf (gaussianReal 0 1)
          (rubenLowerTailArgument m rho q a b2)) ∂muB ∂(chiMeasure m) := by
      simpa [muR, rubenGaussianUpperTail] using
        gaussian_middle_lowerTail_mixture
          (chiMeasure m) muB (rubenLowerTailArgument m rho q)
          (measurable_uncurry_rubenLowerTailArgument m rho q)
    _ = ∫ a, ∫ b2,
        (1 - cdf (gaussianReal 0 1)
          (rubenLowerTailArgument m rho q a b2))
        ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
        ∂(chiMeasure m) := by rfl

/-- Exact one-sided upper-tail identity for the signed Pearson statistic under
the correlated Gaussian construction. -/
theorem correlatedSignedPearsonT_upperTail_eq_gaussianMixture
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) (q : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | q < correlatedSignedPearsonT (E := E) m rho z} =
    ∫ a, ∫ b2,
      (1 - cdf (gaussianReal 0 1)
        (rubenUpperTailArgument m rho q a b2))
      ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
      ∂(chiMeasure m) := by
  let muR : Measure (ℝ × (ℝ × ℝ)) :=
    (chiMeasure m).prod
      ((gaussianReal 0 1).prod
        (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))
  calc
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | q < correlatedSignedPearsonT (E := E) m rho z} =
        (Measure.map (correlatedSignedPearsonT (E := E) m rho)
          ((stdGaussian E).prod (stdGaussian E))).real (Ioi q) := by
      rw [map_measureReal_apply
        (measurable_correlatedSignedPearsonT m rho) measurableSet_Ioi]
      congr 1
    _ = (Measure.map (signedRubenCoordinateStatistic m rho) muR).real
        (Ioi q) := by
      rw [map_correlatedSignedPearsonT_gaussianProduct_eq_rubenProduct
        m hdim hm rho hrho]
    _ = muR.real {w | q < signedRubenCoordinateStatistic m rho w} := by
      rw [map_measureReal_apply
        (measurable_signedRubenCoordinateStatistic m rho) measurableSet_Ioi]
      congr 1
    _ = ∫ a, ∫ b2,
        (1 - cdf (gaussianReal 0 1)
          (rubenUpperTailArgument m rho q a b2))
        ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
        ∂(chiMeasure m) := by
      simpa [muR] using rubenProduct_upperTail_eq_gaussianMixture m hm rho q

/-- Exact one-sided lower-tail identity for the signed Pearson statistic under
the correlated Gaussian construction. -/
theorem correlatedSignedPearsonT_lowerTail_eq_gaussianMixture
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) (q : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | correlatedSignedPearsonT (E := E) m rho z < -q} =
    ∫ a, ∫ b2,
      (1 - cdf (gaussianReal 0 1)
        (rubenLowerTailArgument m rho q a b2))
      ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
      ∂(chiMeasure m) := by
  let muR : Measure (ℝ × (ℝ × ℝ)) :=
    (chiMeasure m).prod
      ((gaussianReal 0 1).prod
        (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))
  calc
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | correlatedSignedPearsonT (E := E) m rho z < -q} =
        (Measure.map (correlatedSignedPearsonT (E := E) m rho)
          ((stdGaussian E).prod (stdGaussian E))).real (Iio (-q)) := by
      rw [map_measureReal_apply
        (measurable_correlatedSignedPearsonT m rho) measurableSet_Iio]
      congr 1
    _ = (Measure.map (signedRubenCoordinateStatistic m rho) muR).real
        (Iio (-q)) := by
      rw [map_correlatedSignedPearsonT_gaussianProduct_eq_rubenProduct
        m hdim hm rho hrho]
    _ = muR.real {w | signedRubenCoordinateStatistic m rho w < -q} := by
      rw [map_measureReal_apply
        (measurable_signedRubenCoordinateStatistic m rho) measurableSet_Iio]
      congr 1
    _ = ∫ a, ∫ b2,
        (1 - cdf (gaussianReal 0 1)
          (rubenLowerTailArgument m rho q a b2))
        ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
        ∂(chiMeasure m) := by
      simpa [muR] using rubenProduct_lowerTail_eq_gaussianMixture m hm rho q

/-- Exact two-sided Gaussian-tail mixture for the signed Pearson statistic.
The two terms are the conditional upper and lower standard-normal tails. -/
theorem correlatedSignedPearsonT_twoSidedTail_eq_gaussianMixture
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) (q : ℝ) (hq : 0 ≤ q) :
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | q < |correlatedSignedPearsonT (E := E) m rho z|} =
    (∫ a, ∫ b2,
      (1 - cdf (gaussianReal 0 1)
        (rubenUpperTailArgument m rho q a b2))
      ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
      ∂(chiMeasure m)) +
    (∫ a, ∫ b2,
      (1 - cdf (gaussianReal 0 1)
        (rubenLowerTailArgument m rho q a b2))
      ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
      ∂(chiMeasure m)) := by
  let P : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let T : E × E -> ℝ := correlatedSignedPearsonT (E := E) m rho
  let U : Set (E × E) := {z | q < T z}
  let L : Set (E × E) := {z | T z < -q}
  have hT : Measurable T := by
    simpa [T] using measurable_correlatedSignedPearsonT (E := E) m rho
  have hU : MeasurableSet U := by
    dsimp [U]
    exact measurableSet_lt measurable_const hT
  have hL : MeasurableSet L := by
    dsimp [L]
    exact measurableSet_lt hT measurable_const
  have hdisj : Disjoint U L := by
    rw [Set.disjoint_left]
    intro z hzU hzL
    dsimp [U] at hzU
    dsimp [L] at hzL
    linarith
  have habs : {z | q < |T z|} = U ∪ L := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hz
      by_cases hsign : 0 ≤ T z
      · left
        dsimp [U]
        simpa [abs_of_nonneg hsign] using hz
      · right
        dsimp [L]
        have hneg : T z < 0 := lt_of_not_ge hsign
        rw [abs_of_neg hneg] at hz
        linarith
    · intro hz
      rcases hz with hzU | hzL
      · dsimp [U] at hzU
        have hpos : 0 < T z := lt_of_le_of_lt hq hzU
        simpa [abs_of_pos hpos] using hzU
      · dsimp [L] at hzL
        have hneg : T z < 0 := lt_of_lt_of_le hzL (neg_nonpos.mpr hq)
        rw [abs_of_neg hneg]
        linarith
  calc
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | q < |correlatedSignedPearsonT (E := E) m rho z|} =
        P.real (U ∪ L) := by rw [habs]
    _ = P.real U + P.real L := measureReal_union hdisj hL
    _ = (∫ a, ∫ b2,
        (1 - cdf (gaussianReal 0 1)
          (rubenUpperTailArgument m rho q a b2))
        ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
        ∂(chiMeasure m)) +
      (∫ a, ∫ b2,
        (1 - cdf (gaussianReal 0 1)
          (rubenLowerTailArgument m rho q a b2))
        ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
        ∂(chiMeasure m)) := by
      rw [show P.real U = ∫ a, ∫ b2,
          (1 - cdf (gaussianReal 0 1)
            (rubenUpperTailArgument m rho q a b2))
          ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
          ∂(chiMeasure m) by
        simpa [P, U, T] using
          correlatedSignedPearsonT_upperTail_eq_gaussianMixture
            (E := E) m hdim hm rho hrho q]
      rw [show P.real L = ∫ a, ∫ b2,
          (1 - cdf (gaussianReal 0 1)
            (rubenLowerTailArgument m rho q a b2))
          ∂(gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2))
          ∂(chiMeasure m) by
        simpa [P, L, T] using
          correlatedSignedPearsonT_lowerTail_eq_gaussianMixture
            (E := E) m hdim hm rho hrho q]

end

end LogdetLean.Coherence
