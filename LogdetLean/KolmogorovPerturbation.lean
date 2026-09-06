import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import LogdetLean.GaussianAntiConcentration
import LogdetLean.KolmogorovDistance
/-!
# Kolmogorov perturbation through CDF shift bounds

This file contains the model-independent perturbation step used after a
normal approximation has been proved for a leading term.  The first theorem
is deterministic: a two-sided shifted-CDF sandwich and an anti-concentration
bound imply a Kolmogorov bound.  The second theorem derives the sandwich from
a coupling.  The final theorem specializes the reference law to the standard
Gaussian using the density bound proved in `GaussianAntiConcentration`.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- A one-sided modulus-of-continuity bound for a CDF at scale `ε`. -/
def HasCDFIncrementBound (ν : Measure ℝ) (ε ω : ℝ) : Prop :=
  ∀ x, cdf ν (x + ε) - cdf ν x ≤ ω

/-- A shifted CDF sandwich.  In applications, `q` is the probability that
two coupled variables differ by more than `ε`. -/
def HasCDFShiftSandwich (μ η : Measure ℝ) (ε q : ℝ) : Prop :=
  (∀ x, cdf η (x - ε) - q ≤ cdf μ x) ∧
    ∀ x, cdf μ x ≤ cdf η (x + ε) + q

/-- Deterministic Kolmogorov perturbation theorem. -/
theorem kolmogorovDistance_le_of_cdf_shift_sandwich
    (μ η ν : Measure ℝ) {ε q ω : ℝ}
    (hsand : HasCDFShiftSandwich μ η ε q)
    (hmod : HasCDFIncrementBound ν ε ω) :
    kolmogorovDistance μ ν ≤ kolmogorovDistance η ν + q + ω := by
  apply supDistance_le_of_bound
  intro x
  have hηp : |cdf η (x + ε) - cdf ν (x + ε)| ≤
      kolmogorovDistance η ν := by
    exact point_le_supDistance
      (fun y ↦ abs_cdf_sub_cdf_le_one η ν y) (x + ε)
  have hηm : |cdf η (x - ε) - cdf ν (x - ε)| ≤
      kolmogorovDistance η ν := by
    exact point_le_supDistance
      (fun y ↦ abs_cdf_sub_cdf_le_one η ν y) (x - ε)
  have hmodp := hmod x
  have hmodm := hmod (x - ε)
  have harg : x - ε + ε = x := by ring
  rw [harg] at hmodm
  have hu : cdf μ x - cdf ν x ≤ kolmogorovDistance η ν + q + ω := by
    have hs := hsand.2 x
    rw [abs_le] at hηp
    linarith
  have hl : -(kolmogorovDistance η ν + q + ω) ≤ cdf μ x - cdf ν x := by
    have hs := hsand.1 x
    rw [abs_le] at hηm
    linarith
  exact (abs_le.mpr ⟨hl, hu⟩)

/-- The bad event for an `ε`-coupling of two real random variables. -/
def couplingBadEvent {Ω : Type*} (X Y : Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | ε < |X ω - Y ω|}

theorem measurableSet_couplingBadEvent {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (ε : ℝ) :
    MeasurableSet (couplingBadEvent X Y ε) := by
  exact measurableSet_lt measurable_const (hX.sub hY).abs

/-- A coupling whose bad event has probability at most `q` gives the shifted
CDF sandwich needed by the deterministic perturbation theorem. -/
theorem cdf_shift_sandwich_of_coupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {ε q : ℝ} (hbad : P.real (couplingBadEvent X Y ε) ≤ q) :
    HasCDFShiftSandwich (P.map X) (P.map Y) ε q := by
  have hprobX : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hprobY : IsProbabilityMeasure (P.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  constructor
  · intro x
    rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hX measurableSet_Iic,
      map_measureReal_apply hY measurableSet_Iic]
    let A : Set Ω := X ⁻¹' Iic x
    let C : Set Ω := Y ⁻¹' Iic (x - ε)
    let E : Set Ω := couplingBadEvent X Y ε
    have hsubset : C ⊆ A ∪ E := by
      intro ω hω
      by_cases hE : ω ∈ E
      · exact Or.inr hE
      · left
        have hYω : Y ω ≤ x - ε := hω
        have habs : |X ω - Y ω| ≤ ε := le_of_not_gt hE
        have hXY : X ω - Y ω ≤ ε := (le_abs_self _).trans habs
        change X ω ≤ x
        linarith
    have hmono : P.real C ≤ P.real (A ∪ E) := measureReal_mono hsubset
    have hunion : P.real (A ∪ E) ≤ P.real A + P.real E := measureReal_union_le _ _
    change P.real C - q ≤ P.real A
    change P.real E ≤ q at hbad
    linarith
  · intro x
    rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hX measurableSet_Iic,
      map_measureReal_apply hY measurableSet_Iic]
    let A : Set Ω := X ⁻¹' Iic x
    let B : Set Ω := Y ⁻¹' Iic (x + ε)
    let E : Set Ω := couplingBadEvent X Y ε
    have hsubset : A ⊆ B ∪ E := by
      intro ω hω
      by_cases hE : ω ∈ E
      · exact Or.inr hE
      · left
        have hXω : X ω ≤ x := hω
        have habs : |X ω - Y ω| ≤ ε := le_of_not_gt hE
        have hYX : Y ω - X ω ≤ ε := by
          have := (neg_le_abs (X ω - Y ω)).trans habs
          linarith
        change Y ω ≤ x + ε
        linarith
    have hmono : P.real A ≤ P.real (B ∪ E) := measureReal_mono hsubset
    have hunion : P.real (B ∪ E) ≤ P.real B + P.real E := measureReal_union_le _ _
    change P.real A ≤ P.real B + q
    change P.real E ≤ q at hbad
    linarith

/-- Coupling perturbation theorem for an arbitrary reference law with a
known CDF increment bound. -/
theorem kolmogorovDistance_map_le_of_coupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (ν : Measure ℝ) {ε q ω : ℝ}
    (hbad : P.real (couplingBadEvent X Y ε) ≤ q)
    (hmod : HasCDFIncrementBound ν ε ω) :
    kolmogorovDistance (P.map X) ν ≤
      kolmogorovDistance (P.map Y) ν + q + ω :=
  kolmogorovDistance_le_of_cdf_shift_sandwich _ _ _
    (cdf_shift_sandwich_of_coupling P hX hY hbad) hmod

/-- Standard-normal specialization: coupling error `q` and displacement
scale `ε` cost at most `q + ε / sqrt (2π)` in Kolmogorov distance. -/
theorem kolmogorovDistance_standardGaussian_le_of_coupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {ε q : ℝ} (hε : 0 ≤ ε)
    (hbad : P.real (couplingBadEvent X Y ε) ≤ q) :
    kolmogorovDistance (P.map X) (gaussianReal 0 1) ≤
      kolmogorovDistance (P.map Y) (gaussianReal 0 1) + q +
        ε / Real.sqrt (2 * Real.pi) := by
  apply kolmogorovDistance_map_le_of_coupling P hX hY _ hbad
  exact fun x ↦ standardGaussian_cdf_increment_le x ε hε

/-- Chebyshev's inequality in the exact form needed for a coupling
perturbation: a second-moment bound controls the probability of displacement
larger than `ε`. -/
theorem couplingBadEvent_measureReal_le_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X Y : Ω → ℝ} {ε Q : ℝ} (hε : 0 < ε)
    (hsq : Integrable (fun ω ↦ (X ω - Y ω) ^ 2) P)
    (hQ : (∫ ω, (X ω - Y ω) ^ 2 ∂P) ≤ Q) :
    P.real (couplingBadEvent X Y ε) ≤ Q / ε ^ 2 := by
  let S : Set Ω := {ω | ε ^ 2 ≤ (X ω - Y ω) ^ 2}
  have hsubset : couplingBadEvent X Y ε ⊆ S := by
    intro ω hω
    have hsquare :=
      (sq_le_sq₀ hε.le (abs_nonneg (X ω - Y ω))).2 (le_of_lt hω)
    simpa [S, sq_abs] using hsquare
  have hmono : P.real (couplingBadEvent X Y ε) ≤ P.real S :=
    measureReal_mono hsubset
  have hmarkov : ε ^ 2 * P.real S ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂P := by
    simpa [S] using mul_meas_ge_le_integral_of_nonneg
      (μ := P) (f := fun ω ↦ (X ω - Y ω) ^ 2)
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) hsq (ε ^ 2)
  have hmul : ε ^ 2 * P.real (couplingBadEvent X Y ε) ≤ Q := by
    calc
      ε ^ 2 * P.real (couplingBadEvent X Y ε) ≤ ε ^ 2 * P.real S :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg ε)
      _ ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂P := hmarkov
      _ ≤ Q := hQ
  exact (le_div_iff₀ (sq_pos_of_pos hε)).2 (by simpa [mul_comm] using hmul)

/-- Standard-normal Kolmogorov perturbation from an `L²` remainder bound. -/
theorem kolmogorovDistance_standardGaussian_le_of_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {ε Q : ℝ} (hε : 0 < ε)
    (hsq : Integrable (fun ω ↦ (X ω - Y ω) ^ 2) P)
    (hQ : (∫ ω, (X ω - Y ω) ^ 2 ∂P) ≤ Q) :
    kolmogorovDistance (P.map X) (gaussianReal 0 1) ≤
      kolmogorovDistance (P.map Y) (gaussianReal 0 1) + Q / ε ^ 2 +
        ε / Real.sqrt (2 * Real.pi) := by
  exact kolmogorovDistance_standardGaussian_le_of_coupling P hX hY hε.le
    (couplingBadEvent_measureReal_le_secondMoment P hε hsq hQ)

/-- At a cubic second-moment scale `Q=t³`, choosing displacement threshold
`ε=t` gives the explicit cube-root perturbation bound. -/
theorem kolmogorovDistance_standardGaussian_le_at_cubeRootScale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {t : ℝ} (ht : 0 < t)
    (hsq : Integrable (fun ω ↦ (X ω - Y ω) ^ 2) P)
    (hQ : (∫ ω, (X ω - Y ω) ^ 2 ∂P) ≤ t ^ 3) :
    kolmogorovDistance (P.map X) (gaussianReal 0 1) ≤
      kolmogorovDistance (P.map Y) (gaussianReal 0 1) + t +
        t / Real.sqrt (2 * Real.pi) := by
  have h := kolmogorovDistance_standardGaussian_le_of_secondMoment
    P hX hY ht hsq hQ
  convert h using 1
  field_simp

end

end LogdetLean
