import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import LogdetLean.KolmogorovPerturbation
/-!
# The reusable Chebyshev--Kolmogorov perturbation bound

This is the probability step used to pass from a leading normal
approximation to the full general-correlation statistic.  It combines the
coupling inequality in `KolmogorovPerturbation` with Mathlib's formally
verified Chebyshev inequality.  Dependence between the leading variable and
the remainder is allowed.

The resulting estimate is the rigorous Lean version of equation
`perturbation-proof` in the sharp manuscript and of the corresponding
remainder step in Zhao (2026), arXiv:2608.00565v1.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Real-valued Chebyshev bound for a centered random variable, with a strict
tail event. -/
theorem measureReal_abs_gt_le_variance_div_sq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) (hcenter : P[Y] = 0) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε < |Y ω|} ≤ Var[Y; P] / ε ^ 2 := by
  have hcheb := meas_ge_le_variance_div_sq (μ := P) hY hε
  have hsubset : {ω | ε < |Y ω|} ⊆
      {ω | ε ≤ |Y ω - P[Y]|} := by
    intro ω hω
    change ε < |Y ω| at hω
    change ε ≤ |Y ω - P[Y]|
    rw [hcenter, sub_zero]
    exact hω.le
  have hmeasure : P {ω | ε < |Y ω|} ≤
      ENNReal.ofReal (Var[Y; P] / ε ^ 2) :=
    (measure_mono hsubset).trans hcheb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal] at hreal
  · exact hreal
  · exact div_nonneg (variance_nonneg _ _) (sq_nonneg ε)

/-- The coupling bad event between `X+Y` and `X` is exactly the tail event of
the additive remainder `Y`. -/
theorem couplingBadEvent_add_eq
    {Ω : Type*} (X Y : Ω → ℝ) (ε : ℝ) :
    couplingBadEvent (fun ω ↦ X ω + Y ω) X ε = {ω | ε < |Y ω|} := by
  ext ω
  simp [couplingBadEvent]

/-- Quantitative perturbation by a centered square-integrable remainder.
No independence hypothesis is present. -/
theorem kolmogorovDistance_standardGaussian_add_le_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hYmeas : Measurable Y)
    (hY : MemLp Y 2 P) (hcenter : P[Y] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    kolmogorovDistance (P.map (fun ω ↦ X ω + Y ω))
        (gaussianReal 0 1) ≤
      kolmogorovDistance (P.map X) (gaussianReal 0 1) +
        Var[Y; P] / ε ^ 2 + ε / Real.sqrt (2 * Real.pi) := by
  have hbad : P.real
      (couplingBadEvent (fun ω ↦ X ω + Y ω) X ε) ≤
      Var[Y; P] / ε ^ 2 := by
    rw [couplingBadEvent_add_eq]
    exact measureReal_abs_gt_le_variance_div_sq P hY hcenter hε
  exact kolmogorovDistance_standardGaussian_le_of_coupling P
    (hX.add hYmeas) hX hε.le hbad

/-- A supplied second-moment/variance upper bound can replace the exact
remainder variance in the preceding theorem. -/
theorem kolmogorovDistance_standardGaussian_add_le_secondMomentBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hYmeas : Measurable Y)
    (hY : MemLp Y 2 P) (hcenter : P[Y] = 0)
    {Q ε : ℝ} (hvar : Var[Y; P] ≤ Q) (hε : 0 < ε) :
    kolmogorovDistance (P.map (fun ω ↦ X ω + Y ω))
        (gaussianReal 0 1) ≤
      kolmogorovDistance (P.map X) (gaussianReal 0 1) +
        Q / ε ^ 2 + ε / Real.sqrt (2 * Real.pi) := by
  calc
    kolmogorovDistance (P.map (fun ω ↦ X ω + Y ω))
        (gaussianReal 0 1) ≤
      kolmogorovDistance (P.map X) (gaussianReal 0 1) +
        Var[Y; P] / ε ^ 2 + ε / Real.sqrt (2 * Real.pi) :=
      kolmogorovDistance_standardGaussian_add_le_variance
        P hX hYmeas hY hcenter hε
    _ ≤ kolmogorovDistance (P.map X) (gaussianReal 0 1) +
        Q / ε ^ 2 + ε / Real.sqrt (2 * Real.pi) := by
      gcongr

end

end LogdetLean
