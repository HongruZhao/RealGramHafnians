import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable
/-!
# Extending identities from compactly supported to bounded coordinate tests

This file proves a purely measure-theoretic closure lemma.  If two integrable
real densities have equal integrals after multiplication by every compactly
supported continuous function of a measurable coordinate, then they have
equal integrals after multiplication by every bounded measurable function of
that coordinate.

The proof uses only positive measures.  We add the common density
`|f| + |h|` to both signed densities, push the resulting finite positive
measures to the coordinate space, and invoke Riesz--Markov uniqueness.
-/

open MeasureTheory
open scoped CompactlySupported

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {Ω X : Type*} [MeasurableSpace Ω]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]

/-- A common positive shift which turns both real densities into nonnegative
densities without changing their difference. -/
def commonAbsoluteShift (f h : Ω → ℝ) (ω : Ω) : ℝ :=
  |f ω| + |h ω|

theorem commonAbsoluteShift_add_left_nonneg
    (f h : Ω → ℝ) (ω : Ω) :
    0 ≤ commonAbsoluteShift f h ω + f ω := by
  unfold commonAbsoluteShift
  nlinarith [neg_le_abs (f ω), abs_nonneg (h ω)]

theorem commonAbsoluteShift_add_right_nonneg
    (f h : Ω → ℝ) (ω : Ω) :
    0 ≤ commonAbsoluteShift f h ω + h ω := by
  unfold commonAbsoluteShift
  nlinarith [neg_le_abs (h ω), abs_nonneg (f ω)]

theorem integrable_commonAbsoluteShift_add_left
    {μ : Measure Ω} {f h : Ω → ℝ}
    (hf : Integrable f μ) (hh : Integrable h μ) :
    Integrable (fun ω ↦ commonAbsoluteShift f h ω + f ω) μ := by
  have hbase : Integrable
      (fun ω ↦ ‖f ω‖ + ‖h ω‖ + f ω) μ :=
    (hf.norm.add hh.norm).add hf
  exact hbase.congr <| ae_of_all μ fun ω ↦ by
    simp [commonAbsoluteShift, Real.norm_eq_abs]

theorem integrable_commonAbsoluteShift_add_right
    {μ : Measure Ω} {f h : Ω → ℝ}
    (hf : Integrable f μ) (hh : Integrable h μ) :
    Integrable (fun ω ↦ commonAbsoluteShift f h ω + h ω) μ := by
  have hbase : Integrable
      (fun ω ↦ ‖f ω‖ + ‖h ω‖ + h ω) μ :=
    (hf.norm.add hh.norm).add hh
  exact hbase.congr <| ae_of_all μ fun ω ↦ by
    simp [commonAbsoluteShift, Real.norm_eq_abs]

/-- Push a nonnegative real density forward along a measurable coordinate. -/
def positiveCoordinateMeasure
    (μ : Measure Ω) (S : Ω → X) (ρ : Ω → ℝ) : Measure X :=
  Measure.map S (μ.withDensity fun ω ↦ ENNReal.ofReal (ρ ω))

private theorem integral_positiveCoordinateMeasure
    {μ : Measure Ω} {S : Ω → X} {ρ : Ω → ℝ}
    (hS : Measurable S) (hρ : Measurable ρ)
    (hρ0 : ∀ ω, 0 ≤ ρ ω)
    (u : X → ℝ)
    (hu : AEStronglyMeasurable u (positiveCoordinateMeasure μ S ρ)) :
    (∫ x, u x ∂positiveCoordinateMeasure μ S ρ) =
      ∫ ω, u (S ω) * ρ ω ∂μ := by
  rw [positiveCoordinateMeasure, integral_map hS.aemeasurable hu]
  rw [integral_withDensity_eq_integral_toReal_smul
    hρ.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [ENNReal.toReal_ofReal (hρ0 ω)]
  simp only [smul_eq_mul]
  ring

/-- Equality against all compactly supported continuous tests of a measurable
coordinate extends to every bounded measurable coordinate test. -/
theorem integral_comp_mul_eq_of_compactlySupported
    (μ : Measure Ω) (S : Ω → X) (f h : Ω → ℝ)
    (hS : Measurable S) (hfmeas : Measurable f) (hhmeas : Measurable h)
    (hf : Integrable f μ) (hh : Integrable h μ)
    (hcc : ∀ φ : C_c(X, ℝ),
      (∫ ω, φ (S ω) * f ω ∂μ) =
        ∫ ω, φ (S ω) * h ω ∂μ)
    (u : X → ℝ) (hu : Measurable u)
    (C : ℝ) (huC : ∀ x, |u x| ≤ C) :
    (∫ ω, u (S ω) * f ω ∂μ) =
      ∫ ω, u (S ω) * h ω ∂μ := by
  let ρf : Ω → ℝ := fun ω ↦ commonAbsoluteShift f h ω + f ω
  let ρh : Ω → ℝ := fun ω ↦ commonAbsoluteShift f h ω + h ω
  let νf : Measure X := positiveCoordinateMeasure μ S ρf
  let νh : Measure X := positiveCoordinateMeasure μ S ρh
  have hρfint : Integrable ρf μ :=
    integrable_commonAbsoluteShift_add_left hf hh
  have hρhint : Integrable ρh μ :=
    integrable_commonAbsoluteShift_add_right hf hh
  have hρfmeas : Measurable ρf := by
    change Measurable
      (((fun ω ↦ |f ω|) + fun ω ↦ |h ω|) + f)
    simpa only [Real.norm_eq_abs] using
      ((hfmeas.norm.add hhmeas.norm).add hfmeas)
  have hρhmeas : Measurable ρh := by
    change Measurable
      (((fun ω ↦ |f ω|) + fun ω ↦ |h ω|) + h)
    simpa only [Real.norm_eq_abs] using
      ((hfmeas.norm.add hhmeas.norm).add hhmeas)
  have hρf0 : ∀ ω, 0 ≤ ρf ω := fun ω ↦
    commonAbsoluteShift_add_left_nonneg f h ω
  have hρh0 : ∀ ω, 0 ≤ ρh ω := fun ω ↦
    commonAbsoluteShift_add_right_nonneg f h ω
  letI : IsFiniteMeasure
      (μ.withDensity fun ω ↦ ENNReal.ofReal (ρf ω)) :=
    isFiniteMeasure_withDensity_ofReal hρfint.hasFiniteIntegral
  letI : IsFiniteMeasure
      (μ.withDensity fun ω ↦ ENNReal.ofReal (ρh ω)) :=
    isFiniteMeasure_withDensity_ofReal hρhint.hasFiniteIntegral
  letI : IsFiniteMeasure νf := by
    dsimp [νf, positiveCoordinateMeasure]
    infer_instance
  letI : IsFiniteMeasure νh := by
    dsimp [νh, positiveCoordinateMeasure]
    infer_instance
  have hν : νf = νh := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro φ
    have hφf : AEStronglyMeasurable (fun x : X ↦ φ x) νf :=
      φ.continuous.aestronglyMeasurable
    have hφh : AEStronglyMeasurable (fun x : X ↦ φ x) νh :=
      φ.continuous.aestronglyMeasurable
    rw [show (∫ x, φ x ∂νf) =
        ∫ ω, φ (S ω) * ρf ω ∂μ by
          exact integral_positiveCoordinateMeasure hS hρfmeas hρf0 _ hφf,
      show (∫ x, φ x ∂νh) =
        ∫ ω, φ (S ω) * ρh ω ∂μ by
          exact integral_positiveCoordinateMeasure hS hρhmeas hρh0 _ hφh]
    have hφbound : ∀ x : X, ‖φ x‖ ≤
        ‖φ.toBoundedContinuousFunction‖ :=
      fun x ↦ BoundedContinuousFunction.norm_coe_le_norm
        φ.toBoundedContinuousFunction x
    have hφmeas : AEStronglyMeasurable (fun ω ↦ φ (S ω)) μ :=
      (φ.continuous.measurable.comp hS).aestronglyMeasurable
    have hφq : Integrable
        (fun ω ↦ φ (S ω) * commonAbsoluteShift f h ω) μ := by
      have hq : Integrable (fun ω ↦ ‖f ω‖ + ‖h ω‖) μ :=
        hf.norm.add hh.norm
      have hq' : Integrable (commonAbsoluteShift f h) μ :=
        hq.congr <| ae_of_all μ fun ω ↦ by
          simp [commonAbsoluteShift, Real.norm_eq_abs]
      exact hq'.bdd_mul hφmeas <|
        Filter.Eventually.of_forall fun ω ↦ hφbound (S ω)
    have hφfint : Integrable (fun ω ↦ φ (S ω) * f ω) μ :=
      hf.bdd_mul hφmeas <|
        Filter.Eventually.of_forall fun ω ↦ hφbound (S ω)
    have hφhint : Integrable (fun ω ↦ φ (S ω) * h ω) μ :=
      hh.bdd_mul hφmeas <|
        Filter.Eventually.of_forall fun ω ↦ hφbound (S ω)
    change (∫ ω, φ (S ω) *
        (commonAbsoluteShift f h ω + f ω) ∂μ) =
      ∫ ω, φ (S ω) *
        (commonAbsoluteShift f h ω + h ω) ∂μ
    simp_rw [mul_add]
    rw [integral_add hφq hφfint, integral_add hφq hφhint, hcc φ]
  have humeasf : AEStronglyMeasurable u νf := hu.aestronglyMeasurable
  have humeash : AEStronglyMeasurable u νh := hu.aestronglyMeasurable
  have hshift :
      (∫ ω, u (S ω) * ρf ω ∂μ) =
        ∫ ω, u (S ω) * ρh ω ∂μ := by
    rw [← integral_positiveCoordinateMeasure hS hρfmeas hρf0 u humeasf,
      ← integral_positiveCoordinateMeasure hS hρhmeas hρh0 u humeash]
    change (∫ x, u x ∂νf) = ∫ x, u x ∂νh
    rw [hν]
  have hunorm : ∀ x, ‖u x‖ ≤ C := by
    intro x
    simpa [Real.norm_eq_abs] using huC x
  have humeascomp : AEStronglyMeasurable (fun ω ↦ u (S ω)) μ :=
    (hu.comp hS).aestronglyMeasurable
  have huq : Integrable
      (fun ω ↦ u (S ω) * commonAbsoluteShift f h ω) μ := by
    have hq : Integrable (fun ω ↦ ‖f ω‖ + ‖h ω‖) μ :=
      hf.norm.add hh.norm
    have hq' : Integrable (commonAbsoluteShift f h) μ :=
      hq.congr <| ae_of_all μ fun ω ↦ by
        simp [commonAbsoluteShift, Real.norm_eq_abs]
    exact hq'.bdd_mul humeascomp <|
      Filter.Eventually.of_forall fun ω ↦ hunorm (S ω)
  have huf : Integrable (fun ω ↦ u (S ω) * f ω) μ :=
    hf.bdd_mul humeascomp <|
      Filter.Eventually.of_forall fun ω ↦ hunorm (S ω)
  have huh : Integrable (fun ω ↦ u (S ω) * h ω) μ :=
    hh.bdd_mul humeascomp <|
      Filter.Eventually.of_forall fun ω ↦ hunorm (S ω)
  have hshift' :
      (∫ ω, u (S ω) * commonAbsoluteShift f h ω ∂μ) +
          ∫ ω, u (S ω) * f ω ∂μ =
        (∫ ω, u (S ω) * commonAbsoluteShift f h ω ∂μ) +
          ∫ ω, u (S ω) * h ω ∂μ := by
    rw [← integral_add huq huf, ← integral_add huq huh]
    simpa [ρf, ρh, mul_add] using hshift
  exact add_left_cancel hshift'

end Wishart

end

end LogdetLean.GramHafnian
