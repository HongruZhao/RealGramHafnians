import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod
/-!
# Conditioning one coordinate of a product law

The rare matching event depends only on the retained prefix.  This file
records the elementary measure identity saying that conditioning a product
law on a prefix event leaves the independent second coordinate unchanged.
-/

namespace LogdetLean.Coherence

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

noncomputable section

/-- Conditioning `μ.prod ν` on `s × univ` conditions only its first factor,
provided the second factor has total mass one.  The identity is exact and
also covers the zero-probability case through the totalized definition of
`cond`. -/
theorem cond_prod_prod_univ
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure ν] (s : Set α) :
    (μ.prod ν)[|s ×ˢ (Set.univ : Set β)] = μ[|s].prod ν := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod]
  simp only [measure_univ, mul_one]
  rw [← Measure.restrict_prod_eq_prod_univ]
  exact (Measure.prod_smul_left (μ := μ.restrict s) (ν := ν) _).symm

/-- A measurable pushforward commutes with conditioning on the preimage of a
measurable target event. -/
theorem map_cond_preimage
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) :
    Measure.map f μ[|f ⁻¹' s] = (Measure.map f μ)[|s] := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, ← Measure.restrict_map hf hs,
    Measure.map_apply hf hs]

end

end LogdetLean.Coherence
