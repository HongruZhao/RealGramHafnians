import Mathlib.Probability.ConditionalProbability
/-!
# Real-valued conditional-probability identities

The factorial-moment assembly is written with `Measure.real`.  This file
records the finite-measure form of the elementary identity

`P(A ∩ B) = P(A) P(B | A)`.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

/-- Real-valued multiplication rule for conditioning on a measurable event.
The order of the two real factors is chosen to match the coherence matching
calculation. -/
theorem measureReal_inter_eq_measureReal_mul_cond
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (s t : Set Ω) (hs : MeasurableSet s) :
    μ.real (s ∩ t) = μ.real s * μ[|s].real t := by
  have h := cond_mul_eq_inter hs t μ
  have hreal := congrArg ENNReal.toReal h
  simpa [Measure.real, ENNReal.toReal_mul, mul_comm] using hreal.symm

/-- The same multiplication rule with the intersection written in the
opposite order. -/
theorem measureReal_inter_eq_cond_mul_measureReal
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (s t : Set Ω) (hs : MeasurableSet s) :
    μ.real (t ∩ s) = μ[|s].real t * μ.real s := by
  rw [inter_comm]
  simpa [mul_comm] using measureReal_inter_eq_measureReal_mul_cond μ s t hs

end

end LogdetLean.Coherence
