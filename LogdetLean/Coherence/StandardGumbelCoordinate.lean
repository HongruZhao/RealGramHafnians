import LogdetLean.Coherence.AllGapJointIndependence
import Mathlib.Tactic
/-!
# Standard Gumbel coordinate for the null joint limit

This module records the exact affine reparametrization of the coherence
coordinate used in the public paper. It is a direct corollary of the
model-specific all-gap joint theorem; no new probabilistic hypothesis is
introduced.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory

/-- Affine transformation of the classical coherence statistic whose limiting
CDF is the standard Gumbel CDF `exp (-exp (-t))`. -/
def standardGumbelCoordinate (m p : ℕ)
    (data : NestedTuple (ObservationSpace (m + 1)) p) : ℝ :=
  coherenceExtreme m p data / 2 + Real.log (8 * Real.pi) / 2

/-- Joint lower-tail probability for the standardized log determinant and the
standard Gumbel coherence coordinate. -/
def gaussianGumbelJointLowerProbability
    (m p : ℕ) (z t : ℝ) : ℝ :=
  (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p
    {data | Z0mpStatistic m p data ≤ z ∧
      standardGumbelCoordinate m p data ≤ t}).toReal

/-- The affine Gumbel event is exactly the original coherence event at the
corresponding threshold. -/
theorem gaussianGumbelJointLowerProbability_eq_coherence
    (m p : ℕ) (z t : ℝ) :
    gaussianGumbelJointLowerProbability m p z t =
      gaussianCoherenceJointLowerProbability m p z
        (2 * t - Real.log (8 * Real.pi)) := by
  unfold gaussianGumbelJointLowerProbability
    gaussianCoherenceJointLowerProbability
  congr 2
  ext data
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, ht⟩
    refine ⟨hz, ?_⟩
    unfold standardGumbelCoordinate at ht
    linarith
  · rintro ⟨hz, hx⟩
    refine ⟨hz, ?_⟩
    unfold standardGumbelCoordinate
    linarith

/-- At the affine Gumbel threshold, the classical Poisson intensity is
exactly `exp (-t)`. -/
theorem classicalCoherenceIntensity_gumbel (t : ℝ) :
    classicalCoherenceIntensity (2 * t - Real.log (8 * Real.pi)) =
      Real.exp (-t) := by
  have hA : 0 < (8 * Real.pi : ℝ) := mul_pos (by norm_num) Real.pi_pos
  have hsqrt :
      Real.exp (Real.log (8 * Real.pi) / 2) = Real.sqrt (8 * Real.pi) := by
    rw [← Real.log_sqrt hA.le, Real.exp_log (Real.sqrt_pos.2 hA)]
  unfold classicalCoherenceIntensity
  rw [show -(2 * t - Real.log (8 * Real.pi)) / 2 =
      -t + Real.log (8 * Real.pi) / 2 by ring]
  rw [Real.exp_add, hsqrt]
  field_simp [(Real.sqrt_pos.2 hA).ne']

/-- **Standard-Gumbel null joint limit.** Along every nonsingular sequence,
the standardized log determinant and the affine coherence coordinate have the
product standard-normal/standard-Gumbel lower-tail limit. -/
theorem allGapGaussianStandardGumbelJointLimit
    (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (z t : ℝ) :
    Tendsto
      (fun p ↦ gaussianGumbelJointLowerProbability (mseq p) p z t)
      atTop
      (nhds (standardNormalCDF z * Real.exp (-Real.exp (-t)))) := by
  have h := allGapGaussianJointIndependence mseq hadm z
    (2 * t - Real.log (8 * Real.pi))
  convert h using 1
  · funext p
    exact gaussianGumbelJointLowerProbability_eq_coherence
      (mseq p) p z t
  · rw [classicalCoherenceIntensity_gumbel]

end

end LogdetLean.Coherence
