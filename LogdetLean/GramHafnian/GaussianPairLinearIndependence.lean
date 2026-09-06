import LogdetLean.GaussianLinearIndependence
import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Almost-sure linear independence of a Gaussian pair

This is the product-measure adapter used by the rank-two conditional moment.
-/

open MeasureTheory ProbabilityTheory Module

namespace LogdetLean.GramHafnian

noncomputable section

/-- Two independent standard Gaussian vectors are linearly independent
almost surely as soon as the ambient dimension is at least two. -/
theorem ae_linearIndependent_gaussianPair
    (k : ℕ) (hk : 2 ≤ k) :
    ∀ᵐ z : (EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))
      ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin k)))),
      LinearIndependent ℝ ![z.1, z.2] := by
  let E := EuclideanSpace ℝ (Fin k)
  let toTuple : E × E → (Fin 2 → E) :=
    (MeasurableEquiv.finTwoArrow : (Fin 2 → E) ≃ᵐ E × E).symm
  have hdim : 2 ≤ finrank ℝ E := by simpa [E] using hk
  have htuple :
      ∀ᵐ v ∂(Measure.pi fun _ : Fin 2 ↦ stdGaussian E),
        LinearIndependent ℝ v :=
    LogdetLean.ae_linearIndependent_pi_stdGaussian (E := E) 2 hdim
  have hmp : MeasurePreserving toTuple
      ((stdGaussian E).prod (stdGaussian E))
      (Measure.pi fun _ : Fin 2 ↦ stdGaussian E) := by
    exact (measurePreserving_finTwoArrow (stdGaussian E)).symm
      (MeasurableEquiv.finTwoArrow : (Fin 2 → E) ≃ᵐ E × E)
  have hpull :
      ∀ᵐ z ∂((stdGaussian E).prod (stdGaussian E)),
        LinearIndependent ℝ (toTuple z) :=
    hmp.quasiMeasurePreserving.ae htuple
  filter_upwards [hpull] with z hz
  change LinearIndependent ℝ (toTuple z) at hz
  have htupleEq : toTuple z = ![z.1, z.2] := by
    funext i
    fin_cases i <;> rfl
  rwa [htupleEq] at hz

end

end LogdetLean.GramHafnian
