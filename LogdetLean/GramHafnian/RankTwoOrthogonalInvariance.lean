import LogdetLean.GramHafnian.RankTwoCentralBinomial
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Prod
/-!
# Orthogonal invariance of the rank-two Gaussian bilinear form

This is the coordinate-free bridge to the two-coordinate calculation.  It
proves directly from Mathlib's standard-Gaussian invariance that a simultaneous
orthogonal change of coordinates in the deterministic vectors and the two
Gaussian vectors leaves every moment unchanged.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- Coordinate-free real version of the rank-two bilinear form. -/
def innerRankTwoBilinear (g₁ g₂ : E) (w : E × E) : Real :=
  inner Real g₁ w.1 * inner Real g₂ w.2 +
    inner Real g₁ w.2 * inner Real g₂ w.1

theorem map_prod_standardGaussian_linearIsometryEquiv
    (O : E ≃ₗᵢ[Real] E) :
    Measure.map (Prod.map O O)
        ((stdGaussian E).prod (stdGaussian E)) =
      (stdGaussian E).prod (stdGaussian E) := by
  have h := (Measure.map_prod_map (stdGaussian E) (stdGaussian E)
    (by fun_prop : Measurable O) (by fun_prop : Measurable O)).symm
  simpa only [stdGaussian_map] using h

/-- **Orthogonal-invariance bridge.**  Every natural moment of the rank-two
bilinear form depends only on the simultaneous orthogonal orbit of `(g₁,g₂)`.
No moment or invariance axiom is assumed. -/
theorem integral_innerRankTwoBilinear_pow_orthogonal
    (O : E ≃ₗᵢ[Real] E) (g₁ g₂ : E) (m : Nat) :
    (∫ w, innerRankTwoBilinear (O g₁) (O g₂) w ^ m
        ∂((stdGaussian E).prod (stdGaussian E))) =
      ∫ w, innerRankTwoBilinear g₁ g₂ w ^ m
        ∂((stdGaussian E).prod (stdGaussian E)) := by
  let mu := (stdGaussian E).prod (stdGaussian E)
  let T : E × E → E × E := Prod.map O O
  have hmap : Measure.map T mu = mu :=
    map_prod_standardGaussian_linearIsometryEquiv O
  have hmeasT : AEMeasurable T mu := by
    exact (by fun_prop : Measurable T).aemeasurable
  have hf : AEStronglyMeasurable
      (fun w ↦ innerRankTwoBilinear (O g₁) (O g₂) w ^ m)
      (Measure.map T mu) := by
    apply Measurable.aestronglyMeasurable
    unfold innerRankTwoBilinear
    fun_prop
  calc
    (∫ w, innerRankTwoBilinear (O g₁) (O g₂) w ^ m ∂mu) =
        ∫ w, innerRankTwoBilinear (O g₁) (O g₂) w ^ m
          ∂(Measure.map T mu) := by rw [hmap]
    _ = ∫ w, innerRankTwoBilinear (O g₁) (O g₂) (T w) ^ m ∂mu :=
      integral_map hmeasT hf
    _ = ∫ w, innerRankTwoBilinear g₁ g₂ w ^ m ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        unfold T innerRankTwoBilinear
        change (inner Real (O g₁) (O w.1) * inner Real (O g₂) (O w.2) +
          inner Real (O g₁) (O w.2) * inner Real (O g₂) (O w.1)) ^ m = _
        rw [O.inner_map_map, O.inner_map_map, O.inner_map_map, O.inner_map_map]

end

end LogdetLean.GramHafnian
