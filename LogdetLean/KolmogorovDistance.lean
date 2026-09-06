import Mathlib.Probability.CDF
import Mathlib.Tactic
import LogdetLean.EdgeworthTransfer
/-!
# Kolmogorov distance for probability laws on the real line

This file supplies the small API needed by the paper.  It is defined directly
as the supremum distance between cumulative distribution functions.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Kolmogorov distance between two finite laws on the real line. -/
def kolmogorovDistance (μ ν : Measure ℝ) : ℝ :=
  supDistance (ProbabilityTheory.cdf μ) (ProbabilityTheory.cdf ν)

/-- Every pair of CDFs differs pointwise by at most one. -/
theorem abs_cdf_sub_cdf_le_one (μ ν : Measure ℝ) (x : ℝ) :
    |ProbabilityTheory.cdf μ x - ProbabilityTheory.cdf ν x| ≤ 1 := by
  rw [abs_le]
  constructor <;>
    linarith [ProbabilityTheory.cdf_nonneg μ x,
      ProbabilityTheory.cdf_le_one μ x,
      ProbabilityTheory.cdf_nonneg ν x,
      ProbabilityTheory.cdf_le_one ν x]

/-- Kolmogorov distance is nonnegative. -/
theorem kolmogorovDistance_nonneg (μ ν : Measure ℝ) :
    0 ≤ kolmogorovDistance μ ν := by
  have hpoint := point_le_supDistance (fun x ↦ abs_cdf_sub_cdf_le_one μ ν x) 0
  exact (abs_nonneg _).trans hpoint

/-- Kolmogorov distance is at most one. -/
theorem kolmogorovDistance_le_one (μ ν : Measure ℝ) :
    kolmogorovDistance μ ν ≤ 1 :=
  supDistance_le_of_bound (fun x ↦ abs_cdf_sub_cdf_le_one μ ν x)

/-- Kolmogorov distance is symmetric. -/
theorem kolmogorovDistance_comm (μ ν : Measure ℝ) :
    kolmogorovDistance μ ν = kolmogorovDistance ν μ := by
  unfold kolmogorovDistance supDistance
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, abs_sub_comm _ _⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, abs_sub_comm _ _⟩

/-- Kolmogorov distance satisfies the triangle inequality. -/
theorem kolmogorovDistance_triangle (μ ν ρ : Measure ℝ) :
    kolmogorovDistance μ ρ ≤
      kolmogorovDistance μ ν + kolmogorovDistance ν ρ := by
  apply supDistance_le_of_bound
  intro x
  calc
    |ProbabilityTheory.cdf μ x - ProbabilityTheory.cdf ρ x| ≤
        |ProbabilityTheory.cdf μ x - ProbabilityTheory.cdf ν x| +
          |ProbabilityTheory.cdf ν x - ProbabilityTheory.cdf ρ x| := by
            exact abs_sub_le _ _ _
    _ ≤ kolmogorovDistance μ ν + kolmogorovDistance ν ρ := by
      apply add_le_add
      · exact point_le_supDistance
          (fun y ↦ abs_cdf_sub_cdf_le_one μ ν y) x
      · exact point_le_supDistance
          (fun y ↦ abs_cdf_sub_cdf_le_one ν ρ y) x

end

end LogdetLean
