import LogdetLean.GramHafnian.ShiftedAnticoncentration.FinalAssembly
import LogdetLean.GramHafnian.ShiftedAnticoncentration.SimplifiedConstantBound
/-!
# Simplified polynomial coefficient after the literal final assembly
-/

open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The two literal analytic steps also imply the paper's simpler exponential
upper bound for the normalized shifted small-ball coefficient. -/
theorem gaussianGramHafnianShiftedAnticoncentration_simplified_of_steps
    (hFourier : ∀ k r : ℕ, 2 ≤ r → 4 * r ≤ k →
      pastCofactorWInverseMoment k r ≤
        pastCofactorVInverseMoment k (r - 1) *
          ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹))
    (hWishart : ∀ k r : ℕ, 2 ≤ r → 4 * r ≤ k →
      pastCofactorVInverseMoment k r ≤
        pastCofactorWInverseMoment k r *
          ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹)) :
    ∀ n k : ℕ, 1 ≤ n → 4 * n ≤ k →
      ∀ z : ℂ, ∀ eps : ℝ, 0 ≤ eps →
        gramHafnianShiftedSmallBallProbability k n z eps ≤
          (2 * Real.sqrt (n : ℝ) *
            Real.exp
              (1 / ((k : ℝ) - 1) +
                (3 * (n : ℝ) ^ 2 - 3) /
                  ((k : ℝ) - 4 * (n : ℝ) + 1))) * eps ^ 2 := by
  intro n k hn hkn z eps heps
  have hmain :=
    gaussianGramHafnianShiftedAnticoncentration_of_steps hFourier hWishart
      n k hn hkn z eps heps
  calc
    gramHafnianShiftedSmallBallProbability k n z eps ≤
        shiftedAnticoncentrationConstant k n * eps ^ 2 := hmain
    _ ≤ (2 * Real.sqrt (n : ℝ) *
          Real.exp
            (1 / ((k : ℝ) - 1) +
              (3 * (n : ℝ) ^ 2 - 3) /
                ((k : ℝ) - 4 * (n : ℝ) + 1))) * eps ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (shiftedAnticoncentrationConstant_le_simplified hn hkn)
        (sq_nonneg eps)

end

end LogdetLean.GramHafnian
