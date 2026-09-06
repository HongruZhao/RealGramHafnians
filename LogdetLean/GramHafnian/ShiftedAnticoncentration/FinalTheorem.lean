import LogdetLean.GramHafnian.ShiftedAnticoncentration.FinalAssembly
import LogdetLean.GramHafnian.ShiftedAnticoncentration.SimplifiedFinalAssembly
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.LiteralFourierStep
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralWishartStep
/-!
# Unconditional shifted anticoncentration for Gaussian Gram hafnians

This module joins the literal Fourier and conditional-Wishart steps to the
deterministic final assembly.  It also records the probability-capped forms
with right-hand side `min 1 (B * ε ^ 2)`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- **Exact shifted-anticoncentration theorem.**

For every admissible rectangular dimension, every complex shift, and every
nonnegative radius, the literal Gaussian Gram hafnian has the exact finite
`ε²` small-ball bound encoded by `shiftedAnticoncentrationConstant`. -/
theorem gaussianGramHafnianShiftedAnticoncentration :
    GaussianGramHafnianShiftedAnticoncentration := by
  apply gaussianGramHafnianShiftedAnticoncentration_of_steps
  · intro k r hr2 hk
    exact pastCofactorWInverseMoment_le_fourier k r hr2 (by omega)
  · intro k r hr2 hk
    exact Wishart.pastCofactorVInverseMoment_le_wishart k r hr2 hk

/-- The exact theorem with the paper's simpler explicit coefficient. -/
theorem gaussianGramHafnianShiftedAnticoncentration_simplified :
    ∀ n k : ℕ, 1 ≤ n → 4 * n ≤ k →
      ∀ z : ℂ, ∀ eps : ℝ, 0 ≤ eps →
        gramHafnianShiftedSmallBallProbability k n z eps ≤
          (2 * Real.sqrt (n : ℝ) *
            Real.exp
              (1 / ((k : ℝ) - 1) +
                (3 * (n : ℝ) ^ 2 - 3) /
                  ((k : ℝ) - 4 * (n : ℝ) + 1))) * eps ^ 2 := by
  apply gaussianGramHafnianShiftedAnticoncentration_simplified_of_steps
  · intro k r hr2 hk
    exact pastCofactorWInverseMoment_le_fourier k r hr2 (by omega)
  · intro k r hr2 hk
    exact Wishart.pastCofactorVInverseMoment_le_wishart k r hr2 hk

/-- Probability-capped form of the exact finite theorem. -/
theorem gaussianGramHafnianShiftedAnticoncentration_min :
    ∀ n k : ℕ, 1 ≤ n → 4 * n ≤ k →
      ∀ z : ℂ, ∀ eps : ℝ, 0 ≤ eps →
        gramHafnianShiftedSmallBallProbability k n z eps ≤
          min 1 (shiftedAnticoncentrationConstant k n * eps ^ 2) := by
  intro n k hn hk z eps heps
  apply le_min
  · unfold gramHafnianShiftedSmallBallProbability
    exact measureReal_le_one
  · exact gaussianGramHafnianShiftedAnticoncentration
      n k hn hk z eps heps

/-- Probability-capped form with the simpler explicit coefficient. -/
theorem gaussianGramHafnianShiftedAnticoncentration_simplified_min :
    ∀ n k : ℕ, 1 ≤ n → 4 * n ≤ k →
      ∀ z : ℂ, ∀ eps : ℝ, 0 ≤ eps →
        gramHafnianShiftedSmallBallProbability k n z eps ≤
          min 1
            ((2 * Real.sqrt (n : ℝ) *
              Real.exp
                (1 / ((k : ℝ) - 1) +
                  (3 * (n : ℝ) ^ 2 - 3) /
                    ((k : ℝ) - 4 * (n : ℝ) + 1))) * eps ^ 2) := by
  intro n k hn hk z eps heps
  apply le_min
  · unfold gramHafnianShiftedSmallBallProbability
    exact measureReal_le_one
  · exact gaussianGramHafnianShiftedAnticoncentration_simplified
      n k hn hk z eps heps

end

end LogdetLean.GramHafnian
