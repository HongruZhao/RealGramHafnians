import LogdetLean.GeneralRModel
import LogdetLean.Paper2608Computations
import Mathlib.Tactic
/-!
# Elementary matrix identities for a correlation matrix

This module isolates the deterministic identities used in both the old CLT
paper and the new quantitative paper.  For `A = R-I`, its squared Frobenius
energy is `a_R = tr(A^2)`.  Unit diagonal gives `tr A=0`, symmetry turns
`tr(A^2)` into a sum of squares, and consequently
`tr(R^2)=p+a_R`.

The argument is the matrix algebra in Zhao (2026), equation (5.11), pp.
13--14.  It is reproved here from finite sums; no spectral theorem is used.
-/

namespace LogdetLean

noncomputable section

open Matrix
open scoped BigOperators

namespace CorrelationMatrix

variable {p : ℕ} (R : CorrelationMatrix p)

/-- The off-identity part `A_R=R-I`. -/
def deviation : Matrix (Fin p) (Fin p) ℝ := R.val - 1

/-- The squared Frobenius/trace energy `a_R=tr(A_R^2)`. -/
def deviationEnergy : ℝ := Matrix.trace (R.deviation * R.deviation)

@[simp]
theorem deviation_apply (i j : Fin p) :
    R.deviation i j = R.val i j - if i = j then 1 else 0 := by
  by_cases hij : i = j <;> simp [deviation, hij]

@[simp]
theorem deviation_diag (i : Fin p) : R.deviation i i = 0 := by
  simp [deviation]

/-- `A_R` is symmetric. -/
theorem deviation_transpose : R.deviationᵀ = R.deviation := by
  rw [deviation, Matrix.transpose_sub, R.transpose_eq]
  simp

/-- Unit diagonal implies `tr(A_R)=0`. -/
theorem trace_deviation : Matrix.trace R.deviation = 0 := by
  simp [Matrix.trace]

/-- The trace energy is literally the finite sum of all entry squares. -/
theorem deviationEnergy_eq_sum_sq :
    R.deviationEnergy = ∑ i, ∑ j, (R.deviation i j) ^ 2 := by
  unfold deviationEnergy
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  have hs : R.deviation j i = R.deviation i j := by
    have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A i j)
      R.deviation_transpose
    simpa using h
  rw [hs]
  ring

theorem deviationEnergy_nonneg : 0 ≤ R.deviationEnergy := by
  rw [R.deviationEnergy_eq_sum_sq]
  positivity

/-- The energy can equivalently be summed only over off-diagonal entries. -/
theorem deviationEnergy_eq_sum_offDiag_sq :
    R.deviationEnergy =
      ∑ i, ∑ j with i ≠ j, (R.val i j) ^ 2 := by
  rw [R.deviationEnergy_eq_sum_sq]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hij : i = j
  · subst j
    simp
  · simp [deviation_apply, hij]

/-- The basic identity `R=I+A_R`. -/
theorem one_add_deviation : 1 + R.deviation = R.val := by
  simp [deviation]

/-- Equation (5.11): `tr(R^2)=p+a_R`. -/
theorem trace_square_eq_card_add_energy :
    Matrix.trace (R.val * R.val) =
      (Fintype.card (Fin p) : ℝ) + R.deviationEnergy := by
  rw [← R.one_add_deviation]
  exact trace_one_add_square_of_trace_eq_zero R.deviation R.trace_deviation

theorem trace_square_eq_dimension_add_energy :
    Matrix.trace (R.val * R.val) = (p : ℝ) + R.deviationEnergy := by
  simpa using R.trace_square_eq_card_add_energy

end CorrelationMatrix

end

end LogdetLean
