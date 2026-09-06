import LogdetLean.GramHafnian.ShiftedAnticoncentration.AssemblyAlgebra
import LogdetLean.GramHafnian.ShiftedAnticoncentration.ENNInverseMomentRecurrence
/-!
# Literal `ENNReal` probability to the normalized theorem

The conditioning argument controls the literal measure of the disk in
`ENNReal`.  This file performs the sole conversion to the real-valued
probability used in the public statement and then invokes the exact
normalization algebra.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- An `ENNReal` raw disk estimate with the final inverse-variance product
implies the exact normalized shifted anticoncentration coefficient. -/
theorem normalizedSmallBall_of_ennInverseVarianceBound
    (k n : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps)
    (henn :
      (circularGaussianColumnMatrixMeasure n k)
          (gramHafnianShiftedSmallBallEvent k n z eps) ≤
        ENNReal.ofReal ((eps * gramHafnianSigma k n) ^ 2) *
          ENNReal.ofReal (inverseVarianceBound k n)) :
    gramHafnianShiftedSmallBallProbability k n z eps ≤
      shiftedAnticoncentrationConstant k n * eps ^ 2 := by
  have hbound : 0 ≤ inverseVarianceBound k n :=
    inverseVarianceBound_nonneg_of_le hkn hn le_rfl
  have hrhs_ne_top :
      ENNReal.ofReal ((eps * gramHafnianSigma k n) ^ 2) *
          ENNReal.ofReal (inverseVarianceBound k n) ≠ ⊤ := by
    finiteness
  have hreal := ENNReal.toReal_mono hrhs_ne_top henn
  have hraw : gramHafnianShiftedSmallBallProbability k n z eps ≤
      (eps * gramHafnianSigma k n) ^ 2 * inverseVarianceBound k n := by
    unfold gramHafnianShiftedSmallBallProbability
    rw [Measure.real]
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal hbound] using hreal
  exact normalizedSmallBall_of_paperInverseVarianceBound
    k n hn hkn z eps (inverseVarianceBound k n) heps hraw le_rfl

end

end LogdetLean.GramHafnian
