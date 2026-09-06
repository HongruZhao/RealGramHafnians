import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorAlmostSurePositivity
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorInverseMomentAssembly
import LogdetLean.GramHafnian.ShiftedAnticoncentration.ENNAssembly
/-!
# Final literal assembly from the two analytic one-step estimates

This file closes every deterministic and measure-theoretic step after the
Fourier-compression and conditional-Wishart inverse-moment inequalities.  Its
two hypotheses are precisely the public levelwise endpoints supplied by those
analytic modules.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The literal Fourier and Wishart one-step bounds imply the exact public
shifted-anticoncentration theorem. -/
theorem gaussianGramHafnianShiftedAnticoncentration_of_steps
    (hFourier : ∀ k r : ℕ, 2 ≤ r → 4 * r ≤ k →
      pastCofactorWInverseMoment k r ≤
        pastCofactorVInverseMoment k (r - 1) *
          ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹))
    (hWishart : ∀ k r : ℕ, 2 ≤ r → 4 * r ≤ k →
      pastCofactorVInverseMoment k r ≤
        pastCofactorWInverseMoment k r *
          ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹)) :
    GaussianGramHafnianShiftedAnticoncentration := by
  intro n k hn hkn z eps heps
  have hInv : pastCofactorVInverseMoment k n ≤
      ENNReal.ofReal (inverseVarianceBound k n) := by
    apply pastCofactorVInverseMoment_le_inverseVarianceBound_of_steps
      k n hn hkn
    · intro r hr2 hrn
      exact hFourier k r hr2 (by omega)
    · intro r hr2 hrn
      exact hWishart k r hr2 (by omega)
  have hVfull :=
    ae_oddCofactorV_pos_circularGaussianColumnMatrix hn (by omega : 2 * n - 1 ≤ k)
  have hVpast := ae_pastCofactorV_pos_of_ae_oddCofactorV_pos hn hVfull
  have hrho : 0 ≤ eps * gramHafnianSigma k n :=
    mul_nonneg heps (gramHafnianSigma_nonneg k n)
  have hraw :=
    circularGaussianColumnMatrix_shiftedSmallBall_le_pastInverseMoment
      hn hVpast z (eps * gramHafnianSigma k n) hrho
  have henn :
      (circularGaussianColumnMatrixMeasure n k)
          (gramHafnianShiftedSmallBallEvent k n z eps) ≤
        ENNReal.ofReal ((eps * gramHafnianSigma k n) ^ 2) *
          ENNReal.ofReal (inverseVarianceBound k n) := by
    calc
      (circularGaussianColumnMatrixMeasure n k)
          (gramHafnianShiftedSmallBallEvent k n z eps) ≤
          ENNReal.ofReal ((eps * gramHafnianSigma k n) ^ 2) *
            ennInverseMoment
              (Measure.pi fun _ : OddCofactorIndex n hn ↦
                circularGaussianVector k)
              (pastCofactorV hn) := by
        simpa [gramHafnianShiftedSmallBallEvent] using hraw
      _ = ENNReal.ofReal ((eps * gramHafnianSigma k n) ^ 2) *
          pastCofactorVInverseMoment k n := by
        rw [pastCofactorVInverseMoment_eq hn]
      _ ≤ ENNReal.ofReal ((eps * gramHafnianSigma k n) ^ 2) *
          ENNReal.ofReal (inverseVarianceBound k n) := by
        exact mul_le_mul le_rfl hInv bot_le bot_le
  exact normalizedSmallBall_of_ennInverseVarianceBound
    k n hn hkn z eps heps henn

end

end LogdetLean.GramHafnian
