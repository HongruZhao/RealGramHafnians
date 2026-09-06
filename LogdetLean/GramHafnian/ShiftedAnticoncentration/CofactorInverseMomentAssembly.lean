import LogdetLean.GramHafnian.ShiftedAnticoncentration.PastCofactorRandomVariables
import LogdetLean.GramHafnian.ShiftedAnticoncentration.BaseInverseMoment
import LogdetLean.GramHafnian.ShiftedAnticoncentration.ENNInverseMomentRecurrence
/-!
# Assembly of the two literal one-step inverse-moment inequalities

This module gives names to the levelwise `V_r` and `W_r` inverse moments
and verifies that the Fourier factor `(2r-2)^{-1}` and conditional-Wishart
factor `(k-4r+1)^{-1}` multiply to the exact recurrence in the paper.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Extended-nonnegative inverse moment of the literal past variance `V_r`.
The value at the unused level `r=0` is set to zero. -/
def pastCofactorVInverseMoment (k r : ℕ) : ENNReal :=
  if hr : 1 ≤ r then
    ennInverseMoment
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)
      (pastCofactorV hr)
  else 0

/-- Extended-nonnegative inverse moment of the literal cofactor norm `W_r`.
The value at the unused level `r=0` is set to zero. -/
def pastCofactorWInverseMoment (k r : ℕ) : ENNReal :=
  if hr : 1 ≤ r then
    ennInverseMoment
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)
      (pastCofactorW hr)
  else 0

theorem pastCofactorVInverseMoment_eq
    {k r : ℕ} (hr : 1 ≤ r) :
    pastCofactorVInverseMoment k r =
      ennInverseMoment
        (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)
        (pastCofactorV hr) := by
  simp only [pastCofactorVInverseMoment, dif_pos hr]

theorem pastCofactorWInverseMoment_eq
    {k r : ℕ} (hr : 1 ≤ r) :
    pastCofactorWInverseMoment k r =
      ennInverseMoment
        (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)
        (pastCofactorW hr) := by
  simp only [pastCofactorWInverseMoment, dif_pos hr]

/-- Exact base value `E[V_1^{-1}] = (k-1)^{-1}` in the totalized notation. -/
theorem pastCofactorVInverseMoment_level_one
    {k : ℕ} (hk : 2 ≤ k) :
    pastCofactorVInverseMoment k 1 =
      ENNReal.ofReal (((k : ℝ) - 1)⁻¹) := by
  rw [pastCofactorVInverseMoment_eq (by omega)]
  exact ennInverseMoment_pastCofactorV_level_one hk

/-- The two analytic one-step estimates imply the exact finite inverse-
variance product.  The hypotheses are discharged later by the literal
Fourier-compression and conditional-Wishart theorems. -/
theorem pastCofactorVInverseMoment_le_inverseVarianceBound_of_steps
    (k n : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (hFourier : ∀ r, 2 ≤ r → r ≤ n →
      pastCofactorWInverseMoment k r ≤
        pastCofactorVInverseMoment k (r - 1) *
          ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹))
    (hWishart : ∀ r, 2 ≤ r → r ≤ n →
      pastCofactorVInverseMoment k r ≤
        pastCofactorWInverseMoment k r *
          ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹)) :
    pastCofactorVInverseMoment k n ≤
      ENNReal.ofReal (inverseVarianceBound k n) := by
  apply ennInverseVarianceBound_of_paper_recurrence
    (pastCofactorVInverseMoment k) n k hn hkn
  · apply le_of_eq
    exact pastCofactorVInverseMoment_level_one (by omega)
  · intro r hr2 hrn
    have hF := hFourier r hr2 hrn
    have hW := hWishart r hr2 hrn
    have ha : 0 ≤ ((2 : ℝ) * r - 2)⁻¹ := by
      apply inv_nonneg.mpr
      have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
      linarith
    have hb : 0 ≤ ((k : ℝ) - 4 * r + 1)⁻¹ := by
      apply inv_nonneg.mpr
      have hkr : 4 * r ≤ k := by omega
      have hkrR : (4 : ℝ) * r ≤ (k : ℝ) := by exact_mod_cast hkr
      linarith
    calc
      pastCofactorVInverseMoment k r ≤
          pastCofactorWInverseMoment k r *
            ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹) := hW
      _ ≤ (pastCofactorVInverseMoment k (r - 1) *
              ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹)) *
            ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹) := by
        exact mul_le_mul hF le_rfl bot_le bot_le
      _ = pastCofactorVInverseMoment k (r - 1) *
          ENNReal.ofReal (inverseVarianceStep k r) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul ha]
        congr 2
        unfold inverseVarianceStep
        rw [mul_inv]

end

end LogdetLean.GramHafnian
