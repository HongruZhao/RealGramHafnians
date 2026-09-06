import RealGramHafnians.Proofs.RowSuspensionInverseRecursion
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealBaseResolvent
/-!
# Iteration of the sharp real row-suspension recursion
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 5000000

/-- Exact recursively accumulated Gamma coefficient. -/
def sharpRealGammaCoefficient : ℕ → ℕ → ENNReal
  | 0, _ => 1
  | 1, k => realAuxiliaryGammaHalfFactor k
  | n + 2, k =>
      sharpRealGammaCoefficient (n + 1) (k - 1) *
        realAuxiliaryGammaHalfFactor k *
        realAuxiliaryGammaHalfFactor (2 * (n + 2) - 1)

@[simp] theorem sharpRealGammaCoefficient_zero (k : ℕ) :
    sharpRealGammaCoefficient 0 k = 1 := rfl

@[simp] theorem sharpRealGammaCoefficient_one (k : ℕ) :
    sharpRealGammaCoefficient 1 k = realAuxiliaryGammaHalfFactor k := rfl

@[simp] theorem sharpRealGammaCoefficient_add_two (n k : ℕ) :
    sharpRealGammaCoefficient (n + 2) k =
      sharpRealGammaCoefficient (n + 1) (k - 1) *
        realAuxiliaryGammaHalfFactor k *
        realAuxiliaryGammaHalfFactor (2 * (n + 2) - 1) := rfl

/-- Exact iterated negative-half-moment estimate. -/
theorem sharpRealCofactorInverseSqrtMoment_le_coefficient
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    sharpRealCofactorInverseSqrtMoment n k hn ≤
      sharpRealGammaCoefficient n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              change sharpRealCofactorInverseSqrtMoment 1 k _ ≤ _
              rw [sharpRealGammaCoefficient_one]
              unfold sharpRealCofactorInverseSqrtMoment
              exact le_of_eq (ennInverseSqrtMoment_pastRealCofactorV_level_one hk)
          | succ n =>
              have hkpos : 1 ≤ k := by omega
              have hdimLower : 2 * (n + 1) - 1 ≤ k - 1 := by omega
              have hkLower : 2 ≤ k - 1 := by omega
              have hstep := sharpRealCofactorInverseSqrtMoment_step
                (r := n + 2) (k := k - 1) (by omega)
                (by simpa [Nat.sub_add_cancel hkpos] using hdim)
              have hih := ih (n + 1) (by omega) (k := k - 1)
                (by omega) hkLower hdimLower
              rw [Nat.sub_add_cancel hkpos] at hstep
              calc
                sharpRealCofactorInverseSqrtMoment (n + 2) k _ ≤
                    sharpRealCofactorInverseSqrtMoment (n + 1) (k - 1) _ *
                      realAuxiliaryGammaHalfFactor k *
                      realAuxiliaryGammaHalfFactor (2 * (n + 2) - 1) := hstep
                _ ≤ sharpRealGammaCoefficient (n + 1) (k - 1) *
                      realAuxiliaryGammaHalfFactor k *
                      realAuxiliaryGammaHalfFactor (2 * (n + 2) - 1) := by
                    gcongr
                _ = sharpRealGammaCoefficient (n + 2) k := by
                    rw [sharpRealGammaCoefficient_add_two]

end

end LogdetLean.GramHafnian
