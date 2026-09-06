import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealBaseResolvent
/-!
# Exact finite iteration of the literal beta-one resolvent recursion

This file starts the recursion at level one and iterates the exact
auxiliary-Gamma coefficient.  The final bound has only the sum of the
transpose-Gram bad-event probabilities and the exact product of the
negative-half Gamma factors.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Proof-independent version of the literal level bad probability. -/
def pastRealCofactorGramBadProbabilityNat
    (r k : ℕ) (delta : ℝ) : ENNReal :=
  if hr : 1 ≤ r then
    pastRealCofactorGramBadProbability r k hr delta
  else 0

theorem pastRealCofactorGramBadProbabilityNat_eq
    {r k : ℕ} (hr : 1 ≤ r) (delta : ℝ) :
    pastRealCofactorGramBadProbabilityNat r k delta =
      pastRealCofactorGramBadProbability r k hr delta := by
  simp [pastRealCofactorGramBadProbabilityNat, hr]

/-- Sum of the literal matrix bad-event probabilities from levels two
through `n`.  Level one is treated exactly by its chi-square law. -/
def pastRealCofactorGramBadProbabilitySum
    (n k : ℕ) (delta : ℝ) : ENNReal :=
  ∑ r ∈ Finset.Icc 2 n,
    pastRealCofactorGramBadProbabilityNat r k delta

/-- Exact level-one chi-square negative-half moment. -/
def pastRealCofactorBaseHalfFactor (k : ℕ) : ENNReal :=
  realAuxiliaryGammaHalfFactor k

/-- Exact product coefficient multiplying `sqrt lambda` after `n` levels. -/
def pastRealCofactorHalfFactorProduct
    (n k : ℕ) (delta : ℝ) : ENNReal :=
  pastRealCofactorBaseHalfFactor k *
    ∏ r ∈ Finset.Icc 2 n,
      pastRealCofactorLevelHalfFactor r k delta

theorem pastRealCofactorGramBadProbabilitySum_one
    (k : ℕ) (delta : ℝ) :
    pastRealCofactorGramBadProbabilitySum 1 k delta = 0 := by
  simp [pastRealCofactorGramBadProbabilitySum]

theorem pastRealCofactorHalfFactorProduct_one
    (k : ℕ) (delta : ℝ) :
    pastRealCofactorHalfFactorProduct 1 k delta =
      realAuxiliaryGammaHalfFactor k := by
  simp [pastRealCofactorHalfFactorProduct, pastRealCofactorBaseHalfFactor]

theorem pastRealCofactorGramBadProbabilitySum_succ
    (j k : ℕ) (hj : 1 ≤ j) (delta : ℝ) :
    pastRealCofactorGramBadProbabilitySum (j + 1) k delta =
      pastRealCofactorGramBadProbabilitySum j k delta +
        pastRealCofactorGramBadProbability (j + 1) k (by omega) delta := by
  unfold pastRealCofactorGramBadProbabilitySum
  rw [Finset.sum_Icc_succ_top (by omega)]
  rw [pastRealCofactorGramBadProbabilityNat_eq (by omega) delta]

theorem pastRealCofactorHalfFactorProduct_succ
    (j k : ℕ) (hj : 1 ≤ j) (delta : ℝ) :
    pastRealCofactorHalfFactorProduct (j + 1) k delta =
      pastRealCofactorHalfFactorProduct j k delta *
        pastRealCofactorLevelHalfFactor (j + 1) k delta := by
  unfold pastRealCofactorHalfFactorProduct
  rw [Finset.prod_Icc_succ_top (by omega)]
  ac_rfl

/-- Exact finite literal beta-one resolvent theorem. -/
theorem pastRealCofactorHalfResolvent_le_finite_gamma_product
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hdeltalt : delta < 1)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    pastRealCofactorHalfResolvent n k hn lambda ≤
      pastRealCofactorGramBadProbabilitySum n k delta +
        pastRealCofactorHalfFactorProduct n k delta *
          ENNReal.ofReal (Real.sqrt lambda) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j hj ↦
    ∀ t : ℝ, 0 < t →
      pastRealCofactorHalfResolvent j k hj t ≤
        pastRealCofactorGramBadProbabilitySum j k delta +
          pastRealCofactorHalfFactorProduct j k delta *
            ENNReal.ofReal (Real.sqrt t)
  have hP : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · intro t ht
      simpa [P, pastRealCofactorGramBadProbabilitySum_one,
        pastRealCofactorHalfFactorProduct_one] using
        pastRealCofactorHalfResolvent_one_le_exact_sqrt_envelope hk t ht
    · intro j hj ih t ht
      have hstep :=
        pastRealCofactorHalfResolvent_le_of_lower_sqrt_envelope
          (r := j + 1) (k := k) (by omega) (by omega)
          (by omega) delta hdelta hdeltalt
          (pastRealCofactorGramBadProbabilitySum j k delta)
          (pastRealCofactorHalfFactorProduct j k delta)
          (by
            intro s hs
            simpa using ih s hs)
          t ht
      rw [pastRealCofactorGramBadProbabilitySum_succ j k hj delta,
        pastRealCofactorHalfFactorProduct_succ j k hj delta]
      simpa [P] using hstep
  exact hP lambda hlambda

end

end LogdetLean.GramHafnian
