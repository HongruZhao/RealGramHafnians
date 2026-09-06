import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorEnergy
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
/-!
# Continuity and measurability of the odd cofactor data

All objects are explicit finite sums and products of coordinates.  This file
records the resulting continuity and Borel measurability for later uses of
Tonelli and conditional distributions.
-/

namespace LogdetLean.GramHafnian

noncomputable section

/-- Each exact hafnian cofactor is a continuous polynomial of the literal
complex column matrix. -/
theorem continuous_oddHafnianCofactorVector_apply
    {r k : ℕ} (hr : 1 ≤ r) (j : OddCofactorIndex r hr) :
    Continuous (fun X : ComplexColumnMatrix r k ↦
      oddHafnianCofactorVector hr X j) := by
  unfold oddHafnianCofactorVector hafnianPairCofactor typeHafnian
    typeMatchingMonomial transposeGram rowMatrix
  fun_prop

/-- The entire finite cofactor vector is continuous. -/
theorem continuous_oddHafnianCofactorVector
    {r k : ℕ} (hr : 1 ≤ r) :
    Continuous (oddHafnianCofactorVector (k := k) hr) := by
  exact continuous_pi fun j ↦
    continuous_oddHafnianCofactorVector_apply hr j

/-- Each coordinate of `A_r C_r` is continuous. -/
theorem continuous_oddCofactorColumnCombination_apply
    {r k : ℕ} (hr : 1 ≤ r) (a : Fin k) :
    Continuous (fun X : ComplexColumnMatrix r k ↦
      oddCofactorColumnCombination hr X a) := by
  unfold oddCofactorColumnCombination
  apply continuous_finsetSum
  intro j _hj
  have hcoord : Continuous (fun X : ComplexColumnMatrix r k ↦ X j.1 a) := by
    fun_prop
  exact hcoord.mul (continuous_oddHafnianCofactorVector_apply hr j)

/-- The vector `A_r C_r` is continuous. -/
theorem continuous_oddCofactorColumnCombination
    {r k : ℕ} (hr : 1 ≤ r) :
    Continuous (oddCofactorColumnCombination (k := k) hr) := by
  exact continuous_pi fun a ↦
    continuous_oddCofactorColumnCombination_apply hr a

/-- The squared cofactor energy `W_r` is continuous. -/
theorem continuous_oddCofactorW {r k : ℕ} (hr : 1 ≤ r) :
    Continuous (oddCofactorW (k := k) hr) := by
  unfold oddCofactorW
  apply continuous_finsetSum
  intro j _hj
  exact Complex.continuous_normSq.comp
    (continuous_oddHafnianCofactorVector_apply hr j)

/-- The conditional-variance energy `V_r` is continuous. -/
theorem continuous_oddCofactorV {r k : ℕ} (hr : 1 ≤ r) :
    Continuous (oddCofactorV (k := k) hr) := by
  unfold oddCofactorV
  apply continuous_finsetSum
  intro a _ha
  exact Complex.continuous_normSq.comp
    (continuous_oddCofactorColumnCombination_apply hr a)

theorem measurable_oddHafnianCofactorVector
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (oddHafnianCofactorVector (k := k) hr) :=
  (continuous_oddHafnianCofactorVector hr).measurable

theorem measurable_oddCofactorColumnCombination
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (oddCofactorColumnCombination (k := k) hr) :=
  (continuous_oddCofactorColumnCombination hr).measurable

theorem measurable_oddCofactorW {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (oddCofactorW (k := k) hr) :=
  (continuous_oddCofactorW hr).measurable

theorem measurable_oddCofactorV {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (oddCofactorV (k := k) hr) :=
  (continuous_oddCofactorV hr).measurable

end

end LogdetLean.GramHafnian
