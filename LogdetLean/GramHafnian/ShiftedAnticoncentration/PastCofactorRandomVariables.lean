import LogdetLean.GramHafnian.ShiftedAnticoncentration.LastColumnProduct
/-!
# Random variables on the non-final-column probability space

Both one-step analytic arguments use the same iid family of `2r-1` past
columns.  This module fixes the literal cofactor vector and its two energies
on that common space.
-/

namespace LogdetLean.GramHafnian

noncomputable section

/-- The odd hafnian-cofactor vector as a function of the iid past columns. -/
def pastHafnianCofactorVector {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    OddCofactorIndex r hr → ℂ :=
  oddHafnianCofactorVector hr (pastCofactorMatrix hr A)

/-- `W_r = ‖C_r‖²` on the exact iid past-column space. -/
def pastCofactorW {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) : ℝ :=
  oddCofactorW hr (pastCofactorMatrix hr A)

@[fun_prop]
theorem measurable_pastHafnianCofactorVector {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastHafnianCofactorVector (k := k) hr) := by
  unfold pastHafnianCofactorVector pastCofactorMatrix
  exact (measurable_oddHafnianCofactorVector hr).comp
    ((lastColumnProductEquiv r k hr).measurable.comp
      (measurable_id.prodMk measurable_const))

@[fun_prop]
theorem measurable_pastCofactorW {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastCofactorW (k := k) hr) := by
  unfold pastCofactorW pastCofactorMatrix
  exact (measurable_oddCofactorW hr).comp
    ((lastColumnProductEquiv r k hr).measurable.comp
      (measurable_id.prodMk measurable_const))

theorem pastCofactorW_nonneg {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    0 ≤ pastCofactorW hr A :=
  oddCofactorW_nonneg hr (pastCofactorMatrix hr A)

theorem pastCofactorV_nonneg {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    0 ≤ pastCofactorV hr A :=
  oddCofactorV_nonneg hr (pastCofactorMatrix hr A)

/-- Coordinate formula for the past cofactor energy. -/
theorem pastCofactorW_eq_sum_normSq {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    pastCofactorW hr A =
      ∑ j : OddCofactorIndex r hr,
        Complex.normSq (pastHafnianCofactorVector hr A j) := by
  rfl

end

end LogdetLean.GramHafnian
