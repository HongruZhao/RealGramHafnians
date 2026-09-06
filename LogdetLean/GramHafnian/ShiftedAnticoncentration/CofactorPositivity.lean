import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorMeasurable
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianDisk
/-!
# Deterministic positivity of the cofactor energy

If the past columns are complex-linearly independent and the odd hafnian
cofactor vector is nonzero, then `A C` is nonzero and hence `V = ‖A C‖²`
is strictly positive.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- The coordinate definition of `V` is the squared Euclidean norm of the
cofactor column combination. -/
theorem oddCofactorV_eq_normSq_combination
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k) :
    oddCofactorV hr X =
      ‖(WithLp.toLp 2 (oddCofactorColumnCombination hr X) :
        CircularEuclideanSpace k)‖ ^ 2 := by
  unfold oddCofactorV
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro a _ha
  exact Complex.normSq_eq_norm_sq _

/-- The Euclidean vector `A C` is the finite complex linear combination of
the past columns with coefficients given by the odd cofactor vector. -/
theorem sum_smul_pastColumns_eq_cofactorCombination
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k) :
    (∑ j : OddCofactorIndex r hr,
        oddHafnianCofactorVector hr X j •
          (WithLp.toLp 2 (X j.1) : CircularEuclideanSpace k)) =
      WithLp.toLp 2 (oddCofactorColumnCombination hr X) := by
  apply (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).injective
  simp only [map_sum, map_smul, WithLp.coe_linearEquiv,
    WithLp.ofLp_toLp]
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold oddCofactorColumnCombination
  apply Finset.sum_congr rfl
  intro j _hj
  exact mul_comm _ _

/-- Full complex column rank makes `C ↦ A C` injective. -/
theorem cofactorCombination_ne_zero_of_linearIndependent
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k)
    (hLI : LinearIndependent ℂ
      (fun j : OddCofactorIndex r hr =>
        (WithLp.toLp 2 (X j.1) : CircularEuclideanSpace k)))
    (hC : oddHafnianCofactorVector hr X ≠ 0) :
    oddCofactorColumnCombination hr X ≠ 0 := by
  intro hzero
  have hsum : (∑ j : OddCofactorIndex r hr,
      oddHafnianCofactorVector hr X j •
        (WithLp.toLp 2 (X j.1) : CircularEuclideanSpace k)) = 0 := by
    rw [sum_smul_pastColumns_eq_cofactorCombination hr X, hzero]
    rfl
  have hall := (Fintype.linearIndependent_iff.mp hLI)
    (oddHafnianCofactorVector hr X) hsum
  apply hC
  funext j
  exact hall j

/-- Strict positivity of `V` under the two deterministic nondegeneracy
conditions used by the almost-sure induction. -/
theorem oddCofactorV_pos_of_linearIndependent_of_cofactor_ne_zero
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k)
    (hLI : LinearIndependent ℂ
      (fun j : OddCofactorIndex r hr =>
        (WithLp.toLp 2 (X j.1) : CircularEuclideanSpace k)))
    (hC : oddHafnianCofactorVector hr X ≠ 0) :
    0 < oddCofactorV hr X := by
  rw [oddCofactorV_eq_normSq_combination]
  have hraw := cofactorCombination_ne_zero_of_linearIndependent hr X hLI hC
  have hlp : (WithLp.toLp 2 (oddCofactorColumnCombination hr X) :
      CircularEuclideanSpace k) ≠ 0 := by
    exact (WithLp.toLp_eq_zero 2).not.mpr hraw
  exact sq_pos_of_pos (norm_pos_iff.mpr hlp)

end

end LogdetLean.GramHafnian
