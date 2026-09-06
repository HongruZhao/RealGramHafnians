import LogdetLean.GramHafnian.ShiftedAnticoncentration.InverseMomentRecurrence
/-!
# Extended-nonnegative inverse-moment recurrence

The literal probabilistic estimates are naturally `ENNReal` lintegral
inequalities.  This module iterates their exact factors without first
assuming finiteness or converting to ordinary integrals.
-/

open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Every partial inverse-variance product is nonnegative throughout the
paper range. -/
theorem inverseVarianceBound_nonneg_of_le
    {k n j : ℕ} (hkn : 4 * n ≤ k) (hj : 1 ≤ j) (hjn : j ≤ n) :
    0 ≤ inverseVarianceBound k j := by
  unfold inverseVarianceBound
  apply mul_nonneg
  · apply inv_nonneg.mpr
    have hk : 1 ≤ k := by omega
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  · apply Finset.prod_nonneg
    intro r hr
    have hrmem := Finset.mem_Icc.mp hr
    exact inverseVarianceStep_nonneg hkn hrmem.1 (hrmem.2.trans hjn)

/-- Appending the top level multiplies the real inverse-variance product by
the corresponding one-step factor. -/
theorem inverseVarianceBound_succ
    (k j : ℕ) (hj : 1 ≤ j) :
    inverseVarianceBound k (j + 1) =
      inverseVarianceBound k j * inverseVarianceStep k (j + 1) := by
  unfold inverseVarianceBound
  rw [Finset.prod_Icc_succ_top (by omega)]
  ring

/-- Exact `ENNReal` iteration of the paper's inverse-moment recurrence.
No finiteness hypothesis is used: finiteness follows from the displayed
finite upper bound. -/
theorem ennInverseVarianceBound_of_paper_recurrence
    (u : ℕ → ENNReal) (n k : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (hbase : u 1 ≤ ENNReal.ofReal (((k : ℝ) - 1)⁻¹))
    (hstep : ∀ r, 2 ≤ r → r ≤ n →
      u r ≤ u (r - 1) * ENNReal.ofReal (inverseVarianceStep k r)) :
    u n ≤ ENNReal.ofReal (inverseVarianceBound k n) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    j ≤ n → u j ≤ ENNReal.ofReal (inverseVarianceBound k j)
  have hind : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · intro _
      simpa [P, inverseVarianceBound] using hbase
    · intro j hj ih hsucc
      have hrec := hstep (j + 1) (by omega) hsucc
      have hih := ih (by omega)
      have hbound_nonneg : 0 ≤ inverseVarianceBound k j :=
        inverseVarianceBound_nonneg_of_le hkn hj (by omega)
      have hstep_nonneg : 0 ≤ inverseVarianceStep k (j + 1) :=
        inverseVarianceStep_nonneg hkn (by omega) (by omega)
      calc
        u (j + 1) ≤
            u j * ENNReal.ofReal (inverseVarianceStep k (j + 1)) := by
          simpa using hrec
        _ ≤ ENNReal.ofReal (inverseVarianceBound k j) *
            ENNReal.ofReal (inverseVarianceStep k (j + 1)) :=
          mul_le_mul hih le_rfl bot_le bot_le
        _ = ENNReal.ofReal
            (inverseVarianceBound k j * inverseVarianceStep k (j + 1)) := by
          rw [ENNReal.ofReal_mul hbound_nonneg]
        _ = ENNReal.ofReal (inverseVarianceBound k (j + 1)) := by
          rw [inverseVarianceBound_succ k j hj]
  exact hind le_rfl

end

end LogdetLean.GramHafnian
