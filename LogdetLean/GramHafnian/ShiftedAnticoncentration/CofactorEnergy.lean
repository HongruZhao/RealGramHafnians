import LogdetLean.GramHafnian.GramMomentFubini
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorExpansion
/-!
# The odd Gram-hafnian cofactor vector and its energies

For a literal `k × 2r` column matrix, the distinguished vertex is its last
column.  The remaining `2r-1` vertices index the odd cofactor vector.  The
definitions below are exactly

`C_j = haf(A_{-j}ᵀ A_{-j})`, `W = ‖C‖²`, and `V = ‖A C‖²`.

They are phrased directly in the existing `ComplexColumnMatrix` model.
-/

open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian

noncomputable section

/-- The last vertex of `Fin (2*r)` in the nonempty regime `r ≥ 1`. -/
def evenLastIndex (r : ℕ) (hr : 1 ≤ r) : Fin (2 * r) :=
  ⟨2 * r - 1, by omega⟩

/-- Every other vertex lies strictly below the distinguished last vertex. -/
theorem lt_evenLastIndex {r : ℕ} (hr : 1 ≤ r) (j : Fin (2 * r))
    (hj : j ≠ evenLastIndex r hr) : j < evenLastIndex r hr := by
  apply Fin.lt_iff_val_lt_val.mpr
  change j.1 < 2 * r - 1
  have hjle : j.1 ≤ 2 * r - 1 := by omega
  rcases lt_or_eq_of_le hjle with hjlt | hjeq
  · exact hjlt
  · exfalso
    apply hj
    apply Fin.ext
    exact hjeq

/-- The `2r-1` indices left after exposing the last column. -/
abbrev OddCofactorIndex (r : ℕ) (hr : 1 ≤ r) :=
  {j : Fin (2 * r) // j ≠ evenLastIndex r hr}

theorem card_oddCofactorIndex (r : ℕ) (hr : 1 ≤ r) :
    Fintype.card (OddCofactorIndex r hr) = 2 * r - 1 := by
  rw [Fintype.card_subtype_compl]
  have hone : Fintype.card
      {j : Fin (2 * r) // j = evenLastIndex r hr} = 1 := by simp
  rw [hone]
  simp

/-- The exact odd hafnian-cofactor vector for the literal column model. -/
def oddHafnianCofactorVector {r k : ℕ} (hr : 1 ≤ r)
    (X : ComplexColumnMatrix r k) : OddCofactorIndex r hr → ℂ :=
  fun j ↦ hafnianPairCofactor (transposeGram (rowMatrix X))
    (evenLastIndex r hr) j

/-- Coordinate form of `A_r C_r`, where `A_r` consists of all columns except
the exposed last one. -/
def oddCofactorColumnCombination {r k : ℕ} (hr : 1 ≤ r)
    (X : ComplexColumnMatrix r k) : Fin k → ℂ :=
  fun a ↦ ∑ j : OddCofactorIndex r hr,
    X j.1 a * oddHafnianCofactorVector hr X j

/-- `W_r = ‖C_r‖²`, written as a literal finite sum of complex norm-squares. -/
def oddCofactorW {r k : ℕ} (hr : 1 ≤ r)
    (X : ComplexColumnMatrix r k) : ℝ :=
  ∑ j : OddCofactorIndex r hr,
    Complex.normSq (oddHafnianCofactorVector hr X j)

/-- `V_r = ‖A_r C_r‖²`, written in coordinates. -/
def oddCofactorV {r k : ℕ} (hr : 1 ≤ r)
    (X : ComplexColumnMatrix r k) : ℝ :=
  ∑ a : Fin k, Complex.normSq (oddCofactorColumnCombination hr X a)

theorem oddCofactorW_nonneg {r k : ℕ} (hr : 1 ≤ r)
    (X : ComplexColumnMatrix r k) : 0 ≤ oddCofactorW hr X := by
  unfold oddCofactorW
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

theorem oddCofactorV_nonneg {r k : ℕ} (hr : 1 ≤ r)
    (X : ComplexColumnMatrix r k) : 0 ≤ oddCofactorV hr X := by
  unfold oddCofactorV
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- At the first level the unique cofactor is the empty hafnian, hence one. -/
theorem oddHafnianCofactorVector_level_one
    {k : ℕ} (X : ComplexColumnMatrix 1 k)
    (j : OddCofactorIndex 1 (by omega)) :
    oddHafnianCofactorVector (by omega) X j = 1 := by
  letI : IsEmpty
      (TypePerfectMatching.PairComplement (evenLastIndex 1 (by omega)) j.1) :=
    ⟨fun p ↦ by
      have hjlt : j.1 < evenLastIndex 1 (by omega) :=
        lt_evenLastIndex (by omega) j.1 j.2
      have hplt : p.1 < evenLastIndex 1 (by omega) :=
        lt_evenLastIndex (by omega) p.1 p.2.1
      apply p.2.2
      apply Fin.ext
      change p.1.1 = j.1.1
      change p.1.1 < 1 at hplt
      change j.1.1 < 1 at hjlt
      omega⟩
  unfold oddHafnianCofactorVector hafnianPairCofactor
  exact typeHafnian_eq_one_of_isEmpty _

/-- The first cofactor energy is exactly `W₁ = 1`. -/
theorem oddCofactorW_level_one {k : ℕ} (X : ComplexColumnMatrix 1 k) :
    oddCofactorW (by omega) X = 1 := by
  unfold oddCofactorW
  simp_rw [oddHafnianCofactorVector_level_one X]
  simp [card_oddCofactorIndex]

/-- The public literal hafnian agrees with the finite-type hafnian used for
cofactor expansion. -/
theorem gramHafnian_eq_typeHafnian_transposeGram {r k : ℕ}
    (X : ComplexColumnMatrix r k) :
    gramHafnian (rowMatrix X) = typeHafnian (transposeGram (rowMatrix X)) := by
  symm
  exact typeHafnian_fin_eq_hafnian _

/-- Exact last-column expansion in the literal model:
`haf(XᵀX) = x_lastᵀ (A_r C_r)`. -/
theorem gramHafnian_eq_lastColumn_dot_cofactorCombination
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k) :
    gramHafnian (rowMatrix X) =
      ∑ a : Fin k, X (evenLastIndex r hr) a *
        oddCofactorColumnCombination hr X a := by
  rw [gramHafnian_eq_typeHafnian_transposeGram]
  rw [typeHafnian_expand_greatest (transposeGram (rowMatrix X))
    (evenLastIndex r hr) (lt_evenLastIndex hr)]
  unfold oddCofactorColumnCombination oddHafnianCofactorVector
  simp only [transposeGram_apply, rowMatrix]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- A cofactor is independent of the exposed last column. -/
theorem oddHafnianCofactorVector_congr_off_last
    {r k : ℕ} (hr : 1 ≤ r) {X Y : ComplexColumnMatrix r k}
    (hXY : ∀ i : Fin (2 * r), i ≠ evenLastIndex r hr → X i = Y i)
    (j : OddCofactorIndex r hr) :
    oddHafnianCofactorVector hr X j =
      oddHafnianCofactorVector hr Y j := by
  unfold oddHafnianCofactorVector hafnianPairCofactor
  congr 1
  funext p q
  unfold transposeGram
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowMatrix]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [hXY p.1 p.2.1, hXY q.1 q.2.1]

end

end LogdetLean.GramHafnian
