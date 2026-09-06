import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseInterior
/-!
# Exact background-coordinate cofactor decomposition

This file combines the two greatest-vertex expansions from
`CofactorPhaseInterior` and identifies the resulting ordered-pair formula
with the matrix `cofactorM`.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- A background cofactor split according to whether `Y` is paired with
`X` or with a background column `b`.  In the latter case the remaining
cofactor is expanded at `X`, whose mate is the ordered index `a`. -/
theorem twoExposedCofactor_background_eq_ordered_pair_sum
    {m k : ℕ} (A : TwoExposedColumnFamily m k) (j : Fin m) :
    twoExposedCofactorVector A (remainingIndex m j) =
      transposeDot (A (exposedXIndex m)) (A (exposedYIndex m)) *
          remainingHafnianDeleteOne A j +
        ∑ b : {b : Fin m // b ≠ j},
          transposeDot (A (remainingIndex m b.1)) (A (exposedYIndex m)) *
            ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
              transposeDot (A (remainingIndex m a.1))
                  (A (exposedXIndex m)) *
                remainingHafnianDeleteThree A j a.1 b.1 := by
  unfold twoExposedCofactorVector finiteGramCofactorVector
  rw [typeHafnian_expand_greatest _ (exposedYInDeleteRemaining m j)
    (deleteRemaining_greatest_Y m j)]
  calc
    (∑ y : {y : DeleteRemainingIndex m j //
        y ≠ exposedYInDeleteRemaining m j},
        columnTransposeGram
            (fun i : DeleteRemainingIndex m j ↦ A i.1)
          y.1 (exposedYInDeleteRemaining m j) *
          hafnianPairCofactor
            (columnTransposeGram
              (fun i : DeleteRemainingIndex m j ↦ A i.1))
            (exposedYInDeleteRemaining m j) y) =
        ∑ s : Option {b : Fin m // b ≠ j},
          columnTransposeGram
              (fun i : DeleteRemainingIndex m j ↦ A i.1)
            (deleteRemainingWithoutYEquiv m j s).1
            (exposedYInDeleteRemaining m j) *
            hafnianPairCofactor
              (columnTransposeGram
                (fun i : DeleteRemainingIndex m j ↦ A i.1))
              (exposedYInDeleteRemaining m j)
              (deleteRemainingWithoutYEquiv m j s) := by
      apply Fintype.sum_equiv (deleteRemainingWithoutYEquiv m j).symm
      intro y
      obtain ⟨s, rfl⟩ := (deleteRemainingWithoutYEquiv m j).surjective y
      simp
    _ =
      transposeDot (A (exposedXIndex m)) (A (exposedYIndex m)) *
          remainingHafnianDeleteOne A j +
        ∑ b : {b : Fin m // b ≠ j},
          transposeDot (A (remainingIndex m b.1)) (A (exposedYIndex m)) *
            ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
              transposeDot (A (remainingIndex m a.1))
                  (A (exposedXIndex m)) *
                remainingHafnianDeleteThree A j a.1 b.1 := by
      rw [Fintype.sum_option]
      congr 1
      · change
          columnTransposeGram
              (fun i : DeleteRemainingIndex m j ↦ A i.1)
            (exposedXInDeleteRemaining m j)
            (exposedYInDeleteRemaining m j) *
            hafnianPairCofactor
              (columnTransposeGram
                (fun i : DeleteRemainingIndex m j ↦ A i.1))
              (exposedYInDeleteRemaining m j)
              (exposedXAfterDeleteRemainingY m j) = _
        rw [pairCofactor_deleteRemaining_Y_X_eq_deleteOne]
        unfold columnTransposeGram transposeDot
        rfl
      · apply Finset.sum_congr rfl
        intro b _hb
        change
          columnTransposeGram
              (fun i : DeleteRemainingIndex m j ↦ A i.1)
            (otherRemainingInDeleteRemaining m j b)
            (exposedYInDeleteRemaining m j) *
            hafnianPairCofactor
              (columnTransposeGram
                (fun i : DeleteRemainingIndex m j ↦ A i.1))
              (exposedYInDeleteRemaining m j)
              (otherRemainingAfterDeleteRemainingY m j b) = _
        rw [pairCofactor_deleteRemaining_Y_background_eq_sum_X]
        unfold columnTransposeGram transposeDot
        rfl

/-- The transpose-bilinear form of a scalar diagonal matrix. -/
theorem transposeBilinear_diagonal
    {k : ℕ} (x y : Fin k → ℂ) (c : ℂ) :
    transposeBilinear x (fun p q ↦ if p = q then c else 0) y =
      transposeDot x y * c := by
  unfold transposeBilinear transposeDot
  calc
    (∑ p : Fin k, ∑ q : Fin k,
        x p * (if p = q then c else 0) * y q) =
        ∑ p : Fin k, x p * c * y p := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp
    _ = (∑ p : Fin k, x p * y p) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- Exact factorization of a transpose-bilinear form against one ordered
rank-one matrix. -/
theorem transposeBilinear_rankOne
    {k : ℕ} (x u v y : Fin k → ℂ) (c : ℂ) :
    transposeBilinear x (fun p q ↦ c * u p * v q) y =
      transposeDot u x * c * transposeDot v y := by
  unfold transposeBilinear transposeDot
  calc
    (∑ p : Fin k, ∑ q : Fin k,
        x p * (c * u p * v q) * y q) =
        ∑ p : Fin k,
          (x p * c * u p) * (∑ q : Fin k, v q * y q) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ = (∑ p : Fin k, x p * c * u p) *
          (∑ q : Fin k, v q * y q) := by
      rw [Finset.sum_mul]
    _ = (∑ p : Fin k, u p * x p) * c *
          (∑ q : Fin k, v q * y q) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

theorem transposeBilinear_add
    {k : ℕ} (x y : Fin k → ℂ)
    (M N : Matrix (Fin k) (Fin k) ℂ) :
    transposeBilinear x (fun p q ↦ M p q + N p q) y =
      transposeBilinear x M y + transposeBilinear x N y := by
  unfold transposeBilinear
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

theorem transposeBilinear_fintype_sum
    {ι : Type*} [Fintype ι] {k : ℕ} (x y : Fin k → ℂ)
    (M : ι → Matrix (Fin k) (Fin k) ℂ) :
    transposeBilinear x (fun p q ↦ ∑ i : ι, M i p q) y =
      ∑ i : ι, transposeBilinear x (M i) y := by
  unfold transposeBilinear
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    enter [2, p]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- The ordered-pair definition of `cofactorM` represents exactly the
background cofactor scalar obtained by the two-stage hafnian expansion. -/
theorem transposeBilinear_cofactorM_eq_ordered_pair_sum
    {m k : ℕ} (A : TwoExposedColumnFamily m k) (j : Fin m) :
    transposeBilinear (A (exposedXIndex m)) (cofactorM A j)
        (A (exposedYIndex m)) =
      transposeDot (A (exposedXIndex m)) (A (exposedYIndex m)) *
          remainingHafnianDeleteOne A j +
        ∑ b : {b : Fin m // b ≠ j},
          transposeDot (A (remainingIndex m b.1)) (A (exposedYIndex m)) *
            ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
              transposeDot (A (remainingIndex m a.1))
                  (A (exposedXIndex m)) *
                remainingHafnianDeleteThree A j a.1 b.1 := by
  let D : Matrix (Fin k) (Fin k) ℂ :=
    fun p q ↦ if p = q then remainingHafnianDeleteOne A j else 0
  let R : (b : {b : Fin m // b ≠ j}) →
      (a : {a : Fin m // a ≠ j ∧ a ≠ b.1}) →
      Matrix (Fin k) (Fin k) ℂ :=
    fun b a p q ↦ remainingHafnianDeleteThree A j a.1 b.1 *
      A (remainingIndex m a.1) p * A (remainingIndex m b.1) q
  have hcofactor : cofactorM A j =
      (fun p q ↦ D p q + ∑ b, ∑ a, R b a p q) := by
    rfl
  have hD : transposeBilinear (A (exposedXIndex m)) D
        (A (exposedYIndex m)) =
      transposeDot (A (exposedXIndex m)) (A (exposedYIndex m)) *
        remainingHafnianDeleteOne A j := by
    dsimp [D]
    exact transposeBilinear_diagonal _ _ _
  have hR : ∀ (b : {b : Fin m // b ≠ j})
      (a : {a : Fin m // a ≠ j ∧ a ≠ b.1}),
      transposeBilinear (A (exposedXIndex m)) (R b a)
          (A (exposedYIndex m)) =
        transposeDot (A (remainingIndex m a.1)) (A (exposedXIndex m)) *
          remainingHafnianDeleteThree A j a.1 b.1 *
          transposeDot (A (remainingIndex m b.1)) (A (exposedYIndex m)) := by
    intro b a
    dsimp [R]
    exact transposeBilinear_rankOne _ _ _ _ _
  have hsum :
      transposeBilinear (A (exposedXIndex m))
          (fun p q ↦ ∑ b, ∑ a, R b a p q)
          (A (exposedYIndex m)) =
        ∑ b : {b : Fin m // b ≠ j},
          ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
            transposeBilinear (A (exposedXIndex m)) (R b a)
              (A (exposedYIndex m)) := by
    calc
      _ = ∑ b : {b : Fin m // b ≠ j},
          transposeBilinear (A (exposedXIndex m))
            (fun p q ↦ ∑ a, R b a p q)
            (A (exposedYIndex m)) :=
        transposeBilinear_fintype_sum _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _hb
        exact transposeBilinear_fintype_sum _ _ _
  rw [hcofactor]
  calc
    transposeBilinear (A (exposedXIndex m))
        (fun p q ↦ D p q + ∑ b, ∑ a, R b a p q)
        (A (exposedYIndex m)) =
      transposeBilinear (A (exposedXIndex m)) D
          (A (exposedYIndex m)) +
        transposeBilinear (A (exposedXIndex m))
          (fun p q ↦ ∑ b, ∑ a, R b a p q)
          (A (exposedYIndex m)) :=
      transposeBilinear_add _ _ _ _
    _ = transposeDot (A (exposedXIndex m)) (A (exposedYIndex m)) *
          remainingHafnianDeleteOne A j +
        ∑ b : {b : Fin m // b ≠ j},
          ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
            transposeDot (A (remainingIndex m a.1)) (A (exposedXIndex m)) *
              remainingHafnianDeleteThree A j a.1 b.1 *
              transposeDot (A (remainingIndex m b.1))
                (A (exposedYIndex m)) := by
      rw [hD, hsum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr rfl
      intro a _ha
      exact hR b a
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro b _hb
      rw [← Finset.sum_mul]
      ring

/-- Third exact cofactor identity: every background coordinate has the
bilinear form `C_j = Xᵀ M_{j,R} Y`. -/
theorem twoExposedCofactor_background_eq_transposeBilinear_X_M_Y
    {m k : ℕ} (A : TwoExposedColumnFamily m k) (j : Fin m) :
    twoExposedCofactorVector A (remainingIndex m j) =
      transposeBilinear (A (exposedXIndex m)) (cofactorM A j)
        (A (exposedYIndex m)) := by
  rw [twoExposedCofactor_background_eq_ordered_pair_sum,
    transposeBilinear_cofactorM_eq_ordered_pair_sum]

end

end LogdetLean.GramHafnian
