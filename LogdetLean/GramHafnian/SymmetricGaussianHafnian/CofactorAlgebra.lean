import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseInterior
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseSymmetry
/-!
# Literal symmetric-matrix hafnian cofactor algebra

The input in this file is a matrix, not a family of Gram factors.  Every
cofactor is the finite perfect-matching definition `typeHafnian` on the
principal submatrix with one vertex deleted.  The two exposed vertices are
the last two indices; the background occupies `Fin m`.

Only the index equivalences and generic hafnian expansion from the existing
deterministic library are reused.  In particular, no Gaussian law or
anticoncentration hypothesis is assumed here.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The literal principal hafnian cofactor, with one vertex deleted. -/
def matrixCofactor {ι R : Type*} [Fintype ι] [LinearOrder ι]
    [CommSemiring R] (S : Matrix ι ι R) (j : ι) : R :=
  typeHafnian (fun a b : {a : ι // a ≠ j} ↦ S a.1 b.1)

/-- Background hafnian after deletion of one background vertex. -/
def backgroundQ {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j : Fin m) : R :=
  typeHafnian (fun a b : {a : Fin m // a ≠ j} ↦
    S (remainingIndex m a.1) (remainingIndex m b.1))

/-- Background hafnian after deletion of the three displayed vertices. -/
def backgroundHafnianDeleteThree {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j a b : Fin m) : R :=
  typeHafnian (fun s t : {s : Fin m // s ≠ j ∧ s ≠ a ∧ s ≠ b} ↦
    S (remainingIndex m s.1) (remainingIndex m t.1))

/-- The independently exposed first edge vector in the symmetric model. -/
def matrixX {m : ℕ} {R : Type*}
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (a : Fin m) : R :=
  S (remainingIndex m a) (exposedXIndex m)

/-- The independently exposed second edge vector in the symmetric model. -/
def matrixY {m : ℕ} {R : Type*}
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (a : Fin m) : R :=
  S (remainingIndex m a) (exposedYIndex m)

/-- The scalar edge joining the two exposed vertices. -/
def matrixU {m : ℕ} {R : Type*}
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) : R :=
  S (exposedXIndex m) (exposedYIndex m)

/-- The direct cofactor matrix: its diagonal and its `j` row/column vanish.
Off those exceptional indices it is the triple-deletion background hafnian. -/
def backgroundM {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j : Fin m) :
    Matrix (Fin m) (Fin m) R :=
  fun a b ↦ if b ≠ j ∧ a ≠ j ∧ a ≠ b then
    backgroundHafnianDeleteThree S j a b else 0

@[simp] theorem backgroundM_diagonal
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j a : Fin m) :
    backgroundM S j a a = 0 := by
  simp [backgroundM]

@[simp] theorem backgroundM_row
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j b : Fin m) :
    backgroundM S j j b = 0 := by
  simp [backgroundM]

@[simp] theorem backgroundM_column
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j a : Fin m) :
    backgroundM S j a j = 0 := by
  simp [backgroundM]

theorem pairCofactor_deleteX_eq_backgroundQ
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (a : Fin m) :
    hafnianPairCofactor
        (fun i j : {i : Fin (m + 2) // i ≠ exposedXIndex m} ↦ S i.1 j.1)
        (exposedYInDeleteX m) (remainingOrderIsoDeleteXY m a) =
      backgroundQ S a := by
  unfold hafnianPairCofactor backgroundQ
  exact (typeHafnian_reindex_orderIso
    (remainingDeleteOneOrderIsoPairComplementX m a)
    (fun i j : TypePerfectMatching.PairComplement
      (exposedYInDeleteX m) (remainingInDeleteX m a) ↦ S i.1.1 j.1.1)).symm

theorem pairCofactor_deleteY_eq_backgroundQ
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (a : Fin m) :
    hafnianPairCofactor
        (fun i j : {i : Fin (m + 2) // i ≠ exposedYIndex m} ↦ S i.1 j.1)
        (exposedXInDeleteY m) (remainingOrderIsoDeleteYX m a) =
      backgroundQ S a := by
  unfold hafnianPairCofactor backgroundQ
  exact (typeHafnian_reindex_orderIso
    (remainingDeleteOneOrderIsoPairComplementY m a)
    (fun i j : TypePerfectMatching.PairComplement
      (exposedXInDeleteY m) (remainingInDeleteY m a) ↦ S i.1.1 j.1.1)).symm

/-- The first endpoint cofactor is the exposed `Y` vector paired with `q`. -/
theorem matrixCofactor_X_eq_sum_Y_Q
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    matrixCofactor S (exposedXIndex m) =
      ∑ a : Fin m, matrixY S a * backgroundQ S a := by
  unfold matrixCofactor
  rw [typeHafnian_expand_greatest _ (exposedYInDeleteX m)
    (deleteX_greatest_Y m)]
  apply Fintype.sum_equiv (remainingOrderIsoDeleteXY m).symm
  intro y
  obtain ⟨a, rfl⟩ := (remainingOrderIsoDeleteXY m).surjective y
  rw [pairCofactor_deleteX_eq_backgroundQ]
  rfl

/-- The second endpoint has exactly the same background coefficient `q`. -/
theorem matrixCofactor_Y_eq_sum_X_Q
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    matrixCofactor S (exposedYIndex m) =
      ∑ a : Fin m, matrixX S a * backgroundQ S a := by
  unfold matrixCofactor
  rw [typeHafnian_expand_greatest _ (exposedXInDeleteY m)
    (deleteY_greatest_X m)]
  apply Fintype.sum_equiv (remainingOrderIsoDeleteYX m).symm
  intro y
  obtain ⟨a, rfl⟩ := (remainingOrderIsoDeleteYX m).surjective y
  rw [pairCofactor_deleteY_eq_backgroundQ]
  rfl

theorem pairCofactor_deleteRemaining_Y_X_eq_backgroundQ
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j : Fin m) :
    hafnianPairCofactor
        (fun i l : DeleteRemainingIndex m j ↦ S i.1 l.1)
        (exposedYInDeleteRemaining m j)
        (exposedXAfterDeleteRemainingY m j) =
      backgroundQ S j := by
  unfold hafnianPairCofactor backgroundQ
  exact (typeHafnian_reindex_orderIso
    (remainingDeleteJOrderIsoPairComplementYX m j)
    (fun i l : TypePerfectMatching.PairComplement
      (exposedYInDeleteRemaining m j) (exposedXInDeleteRemaining m j) ↦
        S i.1.1 l.1.1)).symm

theorem pairCofactor_after_YB_XA_eq_backgroundDeleteThree
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j : Fin m)
    (b : {b : Fin m // b ≠ j})
    (a : {a : Fin m // a ≠ j ∧ a ≠ b.1}) :
    hafnianPairCofactor
        (fun i l : TypePerfectMatching.PairComplement
          (exposedYInDeleteRemaining m j)
          (otherRemainingInDeleteRemaining m j b) ↦ S i.1.1 l.1.1)
        (exposedXInPairComplementYB m j b)
        (remainingExceptJBOrderIsoAfterYX m j b a) =
      backgroundHafnianDeleteThree S j a.1 b.1 := by
  unfold hafnianPairCofactor backgroundHafnianDeleteThree
  exact (typeHafnian_reindex_orderIso
    (remainingDeleteThreeOrderIsoAfterYBXA m j b a)
    (fun i l : TypePerfectMatching.PairComplement
      (exposedXInPairComplementYB m j b)
      (otherRemainingInPairComplementYB m j b a) ↦ S i.1.1.1 l.1.1.1)).symm

theorem pairCofactor_deleteRemaining_Y_background_eq_sum
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j : Fin m)
    (b : {b : Fin m // b ≠ j}) :
    hafnianPairCofactor
        (fun i l : DeleteRemainingIndex m j ↦ S i.1 l.1)
        (exposedYInDeleteRemaining m j)
        (otherRemainingAfterDeleteRemainingY m j b) =
      ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
        matrixX S a.1 * backgroundHafnianDeleteThree S j a.1 b.1 := by
  unfold hafnianPairCofactor
  rw [typeHafnian_expand_greatest _ (exposedXInPairComplementYB m j b)
    (pairComplementYB_greatest_X m j b)]
  apply Fintype.sum_equiv (remainingExceptJBOrderIsoAfterYX m j b).symm
  intro y
  obtain ⟨a, rfl⟩ := (remainingExceptJBOrderIsoAfterYX m j b).surjective y
  exact congrArg (fun t : R ↦ matrixX S a.1 * t)
    (pairCofactor_after_YB_XA_eq_backgroundDeleteThree S j b a)

/-- Full literal cofactor identity, split into the exposed scalar edge and
the ordered pair of distinct background mates.  No Gram factor occurs. -/
theorem matrixCofactor_background_eq_ordered_pair_sum
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j : Fin m) :
    matrixCofactor S (remainingIndex m j) =
      matrixU S * backgroundQ S j +
        ∑ b : {b : Fin m // b ≠ j}, matrixY S b.1 *
          ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
            matrixX S a.1 * backgroundHafnianDeleteThree S j a.1 b.1 := by
  unfold matrixCofactor
  rw [typeHafnian_expand_greatest _ (exposedYInDeleteRemaining m j)
    (deleteRemaining_greatest_Y m j)]
  calc
    (∑ y : {y : DeleteRemainingIndex m j // y ≠ exposedYInDeleteRemaining m j},
        S y.1.1 (exposedYIndex m) *
          hafnianPairCofactor
            (fun i l : DeleteRemainingIndex m j ↦ S i.1 l.1)
            (exposedYInDeleteRemaining m j) y) =
        ∑ s : Option {b : Fin m // b ≠ j},
          S (deleteRemainingWithoutYEquiv m j s).1.1 (exposedYIndex m) *
            hafnianPairCofactor
              (fun i l : DeleteRemainingIndex m j ↦ S i.1 l.1)
              (exposedYInDeleteRemaining m j)
              (deleteRemainingWithoutYEquiv m j s) := by
      apply Fintype.sum_equiv (deleteRemainingWithoutYEquiv m j).symm
      intro y
      obtain ⟨s, rfl⟩ := (deleteRemainingWithoutYEquiv m j).surjective y
      simp
    _ = _ := by
      rw [Fintype.sum_option]
      congr 1
      · change matrixU S *
          hafnianPairCofactor
            (fun i l : DeleteRemainingIndex m j ↦ S i.1 l.1)
            (exposedYInDeleteRemaining m j)
            (exposedXAfterDeleteRemainingY m j) = _
        rw [pairCofactor_deleteRemaining_Y_X_eq_backgroundQ]
      · apply Finset.sum_congr rfl
        intro b _hb
        change matrixY S b.1 *
          hafnianPairCofactor
            (fun i l : DeleteRemainingIndex m j ↦ S i.1 l.1)
            (exposedYInDeleteRemaining m j)
            (otherRemainingAfterDeleteRemainingY m j b) = _
        rw [pairCofactor_deleteRemaining_Y_background_eq_sum]

private theorem sum_subtype_eq_sum_if
    {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (p : ι → Prop) [DecidablePred p] (f : ι → R) :
    (∑ a : {a : ι // p a}, f a.1) =
      ∑ a : ι, if p a then f a else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter p) (by simp) f).symm

theorem backgroundM_bilinear_eq_ordered_pair_sum
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j : Fin m) :
    (∑ a : Fin m, ∑ b : Fin m,
      matrixX S a * backgroundM S j a b * matrixY S b) =
      ∑ b : {b : Fin m // b ≠ j}, matrixY S b.1 *
        ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
          matrixX S a.1 * backgroundHafnianDeleteThree S j a.1 b.1 := by
  classical
  rw [Finset.sum_comm]
  erw [sum_subtype_eq_sum_if (fun b : Fin m ↦ b ≠ j)
    (fun b ↦ matrixY S b * ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b},
      matrixX S a.1 * backgroundHafnianDeleteThree S j a.1 b)]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hb : b ≠ j
  · erw [if_pos hb]
    erw [sum_subtype_eq_sum_if (fun a : Fin m ↦ a ≠ j ∧ a ≠ b)
      (fun a ↦ matrixX S a * backgroundHafnianDeleteThree S j a b)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : a ≠ j ∧ a ≠ b
    · simp [backgroundM, hb, ha.1, ha.2, mul_comm, mul_left_comm, mul_assoc]
    · simp [backgroundM, hb, ha]
  · simp [backgroundM, hb]

/-- The requested matrix form `C_j = u q_j + Xᵀ M_j Y`, proved from the
literal finite perfect-matching definition rather than adopted as a definition. -/
theorem matrixCofactor_background_eq_UQ_add_bilinear
    {m : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (j : Fin m) :
    matrixCofactor S (remainingIndex m j) =
      matrixU S * backgroundQ S j +
        ∑ a : Fin m, ∑ b : Fin m,
          matrixX S a * backgroundM S j a b * matrixY S b := by
  rw [matrixCofactor_background_eq_ordered_pair_sum,
    backgroundM_bilinear_eq_ordered_pair_sum]

/-- Complex specialization in the existing transpose-bilinear notation. -/
theorem matrixCofactor_background_eq_UQ_add_transposeBilinear
    {m : ℕ} (S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) (j : Fin m) :
    matrixCofactor S (remainingIndex m j) =
      matrixU S * backgroundQ S j +
        transposeBilinear (matrixX S) (backgroundM S j) (matrixY S) :=
  matrixCofactor_background_eq_UQ_add_bilinear S j

/-- Generic last-vertex expansion of a literal matrix hafnian. -/
theorem matrixHafnian_expand_last
    {n : ℕ} {R : Type*} [CommSemiring R]
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    typeHafnian S =
      ∑ j : {j : Fin (n + 1) // j ≠ Fin.last n},
        S j.1 (Fin.last n) * hafnianPairCofactor S (Fin.last n) j := by
  apply typeHafnian_expand_greatest S (Fin.last n)
  intro j hj
  exact lt_of_le_of_ne (Fin.le_last j) hj

/-- Symmetric matrices allow arbitrary simultaneous permutation of the
literal cofactor submatrix, not just order-preserving relabelling. -/
theorem matrixCofactor_reindex
    {α β R : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] [CommSemiring R]
    (e : α ≃ β) (S : Matrix β β R) (hS : ∀ i j, S i j = S j i) (j : α) :
    matrixCofactor (fun a b ↦ S (e a) (e b)) j = matrixCofactor S (e j) := by
  unfold matrixCofactor
  exact typeHafnian_reindex_equiv_of_symmetric
    (deleteIndexEquiv e j)
    (fun a b : {a : β // a ≠ e j} ↦ S a.1 b.1)
    (fun a b ↦ hS a.1 b.1)

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
