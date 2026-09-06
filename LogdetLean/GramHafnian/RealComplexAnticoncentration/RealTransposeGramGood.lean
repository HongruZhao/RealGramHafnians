import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLastColumnProduct
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
/-!
# An elementary entrywise certificate for a real Gaussian Gram matrix

The certificate in this file is deterministic.  Every entry of `Aᵀ A` is
within `delta * k / m` of its mean, where `m` is the number of columns.  A
finite Cauchy--Schwarz estimate then gives

`‖A C‖² ≥ k (1 - delta) ‖C‖²`.

No spectral theorem or random-matrix estimate is used.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An entry of the transpose Gram matrix of a family of real columns. -/
def realTransposeGramEntry {k : ℕ} (A : ι → Fin k → ℝ) (i j : ι) : ℝ :=
  ∑ a : Fin k, A i a * A j a

/-- The centered transpose-Gram entry: diagonal entries are centered at `k`
and off-diagonal entries at zero. -/
def centeredRealTransposeGramEntry (k : ℕ) (A : ι → Fin k → ℝ)
    (i j : ι) : ℝ :=
  realTransposeGramEntry A i j - if i = j then (k : ℝ) else 0

/-- Entrywise good event used by the elementary beta-one proof.  The common
threshold is `delta * k / m`, with `m = card ι`. -/
def realTransposeGramGood (k : ℕ) (delta : ℝ)
    (A : ι → Fin k → ℝ) : Prop :=
  ∀ i j, |centeredRealTransposeGramEntry k A i j| ≤
    delta * (k : ℝ) / (Fintype.card ι : ℝ)

theorem measurableSet_realTransposeGramGood (k : ℕ) (delta : ℝ) :
    MeasurableSet {A : ι → Fin k → ℝ | realTransposeGramGood k delta A} := by
  unfold realTransposeGramGood centeredRealTransposeGramEntry
    realTransposeGramEntry
  have h : MeasurableSet (⋂ i, ⋂ j,
      {A : ι → Fin k → ℝ |
        |(∑ a : Fin k, A i a * A j a) -
          if i = j then (k : ℝ) else 0| ≤
            delta * (k : ℝ) / (Fintype.card ι : ℝ)}) :=
    MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
    measurableSet_le
      ((by fun_prop : Measurable (fun A : ι → Fin k → ℝ ↦
        |(∑ a : Fin k, A i a * A j a) -
          if i = j then (k : ℝ) else 0|))) measurable_const
  convert h using 1
  ext A
  simp

/-- Squared Euclidean norm of a coefficient vector indexed by the columns. -/
def realColumnCoefficientSqEnergy (C : ι → ℝ) : ℝ :=
  ∑ i, (C i) ^ 2

/-- Squared norm of the column combination `A C`. -/
def realColumnCombinationEnergy {k : ℕ} (A : ι → Fin k → ℝ)
    (C : ι → ℝ) : ℝ :=
  ∑ a : Fin k, (∑ i : ι, A i a * C i) ^ 2

theorem realColumnCoefficientSqEnergy_nonneg (C : ι → ℝ) :
    0 ≤ realColumnCoefficientSqEnergy C := by
  unfold realColumnCoefficientSqEnergy
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem realColumnCombinationEnergy_nonneg {k : ℕ}
    (A : ι → Fin k → ℝ) (C : ι → ℝ) :
    0 ≤ realColumnCombinationEnergy A C := by
  unfold realColumnCombinationEnergy
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem realColumnCombinationEnergy_eq_gramQuadratic {k : ℕ}
    (A : ι → Fin k → ℝ) (C : ι → ℝ) :
    realColumnCombinationEnergy A C =
      ∑ i : ι, ∑ j : ι, C i * realTransposeGramEntry A i j * C j := by
  unfold realColumnCombinationEnergy realTransposeGramEntry
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem centeredGramQuadratic_identity {k : ℕ}
    (A : ι → Fin k → ℝ) (C : ι → ℝ) :
    (∑ i : ι, ∑ j : ι,
        C i * centeredRealTransposeGramEntry k A i j * C j) =
      realColumnCombinationEnergy A C -
        (k : ℝ) * realColumnCoefficientSqEnergy C := by
  rw [realColumnCombinationEnergy_eq_gramQuadratic]
  unfold centeredRealTransposeGramEntry realColumnCoefficientSqEnergy
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp [mul_ite, ite_mul]
  calc
    (∑ x : ι, C x * (k : ℝ) * C x) =
        ∑ x : ι, (k : ℝ) * C x ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (k : ℝ) * ∑ x : ι, C x ^ 2 := by rw [Finset.mul_sum]

theorem abs_centeredGramQuadratic_le
    [Nonempty ι] {k : ℕ} {delta : ℝ}
    (hdelta : 0 ≤ delta) (A : ι → Fin k → ℝ) (C : ι → ℝ)
    (hgood : realTransposeGramGood k delta A) :
    |∑ i : ι, ∑ j : ι,
        C i * centeredRealTransposeGramEntry k A i j * C j| ≤
      delta * (k : ℝ) * realColumnCoefficientSqEnergy C := by
  let t : ℝ := delta * (k : ℝ) / (Fintype.card ι : ℝ)
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have ht : 0 ≤ t := div_nonneg (mul_nonneg hdelta (Nat.cast_nonneg k)) hcard.le
  have hentry : ∀ i j,
      |C i * centeredRealTransposeGramEntry k A i j * C j| ≤
        |C i| * t * |C j| := by
    intro i j
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hgood i j) (abs_nonneg (C i)))
      (abs_nonneg (C j))
  have hsum :
      |∑ i : ι, ∑ j : ι,
          C i * centeredRealTransposeGramEntry k A i j * C j| ≤
        t * (∑ i : ι, |C i|) ^ 2 := by
    calc
      |∑ i : ι, ∑ j : ι,
          C i * centeredRealTransposeGramEntry k A i j * C j| ≤
          ∑ i : ι, |∑ j : ι,
            C i * centeredRealTransposeGramEntry k A i j * C j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : ι, ∑ j : ι,
          |C i * centeredRealTransposeGramEntry k A i j * C j| := by
        gcongr with i
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : ι, ∑ j : ι, |C i| * t * |C j| := by
        gcongr with i j
        exact hentry i j
      _ = t * (∑ i : ι, |C i|) ^ 2 := by
        simp_rw [sq, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  have hcauchy :
      (∑ i : ι, |C i|) ^ 2 ≤
        (Fintype.card ι : ℝ) * realColumnCoefficientSqEnergy C := by
    simpa [realColumnCoefficientSqEnergy, sq_abs] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset ι)) (f := fun i ↦ |C i|))
  calc
    |∑ i : ι, ∑ j : ι,
        C i * centeredRealTransposeGramEntry k A i j * C j| ≤
        t * (∑ i : ι, |C i|) ^ 2 := hsum
    _ ≤ t * ((Fintype.card ι : ℝ) * realColumnCoefficientSqEnergy C) :=
      mul_le_mul_of_nonneg_left hcauchy ht
    _ = delta * (k : ℝ) * realColumnCoefficientSqEnergy C := by
      dsimp [t]
      field_simp [hcard.ne']

/-- Deterministic Gershgorin/Cauchy--Schwarz lower bound supplied by the
entrywise good event. -/
theorem realColumnCombinationEnergy_ge_of_realTransposeGramGood
    [Nonempty ι] {k : ℕ} {delta : ℝ}
    (hdelta : 0 ≤ delta) (A : ι → Fin k → ℝ) (C : ι → ℝ)
    (hgood : realTransposeGramGood k delta A) :
    (k : ℝ) * (1 - delta) * realColumnCoefficientSqEnergy C ≤
      realColumnCombinationEnergy A C := by
  have habs := abs_centeredGramQuadratic_le hdelta A C hgood
  have hlower :
      -(delta * (k : ℝ) * realColumnCoefficientSqEnergy C) ≤
        ∑ i : ι, ∑ j : ι,
          C i * centeredRealTransposeGramEntry k A i j * C j :=
    (neg_le_of_abs_le habs)
  rw [centeredGramQuadratic_identity] at hlower
  linarith

/-- Direct adapter to the literal odd hafnian cofactors used at level `r`. -/
theorem pastRealCofactorV_ge_mul_pastRealCofactorW_of_good
    {r k : ℕ} (hr : 1 ≤ r) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (A : OddCofactorIndex r hr → Fin k → ℝ)
    (hgood : realTransposeGramGood k delta A) :
    (k : ℝ) * (1 - delta) * pastRealCofactorW hr A ≤
      pastRealCofactorV hr A := by
  letI : Nonempty (OddCofactorIndex r hr) :=
    Fintype.card_pos_iff.mp (by
      rw [card_oddCofactorIndex]
      omega)
  have h := realColumnCombinationEnergy_ge_of_realTransposeGramGood
    hdelta A (pastRealHafnianCofactorVector hr A) hgood
  unfold realColumnCombinationEnergy realColumnCoefficientSqEnergy at h
  unfold pastRealCofactorV realOddCofactorV
    realOddCofactorColumnCombination
  unfold pastRealCofactorW realOddCofactorW
  unfold pastRealHafnianCofactorVector at h
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  unfold pastRealCofactorMatrix
  rw [realLastColumnProductEquiv_apply_nonlast hr (A, 0) j]

end

end LogdetLean.GramHafnian
