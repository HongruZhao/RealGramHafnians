import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseReindex
/-!
# Deterministic data for the two-exposed-column cofactor phase

We work with `m` remaining columns followed by two displayed columns `X,Y`.
For the application, `m = 2r-3`.  Keeping `m` abstract makes every identity
purely finite and separates parity from the algebra.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- A column family consisting of `m` background columns followed by `X,Y`. -/
abbrev TwoExposedColumnFamily (m k : ℕ) := Fin (m + 2) → (Fin k → ℂ)

/-- Inclusion of a background-column index. -/
def remainingIndex (m : ℕ) (i : Fin m) : Fin (m + 2) :=
  ⟨i.1, by omega⟩

/-- Index of the displayed column `X`. -/
def exposedXIndex (m : ℕ) : Fin (m + 2) := ⟨m, by omega⟩

/-- Index of the displayed column `Y`. -/
def exposedYIndex (m : ℕ) : Fin (m + 2) := ⟨m + 1, by omega⟩

@[simp] theorem remainingIndex_val (m : ℕ) (i : Fin m) :
    (remainingIndex m i).1 = i.1 := rfl

@[simp] theorem exposedXIndex_val (m : ℕ) :
    (exposedXIndex m).1 = m := rfl

@[simp] theorem exposedYIndex_val (m : ℕ) :
    (exposedYIndex m).1 = m + 1 := rfl

theorem remainingIndex_lt_exposedXIndex (m : ℕ) (i : Fin m) :
    remainingIndex m i < exposedXIndex m := by
  exact i.2

theorem exposedXIndex_lt_exposedYIndex (m : ℕ) :
    exposedXIndex m < exposedYIndex m := by
  change m < m + 1
  omega

theorem ne_exposedXIndex_of_remaining (m : ℕ) (i : Fin m) :
    remainingIndex m i ≠ exposedXIndex m :=
  (remainingIndex_lt_exposedXIndex m i).ne

theorem ne_exposedYIndex_of_remaining (m : ℕ) (i : Fin m) :
    remainingIndex m i ≠ exposedYIndex m :=
  (remainingIndex_lt_exposedXIndex m i).trans
    (exposedXIndex_lt_exposedYIndex m) |>.ne

theorem exposedXIndex_ne_exposedYIndex (m : ℕ) :
    exposedXIndex m ≠ exposedYIndex m :=
  (exposedXIndex_lt_exposedYIndex m).ne

/-- Transpose Gram matrix for a column family on an arbitrary finite index. -/
def columnTransposeGram {ι : Type*} [Fintype ι] {k : ℕ}
    (A : ι → (Fin k → ℂ)) : Matrix ι ι ℂ :=
  fun i j ↦ ∑ a : Fin k, A i a * A j a

theorem columnTransposeGram_comm {ι : Type*} [Fintype ι] {k : ℕ}
    (A : ι → (Fin k → ℂ)) (i j : ι) :
    columnTransposeGram A i j = columnTransposeGram A j i := by
  unfold columnTransposeGram
  apply Finset.sum_congr rfl
  intro a _ha
  exact mul_comm _ _

/-- Cofactor vector of a Gram hafnian on an arbitrary ordered column set. -/
def finiteGramCofactorVector {ι : Type*} [Fintype ι] [LinearOrder ι]
    {k : ℕ} (A : ι → (Fin k → ℂ)) (j : ι) : ℂ :=
  typeHafnian (columnTransposeGram (fun i : {i : ι // i ≠ j} ↦ A i.1))

/-- The cofactor vector for `m` background columns followed by `X,Y`. -/
def twoExposedCofactorVector {m k : ℕ} (A : TwoExposedColumnFamily m k) :
    Fin (m + 2) → ℂ :=
  finiteGramCofactorVector A

/-- Background hafnian after deleting every index in `s`. -/
def remainingHafnianExcept {m k : ℕ} (A : TwoExposedColumnFamily m k)
    (s : Finset (Fin m)) : ℂ :=
  typeHafnian (columnTransposeGram
    (fun i : {i : Fin m // i ∉ s} ↦ A (remainingIndex m i.1)))

/-- Background hafnian after deleting one displayed background index. -/
def remainingHafnianDeleteOne {m k : ℕ} (A : TwoExposedColumnFamily m k)
    (a : Fin m) : ℂ :=
  typeHafnian (columnTransposeGram
    (fun i : {i : Fin m // i ≠ a} ↦ A (remainingIndex m i.1)))

/-- Background hafnian after deleting three pairwise-used indices.  Repeated
arguments are harmless; in the decomposition they are always distinct. -/
def remainingHafnianDeleteThree {m k : ℕ}
    (A : TwoExposedColumnFamily m k) (j a b : Fin m) : ℂ :=
  typeHafnian (columnTransposeGram
    (fun i : {i : Fin m // i ≠ j ∧ i ≠ a ∧ i ≠ b} ↦
      A (remainingIndex m i.1)))

/-- The common endpoint vector
`q_R = sum_a haf(R_{-a}ᵀR_{-a}) r_a`. -/
def cofactorQ {m k : ℕ} (A : TwoExposedColumnFamily m k) : Fin k → ℂ :=
  fun p ↦ ∑ a : Fin m,
    remainingHafnianDeleteOne A a * A (remainingIndex m a) p

/-- The matrix `M_{j,R}`.  The double sum is over ordered pairs
`a,b ∈ Fin m \ {j}` with `a ≠ b`, exactly as in the paper. -/
def cofactorM {m k : ℕ} (A : TwoExposedColumnFamily m k) (j : Fin m) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun p q ↦
    (if p = q then remainingHafnianDeleteOne A j else 0) +
      ∑ b : {b : Fin m // b ≠ j},
        ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
          remainingHafnianDeleteThree A j a.1 b.1 *
            A (remainingIndex m a.1) p * A (remainingIndex m b.1) q

/-- Transpose bilinear form `xᵀ M y`, with no complex conjugation. -/
def transposeBilinear {k : ℕ} (x : Fin k → ℂ)
    (M : Matrix (Fin k) (Fin k) ℂ) (y : Fin k → ℂ) : ℂ :=
  ∑ p : Fin k, ∑ q : Fin k, x p * M p q * y q

/-- Transpose dot product `xᵀy`. -/
def transposeDot {k : ℕ} (x y : Fin k → ℂ) : ℂ :=
  ∑ p : Fin k, x p * y p

end

end LogdetLean.GramHafnian
