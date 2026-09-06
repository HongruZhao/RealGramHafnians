import LogdetLean.GramHafnian.PerfectMatching
/-!
# Hafnians and transpose Gram matrices

The definitions in this file are literal finite sums.  The final theorem
`gramHafnian_eq_sum_coloredMatchings` is the deterministic expansion used
before applying Gaussian moment identities: every matched pair chooses one
row (a "colour") of the rectangular matrix.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

variable {n k : ℕ}

/-- The monomial contributed by one perfect matching. -/
def matchingMonomial {R : Type*} [CommMonoid R]
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (M : PerfectMatching n) : R :=
  ∏ i ∈ M.pairReps, A i (M i)

/-- The hafnian, defined as a sum over fixed-point-free involutions, with
each pair represented by its smaller endpoint. -/
noncomputable def hafnian {R : Type*} [CommSemiring R]
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) : R :=
  ∑ M : PerfectMatching n, matchingMonomial A M

/-- The symmetric transpose Gram matrix `Xᵀ X` (no complex conjugation). -/
def transposeGram {R : Type*} [CommSemiring R]
    (X : Matrix (Fin k) (Fin (2 * n)) R) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) R :=
  X.transpose * X

@[simp] theorem transposeGram_apply {R : Type*} [CommSemiring R]
    (X : Matrix (Fin k) (Fin (2 * n)) R) (i j : Fin (2 * n)) :
    transposeGram X i j = ∑ a : Fin k, X a i * X a j := by
  simp [transposeGram, Matrix.mul_apply]

theorem transposeGram_transpose {R : Type*} [CommSemiring R]
    (X : Matrix (Fin k) (Fin (2 * n)) R) :
    (transposeGram X).transpose = transposeGram X := by
  ext i j
  simp [transposeGram_apply, mul_comm]

/-- The Gram hafnian observable. -/
noncomputable def gramHafnian {R : Type*} [CommSemiring R]
    (X : Matrix (Fin k) (Fin (2 * n)) R) : R :=
  hafnian (transposeGram X)

/-- A row-colouring of the pairs of a matching. -/
abbrev PairColoring (M : PerfectMatching n) (k : ℕ) :=
  M.pairReps → Fin k

/-- The matrix monomial selected by a matching and one row-colouring. -/
def coloredMatchingMonomial {R : Type*} [CommMonoid R]
    (X : Matrix (Fin k) (Fin (2 * n)) R) (M : PerfectMatching n)
    (c : PairColoring M k) : R :=
  ∏ i : M.pairReps, X (c i) i.1 * X (c i) (M i.1)

/-- Exact deterministic row-colouring expansion of `haf(Xᵀ X)`.  No
probability or Gaussian assumption is used here. -/
theorem gramHafnian_eq_sum_coloredMatchings {R : Type*} [CommSemiring R]
    (X : Matrix (Fin k) (Fin (2 * n)) R) :
    gramHafnian X =
      ∑ M : PerfectMatching n, ∑ c : PairColoring M k,
        coloredMatchingMonomial X M c := by
  classical
  unfold gramHafnian hafnian matchingMonomial coloredMatchingMonomial
  apply Finset.sum_congr rfl
  intro M _
  simp only [transposeGram_apply]
  rw [Finset.prod_subtype M.pairReps (fun _ ↦ Iff.rfl)]
  exact Fintype.prod_sum (fun i : M.pairReps ↦
    fun a : Fin k ↦ X a i.1 * X a (M i.1))

end LogdetLean.GramHafnian
