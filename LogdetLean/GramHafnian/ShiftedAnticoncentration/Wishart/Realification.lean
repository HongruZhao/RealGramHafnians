import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Complex.Basic
/-!
# Realification coordinates for the coupled complex Gram matrices

This file contains the deterministic coordinate identities used in the
conditional-Wishart argument.  If `A = X + iY`, the real matrix `[X Y]` has
Gram matrix `M`, while the two complex Gram matrices are

* `Q = Aᴴ A`, and
* `S = Aᵀ A`.

The formulas below are completely algebraic.  In particular, they do not use
a Gaussian law or a Wishart density.
-/

open scoped BigOperators ComplexOrder

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*}

/-- Assemble a complex matrix `A = X + iY` from two real matrices. -/
def complexOfRealPair (X Y : Matrix k m ℝ) : Matrix k m ℂ :=
  fun i j ↦ (X i j : ℂ) + Complex.I * (Y i j : ℂ)

/-- Horizontally concatenate two real matrices, with the column index written
as a sum type. -/
def realColumnPair (X Y : Matrix k m ℝ) : Matrix k (m ⊕ m) ℝ :=
  fun i ↦ Sum.elim (X i) (Y i)

/-- Horizontally concatenate a complex matrix and its entrywise conjugate. -/
def complexConjugateColumnPair (A : Matrix k m ℂ) : Matrix k (m ⊕ m) ℂ :=
  fun i ↦ Sum.elim (A i) (fun j ↦ star (A i j))

/-- The fixed complex change-of-columns matrix
`[[I,I],[iI,-iI]]`. -/
def complexPairTransform [DecidableEq m] : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  Matrix.fromBlocks 1 1 (Complex.I • (1 : Matrix m m ℂ))
    ((-Complex.I) • (1 : Matrix m m ℂ))

/-- The real transpose Gram matrix of `[X Y]`. -/
def realPairGram [Fintype k] (X Y : Matrix k m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  (realColumnPair X Y).transpose * realColumnPair X Y

/-- The Hermitian Gram matrix `Q=AᴴA`. -/
def hermitianGram [Fintype k] (A : Matrix k m ℂ) : Matrix m m ℂ :=
  A.conjTranspose * A

/-- The symmetric transpose Gram matrix `S=AᵀA`. -/
def transposeGramMatrix [Fintype k] (A : Matrix k m ℂ) : Matrix m m ℂ :=
  A.transpose * A

/-- The coupled block matrix built from `Q=AᴴA` and `S=AᵀA`. -/
def coupledGramKernel [Fintype k] (A : Matrix k m ℂ) :
    Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  Matrix.fromBlocks (hermitianGram A)
    ((transposeGramMatrix A).map star)
    (transposeGramMatrix A)
    ((hermitianGram A).map star)

/-- Coordinate expression for `Q` in terms of the real blocks
`U=XᵀX`, `C=XᵀY`, and `V=YᵀY`. -/
def qOfRealBlocks (U C V : Matrix m m ℝ) : Matrix m m ℂ :=
  fun i j ↦ ((U i j + V i j : ℝ) : ℂ) +
    Complex.I * ((C i j - C j i : ℝ) : ℂ)

/-- Coordinate expression for `S` in terms of the real blocks
`U=XᵀX`, `C=XᵀY`, and `V=YᵀY`. -/
def sOfRealBlocks (U C V : Matrix m m ℝ) : Matrix m m ℂ :=
  fun i j ↦ ((U i j - V i j : ℝ) : ℂ) +
    Complex.I * ((C i j + C j i : ℝ) : ℂ)

/-- Recover the upper-left real block from `(Q,S)`. -/
def recoverU (Q S : Matrix m m ℂ) : Matrix m m ℝ :=
  fun i j ↦ (Q i j).re / 2 + (S i j).re / 2

/-- Recover the lower-right real block from `(Q,S)`. -/
def recoverV (Q S : Matrix m m ℂ) : Matrix m m ℝ :=
  fun i j ↦ (Q i j).re / 2 - (S i j).re / 2

/-- Recover the real off-diagonal block from `(Q,S)`. -/
def recoverC (Q S : Matrix m m ℂ) : Matrix m m ℝ :=
  fun i j ↦ (Q i j).im / 2 + (S i j).im / 2

@[simp] theorem recoverU_qsOfRealBlocks (U C V : Matrix m m ℝ) :
    recoverU (qOfRealBlocks U C V) (sOfRealBlocks U C V) = U := by
  ext i j
  simp [recoverU, qOfRealBlocks, sOfRealBlocks]
  ring

@[simp] theorem recoverV_qsOfRealBlocks (U C V : Matrix m m ℝ) :
    recoverV (qOfRealBlocks U C V) (sOfRealBlocks U C V) = V := by
  ext i j
  simp [recoverV, qOfRealBlocks, sOfRealBlocks]
  ring

@[simp] theorem recoverC_qsOfRealBlocks (U C V : Matrix m m ℝ) :
    recoverC (qOfRealBlocks U C V) (sOfRealBlocks U C V) = C := by
  ext i j
  simp [recoverC, qOfRealBlocks, sOfRealBlocks]
  ring

/-- The `Q` coordinate is Hermitian whenever the two diagonal real blocks
are symmetric. -/
theorem qOfRealBlocks_isHermitian {U C V : Matrix m m ℝ}
    (hU : U.IsSymm) (hV : V.IsSymm) :
    (qOfRealBlocks U C V).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j ↦ ?_
  apply Complex.ext <;>
    simp [qOfRealBlocks, hU.apply i j, hV.apply i j]
  <;> ring

/-- The `S` coordinate is symmetric whenever the two diagonal real blocks
are symmetric. -/
theorem sOfRealBlocks_isSymm {U C V : Matrix m m ℝ}
    (hU : U.IsSymm) (hV : V.IsSymm) :
    (sOfRealBlocks U C V).IsSymm := by
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  apply Complex.ext <;>
    simp [sOfRealBlocks, hU.apply i j, hV.apply i j]
  <;> ring

/-- The explicit recovery formulas are also a right inverse on Hermitian
`Q` and symmetric `S`. -/
theorem qOfRealBlocks_recover {Q S : Matrix m m ℂ}
    (hQ : Q.IsHermitian) (hS : S.IsSymm) :
    qOfRealBlocks (recoverU Q S) (recoverC Q S) (recoverV Q S) = Q := by
  ext i j
  have hQr := congrArg Complex.re (hQ.apply i j)
  have hQi := congrArg Complex.im (hQ.apply i j)
  have hSr := congrArg Complex.re (hS.apply i j)
  have hSi := congrArg Complex.im (hS.apply i j)
  apply Complex.ext <;>
    simp [qOfRealBlocks, recoverU, recoverC, recoverV] at hQr hQi hSr hSi ⊢
  <;> linarith

/-- The explicit recovery formulas recover the symmetric coordinate as well. -/
theorem sOfRealBlocks_recover {Q S : Matrix m m ℂ}
    (hQ : Q.IsHermitian) (hS : S.IsSymm) :
    sOfRealBlocks (recoverU Q S) (recoverC Q S) (recoverV Q S) = S := by
  ext i j
  have hQr := congrArg Complex.re (hQ.apply i j)
  have hQi := congrArg Complex.im (hQ.apply i j)
  have hSr := congrArg Complex.re (hS.apply i j)
  have hSi := congrArg Complex.im (hS.apply i j)
  apply Complex.ext <;>
    simp [sOfRealBlocks, recoverU, recoverC, recoverV] at hQr hQi hSr hSi ⊢
  <;> linarith

/-- The real block formulas and `(Q,S)` coordinates are mutually inverse on
the natural symmetry classes.  This is the coordinate-level bijectivity
statement used by the Wishart change of variables. -/
theorem qsOfRealBlocks_recover {Q S : Matrix m m ℂ}
    (hQ : Q.IsHermitian) (hS : S.IsSymm) :
    (qOfRealBlocks (recoverU Q S) (recoverC Q S) (recoverV Q S),
      sOfRealBlocks (recoverU Q S) (recoverC Q S) (recoverV Q S)) = (Q, S) := by
  rw [qOfRealBlocks_recover hQ hS, sOfRealBlocks_recover hQ hS]

section Finite

variable [Fintype k] [Fintype m] [DecidableEq m]

/-- Multiplication by the fixed transform sends `[X Y]` to `[A, conj A]`. -/
theorem realColumnPair_mul_complexPairTransform
    (X Y : Matrix k m ℝ) :
    (realColumnPair X Y).map Complex.ofReal * complexPairTransform =
      complexConjugateColumnPair (complexOfRealPair X Y) := by
  classical
  ext i j
  cases j with
  | inl j =>
      simp [realColumnPair, complexPairTransform, complexConjugateColumnPair,
        complexOfRealPair, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
      <;> ring
  | inr j =>
      simp [realColumnPair, complexPairTransform, complexConjugateColumnPair,
        complexOfRealPair, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
      <;> ring

/-- Mapping the real Gram matrix into `ℂ` agrees with taking the complex
Hermitian Gram of the mapped real column pair. -/
theorem map_realPairGram
    (X Y : Matrix k m ℝ) :
    (realPairGram X Y).map Complex.ofReal =
      ((realColumnPair X Y).map Complex.ofReal).conjTranspose *
        (realColumnPair X Y).map Complex.ofReal := by
  ext i j
  simp [realPairGram, realColumnPair, Matrix.mul_apply]

/-- Exact formula for `Q=AᴴA` under `A=X+iY`. -/
theorem hermitianGram_complexOfRealPair
    (X Y : Matrix k m ℝ) :
    hermitianGram (complexOfRealPair X Y) =
      qOfRealBlocks (X.transpose * X) (X.transpose * Y) (Y.transpose * Y) := by
  ext i j
  apply Complex.ext <;>
    simp [hermitianGram, complexOfRealPair, qOfRealBlocks, Matrix.mul_apply,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_comm]
  <;> ring_nf

/-- Exact formula for `S=AᵀA` under `A=X+iY`. -/
theorem transposeGramMatrix_complexOfRealPair
    (X Y : Matrix k m ℝ) :
    transposeGramMatrix (complexOfRealPair X Y) =
      sOfRealBlocks (X.transpose * X) (X.transpose * Y) (Y.transpose * Y) := by
  ext i j
  apply Complex.ext <;>
    simp [transposeGramMatrix, complexOfRealPair, sOfRealBlocks, Matrix.mul_apply,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_comm]
  <;> ring_nf

/-- The Gram matrix of `[A,conj A]` is the explicit `(Q,S)` block kernel. -/
theorem conjugateColumnPair_gram (A : Matrix k m ℂ) :
    (complexConjugateColumnPair A).conjTranspose * complexConjugateColumnPair A =
      coupledGramKernel A := by
  ext i j
  cases i <;> cases j <;>
    simp [complexConjugateColumnPair, coupledGramKernel, hermitianGram,
      transposeGramMatrix, Matrix.mul_apply]

/-- The transpose Gram coordinate is complex symmetric. -/
theorem transposeGramMatrix_isSymm (A : Matrix k m ℂ) :
    (transposeGramMatrix A).IsSymm := by
  unfold transposeGramMatrix Matrix.IsSymm
  simp

/-- The usual complex Gram coordinate is Hermitian. -/
theorem hermitianGram_isHermitian (A : Matrix k m ℂ) :
    (hermitianGram A).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_self A

/-- The coupled kernel is always positive semidefinite because it is a Gram
matrix. -/
theorem coupledGramKernel_posSemidef (A : Matrix k m ℂ) :
    (coupledGramKernel A).PosSemidef := by
  rw [← conjugateColumnPair_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Full column rank of `[A,conj A]` makes the coupled kernel positive
definite. -/
theorem coupledGramKernel_posDef (A : Matrix k m ℂ)
    (hA : Function.Injective (complexConjugateColumnPair A).mulVec) :
    (coupledGramKernel A).PosDef := by
  rw [← conjugateColumnPair_gram]
  exact Matrix.PosDef.conjTranspose_mul_self _ hA

/-- Entrywise conjugation of a Hermitian matrix agrees with transpose. -/
theorem map_star_eq_transpose_of_isHermitian {Q : Matrix m m ℂ}
    (hQ : Q.IsHermitian) :
    Q.map star = Q.transpose := by
  ext i j
  exact hQ.apply j i

/-- Entrywise conjugation preserves positive definiteness of a Hermitian
matrix. -/
theorem map_star_posDef {Q : Matrix m m ℂ} (hQ : Q.PosDef) :
    (Q.map star).PosDef := by
  rw [map_star_eq_transpose_of_isHermitian hQ.isHermitian]
  exact hQ.transpose

/-- If `S` is symmetric, the conjugate block has adjoint exactly `S`. -/
theorem map_star_conjTranspose_of_isSymm {S : Matrix m m ℂ}
    (hS : S.IsSymm) :
    (S.map star).conjTranspose = S := by
  ext i j
  simp [Matrix.conjTranspose_apply, hS.apply i j]

/-- The central congruence identity
`K(Q,S)=Lᴴ (M : ℂ) L`. -/
theorem coupledGramKernel_eq_transform_congruence
    (X Y : Matrix k m ℝ) :
    coupledGramKernel (complexOfRealPair X Y) =
      (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ).conjTranspose *
        (realPairGram X Y).map Complex.ofReal * complexPairTransform := by
  rw [← conjugateColumnPair_gram, ← realColumnPair_mul_complexPairTransform,
    map_realPairGram]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Finite

end Wishart

end

end LogdetLean.GramHafnian
