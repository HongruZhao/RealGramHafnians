import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.Realification
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Basic
/-!
# Schur complements and the directional matrix Cauchy inequality

This module isolates the deterministic inequalities used after the
conditional Wishart score.  All inverses below are ordinary nonsingular
matrix inverses.  Positive definiteness supplies their invertibility.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Schur complement of the lower-right block in a Hermitian block matrix. -/
def schurComplement22 (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) : Matrix m m ℂ :=
  A - B * D⁻¹ * B.conjTranspose

/-- The term removed from the upper-left block is positive semidefinite. -/
theorem schurCorrection_posSemidef (B : Matrix m n ℂ) {D : Matrix n n ℂ}
    (hD : D.PosDef) :
    (B * D⁻¹ * B.conjTranspose).PosSemidef := by
  exact hD.inv.posSemidef.mul_mul_conjTranspose_same B

/-- A lower-right Schur complement is below its original diagonal block in
Loewner order. -/
theorem schurComplement22_le (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    {D : Matrix n n ℂ} (hD : D.PosDef) :
    schurComplement22 A B D ≤ A := by
  rw [Matrix.le_iff]
  simpa [schurComplement22] using schurCorrection_posSemidef B hD

/-- A positive-definite Hermitian block matrix has a positive-definite Schur
complement. -/
theorem schurComplement22_posDef_of_fromBlocks_posDef
    {A : Matrix m m ℂ} {B : Matrix m n ℂ} {D : Matrix n n ℂ}
    (hK : (Matrix.fromBlocks A B B.conjTranspose D).PosDef) :
    (schurComplement22 A B D).PosDef := by
  have hD : D.PosDef := by
    convert hK.submatrix (e := Sum.inr) Sum.inr_injective using 1 <;>
      ext i j <;> rfl
  letI : Invertible D := hD.isUnit.invertible
  have hpsd : (schurComplement22 A B D).PosSemidef := by
    exact (Matrix.PosDef.fromBlocks₂₂ A B hD).mp hK.posSemidef
  apply hpsd.posDef_iff_isUnit.mpr
  have hu : IsUnit (A - B * ⅟D * B.conjTranspose) :=
    (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂).mp hK.isUnit
  simpa [schurComplement22] using hu

/-- The upper-left block of the inverse is the inverse Schur complement. -/
theorem inverse_fromBlocks_toBlocks11
    {A : Matrix m m ℂ} {B : Matrix m n ℂ} {D : Matrix n n ℂ}
    (hK : (Matrix.fromBlocks A B B.conjTranspose D).PosDef) :
    Matrix.toBlocks₁₁ (Matrix.fromBlocks A B B.conjTranspose D)⁻¹ =
      (schurComplement22 A B D)⁻¹ := by
  have hD : D.PosDef := by
    convert hK.submatrix (e := Sum.inr) Sum.inr_injective using 1 <;>
      ext i j <;> rfl
  have hSchur := schurComplement22_posDef_of_fromBlocks_posDef hK
  letI : Invertible D := hD.isUnit.invertible
  letI : Invertible (schurComplement22 A B D) := hSchur.isUnit.invertible
  letI : Invertible (Matrix.fromBlocks A B B.conjTranspose D) := hK.isUnit.invertible
  letI : Invertible (A - B * ⅟D * B.conjTranspose) :=
    Invertible.copy (hSchur.isUnit.invertible) _ (by simp [schurComplement22])
  have h := congrArg Matrix.toBlocks₁₁
    (Matrix.invOf_fromBlocks₂₂_eq A B B.conjTranspose D)
  simpa [schurComplement22] using h

/-- Inversion reverses the Schur-complement inequality. -/
theorem inverse_le_schurComplement22_inverse
    {A : Matrix m m ℂ} {B : Matrix m n ℂ} {D : Matrix n n ℂ}
    (hK : (Matrix.fromBlocks A B B.conjTranspose D).PosDef) :
    A⁻¹ ≤ (schurComplement22 A B D)⁻¹ := by
  have hA : A.PosDef := by
    convert hK.submatrix (e := Sum.inl) Sum.inl_injective using 1 <;>
      ext i j <;> rfl
  have hD : D.PosDef := by
    convert hK.submatrix (e := Sum.inr) Sum.inr_injective using 1 <;>
      ext i j <;> rfl
  have hSchur := schurComplement22_posDef_of_fromBlocks_posDef hK
  have hle := schurComplement22_le A B hD
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    (CStarAlgebra.ringInverse_le_ringInverse hle hSchur.isStrictlyPositive)

/-- The Schur complement occurring in the coupled `(Q,S)` Gram kernel. -/
def coupledSchurComplement (A : Matrix n m ℂ) : Matrix m m ℂ :=
  schurComplement22 (hermitianGram A)
    ((transposeGramMatrix A).map star)
    ((hermitianGram A).map star)

/-- Re-express the coupled kernel in the canonical Hermitian block shape
`[[Q,B],[Bᴴ,D]]`. -/
theorem coupledGramKernel_eq_fromBlocks_adjoint (A : Matrix n m ℂ) :
    coupledGramKernel A =
      Matrix.fromBlocks (hermitianGram A)
        ((transposeGramMatrix A).map star)
        ((transposeGramMatrix A).map star).conjTranspose
        ((hermitianGram A).map star) := by
  rw [map_star_conjTranspose_of_isSymm (transposeGramMatrix_isSymm A)]
  rfl

/-- Under full column rank of `[A,conj A]`, the coupled Schur complement is
positive definite. -/
theorem coupledSchurComplement_posDef (A : Matrix n m ℂ)
    (hA : Function.Injective (complexConjugateColumnPair A).mulVec) :
    (coupledSchurComplement A).PosDef := by
  apply schurComplement22_posDef_of_fromBlocks_posDef
  rw [← coupledGramKernel_eq_fromBlocks_adjoint]
  exact coupledGramKernel_posDef A hA

/-- The usual inverse Gram is dominated by the upper-left inverse block of
the coupled kernel. -/
theorem hermitianGram_inverse_le_coupledSchur_inverse
    (A : Matrix n m ℂ)
    (hA : Function.Injective (complexConjugateColumnPair A).mulVec) :
    (hermitianGram A)⁻¹ ≤ (coupledSchurComplement A)⁻¹ := by
  apply inverse_le_schurComplement22_inverse
  rw [← coupledGramKernel_eq_fromBlocks_adjoint]
  exact coupledGramKernel_posDef A hA

/-- Exact upper-left inverse-block identity for the coupled kernel. -/
theorem coupledKernel_inverse_toBlocks11
    (A : Matrix n m ℂ)
    (hA : Function.Injective (complexConjugateColumnPair A).mulVec) :
    Matrix.toBlocks₁₁ (coupledGramKernel A)⁻¹ =
      (coupledSchurComplement A)⁻¹ := by
  rw [coupledGramKernel_eq_fromBlocks_adjoint]
  exact inverse_fromBlocks_toBlocks11
    (by
      rw [← coupledGramKernel_eq_fromBlocks_adjoint]
      exact coupledGramKernel_posDef A hA)

/-- Real part of the Hermitian quadratic form `cᴴQc`. -/
def quadraticFormReal (Q : Matrix m m ℂ) (c : m → ℂ) : ℝ :=
  Complex.re (dotProduct (star c) (Q.mulVec c))

/-- Squared Euclidean norm written in the same coordinate convention. -/
def vectorNormSq (c : m → ℂ) : ℝ :=
  Complex.re (dotProduct (star c) c)

/-- Matrix Cauchy--Schwarz:
`(cᴴQc)(cᴴQ⁻¹c) ≥ (cᴴc)²`, expressed as an inequality of real
quadratic forms. -/
theorem matrix_cauchy_schwarz {Q : Matrix m m ℂ} (hQ : Q.PosDef)
    (c : m → ℂ) :
    vectorNormSq c ^ 2 ≤
      quadraticFormReal Q c * quadraticFormReal Q⁻¹ c := by
  letI : Invertible Q := hQ.isUnit.invertible
  letI : SeminormedAddCommGroup (m → ℂ) :=
    Q.toSeminormedAddCommGroup hQ.posSemidef
  letI : InnerProductSpace ℂ (m → ℂ) :=
    Q.toInnerProductSpace hQ.posSemidef
  letI : InnerProductSpace ℝ (m → ℂ) :=
    InnerProductSpace.rclikeToReal ℂ (m → ℂ)
  let y : m → ℂ := (Q⁻¹).mulVec c
  have hy : Q.mulVec y = c := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
    simp
  have hxy : inner ℝ c y = vectorNormSq c := by
    change Complex.re (dotProduct (Q.mulVec y) (star c)) =
      Complex.re (dotProduct (star c) c)
    rw [hy, dotProduct_comm]
  have hxx : inner ℝ c c = quadraticFormReal Q c := by
    change Complex.re (dotProduct (Q.mulVec c) (star c)) =
      Complex.re (dotProduct (star c) (Q.mulVec c))
    rw [dotProduct_comm]
  have hyy : inner ℝ y y = quadraticFormReal Q⁻¹ c := by
    change Complex.re (dotProduct (Q.mulVec y) (star y)) =
      Complex.re (dotProduct (star c) ((Q⁻¹).mulVec c))
    rw [hy]
    dsimp [y]
    rw [Matrix.dotProduct_star]
    simp [dotProduct_comm]
  have hcs := real_inner_mul_inner_self_le c y
  rw [hxy, hxx, hyy] at hcs
  simpa [pow_two] using hcs

/-- A nonzero vector has strictly positive squared Euclidean norm. -/
theorem vectorNormSq_pos {c : m → ℂ} (hc : c ≠ 0) :
    0 < vectorNormSq c := by
  have h := (Matrix.dotProduct_star_self_pos_iff (R := ℂ)).2 hc
  exact (Complex.pos_iff.mp h).1

/-- A positive-definite Hermitian quadratic form is strictly positive in a
nonzero direction. -/
theorem quadraticFormReal_pos {Q : Matrix m m ℂ} (hQ : Q.PosDef)
    {c : m → ℂ} (hc : c ≠ 0) :
    0 < quadraticFormReal Q c := by
  exact hQ.re_dotProduct_pos hc

/-- Reciprocal form of matrix Cauchy--Schwarz, exactly as needed in the
inverse-moment argument. -/
theorem inverse_quadraticFormReal_le {Q : Matrix m m ℂ} (hQ : Q.PosDef)
    {c : m → ℂ} (hc : c ≠ 0) :
    (quadraticFormReal Q c)⁻¹ ≤
      quadraticFormReal Q⁻¹ c / vectorNormSq c ^ 2 := by
  have hq := quadraticFormReal_pos hQ hc
  have hw := vectorNormSq_pos hc
  rw [← one_div]
  apply (div_le_div_iff₀ hq (sq_pos_of_pos hw)).2
  simpa [mul_comm] using matrix_cauchy_schwarz hQ c

/-- For a Hermitian Gram matrix, the quadratic form is the squared norm of
the matrix-vector product. -/
theorem quadraticFormReal_conjTranspose_mul_self
    (A : Matrix n m ℂ) (c : m → ℂ) :
    quadraticFormReal (A.conjTranspose * A) c =
      vectorNormSq (A.mulVec c) := by
  unfold quadraticFormReal vectorNormSq
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]

end Wishart

end


end LogdetLean.GramHafnian
