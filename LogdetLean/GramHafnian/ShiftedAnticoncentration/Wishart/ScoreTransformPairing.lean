import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SchurCauchy
/-!
# Trace pairing under the real-to-complex score transform

The fixed matrix `complexPairTransform` converts the real Wishart Gram into
the coupled complex Gram.  This file records its explicit inverse and proves
the invariant inverse-score trace pairing.  This is the deterministic source
of the factor two which changes the real-Wishart coefficient into the desired
complex-Wishart coefficient.
-/

open scoped BigOperators ComplexOrder

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Explicit inverse of `[[I,I],[iI,-iI]]`. -/
def complexPairTransformInverse : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  (1 / 2 : ℂ) •
    Matrix.fromBlocks 1 ((-Complex.I) • (1 : Matrix m m ℂ))
      1 (Complex.I • (1 : Matrix m m ℂ))

theorem complexPairTransform_mul_inverse :
    (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ) *
        complexPairTransformInverse = 1 := by
  classical
  unfold complexPairTransform complexPairTransformInverse
  rw [Matrix.mul_smul, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.one_apply, Complex.I_sq] <;>
    split_ifs <;> norm_num <;> ring

theorem complexPairTransform_inverse_mul :
    complexPairTransformInverse *
        (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ) = 1 := by
  classical
  unfold complexPairTransform complexPairTransformInverse
  rw [Matrix.smul_mul, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.one_apply, Complex.I_sq] <;>
    split_ifs <;> norm_num <;> ring

theorem complexPairTransform_isUnit :
    IsUnit (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ) := by
  exact isUnit_iff_exists_inv.mpr
    ⟨complexPairTransformInverse, complexPairTransform_mul_inverse⟩

/-- Inverse-score trace pairings are invariant under an invertible
congruence `M ↦ Lᴴ M L`. -/
theorem trace_nonsingInv_congruence_pairing
    {n : Type*} [Fintype n] [DecidableEq n]
    (L M D : Matrix n n ℂ)
    (hL : IsUnit L) (hM : IsUnit M.det) :
    Matrix.trace
        ((L.conjTranspose * M * L)⁻¹ *
          (L.conjTranspose * D * L)) =
      Matrix.trace (M⁻¹ * D) := by
  have hLH : IsUnit L.conjTranspose :=
    (Matrix.isUnit_conjTranspose L).2 hL
  have hLHdet : IsUnit L.conjTranspose.det :=
    (Matrix.isUnit_iff_isUnit_det L.conjTranspose).1 hLH
  have hMmat : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hM
  have hKmat : IsUnit (L.conjTranspose * M * L) :=
    (hLH.mul hMmat).mul hL
  have hKdet : IsUnit (L.conjTranspose * M * L).det :=
    (Matrix.isUnit_iff_isUnit_det (L.conjTranspose * M * L)).1 hKmat
  have hcand :
      M * (L * (L.conjTranspose * M * L)⁻¹ * L.conjTranspose) = 1 := by
    calc
      M * (L * (L.conjTranspose * M * L)⁻¹ * L.conjTranspose) =
          L.conjTranspose⁻¹ *
            (L.conjTranspose *
              (M * (L * (L.conjTranspose * M * L)⁻¹ * L.conjTranspose))) := by
        symm
        exact Matrix.nonsing_inv_mul_cancel_left L.conjTranspose _ hLHdet
      _ = L.conjTranspose⁻¹ *
          (((L.conjTranspose * M * L) *
            (L.conjTranspose * M * L)⁻¹) * L.conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = L.conjTranspose⁻¹ * (1 * L.conjTranspose) := by
        rw [Matrix.mul_nonsing_inv _ hKdet]
      _ = 1 := by
        simp [Matrix.nonsing_inv_mul _ hLHdet]
  have hinv :
      M⁻¹ = L * (L.conjTranspose * M * L)⁻¹ * L.conjTranspose :=
    Matrix.inv_eq_right_inv hcand
  calc
    Matrix.trace
        ((L.conjTranspose * M * L)⁻¹ *
          (L.conjTranspose * D * L)) =
        Matrix.trace
          (((L.conjTranspose * M * L)⁻¹ * L.conjTranspose * D) * L) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace
          (L * ((L.conjTranspose * M * L)⁻¹ * L.conjTranspose * D)) :=
      Matrix.trace_mul_comm _ L
    _ = Matrix.trace
          ((L * (L.conjTranspose * M * L)⁻¹ * L.conjTranspose) * D) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (M⁻¹ * D) := by rw [← hinv]

/-- Complexification commutes with the nonsingular inverse at every
nonsingular real matrix. -/
theorem map_nonsingInv_ofReal
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : IsUnit M.det) :
    (M⁻¹).map Complex.ofReal = (M.map Complex.ofReal)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  change Complex.ofRealHom.mapMatrix M *
      Complex.ofRealHom.mapMatrix M⁻¹ = 1
  rw [← map_mul, Matrix.mul_nonsing_inv M hM, map_one]

/-- Real inverse-score trace pairing, embedded in `ℂ`, equals the pairing
after an arbitrary invertible complex congruence. -/
theorem complexified_trace_nonsingInv_congruence_pairing
    {n : Type*} [Fintype n] [DecidableEq n]
    (L : Matrix n n ℂ) (M D : Matrix n n ℝ)
    (hL : IsUnit L) (hM : IsUnit M.det) :
    ((Matrix.trace (M⁻¹ * D) : ℝ) : ℂ) =
      Matrix.trace
        ((L.conjTranspose * M.map Complex.ofReal * L)⁻¹ *
          (L.conjTranspose * D.map Complex.ofReal * L)) := by
  have hMc : IsUnit (M.map Complex.ofReal).det := by
    change IsUnit (Complex.ofRealHom.mapMatrix M).det
    rw [← Complex.ofRealHom.map_det M]
    exact hM.map Complex.ofRealHom
  calc
    ((Matrix.trace (M⁻¹ * D) : ℝ) : ℂ) =
        Matrix.trace ((M⁻¹ * D).map Complex.ofReal) := by
      simp [Matrix.trace, Complex.ofReal_sum]
    _ = Matrix.trace
        ((M⁻¹).map Complex.ofReal * D.map Complex.ofReal) := by
      congr 1
      change Complex.ofRealHom.mapMatrix (M⁻¹ * D) =
        Complex.ofRealHom.mapMatrix M⁻¹ * Complex.ofRealHom.mapMatrix D
      exact Complex.ofRealHom.mapMatrix.map_mul _ _
    _ = Matrix.trace ((M.map Complex.ofReal)⁻¹ *
        D.map Complex.ofReal) := by
      rw [map_nonsingInv_ofReal M hM]
    _ = Matrix.trace
        ((L.conjTranspose * M.map Complex.ofReal * L)⁻¹ *
          (L.conjTranspose * D.map Complex.ofReal * L)) := by
      symm
      exact trace_nonsingInv_congruence_pairing L
        (M.map Complex.ofReal) (D.map Complex.ofReal) hL hMc

/-- Exact real-to-coupled-complex inverse-score trace identity. -/
theorem realPairGram_inverse_scoreDelta_trace_eq_coupled
    {k : Type*} [Fintype k]
    (X Y : Matrix k m ℝ) {H : Matrix m m ℂ}
    (hH : H.IsHermitian)
    (hM : IsUnit (realPairGram X Y).det) :
    ((Matrix.trace ((realPairGram X Y)⁻¹ * scoreDeltaM H) : ℝ) : ℂ) =
      Matrix.trace
        ((coupledGramKernel (complexOfRealPair X Y))⁻¹ *
          Matrix.fromBlocks H 0 0 (H.map star)) := by
  have h := complexified_trace_nonsingInv_congruence_pairing
    (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ)
    (realPairGram X Y) (scoreDeltaM H)
    complexPairTransform_isUnit hM
  rw [← coupledGramKernel_eq_transform_congruence X Y,
    scoreDeltaM_transform_congruence hH] at h
  exact h

/-- Hermitian rank-one matrix `c cᴴ`. -/
def hermitianRankOne (c : m → ℂ) : Matrix m m ℂ :=
  fun i j ↦ c i * star (c j)

theorem hermitianRankOne_isHermitian (c : m → ℂ) :
    (hermitianRankOne c).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j ↦ ?_
  simp [hermitianRankOne, mul_comm]

/-- Trace of a product with `c cᴴ` is the corresponding quadratic
pairing, before taking real parts. -/
theorem trace_mul_hermitianRankOne (B : Matrix m m ℂ) (c : m → ℂ) :
    Matrix.trace (B * hermitianRankOne c) =
      dotProduct (star c) (B.mulVec c) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, hermitianRankOne]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

theorem re_trace_mul_hermitianRankOne
    (B : Matrix m m ℂ) (c : m → ℂ) :
    (Matrix.trace (B * hermitianRankOne c)).re =
      quadraticFormReal B c := by
  rw [trace_mul_hermitianRankOne]
  rfl

/-- Trace of a product with a block-diagonal matrix is the sum of the two
diagonal-block trace pairings. -/
theorem trace_mul_fromBlocks_diagonal
    (K : Matrix (m ⊕ m) (m ⊕ m) ℂ)
    (H J : Matrix m m ℂ) :
    Matrix.trace (K * Matrix.fromBlocks H 0 0 J) =
      Matrix.trace (Matrix.toBlocks₁₁ K * H) +
        Matrix.trace (Matrix.toBlocks₂₂ K * J) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

/-- Entrywise conjugation commutes with a matrix trace pairing. -/
theorem trace_map_star_mul_map_star
    (B H : Matrix m m ℂ) :
    Matrix.trace ((B.map star) * (H.map star)) =
      star (Matrix.trace (B * H)) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, map_sum, map_mul]

/-- If the lower diagonal block is the conjugate of the upper one, pairing
against the two conjugate rank-one directions gives twice the real upper
quadratic form. -/
theorem trace_mul_fromBlocks_rankOne_of_block22_eq_star
    (K : Matrix (m ⊕ m) (m ⊕ m) ℂ) (c : m → ℂ)
    (hblock : Matrix.toBlocks₂₂ K =
      (Matrix.toBlocks₁₁ K).map star) :
    Matrix.trace
        (K * Matrix.fromBlocks (hermitianRankOne c) 0 0
          ((hermitianRankOne c).map star)) =
      ((2 * quadraticFormReal (Matrix.toBlocks₁₁ K) c : ℝ) : ℂ) := by
  rw [trace_mul_fromBlocks_diagonal, hblock,
    trace_map_star_mul_map_star]
  rw [← re_trace_mul_hermitianRankOne]
  apply Complex.ext <;> simp
  ring

/-- Conjugate a block matrix entrywise and swap its two block indices. -/
def coupledConjugation
    (K : Matrix (m ⊕ m) (m ⊕ m) ℂ) :
    Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  Matrix.fromBlocks
    ((Matrix.toBlocks₂₂ K).map star)
    ((Matrix.toBlocks₂₁ K).map star)
    ((Matrix.toBlocks₁₂ K).map star)
    ((Matrix.toBlocks₁₁ K).map star)

@[simp] theorem coupledConjugation_fromBlocks
    (A B C D : Matrix m m ℂ) :
    coupledConjugation (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (D.map star) (C.map star)
        (B.map star) (A.map star) := by
  simp [coupledConjugation]

@[simp] theorem coupledConjugation_one :
    coupledConjugation (1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [coupledConjugation, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem coupledConjugation_mul
    (K J : Matrix (m ⊕ m) (m ⊕ m) ℂ) :
    coupledConjugation (K * J) =
      coupledConjugation K * coupledConjugation J := by
  rw [← Matrix.fromBlocks_toBlocks K, ← Matrix.fromBlocks_toBlocks J,
    Matrix.fromBlocks_multiply]
  simp only [coupledConjugation_fromBlocks, Matrix.fromBlocks_multiply,
    Matrix.map_add]
  congr 1 <;> ext i j <;>
    simp [Matrix.mul_apply, map_sum, map_add, map_mul, add_comm]

/-- The coupled Gram kernel is fixed by block-swap conjugation. -/
theorem coupledConjugation_coupledGramKernel
    {k : Type*} [Fintype k] (A : Matrix k m ℂ) :
    coupledConjugation (coupledGramKernel A) = coupledGramKernel A := by
  unfold coupledGramKernel
  rw [coupledConjugation_fromBlocks]
  ext i j
  cases i <;> cases j <;> simp

/-- Inversion preserves block-swap conjugation symmetry. -/
theorem coupledConjugation_nonsingInv_eq
    (K : Matrix (m ⊕ m) (m ⊕ m) ℂ)
    (hfix : coupledConjugation K = K)
    (hK : IsUnit K.det) :
    coupledConjugation K⁻¹ = K⁻¹ := by
  have hright : K * coupledConjugation K⁻¹ = 1 := by
    calc
      K * coupledConjugation K⁻¹ =
          coupledConjugation K * coupledConjugation K⁻¹ := by rw [hfix]
      _ = coupledConjugation (K * K⁻¹) :=
        (coupledConjugation_mul K K⁻¹).symm
      _ = coupledConjugation 1 := by rw [Matrix.mul_nonsing_inv K hK]
      _ = 1 := coupledConjugation_one
  exact (Matrix.inv_eq_right_inv hright).symm

/-- The lower-right inverse block of a nonsingular coupled Gram kernel is
the entrywise conjugate of its upper-left inverse block. -/
theorem coupledKernel_inverse_toBlocks22_eq_star_toBlocks11
    {k : Type*} [Fintype k] (A : Matrix k m ℂ)
    (hK : IsUnit (coupledGramKernel A).det) :
    Matrix.toBlocks₂₂ (coupledGramKernel A)⁻¹ =
      (Matrix.toBlocks₁₁ (coupledGramKernel A)⁻¹).map star := by
  have hsym := coupledConjugation_nonsingInv_eq
    (coupledGramKernel A) (coupledConjugation_coupledGramKernel A) hK
  have hblock := congrArg Matrix.toBlocks₂₂ hsym
  simpa [coupledConjugation] using hblock.symm

/-- Final deterministic factor-two identity for a coupled inverse paired
with a Hermitian rank-one score direction. -/
theorem coupledKernel_inverse_rankOne_score_trace
    {k : Type*} [Fintype k] (A : Matrix k m ℂ) (c : m → ℂ)
    (hK : IsUnit (coupledGramKernel A).det) :
    Matrix.trace
        ((coupledGramKernel A)⁻¹ *
          Matrix.fromBlocks (hermitianRankOne c) 0 0
            ((hermitianRankOne c).map star)) =
      ((2 * quadraticFormReal
          (Matrix.toBlocks₁₁ (coupledGramKernel A)⁻¹) c : ℝ) : ℂ) := by
  exact trace_mul_fromBlocks_rankOne_of_block22_eq_star _ _
    (coupledKernel_inverse_toBlocks22_eq_star_toBlocks11 A hK)

/-- The real inverse-score trace in the rank-one direction is twice the
upper-left coupled-inverse quadratic form. -/
theorem realPairGram_inverse_rankOne_score_trace_eq_coupled
    {k : Type*} [Fintype k]
    (X Y : Matrix k m ℝ) (c : m → ℂ)
    (hM : IsUnit (realPairGram X Y).det)
    (hK : IsUnit
      (coupledGramKernel (complexOfRealPair X Y)).det) :
    Matrix.trace
        ((realPairGram X Y)⁻¹ * scoreDeltaM (hermitianRankOne c)) =
      2 * quadraticFormReal
        (Matrix.toBlocks₁₁
          (coupledGramKernel (complexOfRealPair X Y))⁻¹) c := by
  have hcomplex := realPairGram_inverse_scoreDelta_trace_eq_coupled
    X Y (hermitianRankOne_isHermitian c) hM
  rw [coupledKernel_inverse_rankOne_score_trace
    (complexOfRealPair X Y) c hK] at hcomplex
  have hre := congrArg Complex.re hcomplex
  simpa using hre

/-- Schur-complement form of the preceding factor-two identity. -/
theorem realPairGram_inverse_rankOne_score_trace_eq_coupledSchur
    {k : Type*} [Fintype k] [DecidableEq k]
    (X Y : Matrix k m ℝ) (c : m → ℂ)
    (hM : IsUnit (realPairGram X Y).det)
    (hfull : Function.Injective
      (complexConjugateColumnPair (complexOfRealPair X Y)).mulVec) :
    Matrix.trace
        ((realPairGram X Y)⁻¹ * scoreDeltaM (hermitianRankOne c)) =
      2 * quadraticFormReal
        (coupledSchurComplement (complexOfRealPair X Y))⁻¹ c := by
  have hKmat : IsUnit (coupledGramKernel (complexOfRealPair X Y)) :=
    (coupledGramKernel_posDef (complexOfRealPair X Y) hfull).isUnit
  have hK : IsUnit
      (coupledGramKernel (complexOfRealPair X Y)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hKmat
  rw [realPairGram_inverse_rankOne_score_trace_eq_coupled X Y c hM hK,
    coupledKernel_inverse_toBlocks11 (complexOfRealPair X Y) hfull]

end Wishart

end

end LogdetLean.GramHafnian
