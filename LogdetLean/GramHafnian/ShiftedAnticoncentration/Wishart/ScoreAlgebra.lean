import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.Realification
/-!
# Deterministic algebra behind the conditional Wishart score

The probabilistic score identity uses a real symmetric perturbation which,
in the `(Q,S)` coordinates, changes `Q` by a prescribed Hermitian matrix and
leaves `S` fixed.  It is then lifted to the Gaussian matrix by the vector
field `R ↦ (1/2) R (RᵀR)⁻¹ D`.

This file verifies those two deterministic statements.  There is no
probability, differentiation, integration by parts, or conditional
expectation in this module.
-/

open scoped BigOperators ComplexOrder

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*}

/-- Real block matrix corresponding to the coordinates `(U,C,V)`. -/
def realBlockMatrix (U C V : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  Matrix.fromBlocks U C C.transpose V

/-- Upper-left real block of the score direction associated with `H`. -/
def scoreDeltaU (H : Matrix m m ℂ) : Matrix m m ℝ :=
  recoverU H 0

/-- Lower-right real block of the score direction associated with `H`. -/
def scoreDeltaV (H : Matrix m m ℂ) : Matrix m m ℝ :=
  recoverV H 0

/-- Off-diagonal real block of the score direction associated with `H`. -/
def scoreDeltaC (H : Matrix m m ℂ) : Matrix m m ℝ :=
  recoverC H 0

/-- The real symmetric score direction which realizes `(δQ,δS)=(H,0)`. -/
def scoreDeltaM (H : Matrix m m ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  realBlockMatrix (scoreDeltaU H) (scoreDeltaC H) (scoreDeltaV H)

/-- Both diagonal real blocks of the score direction are symmetric. -/
theorem scoreDeltaU_isSymm {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    (scoreDeltaU H).IsSymm := by
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  have h := congrArg Complex.re (hH.apply i j)
  simp [scoreDeltaU, recoverU] at h ⊢
  linarith

theorem scoreDeltaV_isSymm {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    (scoreDeltaV H).IsSymm := by
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  have h := congrArg Complex.re (hH.apply i j)
  simp [scoreDeltaV, recoverV] at h ⊢
  linarith

/-- The score direction is a real symmetric matrix. -/
theorem scoreDeltaM_isSymm {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    (scoreDeltaM H).IsSymm := by
  exact Matrix.IsSymm.fromBlocks (scoreDeltaU_isSymm hH) rfl
    (scoreDeltaV_isSymm hH)

/-- In `(Q,S)` coordinates the score direction changes `Q` by exactly `H`. -/
theorem qOf_scoreDelta {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    qOfRealBlocks (scoreDeltaU H) (scoreDeltaC H) (scoreDeltaV H) = H := by
  simpa [scoreDeltaU, scoreDeltaC, scoreDeltaV] using
    qOfRealBlocks_recover hH (Matrix.isSymm_zero : (0 : Matrix m m ℂ).IsSymm)

/-- In `(Q,S)` coordinates the score direction leaves `S` fixed. -/
theorem sOf_scoreDelta {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    sOfRealBlocks (scoreDeltaU H) (scoreDeltaC H) (scoreDeltaV H) = 0 := by
  simpa [scoreDeltaU, scoreDeltaC, scoreDeltaV] using
    sOfRealBlocks_recover hH (Matrix.isSymm_zero : (0 : Matrix m m ℂ).IsSymm)

section Transform

variable [Fintype m] [DecidableEq m]

/-- A Hermitian diagonal entry is real. -/
theorem ofReal_re_diagonal_eq {H : Matrix m m ℂ} (hH : H.IsHermitian)
    (i : m) : ((H i i).re : ℂ) = H i i := by
  have h := congrArg Complex.im (hH.apply i i)
  apply Complex.ext
  · simp
  · simp at h ⊢
    linarith

/-- The trace of the real score direction equals the complex trace pairing
with the Hermitian direction.  This is the `tr(D)` term in the Gaussian
score calculation. -/
theorem scoreDeltaM_trace {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    ((Matrix.trace (scoreDeltaM H) : ℝ) : ℂ) = Matrix.trace H := by
  calc
    ((Matrix.trace (scoreDeltaM H) : ℝ) : ℂ) =
        ∑ i, ((H i i).re : ℂ) := by
      simp [Matrix.trace, scoreDeltaM, realBlockMatrix, scoreDeltaU,
        scoreDeltaV, recoverU, recoverV, Fintype.sum_sum_type,
        Complex.ofReal_sum, Finset.sum_add_distrib]
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      ring
    _ = ∑ i, H i i := by
      apply Finset.sum_congr rfl
      intro i _
      exact ofReal_re_diagonal_eq hH i
    _ = Matrix.trace H := rfl

/-- The fixed complex transform converts an arbitrary real symmetric block
matrix into its exact `(Q,S)` block representation. -/
theorem realBlockMatrix_transform_congruence (U C V : Matrix m m ℝ) :
    (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ).conjTranspose *
        (realBlockMatrix U C V).map Complex.ofReal * complexPairTransform =
      Matrix.fromBlocks (qOfRealBlocks U C V) ((sOfRealBlocks U C V).map star)
        (sOfRealBlocks U C V) ((qOfRealBlocks U C V).map star) := by
  classical
  unfold complexPairTransform realBlockMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_map,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp [qOfRealBlocks, sOfRealBlocks] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

/-- Congruence form of the exact score direction: its coupled variation is
`diag(H,conj H)` and the off-diagonal `S` variation vanishes. -/
theorem scoreDeltaM_transform_congruence {H : Matrix m m ℂ}
    (hH : H.IsHermitian) :
    (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ).conjTranspose *
        (scoreDeltaM H).map Complex.ofReal * complexPairTransform =
      Matrix.fromBlocks H 0 0 (H.map star) := by
  rw [scoreDeltaM, realBlockMatrix_transform_congruence,
    qOf_scoreDelta hH, sOf_scoreDelta hH]
  simp

end Transform

section SteinLift

variable [Fintype k] [Fintype m] [DecidableEq m]

/-- The real Gram matrix of a rectangular matrix. -/
def realWishartGram (R : Matrix k m ℝ) : Matrix m m ℝ :=
  R.transpose * R

/-- Value of the Gaussian-Stein vector field which lifts the Gram direction
`D` to the rectangular matrix `R`. -/
def steinVectorFieldValue (R : Matrix k m ℝ) (D : Matrix m m ℝ) :
    Matrix k m ℝ :=
  (1 / 2 : ℝ) • (R * (realWishartGram R)⁻¹ * D)

/-- The right-hand contribution to the first variation of `RᵀR` is `D/2`. -/
theorem transpose_mul_steinVectorFieldValue
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    R.transpose * steinVectorFieldValue R D = (1 / 2 : ℝ) • D := by
  calc
    R.transpose * steinVectorFieldValue R D =
        (1 / 2 : ℝ) •
          (realWishartGram R * (realWishartGram R)⁻¹ * D) := by
      simp [steinVectorFieldValue, realWishartGram, Matrix.mul_assoc]
    _ = (1 / 2 : ℝ) • D := by
      rw [Matrix.mul_nonsing_inv _ hM]
      simp

/-- For symmetric `D`, the left-hand contribution to the first Gram
variation is also `D/2`. -/
theorem steinVectorFieldValue_transpose_mul
    (R : Matrix k m ℝ) {D : Matrix m m ℝ} (hD : D.IsSymm)
    (hM : IsUnit (realWishartGram R).det) :
    (steinVectorFieldValue R D).transpose * R = (1 / 2 : ℝ) • D := by
  have h := congrArg Matrix.transpose
    (transpose_mul_steinVectorFieldValue R D hM)
  simpa [Matrix.transpose_mul, hD.eq] using h

/-- The Stein vector field has exactly the prescribed first variation of
the real Gram map `R ↦ RᵀR`. -/
theorem gram_firstVariation_steinVectorFieldValue
    (R : Matrix k m ℝ) {D : Matrix m m ℝ} (hD : D.IsSymm)
    (hM : IsUnit (realWishartGram R).det) :
    (steinVectorFieldValue R D).transpose * R +
        R.transpose * steinVectorFieldValue R D = D := by
  rw [steinVectorFieldValue_transpose_mul R hD hM,
    transpose_mul_steinVectorFieldValue R D hM]
  ext i j
  simp
  ring

/-- Frobenius inner product of two real rectangular matrices. -/
def realFrobeniusInner (R V : Matrix k m ℝ) : ℝ :=
  ∑ i, ∑ j, R i j * V i j

/-- The Frobenius inner product is the trace pairing `tr(RᵀV)`. -/
theorem realFrobeniusInner_eq_trace_transpose_mul
    (R V : Matrix k m ℝ) :
    realFrobeniusInner R V = Matrix.trace (R.transpose * V) := by
  simp only [realFrobeniusInner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- The Gaussian radial term of the Stein vector field is exactly
`tr(D)/2`; equivalently, twice the Frobenius pairing is `tr(D)`. -/
theorem two_mul_frobenius_steinVectorFieldValue
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    2 * realFrobeniusInner R (steinVectorFieldValue R D) = Matrix.trace D := by
  rw [realFrobeniusInner_eq_trace_transpose_mul,
    transpose_mul_steinVectorFieldValue R D hM, Matrix.trace_smul]
  simp

end SteinLift

end Wishart

end

end LogdetLean.GramHafnian
