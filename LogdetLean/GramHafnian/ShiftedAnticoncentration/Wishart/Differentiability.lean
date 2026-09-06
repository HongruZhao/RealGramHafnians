import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.Divergence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Differentiability of the lifted inverse-Gram vector field

This module connects the algebraic linearization from `Divergence.lean` to
the actual derivative of `R ↦ (1/2)R(RᵀR)⁻¹D` on the full-rank locus.
-/

open scoped BigOperators Matrix.Norms.Operator

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*} [Fintype k] [Fintype m]
  [DecidableEq k] [DecidableEq m]

/-- Affine line through a rectangular matrix in direction `E`. -/
def matrixLine (R E : Matrix k m ℝ) (t : ℝ) : Matrix k m ℝ :=
  R + t • E

/-- The affine matrix line itself has derivative `E`. -/
theorem hasDerivAt_matrixLine
    (R E : Matrix k m ℝ) :
    HasDerivAt (matrixLine R E) E 0 := by
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro i
  unfold matrixLine
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  convert
    (hasDerivAt_const (x := (0 : ℝ)) (c := R a i)).add
      ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (E a i)) using 1 <;>
    first | rfl | simp | exact Subsingleton.elim _ _

/-- Derivative of the real Gram map along an affine matrix line. -/
theorem hasDerivAt_realWishartGram_matrixLine
    (R E : Matrix k m ℝ) :
    HasDerivAt (fun t : ℝ ↦ realWishartGram (matrixLine R E t))
      (E.transpose * R + R.transpose * E) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simp only [realWishartGram, matrixLine, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hsum : HasDerivAt
      (fun x : ℝ ↦ ∑ b,
        (R b i + x * E b i) * (R b j + x * E b j))
      ((∑ b, E b i * R b j) + (∑ b, R b i * E b j)) 0 := by
    have hsum' : HasDerivAt
        (fun x : ℝ ↦ ∑ b,
          (R b i + x * E b i) * (R b j + x * E b j))
        (∑ b, (E b i * R b j + R b i * E b j)) 0 := by
      apply HasDerivAt.fun_sum
      intro b _
      have hi : HasDerivAt (fun x : ℝ ↦ R b i + x * E b i) (E b i) 0 := by
        convert
          (hasDerivAt_const (x := (0 : ℝ)) (c := R b i)).add
            ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (E b i)) using 1 <;>
          first | rfl | simp | exact Subsingleton.elim _ _
      have hj : HasDerivAt (fun x : ℝ ↦ R b j + x * E b j) (E b j) 0 := by
        convert
          (hasDerivAt_const (x := (0 : ℝ)) (c := R b j)).add
            ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (E b j)) using 1 <;>
          first | rfl | simp | exact Subsingleton.elim _ _
      convert hi.mul hj using 1 <;>
        first | rfl | simp | exact Subsingleton.elim _ _
    simpa only [Finset.sum_add_distrib] using hsum'
  exact hsum

/- The matrix inverse derivative needs a submultiplicative matrix norm.
These local instances force the same operator-norm topology in both the
statement and the library inverse theorem. -/
local instance wishartMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix m m ℝ) :=
  Matrix.linftyOpNormedAddCommGroup

local instance wishartMatrixNormedSpace : NormedSpace ℝ (Matrix m m ℝ) :=
  Matrix.linftyOpNormedSpace

local instance wishartMatrixAddCommGroup : AddCommGroup (Matrix m m ℝ) :=
  wishartMatrixNormedAddCommGroup.toAddCommGroup

local instance wishartMatrixModule : Module ℝ (Matrix m m ℝ) :=
  wishartMatrixNormedSpace.toModule

local instance wishartMatrixPseudoMetricSpace : PseudoMetricSpace (Matrix m m ℝ) :=
  wishartMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance wishartMatrixUniformSpace : UniformSpace (Matrix m m ℝ) :=
  wishartMatrixPseudoMetricSpace.toUniformSpace

local instance wishartMatrixTopologicalSpace : TopologicalSpace (Matrix m m ℝ) :=
  wishartMatrixUniformSpace.toTopologicalSpace

local instance wishartMatrixNormedRing : NormedRing (Matrix m m ℝ) :=
  Matrix.linftyOpNormedRing

local instance wishartMatrixNormedAlgebra : NormedAlgebra ℝ (Matrix m m ℝ) :=
  Matrix.linftyOpNormedAlgebra

/-- Evaluation of one square-matrix entry, as a linear map. -/
def squareMatrixEntryLinearMap (i j : m) :
    Matrix m m ℝ →ₗ[ℝ] ℝ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of one square-matrix entry is continuous for the operator
norm.  Finite dimensionality supplies continuity without requiring an
entrywise norm estimate. -/
def squareMatrixEntryCLM (i j : m) :
    Matrix m m ℝ →L[ℝ] ℝ :=
  (squareMatrixEntryLinearMap i j).toContinuousLinearMap

/-- Fréchet derivative of the nonsingular matrix inverse at an invertible
matrix, phrased for mathlib's nonsingular inverse operation. -/
theorem hasFDerivAt_matrix_nonsing_inv (M : Matrix m m ℝ)
    (hM : IsUnit M.det) :
    HasFDerivAt (fun N : Matrix m m ℝ ↦ N⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix m m ℝ) M⁻¹ M⁻¹) M := by
  have hUnit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr hM
  rcases hUnit with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_invertible,
    Matrix.coe_units_inv] using
    (hasFDerivAt_ringInverse (𝕜 := ℝ) u)

/-- Derivative of the inverse Gram matrix along an affine line. -/
theorem hasDerivAt_inverse_realWishartGram_matrixLine
    (R E : Matrix k m ℝ) (hM : IsUnit (realWishartGram R).det) :
    HasDerivAt
      (fun t : ℝ ↦ (realWishartGram (matrixLine R E t))⁻¹)
      (-((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹)) 0 := by
  have hbase : realWishartGram R = realWishartGram (matrixLine R E 0) := by
    simp [matrixLine]
  have h := (hasFDerivAt_matrix_nonsing_inv (realWishartGram R) hM).comp_hasDerivAt_of_eq
    0 (hasDerivAt_realWishartGram_matrixLine R E) hbase
  simpa [Function.comp_def, matrixLine,
    ContinuousLinearMap.mulLeftRight_apply] using h

/-- Entrywise form of the inverse-Gram derivative. -/
theorem hasDerivAt_inverse_realWishartGram_entry_matrixLine
    (R E : Matrix k m ℝ) (hM : IsUnit (realWishartGram R).det)
    (i j : m) :
    HasDerivAt
      (fun t : ℝ ↦ (realWishartGram (matrixLine R E t))⁻¹ i j)
      ((-((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹)) i j) 0 := by
  have h := (squareMatrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt
    0 (hasDerivAt_inverse_realWishartGram_matrixLine R E hM)
  convert h using 1 <;>
    first
    | rfl
    | simp [Function.comp_def, squareMatrixEntryCLM,
        squareMatrixEntryLinearMap]
    | exact Subsingleton.elim _ _

/-- A rectangular matrix entry varies affinely along `matrixLine`. -/
theorem hasDerivAt_matrixLine_apply
    (R E : Matrix k m ℝ) (a : k) (i : m) :
    HasDerivAt (fun t : ℝ ↦ matrixLine R E t a i) (E a i) 0 := by
  unfold matrixLine
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  convert
    (hasDerivAt_const (x := (0 : ℝ)) (c := R a i)).add
      ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (E a i)) using 1 <;>
    first | rfl | simp | exact Subsingleton.elim _ _

/-- Product-rule form of the linearization, before distributing the two
terms in the Gram derivative. -/
def steinVectorFieldRawLinearization
    (R : Matrix k m ℝ) (D : Matrix m m ℝ) (E : Matrix k m ℝ) :
    Matrix k m ℝ :=
  (1 / 2 : ℝ) •
    (E * ((realWishartGram R)⁻¹ * D) +
      R * (-((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹)) * D)

/-- The product-rule and distributed forms of the linearization agree. -/
theorem steinVectorFieldRawLinearization_eq
    (R : Matrix k m ℝ) (D : Matrix m m ℝ) (E : Matrix k m ℝ) :
    steinVectorFieldRawLinearization R D E =
      steinVectorFieldLinearization R D E := by
  unfold steinVectorFieldRawLinearization steinVectorFieldLinearization
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, sub_eq_add_neg]
  abel

/-- The lifted rational field has the advertised derivative along every
affine matrix line through a full-rank point. -/
theorem hasDerivAt_steinVectorFieldValue_matrixLine
    (R E : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    HasDerivAt
      (fun t : ℝ ↦ steinVectorFieldValue (matrixLine R E t) D)
      (steinVectorFieldLinearization R D E) 0 := by
  rw [← steinVectorFieldRawLinearization_eq R D E]
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro i
  let G : Matrix m m ℝ := (realWishartGram R)⁻¹
  let dG : Matrix m m ℝ :=
    -((realWishartGram R)⁻¹ *
      (E.transpose * R + R.transpose * E) *
      (realWishartGram R)⁻¹)
  have hGD (j : m) : HasDerivAt
      (fun t : ℝ ↦
        ((realWishartGram (matrixLine R E t))⁻¹ * D) j i)
      ((dG * D) j i) 0 := by
    simp only [Matrix.mul_apply]
    apply HasDerivAt.fun_sum
    intro l _
    exact
      (hasDerivAt_inverse_realWishartGram_entry_matrixLine R E hM j l).mul_const
        (D l i)
  have hterm (j : m) : HasDerivAt
      (fun t : ℝ ↦ matrixLine R E t a j *
        ((realWishartGram (matrixLine R E t))⁻¹ * D) j i)
      (E a j * (G * D) j i + R a j * (dG * D) j i) 0 := by
    have h := (hasDerivAt_matrixLine_apply R E a j).mul (hGD j)
    convert h using 1 <;>
      first
      | rfl
      | simp [matrixLine, G]
      | exact Subsingleton.elim _ _
  have hsum : HasDerivAt
      (fun t : ℝ ↦ ∑ j, matrixLine R E t a j *
        ((realWishartGram (matrixLine R E t))⁻¹ * D) j i)
      (∑ j, (E a j * (G * D) j i +
        R a j * (dG * D) j i)) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    exact hterm j
  have hscaled := hsum.const_mul (1 / 2 : ℝ)
  have hfun :
      (fun t : ℝ ↦ steinVectorFieldValue (matrixLine R E t) D a i) =
        (fun t : ℝ ↦ (1 / 2 : ℝ) *
          ∑ j, matrixLine R E t a j *
            ((realWishartGram (matrixLine R E t))⁻¹ * D) j i) := by
    funext t
    simp [steinVectorFieldValue, Matrix.mul_apply, Matrix.mul_assoc,
      Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  have hder :
      steinVectorFieldRawLinearization R D E a i =
        (1 / 2 : ℝ) *
          (∑ j, (E a j * (G * D) j i + R a j * (dG * D) j i)) := by
    unfold steinVectorFieldRawLinearization
    change
      ((1 / 2 : ℝ) • (E * (G * D) + (R * dG) * D)) a i =
        (1 / 2 : ℝ) *
          (∑ j, (E a j * (G * D) j i + R a j * (dG * D) j i))
    rw [Matrix.mul_assoc R dG D]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib]
  convert hscaled using 1 <;>
    first
    | exact hfun
    | exact hder
    | rfl
    | exact Subsingleton.elim _ _

/-- Coordinate definition of the genuine divergence of the lifted field.
Each partial derivative is taken along the corresponding matrix unit. -/
def steinVectorFieldCoordinateDivergence
    (R : Matrix k m ℝ) (D : Matrix m m ℝ) : ℝ :=
  ∑ a, ∑ i,
    deriv
      (fun t : ℝ ↦
        steinVectorFieldValue
          (matrixLine R (Matrix.single a i 1) t) D a i)
      0

/-- On the full-rank locus, the analytic coordinate divergence equals the
coordinate trace of the algebraic linearization. -/
theorem steinVectorFieldCoordinateDivergence_eq_coordinateTrace
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    steinVectorFieldCoordinateDivergence R D =
      rectangularCoordinateTrace (steinVectorFieldLinearization R D) := by
  unfold steinVectorFieldCoordinateDivergence rectangularCoordinateTrace
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  have hmat := hasDerivAt_steinVectorFieldValue_matrixLine R
    (Matrix.single a i 1) D hM
  have ha := hasDerivAt_pi.mp hmat a
  have hai := hasDerivAt_pi.mp ha i
  exact hai.deriv

/-- Exact analytic divergence formula for the singular lifted rational
vector field, valid at every full-rank matrix. -/
theorem steinVectorFieldCoordinateDivergence_eq
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    steinVectorFieldCoordinateDivergence R D =
      (((Fintype.card k : ℝ) - (Fintype.card m : ℝ) - 1) / 2) *
        Matrix.trace ((realWishartGram R)⁻¹ * D) := by
  rw [steinVectorFieldCoordinateDivergence_eq_coordinateTrace R D hM,
    rectangularCoordinateTrace_steinVectorFieldLinearization R D hM]

end Wishart

end

end LogdetLean.GramHafnian
