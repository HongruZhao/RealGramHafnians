import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FlatDivergenceTransport
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedScore
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Smooth weights factoring through the preserved S coordinate

This file supplies the literal Frechet derivative of
`R \mapsto S(R^T R)` and packages the chain rule for scalar weights of this
preserved coordinate.  In particular, the resulting derivative factors in
the exact form consumed by the integrated conditional-Wishart score theorem.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/- Matrix norm structures have algebraic parents that are propositionally,
but not always definitionally, the same as the standalone function-space
instances.  Fix the parent structures locally so all Frechet derivatives in
this file use one coherent elementwise topology. -/
local instance preservedMatrixNormedAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : NormedAddCommGroup (Matrix a b 𝕜) :=
  Matrix.normedAddCommGroup

local instance preservedMatrixNormedSpace
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    NormedSpace 𝔽 (Matrix a b 𝕜) :=
  Matrix.normedSpace

local instance preservedMatrixAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : AddCommGroup (Matrix a b 𝕜) :=
  preservedMatrixNormedAddCommGroup.toAddCommGroup

local instance preservedMatrixModule
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    Module 𝔽 (Matrix a b 𝕜) :=
  preservedMatrixNormedSpace.toModule

local instance preservedMatrixPseudoMetricSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : PseudoMetricSpace (Matrix a b 𝕜) :=
  preservedMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance preservedMatrixUniformSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : UniformSpace (Matrix a b 𝕜) :=
  preservedMatrixPseudoMetricSpace.toUniformSpace

local instance preservedMatrixTopologicalSpace
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : TopologicalSpace (Matrix a b 𝕜) :=
  preservedMatrixUniformSpace.toTopologicalSpace

/-- Evaluation of an entry of a rectangular real matrix. -/
def rectangularMatrixEntryLinearMap
    {k p : Type*} (a : k) (j : p) :
    Matrix k p ℝ →ₗ[ℝ] ℝ where
  toFun R := R a j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Entry evaluation is continuous in finite dimensions. -/
def rectangularMatrixEntryCLM
    {k p : Type*} [Fintype k] [Fintype p]
    (a : k) (j : p) : Matrix k p ℝ →L[ℝ] ℝ :=
  (rectangularMatrixEntryLinearMap a j).toContinuousLinearMap

@[simp] theorem rectangularMatrixEntryCLM_apply
    {k p : Type*} [Fintype k] [Fintype p]
    (a : k) (j : p) (R : Matrix k p ℝ) :
    rectangularMatrixEntryCLM a j R = R a j :=
  rfl

/-- The first variation of `R \mapsto R^T R`, as a linear map. -/
def realWishartGramFirstVariationLinearMap
    {k p : Type*} [Fintype k] [Fintype p]
    (R : Matrix k p ℝ) : Matrix k p ℝ →ₗ[ℝ] Matrix p p ℝ where
  toFun F := F.transpose * R + R.transpose * F
  map_add' F G := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply,
      add_mul, mul_add, Finset.sum_add_distrib]
    abel
  map_smul' c F := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.mul_apply, smul_eq_mul, mul_assoc]
    have hsecond :
        (∑ a, R a i * (c * F a j)) =
          c * ∑ a, R a i * F a j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have hfirst :
        (∑ a, c * (F a i * R a j)) =
          c * ∑ a, F a i * R a j := by
      rw [Finset.mul_sum]
    rw [hsecond, hfirst]
    simp only [RingHom.id_apply]
    ring

/-- The derivative of `R \mapsto R^T R`, as a continuous linear map. -/
def realWishartGramFirstVariationCLM
    {k p : Type*} [Fintype k] [Fintype p]
    (R : Matrix k p ℝ) : Matrix k p ℝ →L[ℝ] Matrix p p ℝ :=
  (realWishartGramFirstVariationLinearMap R).toContinuousLinearMap

@[simp] theorem realWishartGramFirstVariationCLM_apply
    {k p : Type*} [Fintype k] [Fintype p]
    (R F : Matrix k p ℝ) :
    realWishartGramFirstVariationCLM R F =
      F.transpose * R + R.transpose * F := by
  rfl

/-- For fixed left input, `(X,Y) \mapsto X^T Y` is linear in `Y`. -/
def transposeMulRightLinearMap
    {k p : Type*} [Fintype k] [Fintype p]
    (X : Matrix k p ℝ) : Matrix k p ℝ →ₗ[ℝ] Matrix p p ℝ where
  toFun Y := X.transpose * Y
  map_add' Y Z := by simp [Matrix.mul_add]
  map_smul' c Y := by simp [Matrix.mul_smul]

/-- The transpose-multiplication bilinear map, with the right-linear map
made continuous by finite dimensionality, is linear in its left input. -/
def transposeMulOuterLinearMap
    {k p : Type*} [Fintype k] [Fintype p] :
    Matrix k p ℝ →ₗ[ℝ] (Matrix k p ℝ →L[ℝ] Matrix p p ℝ) where
  toFun X := (transposeMulRightLinearMap X).toContinuousLinearMap
  map_add' X Z := by
    ext Y i j
    simp [transposeMulRightLinearMap, Matrix.add_mul]
  map_smul' c X := by
    ext Y i j
    simp [transposeMulRightLinearMap, Matrix.smul_mul]

/-- Continuous bilinear form `(X,Y) \mapsto X^T Y`.  Both continuity
steps use only finite dimensionality. -/
def transposeMulBilinearCLM
    {k p : Type*} [Fintype k] [Fintype p] :
    Matrix k p ℝ →L[ℝ] (Matrix k p ℝ →L[ℝ] Matrix p p ℝ) :=
  transposeMulOuterLinearMap.toContinuousLinearMap

@[simp] theorem transposeMulBilinearCLM_apply
    {k p : Type*} [Fintype k] [Fintype p]
    (X Y : Matrix k p ℝ) :
    transposeMulBilinearCLM X Y = X.transpose * Y :=
  rfl

/-- Frechet derivative of the real Gram map at every rectangular matrix. -/
theorem hasFDerivAt_realWishartGram
    {k p : Type*} [Fintype k] [Fintype p]
    (R : Matrix k p ℝ) :
    HasFDerivAt realWishartGram
      (realWishartGramFirstVariationCLM R) R := by
  let B := transposeMulBilinearCLM (k := k) (p := p)
  have h := B.hasFDerivAt_of_bilinear
    (hasFDerivAt_id R) (hasFDerivAt_id R)
  convert h using 1 <;>
    first
    | rfl
    | exact Subsingleton.elim _ _
    | (funext X; simp [B, realWishartGram])
    | (ext F; simp [B, realWishartGramFirstVariationCLM_apply]; abel)
    | simp [preservedMatrixTopologicalSpace,
        preservedMatrixUniformSpace, preservedMatrixPseudoMetricSpace]

/-- The extraction of the complex `S` coordinate is real-linear. -/
def sCoordinateOfRealGramLinearMap
    {m : Type*} :
    Matrix (m ⊕ m) (m ⊕ m) ℝ →ₗ[ℝ] Matrix m m ℂ where
  toFun := sCoordinateOfRealGram
  map_add' A B := by
    ext i j
    apply Complex.ext <;>
      simp [sCoordinateOfRealGram, realGramBlock11, realGramBlock12,
        realGramBlock22, sOfRealBlocks] <;> ring
  map_smul' c A := by
    ext i j
    apply Complex.ext <;>
      simp [sCoordinateOfRealGram, realGramBlock11, realGramBlock12,
        realGramBlock22, sOfRealBlocks] <;> ring

/-- Continuous version of the real-linear `S`-coordinate extraction. -/
def sCoordinateOfRealGramCLM
    {m : Type*} [Fintype m] :
    Matrix (m ⊕ m) (m ⊕ m) ℝ →L[ℝ] Matrix m m ℂ :=
  sCoordinateOfRealGramLinearMap.toContinuousLinearMap

@[simp] theorem sCoordinateOfRealGramCLM_apply
    {m : Type*} [Fintype m]
    (M : Matrix (m ⊕ m) (m ⊕ m) ℝ) :
    sCoordinateOfRealGramCLM M = sCoordinateOfRealGram M :=
  rfl

/-- Continuous-linear first variation of the preserved `S` coordinate. -/
def sCoordinateFirstVariationCLM
    {k m : Type*} [Fintype k] [Fintype m]
    (R : Matrix k (m ⊕ m) ℝ) :
    Matrix k (m ⊕ m) ℝ →L[ℝ] Matrix m m ℂ :=
  sCoordinateOfRealGramCLM.comp
    (realWishartGramFirstVariationCLM R)

@[simp] theorem sCoordinateFirstVariationCLM_apply
    {k m : Type*} [Fintype k] [Fintype m]
    (R F : Matrix k (m ⊕ m) ℝ) :
    sCoordinateFirstVariationCLM R F =
      sCoordinateFirstVariation R F := by
  simp [sCoordinateFirstVariationCLM, sCoordinateFirstVariation]

/-- The literal preserved-coordinate map on rectangular real matrices. -/
def preservedSCoordinate
    {k m : Type*} [Fintype k]
    (R : Matrix k (m ⊕ m) ℝ) : Matrix m m ℂ :=
  sCoordinateOfRealGram (realWishartGram R)

/-- Frechet derivative of the literal preserved-coordinate map. -/
theorem hasFDerivAt_preservedSCoordinate
    {k m : Type*} [Fintype k] [Fintype m]
    (R : Matrix k (m ⊕ m) ℝ) :
    HasFDerivAt preservedSCoordinate
      (sCoordinateFirstVariationCLM R) R := by
  exact sCoordinateOfRealGramCLM.hasFDerivAt.comp R
    (hasFDerivAt_realWishartGram R)

/-- A scalar weight obtained by composing a test with the preserved
coordinate. -/
def preservedSWeight
    {k m : Type*} [Fintype k]
    (psi : Matrix m m ℂ → ℝ)
    (R : Matrix k (m ⊕ m) ℝ) : ℝ :=
  psi (preservedSCoordinate R)

/-- The chain-rule derivative of a scalar preserved-`S` weight. -/
def preservedSWeightDerivative
    {k m : Type*} [Fintype k] [Fintype m]
    (psi' : Matrix m m ℂ → Matrix m m ℂ →L[ℝ] ℝ)
    (R : Matrix k (m ⊕ m) ℝ) :
    Matrix k (m ⊕ m) ℝ →L[ℝ] ℝ :=
  (psi' (preservedSCoordinate R)).comp
    (sCoordinateFirstVariationCLM R)

/-- Chain rule for every differentiable scalar test on the `S` coordinate. -/
theorem hasFDerivAt_preservedSWeight
    {k m : Type*} [Fintype k] [Fintype m]
    (psi : Matrix m m ℂ → ℝ)
    (psi' : Matrix m m ℂ → Matrix m m ℂ →L[ℝ] ℝ)
    (hpsi : ∀ S, HasFDerivAt psi (psi' S) S)
    (R : Matrix k (m ⊕ m) ℝ) :
    HasFDerivAt (preservedSWeight psi)
      (preservedSWeightDerivative psi' R) R := by
  exact (hpsi (preservedSCoordinate R)).comp R
    (hasFDerivAt_preservedSCoordinate R)

/-- The preserved-weight derivative factors through the advertised first
variation, in exactly the form required by `IntegratedScore`. -/
theorem preservedSWeightDerivative_factor
    {k m : Type*} [Fintype k] [Fintype m]
    (psi' : Matrix m m ℂ → Matrix m m ℂ →L[ℝ] ℝ)
    (R F : Matrix k (m ⊕ m) ℝ) :
    preservedSWeightDerivative psi' R F =
      psi' (preservedSCoordinate R)
        (sCoordinateFirstVariation R F) := by
  simp [preservedSWeightDerivative]

end Wishart

end

end LogdetLean.GramHafnian
