import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.HalfGaussianMatrixMass
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SteinFieldCoordinateBounds
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.PreservedSWeight
import Mathlib.Analysis.Normed.Operator.Basic
/-!
# Bounds for bounded-derivative Gram tests against the singular Stein field

This module controls the only weighted term not covered by the bare
inverse-Gram field estimates: the product of one coordinate of

`D (phi ∘ (R ↦ RᵀR))`

with the matching coordinate of the singular Stein field.  A uniform bound
on the full Frechet derivative of `phi` gives a square bound by the Gaussian
matrix mass; Young's inequality then leaves only the common integrable
majorant `1 + ||R||_F² + trace ((RᵀR)⁻¹)`.
-/

open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/- The calculus imports intentionally do not globally select the operator
norm topology on spaces of continuous linear maps.  Select it locally only
for the scalar matrix functionals whose uniform norm is an explicit
hypothesis below. -/
local instance matrixFunctionalNorm
    {p : Type*} [Fintype p] :
    Norm (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

local instance matrixFunctionalSeminormedAddCommGroup
    {p : Type*} [Fintype p] :
    SeminormedAddCommGroup (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- Every coordinate square is bounded by the squared Frobenius mass. -/
theorem sq_entry_le_rectangularSqMass
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (R : Matrix k p ℝ) (a : k) (i : p) :
    (R a i) ^ 2 ≤ rectangularSqMass R := by
  unfold rectangularSqMass
  calc
    (R a i) ^ 2 ≤ ∑ j : p, (R a j) ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (R a j)) (Finset.mem_univ i)
    _ ≤ ∑ b : k, ∑ j : p, (R b j) ^ 2 :=
      Finset.single_le_sum
        (fun b _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (R b j))
        (Finset.mem_univ a)

/-- Entrywise supremum norm squared is bounded by squared Frobenius mass. -/
theorem elementwise_norm_sq_le_rectangularSqMass
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (R : Matrix k p ℝ) :
    ‖R‖ ^ 2 ≤ rectangularSqMass R := by
  have habs (a : k) (i : p) :
      |R a i| ≤ Real.sqrt (rectangularSqMass R) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (rectangularSqMass_nonneg R)]
    exact sq_entry_le_rectangularSqMass R a i
  have hnorm : ‖R‖ ≤ Real.sqrt (rectangularSqMass R) := by
    rw [Matrix.norm_le_iff (Real.sqrt_nonneg _)]
    intro a i
    simpa [Real.norm_eq_abs] using habs a i
  calc
    ‖R‖ ^ 2 ≤ (Real.sqrt (rectangularSqMass R)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg R) (Real.sqrt_nonneg _)).mpr hnorm
    _ = rectangularSqMass R := Real.sq_sqrt (rectangularSqMass_nonneg R)

/-- Crude multiplication bound for the elementwise supremum matrix norm. -/
theorem elementwise_norm_mul_le_card
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    ‖A * B‖ ≤ (Fintype.card m : ℝ) * ‖A‖ * ‖B‖ := by
  rw [Matrix.norm_le_iff (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg A)) (norm_nonneg B))]
  intro i j
  calc
    ‖(A * B) i j‖ = ‖∑ x, A i x * B x j‖ := by rw [Matrix.mul_apply]
    _ ≤ ∑ x, ‖A i x * B x j‖ := norm_sum_le _ _
    _ ≤ ∑ _x : m, ‖A‖ * ‖B‖ := by
      apply Finset.sum_le_sum
      intro x _
      exact (norm_mul_le _ _).trans (mul_le_mul
        (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B)
        (norm_nonneg _) (norm_nonneg _))
    _ = (Fintype.card m : ℝ) * ‖A‖ * ‖B‖ := by
      simp [nsmul_eq_mul]
      ring

theorem elementwise_norm_single_one_le
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (a : k) (i : p) :
    ‖Matrix.single a i (1 : ℝ)‖ ≤ 1 := by
  rw [Matrix.norm_le_iff (by norm_num)]
  intro b j
  simp only [Matrix.single_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- A same-coordinate first Gram variation grows at most linearly in `R`. -/
theorem elementwise_norm_realWishartGramFirstVariation_single_le
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (R : Matrix k p ℝ) (a : k) (i : p) :
    ‖(Matrix.single a i (1 : ℝ)).transpose * R +
        R.transpose * Matrix.single a i (1 : ℝ)‖ ≤
      2 * (Fintype.card k : ℝ) * ‖R‖ := by
  let E : Matrix k p ℝ := Matrix.single a i 1
  have hE : ‖E‖ ≤ 1 := elementwise_norm_single_one_le a i
  have hET : ‖E.transpose‖ ≤ 1 := by
    rw [Matrix.norm_transpose]
    exact hE
  have hRT : ‖R.transpose‖ = ‖R‖ := Matrix.norm_transpose R
  calc
    ‖E.transpose * R + R.transpose * E‖ ≤
        ‖E.transpose * R‖ + ‖R.transpose * E‖ := norm_add_le _ _
    _ ≤ ((Fintype.card k : ℝ) * ‖E.transpose‖ * ‖R‖) +
        ((Fintype.card k : ℝ) * ‖R.transpose‖ * ‖E‖) :=
      add_le_add (elementwise_norm_mul_le_card _ _)
        (elementwise_norm_mul_le_card _ _)
    _ ≤ ((Fintype.card k : ℝ) * 1 * ‖R‖) +
        ((Fintype.card k : ℝ) * ‖R‖ * 1) := by
      rw [hRT]
      gcongr
    _ = 2 * (Fintype.card k : ℝ) * ‖R‖ := by ring

/-- A scalar test pulled back through the real Gram map. -/
def gramTestWeight
    {k p : Type*} [Fintype k]
    (phi : Matrix p p ℝ → ℝ) (R : Matrix k p ℝ) : ℝ :=
  phi (realWishartGram R)

/-- Chain-rule differential of a scalar test pulled back through the Gram map. -/
def gramTestWeightDerivative
    {k p : Type*} [Fintype k] [Fintype p]
    (phi' : Matrix p p ℝ → Matrix p p ℝ →L[ℝ] ℝ)
    (R : Matrix k p ℝ) : Matrix k p ℝ →L[ℝ] ℝ :=
  (phi' (realWishartGram R)).comp (realWishartGramFirstVariationCLM R)

theorem hasFDerivAt_gramTestWeight
    {k p : Type*} [Fintype k] [Fintype p]
    (phi : Matrix p p ℝ → ℝ)
    (phi' : Matrix p p ℝ → Matrix p p ℝ →L[ℝ] ℝ)
    (hphi : ∀ M, HasFDerivAt phi (phi' M) M)
    (R : Matrix k p ℝ) :
    HasFDerivAt (gramTestWeight phi)
      (gramTestWeightDerivative phi' R) R := by
  exact (hphi (realWishartGram R)).comp R (hasFDerivAt_realWishartGram R)

/-- The square of a same-coordinate derivative of a bounded-derivative
Gram test is controlled by the nonsingular Gaussian matrix mass. -/
theorem sq_gramTestWeightDerivative_single_le
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (phi' : Matrix p p ℝ → Matrix p p ℝ →L[ℝ] ℝ)
    (C₁ : ℝ) (hphi' : ∀ M, ‖phi' M‖ ≤ C₁)
    (R : Matrix k p ℝ) (a : k) (i : p) :
    (gramTestWeightDerivative phi' R
        (Matrix.single a i (1 : ℝ))) ^ 2 ≤
      (2 * (Fintype.card k : ℝ) * C₁) ^ 2 * rectangularSqMass R := by
  let E : Matrix k p ℝ := Matrix.single a i 1
  let B : Matrix p p ℝ := E.transpose * R + R.transpose * E
  let L := phi' (realWishartGram R)
  have hC₁ : 0 ≤ C₁ :=
    (norm_nonneg (phi' (0 : Matrix p p ℝ))).trans (hphi' 0)
  have hB : ‖B‖ ≤ 2 * (Fintype.card k : ℝ) * ‖R‖ := by
    simpa [B, E] using
      elementwise_norm_realWishartGramFirstVariation_single_le R a i
  have hLnorm : ‖L‖ ≤ C₁ := by
    simpa [L] using hphi' (realWishartGram R)
  have hL : ‖L B‖ ≤ C₁ * (2 * (Fintype.card k : ℝ) * ‖R‖) := by
    calc
      ‖L B‖ ≤ ‖L‖ * ‖B‖ := L.le_opNorm B
      _ ≤ C₁ * (2 * (Fintype.card k : ℝ) * ‖R‖) :=
        mul_le_mul hLnorm hB (norm_nonneg _) hC₁
  have habs :
      |gramTestWeightDerivative phi' R E| ≤
        2 * (Fintype.card k : ℝ) * C₁ * ‖R‖ := by
    change ‖L B‖ ≤ _
    calc
      ‖L B‖ ≤ C₁ * (2 * (Fintype.card k : ℝ) * ‖R‖) := hL
      _ = 2 * (Fintype.card k : ℝ) * C₁ * ‖R‖ := by ring
  have hright : 0 ≤ 2 * (Fintype.card k : ℝ) * C₁ * ‖R‖ := by
    positivity
  calc
    (gramTestWeightDerivative phi' R E) ^ 2 =
        |gramTestWeightDerivative phi' R E| ^ 2 := by rw [sq_abs]
    _ ≤ (2 * (Fintype.card k : ℝ) * C₁ * ‖R‖) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hright).mpr habs
    _ = (2 * (Fintype.card k : ℝ) * C₁) ^ 2 * ‖R‖ ^ 2 := by ring
    _ ≤ (2 * (Fintype.card k : ℝ) * C₁) ^ 2 *
        rectangularSqMass R :=
      mul_le_mul_of_nonneg_left
        (elementwise_norm_sq_le_rectangularSqMass R) (sq_nonneg _)

end Wishart

end

end LogdetLean.GramHafnian
