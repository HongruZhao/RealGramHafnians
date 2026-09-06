import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SingularSteinFieldBounds
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.MatrixSteinHaffClosure
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericSteinHaffIntegrability
/-!
# Axiom-free Stein--Haff identity for bounded full derivatives

This file discharges the componentwise `L¹` hypotheses of the already
formalized Gaussian divergence theorem.  The test class is deliberately
stronger than a merely bounded chosen directional derivative: the full
Frechet differential of the scalar Gram test is uniformly bounded.  This is
exactly what the compactly supported preserved-coordinate tests provide.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

local instance steinHaffMatrixFunctionalNorm
    {p : Type*} [Fintype p] :
    Norm (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

local instance steinHaffMatrixFunctionalSeminormedAddCommGroup
    {p : Type*} [Fintype p] :
    SeminormedAddCommGroup (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

private theorem measurable_matrix_mul
    {X l m n : Type*} [MeasurableSpace X]
    [Fintype l] [Fintype m] [Fintype n]
    {A : X → Matrix l m ℝ} {B : X → Matrix m n ℝ}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x * B x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun q _ ↦
    ((measurable_pi_apply q).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply q).comp hB))

private theorem measurable_matrix_transpose
    {X l m : Type*} [MeasurableSpace X]
    [Fintype l] [Fintype m]
    {A : X → Matrix l m ℝ} (hA : Measurable A) :
    Measurable (fun x ↦ (A x).transpose) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hA)

private theorem measurable_matrix_add
    {X l m : Type*} [MeasurableSpace X]
    [Fintype l] [Fintype m]
    {A B : X → Matrix l m ℝ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x + B x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).add
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hB))

private theorem measurable_matrix_neg
    {X l m : Type*} [MeasurableSpace X]
    [Fintype l] [Fintype m]
    {A : X → Matrix l m ℝ} (hA : Measurable A) :
    Measurable (fun x ↦ -A x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).neg

private theorem measurable_matrix_sub
    {X l m : Type*} [MeasurableSpace X]
    [Fintype l] [Fintype m]
    {A B : X → Matrix l m ℝ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x - B x) := by
  simpa only [sub_eq_add_neg] using measurable_matrix_add hA (measurable_matrix_neg hB)

private theorem measurable_matrix_const_smul
    {X l m : Type*} [MeasurableSpace X]
    [Fintype l] [Fintype m]
    {A : X → Matrix l m ℝ} (hA : Measurable A) (c : ℝ) :
    Measurable (fun x ↦ c • A x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_const.mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA))

private theorem const_add_linear_le_sum_mul_majorant
    {A B C r t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (ht : 0 ≤ t) :
    C + A * r + B * t ≤ (A + B + C) * (1 + r + t) := by
  calc
    C + A * r + B * t ≤
        C + A * r + B * t +
          (A + B + B * r + C * r + A * t + C * t) := by
      apply le_add_of_nonneg_right
      positivity
    _ = (A + B + C) * (1 + r + t) := by ring

/-- Coordinatewise measurability of the nonsingular inverse Gram matrix. -/
theorem measurable_nonsingInv_realWishartGram_matrix
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p] :
    Measurable (fun R : Matrix k p ℝ ↦ (realWishartGram R)⁻¹) := by
  have hGram : Measurable
      (realWishartGram : Matrix k p ℝ → Matrix p p ℝ) :=
    measurable_realWishartGram_genericSteinHaff
  have measurable_det_of_measurable
      {A : Matrix k p ℝ → Matrix p p ℝ}
      (hA : Measurable A) : Measurable (fun R ↦ (A R).det) := by
    simp_rw [Matrix.det_apply']
    exact Finset.measurable_sum _ fun σ _ ↦
      measurable_const.mul (Finset.measurable_prod _ fun i _ ↦
        (measurable_pi_apply i).comp
          ((measurable_pi_apply (σ i)).comp hA))
  have hdet : Measurable
      (fun R : Matrix k p ℝ ↦ (realWishartGram R).det) :=
    measurable_det_of_measurable hGram
  have hentry (i j : p) : Measurable
      (fun R : Matrix k p ℝ ↦ realWishartGram R i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hGram)
  have hadj : Measurable
      (fun R : Matrix k p ℝ ↦ (realWishartGram R).adjugate) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.adjugate_apply]
    apply measurable_det_of_measurable
    refine measurable_pi_lambda _ fun a ↦ measurable_pi_lambda _ fun b ↦ ?_
    by_cases ha : a = j
    · simp [ha]
    · simpa [Matrix.updateRow_apply, ha] using hentry a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hdet.fun_inv.mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hadj))

theorem measurable_steinVectorFieldValue_apply
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (D : Matrix p p ℝ) (a : k) (i : p) :
    Measurable (fun R : Matrix k p ℝ ↦ steinVectorFieldValue R D a i) := by
  have hR : Measurable (fun R : Matrix k p ℝ ↦ R) := measurable_id
  have hG := measurable_nonsingInv_realWishartGram_matrix (k := k) (p := p)
  have hRG : Measurable (fun R : Matrix k p ℝ ↦
      R * (realWishartGram R)⁻¹) :=
    measurable_matrix_mul hR hG
  have hD : Measurable (fun _R : Matrix k p ℝ ↦ D) := measurable_const
  have hRGD : Measurable (fun R : Matrix k p ℝ ↦
      (R * (realWishartGram R)⁻¹) * D) :=
    measurable_matrix_mul hRG hD
  exact (measurable_pi_apply i).comp ((measurable_pi_apply a).comp
    (measurable_matrix_const_smul hRGD (1 / 2 : ℝ)))

theorem measurable_steinVectorFieldLinearization_single_same
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (D : Matrix p p ℝ) (a : k) (i : p) :
    Measurable (fun R : Matrix k p ℝ ↦
      steinVectorFieldLinearization R D (Matrix.single a i 1) a i) := by
  have hR : Measurable (fun R : Matrix k p ℝ ↦ R) := measurable_id
  have hRT : Measurable (fun R : Matrix k p ℝ ↦ R.transpose) :=
    measurable_matrix_transpose hR
  have hG := measurable_nonsingInv_realWishartGram_matrix (k := k) (p := p)
  have hRG : Measurable (fun R : Matrix k p ℝ ↦
      R * (realWishartGram R)⁻¹) :=
    measurable_matrix_mul hR hG
  have hD : Measurable (fun _R : Matrix k p ℝ ↦ D) := measurable_const
  have hGD : Measurable (fun R : Matrix k p ℝ ↦
      (realWishartGram R)⁻¹ * D) :=
    measurable_matrix_mul hG hD
  have hRGD : Measurable (fun R : Matrix k p ℝ ↦
      (R * (realWishartGram R)⁻¹) * D) :=
    measurable_matrix_mul hRG hD
  have hRGR : Measurable (fun R : Matrix k p ℝ ↦
      (R * (realWishartGram R)⁻¹) * R.transpose) :=
    measurable_matrix_mul hRG hRT
  have hE : Measurable
      (fun _R : Matrix k p ℝ ↦ Matrix.single a i (1 : ℝ)) := measurable_const
  have hET : Measurable (fun _R : Matrix k p ℝ ↦
      (Matrix.single a i (1 : ℝ)).transpose) :=
    measurable_matrix_transpose hE
  have hEGD : Measurable (fun R : Matrix k p ℝ ↦
      Matrix.single a i (1 : ℝ) * ((realWishartGram R)⁻¹ * D)) :=
    measurable_matrix_mul hE hGD
  have hRGET : Measurable (fun R : Matrix k p ℝ ↦
      (R * (realWishartGram R)⁻¹) *
        (Matrix.single a i (1 : ℝ)).transpose) :=
    measurable_matrix_mul hRG hET
  have hUGE : Measurable (fun R : Matrix k p ℝ ↦
      ((R * (realWishartGram R)⁻¹) *
          (Matrix.single a i (1 : ℝ)).transpose) *
        (R * (realWishartGram R)⁻¹ * D)) :=
    measurable_matrix_mul hRGET hRGD
  have hRGE : Measurable (fun R : Matrix k p ℝ ↦
      ((R * (realWishartGram R)⁻¹) * R.transpose) *
        Matrix.single a i (1 : ℝ)) :=
    measurable_matrix_mul hRGR hE
  have hPE : Measurable (fun R : Matrix k p ℝ ↦
      (((R * (realWishartGram R)⁻¹) * R.transpose) *
          Matrix.single a i (1 : ℝ)) *
        ((realWishartGram R)⁻¹ * D)) :=
    measurable_matrix_mul hRGE hGD
  have hsub : Measurable (fun R : Matrix k p ℝ ↦
      (Matrix.single a i (1 : ℝ) * ((realWishartGram R)⁻¹ * D) -
        (R * (realWishartGram R)⁻¹) * (Matrix.single a i (1 : ℝ)).transpose *
          (R * (realWishartGram R)⁻¹ * D)) -
        (R * (realWishartGram R)⁻¹ * R.transpose) * Matrix.single a i (1 : ℝ) *
          ((realWishartGram R)⁻¹ * D)) := by
    exact measurable_matrix_sub (measurable_matrix_sub hEGD hUGE) hPE
  exact (measurable_pi_apply i).comp ((measurable_pi_apply a).comp
    (measurable_matrix_const_smul hsub (1 / 2 : ℝ)))

/-- Matrix-coordinate versions of the three fields consumed by Gaussian
integration by parts. -/
def gramTestSteinComponent
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (phi : Matrix p p ℝ → ℝ) (D : Matrix p p ℝ) (a : k) (i : p)
    (R : Matrix k p ℝ) : ℝ :=
  gramTestWeight phi R * steinVectorFieldValue R D a i

def gramTestSteinComponentDerivative
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (phi : Matrix p p ℝ → ℝ)
    (phi' : Matrix p p ℝ → Matrix p p ℝ →L[ℝ] ℝ)
    (D : Matrix p p ℝ) (a : k) (i : p) (R : Matrix k p ℝ) : ℝ :=
  gramTestWeightDerivative phi' R (Matrix.single a i 1) *
      steinVectorFieldValue R D a i +
    gramTestWeight phi R *
      steinVectorFieldLinearization R D (Matrix.single a i 1) a i

/-- The radial scalar term paired with a single matrix coordinate. -/
def gramTestSteinComponentRadial
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (phi : Matrix p p ℝ → ℝ) (D : Matrix p p ℝ) (a : k) (i : p)
    (R : Matrix k p ℝ) : ℝ :=
  2 * R a i * gramTestSteinComponent phi D a i R

theorem measurable_gramTestWeight
    {k p : Type*} [Fintype k] [Fintype p]
    (phi : Matrix p p ℝ → ℝ) (hphi : Continuous phi) :
    Measurable (gramTestWeight (k := k) phi) := by
  exact (measurable_of_continuous_matrix_real_genericSteinHaff phi hphi).comp
    measurable_realWishartGram_genericSteinHaff

theorem continuous_gramTestWeightDerivative_single
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (phi' : Matrix p p ℝ → Matrix p p ℝ →L[ℝ] ℝ)
    (hphi' : Continuous phi') (a : k) (i : p) :
    Continuous (fun R : Matrix k p ℝ ↦
      gramTestWeightDerivative phi' R (Matrix.single a i 1)) := by
  have heq : (fun R : Matrix k p ℝ ↦
      gramTestWeightDerivative phi' R (Matrix.single a i 1)) =
      (fun R : Matrix k p ℝ ↦
        phi' (realWishartGram R)
          ((Matrix.single a i (1 : ℝ)).transpose * R +
            R.transpose * Matrix.single a i (1 : ℝ))) := by
    funext R
    rfl
  rw [heq]
  have hL : Continuous (fun R : Matrix k p ℝ ↦
      phi' (realWishartGram R)) :=
    hphi'.comp continuous_realWishartGram_genericSteinHaff
  have hB : Continuous (fun R : Matrix k p ℝ ↦
      (Matrix.single a i (1 : ℝ)).transpose * R +
        R.transpose * Matrix.single a i (1 : ℝ)) := by
    fun_prop
  exact hL.clm_apply hB

/-- Opaque chain-rule interface in the singular Stein direction.  Keeping
this identity in the defining matrix topology prevents downstream users
from having to unfold continuous-linear-map instance parents. -/
theorem gramTestWeightDerivative_steinVectorFieldValue
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (phi' : Matrix p p ℝ → Matrix p p ℝ →L[ℝ] ℝ)
    (R : Matrix k p ℝ) (D : Matrix p p ℝ)
    (hD : D.IsSymm) (hM : IsUnit (realWishartGram R).det) :
    gramTestWeightDerivative phi' R (steinVectorFieldValue R D) =
      phi' (realWishartGram R) D := by
  change phi' (realWishartGram R)
      ((steinVectorFieldValue R D).transpose * R +
        R.transpose * steinVectorFieldValue R D) = _
  rw [gram_firstVariation_steinVectorFieldValue R hD hM]

theorem measurable_gramTestSteinComponent
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (phi : Matrix p p ℝ → ℝ) (hphi : Continuous phi)
    (D : Matrix p p ℝ) (a : k) (i : p) :
    Measurable (gramTestSteinComponent phi D a i) := by
  exact (measurable_gramTestWeight phi hphi).mul
    (measurable_steinVectorFieldValue_apply D a i)

theorem measurable_gramTestSteinComponentDerivative
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (phi : Matrix p p ℝ → ℝ) (hphi : Continuous phi)
    (phi' : Matrix p p ℝ → Matrix p p ℝ →L[ℝ] ℝ)
    (hphi' : Continuous phi')
    (D : Matrix p p ℝ) (a : k) (i : p) :
    Measurable (gramTestSteinComponentDerivative phi phi' D a i) := by
  exact ((measurable_of_continuous_matrix_real_genericSteinHaff _
      (continuous_gramTestWeightDerivative_single phi' hphi' a i)).mul
      (measurable_steinVectorFieldValue_apply D a i)).add
    ((measurable_gramTestWeight phi hphi).mul
      (measurable_steinVectorFieldLinearization_single_same D a i))

theorem measurable_gramTestSteinComponentRadial
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (phi : Matrix p p ℝ → ℝ) (hphi : Continuous phi)
    (D : Matrix p p ℝ) (a : k) (i : p) :
    Measurable (gramTestSteinComponentRadial phi D a i) := by
  have hcoord : Measurable (fun R : Matrix k p ℝ ↦ R a i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply a).comp measurable_id)
  exact (measurable_const.mul hcoord).mul
    (measurable_gramTestSteinComponent phi hphi D a i)

/-- Pointwise domination of a weighted singular-field coordinate by the
common first-inverse-moment majorant. -/
theorem abs_gramTestSteinComponent_le_massMajorant
    {k p : ℕ}
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (C₀ : ℝ) (hphi : ∀ M, |phi M| ≤ C₀)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) (R : Matrix (Fin k) (Fin p) ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    |gramTestSteinComponent phi D a i R| ≤
      (C₀ ^ 2 + matrixEntryAbsMass D ^ 2) *
        halfGaussianMatrixMassMajorant k p R := by
  let g := gramTestWeight phi R
  let v := steinVectorFieldValue R D a i
  let c := matrixEntryAbsMass D
  let r := rectangularSqMass R
  let t := Matrix.trace (realWishartGram R)⁻¹
  have hC₀ : 0 ≤ C₀ :=
    (abs_nonneg (phi (0 : Matrix (Fin p) (Fin p) ℝ))).trans (hphi 0)
  have hgabs : |g| ≤ C₀ := by
    simpa [g, gramTestWeight] using hphi (realWishartGram R)
  have hgsq : g ^ 2 ≤ C₀ ^ 2 := by
    rw [← sq_abs g]
    exact (sq_le_sq₀ (abs_nonneg g) hC₀).mpr hgabs
  have hv : v ^ 2 ≤ c ^ 2 * t := by
    simpa [v, c, t] using sq_steinVectorFieldValue_apply_le R D a i hM
  have hr : 0 ≤ r := by simpa [r] using rectangularSqMass_nonneg R
  have ht : 0 ≤ t := by
    simpa [t] using trace_nonsingInv_realWishartGram_nonneg R
  calc
    |gramTestSteinComponent phi D a i R| = |g * v| := by
      rfl
    _ ≤ g ^ 2 + v ^ 2 := abs_mul_le_sq_add_sq g v
    _ ≤ C₀ ^ 2 + c ^ 2 * t := add_le_add hgsq hv
    _ = C₀ ^ 2 + 0 * r + c ^ 2 * t := by ring
    _ ≤ (0 + c ^ 2 + C₀ ^ 2) * (1 + r + t) :=
      const_add_linear_le_sum_mul_majorant (by positivity)
        (sq_nonneg c) (sq_nonneg C₀) hr ht
    _ = (C₀ ^ 2 + matrixEntryAbsMass D ^ 2) *
          halfGaussianMatrixMassMajorant k p R := by
      simp only [c, r, t, halfGaussianMatrixMassMajorant]
      ring

/-- Pointwise domination of the full product-rule coordinate derivative.
Only the first inverse-Gram trace moment is used. -/
theorem abs_gramTestSteinComponentDerivative_le_massMajorant
    {k p : ℕ}
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (phi' : Matrix (Fin p) (Fin p) ℝ →
      Matrix (Fin p) (Fin p) ℝ →L[ℝ] ℝ)
    (C₀ : ℝ) (hphi : ∀ M, |phi M| ≤ C₀)
    (C₁ : ℝ) (hphi' : ∀ M, ‖phi' M‖ ≤ C₁)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) (R : Matrix (Fin k) (Fin p) ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    |gramTestSteinComponentDerivative phi phi' D a i R| ≤
      ((2 * (k : ℝ) * C₁) ^ 2 + matrixEntryAbsMass D ^ 2 +
        C₀ * ((((1 + (p : ℝ)) * matrixEntryAbsMass D) +
          1 + matrixEntryAbsMass D ^ 2))) *
        halfGaussianMatrixMassMajorant k p R := by
  let g := gramTestWeight phi R
  let dg := gramTestWeightDerivative phi' R (Matrix.single a i 1)
  let v := steinVectorFieldValue R D a i
  let ell := steinVectorFieldLinearization R D (Matrix.single a i 1) a i
  let A := 2 * (k : ℝ) * C₁
  let c := matrixEntryAbsMass D
  let L := ((1 + (p : ℝ)) * c) + 1 + c ^ 2
  let r := rectangularSqMass R
  let t := Matrix.trace (realWishartGram R)⁻¹
  have hC₀ : 0 ≤ C₀ :=
    (abs_nonneg (phi (0 : Matrix (Fin p) (Fin p) ℝ))).trans (hphi 0)
  have hC₁ : 0 ≤ C₁ :=
    (norm_nonneg (phi' (0 : Matrix (Fin p) (Fin p) ℝ))).trans (hphi' 0)
  have hc : 0 ≤ c := by
    simpa [c] using matrixEntryAbsMass_nonneg D
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hgabs : |g| ≤ C₀ := by
    simpa [g, gramTestWeight] using hphi (realWishartGram R)
  have hdg : dg ^ 2 ≤ A ^ 2 * r := by
    simpa [dg, A, r] using
      sq_gramTestWeightDerivative_single_le phi' C₁ hphi' R a i
  have hv : v ^ 2 ≤ c ^ 2 * t := by
    simpa [v, c, t] using sq_steinVectorFieldValue_apply_le R D a i hM
  have hell : |ell| ≤ L * t := by
    simpa [ell, L, c, t] using
      abs_steinVectorFieldLinearization_single_same_le R D a i hM
  have hgel : |g * ell| ≤ C₀ * (L * t) := by
    rw [abs_mul]
    exact mul_le_mul hgabs hell (abs_nonneg ell) hC₀
  have hr : 0 ≤ r := by simpa [r] using rectangularSqMass_nonneg R
  have ht : 0 ≤ t := by
    simpa [t] using trace_nonsingInv_realWishartGram_nonneg R
  have hB : 0 ≤ c ^ 2 + C₀ * L := by positivity
  calc
    |gramTestSteinComponentDerivative phi phi' D a i R| =
        |dg * v + g * ell| := by rfl
    _ ≤ |dg * v| + |g * ell| := abs_add_le _ _
    _ ≤ (dg ^ 2 + v ^ 2) + C₀ * (L * t) :=
      add_le_add (abs_mul_le_sq_add_sq dg v) hgel
    _ ≤ (A ^ 2 * r + c ^ 2 * t) + C₀ * (L * t) :=
      add_le_add (add_le_add hdg hv) le_rfl
    _ = 0 + A ^ 2 * r + (c ^ 2 + C₀ * L) * t := by ring
    _ ≤ (A ^ 2 + (c ^ 2 + C₀ * L) + 0) * (1 + r + t) :=
      const_add_linear_le_sum_mul_majorant (sq_nonneg A) hB
        (by positivity) hr ht
    _ = ((2 * (k : ℝ) * C₁) ^ 2 + matrixEntryAbsMass D ^ 2 +
          C₀ * ((((1 + (p : ℝ)) * matrixEntryAbsMass D) +
            1 + matrixEntryAbsMass D ^ 2))) *
          halfGaussianMatrixMassMajorant k p R := by
      simp only [A, c, L, r, t, halfGaussianMatrixMassMajorant]
      ring

/-- Pointwise domination of the radial term in a single scalar Gaussian
integration-by-parts coordinate. -/
theorem abs_gramTestSteinComponentRadial_le_massMajorant
    {k p : ℕ}
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (C₀ : ℝ) (hphi : ∀ M, |phi M| ≤ C₀)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) (R : Matrix (Fin k) (Fin p) ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    |gramTestSteinComponentRadial phi D a i R| ≤
      (2 * C₀ * (1 + matrixEntryAbsMass D ^ 2)) *
        halfGaussianMatrixMassMajorant k p R := by
  let g := gramTestWeight phi R
  let v := steinVectorFieldValue R D a i
  let x := R a i
  let c := matrixEntryAbsMass D
  let r := rectangularSqMass R
  let t := Matrix.trace (realWishartGram R)⁻¹
  have hC₀ : 0 ≤ C₀ :=
    (abs_nonneg (phi (0 : Matrix (Fin p) (Fin p) ℝ))).trans (hphi 0)
  have hgabs : |g| ≤ C₀ := by
    simpa [g, gramTestWeight] using hphi (realWishartGram R)
  have hx : x ^ 2 ≤ r := by
    simpa [x, r] using sq_entry_le_rectangularSqMass R a i
  have hv : v ^ 2 ≤ c ^ 2 * t := by
    simpa [v, c, t] using sq_steinVectorFieldValue_apply_le R D a i hM
  have hprod : |x * v| ≤ x ^ 2 + v ^ 2 := abs_mul_le_sq_add_sq x v
  have hr : 0 ≤ r := by simpa [r] using rectangularSqMass_nonneg R
  have ht : 0 ≤ t := by
    simpa [t] using trace_nonsingInv_realWishartGram_nonneg R
  have hc : 0 ≤ c := by
    simpa [c] using matrixEntryAbsMass_nonneg D
  calc
    |gramTestSteinComponentRadial phi D a i R| =
        2 * |g| * |x * v| := by
      simp only [gramTestSteinComponentRadial, gramTestSteinComponent,
        g, v, x, abs_mul]
      norm_num
      ring
    _ ≤ 2 * C₀ * |x * v| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgabs (by positivity)) (abs_nonneg _)
    _ ≤ 2 * C₀ * (x ^ 2 + v ^ 2) := by
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ 2 * C₀ * (r + c ^ 2 * t) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hx hv) (by positivity)
    _ = 0 + (2 * C₀) * r + (2 * C₀ * c ^ 2) * t := by ring
    _ ≤ ((2 * C₀) + (2 * C₀ * c ^ 2) + 0) * (1 + r + t) :=
      const_add_linear_le_sum_mul_majorant (by positivity) (by positivity)
        (by positivity) hr ht
    _ = (2 * C₀ * (1 + matrixEntryAbsMass D ^ 2)) *
          halfGaussianMatrixMassMajorant k p R := by
      simp only [c, r, t, halfGaussianMatrixMassMajorant]
      ring

/-- Every weighted Stein-field coordinate is integrable under the numeric
half-Gaussian matrix law at the sharp first inverse-moment threshold. -/
theorem integrable_gramTestSteinComponent_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 1 < k)
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ) (hphiCont : Continuous phi)
    (C₀ : ℝ) (hphi : ∀ M, |phi M| ≤ C₀)
    (D : Matrix (Fin p) (Fin p) ℝ) (a : Fin k) (i : Fin p) :
    Integrable (gramTestSteinComponent phi D a i)
      (halfGaussianMatrix k p) := by
  apply integrable_of_abs_le_const_mul_halfGaussianMatrixMassMajorant
    hgap (measurable_gramTestSteinComponent phi hphiCont D a i).aestronglyMeasurable
    (C₀ ^ 2 + matrixEntryAbsMass D ^ 2)
  filter_upwards [ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (by omega)]
    with R hR
  exact abs_gramTestSteinComponent_le_massMajorant
    phi C₀ hphi D a i R hR

/-- Every explicit product-rule coordinate derivative is integrable under
the numeric half-Gaussian matrix law. -/
theorem integrable_gramTestSteinComponentDerivative_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 1 < k)
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ) (hphiCont : Continuous phi)
    (phi' : Matrix (Fin p) (Fin p) ℝ →
      Matrix (Fin p) (Fin p) ℝ →L[ℝ] ℝ)
    (hphi'Cont : Continuous phi')
    (C₀ : ℝ) (hphi : ∀ M, |phi M| ≤ C₀)
    (C₁ : ℝ) (hphi' : ∀ M, ‖phi' M‖ ≤ C₁)
    (D : Matrix (Fin p) (Fin p) ℝ) (a : Fin k) (i : Fin p) :
    Integrable (gramTestSteinComponentDerivative phi phi' D a i)
      (halfGaussianMatrix k p) := by
  apply integrable_of_abs_le_const_mul_halfGaussianMatrixMassMajorant
    hgap
    (measurable_gramTestSteinComponentDerivative
      phi hphiCont phi' hphi'Cont D a i).aestronglyMeasurable
    ((2 * (k : ℝ) * C₁) ^ 2 + matrixEntryAbsMass D ^ 2 +
      C₀ * ((((1 + (p : ℝ)) * matrixEntryAbsMass D) +
        1 + matrixEntryAbsMass D ^ 2)))
  filter_upwards [ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (by omega)]
    with R hR
  exact abs_gramTestSteinComponentDerivative_le_massMajorant
    phi phi' C₀ hphi C₁ hphi' D a i R hR

/-- Every radial coordinate term is integrable under the numeric
half-Gaussian matrix law. -/
theorem integrable_gramTestSteinComponentRadial_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 1 < k)
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ) (hphiCont : Continuous phi)
    (C₀ : ℝ) (hphi : ∀ M, |phi M| ≤ C₀)
    (D : Matrix (Fin p) (Fin p) ℝ) (a : Fin k) (i : Fin p) :
    Integrable (gramTestSteinComponentRadial phi D a i)
      (halfGaussianMatrix k p) := by
  apply integrable_of_abs_le_const_mul_halfGaussianMatrixMassMajorant
    hgap (measurable_gramTestSteinComponentRadial
      phi hphiCont D a i).aestronglyMeasurable
    (2 * C₀ * (1 + matrixEntryAbsMass D ^ 2))
  filter_upwards [ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (by omega)]
    with R hR
  exact abs_gramTestSteinComponentRadial_le_massMajorant
    phi C₀ hphi D a i R hR

/-- Exact transport of all three componentwise integrability families from
the numeric matrix law to the flattened scalar Gaussian product consumed by
`preservedScore_halfGaussianMatrix_of_flattenedSteinFamilies`. -/
theorem integrable_flattenedGramTestSteinComponent_families
    {k p n : ℕ} (hdim : n + 1 = k * p) (hgap : p + 1 < k)
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ) (hphiCont : Continuous phi)
    (phi' : Matrix (Fin p) (Fin p) ℝ →
      Matrix (Fin p) (Fin p) ℝ →L[ℝ] ℝ)
    (hphi'Cont : Continuous phi')
    (C₀ : ℝ) (hphi : ∀ M, |phi M| ≤ C₀)
    (C₁ : ℝ) (hphi' : ∀ M, ‖phi' M‖ ≤ C₁)
    (D : Matrix (Fin p) (Fin p) ℝ) :
    (∀ q, Integrable
        (flattenedWeightedSteinComponent hdim (gramTestWeight phi) D q)
        (halfGaussianPi (n + 1))) ∧
      (∀ q, Integrable
        (flattenedWeightedSteinComponentDerivative hdim (gramTestWeight phi)
          (fun R ↦ gramTestWeightDerivative phi' R) D q)
        (halfGaussianPi (n + 1))) ∧
      (∀ q, Integrable
        (fun x ↦ 2 * x q * flattenedWeightedSteinComponent
          hdim (gramTestWeight phi) D q x)
        (halfGaussianPi (n + 1))) := by
  let e := flatSuccMatrixMeasurableEquiv hdim
  have hmp : MeasurePreserving e (halfGaussianPi (n + 1))
      (halfGaussianMatrix k p) :=
    measurePreserving_flatSuccMatrixMeasurableEquiv hdim
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm := integrable_gramTestSteinComponent_halfGaussianMatrix
      hgap phi hphiCont C₀ hphi D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun x ↦ by
      rfl)
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm := integrable_gramTestSteinComponentDerivative_halfGaussianMatrix
      hgap phi hphiCont phi' hphi'Cont C₀ hphi C₁ hphi' D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun x ↦ by
      rfl)
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm := integrable_gramTestSteinComponentRadial_halfGaussianMatrix
      hgap phi hphiCont C₀ hphi D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun x ↦ by
      change 2 * (flatSuccMatrixMeasurableEquiv hdim x) a i *
          (gramTestWeight phi (flatSuccMatrixMeasurableEquiv hdim x) *
            steinVectorFieldValue (flatSuccMatrixMeasurableEquiv hdim x) D a i) =
        2 * x q *
          (gramTestWeight phi (flatSuccMatrixMeasurableEquiv hdim x) *
            steinVectorFieldValue (flatSuccMatrixMeasurableEquiv hdim x) D a i)
      rw [show (flatSuccMatrixMeasurableEquiv hdim x) a i = x q by
        simpa [a, i] using flatSuccMatrix_apply_flatCoordinatePair hdim x q])

end Wishart

end

end LogdetLean.GramHafnian
