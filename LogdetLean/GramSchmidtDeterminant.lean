import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import LogdetLean.NormalizedGram
/-!
# Gram determinants and Gram--Schmidt residuals

This file proves the deterministic QR/Gram--Schmidt identity used in the
Gaussian-to-Beta bridge.  It contains no probability.

Mathematical provenance: this formal proof follows Rouault (2005),
Section 2.1, equations (4)--(6) and (9)--(10), printed pp. 4--5.  Rouault's
identity is reproved from mathlib's Gram--Schmidt and determinant libraries.
See `PROVENANCE.md`; no novelty is claimed for the underlying identity.
-/

namespace LogdetLean

set_option maxHeartbeats 800000

open scoped BigOperators
open Finset Submodule Module

noncomputable section

open InnerProductSpace

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [WellFoundedLT ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype ι] in
/-- Gram--Schmidt commutes with a linear isometry. -/
lemma LinearIsometry.map_gramSchmidt {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E →ₗᵢ[ℝ] F) (v : ι → E) (i : ι) :
    f (gramSchmidt ℝ v i) = gramSchmidt ℝ (f ∘ v) i := by
  apply (wellFounded_lt (α := ι)).induction i
  intro i ih
  rw [gramSchmidt_def, gramSchmidt_def]
  simp only [map_sub, map_sum, starProjection_singleton, map_smul,
    Function.comp_apply]
  apply congrArg (fun z ↦ f (v i) - z)
  apply Finset.sum_congr rfl
  intro j hj
  rw [← ih j (Finset.mem_Iio.mp hj), f.inner_map_map, f.norm_map]

omit [Fintype ι] in
/-- The diagonal coefficient in Gram--Schmidt is the norm of the residual. -/
lemma inner_gramSchmidtNormed_self (v : ι → E) (i : ι)
    (hi : gramSchmidt ℝ v i ≠ 0) :
    ⟪gramSchmidtNormed ℝ v i, v i⟫_ℝ = ‖gramSchmidt ℝ v i‖ := by
  rw [gramSchmidtNormed, inner_smul_left]
  rw [gramSchmidt_def' ℝ v i]
  simp only [inner_add_right, inner_sum, starProjection_singleton,
    inner_smul_right]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hsum :
      ∑ j ∈ Iio i,
          (⟪gramSchmidt ℝ v j, v i⟫_ℝ / ‖gramSchmidt ℝ v j‖ ^ 2) *
            ⟪gramSchmidt ℝ v i, gramSchmidt ℝ v j⟫_ℝ = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [gramSchmidt_orthogonal ℝ v]
    · ring
    · exact ne_of_gt (Finset.mem_Iio.mp hj)
  rw [hsum, add_zero, real_inner_self_eq_norm_sq]
  have hn : ‖gramSchmidt ℝ v i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
  simp only [starRingEnd_apply, star_trivial]
  field_simp

/-- If the ambient dimension equals the number of vectors, the Gram
determinant is the product of squared Gram--Schmidt residual lengths. -/
theorem det_gram_eq_prod_norm_gramSchmidt_sq_of_finrank_eq
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = Fintype.card ι)
    (v : ι → E) (hv : LinearIndependent ℝ v) :
    (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  classical
  let b : OrthonormalBasis ι ℝ E := gramSchmidtOrthonormalBasis hdim v
  let M : Matrix ι ι ℝ := Matrix.of fun i j ↦ b.repr (v j) i
  have hgram : Matrix.gram ℝ v = M.conjTranspose * M := by
    simpa [M] using (Matrix.gram_eq_conjTranspose_mul b v)
  have hdetM : M.det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
    calc
      M.det = b.toBasis.det v := rfl
      _ = ∏ i, ⟪b i, v i⟫_ℝ :=
        gramSchmidtOrthonormalBasis_det hdim v
      _ = ∏ i, ‖gramSchmidt ℝ v i‖ := by
        apply Finset.prod_congr rfl
        intro i hi
        have hgs : gramSchmidt ℝ v i ≠ 0 := gramSchmidt_ne_zero i hv
        have hnormed : gramSchmidtNormed ℝ v i ≠ 0 := by
          simp [gramSchmidtNormed, hgs]
        rw [show b i = gramSchmidtNormed ℝ v i from
          gramSchmidtOrthonormalBasis_apply hdim hnormed]
        exact inner_gramSchmidtNormed_self v i hgs
  rw [hgram, Matrix.det_mul, Matrix.det_conjTranspose, hdetM]
  simp only [star_trivial]
  rw [← Finset.prod_mul_distrib]
  simp only [pow_two]

/-- The Gram determinant of any finite linearly independent family is the
product of the squared residual lengths produced by Gram--Schmidt.  The
ambient space may have larger dimension than the family. -/
theorem det_gram_eq_prod_norm_gramSchmidt_sq
    (v : ι → E) (hv : LinearIndependent ℝ v) :
    (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  classical
  let W : Submodule ℝ E := span ℝ (Set.range v)
  let w : ι → W := fun i ↦ ⟨v i, subset_span (Set.mem_range_self i)⟩
  have hw : LinearIndependent ℝ w := by
    apply LinearIndependent.of_comp W.subtype
    convert hv using 1
    ext i
    rfl
  let _ : FiniteDimensional ℝ W :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  have hdim : finrank ℝ W = Fintype.card ι := by
    simpa [W] using finrank_span_eq_card hv
  have hsquare :=
    det_gram_eq_prod_norm_gramSchmidt_sq_of_finrank_eq hdim w hw
  have hgram : Matrix.gram ℝ w = Matrix.gram ℝ v := by
    ext i j
    rfl
  rw [hgram] at hsquare
  rw [hsquare]
  apply Finset.prod_congr rfl
  intro i hi
  have hmap := LinearIsometry.map_gramSchmidt W.subtypeₗᵢ w i
  have hnorm := congrArg norm hmap
  have heq : ‖gramSchmidt ℝ w i‖ = ‖gramSchmidt ℝ v i‖ := by
    simpa [w, W, Function.comp_def] using hnorm
  rw [heq]

/-- Normalizing every column divides the Gram--Schmidt volume product by the
product of the squared original column lengths. -/
theorem det_normalizedGram_eq_prod_gramSchmidt_ratio
    (v : ι → E) (hv : LinearIndependent ℝ v) :
    (normalizedGram v).det =
      ∏ i, (‖gramSchmidt ℝ v i‖ ^ 2 / ‖v i‖ ^ 2) := by
  rw [det_normalizedGram, det_gram_eq_prod_norm_gramSchmidt_sq v hv,
    ← Finset.prod_div_distrib]

/-- The exact form used for `p` vectors in the Euclidean Gaussian residual
space of dimension `m`.  Linear independence in particular forces `p ≤ m`. -/
theorem det_normalizedGram_euclidean_eq_prod_gramSchmidt_ratio
    {m p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin m))
    (hv : LinearIndependent ℝ v) :
    (normalizedGram v).det =
      ∏ j, (‖gramSchmidt ℝ v j‖ ^ 2 / ‖v j‖ ^ 2) :=
  det_normalizedGram_eq_prod_gramSchmidt_ratio v hv

/-- For a nonempty `Fin` family, the first Gram--Schmidt factor is exactly one
after normalization. -/
theorem gramSchmidt_ratio_zero_eq_one {p : ℕ}
    (v : Fin (p + 1) → E) (hv : LinearIndependent ℝ v) :
    ‖gramSchmidt ℝ v 0‖ ^ 2 / ‖v 0‖ ^ 2 = 1 := by
  change ‖gramSchmidt ℝ v (⊥ : Fin (p + 1))‖ ^ 2 /
      ‖v (⊥ : Fin (p + 1))‖ ^ 2 = 1
  rw [InnerProductSpace.gramSchmidt_bot]
  have hv0 : v (⊥ : Fin (p + 1)) ≠ 0 := hv.ne_zero ⊥
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0))

end

end LogdetLean
