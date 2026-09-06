import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FixedHScoreIntegrability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# Coordinate bounds for the singular inverse-Gram Stein field

This file isolates the deterministic estimates needed to justify Gaussian
integration by parts for

`V(R) = (1/2) R (RᵀR)⁻¹ D`.

At full column rank every same-coordinate derivative of `V` is dominated by
a fixed multiple of `trace ((RᵀR)⁻¹)`.  Thus only the first inverse-Wishart
moment is required.
-/

open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k p : Type*} [Fintype k] [Fintype p]
  [DecidableEq k] [DecidableEq p]

/-- The inverse lift `R (RᵀR)⁻¹` has Gram matrix `(RᵀR)⁻¹`. -/
theorem transpose_inverseLift_mul_inverseLift
    (R : Matrix k p ℝ) (hM : IsUnit (realWishartGram R).det) :
    (R * (realWishartGram R)⁻¹).transpose *
        (R * (realWishartGram R)⁻¹) =
      (realWishartGram R)⁻¹ := by
  rw [Matrix.transpose_mul, (realWishartGram_inv_isSymm R).eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc R.transpose R (realWishartGram R)⁻¹]
  change (realWishartGram R)⁻¹ *
      (realWishartGram R * (realWishartGram R)⁻¹) = _
  rw [← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]

/-- Every coordinate square of `R (RᵀR)⁻¹` is bounded by the inverse-Gram
trace. -/
theorem sq_inverseLift_apply_le_trace
    (R : Matrix k p ℝ) (a : k) (i : p)
    (hM : IsUnit (realWishartGram R).det) :
    (R * (realWishartGram R)⁻¹) a i ^ 2 ≤
      Matrix.trace (realWishartGram R)⁻¹ := by
  let U := R * (realWishartGram R)⁻¹
  have hgram : U.transpose * U = (realWishartGram R)⁻¹ := by
    simpa [U] using transpose_inverseLift_mul_inverseLift R hM
  have hsingle : U a i ^ 2 ≤ ∑ b, U b i ^ 2 := by
    exact Finset.single_le_sum (fun b _ ↦ sq_nonneg (U b i))
      (Finset.mem_univ a)
  have hdiag : (∑ b, U b i ^ 2) = (realWishartGram R)⁻¹ i i := by
    have := congrArg (fun A : Matrix p p ℝ ↦ A i i) hgram
    simpa [Matrix.mul_apply, pow_two] using this
  calc
    U a i ^ 2 ≤ ∑ b, U b i ^ 2 := hsingle
    _ = (realWishartGram R)⁻¹ i i := hdiag
    _ ≤ |(realWishartGram R)⁻¹ i i| := le_abs_self _
    _ ≤ Matrix.trace (realWishartGram R)⁻¹ :=
      abs_apply_le_trace_of_posSemidef
        (realWishartGram R)⁻¹ (realWishartGram_inv_posSemidef R) i i

/-- A row of the inverse lift has squared mass at most the inverse-Gram
trace. -/
theorem row_sqMass_inverseLift_le_trace
    (R : Matrix k p ℝ) (a : k)
    (hM : IsUnit (realWishartGram R).det) :
    (∑ i, (R * (realWishartGram R)⁻¹) a i ^ 2) ≤
      Matrix.trace (realWishartGram R)⁻¹ := by
  let U := R * (realWishartGram R)⁻¹
  have hgram : U.transpose * U = (realWishartGram R)⁻¹ := by
    simpa [U] using transpose_inverseLift_mul_inverseLift R hM
  calc
    (∑ i, U a i ^ 2) ≤ ∑ i, ∑ b, U b i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.single_le_sum (fun b _ ↦ sq_nonneg (U b i))
        (Finset.mem_univ a)
    _ = Matrix.trace (U.transpose * U) := by
      simp [Matrix.trace, Matrix.mul_apply, pow_two]
    _ = Matrix.trace (realWishartGram R)⁻¹ := by rw [hgram]

/-- Multiplying the inverse lift by a fixed matrix costs only the square of
the entrywise `ℓ¹` mass of that matrix. -/
theorem sq_inverseLift_mul_apply_le
    (R : Matrix k p ℝ) (D : Matrix p p ℝ) (a : k) (i : p)
    (hM : IsUnit (realWishartGram R).det) :
    (R * (realWishartGram R)⁻¹ * D) a i ^ 2 ≤
      matrixEntryAbsMass D ^ 2 *
        Matrix.trace (realWishartGram R)⁻¹ := by
  let U := R * (realWishartGram R)⁻¹
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : p ↦ U a j) (fun j : p ↦ D j i)
  have hU := row_sqMass_inverseLift_le_trace R a hM
  have hDcol : (∑ j, D j i ^ 2) ≤ matrixEntryAbsMass D ^ 2 := by
    calc
      (∑ j, D j i ^ 2) = ∑ j, |D j i| ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [sq_abs]
      _ ≤ (∑ j, |D j i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)
      _ ≤ matrixEntryAbsMass D ^ 2 := by
        have hcol : (∑ j, |D j i|) ≤ matrixEntryAbsMass D := by
          unfold matrixEntryAbsMass
          apply Finset.sum_le_sum
          intro j _
          exact Finset.single_le_sum (fun l _ ↦ abs_nonneg (D j l))
            (Finset.mem_univ i)
        exact (sq_le_sq₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
          (matrixEntryAbsMass_nonneg D)).2 hcol
  calc
    (R * (realWishartGram R)⁻¹ * D) a i ^ 2 =
        (∑ j, U a j * D j i) ^ 2 := by
      simp [U, Matrix.mul_apply, Matrix.mul_assoc]
    _ ≤ (∑ j, U a j ^ 2) * ∑ j, D j i ^ 2 := hcs
    _ ≤ Matrix.trace (realWishartGram R)⁻¹ *
        matrixEntryAbsMass D ^ 2 :=
      mul_le_mul hU hDcol (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        (realWishartGram_inv_posSemidef R).trace_nonneg
    _ = matrixEntryAbsMass D ^ 2 *
        Matrix.trace (realWishartGram R)⁻¹ := by ring

/-- Coordinate squares of the Stein field itself are controlled by one
inverse-Gram trace. -/
theorem sq_steinVectorFieldValue_apply_le
    (R : Matrix k p ℝ) (D : Matrix p p ℝ) (a : k) (i : p)
    (hM : IsUnit (realWishartGram R).det) :
    steinVectorFieldValue R D a i ^ 2 ≤
      matrixEntryAbsMass D ^ 2 *
        Matrix.trace (realWishartGram R)⁻¹ := by
  have h := sq_inverseLift_mul_apply_le R D a i hM
  have hnonneg : 0 ≤ matrixEntryAbsMass D ^ 2 *
      Matrix.trace (realWishartGram R)⁻¹ :=
    mul_nonneg (sq_nonneg _) (realWishartGram_inv_posSemidef R).trace_nonneg
  simp only [steinVectorFieldValue, Matrix.smul_apply, smul_eq_mul]
  nlinarith [sq_nonneg ((R * (realWishartGram R)⁻¹ * D) a i)]

/-- Entrywise multiplication by a fixed matrix is controlled by its
entrywise mass and the trace of a positive-semidefinite matrix. -/
theorem abs_mul_apply_le_matrixEntryAbsMass_mul_trace
    (A D : Matrix p p ℝ) (hA : A.PosSemidef) (i j : p) :
    |(A * D) i j| ≤ matrixEntryAbsMass D * Matrix.trace A := by
  calc
    |(A * D) i j| = |∑ l, A i l * D l j| := by
      rw [Matrix.mul_apply]
    _ ≤ ∑ l, |A i l * D l j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, Matrix.trace A * |D l j| := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_apply_le_trace_of_posSemidef A hA i l) (abs_nonneg _)
    _ = Matrix.trace A * ∑ l, |D l j| := by rw [Finset.mul_sum]
    _ ≤ Matrix.trace A * matrixEntryAbsMass D := by
      apply mul_le_mul_of_nonneg_left _ hA.trace_nonneg
      unfold matrixEntryAbsMass
      apply Finset.sum_le_sum
      intro l _
      exact Finset.single_le_sum (fun q _ ↦ abs_nonneg (D l q))
        (Finset.mem_univ j)
    _ = matrixEntryAbsMass D * Matrix.trace A := by ring

/-- The diagonal of the inverse-Gram projection is bounded by the column
dimension. -/
theorem abs_inverseGram_projection_diag_le_card
    (R : Matrix k p ℝ) (a : k)
    (hM : IsUnit (realWishartGram R).det) :
    |(R * (realWishartGram R)⁻¹ * R.transpose) a a| ≤
      (Fintype.card p : ℝ) := by
  have hP : (R * (realWishartGram R)⁻¹ * R.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (realWishartGram_inv_posSemidef R).mul_mul_conjTranspose_same R
  calc
    |(R * (realWishartGram R)⁻¹ * R.transpose) a a| ≤
        Matrix.trace (R * (realWishartGram R)⁻¹ * R.transpose) :=
      abs_apply_le_trace_of_posSemidef _ hP a a
    _ = (Fintype.card p : ℝ) := trace_inverseGram_projection R hM

@[simp] theorem single_mul_apply_same
    (B : Matrix p p ℝ) (a : k) (i : p) :
    (Matrix.single a i (1 : ℝ) * B) a i = B i i := by
  simp [Matrix.mul_apply, Matrix.single_apply]

@[simp] theorem mul_single_transpose_mul_apply_same
    (U W : Matrix k p ℝ) (a : k) (i : p) :
    (U * (Matrix.single a i (1 : ℝ)).transpose * W) a i =
      U a i * W a i := by
  rw [Matrix.mul_apply]
  have hinner (x : k) :
      (U * (Matrix.single a i (1 : ℝ)).transpose) a x =
        if x = a then U a i else 0 := by
    by_cases hx : x = a
    · subst x
      simp [Matrix.mul_apply, Matrix.single_apply]
    · have hax : a ≠ x := fun h ↦ hx h.symm
      simp [Matrix.mul_apply, Matrix.single_apply, hx, hax]
  simp_rw [hinner]
  simp

@[simp] theorem mul_single_mul_apply_same
    (P : Matrix k k ℝ) (B : Matrix p p ℝ) (a : k) (i : p) :
    (P * Matrix.single a i (1 : ℝ) * B) a i = P a a * B i i := by
  rw [Matrix.mul_apply]
  have hinner (x : p) :
      (P * Matrix.single a i (1 : ℝ)) a x =
        if x = i then P a a else 0 := by
    by_cases hx : x = i
    · subst x
      simp [Matrix.mul_apply, Matrix.single_apply]
    · have hix : i ≠ x := fun h ↦ hx h.symm
      simp [Matrix.mul_apply, Matrix.single_apply, hx, hix]
  simp_rw [hinner]
  simp

/-- Exact same-coordinate formula for the derivative of the inverse-Gram
Stein field. -/
theorem two_mul_steinVectorFieldLinearization_single_same
    (R : Matrix k p ℝ) (D : Matrix p p ℝ) (a : k) (i : p) :
    2 * steinVectorFieldLinearization R D (Matrix.single a i 1) a i =
      (1 - (R * (realWishartGram R)⁻¹ * R.transpose) a a) *
          ((realWishartGram R)⁻¹ * D) i i -
        (R * (realWishartGram R)⁻¹) a i *
          (R * (realWishartGram R)⁻¹ * D) a i := by
  classical
  unfold steinVectorFieldLinearization
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    single_mul_apply_same, mul_single_transpose_mul_apply_same,
    mul_single_mul_apply_same]
  ring

/-- Every same-coordinate derivative of the singular Stein field is
dominated by one inverse-Gram trace.  The constant is deliberately crude;
only integrability matters. -/
theorem abs_steinVectorFieldLinearization_single_same_le
    (R : Matrix k p ℝ) (D : Matrix p p ℝ) (a : k) (i : p)
    (hM : IsUnit (realWishartGram R).det) :
    |steinVectorFieldLinearization R D (Matrix.single a i 1) a i| ≤
      (((1 + (Fintype.card p : ℝ)) * matrixEntryAbsMass D) +
          1 + matrixEntryAbsMass D ^ 2) *
        Matrix.trace (realWishartGram R)⁻¹ := by
  let G := (realWishartGram R)⁻¹
  let U := R * G
  let W := R * G * D
  let P := R * G * R.transpose
  let c := matrixEntryAbsMass D
  let t := Matrix.trace G
  have ht : 0 ≤ t := (realWishartGram_inv_posSemidef R).trace_nonneg
  have hc : 0 ≤ c := matrixEntryAbsMass_nonneg D
  have hp : |P a a| ≤ (Fintype.card p : ℝ) := by
    simpa [P, G] using abs_inverseGram_projection_diag_le_card R a hM
  have hGD : |(G * D) i i| ≤ c * t := by
    simpa [G, c, t] using abs_mul_apply_le_matrixEntryAbsMass_mul_trace
      G D (realWishartGram_inv_posSemidef R) i i
  have hU : U a i ^ 2 ≤ t := by
    simpa [U, G, t] using sq_inverseLift_apply_le_trace R a i hM
  have hW : W a i ^ 2 ≤ c ^ 2 * t := by
    simpa [W, U, G, c, t, Matrix.mul_assoc] using
      sq_inverseLift_mul_apply_le R D a i hM
  have hUW : |U a i * W a i| ≤ (1 + c ^ 2) * t := by
    calc
      |U a i * W a i| ≤ U a i ^ 2 + W a i ^ 2 :=
        abs_mul_le_sq_add_sq _ _
      _ ≤ t + c ^ 2 * t := add_le_add hU hW
      _ = (1 + c ^ 2) * t := by ring
  have hOneP : |1 - P a a| ≤ 1 + (Fintype.card p : ℝ) := by
    calc
      |1 - P a a| ≤ |(1 : ℝ)| + |P a a| := abs_sub _ _
      _ ≤ 1 + (Fintype.card p : ℝ) := by simpa using add_le_add_left hp 1
  have hmain :
      |(1 - P a a) * (G * D) i i - U a i * W a i| ≤
        ((1 + (Fintype.card p : ℝ)) * c + 1 + c ^ 2) * t := by
    calc
      |(1 - P a a) * (G * D) i i - U a i * W a i| ≤
          |1 - P a a| * |(G * D) i i| + |U a i * W a i| := by
        simpa [abs_mul] using
          (abs_sub_le ((1 - P a a) * (G * D) i i)
            0 (U a i * W a i))
      _ ≤ (1 + (Fintype.card p : ℝ)) * (c * t) +
          (1 + c ^ 2) * t :=
        add_le_add
          (mul_le_mul hOneP hGD (abs_nonneg _) (by positivity)) hUW
      _ = ((1 + (Fintype.card p : ℝ)) * c + 1 + c ^ 2) * t := by ring
  have hexact := two_mul_steinVectorFieldLinearization_single_same
    R D a i
  have htwo :
      |2 * steinVectorFieldLinearization R D (Matrix.single a i 1) a i| ≤
        ((1 + (Fintype.card p : ℝ)) * c + 1 + c ^ 2) * t := by
    rw [hexact]
    exact hmain
  have hnonneg :
      0 ≤ ((1 + (Fintype.card p : ℝ)) * c + 1 + c ^ 2) * t := by
    positivity
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htwo
  dsimp [c, t] at htwo ⊢
  nlinarith

end Wishart

end

end LogdetLean.GramHafnian
