import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
/-!
# A quadratic determinant bound for a small correlation prefix

The determinant has no linear off-diagonal term at the identity matrix.  This
file records a fully quantitative finite-dimensional version of that fact.
If a real square matrix has unit diagonal and all off-diagonal entries are at
most `δ` in absolute value, every nonidentity term in the Leibniz formula
contains at least two off-diagonal factors.  Consequently

`|det A - 1| ≤ q! * δ^2`.

The final theorem converts this into the corresponding local logarithmic
bound.  These are deterministic statements; no probability theory is used.
-/

namespace LogdetLean.Coherence

noncomputable section

open scoped BigOperators

private def leibnizTerm {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (σ : Equiv.Perm (Fin q)) : ℝ :=
  ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i

private lemma leibnizTerm_one {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (hdiag : ∀ i, A i i = 1) :
    leibnizTerm A 1 = 1 := by
  simp [leibnizTerm, hdiag]

private lemma abs_prod_le_sq_of_perm_ne_one
    {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (δ : ℝ)
    (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (σ : Equiv.Perm (Fin q)) (hσ : σ ≠ 1) :
    |∏ i, A (σ i) i| ≤ δ ^ 2 := by
  classical
  calc
    |∏ i, A (σ i) i| = ∏ i, |A (σ i) i| := by
      simpa using
        (Finset.abs_prod (Finset.univ : Finset (Fin q))
          (fun i ↦ A (σ i) i))
    _ = ∏ i ∈ σ.support, |A (σ i) i| := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro i _ hi
      have hfix : σ i = i := by
        simpa [Equiv.Perm.mem_support] using hi
      rw [hfix, hdiag, abs_one]
    _ ≤ ∏ _i ∈ σ.support, δ := by
      gcongr with i hi
      exact hoff (σ i) i (Equiv.Perm.mem_support.mp hi)
    _ = δ ^ σ.support.card := by simp
    _ ≤ δ ^ 2 := by
      exact pow_le_pow_of_le_one hδ0 hδ1
        (Equiv.Perm.two_le_card_support_of_ne_one hσ)

private lemma abs_leibnizTerm_le_sq_of_perm_ne_one
    {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (δ : ℝ)
    (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (σ : Equiv.Perm (Fin q)) (hσ : σ ≠ 1) :
    |leibnizTerm A σ| ≤ δ ^ 2 := by
  rw [leibnizTerm, abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs,
    Int.cast_one, one_mul]
  exact abs_prod_le_sq_of_perm_ne_one A δ hdiag hoff hδ0 hδ1 σ hσ

/-- A unit-diagonal real `q × q` matrix whose off-diagonal entries have
absolute value at most `δ ≤ 1` differs in determinant from one by at most
`q! δ²`.  The quadratic power is the trace-zero cancellation: every
nonidentity permutation moves at least two indices. -/
theorem abs_det_sub_one_le_factorial_mul_sq
    {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (δ : ℝ)
    (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    |A.det - 1| ≤ (Nat.factorial q : ℝ) * δ ^ 2 := by
  classical
  let S : Finset (Equiv.Perm (Fin q)) := Finset.univ.erase 1
  have hdet : A.det = ∑ σ, leibnizTerm A σ := by
    simpa [leibnizTerm] using Matrix.det_apply' A
  have hone : leibnizTerm A 1 = 1 := leibnizTerm_one A hdiag
  have hsum : A.det - 1 = ∑ σ ∈ S, leibnizTerm A σ := by
    rw [hdet, ← hone]
    have hmem : (1 : Equiv.Perm (Fin q)) ∈
        (Finset.univ : Finset (Equiv.Perm (Fin q))) := Finset.mem_univ _
    rw [← Finset.sum_erase_add _ _ hmem]
    simp [S]
  rw [hsum]
  calc
    |∑ σ ∈ S, leibnizTerm A σ| ≤ ∑ σ ∈ S, |leibnizTerm A σ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ ∈ S, δ ^ 2 := by
      gcongr with σ hσ
      exact abs_leibnizTerm_le_sq_of_perm_ne_one A δ hdiag hoff hδ0 hδ1 σ
        (Finset.ne_of_mem_erase hσ)
    _ = (S.card : ℝ) * δ ^ 2 := by simp
    _ ≤ (Nat.factorial q : ℝ) * δ ^ 2 := by
      gcongr
      calc
        S.card ≤ Fintype.card (Equiv.Perm (Fin q)) := Finset.card_le_univ _
        _ = Nat.factorial q := by simp [Fintype.card_perm]

/-- A scalar logarithm estimate used to pass from a determinant perturbation
to a log-determinant perturbation. -/
theorem abs_log_le_two_mul_abs_sub_one
    {x : ℝ} (hx : 0 < x) (hclose : |x - 1| ≤ (1 / 2 : ℝ)) :
    |Real.log x| ≤ 2 * |x - 1| := by
  have hxhalf : (1 / 2 : ℝ) ≤ x := by
    have hlower : -(1 / 2 : ℝ) ≤ x - 1 :=
      (neg_le_of_abs_le hclose)
    linarith
  by_cases h1 : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (sub_nonneg.mpr h1)]
    nlinarith [Real.log_le_sub_one_of_pos hx]
  · have hxle : x ≤ 1 := le_of_not_ge h1
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.le hxle
    rw [abs_of_nonpos hlog, abs_of_nonpos (sub_nonpos.mpr hxle)]
    have hinv : Real.log x ≥ 1 - x⁻¹ := Real.one_sub_inv_le_log_of_pos hx
    have hxinv : x⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀' hx]
      nlinarith
    have hfrac : x⁻¹ - 1 ≤ 2 * (1 - x) := by
      calc
        x⁻¹ - 1 = x⁻¹ * (1 - x) := by
          field_simp
        _ ≤ 2 * (1 - x) :=
          mul_le_mul_of_nonneg_right hxinv (sub_nonneg.mpr hxle)
    linarith

/-- If the determinant is positive and the deterministic quadratic remainder
is at most one half, the log determinant obeys the same quadratic estimate up
to the universal local factor two. -/
theorem abs_log_det_le_two_factorial_mul_sq
    {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (δ : ℝ)
    (hdiag : ∀ i, A i i = 1)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdet : 0 < A.det)
    (hsmall : (Nat.factorial q : ℝ) * δ ^ 2 ≤ (1 / 2 : ℝ)) :
    |Real.log A.det| ≤ 2 * (Nat.factorial q : ℝ) * δ ^ 2 := by
  have hperturb : |A.det - 1| ≤ (Nat.factorial q : ℝ) * δ ^ 2 :=
    abs_det_sub_one_le_factorial_mul_sq A δ hdiag hoff hδ0 hδ1
  have hclose : |A.det - 1| ≤ (1 / 2 : ℝ) := hperturb.trans hsmall
  calc
    |Real.log A.det| ≤ 2 * |A.det - 1| :=
      abs_log_le_two_mul_abs_sub_one hdet hclose
    _ ≤ 2 * ((Nat.factorial q : ℝ) * δ ^ 2) := by gcongr
    _ = 2 * (Nat.factorial q : ℝ) * δ ^ 2 := by ring

end

end LogdetLean.Coherence
