import LogdetLean.NormalizedGram
import Mathlib.Tactic
/-!
# Determinants under finite column mixing

The pure matching coupling is a block-triangular linear transformation of
independent Gaussian columns.  This file proves the required deterministic
identity for an arbitrary finite column-mixing matrix.  It is independent of
Gaussianity and will also be reusable for larger fixed blocks.
-/

namespace LogdetLean.Coherence

noncomputable section

open scoped BigOperators

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Right multiplication of a finite vector family by a scalar matrix. -/
def mixColumnFamily (T : Matrix ι ι ℝ) (v : ι → E) : ι → E :=
  fun j ↦ ∑ i, T i j • v i

/-- The Gram matrix of a mixed family is `Tᴴ Gram(v) T`. -/
theorem gram_mixColumnFamily (T : Matrix ι ι ℝ) (v : ι → E) :
    Matrix.gram ℝ (mixColumnFamily T v) =
      T.conjTranspose * Matrix.gram ℝ v * T := by
  ext j k
  change
    inner ℝ (∑ a, T a j • v a) (∑ b, T b k • v b) =
      ∑ a, (∑ b, T b j * inner ℝ (v b) (v a)) * T a k
  calc
    inner ℝ (∑ a, T a j • v a) (∑ b, T b k • v b) =
      ∑ a, ∑ b, T a j * (T b k * inner ℝ (v a) (v b)) := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [real_inner_smul_left, inner_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      rw [real_inner_smul_right]
    _ = ∑ a, (∑ b, T b j * inner ℝ (v b) (v a)) * T a k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _hb
      rw [real_inner_comm]
      ring

/-- Mixing multiplies the unnormalized Gram determinant by `det(T)^2`. -/
theorem det_gram_mixColumnFamily (T : Matrix ι ι ℝ) (v : ι → E) :
    (Matrix.gram ℝ (mixColumnFamily T v)).det =
      T.det ^ 2 * (Matrix.gram ℝ v).det := by
  rw [gram_mixColumnFamily, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]
  simp only [starRingEnd_apply, star_id_of_comm]
  ring

/-- Exact normalized-Gram determinant identity under an arbitrary invertible
column mixing.  The squared determinant is the unnormalized volume change;
the product of column norms is the Pearson normalization change. -/
theorem det_normalizedGram_mixColumnFamily
    (T : Matrix ι ι ℝ) (v : ι → E)
    (hv : ∀ i, v i ≠ 0)
    (hTv : ∀ i, mixColumnFamily T v i ≠ 0) :
    (normalizedGram (mixColumnFamily T v)).det =
      T.det ^ 2 * (normalizedGram v).det *
        (∏ i, ‖v i‖ ^ 2) /
          (∏ i, ‖mixColumnFamily T v i‖ ^ 2) := by
  let Nv : ℝ := ∏ i, ‖v i‖ ^ 2
  let NTv : ℝ := ∏ i, ‖mixColumnFamily T v i‖ ^ 2
  have hNv : Nv ≠ 0 := by
    dsimp [Nv]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _hi
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv i))
  have hNTv : NTv ≠ 0 := by
    dsimp [NTv]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _hi
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hTv i))
  rw [det_normalizedGram, det_normalizedGram,
    det_gram_mixColumnFamily]
  change T.det ^ 2 * (Matrix.gram ℝ v).det / NTv =
    T.det ^ 2 * ((Matrix.gram ℝ v).det / Nv) * Nv / NTv
  field_simp [hNv, hNTv]

end

end LogdetLean.Coherence
