import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GaussianIBP
import LogdetLean.WishartSequentialKernel
/-!
# Inverse-determinant integrability for real Gaussian Gram matrices

The exact Bartlett--Mellin transform already proved in
`WishartSequentialKernel` is nonzero at Mellin exponent `-1` precisely beyond
the first inverse-Wishart threshold.  Since mathlib defines a nonintegrable
Bochner integral to be zero, this nonzero evaluation itself certifies
integrability, without importing a Wishart density formula.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Positivity of one diagonal Bartlett transform at exponent `-1` and zero
Laplace tilt. -/
theorem wishartDiagonalStageTransform_neg_one_zero_pos
    {k n : ℕ} (hk : 0 < k) (hnk : n < k)
    (hshape : 0 < (((k - n : ℕ) : ℝ) / 2) - 1) :
    0 < wishartDiagonalStageTransform k n (-1) 0 := by
  unfold wishartDiagonalStageTransform
  have hbase : 0 < (((k - n : ℕ) : ℝ) / 2) := by
    have : 0 < k - n := Nat.sub_pos_of_lt hnk
    positivity
  have hkreal : 0 < (k : ℝ) / 2 := by positivity
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hGshape : 0 < Real.Gamma ((((k - n : ℕ) : ℝ) / 2) + (-1)) := by
    apply Real.Gamma_pos_of_pos
    linarith
  have hGbase : 0 < Real.Gamma (((k - n : ℕ) : ℝ) / 2) :=
    Real.Gamma_pos_of_pos hbase
  have hp₁ : 0 < (1 / 2 : ℝ) ^ ((k : ℝ) / 2) :=
    Real.rpow_pos_of_pos hhalf _
  have hp₂ : 0 < ((1 / 2 : ℝ) + 0) ^ ((k : ℝ) / 2 + (-1)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  positivity

/-- At `k > p+1`, the reciprocal determinant of a `p`-column standard
Gaussian Gram matrix is integrable.  The columns are represented by the
right-nested product used by the proved Bartlett decomposition. -/
theorem integrable_nestedGaussianWishartKernel_neg_one_zero
    {k p : ℕ} (hk : 0 < k) (hp : p ≤ k) (hgap : p + 1 < k) :
    Integrable
      (nestedGaussianWishartKernel
        (E := EuclideanSpace ℝ (Fin k)) (-1) (fun _ ↦ 0) p)
      (nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin k))) p) := by
  have ht : ∀ n < p,
      0 < (((k - n : ℕ) : ℝ) / 2) + (-1) := by
    intro n hn
    have hnk : n < k := lt_of_lt_of_le hn hp
    have hnat : 3 ≤ k - n := by omega
    have hcast : (3 : ℝ) ≤ ((k - n : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hrate : ∀ n < p, 0 < (1 / 2 : ℝ) + (0 : ℝ) := by
    intro _ _
    norm_num
  have heval := integral_nestedGaussianWishartKernel_eq_diagonal
    hk hp (fun _ ↦ (0 : ℝ)) ht hrate
  have hprodPos : 0 <
      ∏ n ∈ Finset.range p,
        wishartDiagonalStageTransform k n (-1) 0 := by
    apply Finset.prod_pos
    intro n hn
    have hnp : n < p := Finset.mem_range.mp hn
    have hnk : n < k := lt_of_lt_of_le hnp hp
    exact wishartDiagonalStageTransform_neg_one_zero_pos hk hnk (by
      linarith [ht n hnp])
  apply Integrable.of_integral_ne_zero
  rw [heval]
  exact hprodPos.ne'

end Wishart

end

end LogdetLean.GramHafnian
