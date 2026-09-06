import LogdetLean.GramHafnian.RankTwoGaussianTransport
import LogdetLean.GramHafnian.RankTwoOuterBeta
import Mathlib.Probability.Distributions.Gaussian.Fernique
/-!
# Integrability of the rank-two Gaussian polynomial

This supplies the literal Fubini hypothesis for the fourth Gram-hafnian
moment.  It is separated from the exact conditional calculation so that the
measure-theoretic rearrangement has an independently audited endpoint.
-/

open scoped ENNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Module

namespace LogdetLean.GramHafnian

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every natural power of the rank-two bilinear form in four independent
standard Gaussian vectors is integrable. -/
theorem integrable_innerRankTwoBilinear_pow_stdGaussian_prod_prod (m : ℕ) :
    Integrable (fun w : (E × E) × (E × E) ↦
      innerRankTwoBilinear w.1.1 w.1.2 w.2 ^ m)
      (((stdGaussian E).prod (stdGaussian E)).prod
        ((stdGaussian E).prod (stdGaussian E))) := by
  have hnorm : Integrable (fun x : E ↦ ‖x‖ ^ m) (stdGaussian E) := by
    simpa only [id_eq] using
      (ProbabilityTheory.IsGaussian.memLp_id (stdGaussian E) (m : ℝ≥0∞)
        (by simp)).integrable_norm_pow'
  have hpair : Integrable (fun w : E × E ↦ ‖w.1‖ ^ m * ‖w.2‖ ^ m)
      ((stdGaussian E).prod (stdGaussian E)) :=
    hnorm.mul_prod hnorm
  have hfour : Integrable (fun w : (E × E) × (E × E) ↦
      (‖w.1.1‖ ^ m * ‖w.1.2‖ ^ m) *
        (‖w.2.1‖ ^ m * ‖w.2.2‖ ^ m))
      (((stdGaussian E).prod (stdGaussian E)).prod
        ((stdGaussian E).prod (stdGaussian E))) :=
    hpair.mul_prod hpair
  apply (hfour.const_mul ((2 : ℝ) ^ m)).mono'
  · unfold innerRankTwoBilinear
    fun_prop
  · filter_upwards [] with w
    have hbase :
        ‖innerRankTwoBilinear w.1.1 w.1.2 w.2‖ ≤
          2 * (‖w.1.1‖ * ‖w.1.2‖ * ‖w.2.1‖ * ‖w.2.2‖) := by
      unfold innerRankTwoBilinear
      calc
        ‖inner ℝ w.1.1 w.2.1 * inner ℝ w.1.2 w.2.2 +
            inner ℝ w.1.1 w.2.2 * inner ℝ w.1.2 w.2.1‖ ≤
            ‖inner ℝ w.1.1 w.2.1 * inner ℝ w.1.2 w.2.2‖ +
              ‖inner ℝ w.1.1 w.2.2 * inner ℝ w.1.2 w.2.1‖ :=
                norm_add_le _ _
        _ ≤ (‖w.1.1‖ * ‖w.2.1‖) * (‖w.1.2‖ * ‖w.2.2‖) +
              (‖w.1.1‖ * ‖w.2.2‖) * (‖w.1.2‖ * ‖w.2.1‖) := by
          simp only [norm_mul]
          exact add_le_add
            (mul_le_mul (norm_inner_le_norm w.1.1 w.2.1)
              (norm_inner_le_norm w.1.2 w.2.2) (norm_nonneg _) (by positivity))
            (mul_le_mul (norm_inner_le_norm w.1.1 w.2.2)
              (norm_inner_le_norm w.1.2 w.2.1) (norm_nonneg _) (by positivity))
        _ = 2 * (‖w.1.1‖ * ‖w.1.2‖ * ‖w.2.1‖ * ‖w.2.2‖) := by ring
    calc
      ‖innerRankTwoBilinear w.1.1 w.1.2 w.2 ^ m‖ =
          ‖innerRankTwoBilinear w.1.1 w.1.2 w.2‖ ^ m := norm_pow _ _
      _ ≤ (2 * (‖w.1.1‖ * ‖w.1.2‖ * ‖w.2.1‖ * ‖w.2.2‖)) ^ m := by
        exact pow_le_pow_left₀ (norm_nonneg _) hbase m
      _ = (2 : ℝ) ^ m *
          ((‖w.1.1‖ ^ m * ‖w.1.2‖ ^ m) *
            (‖w.2.1‖ ^ m * ‖w.2.2‖ ^ m)) := by
        simp only [mul_pow]
        ring

/-- Every monomial occurring in the conditional squared-binomial expansion
is integrable under the outer Gaussian pair.  We deliberately derive this
from the already-proved, strictly positive exact integral: this keeps the
measure-theoretic assembly independent of a second ad hoc domination
argument. -/
theorem integrable_innerMonomial_gaussianProduct
    (k n j : ℕ) (hdim : finrank ℝ E = k) (hk : 2 ≤ k) (hj : j ≤ n) :
    Integrable (fun z : E × E ↦
      (‖z.1‖ ^ 2 * ‖z.2‖ ^ 2) ^ (n - j) *
        (inner ℝ z.1 z.2) ^ (2 * j))
      ((stdGaussian E).prod (stdGaussian E)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_innerMonomial_gaussianProduct (E := E) k n j hdim hk hj]
  exact (mul_pos
    (sq_pos_of_pos (dimensionProduct_pos k n (by omega)))
    (pochhammerRatio_pos k j (by omega))).ne'

end

end LogdetLean.GramHafnian
