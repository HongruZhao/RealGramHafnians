import LogdetLean.GramHafnian.SymmetricGaussianHafnian.RealMain
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.CoefficientLowerBounds
import RealGramHafnians.Proofs.SharpRealConstant
/-!
# Real symmetric Gaussian endpoint for the AIHP paper

This file exposes the independent-edge real symmetric Gaussian hafnian
anticoncentration theorem used as the fixed-degree limit of the real Gaussian
Gram model.  The underlying theorem is unconditional and uses no scientific
axiom.
-/

open MeasureTheory ProbabilityTheory Set Complex Filter
open scoped BigOperators Real ENNReal NNReal Nat Topology

namespace LogdetLean.GramHafnian

noncomputable section

open SymmetricGaussianHafnian

/-- The exact coefficient in the fixed-degree real symmetric Gaussian limit. -/
def sharpRealSymmetricSmallBallCoefficient (n : ℕ) : ℝ :=
  realHafnianSmallBallCoefficient n

/-- The RMS scale of the independent-edge real symmetric Gaussian hafnian. -/
def sharpRealSymmetricHafnianRMS (n : ℕ) : ℝ := sigma n

/-- The RMS scale is the square root of the matching count. -/
theorem sharpRealSymmetricHafnianRMS_sq (n : ℕ) :
    sharpRealSymmetricHafnianRMS n ^ 2 =
      ((((2 * n - 1)‼ : ℕ) : ℝ)) := by
  simpa [sharpRealSymmetricHafnianRMS,
    oddPairingNat_eq_doubleFactorial] using sigma_sq n

private theorem realAuxiliaryGammaHalfFactorReal_odd_eq
    (r : ℕ) (hr : 2 ≤ r) :
    realAuxiliaryGammaHalfFactorReal (2 * r - 1) =
      Real.Gamma ((r : ℝ) - 1) /
        (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2)) := by
  unfold realAuxiliaryGammaHalfFactorReal
  rw [← Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  rw [hsqrt]
  have hnum : ((((2 * r - 1 : ℕ) : ℝ)) - 1) / 2 =
      (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  have hden : (((2 * r - 1 : ℕ) : ℝ)) / 2 =
      (r : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  rw [hnum, hden]
  ring

/-- The exact coefficient is the fixed-degree product appearing in the
paper. -/
theorem sharpRealSymmetricSmallBallCoefficient_eq_product
    {n : ℕ} (hn : 1 ≤ n) :
    sharpRealSymmetricSmallBallCoefficient n =
      Real.sqrt (2 / Real.pi) *
        Real.sqrt ((((2 * n - 1)‼ : ℕ) : ℝ)) *
        ∏ r ∈ Finset.Icc 2 n,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1) := by
  rw [sharpRealSymmetricSmallBallCoefficient,
    realHafnianSmallBallCoefficient_eq_gammaProduct,
    realGammaProduct_eq_paperProduct]
  rw [show sigma n = Real.sqrt ((((2 * n - 1)‼ : ℕ) : ℝ)) by
    simp [sigma, oddPairingNat_eq_doubleFactorial]]
  have hprod :
      (∏ r ∈ Finset.Icc 2 n,
        Real.Gamma ((r : ℝ) - 1) /
          (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2))) =
      ∏ r ∈ Finset.Icc 2 n,
        realAuxiliaryGammaHalfFactorReal (2 * r - 1) := by
    apply Finset.prod_congr rfl
    intro r hr
    exact (realAuxiliaryGammaHalfFactorReal_odd_eq r
      (Finset.mem_Icc.mp hr).1).symm
  rw [hprod]

/-- A simple coefficient envelope inherited from the finite Gram theorem. -/
theorem sharpRealSymmetricSmallBallCoefficient_le_sqrt_odd
    {n : ℕ} (hn : 1 ≤ n) :
    sharpRealSymmetricSmallBallCoefficient n ≤
      Real.sqrt (2 / Real.pi) *
        Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) := by
  have hcoeff : sharpRealSymmetricSmallBallCoefficient n =
      Real.sqrt (2 / Real.pi) * realElementaryKn n := by
    rw [sharpRealSymmetricSmallBallCoefficient_eq_product hn,
      realElementaryKn_eq_doubleFactorial_gammaProduct hn]
    ring
  rw [hcoeff]
  exact mul_le_mul_of_nonneg_left (realElementaryKn_le_sqrt_odd hn)
    (Real.sqrt_nonneg _)

/-- The exact real symmetric coefficient has matching polynomial bounds of
order `n^(3/8)`. -/
theorem sharpRealSymmetricSmallBallCoefficient_threeEighth_twoSided
    {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 / Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) ≤
        sharpRealSymmetricSmallBallCoefficient n ∧
      sharpRealSymmetricSmallBallCoefficient n ≤
        (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) := by
  constructor
  · simpa [sharpRealSymmetricSmallBallCoefficient] using
      SymmetricGaussianHafnian.realCoefficient_ge_sqrt_two_div_pi_mul_rpow
        n hn
  · simpa [sharpRealSymmetricSmallBallCoefficient] using
      SymmetricGaussianHafnian.realHafnianSmallBallCoefficient_le_two_div_sqrt_pi_mul_rpow
        n hn

/-- The exact normalized shifted anticoncentration conclusion for the real
symmetric Gaussian hafnian. -/
theorem sharpRealSymmetricGaussian_shiftedSmallBall
    (n : ℕ) (hn : 1 ≤ n) (z : ℝ) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    (realEdgeGaussian (Fin (2 * n)))
        {x | |realEdgeHafnian x - z| ≤
          epsilon * sharpRealSymmetricHafnianRMS n} ≤
      min 1 (ENNReal.ofReal
        (sharpRealSymmetricSmallBallCoefficient n * epsilon)) := by
  simpa [sharpRealSymmetricHafnianRMS,
    sharpRealSymmetricSmallBallCoefficient] using
    symmetricRealHafnian_shifted_smallBall n hn z epsilon hepsilon

end

end LogdetLean.GramHafnian
