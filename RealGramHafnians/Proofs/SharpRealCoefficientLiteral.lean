import RealGramHafnians.Proofs.SharpRealHeadlinePackaging
/-!
# Literal paper formulas for the sharp real coefficient

The main development deliberately keeps the universal Gaussian interval
prefactor and the two Gamma products as named objects.  This file proves the
algebraic identities that put those objects into exactly the displayed form
used in the manuscript.
-/

open scoped BigOperators Real ENNReal Nat

namespace LogdetLean.GramHafnian

noncomputable section

/-- The universal real Gaussian interval prefactor in the literal
`sqrt (2 / pi)` normalization used in the paper. -/
theorem realGaussianIntervalPrefactor_eq_sqrt_two_div_pi_mul
    (rho : ℝ) :
    realGaussianIntervalPrefactor rho =
      Real.sqrt (2 / Real.pi) * rho := by
  unfold realGaussianIntervalPrefactor
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2)]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  have hsqrtTwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hsqrtTwo, hsqrtPi]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- At unit radius, multiplying the universal prefactor by a square root
produces the paper's single square-root display. -/
theorem realGaussianIntervalPrefactor_one_mul_sqrt_eq_literal
    (m : ℕ) :
    realGaussianIntervalPrefactor 1 * Real.sqrt (m : ℝ) =
      Real.sqrt (2 * (m : ℝ) / Real.pi) := by
  rw [realGaussianIntervalPrefactor_eq_sqrt_two_div_pi_mul]
  simp only [mul_one]
  calc
    Real.sqrt (2 / Real.pi) * Real.sqrt (m : ℝ) =
        Real.sqrt ((2 / Real.pi) * (m : ℝ)) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
    _ = Real.sqrt (2 * (m : ℝ) / Real.pi) := by
      congr 1
      ring

/-- Literal version of equation `(exact-B)` in the paper.  The first finite
product is indexed by `j = 0, ..., n-1`; the second is indexed by
`r = 2, ..., n`. -/
theorem sharpRealSmallBallCoefficientB_eq_literal_gamma_products
    {n k : ℕ} (hn : 1 ≤ n) (_hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    sharpRealSmallBallCoefficientB n k =
      Real.sqrt (2 / Real.pi) * realGramHafnianRMS n k *
        (∏ j ∈ Finset.range n,
          realAuxiliaryGammaHalfFactorReal (k - j)) *
        (∏ r ∈ Finset.Icc 2 n,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1)) := by
  have hnk : n ≤ k := by omega
  rw [sharpRealSmallBallCoefficientB,
    realGaussianIntervalPrefactor_eq_sqrt_two_div_pi_mul,
    sharpRealGammaCoefficientReal,
    sharpRealPhysicalGammaProductReal_eq_range hnk]
  unfold sharpRealPhysicalGammaRangeProductReal
    sharpRealOddGammaProductReal
  ring

/-- Literal version of equation `(elementary-B)` in the paper. -/
theorem sharpRealSmallBallCoefficientB_le_literal_elementary
    {n k : ℕ} (hn : 1 ≤ n) (_hk : 2 ≤ k)
    (_hdim : 2 * n - 1 ≤ k) (hkn : n + 2 ≤ k) :
    sharpRealSmallBallCoefficientB n k ≤
      Real.sqrt
          (2 * (((2 * n - 1 : ℕ) : ℝ)) / Real.pi) *
        Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((k - n - 1 : ℕ) : ℝ))) := by
  have hbound := sharpRealNormalizedCoefficientReal_le_exp_sharp hn hkn
  rw [sharpRealSmallBallCoefficientB]
  calc
    realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
          sharpRealGammaCoefficientReal n k ≤
        realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp
            ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (4 * ((k - n - 1 : ℕ) : ℝ))) := hbound
    _ = Real.sqrt
          (2 * (((2 * n - 1 : ℕ) : ℝ)) / Real.pi) *
        Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((k - n - 1 : ℕ) : ℝ))) := by
      rw [realGaussianIntervalPrefactor_one_mul_sqrt_eq_literal
        (2 * n - 1)]

end

end LogdetLean.GramHafnian
