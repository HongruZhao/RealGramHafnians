import LogdetLean.LogBetaCharacteristic
import LogdetLean.NullCenterStandardization
/-!
# Explicit characteristic function in finite digamma/trigamma notation

This file joins the exact Gamma-product characteristic function proved in
`LogBetaCharacteristic` to the exact finite centering and variance evaluations
proved in `NullCenterStandardization` and `BetaCumulantSeries`.

The precise published formulas followed are Xie--Sun (2021), equations
(4)--(7), pp. 430--431, for the centering and variance, and equations
(13)--(16), pp. 435--436, for the Gamma-product characteristic function.
After setting their sample-size symbol `n` equal to the effective centered
dimension `m`, their `j = 1` term is one in the product and zero in the
cumulant sums, so the Lean formulas start at `j = 2`.  The one-factor Mellin
identity is Rouault (2007), equation (2.10), p. 189.

These references are provenance, not axioms.  Both substitutions below are
kernel-checked rewrites by earlier project theorems.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The centered exact Gamma product with the finite digamma centering rather
than the expectation-defined abbreviation. -/
theorem charFun_centeredLogBetaSumLaw_eq_digammaGammaProduct
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    charFun (centeredLogBetaSumLaw m p) t =
      Complex.exp
          (-(((nullCenterDigammaSeries m p * t : ℝ) : ℂ) * Complex.I)) *
        ∏ j ∈ Finset.Icc 2 p,
          (Complex.Gamma
              ((betaShapeA m j : ℂ) + (t : ℂ) * Complex.I) *
            Complex.Gamma
              (((betaShapeA m j + betaShapeB j : ℝ) : ℂ)) /
            (Complex.Gamma (betaShapeA m j : ℂ) *
              Complex.Gamma
                (((betaShapeA m j + betaShapeB j : ℝ) : ℂ) +
                  (t : ℂ) * Complex.I))) := by
  rw [charFun_centeredLogBetaSumLaw_eq_explicitGammaProduct hpm,
    nullCenter_eq_nullCenterDigammaSeries hpm]

/-- The standardized exact Gamma product written entirely with the finite
digamma centering and finite trigamma variance used for `Z_{0,m,p}`. -/
theorem charFun_standardizedNullLaw_eq_digammaTrigammaGammaProduct
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    let q := t / Real.sqrt (nullVSeries m p)
    charFun (standardizedNullLaw m p) t =
      Complex.exp
          (-(((nullCenterDigammaSeries m p * q : ℝ) : ℂ) * Complex.I)) *
        ∏ j ∈ Finset.Icc 2 p,
          (Complex.Gamma
              ((betaShapeA m j : ℂ) + (q : ℂ) * Complex.I) *
            Complex.Gamma
              (((betaShapeA m j + betaShapeB j : ℝ) : ℂ)) /
            (Complex.Gamma (betaShapeA m j : ℂ) *
              Complex.Gamma
                (((betaShapeA m j + betaShapeB j : ℝ) : ℂ) +
                  (q : ℂ) * Complex.I))) := by
  rw [← nullCenter_eq_nullCenterDigammaSeries hpm,
    ← nullVariance_eq_nullVSeries hpm]
  exact charFun_standardizedNullLaw_eq_explicitGammaProduct hpm t

end

end LogdetLean
