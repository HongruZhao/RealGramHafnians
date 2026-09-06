import LogdetLean.GramHafnian.ActualGramMoments
import LogdetLean.GramHafnian.RankOneGaussianBilinear
/-!
# Closed form for the literal Gaussian Gram-hafnian first moment

This module closes the first of the two outer real-Gaussian integrals left by
`ActualGramMoments`.  No probabilistic object is postulated: the matrix law is
the product of the pushed-forward circular scalar Gaussian laws, and the
right-hand side is the exact finite-dimensional closed form.
-/

namespace LogdetLean.GramHafnian

noncomputable section

/-- **Literal Gaussian Gram-hafnian first moment.**  In positive auxiliary
dimension `k`, the expectation of the squared modulus of the Gram hafnian is
the exact rank-one closed form.

The name `actualGramFirstMomentReal` refers to the literal integral defined in
`ActualGramMoments`, rather than an abstract random variable with assumed
moments. -/
theorem actualGramFirstMomentReal_eq_closedFirstMoment
    (k n : ℕ) (hk : 0 < k) :
    actualGramFirstMomentReal k n = closedFirstMoment k n := by
  rw [actualGramFirstMomentReal_eq_realGaussianBilinearIntegral]
  exact integral_bilinearDot_pow_two_mul_twoRealGaussianFieldsMeasure k n hk

/-- Complex-valued restatement of the same literal first-moment identity. -/
theorem actualGramFirstMoment_eq_closedFirstMoment
    (k n : ℕ) (hk : 0 < k) :
    actualGramFirstMoment k n = (closedFirstMoment k n : ℂ) := by
  rw [actualGramFirstMoment_eq_ofReal,
    actualGramFirstMomentReal_eq_closedFirstMoment k n hk]

end

end LogdetLean.GramHafnian
