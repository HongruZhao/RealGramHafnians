import LogdetLean.GramHafnian.Hafnian
/-!
# The one-column fourth-moment contraction

This file isolates the finite tensor calculation behind the complex-Gaussian
column integration.  It is distribution-free: once the fourth moment tensor
is the circular Wick tensor, its contraction is the sum of the two pairings.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

variable {k : ℕ}

/-- Bilinear dot product without conjugation. -/
def bilinearDot {R : Type*} [CommSemiring R] (u v : Fin k → R) : R :=
  ∑ i, u i * v i

/-- Kronecker delta, valued in a semiring. -/
def kroneckerDelta {R : Type*} [CommSemiring R] (a b : Fin k) : R :=
  if a = b then 1 else 0

/-- The two-pairing fourth-moment tensor of iid standard circular complex
coordinates. -/
def circularFourthKernel {R : Type*} [CommSemiring R]
    (a b c d : Fin k) : R :=
  kroneckerDelta a c * kroneckerDelta b d +
    kroneckerDelta a d * kroneckerDelta b c

/-- Contract four coefficient vectors against a four-index tensor. -/
def fourthTensorContraction {R : Type*} [CommSemiring R]
    (g₁ g₂ h₁ h₂ : Fin k → R)
    (K : Fin k → Fin k → Fin k → Fin k → R) : R :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    g₁ a * g₂ b * h₁ c * h₂ d * K a b c d

/-- The exact Wick contraction

`sum g₁[a] g₂[b] h₁[c] h₂[d]
  (δ_ac δ_bd + δ_ad δ_bc)`

equals the two possible bilinear pairings. -/
theorem fourthTensorContraction_circularFourthKernel
    {R : Type*} [CommSemiring R] (g₁ g₂ h₁ h₂ : Fin k → R) :
    fourthTensorContraction g₁ g₂ h₁ h₂ circularFourthKernel =
      bilinearDot g₁ h₁ * bilinearDot g₂ h₂ +
      bilinearDot g₁ h₂ * bilinearDot g₂ h₁ := by
  classical
  unfold fourthTensorContraction circularFourthKernel bilinearDot kroneckerDelta
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply congrArg₂ (.+.)
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- The symmetric rank-two bilinear form used after integrating one complex
Gaussian column. -/
def rankTwoBilinear {R : Type*} [CommSemiring R]
    (g₁ g₂ h₁ h₂ : Fin k → R) : R :=
  bilinearDot g₁ h₁ * bilinearDot g₂ h₂ +
    bilinearDot g₁ h₂ * bilinearDot g₂ h₁

theorem fourthTensorContraction_eq_rankTwoBilinear
    {R : Type*} [CommSemiring R] (g₁ g₂ h₁ h₂ : Fin k → R) :
    fourthTensorContraction g₁ g₂ h₁ h₂ circularFourthKernel =
      rankTwoBilinear g₁ g₂ h₁ h₂ :=
  fourthTensorContraction_circularFourthKernel g₁ g₂ h₁ h₂

end LogdetLean.GramHafnian
