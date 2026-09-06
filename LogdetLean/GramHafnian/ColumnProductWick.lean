import LogdetLean.GramHafnian.OneColumnWick
import Mathlib.MeasureTheory.Integral.Pi
/-!
# From one circular column to `2n` independent columns

Finite-dimensional Fubini turns the one-column Wick contraction into the
`2n`-th power of the rank-two bilinear form.  This is exactly the column
independence step in the Gram--hafnian fourth-moment proof.
-/

open scoped BigOperators
open MeasureTheory

namespace LogdetLean.GramHafnian

variable {n k : ℕ}

/-- Product of the four-linear integrand over `2n` independent columns. -/
def columnFourthProduct
    (g₁ g₂ h₁ h₂ : Fin k → ℂ)
    (X : Fin (2 * n) → (Fin k → ℂ)) : ℂ :=
  ∏ i, columnFourthIntegrand g₁ g₂ h₁ h₂ (X i)

/-- **Independent-column Wick bridge.** The only distribution-specific
inputs are integrability and the literal one-column fourth tensor. -/
theorem integral_columnFourthProduct_eq_rankTwo_pow
    [MeasurableSpace (Fin k → ℂ)]
    (mu : Measure (Fin k → ℂ)) [SigmaFinite mu]
    (g₁ g₂ h₁ h₂ : Fin k → ℂ)
    (hInt : ∀ a b c d,
      Integrable (fun x ↦ coordinateFourthMonomial x a b c d) mu)
    (hMoment : ∀ a b c d,
      ∫ x, coordinateFourthMonomial x a b c d ∂mu =
        circularFourthKernel a b c d) :
    ∫ X, columnFourthProduct g₁ g₂ h₁ h₂ X
        ∂(Measure.pi fun _ : Fin (2 * n) ↦ mu) =
      rankTwoBilinear g₁ g₂ h₁ h₂ ^ (2 * n) := by
  unfold columnFourthProduct
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_columnFourthIntegrand_eq_rankTwoBilinear
    mu g₁ g₂ h₁ h₂ hInt hMoment]
  simp

end LogdetLean.GramHafnian
