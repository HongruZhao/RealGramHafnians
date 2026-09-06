import LogdetLean.GramHafnian.FourthContraction
import Mathlib.MeasureTheory.Integral.Pi
/-!
# Independent complex-coordinate moment factorization

This file is the measure-theoretic bridge needed for circular complex
Gaussians.  It deliberately separates the generic product-law theorem from
the one-dimensional scalar moment calculation.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian

variable {I : Type*} [Fintype I]

/-- One mixed complex monomial `z^a * conj(z)^b`. -/
def mixedComplexMonomial (a b : ℕ) (z : ℂ) : ℂ :=
  z ^ a * conj z ^ b

/-- A coordinatewise mixed monomial. -/
def mixedComplexMultiMonomial (a b : I → ℕ) (z : I → ℂ) : ℂ :=
  ∏ i, mixedComplexMonomial (a i) (b i) (z i)

/-- Exact factorization of a mixed monomial under a finite product measure.
This is a direct finite-dimensional Fubini theorem. -/
theorem integral_mixedComplexMultiMonomial_pi
    (mu : I → Measure ℂ) [∀ i, SigmaFinite (mu i)] (a b : I → ℕ) :
    ∫ z, mixedComplexMultiMonomial a b z ∂(Measure.pi mu) =
      ∏ i, ∫ w, mixedComplexMonomial (a i) (b i) w ∂(mu i) := by
  unfold mixedComplexMultiMonomial
  exact integral_fintype_prod_eq_prod
    (fun i w ↦ mixedComplexMonomial (a i) (b i) w)

/-- The full scalar mixed-moment property of a standard circular complex
Gaussian.  It is a predicate, not an axiom: downstream theorems take an
explicit proof of it. -/
def HasStandardCircularMoments (mu : Measure ℂ) : Prop :=
  ∀ a b : ℕ,
    ∫ z, mixedComplexMonomial a b z ∂mu =
      if a = b then (a.factorial : ℂ) else 0

/-- Product circular moments: a mixed monomial vanishes unless every
coordinate is balanced, and in the balanced case equals the product of
factorials. -/
theorem integral_mixedComplexMultiMonomial_pi_of_circular
    (mu : Measure ℂ) [SigmaFinite mu] (hmu : HasStandardCircularMoments mu)
    (a b : I → ℕ) :
    ∫ z, mixedComplexMultiMonomial a b z
        ∂(Measure.pi fun _ : I ↦ mu) =
      if a = b then ∏ i, ((a i).factorial : ℂ) else 0 := by
  classical
  rw [integral_mixedComplexMultiMonomial_pi]
  unfold HasStandardCircularMoments at hmu
  simp_rw [hmu]
  by_cases hab : a = b
  · subst b
    simp
  · have hpoint : ∃ i, a i ≠ b i := by
      by_contra h
      push_neg at h
      exact hab (funext h)
    obtain ⟨i, hi⟩ := hpoint
    simp [hab, Finset.prod_eq_zero (Finset.mem_univ i), hi]

/-- The iid specialization of the generic Fubini factorization. -/
theorem integral_mixedComplexMultiMonomial_iid
    (mu : Measure ℂ) [SigmaFinite mu] (a b : I → ℕ) :
    ∫ z, mixedComplexMultiMonomial a b z
        ∂(Measure.pi fun _ : I ↦ mu) =
      ∏ i, ∫ w, mixedComplexMonomial (a i) (b i) w ∂mu := by
  simpa using integral_mixedComplexMultiMonomial_pi
    (mu := fun _ : I ↦ mu) a b

end LogdetLean.GramHafnian
