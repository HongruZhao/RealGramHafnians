import LogdetLean.GramHafnian.Hafnian
import Mathlib.MeasureTheory.Integral.Pi
/-!
# Auxiliary-field expansion before Wick regrouping

For an iid real auxiliary field, this file expands a product of linear forms
by row-colourings, groups repeated coordinates into powers, and integrates the
result using finite-dimensional Fubini.  This is the exact analytic part of
the auxiliary-Gaussian hafnian identity.  The still separate combinatorial
step is to regroup the even multiplicity weights by perfect matchings.
-/

open scoped BigOperators
open MeasureTheory

namespace LogdetLean.GramHafnian

variable {I K : Type*} [Fintype I] [Fintype K]
  [DecidableEq I] [DecidableEq K]

/-- Number of vertices assigned a given colour. -/
def colorMultiplicity (c : I → K) (a : K) : ℕ :=
  (Finset.univ.filter fun i ↦ c i = a).card

/-- Product of coordinate powers specified by a multiplicity vector. -/
def realCoordinatePowerProduct (e : K → ℕ) (g : K → ℝ) : ℝ :=
  ∏ a, (g a) ^ (e a)

theorem prod_comp_eq_coordinatePowerProduct
    {R : Type*} [CommMonoid R] (c : I → K) (g : K → R) :
    (∏ i, g (c i)) = ∏ a, (g a) ^ colorMultiplicity c a := by
  rw [← Finset.prod_fiberwise' Finset.univ c g]
  apply Finset.prod_congr rfl
  intro a _
  rw [Finset.prod_const]
  rfl

/-- Product of real linear forms, one for each column. -/
def auxiliaryFieldProduct (X : K → I → ℝ) (g : K → ℝ) : ℝ :=
  ∏ i, ∑ a, g a * X a i

/-- Coefficient of one row-colouring. -/
def coloringCoefficient (X : K → I → ℝ) (c : I → K) : ℝ :=
  ∏ i, X (c i) i

/-- Exact finite row-colouring expansion of the auxiliary-field product. -/
theorem auxiliaryFieldProduct_eq_coloringSum
    (X : K → I → ℝ) (g : K → ℝ) :
    auxiliaryFieldProduct X g =
      ∑ c : I → K,
        coloringCoefficient X c *
          realCoordinatePowerProduct (colorMultiplicity c) g := by
  classical
  unfold auxiliaryFieldProduct
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold coloringCoefficient realCoordinatePowerProduct
  rw [← prod_comp_eq_coordinatePowerProduct c g]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- Fubini factorization for one coordinate-power product. -/
theorem integral_realCoordinatePowerProduct_pi
    (mu : Measure ℝ) [SigmaFinite mu] (e : K → ℕ) :
    ∫ g, realCoordinatePowerProduct e g
        ∂(Measure.pi fun _ : K ↦ mu) =
      ∏ a, ∫ x, x ^ (e a) ∂mu := by
  unfold realCoordinatePowerProduct
  exact integral_fintype_prod_eq_prod (fun a x ↦ x ^ (e a))

/-- Exact integrated colouring expansion for any scalar product law with all
power moments integrable. -/
theorem integral_auxiliaryFieldProduct_eq_coloringMoments
    (mu : Measure ℝ) [SigmaFinite mu]
    (hInt : ∀ r : ℕ, Integrable (fun x : ℝ ↦ x ^ r) mu)
    (X : K → I → ℝ) :
    ∫ g, auxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : K ↦ mu) =
      ∑ c : I → K,
        coloringCoefficient X c *
          ∏ a, ∫ x, x ^ colorMultiplicity c a ∂mu := by
  classical
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (auxiliaryFieldProduct_eq_coloringSum X))]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul, integral_realCoordinatePowerProduct_pi]
  · intro c _
    apply Integrable.const_mul
    apply Integrable.fintype_prod
    intro a
    exact hInt (colorMultiplicity c a)

/-- The scalar moment functional appearing after iid Fubini. -/
def coloringMomentWeight (scalarMoment : ℕ → ℝ) (c : I → K) : ℝ :=
  ∏ a, scalarMoment (colorMultiplicity c a)

/-- Rewriting the integrated expansion when the scalar moments are known. -/
theorem integral_auxiliaryFieldProduct_eq_weightedColoringSum
    (mu : Measure ℝ) [SigmaFinite mu]
    (hInt : ∀ r : ℕ, Integrable (fun x : ℝ ↦ x ^ r) mu)
    (scalarMoment : ℕ → ℝ)
    (hMoment : ∀ r : ℕ, ∫ x, x ^ r ∂mu = scalarMoment r)
    (X : K → I → ℝ) :
    ∫ g, auxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : K ↦ mu) =
      ∑ c : I → K,
        coloringCoefficient X c * coloringMomentWeight scalarMoment c := by
  rw [integral_auxiliaryFieldProduct_eq_coloringMoments mu hInt X]
  simp_rw [hMoment]
  rfl

/-! ## Complex coefficients with a real auxiliary field -/

/-- Complex coefficient of one row-colouring. -/
def complexColoringCoefficient (X : K → I → ℂ) (c : I → K) : ℂ :=
  ∏ i, X (c i) i

/-- Coordinate powers of a real field, embedded into `ℂ`. -/
def complexCoordinatePowerProduct (e : K → ℕ) (g : K → ℝ) : ℂ :=
  ∏ a, (g a : ℂ) ^ (e a)

/-- Product of complex linear forms driven by a real auxiliary field. -/
def complexAuxiliaryFieldProduct (X : K → I → ℂ) (g : K → ℝ) : ℂ :=
  ∏ i, ∑ a, (g a : ℂ) * X a i

theorem complexAuxiliaryFieldProduct_eq_coloringSum
    (X : K → I → ℂ) (g : K → ℝ) :
    complexAuxiliaryFieldProduct X g =
      ∑ c : I → K,
        complexColoringCoefficient X c *
          complexCoordinatePowerProduct (colorMultiplicity c) g := by
  classical
  unfold complexAuxiliaryFieldProduct
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold complexColoringCoefficient complexCoordinatePowerProduct
  have hp : (∏ i, (g (c i) : ℂ)) =
      ∏ a, (g a : ℂ) ^ colorMultiplicity c a :=
    prod_comp_eq_coordinatePowerProduct c (fun a ↦ (g a : ℂ))
  rw [← hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem integral_complexCoordinatePowerProduct_pi
    (mu : Measure ℝ) [SigmaFinite mu] (e : K → ℕ) :
    ∫ g, complexCoordinatePowerProduct e g
        ∂(Measure.pi fun _ : K ↦ mu) =
      ∏ a, ∫ x, (x : ℂ) ^ (e a) ∂mu := by
  unfold complexCoordinatePowerProduct
  exact integral_fintype_prod_eq_prod
    (E := fun _ : K ↦ ℝ) (μ := fun _ : K ↦ mu)
    (fun a x ↦ (x : ℂ) ^ (e a))

/-- Exact iid real-field expansion with complex deterministic coefficients. -/
theorem integral_complexAuxiliaryFieldProduct_eq_weightedColoringSum
    (mu : Measure ℝ) [SigmaFinite mu]
    (hInt : ∀ r : ℕ, Integrable (fun x : ℝ ↦ x ^ r) mu)
    (scalarMoment : ℕ → ℝ)
    (hMoment : ∀ r : ℕ, ∫ x, x ^ r ∂mu = scalarMoment r)
    (X : K → I → ℂ) :
    ∫ g, complexAuxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : K ↦ mu) =
      ∑ c : I → K,
        complexColoringCoefficient X c *
          ∏ a, (scalarMoment (colorMultiplicity c a) : ℂ) := by
  classical
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (complexAuxiliaryFieldProduct_eq_coloringSum X))]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul, integral_complexCoordinatePowerProduct_pi]
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    simp_rw [← Complex.ofReal_pow]
    rw [integral_complex_ofReal, hMoment (colorMultiplicity c a)]
  · intro c _
    apply Integrable.const_mul
    unfold complexCoordinatePowerProduct
    exact Integrable.fintype_prod
      (E := ℝ)
      (μ := fun _ : K ↦ mu)
      (f := fun a x ↦ (x : ℂ) ^ colorMultiplicity c a)
      (fun a ↦ by
        have hr := hInt (colorMultiplicity c a)
        have hc : Integrable
            (fun x : ℝ ↦ ((x ^ colorMultiplicity c a : ℝ) : ℂ)) mu :=
          hr.ofReal
        simpa only [Complex.ofReal_pow] using hc)

end LogdetLean.GramHafnian
