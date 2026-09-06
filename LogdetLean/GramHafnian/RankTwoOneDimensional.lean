import LogdetLean.GramHafnian.RankTwoCentralBinomial
import LogdetLean.GramHafnian.GramMomentFubini
import LogdetLean.GramHafnian.RankOneGaussianBilinear
/-!
# The one-dimensional rank-two Gaussian endpoint

The usual Gaussian radial--angle proof of the fourth Gram-hafnian moment uses
a beta law with second shape `(k-1)/2`, and therefore naturally starts at
`k >= 2`.  This file proves the missing `k = 1` endpoint directly from four
scalar Gaussian even moments.
-/

open scoped BigOperators Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- A coordinate field indexed by `Fin 1` has the scalar Gaussian even
moment. -/
theorem integral_fin_one_eval_pow_two_mul_standardRealGaussianVectorMeasure
    (n : ℕ) :
    (∫ g : Fin 1 → ℝ, g 0 ^ (2 * n)
        ∂standardRealGaussianVectorMeasure 1) =
      (oddPairingNat n : ℝ) := by
  have h := integral_realCoordinatePowerProduct_pi
    (K := Fin 1) (gaussianReal 0 1) (fun _ ↦ 2 * n)
  simpa [standardRealGaussianVectorMeasure, realCoordinatePowerProduct,
    integral_pow_two_gaussianReal, oddPairingNat_eq_doubleFactorial] using h

/-- Pointwise collapse of the symmetric rank-two form in dimension one. -/
theorem rankTwoBilinear_fin_one
    (g₁ g₂ h₁ h₂ : Fin 1 → ℝ) :
    rankTwoBilinear g₁ g₂ h₁ h₂ =
      2 * g₁ 0 * g₂ 0 * h₁ 0 * h₂ 0 := by
  simp [rankTwoBilinear, bilinearDot]
  ring

/-- The literal four-field integral in dimension one, before rewriting the
finite correction. -/
theorem integral_rankTwoBilinear_fin_one_pow_two_mul
    (n : ℕ) :
    (∫ w : FourRealFields 1,
        rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 ^ (2 * n)
          ∂fourRealGaussianFieldsMeasure 1) =
      (2 : ℝ) ^ (2 * n) * (oddPairingNat n : ℝ) ^ 4 := by
  let μ : Measure (Fin 1 → ℝ) := standardRealGaussianVectorMeasure 1
  let f : (Fin 1 → ℝ) → ℝ := fun g ↦ g 0 ^ (2 * n)
  have hprod :
      (∫ w : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) ×
          ((Fin 1 → ℝ) × (Fin 1 → ℝ)),
          (f w.1.1 * f w.1.2) * (f w.2.1 * f w.2.2)
            ∂((μ.prod μ).prod (μ.prod μ))) =
        ((∫ g, f g ∂μ) * (∫ g, f g ∂μ)) *
          ((∫ g, f g ∂μ) * (∫ g, f g ∂μ)) := by
    calc
      (∫ w : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) ×
          ((Fin 1 → ℝ) × (Fin 1 → ℝ)),
          (f w.1.1 * f w.1.2) * (f w.2.1 * f w.2.2)
            ∂((μ.prod μ).prod (μ.prod μ))) =
          (∫ x : (Fin 1 → ℝ) × (Fin 1 → ℝ),
              f x.1 * f x.2 ∂(μ.prod μ)) *
            (∫ y : (Fin 1 → ℝ) × (Fin 1 → ℝ),
              f y.1 * f y.2 ∂(μ.prod μ)) := by
                exact integral_prod_mul
                  (fun x : (Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
                    f x.1 * f x.2)
                  (fun y : (Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
                    f y.1 * f y.2)
      _ = ((∫ g, f g ∂μ) * (∫ g, f g ∂μ)) *
          ((∫ g, f g ∂μ) * (∫ g, f g ∂μ)) := by
            have hinner := integral_prod_mul (μ := μ) (ν := μ) f f
            rw [hinner]
  rw [show (fun w : FourRealFields 1 ↦
      rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 ^ (2 * n)) =
      fun w ↦ (2 : ℝ) ^ (2 * n) *
        ((f w.1.1 * f w.1.2) * (f w.2.1 * f w.2.2)) by
    funext w
    rw [rankTwoBilinear_fin_one]
    dsimp [f]
    simp only [mul_pow]
    ring]
  unfold fourRealGaussianFieldsMeasure twoRealGaussianFieldsMeasure
  rw [integral_const_mul, hprod]
  have hm : (∫ g, f g ∂μ) = (oddPairingNat n : ℝ) := by
    simpa [f, μ] using
      integral_fin_one_eval_pow_two_mul_standardRealGaussianVectorMeasure n
  rw [hm]
  ring

/-- **Exact one-dimensional M2 endpoint.** -/
theorem integral_rankTwoBilinear_fin_one_pow_two_mul_eq_closedFourthMoment
    (n : ℕ) :
    (∫ w : FourRealFields 1,
        rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 ^ (2 * n)
          ∂fourRealGaussianFieldsMeasure 1) =
      closedFourthMoment 1 n := by
  rw [integral_rankTwoBilinear_fin_one_pow_two_mul]
  rw [closedFourthMoment, finiteCorrection_one]
  have hdim : dimensionProduct 1 n = (oddPairingNat n : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [dimensionProduct_succ, oddPairingNat_succ, ih]
        push_cast
        ring
  rw [hdim]
  have hfac := oddPairing_sq_div_factorial_eq_centralBaseline n
  rw [centralBaseline] at hfac
  have hoddNat : oddPairingNat n ≠ 0 := by
    unfold oddPairingNat
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      omega)
  have hodd : (oddPairingNat n : ℝ) ≠ 0 := by exact_mod_cast hoddNat
  have hfact : (((2 * n).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hchoose : (((Nat.choose (2 * n) n : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : n ≤ 2 * n)))
  have hfour : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [hodd, hfact, hchoose, hfour] at hfac ⊢
  have hpow : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [hpow] at hfac
  exact hfac

end

end LogdetLean.GramHafnian
