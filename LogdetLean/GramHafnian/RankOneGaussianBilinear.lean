import LogdetLean.GramHafnian.RankTwoCentralBinomial
import LogdetLean.FixedSubspaceGaussian
import LogdetLean.GammaMellin
import LogdetLean.Coherence.RubenCoordinates
import LogdetLean.GramHafnian.GramMomentFubini
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-!
# Exact rank-one Gaussian bilinear moment

This file proves the exact first moment reduction used for a Gaussian Gram
hafnian.  If `g` and `h` are independent standard real Gaussian vectors in
dimension `k > 0`, then

`E[(sum_i g_i h_i)^(2n)] = (2n-1)!! * k(k+2)...(k+2n-2)`.

The proof conditions on `g`.  The scalar projection of `h` along the axis
`g` is standard normal, while the squared radius of `g` has its exact Gamma
law.  Every ingredient is a theorem in Mathlib or in the shared Gaussian
package; no project axiom is used.
-/

open scoped BigOperators RealInnerProductSpace ENNReal Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- The law of an iid standard real Gaussian vector in coordinate form. -/
def standardRealGaussianVector (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k ↦ gaussianReal 0 1

instance (k : ℕ) : IsProbabilityMeasure (standardRealGaussianVector k) := by
  unfold standardRealGaussianVector
  infer_instance

instance (k : ℕ) : SigmaFinite (standardRealGaussianVector k) := inferInstance

/-- The real bilinear dot product on coordinate vectors. -/
def realBilinearDot {k : ℕ} (g h : Fin k → ℝ) : ℝ :=
  ∑ i, g i * h i

@[simp] theorem dimensionProduct_zero (k : ℕ) :
    dimensionProduct k 0 = 1 := by
  simp [dimensionProduct]

theorem dimensionProduct_succ (k n : ℕ) :
    dimensionProduct k (n + 1) =
      dimensionProduct k n * (k + 2 * n : ℕ) := by
  simp [dimensionProduct, Finset.prod_range_succ]

/-- The Gamma-ratio form of a chi-square moment is exactly the elementary
dimension product. -/
theorem gammaRatio_half_eq_dimensionProduct (k n : ℕ) (hk : 0 < k) :
    (1 / 2 : ℝ) ^ (-(n : ℝ)) *
          Real.Gamma ((k : ℝ) / 2 + n) / Real.Gamma ((k : ℝ) / 2) =
      dimensionProduct k n := by
  induction n with
  | zero =>
      simp [dimensionProduct, (Real.Gamma_pos_of_pos (by positivity :
        0 < (k : ℝ) / 2)).ne']
  | succ n ih =>
      have ha : 0 < (k : ℝ) / 2 := by positivity
      have han : (k : ℝ) / 2 + n ≠ 0 := by positivity
      have hG : Real.Gamma ((k : ℝ) / 2) ≠ 0 :=
        (Real.Gamma_pos_of_pos ha).ne'
      have hGamma :
          Real.Gamma ((k : ℝ) / 2 + ((n + 1 : ℕ) : ℝ)) =
            ((k : ℝ) / 2 + n) * Real.Gamma ((k : ℝ) / 2 + n) := by
        convert Real.Gamma_add_one han using 1 <;> norm_num <;> ring
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num]
      rw [neg_add, Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ)),
        show Real.Gamma ((k : ℝ) / 2 + ((n : ℝ) + 1)) =
          ((k : ℝ) / 2 + n) * Real.Gamma ((k : ℝ) / 2 + n) by
            simpa only [Nat.cast_add, Nat.cast_one] using hGamma,
        dimensionProduct_succ]
      rw [Real.rpow_neg_one]
      calc
        (1 / 2 : ℝ) ^ (-(n : ℝ)) * (1 / 2 : ℝ)⁻¹ *
              (((k : ℝ) / 2 + n) * Real.Gamma ((k : ℝ) / 2 + n)) /
              Real.Gamma ((k : ℝ) / 2) =
            ((1 / 2 : ℝ) ^ (-(n : ℝ)) *
                Real.Gamma ((k : ℝ) / 2 + n) /
                Real.Gamma ((k : ℝ) / 2)) *
              (k + 2 * n : ℕ) := by
                push_cast
                field_simp
        _ = dimensionProduct k n * (k + 2 * n : ℕ) := by rw [ih]

/-- Exact natural moments of the chi-square/Gamma law in dimension `k`. -/
theorem integral_pow_gammaMeasure_half_eq_dimensionProduct
    (k n : ℕ) (hk : 0 < k) :
    (∫ x : ℝ, x ^ n
        ∂gammaMeasure ((k : ℝ) / 2) (1 / 2)) =
      dimensionProduct k n := by
  rw [show (fun x : ℝ ↦ x ^ n) = (fun x : ℝ ↦ x ^ (n : ℝ)) by
    funext x
    exact (Real.rpow_natCast x n).symm]
  rw [LogdetLean.integral_rpow_gammaMeasure
    (by positivity : 0 < (k : ℝ) / 2)
    (by norm_num : 0 < (1 / 2 : ℝ))
    (by positivity : 0 < (k : ℝ) / 2 + (n : ℝ))]
  exact gammaRatio_half_eq_dimensionProduct k n hk

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Exact even radial moments of a nontrivial finite-dimensional standard
Gaussian vector. -/
theorem integral_norm_pow_two_mul_stdGaussian [Nontrivial E] (n : ℕ) :
    (∫ x : E, ‖x‖ ^ (2 * n) ∂stdGaussian E) =
      dimensionProduct (Module.finrank ℝ E) n := by
  have hLaw := LogdetLean.hasLaw_normSq_stdGaussian E
  rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma E] at hLaw
  calc
    (∫ x : E, ‖x‖ ^ (2 * n) ∂stdGaussian E) =
        ∫ x : E, (‖x‖ ^ 2) ^ n ∂stdGaussian E := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact pow_mul ‖x‖ 2 n
    _ = ∫ q : ℝ, q ^ n
          ∂gammaMeasure ((Module.finrank ℝ E : ℝ) / 2) (1 / 2) := by
      simpa only [Function.comp_apply] using
        hLaw.integral_comp
          ((measurable_id'.pow_const n).aestronglyMeasurable)
    _ = dimensionProduct (Module.finrank ℝ E) n :=
      integral_pow_gammaMeasure_half_eq_dimensionProduct _ n
        (Module.finrank_pos)

/-- Conditional even moment of a Gaussian scalar projection. -/
theorem integral_inner_pow_two_mul_stdGaussian (u : E) (n : ℕ) :
    (∫ v : E, inner ℝ u v ^ (2 * n) ∂stdGaussian E) =
      (oddPairingNat n : ℝ) * ‖u‖ ^ (2 * n) := by
  by_cases hu : u = 0
  · subst u
    cases n <;> simp [oddPairingNat]
  · have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hLaw : HasLaw (LogdetLean.Coherence.gaussianAxisCoordinate u)
        (gaussianReal 0 1) (stdGaussian E) :=
      ⟨(LogdetLean.Coherence.measurable_gaussianAxisCoordinate u).aemeasurable,
        LogdetLean.Coherence.map_gaussianAxisCoordinate_stdGaussian u hu⟩
    have haxis :
        (∫ v : E,
            LogdetLean.Coherence.gaussianAxisCoordinate u v ^ (2 * n)
              ∂stdGaussian E) = (oddPairingNat n : ℝ) := by
      calc
        (∫ v : E,
            LogdetLean.Coherence.gaussianAxisCoordinate u v ^ (2 * n)
              ∂stdGaussian E) =
            ∫ z : ℝ, z ^ (2 * n) ∂gaussianReal 0 1 := by
          simpa only [Function.comp_apply] using
            hLaw.integral_comp
              ((measurable_id'.pow_const (2 * n)).aestronglyMeasurable)
        _ = (((2 * n - 1)‼) : ℝ) := by
          exact integral_pow_two_gaussianReal n
        _ = (oddPairingNat n : ℝ) := by
          exact_mod_cast (oddPairingNat_eq_doubleFactorial n).symm
    have hpoint (v : E) :
        inner ℝ u v = ‖u‖ *
          LogdetLean.Coherence.gaussianAxisCoordinate u v := by
      unfold LogdetLean.Coherence.gaussianAxisCoordinate
      field_simp [hnorm]
    calc
      (∫ v : E, inner ℝ u v ^ (2 * n) ∂stdGaussian E) =
          ∫ v : E, (‖u‖ *
            LogdetLean.Coherence.gaussianAxisCoordinate u v) ^ (2 * n)
              ∂stdGaussian E := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun v ↦ congrArg (· ^ (2 * n)) (hpoint v)
      _ = ‖u‖ ^ (2 * n) *
          (∫ v : E,
            LogdetLean.Coherence.gaussianAxisCoordinate u v ^ (2 * n)
              ∂stdGaussian E) := by
        simp_rw [mul_pow]
        rw [integral_const_mul]
      _ = (oddPairingNat n : ℝ) * ‖u‖ ^ (2 * n) := by
        rw [haxis]
        ring

/-- Every polynomial moment of the Gaussian inner product is integrable on
the product law.  This is the hypothesis needed for the literal Fubini step. -/
theorem integrable_inner_pow_stdGaussian_prod (m : ℕ) :
    Integrable (fun w : E × E ↦ inner ℝ w.1 w.2 ^ m)
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hnorm : Integrable (fun x : E ↦ ‖x‖ ^ m) (stdGaussian E) := by
    simpa only [id_eq] using
      (ProbabilityTheory.IsGaussian.memLp_id (stdGaussian E) (m : ℝ≥0∞)
        (by simp)).integrable_norm_pow'
  apply (hnorm.mul_prod hnorm).mono'
  · fun_prop
  · filter_upwards [] with w
    calc
      ‖inner ℝ w.1 w.2 ^ m‖ = ‖inner ℝ w.1 w.2‖ ^ m := norm_pow _ _
      _ ≤ (‖w.1‖ * ‖w.2‖) ^ m := by
        gcongr
        exact norm_inner_le_norm w.1 w.2
      _ = ‖w.1‖ ^ m * ‖w.2‖ ^ m := mul_pow _ _ _

/-- Exact even moment of the inner product of two independent standard
Gaussian vectors in a nontrivial finite-dimensional real inner-product
space. -/
theorem integral_inner_prod_pow_two_mul_stdGaussian [Nontrivial E] (n : ℕ) :
    (∫ w : E × E, inner ℝ w.1 w.2 ^ (2 * n)
        ∂((stdGaussian E).prod (stdGaussian E))) =
      closedFirstMoment (Module.finrank ℝ E) n := by
  calc
    (∫ w : E × E, inner ℝ w.1 w.2 ^ (2 * n)
        ∂((stdGaussian E).prod (stdGaussian E))) =
        ∫ g : E, ∫ h : E, inner ℝ g h ^ (2 * n)
          ∂stdGaussian E ∂stdGaussian E := by
      exact integral_prod _ (integrable_inner_pow_stdGaussian_prod (E := E) (2 * n))
    _ = ∫ g : E, (oddPairingNat n : ℝ) * ‖g‖ ^ (2 * n)
          ∂stdGaussian E := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g ↦
        integral_inner_pow_two_mul_stdGaussian g n
    _ = (oddPairingNat n : ℝ) *
          (∫ g : E, ‖g‖ ^ (2 * n) ∂stdGaussian E) := by
      rw [integral_const_mul]
    _ = (oddPairingNat n : ℝ) *
          dimensionProduct (Module.finrank ℝ E) n := by
      rw [integral_norm_pow_two_mul_stdGaussian]
    _ = closedFirstMoment (Module.finrank ℝ E) n := rfl

/-- The coordinate law introduced in this module is definitionally the same
law used by the Gram-moment Fubini assembly. -/
theorem standardRealGaussianVector_eq_measure (k : ℕ) :
    standardRealGaussianVector k = standardRealGaussianVectorMeasure k := rfl

theorem inner_toLp_eq_bilinearDot {k : ℕ} (g h : Fin k → ℝ) :
    inner ℝ (WithLp.toLp 2 g) (WithLp.toLp 2 h) = bilinearDot g h := by
  rw [EuclideanSpace.inner_toLp_toLp]
  unfold dotProduct bilinearDot
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

/-- Pushing the two coordinate Gaussian fields into Euclidean space gives
the product of two standard multivariate Gaussian laws. -/
theorem map_twoRealFields_toLp_eq_prod_stdGaussian (k : ℕ) :
    Measure.map
        (Prod.map (WithLp.toLp 2) (WithLp.toLp 2))
        (twoRealGaussianFieldsMeasure k) =
      (stdGaussian (EuclideanSpace ℝ (Fin k))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  unfold twoRealGaussianFieldsMeasure standardRealGaussianVectorMeasure
  have h := (Measure.map_prod_map
    (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1)
    (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1)
    (by fun_prop : Measurable (WithLp.toLp 2 :
      (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)))
    (by fun_prop : Measurable (WithLp.toLp 2 :
      (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)))).symm
  simpa only [map_pi_eq_stdGaussian] using h

/-- **Exact rank-one endpoint used by the M1 assembly.**  For two iid
standard real Gaussian coordinate fields in dimension `k > 0`, the even
moment of their bilinear dot product is `closedFirstMoment k n`. -/
theorem integral_bilinearDot_pow_two_mul_twoRealGaussianFieldsMeasure
    (k n : ℕ) (hk : 0 < k) :
    (∫ w : TwoRealFields k, bilinearDot w.1 w.2 ^ (2 * n)
        ∂twoRealGaussianFieldsMeasure k) =
      closedFirstMoment k n := by
  let E := EuclideanSpace ℝ (Fin k)
  let T : TwoRealFields k → E × E :=
    Prod.map (WithLp.toLp 2) (WithLp.toLp 2)
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  letI : Nontrivial E := inferInstance
  have hmap : Measure.map T (twoRealGaussianFieldsMeasure k) =
      (stdGaussian E).prod (stdGaussian E) := by
    simpa only [T, E] using map_twoRealFields_toLp_eq_prod_stdGaussian k
  calc
    (∫ w : TwoRealFields k, bilinearDot w.1 w.2 ^ (2 * n)
        ∂twoRealGaussianFieldsMeasure k) =
        ∫ w : TwoRealFields k,
          inner ℝ (WithLp.toLp 2 w.1) (WithLp.toLp 2 w.2) ^ (2 * n)
            ∂twoRealGaussianFieldsMeasure k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        exact congrArg (· ^ (2 * n))
          (inner_toLp_eq_bilinearDot w.1 w.2).symm
    _ = ∫ z : E × E, inner ℝ z.1 z.2 ^ (2 * n)
          ∂Measure.map T (twoRealGaussianFieldsMeasure k) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ∫ z : E × E, inner ℝ z.1 z.2 ^ (2 * n)
          ∂((stdGaussian E).prod (stdGaussian E)) := by rw [hmap]
    _ = closedFirstMoment (Module.finrank ℝ E) n :=
      integral_inner_prod_pow_two_mul_stdGaussian (E := E) n
    _ = closedFirstMoment k n := by
      simp [E]

end

end LogdetLean.GramHafnian
