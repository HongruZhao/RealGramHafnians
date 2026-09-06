import LogdetLean.GramHafnian.RankOneGaussianBilinear
import LogdetLean.GramHafnian.FiniteHypergeometric
import LogdetLean.Coherence.RubenCoordinates
import LogdetLean.WishartBetaGammaFactors
import LogdetLean.BetaMellin
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-!
# The radial--angular outer moment for the rank-two Gram kernel

This module proves the exact outer Gaussian moment which turns the
rank-two conditional calculation into the finite Gram--hafnian correction.
For two independent standard Gaussian vectors `g₁,g₂` in dimension `k ≥ 2`,
their two squared radii are independent of their squared angle.  The latter
has the exact `Beta(1/2,(k-1)/2)` law.  Consequently

`E[(‖g₁‖² ‖g₂‖²)^n corr(g₁,g₂)^(2j)]
   = dimensionProduct(k,n)^2 * pochhammerRatio(k,j)`.

The proof is measure-theoretic rather than an appeal to a polar-coordinate
heuristic.  Ruben coordinates split the second vector into one Gaussian
coordinate and an orthogonal Gamma energy; the proved Beta--Gamma change of
variables then gives the joint product law.  No project axiom is used.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory Module

namespace LogdetLean.GramHafnian

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Square the axial Gaussian coordinate and apply the Beta--Gamma
change of variables to it and the residual energy. -/
def squareBetaGammaTransform (z : ℝ × ℝ) : ℝ × ℝ :=
  LogdetLean.betaGammaCoord (z.1 ^ 2, z.2)

theorem measurable_squareBetaGammaTransform :
    Measurable squareBetaGammaTransform := by
  unfold squareBetaGammaTransform
  change Measurable (fun z : ℝ × ℝ ↦
    (z.1 ^ 2 / (z.1 ^ 2 + z.2), z.1 ^ 2 + z.2))
  fun_prop

/-- The scalar Ruben coordinates `(Z,Q)` transform exactly into an
independent squared angle and full squared radius. -/
theorem map_squareBetaGammaTransform_gaussian_gamma
    (k : ℕ) (hk : 2 ≤ k) :
    Measure.map squareBetaGammaTransform
        ((gaussianReal 0 1).prod
          (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2))) =
      (betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)).prod
        (gammaMeasure ((k : ℝ) / 2) (1 / 2)) := by
  let _ : SFinite
      (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2)) := by
    unfold gammaMeasure
    infer_instance
  let sqFirst : ℝ × ℝ → ℝ × ℝ :=
    Prod.map (fun z : ℝ ↦ z ^ 2) id
  have hsqFirst : Measurable sqFirst := by
    exact (by fun_prop : Measurable (fun z : ℝ ↦ z ^ 2)).prodMap measurable_id
  have hmapSq :
      Measure.map sqFirst
          ((gaussianReal 0 1).prod
            (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2))) =
        (gammaMeasure (1 / 2) (1 / 2)).prod
          (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2)) := by
    have h := (Measure.map_prod_map
      (gaussianReal 0 1)
      (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2))
      (by fun_prop : Measurable (fun z : ℝ ↦ z ^ 2))
      measurable_id).symm
    simpa only [sqFirst, LogdetLean.map_sq_gaussianReal_zero_one,
      Measure.map_id] using h
  have hres : 0 < (((k - 1 : ℕ) : ℝ) / 2) := by
    have hk1 : 0 < k - 1 := by omega
    exact div_pos (by exact_mod_cast hk1) (by norm_num)
  have hbetaGamma := LogdetLean.map_betaGammaCoord_prod_gamma_eq_prod_beta_gamma
    (a := (1 / 2 : ℝ))
    (b := (((k - 1 : ℕ) : ℝ) / 2))
    (r := (1 / 2 : ℝ))
    (by norm_num) hres (by norm_num)
  have hshape :
      (1 / 2 : ℝ) + (((k - 1 : ℕ) : ℝ) / 2) = (k : ℝ) / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  calc
    Measure.map squareBetaGammaTransform
        ((gaussianReal 0 1).prod
          (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2))) =
        Measure.map LogdetLean.betaGammaCoord
          (Measure.map sqFirst
            ((gaussianReal 0 1).prod
              (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2)))) := by
      rw [Measure.map_map (by
        change Measurable (fun q : ℝ × ℝ ↦
          (q.1 / (q.1 + q.2), q.1 + q.2))
        fun_prop) hsqFirst]
      rfl
    _ = Measure.map LogdetLean.betaGammaCoord
          ((gammaMeasure (1 / 2) (1 / 2)).prod
            (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2))) := by
      rw [hmapSq]
    _ = (betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)).prod
          (gammaMeasure
            ((1 / 2 : ℝ) + (((k - 1 : ℕ) : ℝ) / 2)) (1 / 2)) :=
      hbetaGamma
    _ = (betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)).prod
          (gammaMeasure ((k : ℝ) / 2) (1 / 2)) := by rw [hshape]

/-- The three variables needed in the outer moment: first squared radius,
squared normalized inner product, and second squared radius. -/
def gaussianPairRadialAngleCoordinates (z : E × E) : ℝ × (ℝ × ℝ) :=
  (‖z.1‖ ^ 2,
    (LogdetLean.Coherence.squaredNormalizedInner (E := E) z.1 z.2,
      ‖z.2‖ ^ 2))

theorem measurable_gaussianPairRadialAngleCoordinates :
    Measurable (gaussianPairRadialAngleCoordinates : E × E → ℝ × (ℝ × ℝ)) := by
  unfold gaussianPairRadialAngleCoordinates
  exact (measurable_fst.norm.pow_const 2).prodMk
    ((LogdetLean.Coherence.measurable_uncurry_squaredNormalizedInner
      (E := E)).prodMk
      (measurable_snd.norm.pow_const 2))

/-- Algebraic identification of the squared angle with the Beta--Gamma ratio
in Ruben coordinates.  The totalized zero-axis case is included. -/
theorem squaredNormalizedInner_eq_axisEnergyRatio (u v : E) :
    LogdetLean.Coherence.squaredNormalizedInner (E := E) u v =
      LogdetLean.Coherence.gaussianAxisCoordinate (E := E) u v ^ 2 /
        (LogdetLean.Coherence.gaussianAxisCoordinate (E := E) u v ^ 2 +
          LogdetLean.Coherence.gaussianAxisResidualEnergy (E := E) u v) := by
  by_cases hu : u = 0
  · subst u
    simp [LogdetLean.Coherence.squaredNormalizedInner,
      LogdetLean.Coherence.gaussianAxisCoordinate,
      LogdetLean.Coherence.gaussianAxisResidualEnergy]
  · have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    unfold LogdetLean.Coherence.squaredNormalizedInner
    unfold LogdetLean.Coherence.gaussianAxisResidualEnergy
    unfold LogdetLean.Coherence.gaussianAxisCoordinate
    rw [add_sub_cancel]
    by_cases hv : v = 0
    · subst v
      simp
    · have hnormv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      field_simp [hnorm, hnormv]

/-- Applying the deterministic Beta--Gamma transform to retained Ruben
coordinates gives exactly the radial--angle coordinate map. -/
theorem radialAngleCoordinates_eq_transform_ruben :
    (gaussianPairRadialAngleCoordinates : E × E → ℝ × (ℝ × ℝ)) =
      (Prod.map (fun u : E ↦ ‖u‖ ^ 2) squareBetaGammaTransform) ∘
        LogdetLean.Coherence.retainFirstAndGaussianAxisCoordinates := by
  funext z
  apply Prod.ext
  · simp [gaussianPairRadialAngleCoordinates, Function.comp_def,
      LogdetLean.Coherence.retainFirstAndGaussianAxisCoordinates]
  · apply Prod.ext
    · change LogdetLean.Coherence.squaredNormalizedInner (E := E) z.1 z.2 =
        LogdetLean.Coherence.gaussianAxisCoordinate (E := E) z.1 z.2 ^ 2 /
          (LogdetLean.Coherence.gaussianAxisCoordinate (E := E) z.1 z.2 ^ 2 +
            LogdetLean.Coherence.gaussianAxisResidualEnergy (E := E) z.1 z.2)
      exact squaredNormalizedInner_eq_axisEnergyRatio z.1 z.2
    · simp [gaussianPairRadialAngleCoordinates, Function.comp_def,
        squareBetaGammaTransform, LogdetLean.betaGammaCoord_apply,
        LogdetLean.Coherence.retainFirstAndGaussianAxisCoordinates,
        LogdetLean.Coherence.gaussianAxisCoordinates,
        LogdetLean.Coherence.gaussianAxisResidualEnergy]

/-- **Exact joint radial--angular product law.**  In dimension `k ≥ 2`,
the two Gaussian squared radii are mutually independent of the squared angle,
whose law is `Beta(1/2,(k-1)/2)`. -/
theorem map_gaussianPairRadialAngleCoordinates_gaussianProduct
    (k : ℕ) (hdim : finrank ℝ E = k) (hk : 2 ≤ k) :
    Measure.map (gaussianPairRadialAngleCoordinates : E × E → ℝ × (ℝ × ℝ))
        ((stdGaussian E).prod (stdGaussian E)) =
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)).prod
        ((betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)).prod
          (gammaMeasure ((k : ℝ) / 2) (1 / 2))) := by
  let _ : SFinite
      (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2)) := by
    unfold gammaMeasure
    infer_instance
  let F : E × (ℝ × ℝ) → ℝ × (ℝ × ℝ) :=
    Prod.map (fun u : E ↦ ‖u‖ ^ 2) squareBetaGammaTransform
  have hF : Measurable F := by
    exact (by fun_prop : Measurable (fun u : E ↦ ‖u‖ ^ 2)).prodMap
      measurable_squareBetaGammaTransform
  have hret :=
    LogdetLean.Coherence.map_retainFirstAndGaussianAxisCoordinates_gaussianProduct
      (E := E) k hdim hk
  have hnormSq :
      Measure.map (fun u : E ↦ ‖u‖ ^ 2) (stdGaussian E) =
        gammaMeasure ((k : ℝ) / 2) (1 / 2) := by
    let _ : Nontrivial E :=
      Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
    have h := (LogdetLean.hasLaw_normSq_stdGaussian E).map_eq
    rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma E] at h
    simpa [hdim] using h
  have hscalar := map_squareBetaGammaTransform_gaussian_gamma k hk
  calc
    Measure.map (gaussianPairRadialAngleCoordinates : E × E → ℝ × (ℝ × ℝ))
        ((stdGaussian E).prod (stdGaussian E)) =
        Measure.map F
          (Measure.map
            LogdetLean.Coherence.retainFirstAndGaussianAxisCoordinates
            ((stdGaussian E).prod (stdGaussian E))) := by
      rw [Measure.map_map hF
        LogdetLean.Coherence.measurable_retainFirstAndGaussianAxisCoordinates]
      rw [radialAngleCoordinates_eq_transform_ruben]
    _ = Measure.map F
          ((stdGaussian E).prod
            ((gaussianReal 0 1).prod
              (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2)))) := by
      rw [hret]
    _ = (Measure.map (fun u : E ↦ ‖u‖ ^ 2) (stdGaussian E)).prod
          (Measure.map squareBetaGammaTransform
            ((gaussianReal 0 1).prod
              (gammaMeasure (((k - 1 : ℕ) : ℝ) / 2) (1 / 2)))) := by
      exact (Measure.map_prod_map _ _ (by fun_prop)
        measurable_squareBetaGammaTransform).symm
    _ = (gammaMeasure ((k : ℝ) / 2) (1 / 2)).prod
          ((betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)).prod
            (gammaMeasure ((k : ℝ) / 2) (1 / 2))) := by
      rw [hnormSq, hscalar]

/-- Gamma shifted by a natural number is the rising Pochhammer factor times
the original Gamma value. -/
theorem gamma_add_nat_eq_rising_mul (a : ℝ) (j : ℕ) (ha : 0 < a) :
    Real.Gamma (a + j) = rising a j * Real.Gamma a := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.cast_succ]
      rw [show a + ((j : ℝ) + 1) = (a + (j : ℝ)) + 1 by ring,
        Real.Gamma_add_one (by positivity : a + (j : ℝ) ≠ 0),
        rising_succ, ih]
      ring

/-- Natural moments of a positive-parameter Beta law, in rising-factorial
form. -/
theorem integral_pow_betaMeasure_eq_rising_ratio
    (a b : ℝ) (j : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ, x ^ j ∂betaMeasure a b) =
      rising a j / rising (a + b) j := by
  rw [show (fun x : ℝ ↦ x ^ j) = (fun x : ℝ ↦ x ^ (j : ℝ)) by
    funext x
    exact (Real.rpow_natCast x j).symm]
  rw [LogdetLean.integral_rpow_betaMeasure ha hb (by positivity)]
  change
    (Real.Gamma (a + j) * Real.Gamma b /
        Real.Gamma (a + j + b)) /
      (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) = _
  rw [gamma_add_nat_eq_rising_mul a j ha]
  have hab : 0 < a + b := add_pos ha hb
  rw [show a + (j : ℝ) + b = (a + b) + j by ring,
    gamma_add_nat_eq_rising_mul (a + b) j hab]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hGab : Real.Gamma (a + b) ≠ 0 := (Real.Gamma_pos_of_pos hab).ne'
  have hra : rising a j ≠ 0 := ne_of_gt (rising_pos ha j)
  have hrab : rising (a + b) j ≠ 0 := ne_of_gt (rising_pos hab j)
  field_simp [hGa, hGb, hGab, hra, hrab]

/-- The squared-angle Beta moment is exactly the finite correction's
Pochhammer ratio. -/
theorem integral_pow_squaredAngleBeta_eq_pochhammerRatio
    (k j : ℕ) (hk : 2 ≤ k) :
    (∫ x : ℝ, x ^ j
        ∂betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)) =
      pochhammerRatio k j := by
  have hres : 0 < (((k - 1 : ℕ) : ℝ) / 2) := by
    have hk1 : 0 < k - 1 := by omega
    exact div_pos (by exact_mod_cast hk1) (by norm_num)
  rw [integral_pow_betaMeasure_eq_rising_ratio
    (1 / 2) (((k - 1 : ℕ) : ℝ) / 2) j (by norm_num) hres]
  have hshape :
      (1 / 2 : ℝ) + (((k - 1 : ℕ) : ℝ) / 2) = (k : ℝ) / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  rw [hshape]
  exact half_rising_div_dimension_rising k j (by omega)

/-- **Outer radial--angle moment.**  This is the exact factor consumed by
the rank-two conditional Gaussian calculation. -/
theorem integral_radialAngleMonomial_gaussianProduct
    (k n j : ℕ) (hdim : finrank ℝ E = k) (hk : 2 ≤ k) :
    (∫ z : E × E,
        (‖z.1‖ ^ 2 * ‖z.2‖ ^ 2) ^ n *
          LogdetLean.Coherence.squaredNormalizedInner (E := E) z.1 z.2 ^ j
        ∂((stdGaussian E).prod (stdGaussian E))) =
      dimensionProduct k n ^ 2 * pochhammerRatio k j := by
  let _ : SFinite (gammaMeasure ((k : ℝ) / 2) (1 / 2)) := by
    unfold gammaMeasure
    infer_instance
  let _ : SFinite
      (betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)) := by
    unfold betaMeasure
    infer_instance
  let target : Measure (ℝ × (ℝ × ℝ)) :=
    (gammaMeasure ((k : ℝ) / 2) (1 / 2)).prod
      ((betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)).prod
        (gammaMeasure ((k : ℝ) / 2) (1 / 2)))
  let f : ℝ × (ℝ × ℝ) → ℝ := fun q ↦
    (q.1 * q.2.2) ^ n * q.2.1 ^ j
  have hmap := map_gaussianPairRadialAngleCoordinates_gaussianProduct
    (E := E) k hdim hk
  have hpush :
      (∫ z : E × E, f (gaussianPairRadialAngleCoordinates z)
          ∂((stdGaussian E).prod (stdGaussian E))) =
        ∫ q, f q ∂target := by
    calc
      (∫ z : E × E, f (gaussianPairRadialAngleCoordinates z)
          ∂((stdGaussian E).prod (stdGaussian E))) =
          ∫ q, f q
            ∂Measure.map gaussianPairRadialAngleCoordinates
              ((stdGaussian E).prod (stdGaussian E)) := by
        rw [integral_map
          measurable_gaussianPairRadialAngleCoordinates.aemeasurable
          (by unfold f; fun_prop)]
      _ = ∫ q, f q ∂target := by
        rw [hmap]
  rw [show (fun z : E × E ↦
      (‖z.1‖ ^ 2 * ‖z.2‖ ^ 2) ^ n *
        LogdetLean.Coherence.squaredNormalizedInner (E := E) z.1 z.2 ^ j) =
      fun z ↦ f (gaussianPairRadialAngleCoordinates z) by rfl]
  rw [hpush]
  change
    (∫ q : ℝ × (ℝ × ℝ),
        (q.1 * q.2.2) ^ n * q.2.1 ^ j ∂target) = _
  rw [show (fun q : ℝ × (ℝ × ℝ) ↦
      (q.1 * q.2.2) ^ n * q.2.1 ^ j) =
      fun q ↦ q.1 ^ n * (q.2.1 ^ j * q.2.2 ^ n) by
    funext q
    rw [mul_pow]
    ring]
  unfold target
  calc
    (∫ q : ℝ × (ℝ × ℝ),
        q.1 ^ n * (q.2.1 ^ j * q.2.2 ^ n)
          ∂(gammaMeasure ((k : ℝ) / 2) (1 / 2)).prod
            ((betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)).prod
              (gammaMeasure ((k : ℝ) / 2) (1 / 2)))) =
        (∫ q : ℝ, q ^ n ∂gammaMeasure ((k : ℝ) / 2) (1 / 2)) *
          (∫ q : ℝ × ℝ, q.1 ^ j * q.2 ^ n
            ∂(betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)).prod
              (gammaMeasure ((k : ℝ) / 2) (1 / 2))) :=
      integral_prod_mul (fun q : ℝ ↦ q ^ n)
        (fun q : ℝ × ℝ ↦ q.1 ^ j * q.2 ^ n)
    _ = (∫ q : ℝ, q ^ n ∂gammaMeasure ((k : ℝ) / 2) (1 / 2)) *
          ((∫ u : ℝ, u ^ j
              ∂betaMeasure (1 / 2) (((k - 1 : ℕ) : ℝ) / 2)) *
            (∫ q : ℝ, q ^ n ∂gammaMeasure ((k : ℝ) / 2) (1 / 2))) := by
      rw [integral_prod_mul (fun u : ℝ ↦ u ^ j) (fun q : ℝ ↦ q ^ n)]
    _ = dimensionProduct k n ^ 2 * pochhammerRatio k j := by
      rw [integral_pow_gammaMeasure_half_eq_dimensionProduct k n (by omega),
        integral_pow_squaredAngleBeta_eq_pochhammerRatio k j hk]
      ring

/-- The raw norm/inner-product monomial in the conditional rank-two
expansion is exactly the radial--angle monomial.  The statement includes the
zero-vector cases, where normalized inner products are totalized. -/
theorem innerMonomial_eq_radialAngleMonomial
    (u v : E) (n j : ℕ) (hj : j ≤ n) :
    (‖u‖ ^ 2 * ‖v‖ ^ 2) ^ (n - j) * (inner ℝ u v) ^ (2 * j) =
      (‖u‖ ^ 2 * ‖v‖ ^ 2) ^ n *
        LogdetLean.Coherence.squaredNormalizedInner (E := E) u v ^ j := by
  cases j with
  | zero => simp
  | succ j =>
      have hn : n ≠ 0 := by omega
      by_cases hu : u = 0
      · subst u
        simp [LogdetLean.Coherence.squaredNormalizedInner, hn]
      · by_cases hv : v = 0
        · subst v
          simp [LogdetLean.Coherence.squaredNormalizedInner, hn]
        · have hnormu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
          have hnormv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
          have hq : ‖u‖ ^ 2 * ‖v‖ ^ 2 ≠ 0 := by
            exact mul_ne_zero (pow_ne_zero _ hnormu) (pow_ne_zero _ hnormv)
          unfold LogdetLean.Coherence.squaredNormalizedInner
          rw [div_pow, ← pow_mul, div_eq_mul_inv,
            pow_sub₀ (‖u‖ ^ 2 * ‖v‖ ^ 2) hq hj]
          ring

/-- Raw outer monomial form, directly matching the squared-binomial
conditional rank-two formula. -/
theorem integral_innerMonomial_gaussianProduct
    (k n j : ℕ) (hdim : finrank ℝ E = k) (hk : 2 ≤ k) (hj : j ≤ n) :
    (∫ z : E × E,
        (‖z.1‖ ^ 2 * ‖z.2‖ ^ 2) ^ (n - j) *
          (inner ℝ z.1 z.2) ^ (2 * j)
        ∂((stdGaussian E).prod (stdGaussian E))) =
      dimensionProduct k n ^ 2 * pochhammerRatio k j := by
  calc
    (∫ z : E × E,
        (‖z.1‖ ^ 2 * ‖z.2‖ ^ 2) ^ (n - j) *
          (inner ℝ z.1 z.2) ^ (2 * j)
        ∂((stdGaussian E).prod (stdGaussian E))) =
        ∫ z : E × E,
          (‖z.1‖ ^ 2 * ‖z.2‖ ^ 2) ^ n *
            LogdetLean.Coherence.squaredNormalizedInner (E := E) z.1 z.2 ^ j
          ∂((stdGaussian E).prod (stdGaussian E)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦
        innerMonomial_eq_radialAngleMonomial z.1 z.2 n j hj
    _ = dimensionProduct k n ^ 2 * pochhammerRatio k j :=
      integral_radialAngleMonomial_gaussianProduct k n j hdim hk

end

end LogdetLean.GramHafnian
