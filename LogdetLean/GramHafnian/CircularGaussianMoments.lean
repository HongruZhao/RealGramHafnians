import LogdetLean.GramHafnian.GaussianEvenMoments
import LogdetLean.GramHafnian.ComplexProductMoments
/-!
# A standard circular complex Gaussian and its required scalar moments

We realize a circular complex Gaussian literally as `(X + iY) / sqrt 2`,
where `X,Y` are independent standard real Gaussians.  The moment identities
below are proved by pushforward and finite product integration; none is an
assumed Wick rule.
-/

open scoped ComplexConjugate
open MeasureTheory ProbabilityTheory Complex

namespace LogdetLean.GramHafnian

noncomputable section

/-- The real-pair realization of one standard circular complex coordinate. -/
def circularGaussianCoordinate (q : ℝ × ℝ) : ℂ :=
  ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) / (Real.sqrt 2 : ℝ)

@[fun_prop]
theorem measurable_circularGaussianCoordinate :
    Measurable circularGaussianCoordinate := by
  unfold circularGaussianCoordinate
  fun_prop

/-- The standard circular complex Gaussian law, with `E |Z|² = 1`. -/
def circularGaussian : Measure ℂ :=
  Measure.map circularGaussianCoordinate
    ((gaussianReal 0 1).prod (gaussianReal 0 1))

instance : IsProbabilityMeasure circularGaussian := by
  unfold circularGaussian
  exact Measure.isProbabilityMeasure_map
    measurable_circularGaussianCoordinate.aemeasurable

instance : SigmaFinite circularGaussian := inferInstance

theorem integral_circularGaussian_eq_pair
    (f : ℂ → ℂ) (hf : AEStronglyMeasurable f circularGaussian) :
    ∫ z, f z ∂circularGaussian =
      ∫ q : ℝ × ℝ, f (circularGaussianCoordinate q)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  rw [circularGaussian, integral_map (by fun_prop) hf]

/-- A real product monomial, viewed in `ℂ`, is integrable under the two-real-
Gaussian source law. -/
theorem integrable_pair_complex_monomial (a b : ℕ) :
    Integrable (fun q : ℝ × ℝ ↦ ((q.1 ^ a * q.2 ^ b : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  exact ((integrable_pow_gaussianReal a).mul_prod
    (integrable_pow_gaussianReal b)).ofReal

/-- Factorization of real-coordinate monomials under the source law. -/
theorem integral_pair_complex_monomial (a b : ℕ) :
    (∫ q : ℝ × ℝ, ((q.1 ^ a * q.2 ^ b : ℝ) : ℂ)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
      Complex.ofReal (∫ x : ℝ, x ^ a ∂gaussianReal 0 1) *
        Complex.ofReal (∫ y : ℝ, y ^ b ∂gaussianReal 0 1) := by
  have hfun :
      (fun q : ℝ × ℝ ↦ ((q.1 ^ a * q.2 ^ b : ℝ) : ℂ)) =
        fun q ↦ ((q.1 ^ a : ℝ) : ℂ) * ((q.2 ^ b : ℝ) : ℂ) := by
    funext q
    norm_num
  rw [hfun]
  have hp := integral_prod_mul
    (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x : ℝ ↦ ((x ^ a : ℝ) : ℂ))
    (fun y : ℝ ↦ ((y ^ b : ℝ) : ℂ))
  calc
    (∫ q : ℝ × ℝ, ((q.1 ^ a : ℝ) : ℂ) * ((q.2 ^ b : ℝ) : ℂ)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
        (∫ x : ℝ, ((x ^ a : ℝ) : ℂ) ∂gaussianReal 0 1) *
          (∫ y : ℝ, ((y ^ b : ℝ) : ℂ) ∂gaussianReal 0 1) := hp
    _ = Complex.ofReal (∫ x : ℝ, x ^ a ∂gaussianReal 0 1) *
          Complex.ofReal (∫ y : ℝ, y ^ b ∂gaussianReal 0 1) := by
      rw [integral_complex_ofReal, integral_complex_ofReal]

/-- The circular coordinate has mean zero. -/
theorem integral_id_circularGaussian :
    (∫ z : ℂ, z ∂circularGaussian) = 0 := by
  rw [integral_circularGaussian_eq_pair (fun z : ℂ ↦ z) (by fun_prop)]
  have h10 := integral_pair_complex_monomial 1 0
  have h01 := integral_pair_complex_monomial 0 1
  have hoddR : (∫ x : ℝ, x ^ 1 ∂gaussianReal 0 1) = 0 := by
    simpa using integral_pow_odd_gaussianReal 0
  have honeR : (∫ x : ℝ, x ^ 0 ∂gaussianReal 0 1) = 1 := by simp
  rw [hoddR, honeR] at h10 h01
  norm_num at h10 h01
  rw [show (fun q : ℝ × ℝ ↦ circularGaussianCoordinate q) =
      fun q ↦ (1 / (Real.sqrt 2 : ℂ)) *
        (((q.1 : ℂ)) + Complex.I * (q.2 : ℂ)) by
    funext q
    simp [circularGaussianCoordinate, div_eq_mul_inv]
    ring]
  rw [integral_const_mul]
  have hx : Integrable (fun q : ℝ × ℝ ↦ (q.1 : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 1 0
  have hy : Integrable (fun q : ℝ × ℝ ↦ Complex.I * (q.2 : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have h : Integrable (fun q : ℝ × ℝ ↦ (q.2 : ℂ))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      simpa using integrable_pair_complex_monomial 0 1
    exact h.const_mul _
  rw [integral_add hx hy, integral_const_mul]
  have hx0 : (∫ q : ℝ × ℝ, (q.1 : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
    simpa using h10
  have hy0 : (∫ q : ℝ × ℝ, (q.2 : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
    simpa using h01
  rw [hx0, hy0]
  ring

/-- Pointwise squared-modulus formula for the real-pair realization. -/
theorem circularGaussianCoordinate_mul_conj (q : ℝ × ℝ) :
    circularGaussianCoordinate q * conj (circularGaussianCoordinate q) =
      (((q.1 ^ 2 + q.2 ^ 2) / 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj]
  simp only [circularGaussianCoordinate, Complex.normSq_div,
    Complex.normSq_add_mul_I, Complex.normSq_ofReal]
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [← pow_two (Real.sqrt 2), hs]

/-- Pointwise fourth radial moment formula. -/
theorem circularGaussianCoordinate_sq_mul_conj_sq (q : ℝ × ℝ) :
    circularGaussianCoordinate q ^ 2 * conj (circularGaussianCoordinate q) ^ 2 =
      ((((q.1 ^ 2 + q.2 ^ 2) ^ 2) / 4 : ℝ) : ℂ) := by
  calc
    circularGaussianCoordinate q ^ 2 * conj (circularGaussianCoordinate q) ^ 2 =
        (circularGaussianCoordinate q * conj (circularGaussianCoordinate q)) ^ 2 := by
      ring
    _ = ((((q.1 ^ 2 + q.2 ^ 2) / 2 : ℝ) : ℂ)) ^ 2 := by
      rw [circularGaussianCoordinate_mul_conj]
    _ = ((((q.1 ^ 2 + q.2 ^ 2) ^ 2) / 4 : ℝ) : ℂ) := by
      norm_num
      ring

/-- Pointwise holomorphic-square expansion. -/
theorem circularGaussianCoordinate_sq (q : ℝ × ℝ) :
    circularGaussianCoordinate q ^ 2 =
      ((((q.1 ^ 2 - q.2 ^ 2) / 2 : ℝ) : ℂ) +
        Complex.I * ((q.1 * q.2 : ℝ) : ℂ)) := by
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsC : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
  rw [circularGaussianCoordinate, div_pow, hsC]
  field_simp
  simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  simp only [Complex.ofReal_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem integral_sq_gaussianReal_eq_one :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  simpa using integral_pow_two_gaussianReal 1

private theorem integral_fourth_gaussianReal_eq_three :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  simpa using integral_pow_two_gaussianReal 2

/-- Exact unit variance of the standard circular complex Gaussian. -/
theorem integral_mul_conj_circularGaussian :
    (∫ z : ℂ, z * conj z ∂circularGaussian) = 1 := by
  rw [integral_circularGaussian_eq_pair
    (fun z : ℂ ↦ z * conj z) (by fun_prop)]
  simp_rw [circularGaussianCoordinate_mul_conj]
  have h20 := integral_pair_complex_monomial 2 0
  have h02 := integral_pair_complex_monomial 0 2
  have h0 : (∫ x : ℝ, x ^ 0 ∂gaussianReal 0 1) = 1 := by simp
  rw [integral_sq_gaussianReal_eq_one, h0] at h20 h02
  norm_num at h20 h02
  have hx : Integrable (fun q : ℝ × ℝ ↦ ((q.1 ^ 2 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 2 0
  have hy : Integrable (fun q : ℝ × ℝ ↦ ((q.2 ^ 2 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 0 2
  rw [show (fun q : ℝ × ℝ ↦ ((((q.1 ^ 2 + q.2 ^ 2) / 2 : ℝ) : ℂ))) =
      fun q ↦ (1 / 2 : ℂ) * (((q.1 ^ 2 : ℝ) : ℂ) + ((q.2 ^ 2 : ℝ) : ℂ)) by
    funext q
    norm_num
    ring]
  rw [integral_const_mul, integral_add hx hy]
  have hxInt : (∫ q : ℝ × ℝ, ((q.1 ^ 2 : ℝ) : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 1 := by
    simpa using h20
  have hyInt : (∫ q : ℝ × ℝ, ((q.2 ^ 2 : ℝ) : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 1 := by
    simpa using h02
  rw [hxInt, hyInt]
  norm_num

/-- The holomorphic second moment of a circular Gaussian vanishes. -/
theorem integral_sq_circularGaussian :
    (∫ z : ℂ, z ^ 2 ∂circularGaussian) = 0 := by
  rw [integral_circularGaussian_eq_pair (fun z : ℂ ↦ z ^ 2) (by fun_prop)]
  simp_rw [circularGaussianCoordinate_sq]
  have h20 := integral_pair_complex_monomial 2 0
  have h02 := integral_pair_complex_monomial 0 2
  have h11 := integral_pair_complex_monomial 1 1
  have h0 : (∫ x : ℝ, x ^ 0 ∂gaussianReal 0 1) = 1 := by simp
  have h1 : (∫ x : ℝ, x ^ 1 ∂gaussianReal 0 1) = 0 := by
    simpa using integral_pow_odd_gaussianReal 0
  rw [integral_sq_gaussianReal_eq_one, h0] at h20 h02
  rw [h1] at h11
  norm_num at h20 h02 h11
  have hx : Integrable (fun q : ℝ × ℝ ↦ ((q.1 ^ 2 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 2 0
  have hy : Integrable (fun q : ℝ × ℝ ↦ ((q.2 ^ 2 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 0 2
  have hxy : Integrable (fun q : ℝ × ℝ ↦ ((q.1 * q.2 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 1 1
  have hdiff : Integrable (fun q : ℝ × ℝ ↦
      (1 / 2 : ℂ) * (((q.1 ^ 2 : ℝ) : ℂ) - ((q.2 ^ 2 : ℝ) : ℂ)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (hx.sub hy).const_mul _
  rw [show (fun q : ℝ × ℝ ↦
      ((((q.1 ^ 2 - q.2 ^ 2) / 2 : ℝ) : ℂ) +
        Complex.I * ((q.1 * q.2 : ℝ) : ℂ))) =
      fun q ↦ (1 / 2 : ℂ) *
          (((q.1 ^ 2 : ℝ) : ℂ) - ((q.2 ^ 2 : ℝ) : ℂ)) +
        Complex.I * ((q.1 * q.2 : ℝ) : ℂ) by
    funext q
    norm_num
    ring]
  rw [integral_add hdiff (hxy.const_mul _), integral_const_mul,
    integral_sub hx hy, integral_const_mul]
  have hxInt : (∫ q : ℝ × ℝ, ((q.1 ^ 2 : ℝ) : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 1 := by simpa using h20
  have hyInt : (∫ q : ℝ × ℝ, ((q.2 ^ 2 : ℝ) : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 1 := by simpa using h02
  have hxyInt : (∫ q : ℝ × ℝ, ((q.1 * q.2 : ℝ) : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by simpa using h11
  rw [hxInt, hyInt, hxyInt]
  ring

/-- Exact fourth radial moment `E |Z|⁴ = 2`. -/
theorem integral_sq_mul_conj_sq_circularGaussian :
    (∫ z : ℂ, z ^ 2 * conj z ^ 2 ∂circularGaussian) = 2 := by
  rw [integral_circularGaussian_eq_pair
    (fun z : ℂ ↦ z ^ 2 * conj z ^ 2) (by fun_prop)]
  simp_rw [circularGaussianCoordinate_sq_mul_conj_sq]
  have h40 := integral_pair_complex_monomial 4 0
  have h22 := integral_pair_complex_monomial 2 2
  have h04 := integral_pair_complex_monomial 0 4
  have h0 : (∫ x : ℝ, x ^ 0 ∂gaussianReal 0 1) = 1 := by simp
  rw [integral_fourth_gaussianReal_eq_three, h0] at h40
  rw [integral_sq_gaussianReal_eq_one] at h22
  rw [h0, integral_fourth_gaussianReal_eq_three] at h04
  norm_num at h40 h22 h04
  have hx4 : Integrable (fun q : ℝ × ℝ ↦ ((q.1 ^ 4 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 4 0
  have hx2y2 : Integrable (fun q : ℝ × ℝ ↦
      ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    integrable_pair_complex_monomial 2 2
  have hy4 : Integrable (fun q : ℝ × ℝ ↦ ((q.2 ^ 4 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 0 4
  rw [show (fun q : ℝ × ℝ ↦ ((((q.1 ^ 2 + q.2 ^ 2) ^ 2 / 4 : ℝ) : ℂ))) =
      fun q ↦ (1 / 4 : ℂ) *
        (((q.1 ^ 4 : ℝ) : ℂ) + 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ) +
          ((q.2 ^ 4 : ℝ) : ℂ)) by
    funext q
    norm_num
    ring]
  have hx4Int : (∫ q : ℝ × ℝ, ((q.1 ^ 4 : ℝ) : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 3 := by simpa using h40
  have hx2y2Int : (∫ q : ℝ × ℝ, ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 1 := by simpa using h22
  have hy4Int : (∫ q : ℝ × ℝ, ((q.2 ^ 4 : ℝ) : ℂ)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 3 := by simpa using h04
  have hmid : Integrable (fun q : ℝ × ℝ ↦
      (2 : ℂ) * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := hx2y2.const_mul 2
  have hsumInt :
      (∫ q : ℝ × ℝ,
        ((q.1 ^ 4 : ℝ) : ℂ) + 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ) +
          ((q.2 ^ 4 : ℝ) : ℂ)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 8 := by
    have hfirst := integral_add' hx4 hmid
    have hsecond := integral_add' (hx4.add hmid) hy4
    calc
      (∫ q : ℝ × ℝ,
          ((q.1 ^ 4 : ℝ) : ℂ) + 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ) +
            ((q.2 ^ 4 : ℝ) : ℂ)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
          (∫ q : ℝ × ℝ,
            ((q.1 ^ 4 : ℝ) : ℂ) + 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ)
            ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
          ∫ q : ℝ × ℝ, ((q.2 ^ 4 : ℝ) : ℂ)
            ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
              simpa only [Pi.add_apply] using hsecond
      _ = ((∫ q : ℝ × ℝ, ((q.1 ^ 4 : ℝ) : ℂ)
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
            ∫ q : ℝ × ℝ, 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ)
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
          ∫ q : ℝ × ℝ, ((q.2 ^ 4 : ℝ) : ℂ)
            ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
              rw [show (∫ q : ℝ × ℝ,
                ((q.1 ^ 4 : ℝ) : ℂ) + 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ)
                ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
                (∫ q : ℝ × ℝ, ((q.1 ^ 4 : ℝ) : ℂ)
                  ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
                ∫ q : ℝ × ℝ, 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ)
                  ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) by
                    simpa only [Pi.add_apply] using hfirst]
      _ = 8 := by
        rw [integral_const_mul, hx4Int, hx2y2Int, hy4Int]
        norm_num
  rw [integral_const_mul, hsumInt]
  norm_num

/-- The radial fourth monomial is integrable under the pushed-forward law. -/
theorem integrable_sq_mul_conj_sq_circularGaussian :
    Integrable (fun z : ℂ ↦ z ^ 2 * conj z ^ 2) circularGaussian := by
  rw [circularGaussian,
    integrable_map_measure (by fun_prop) measurable_circularGaussianCoordinate.aemeasurable]
  have hx4 : Integrable (fun q : ℝ × ℝ ↦ ((q.1 ^ 4 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 4 0
  have hx2y2 : Integrable (fun q : ℝ × ℝ ↦
      ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    integrable_pair_complex_monomial 2 2
  have hy4 : Integrable (fun q : ℝ × ℝ ↦ ((q.2 ^ 4 : ℝ) : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa using integrable_pair_complex_monomial 0 4
  have hpoly : Integrable (fun q : ℝ × ℝ ↦
      (1 / 4 : ℂ) *
        (((q.1 ^ 4 : ℝ) : ℂ) + 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ) +
          ((q.2 ^ 4 : ℝ) : ℂ)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ((hx4.add (hx2y2.const_mul 2)).add hy4).const_mul _
  apply hpoly.congr
  exact Filter.Eventually.of_forall fun q ↦ by
    change (1 / 4 : ℂ) *
        (((q.1 ^ 4 : ℝ) : ℂ) + 2 * ((q.1 ^ 2 * q.2 ^ 2 : ℝ) : ℂ) +
          ((q.2 ^ 4 : ℝ) : ℂ)) =
      circularGaussianCoordinate q ^ 2 * conj (circularGaussianCoordinate q) ^ 2
    rw [circularGaussianCoordinate_sq_mul_conj_sq]
    norm_num
    ring

/-- Every scalar mixed monomial needed by the one-column fourth contraction
is integrable.  The exponent restriction is exactly `a,b ≤ 2`. -/
theorem integrable_mixedComplexMonomial_circularGaussian
    (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
    Integrable (mixedComplexMonomial a b) circularGaussian := by
  have hdom : Integrable (fun z : ℂ ↦
      (1 : ℝ) + ‖z ^ 2 * conj z ^ 2‖) circularGaussian :=
    (integrable_const (1 : ℝ)).add
      integrable_sq_mul_conj_sq_circularGaussian.norm
  apply hdom.mono
  · unfold mixedComplexMonomial
    fun_prop
  · exact Filter.Eventually.of_forall fun z ↦ by
      rw [mixedComplexMonomial, norm_mul, norm_pow, norm_pow, norm_conj,
        ← pow_add]
      rw [Real.norm_of_nonneg (by positivity :
        0 ≤ (1 : ℝ) + ‖z ^ 2 * conj z ^ 2‖)]
      have hab : a + b ≤ 4 := by omega
      by_cases hz : ‖z‖ ≤ 1
      · calc
          ‖z‖ ^ (a + b) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
          _ ≤ 1 + ‖z ^ 2 * conj z ^ 2‖ :=
            le_add_of_nonneg_right (norm_nonneg _)
      · have hz1 : 1 ≤ ‖z‖ := le_of_not_ge hz
        calc
          ‖z‖ ^ (a + b) ≤ ‖z‖ ^ 4 := pow_le_pow_right₀ hz1 hab
          _ = ‖z ^ 2 * conj z ^ 2‖ := by
            rw [norm_mul, norm_pow, norm_pow, norm_conj]
            ring
          _ ≤ 1 + ‖z ^ 2 * conj z ^ 2‖ := le_add_of_nonneg_left zero_le_one

/-- The only unbalanced cubic moment needed by the four-index case split. -/
theorem integral_sq_mul_conj_circularGaussian :
    (∫ z : ℂ, z ^ 2 * conj z ∂circularGaussian) = 0 := by
  rw [integral_circularGaussian_eq_pair
    (fun z : ℂ ↦ z ^ 2 * conj z) (by fun_prop)]
  let f30 : ℝ × ℝ → ℂ := fun q ↦ ((q.1 ^ 3 : ℝ) : ℂ)
  let f12 : ℝ × ℝ → ℂ := fun q ↦ ((q.1 * q.2 ^ 2 : ℝ) : ℂ)
  let f21 : ℝ × ℝ → ℂ := fun q ↦ Complex.I * ((q.1 ^ 2 * q.2 : ℝ) : ℂ)
  let f03 : ℝ × ℝ → ℂ := fun q ↦ Complex.I * ((q.2 ^ 3 : ℝ) : ℂ)
  have hf30 : Integrable f30 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa [f30] using integrable_pair_complex_monomial 3 0
  have hf12 : Integrable f12 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa [f12] using integrable_pair_complex_monomial 1 2
  have hf21 : Integrable f21 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have hbase : Integrable (fun q : ℝ × ℝ ↦ ((q.1 ^ 2 * q.2 : ℝ) : ℂ))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      simpa using integrable_pair_complex_monomial 2 1
    simpa [f21] using hbase.const_mul Complex.I
  have hf03 : Integrable f03 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have hbase : Integrable (fun q : ℝ × ℝ ↦ ((q.2 ^ 3 : ℝ) : ℂ))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      simpa using integrable_pair_complex_monomial 0 3
    simpa [f03] using hbase.const_mul Complex.I
  have h1 : (∫ x : ℝ, x ^ 1 ∂gaussianReal 0 1) = 0 := by
    simpa using integral_pow_odd_gaussianReal 0
  have h3 : (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) = 0 := by
    simpa using integral_pow_odd_gaussianReal 1
  have h2 : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 :=
    integral_sq_gaussianReal_eq_one
  have h0 : (∫ x : ℝ, x ^ 0 ∂gaussianReal 0 1) = 1 := by simp
  have h30 := integral_pair_complex_monomial 3 0
  have h12 := integral_pair_complex_monomial 1 2
  have h21 := integral_pair_complex_monomial 2 1
  have h03 := integral_pair_complex_monomial 0 3
  rw [h3, h0] at h30
  rw [h1, h2] at h12
  rw [h2, h1] at h21
  rw [h0, h3] at h03
  norm_num at h30 h12 h21 h03
  have hi30 : (∫ q, f30 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
    simpa [f30] using h30
  have hi12 : (∫ q, f12 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
    simpa [f12] using h12
  have hi21 : (∫ q, f21 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
    simp only [f21]
    rw [integral_const_mul]
    simpa using h21
  have hi03 : (∫ q, f03 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
    simp only [f03]
    rw [integral_const_mul]
    simpa using h03
  have hsum :
      (∫ q, (f30 + f12 + f21 + f03) q
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
    have hA := integral_add' hf30 hf12
    have hB := integral_add' (hf30.add hf12) hf21
    have hC := integral_add' ((hf30.add hf12).add hf21) hf03
    calc
      (∫ q, (f30 + f12 + f21 + f03) q
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
          (∫ q, (f30 + f12 + f21) q
            ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
          ∫ q, f03 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            simpa only [Pi.add_apply] using hC
      _ = ((∫ q, (f30 + f12) q
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
            ∫ q, f21 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
          ∫ q, f03 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            rw [show (∫ q, (f30 + f12 + f21) q
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
              (∫ q, (f30 + f12) q
                ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
              ∫ q, f21 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) by
                simpa only [Pi.add_apply] using hB]
      _ = (((∫ q, f30 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
              ∫ q, f12 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
            ∫ q, f21 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
          ∫ q, f03 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            rw [show (∫ q, (f30 + f12) q
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
              (∫ q, f30 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) +
              ∫ q, f12 q ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) by
                simpa only [Pi.add_apply] using hA]
      _ = 0 := by rw [hi30, hi12, hi21, hi03]; ring
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [show (fun q : ℝ × ℝ ↦
      circularGaussianCoordinate q ^ 2 * conj (circularGaussianCoordinate q)) =
      fun q ↦ (1 / ((2 : ℂ) * (Real.sqrt 2 : ℂ))) *
        (f30 + f12 + f21 + f03) q by
    funext q
    rw [show circularGaussianCoordinate q ^ 2 * conj (circularGaussianCoordinate q) =
      circularGaussianCoordinate q *
        (circularGaussianCoordinate q * conj (circularGaussianCoordinate q)) by ring,
      circularGaussianCoordinate_mul_conj]
    simp only [circularGaussianCoordinate, f30, f12, f21, f03, Pi.add_apply]
    field_simp [Complex.ofReal_ne_zero.mpr hs0]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    ring]
  rw [integral_const_mul, hsum]
  ring

/-- Conjugate unbalanced cubic moment. -/
theorem integral_mul_conj_sq_circularGaussian :
    (∫ z : ℂ, z * conj z ^ 2 ∂circularGaussian) = 0 := by
  calc
    (∫ z : ℂ, z * conj z ^ 2 ∂circularGaussian) =
        ∫ z : ℂ, conj (z ^ 2 * conj z) ∂circularGaussian := by
      congr 1
      funext z
      simp only [map_mul, map_pow, conj_conj]
      ring
    _ = conj (∫ z : ℂ, z ^ 2 * conj z ∂circularGaussian) := integral_conj
    _ = 0 := by rw [integral_sq_mul_conj_circularGaussian]; norm_num

theorem integral_conj_circularGaussian :
    (∫ z : ℂ, conj z ∂circularGaussian) = 0 := by
  rw [integral_conj, integral_id_circularGaussian]
  norm_num

theorem integral_conj_sq_circularGaussian :
    (∫ z : ℂ, conj z ^ 2 ∂circularGaussian) = 0 := by
  calc
    (∫ z : ℂ, conj z ^ 2 ∂circularGaussian) =
        ∫ z : ℂ, conj (z ^ 2) ∂circularGaussian := by
      congr 1
      funext z
      rw [map_pow]
    _ = conj (∫ z : ℂ, z ^ 2 ∂circularGaussian) := integral_conj
    _ = 0 := by rw [integral_sq_circularGaussian]; norm_num

/-- Complete scalar Wick table through bidegree `(2,2)`. -/
theorem integral_mixedComplexMonomial_circularGaussian
    (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
    (∫ z, mixedComplexMonomial a b z ∂circularGaussian) =
      if a = b then (a.factorial : ℂ) else 0 := by
  interval_cases a <;> interval_cases b <;>
    simp [mixedComplexMonomial, integral_id_circularGaussian,
      integral_sq_circularGaussian, integral_mul_conj_circularGaussian,
      integral_sq_mul_conj_circularGaussian,
      integral_mul_conj_sq_circularGaussian,
      integral_sq_mul_conj_sq_circularGaussian,
      integral_conj_circularGaussian, integral_conj_sq_circularGaussian]

end

end LogdetLean.GramHafnian
