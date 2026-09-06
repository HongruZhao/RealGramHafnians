import LogdetLean.GramHafnian.CircularGaussianMoments
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Sharp disk bounds for the literal circular complex Gaussian

This module proves the planar analytic input used by shifted
anti-concentration.  The circular law already used by the Gram--hafnian
development is dominated, as a measure, by `π⁻¹` times complex Lebesgue
measure.  Consequently every disk of radius `ρ` has probability at most
`ρ²`, uniformly in its centre.

The proof works from the two independent real Gaussian densities and the
Jacobian of `(x,y) ↦ (x+iy)/√2`; no Gaussian density or disk estimate is
assumed as a theorem parameter.
-/

open scoped ENNReal NNReal Real InnerProductSpace ComplexConjugate
open MeasureTheory ProbabilityTheory Metric

namespace LogdetLean.GramHafnian

noncomputable section

/-- The standard real Gaussian density, as an `ENNReal`, is bounded by its
value at zero. -/
theorem gaussianPDF_zero_one_le_peak (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi)) := by
  rw [gaussianPDF, gaussianPDFReal]
  apply ENNReal.ofReal_le_ofReal
  norm_num
  have hsqrt : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hexp : Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hexp hsqrt

/-- The product of two standard real Gaussian measures is bounded by its
peak density times planar product Lebesgue measure. -/
theorem standardGaussianPair_le_peak_smul_volume :
    (gaussianReal 0 1).prod (gaussianReal 0 1) ≤
      (ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi)) ^ 2) •
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1)
      (measurable_gaussianPDF 0 1), ← withDensity_const]
  apply withDensity_mono
  filter_upwards [] with q
  simpa [pow_two] using
    mul_le_mul' (gaussianPDF_zero_one_le_peak q.1)
      (gaussianPDF_zero_one_le_peak q.2)

/-- The coordinate map defining the circular Gaussian sends planar Lebesgue
measure to twice complex Lebesgue measure.  The factor two is the Jacobian of
division by `√2` in two real dimensions. -/
theorem map_circularGaussianCoordinate_volume :
    Measure.map circularGaussianCoordinate
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) =
      (2 : ℝ≥0∞) • (volume : Measure ℂ) := by
  have hcoord : circularGaussianCoordinate =
      fun q : ℝ × ℝ ↦ ((Real.sqrt 2)⁻¹ : ℝ) •
        Complex.measurableEquivRealProd.symm q := by
    have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    funext q
    apply Complex.ext <;> simp [circularGaussianCoordinate]
    all_goals
      field_simp [hsqrt]
      rw [hsqrt_sq]
  have hvol :
      Measure.map Complex.measurableEquivRealProd.symm
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) =
        (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm.map_eq
  rw [hcoord, show (fun q : ℝ × ℝ ↦ ((Real.sqrt 2)⁻¹ : ℝ) •
      Complex.measurableEquivRealProd.symm q) =
      (fun z : ℂ ↦ ((Real.sqrt 2)⁻¹ : ℝ) • z) ∘
        Complex.measurableEquivRealProd.symm by rfl,
    ← Measure.map_map (measurable_const_smul ((Real.sqrt 2)⁻¹ : ℝ))
      Complex.measurableEquivRealProd.symm.measurable,
    hvol,
    Measure.map_addHaar_smul (volume : Measure ℂ)]
  · congr 1
    rw [show Module.finrank ℝ ℂ = 2 by simp]
    have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [inv_pow, hsqrt_sq, inv_inv]
    norm_num
  · exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))

/-- The literal circular Gaussian used throughout the project has density at
most `1/π` with respect to complex Lebesgue measure. -/
theorem circularGaussian_le_inv_pi_smul_volume :
    circularGaussian ≤ ENNReal.ofReal (Real.pi⁻¹) • (volume : Measure ℂ) := by
  unfold circularGaussian
  refine (Measure.map_mono standardGaussianPair_le_peak_smul_volume
    measurable_circularGaussianCoordinate).trans_eq ?_
  rw [Measure.map_smul, map_circularGaussianCoordinate_volume, smul_smul]
  congr 1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsqrt_sq : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hreal : (1 / Real.sqrt (2 * Real.pi)) ^ 2 * 2 = Real.pi⁻¹ := by
    field_simp [hsqrt_pos.ne', hpi.ne']
    nlinarith
  calc
    ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi)) ^ 2 * 2 =
        ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi)) ^ 2) *
          ENNReal.ofReal 2 := by
      rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 1 / Real.sqrt (2 * Real.pi))]
      norm_num
    _ = ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi)) ^ 2 * 2) := by
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
    _ = ENNReal.ofReal Real.pi⁻¹ := by rw [hreal]

/-- Sharp shifted disk bound for the standard circular complex Gaussian. -/
theorem circularGaussian_closedBall_le_sq (z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    circularGaussian.real (closedBall z ρ) ≤ ρ ^ 2 := by
  have hmeasure :
      circularGaussian (closedBall z ρ) ≤
        (ENNReal.ofReal (Real.pi⁻¹) • (volume : Measure ℂ)) (closedBall z ρ) :=
    circularGaussian_le_inv_pi_smul_volume (closedBall z ρ)
  rw [Measure.smul_apply, Complex.volume_closedBall] at hmeasure
  rw [measureReal_def]
  calc
    (circularGaussian (closedBall z ρ)).toReal ≤
        (ENNReal.ofReal (Real.pi⁻¹) *
          (ENNReal.ofReal ρ ^ 2 * NNReal.pi)).toReal := by
      exact ENNReal.toReal_mono (by finiteness) hmeasure
    _ = ρ ^ 2 := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hρ, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi⁻¹),
        ENNReal.coe_toReal]
      · simp only [NNReal.coe_real_pi]
        field_simp [Real.pi_ne_zero]

/-- Equivalent norm formulation of the sharp shifted disk bound. -/
theorem circularGaussian_norm_sub_le (z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    circularGaussian.real {w : ℂ | ‖w - z‖ ≤ ρ} ≤ ρ ^ 2 := by
  simpa [Metric.closedBall, dist_eq_norm, norm_sub_rev] using
    circularGaussian_closedBall_le_sq z ρ hρ

/-! ## Exact standard-Gaussian representation -/

/-- The unscaled identification of a real pair with a complex number. -/
def gaussianPairToComplex (q : ℝ × ℝ) : ℂ :=
  (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

@[fun_prop]
theorem measurable_gaussianPairToComplex : Measurable gaussianPairToComplex := by
  unfold gaussianPairToComplex
  fun_prop

/-- A pair of independent standard real Gaussians, transported through the
orthonormal basis `(1,i)`, is the real two-dimensional standard Gaussian on
`ℂ`. -/
theorem map_gaussianPairToComplex_standardGaussianPair :
    Measure.map gaussianPairToComplex
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      stdGaussian ℂ := by
  have hpair := (measurePreserving_finTwoArrow (gaussianReal 0 1)).symm
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI]
  have hcomp : gaussianPairToComplex =
      (fun x : Fin 2 → ℝ ↦
        ∑ i, x i • Complex.orthonormalBasisOneI i) ∘
          MeasurableEquiv.finTwoArrow.symm := by
    funext q
    simp [gaussianPairToComplex, Fin.sum_univ_two,
      Complex.coe_orthonormalBasisOneI, MeasurableEquiv.finTwoArrow]
  rw [hcomp, ← Measure.map_map]
  · exact congrArg
      (Measure.map (fun x : Fin 2 → ℝ ↦
        ∑ i, x i • Complex.orthonormalBasisOneI i)) hpair.map_eq
  all_goals fun_prop

/-- The literal circular law is exactly a `1/√2` rescaling of the standard
real Gaussian measure on the two-dimensional space `ℂ`. -/
theorem circularGaussian_eq_map_smul_stdGaussian :
    circularGaussian =
      (stdGaussian ℂ).map (fun z : ℂ ↦ ((Real.sqrt 2)⁻¹ : ℝ) • z) := by
  unfold circularGaussian
  have hfun : circularGaussianCoordinate =
      (fun z : ℂ ↦ ((Real.sqrt 2)⁻¹ : ℝ) • z) ∘ gaussianPairToComplex := by
    funext q
    simp [circularGaussianCoordinate, gaussianPairToComplex,
      Complex.real_smul, div_eq_mul_inv]
    ring
  rw [hfun, ← Measure.map_map
    (measurable_const_smul ((Real.sqrt 2)⁻¹ : ℝ))
    measurable_gaussianPairToComplex,
    map_gaussianPairToComplex_standardGaussianPair]

/-- Exact characteristic function of the paper-normalized circular law. -/
theorem charFun_circularGaussian (t : ℂ) :
    charFun circularGaussian t =
      Complex.exp (-((‖t‖ : ℂ) ^ 2) / 4) := by
  rw [circularGaussian_eq_map_smul_stdGaussian,
    charFun_map_smul, charFun_stdGaussian]
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.2 (by norm_num)),
    ]
  congr 1
  norm_cast
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hsqrt_ne]
  nlinarith [hsqrt_sq]

/-- Euclidean realization of `k` independent circular coordinates. -/
abbrev CircularEuclideanSpace (k : ℕ) := EuclideanSpace ℂ (Fin k)

/-- The iid circular product, after applying `toLp`, is exactly a
`1/√2`-rescaled real standard Gaussian on complex Euclidean space. -/
theorem map_toLp_pi_circularGaussian_eq_scaled_stdGaussian (k : ℕ) :
    (Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2) =
      (stdGaussian (CircularEuclideanSpace k)).map
        (fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • x) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_pi, charFun_map_smul, charFun_stdGaussian]
  simp_rw [charFun_circularGaussian]
  rw [← Complex.exp_sum]
  congr 1
  norm_cast
  rw [norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.sqrt_pos.2 (by norm_num)), mul_pow,
    EuclideanSpace.norm_sq_eq]
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [inv_pow, hsqrt_sq]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  ring

/-! ## Transpose complex linear forms -/

/-- The transpose, rather than Hermitian, linear form used by the hafnian
last-column expansion. -/
def circularTransposeLinearForm {k : ℕ} (y : Fin k → ℂ)
    (x : CircularEuclideanSpace k) : ℂ :=
  ∑ i, x i * y i

@[fun_prop]
theorem measurable_circularTransposeLinearForm {k : ℕ} (y : Fin k → ℂ) :
    Measurable (circularTransposeLinearForm y) := by
  unfold circularTransposeLinearForm
  fun_prop

/-- Fourier vector representing a transpose complex linear form after
realification. -/
def circularTransposeCharVector {k : ℕ} (y : Fin k → ℂ) (t : ℂ) :
    CircularEuclideanSpace k :=
  WithLp.toLp 2 (fun i ↦ conj (y i) * t)

theorem real_inner_circularTransposeLinearForm {k : ℕ}
    (y : Fin k → ℂ) (x : CircularEuclideanSpace k) (t : ℂ) :
    ⟪circularTransposeLinearForm y x, t⟫_ℝ =
      ⟪x, circularTransposeCharVector y t⟫_ℝ := by
  rw [real_inner_eq_re_inner ℂ, PiLp.inner_apply]
  simp only [circularTransposeLinearForm, circularTransposeCharVector,
    real_inner_eq_re_inner ℂ, RCLike.inner_apply', map_sum, map_mul,
    PiLp.toLp_apply]
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem norm_sq_circularTransposeCharVector {k : ℕ}
    (y : Fin k → ℂ) (t : ℂ) :
    ‖circularTransposeCharVector y t‖ ^ 2 =
      (∑ i, ‖y i‖ ^ 2) * ‖t‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [circularTransposeCharVector, PiLp.toLp_apply, norm_mul,
    Complex.norm_conj, mul_pow]
  rw [← Finset.sum_mul]

/-- Exact characteristic function of a transpose linear form of a real
standard Gaussian on complex Euclidean space. -/
theorem charFun_map_circularTransposeLinearForm_stdGaussian {k : ℕ}
    (y : Fin k → ℂ) (t : ℂ) :
    charFun ((stdGaussian (CircularEuclideanSpace k)).map
        (circularTransposeLinearForm y)) t =
      Complex.exp (-(((∑ i, ‖y i‖ ^ 2) * ‖t‖ ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFun_apply, integral_map
    (measurable_circularTransposeLinearForm y).aemeasurable
    (by fun_prop)]
  have hintegrand :
      (fun x : CircularEuclideanSpace k ↦
          Complex.exp (↑⟪circularTransposeLinearForm y x, t⟫_ℝ * Complex.I)) =
        (fun x ↦ Complex.exp
          (↑⟪x, circularTransposeCharVector y t⟫_ℝ * Complex.I)) := by
    funext x
    rw [real_inner_circularTransposeLinearForm]
  rw [hintegrand, ← charFun_apply, charFun_stdGaussian]
  congr 1
  have hnormC := congrArg ((↑) : ℝ → ℂ)
    (norm_sq_circularTransposeCharVector y t)
  push_cast at hnormC
  rw [hnormC]
  push_cast
  rfl

/-! ## Exact law of an iid circular transpose linear form -/

/-- Squared coefficient norm, which is the complex variance of the
transpose linear form under the paper-normalized circular law. -/
def circularCoefficientEnergy {k : ℕ} (y : Fin k → ℂ) : ℝ :=
  ∑ i, ‖y i‖ ^ 2

theorem circularCoefficientEnergy_nonneg {k : ℕ} (y : Fin k → ℂ) :
    0 ≤ circularCoefficientEnergy y := by
  unfold circularCoefficientEnergy
  positivity

/-- A transpose linear form of the real standard Gaussian on complex
Euclidean space is a circular Gaussian rescaled by `sqrt (2 * energy)`.
The factor two records that `stdGaussian ℂ` has two real coordinates of
variance one, whereas `circularGaussian` has complex variance one. -/
theorem map_circularTransposeLinearForm_stdGaussian_eq_scaled_circular
    {k : ℕ} (y : Fin k → ℂ) :
    (stdGaussian (CircularEuclideanSpace k)).map
        (circularTransposeLinearForm y) =
      circularGaussian.map (fun z : ℂ ↦
        Real.sqrt (2 * circularCoefficientEnergy y) • z) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_circularTransposeLinearForm_stdGaussian,
    charFun_map_smul, charFun_circularGaussian, norm_smul,
    Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (2 * circularCoefficientEnergy y))]
  congr 1
  norm_cast
  rw [mul_pow, Real.sq_sqrt (by
    exact mul_nonneg (by norm_num) (circularCoefficientEnergy_nonneg y) :
      0 ≤ 2 * circularCoefficientEnergy y)]
  unfold circularCoefficientEnergy
  ring

/-- The transpose linear form of independent paper-normalized circular
coordinates is exactly a circular Gaussian rescaled by the square root of
the coefficient energy.  This statement includes energy zero. -/
theorem map_circularTransposeLinearForm_iid_circular_eq_scaled_circular
    {k : ℕ} (y : Fin k → ℂ) :
    ((Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)).map
        (circularTransposeLinearForm y) =
      circularGaussian.map (fun z : ℂ ↦
        Real.sqrt (circularCoefficientEnergy y) • z) := by
  let r : ℝ := (Real.sqrt 2)⁻¹
  let V : ℝ := circularCoefficientEnergy y
  have hcommute :
      circularTransposeLinearForm y ∘
          (fun x : CircularEuclideanSpace k ↦ r • x) =
        (fun z : ℂ ↦ r • z) ∘ circularTransposeLinearForm y := by
    funext x
    simp only [Function.comp_apply, circularTransposeLinearForm]
    change (∑ i, ((r : ℂ) * x i) * y i) =
      (r : ℂ) * ∑ i, x i * y i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [map_toLp_pi_circularGaussian_eq_scaled_stdGaussian]
  change ((stdGaussian (CircularEuclideanSpace k)).map
      (fun x ↦ r • x)).map (circularTransposeLinearForm y) = _
  rw [Measure.map_map (measurable_circularTransposeLinearForm y)
      (measurable_const_smul r),
    hcommute,
    ← Measure.map_map (measurable_const_smul r)
      (measurable_circularTransposeLinearForm y),
    map_circularTransposeLinearForm_stdGaussian_eq_scaled_circular,
    Measure.map_map (measurable_const_smul r)
      (measurable_const_smul (Real.sqrt (2 * circularCoefficientEnergy y)))]
  congr 1
  funext z
  simp only [Function.comp_apply, smul_smul]
  change (r * Real.sqrt (2 * V)) • z = Real.sqrt V • z
  congr 1
  dsimp [r]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]

/-- The same transpose form on the ordinary function-space realization of
the iid product measure. -/
def iidCircularTransposeLinearForm {k : ℕ} (y : Fin k → ℂ)
    (x : Fin k → ℂ) : ℂ :=
  ∑ i, x i * y i

@[fun_prop]
theorem measurable_iidCircularTransposeLinearForm {k : ℕ}
    (y : Fin k → ℂ) : Measurable (iidCircularTransposeLinearForm y) := by
  unfold iidCircularTransposeLinearForm
  fun_prop

/-- Function-space form of the exact iid circular linear-functional law. -/
theorem map_iidCircularTransposeLinearForm_eq_scaled_circular
    {k : ℕ} (y : Fin k → ℂ) :
    (Measure.pi fun _ : Fin k ↦ circularGaussian).map
        (iidCircularTransposeLinearForm y) =
      circularGaussian.map (fun z : ℂ ↦
        Real.sqrt (circularCoefficientEnergy y) • z) := by
  have hcomp : iidCircularTransposeLinearForm y =
      circularTransposeLinearForm y ∘ WithLp.toLp 2 := by
    rfl
  rw [hcomp, ← Measure.map_map
    (measurable_circularTransposeLinearForm y) (by fun_prop)]
  exact map_circularTransposeLinearForm_iid_circular_eq_scaled_circular y

/-! ## Scaled and iid shifted disk bounds -/

/-- A positive real rescaling of a circular Gaussian has the exact sharp
shifted disk upper bound `rho^2 / s^2`. -/
theorem map_pos_smul_circularGaussian_closedBall_le
    (s : ℝ) (hs : 0 < s) (z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (circularGaussian.map (fun w : ℂ ↦ s • w)).real
        (closedBall z ρ) ≤ ρ ^ 2 / s ^ 2 := by
  have hz : s • (s⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hpreimage :
      (fun w : ℂ ↦ s • w) ⁻¹' closedBall z ρ =
        closedBall (s⁻¹ • z) (ρ / s) := by
    ext w
    simp only [Set.mem_preimage, mem_closedBall]
    have hdist : dist (s • w) z = s * dist w (s⁻¹ • z) := by
      calc
        dist (s • w) z = dist (s • w) (s • (s⁻¹ • z)) := by rw [hz]
        _ = s * dist w (s⁻¹ • z) := by
          rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hs]
    rw [hdist]
    rw [le_div_iff₀ hs]
    simp only [mul_comm]
  rw [MeasureTheory.map_measureReal_apply (measurable_const_smul s)
      measurableSet_closedBall,
    hpreimage]
  calc
    circularGaussian.real (closedBall (s⁻¹ • z) (ρ / s)) ≤
        (ρ / s) ^ 2 :=
      circularGaussian_closedBall_le_sq _ _ (div_nonneg hρ hs.le)
    _ = ρ ^ 2 / s ^ 2 := by ring

/-- Sharp conditional small-ball inequality for a transpose linear form of
iid circular coordinates, in the ordinary function-space realization. -/
theorem iidCircularTransposeLinearForm_closedBall_le
    {k : ℕ} (y : Fin k → ℂ)
    (henergy : 0 < circularCoefficientEnergy y)
    (z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ((Measure.pi fun _ : Fin k ↦ circularGaussian).map
        (iidCircularTransposeLinearForm y)).real (closedBall z ρ) ≤
      ρ ^ 2 / circularCoefficientEnergy y := by
  rw [map_iidCircularTransposeLinearForm_eq_scaled_circular]
  simpa [Real.sq_sqrt henergy.le] using
    map_pos_smul_circularGaussian_closedBall_le
      (Real.sqrt (circularCoefficientEnergy y))
      (Real.sqrt_pos.2 henergy) z ρ hρ

/-- Equivalent event formulation of the iid shifted small-ball bound. -/
theorem pi_circularGaussian_transpose_norm_sub_le
    {k : ℕ} (y : Fin k → ℂ)
    (henergy : 0 < circularCoefficientEnergy y)
    (z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (Measure.pi fun _ : Fin k ↦ circularGaussian).real
        {x : Fin k → ℂ |
          ‖iidCircularTransposeLinearForm y x - z‖ ≤ ρ} ≤
      ρ ^ 2 / circularCoefficientEnergy y := by
  have hmeas := measurable_iidCircularTransposeLinearForm y
  change (Measure.pi fun _ : Fin k ↦ circularGaussian).real
      ((iidCircularTransposeLinearForm y) ⁻¹'
        {w : ℂ | ‖w - z‖ ≤ ρ}) ≤ _
  have hset : MeasurableSet {w : ℂ | ‖w - z‖ ≤ ρ} := by
    simpa only [Metric.closedBall, dist_eq_norm] using
      (measurableSet_closedBall : MeasurableSet (closedBall z ρ))
  rw [← MeasureTheory.map_measureReal_apply hmeas hset]
  simpa [Metric.closedBall, dist_eq_norm, norm_sub_rev] using
    iidCircularTransposeLinearForm_closedBall_le y henergy z ρ hρ

end

end LogdetLean.GramHafnian
