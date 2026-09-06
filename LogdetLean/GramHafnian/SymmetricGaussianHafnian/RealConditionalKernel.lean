import LogdetLean.GramHafnian.SymmetricGaussianHafnian.RealSmallBallLowerCore
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.WeightedCompression
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.LocalCofactorCompression
/-!
# The literal real scalar-plus-bilinear conditional kernel

This is the real analogue of `ComplexConditionalKernel`.  All exposed
variables have their genuine `N(0,1)` law.  The extra scalar edge supplies
the positive factor `exp (-ell^2/2)`, while the two exposed stars are
transported to standard real Gaussian Euclidean vectors.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 1200000

def realTransposeDot {k : ℕ} (x y : Fin k → ℝ) : ℝ :=
  ∑ i, x i * y i

def realBilinearPhaseOperator {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

def realLinearPhaseOperator {k : ℕ} (q : Fin k → ℝ) :
    EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (Matrix.toEuclideanLin
    (show Matrix (Fin k) (Fin 1) ℝ from fun i (_ : Fin 1) ↦ q i)).toContinuousLinearMap

def realPhaseCoordinate (a : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 (fun _ : Fin 1 ↦ a)

def realBilinearPhase {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (q : Fin k → ℝ) (a b : ℝ) (X Y : Fin k → ℝ) : ℝ :=
  LogdetLean.GramHafnian.realTransposeBilinearPhase X M Y +
    b * realTransposeDot X q + a * realTransposeDot Y q

theorem realBilinearPhase_eq_euclidean
    {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ)
    (a b : ℝ) (X Y : Fin k → ℝ) :
    realBilinearPhase M q a b X Y =
      inner ℝ (WithLp.toLp 2 X)
        (realBilinearPhaseOperator M (WithLp.toLp 2 Y)) +
      inner ℝ (WithLp.toLp 2 X)
        (realLinearPhaseOperator q (realPhaseCoordinate b)) +
      inner ℝ (WithLp.toLp 2 Y)
        (realLinearPhaseOperator q (realPhaseCoordinate a)) := by
  have hM := inner_toEuclideanLin_eq_realTransposeBilinearPhase X M Y
  have hL (Z : Fin k → ℝ) (c : ℝ) :
      inner ℝ (WithLp.toLp 2 Z)
          (realLinearPhaseOperator q (realPhaseCoordinate c)) =
        c * realTransposeDot Z q := by
    unfold realLinearPhaseOperator realPhaseCoordinate
    change inner ℝ (WithLp.toLp 2 Z)
      (Matrix.toEuclideanLin
        (show Matrix (Fin k) (Fin 1) ℝ from fun i (_ : Fin 1) ↦ q i)
        (WithLp.toLp 2 (fun _ : Fin 1 ↦ c))) = _
    rw [inner_toEuclideanLin_eq_realTransposeBilinearPhase]
    unfold LogdetLean.GramHafnian.realTransposeBilinearPhase
    unfold realTransposeDot
    simp
    rw [← Finset.sum_mul]
    ring
  have hM' : inner ℝ (WithLp.toLp 2 X)
      (realBilinearPhaseOperator M (WithLp.toLp 2 Y)) =
      LogdetLean.GramHafnian.realTransposeBilinearPhase X M Y := by
    simpa [realBilinearPhaseOperator] using hM
  rw [hM', hL, hL]
  unfold realBilinearPhase
  ring

def realBilinearKernel {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (q : Fin k → ℝ) (a b : ℝ) : ℂ :=
  ∫ p : (Fin k → ℝ) × (Fin k → ℝ),
    Complex.exp (((realBilinearPhase M q a b p.1 p.2 : ℝ) : ℂ) * Complex.I)
    ∂((standardRealGaussianProduct (Fin k)).prod
      (standardRealGaussianProduct (Fin k)))

theorem realBilinearKernel_eq_bilinearGaussianIntegral
    {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ)
    (a b : ℝ) :
    realBilinearKernel M q a b =
      bilinearGaussianIntegral (realBilinearPhaseOperator M)
        (realLinearPhaseOperator q) (realPhaseCoordinate a) (realPhaseCoordinate b) := by
  let E := EuclideanSpace ℝ (Fin k)
  let rho : ((Fin k → ℝ) × (Fin k → ℝ)) → E × E :=
    fun p ↦ (WithLp.toLp 2 p.1, WithLp.toLp 2 p.2)
  let kernel : E × E → ℂ := fun p ↦
    Complex.exp (((inner ℝ p.1 (realBilinearPhaseOperator M p.2) +
      inner ℝ p.1 (realLinearPhaseOperator q (realPhaseCoordinate b)) +
      inner ℝ p.2 (realLinearPhaseOperator q (realPhaseCoordinate a)) : ℝ) : ℂ) *
        Complex.I)
  have hsingle : MeasurePreserving (WithLp.toLp 2)
      (standardRealGaussianProduct (Fin k)) (stdGaussian E) := by
    refine ⟨by fun_prop, ?_⟩
    exact map_pi_eq_stdGaussian
  have hrho : MeasurePreserving rho
      ((standardRealGaussianProduct (Fin k)).prod
        (standardRealGaussianProduct (Fin k)))
      ((stdGaussian E).prod (stdGaussian E)) := by
    exact hsingle.prod hsingle
  have htransport :
      (∫ p : (Fin k → ℝ) × (Fin k → ℝ), kernel (rho p)
        ∂((standardRealGaussianProduct (Fin k)).prod
          (standardRealGaussianProduct (Fin k)))) =
      ∫ p, kernel p ∂((stdGaussian E).prod (stdGaussian E)) := by
    rw [← hrho.map_eq]
    symm
    exact integral_map hrho.measurable.aemeasurable
      (by fun_prop : Continuous kernel).aestronglyMeasurable
  unfold realBilinearKernel bilinearGaussianIntegral
  rw [← htransport]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [realBilinearPhase_eq_euclidean]

def realScalarGaussianWeight (ell : ℝ) : ℝ :=
  Real.exp (-(ell ^ 2) / 2)

theorem realScalarGaussianWeight_pos (ell : ℝ) :
    0 < realScalarGaussianWeight ell := Real.exp_pos _

@[fun_prop] theorem measurable_realScalarGaussianWeight :
    Measurable realScalarGaussianWeight := by
  unfold realScalarGaussianWeight
  fun_prop

theorem integral_realScalarGaussian_phase (ell : ℝ) :
    (∫ u : ℝ, Complex.exp ((((u * ell : ℝ) : ℂ) * Complex.I))
      ∂gaussianReal 0 1) = (realScalarGaussianWeight ell : ℂ) := by
  calc
    _ = charFun (gaussianReal 0 1) ell := by
      rw [charFun_apply]
      apply integral_congr_ae
      filter_upwards [] with u
      congr 2
      push_cast
      rw [RCLike.inner_apply]
      simp
      ring
    _ = (realScalarGaussianWeight ell : ℂ) := by
      rw [charFun_gaussianReal]
      unfold realScalarGaussianWeight
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring

theorem integral_independent_realScalarGaussian_phase
    {P : Type*} [MeasurableSpace P]
    (mu : Measure P) [SFinite mu] (ell : ℝ) (phase : P → ℝ) :
    (∫ p : ℝ × P,
      Complex.exp (((((p.1 * ell + phase p.2) : ℝ) : ℂ) * Complex.I))
      ∂((gaussianReal 0 1).prod mu)) =
      (realScalarGaussianWeight ell : ℂ) *
        ∫ p : P, Complex.exp ((((phase p : ℝ) : ℂ) * Complex.I)) ∂mu := by
  have hsplit :
      (fun p : ℝ × P ↦ Complex.exp
        (((((p.1 * ell + phase p.2) : ℝ) : ℂ) * Complex.I))) =
      (fun p : ℝ × P ↦
        Complex.exp ((((p.1 * ell : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((phase p.2 : ℝ) : ℂ) * Complex.I))) := by
    funext p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit, integral_prod_mul
    (fun u : ℝ ↦ Complex.exp ((((u * ell : ℝ) : ℂ) * Complex.I)))
    (fun p : P ↦ Complex.exp ((((phase p : ℝ) : ℂ) * Complex.I))),
    integral_realScalarGaussian_phase]

abbrev RealExposedSample (k : ℕ) :=
  ℝ × ((Fin k → ℝ) × (Fin k → ℝ))

def realExposedMeasure (k : ℕ) : Measure (RealExposedSample k) :=
  (gaussianReal 0 1).prod
    ((standardRealGaussianProduct (Fin k)).prod
      (standardRealGaussianProduct (Fin k)))

instance (k : ℕ) : IsProbabilityMeasure (realExposedMeasure k) := by
  unfold realExposedMeasure
  infer_instance

def realConditionalKernel {k : ℕ} (ell : ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ)
    (a b : ℝ) : ℂ :=
  ∫ p : RealExposedSample k,
    Complex.exp (((((p.1 * ell +
      realBilinearPhase M q a b p.2.1 p.2.2) : ℝ) : ℂ) * Complex.I))
    ∂realExposedMeasure k

theorem realConditionalKernel_eq_weightedBilinearGaussianIntegral
    {k : ℕ} (ell : ℝ) (M : Matrix (Fin k) (Fin k) ℝ)
    (q : Fin k → ℝ) (a b : ℝ) :
    realConditionalKernel ell M q a b =
      weightedBilinearGaussianIntegral (realScalarGaussianWeight ell)
        (realBilinearPhaseOperator M) (realLinearPhaseOperator q)
        (realPhaseCoordinate a) (realPhaseCoordinate b) := by
  unfold realConditionalKernel realExposedMeasure
  rw [integral_independent_realScalarGaussian_phase
    ((standardRealGaussianProduct (Fin k)).prod
      (standardRealGaussianProduct (Fin k))) ell
    (fun p ↦ realBilinearPhase M q a b p.1 p.2)]
  change (realScalarGaussianWeight ell : ℂ) * realBilinearKernel M q a b = _
  rw [realBilinearKernel_eq_bilinearGaussianIntegral]
  rfl

theorem integrable_realConditionalKernel_background
    {Omega : Type*} [MeasurableSpace Omega] {k : ℕ}
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (ell : Omega → ℝ) (M : Omega → Matrix (Fin k) (Fin k) ℝ)
    (q : Omega → (Fin k → ℝ))
    (hell : Measurable ell) (hM : ∀ i j, Measurable (fun omega ↦ M omega i j))
    (hq : Measurable q) (a b : ℝ) :
    Integrable (fun omega ↦ realConditionalKernel (ell omega) (M omega) (q omega) a b)
      mu := by
  let f : Omega × RealExposedSample k → ℂ := fun p ↦
    Complex.exp (((((p.2.1 * ell p.1 +
      realBilinearPhase (M p.1) (q p.1) a b p.2.2.1 p.2.2.2) : ℝ) : ℂ) *
        Complex.I))
  have hfmeas : Measurable f := by
    unfold f realBilinearPhase realTransposeDot
    unfold LogdetLean.GramHafnian.realTransposeBilinearPhase
    fun_prop
  have hf : Integrable f (mu.prod (realExposedMeasure k)) := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with p
    unfold f
    rw [Complex.norm_exp]
    simp
  exact hf.integral_prod_left

theorem norm_integral_realConditionalKernel_sqrt_le_max
    {Omega : Type*} [MeasurableSpace Omega] {k : ℕ}
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (ell : Omega → ℝ) (M : Omega → Matrix (Fin k) (Fin k) ℝ)
    (q : Omega → (Fin k → ℝ))
    (hell : Measurable ell) (hM : ∀ i j, Measurable (fun omega ↦ M omega i j))
    (hq : Measurable q) (a b : ℝ)
    {theta : ℝ} (htheta : 0 < theta) (htheta_one : theta < 1) :
    ‖∫ omega, realConditionalKernel (ell omega) (M omega) (q omega)
      (Real.sqrt theta * a) (Real.sqrt (1 - theta) * b) ∂mu‖ ≤
      max
        ‖∫ omega, realConditionalKernel (ell omega) (M omega) (q omega) a 0 ∂mu‖
        ‖∫ omega, realConditionalKernel (ell omega) (M omega) (q omega) 0 b ∂mu‖ := by
  have hint := integrable_realConditionalKernel_background mu ell M q hell hM hq
    (Real.sqrt theta * a) (Real.sqrt (1 - theta) * b)
  have hleft := integrable_realConditionalKernel_background mu ell M q hell hM hq a 0
  have hright := integrable_realConditionalKernel_background mu ell M q hell hM hq 0 b
  simp only [realConditionalKernel_eq_weightedBilinearGaussianIntegral] at hint hleft hright ⊢
  have hcoord (s c : ℝ) : realPhaseCoordinate (s * c) = s • realPhaseCoordinate c := by
    ext i
    simp [realPhaseCoordinate]
  rw [hcoord, hcoord]
  exact norm_integral_weightedBilinearGaussianIntegral_sqrt_le_max mu
    (fun omega ↦ realScalarGaussianWeight (ell omega))
    (fun omega ↦ realScalarGaussianWeight_pos (ell omega))
    (fun omega ↦ realBilinearPhaseOperator (M omega))
    (fun omega ↦ realLinearPhaseOperator (q omega))
    (realPhaseCoordinate a) (realPhaseCoordinate b)
    htheta htheta_one hint hleft hright

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
