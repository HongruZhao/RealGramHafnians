import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedScore
import LogdetLean.GaussianLinearIndependence
import LogdetLean.GaussianScatter
import LogdetLean.GaussianColumnProduct
import Mathlib.Probability.ProductMeasure
/-!
# Flattening iid half-Gaussian matrices

This file identifies a `k × p` real matrix with `k*p` scalar coordinates and
transports the iid `N(0,1/2)` product law across that identification.  The
equivalence is kept explicit so the coordinate Gaussian integration-by-parts
theorem can be applied without changing the literal matrix random variable.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Row-major measurable equivalence between a flat coordinate vector and a
rectangular real matrix. -/
def flatMatrixMeasurableEquiv (k p : ℕ) :
    (Fin (k * p) → ℝ) ≃ᵐ Matrix (Fin k) (Fin p) ℝ where
  toFun x a i := x (finProdFinEquiv (a, i))
  invFun R q := R (finProdFinEquiv.symm q).1
    (finProdFinEquiv.symm q).2
  left_inv x := by
    funext q
    exact congrArg x
      ((finProdFinEquiv : Fin k × Fin p ≃ Fin (k * p)).apply_symm_apply q)
  right_inv R := by
    ext a i
    simp
  measurable_toFun := by
    change Measurable (fun x : Fin (k * p) → ℝ ↦
      (fun a i ↦ x (finProdFinEquiv (a, i)) : Fin k → Fin p → ℝ))
    fun_prop
  measurable_invFun := by
    change Measurable (fun R : Fin k → Fin p → ℝ ↦
      fun q ↦ R (finProdFinEquiv.symm q).1
        (finProdFinEquiv.symm q).2)
    fun_prop

@[simp]
theorem flatMatrixMeasurableEquiv_apply
    (k p : ℕ) (x : Fin (k * p) → ℝ) (a : Fin k) (i : Fin p) :
    flatMatrixMeasurableEquiv k p x a i =
      x (finProdFinEquiv (a, i)) := by
  rfl

@[simp]
theorem flatMatrixMeasurableEquiv_symm_apply
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) (q : Fin (k * p)) :
    (flatMatrixMeasurableEquiv k p).symm R q =
      R (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 := by
  rfl

/-- Identity equivalence from the curried product measurable space to
Mathlib's explicit matrix measurable-space instance. -/
def curriedMatrixMeasurableEquiv (k p : ℕ) :
    (Fin k → Fin p → ℝ) ≃ᵐ Matrix (Fin k) (Fin p) ℝ where
  toFun x := Matrix.of x
  invFun R a i := R a i
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun x : Fin k → Fin p → ℝ ↦ x)
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin k → Fin p → ℝ ↦ x)
    fun_prop

/-- The row-nested scalar iid law before its harmless coercion to `Matrix`. -/
def halfGaussianRowProduct (k p : ℕ) : Measure (Fin k → Fin p → ℝ) :=
  Measure.pi (fun _ : Fin k ↦
    Measure.pi (fun _ : Fin p ↦ gaussianReal 0 halfGaussianVariance))

/-- The same scalar iid law grouped by matrix columns. -/
def halfGaussianColumnProduct (k p : ℕ) :
    Measure (Fin p → Fin k → ℝ) :=
  Measure.pi (fun _ : Fin p ↦
    Measure.pi (fun _ : Fin k ↦ gaussianReal 0 halfGaussianVariance))

/-- Scalar variance-one-half Gaussian as the inverse-square-root-two image
of the standard scalar Gaussian. -/
theorem map_invSqrtTwo_gaussianReal_zero_one :
    Measure.map (fun x : ℝ ↦ (Real.sqrt 2)⁻¹ * x)
        (gaussianReal 0 1) =
      gaussianReal 0 halfGaussianVariance := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
  unfold halfGaussianVariance
  change (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ)
  rw [inv_pow]
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  rw [hsqrt]
  norm_num

/-- One raw half-Gaussian scalar column, coerced to Euclidean space, is an
inverse-square-root-two scaled standard Gaussian vector. -/
theorem map_toLp_halfGaussianVector (k : ℕ) :
    Measure.map (WithLp.toLp 2)
        (Measure.pi (fun _ : Fin k ↦
          gaussianReal 0 halfGaussianVariance)) =
      Measure.map
        (fun x : EuclideanSpace ℝ (Fin k) ↦
          ((Real.sqrt 2)⁻¹ : ℝ) • x)
        (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  let c : ℝ := (Real.sqrt 2)⁻¹
  let scaleRaw : (Fin k → ℝ) → (Fin k → ℝ) :=
    fun x i ↦ c * x i
  have hscaleRaw :
      Measure.map scaleRaw
          (Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1)) =
        Measure.pi (fun _ : Fin k ↦
          gaussianReal 0 halfGaussianVariance) := by
    rw [Measure.pi_map_pi (fun _ ↦
      (show Measurable (fun x : ℝ ↦ c * x) by fun_prop).aemeasurable)]
    congr 1
    funext i
    simpa [c] using map_invSqrtTwo_gaussianReal_zero_one
  rw [← hscaleRaw]
  rw [Measure.map_map (show Measurable (WithLp.toLp 2 :
      (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) by fun_prop)
    (show Measurable scaleRaw by fun_prop)]
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map
    (show Measurable
      (fun x : EuclideanSpace ℝ (Fin k) ↦ c • x) by fun_prop)
    (show Measurable (WithLp.toLp 2 :
      (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with x
  ext i
  rfl

/-- A common nonzero real scaling preserves linear independence. -/
theorem realLinearIndependent_const_smul
    {E ι : Type*} [AddCommMonoid E] [Module ℝ E]
    {v : ι → E} (hv : LinearIndependent ℝ v)
    {c : ℝ} (hc : c ≠ 0) :
    LinearIndependent ℝ (fun i ↦ c • v i) := by
  let u : ℝˣ := Units.mk0 c hc
  have h := hv.units_smul (fun _ ↦ u)
  have hfun : ((fun _ : ι ↦ u) • v) = (fun i ↦ c • v i) := by
    funext i
    change (u : ℝ) • v i = c • v i
    rfl
  rw [hfun] at h
  exact h

/-- Iid scaled standard Euclidean Gaussian columns are linearly independent
almost surely up to the ambient dimension. -/
theorem ae_linearIndependent_pi_scaledStdGaussian_real
    (k p : ℕ) (hp : p ≤ k) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin p ↦
        (stdGaussian (EuclideanSpace ℝ (Fin k))).map
          (fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • x)),
      LinearIndependent ℝ v := by
  let E := EuclideanSpace ℝ (Fin k)
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hc : c ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hbase : ∀ᵐ v ∂Measure.pi (fun _ : Fin p ↦ stdGaussian E),
      LinearIndependent ℝ v := by
    apply LogdetLean.ae_linearIndependent_pi_stdGaussian
    simpa [E] using hp
  let scale : (Fin p → E) → (Fin p → E) :=
    fun v i ↦ c • v i
  have hmp : MeasurePreserving scale
      (Measure.pi fun _ : Fin p ↦ stdGaussian E)
      (Measure.pi fun _ : Fin p ↦
        (stdGaussian E).map (fun x ↦ c • x)) := by
    apply measurePreserving_pi
    intro i
    exact ⟨by fun_prop, rfl⟩
  have hset : MeasurableSet
      {v : Fin p → E | LinearIndependent ℝ v} :=
    LogdetLean.measurableSet_linearlyIndependentTuples p
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable hset).2
  filter_upwards [hbase] with v hv
  exact realLinearIndependent_const_smul hv hc

/-- Literal raw iid half-Gaussian columns are linearly independent after
their canonical coercion to Euclidean space. -/
theorem ae_linearIndependent_pi_halfGaussianColumns
    (k p : ℕ) (hp : p ≤ k) :
    ∀ᵐ v ∂halfGaussianColumnProduct k p,
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2 (v j) :
          Fin p → EuclideanSpace ℝ (Fin k)) := by
  let E := EuclideanSpace ℝ (Fin k)
  let target : Measure E :=
    (stdGaussian E).map
      (fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • x)
  have hcoord : MeasurePreserving (WithLp.toLp 2)
      (Measure.pi (fun _ : Fin k ↦
        gaussianReal 0 halfGaussianVariance)) target := by
    refine ⟨by fun_prop, ?_⟩
    simpa [target] using map_toLp_halfGaussianVector k
  have hfamily : MeasurePreserving
      (fun v : Fin p → (Fin k → ℝ) ↦
        (fun j ↦ WithLp.toLp 2 (v j) : Fin p → E))
      (halfGaussianColumnProduct k p)
      (Measure.pi fun _ : Fin p ↦ target) := by
    apply measurePreserving_pi
    intro j
    exact hcoord
  exact hfamily.quasiMeasurePreserving.ae
    (ae_linearIndependent_pi_scaledStdGaussian_real k p hp)

/-- Read a matrix as its family of scalar-valued columns. -/
def matrixToColumnsMeasurableEquiv (k p : ℕ) :
    Matrix (Fin k) (Fin p) ℝ ≃ᵐ (Fin p → Fin k → ℝ) :=
  (curriedMatrixMeasurableEquiv k p).symm.trans
    (LogdetLean.piTransposeMeasurableEquiv (Fin k) (Fin p) ℝ)

/-- The literal iid variance-one-half Gaussian law on a real matrix. -/
def halfGaussianMatrix (k p : ℕ) :
    Measure (Matrix (Fin k) (Fin p) ℝ) :=
  Measure.map (flatMatrixMeasurableEquiv k p) (halfGaussianPi (k * p))

instance (k p : ℕ) : IsProbabilityMeasure (halfGaussianMatrix k p) := by
  unfold halfGaussianMatrix
  exact Measure.isProbabilityMeasure_map
    (flatMatrixMeasurableEquiv k p).measurable.aemeasurable

instance (k p : ℕ) : SigmaFinite (halfGaussianMatrix k p) := by
  infer_instance

/-- Flattening preserves the complete iid half-Gaussian product law. -/
theorem measurePreserving_flatMatrixMeasurableEquiv (k p : ℕ) :
    MeasurePreserving (flatMatrixMeasurableEquiv k p)
      (halfGaussianPi (k * p)) (halfGaussianMatrix k p) := by
  exact ⟨(flatMatrixMeasurableEquiv k p).measurable, rfl⟩

/-- Pushforward form of the flat-to-matrix iid Gaussian bridge. -/
theorem map_flatMatrixMeasurableEquiv_halfGaussianPi (k p : ℕ) :
    Measure.map (flatMatrixMeasurableEquiv k p)
        (halfGaussianPi (k * p)) =
      halfGaussianMatrix k p :=
  (measurePreserving_flatMatrixMeasurableEquiv k p).map_eq

/-- The flattened law is exactly the usual row-by-row iid scalar product
law, transported only across the definitional `Matrix` wrapper. -/
theorem map_curriedMatrix_halfGaussianRowProduct (k p : ℕ) :
    Measure.map (curriedMatrixMeasurableEquiv k p)
        (halfGaussianRowProduct k p) =
      halfGaussianMatrix k p := by
  let μ : Measure ℝ := gaussianReal 0 halfGaussianVariance
  let reindex : (Fin (k * p) → ℝ) ≃ᵐ (Fin k × Fin p → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (k * p) ↦ ℝ)
      (finProdFinEquiv : Fin k × Fin p ≃ Fin (k * p))).symm
  let curry : (Fin k × Fin p → ℝ) ≃ᵐ (Fin k → Fin p → ℝ) :=
    MeasurableEquiv.curry (Fin k) (Fin p) ℝ
  have hreindex : Measure.map reindex (halfGaussianPi (k * p)) =
      Measure.pi (fun _ : Fin k × Fin p ↦ μ) := by
    have hmp := (measurePreserving_piCongrLeft
      (fun _ : Fin (k * p) ↦ μ)
      (finProdFinEquiv : Fin k × Fin p ≃ Fin (k * p))).symm
    simpa [reindex, μ, halfGaussianPi] using hmp.map_eq
  have hcurry : Measure.map curry
      (Measure.pi (fun _ : Fin k × Fin p ↦ μ)) =
      halfGaussianRowProduct k p := by
    unfold halfGaussianRowProduct
    rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
    simp_rw [← Measure.infinitePi_eq_pi]
    exact Measure.infinitePi_map_curry
      (fun _ : Fin k ↦ fun _ : Fin p ↦ μ)
  have hfun :
      ((curriedMatrixMeasurableEquiv k p) ∘ curry) ∘ reindex =
        flatMatrixMeasurableEquiv k p := by
    funext x
    ext a i
    rfl
  rw [← hcurry, ← hreindex]
  rw [Measure.map_map (curriedMatrixMeasurableEquiv k p).measurable
      curry.measurable,
    Measure.map_map
      ((curriedMatrixMeasurableEquiv k p).measurable.comp curry.measurable)
      reindex.measurable]
  rw [hfun]
  rfl

/-- Under the matrix law, the columns are independent and every scalar
entry has the literal `N(0,1/2)` law. -/
theorem map_matrixToColumns_halfGaussianMatrix (k p : ℕ) :
    Measure.map (matrixToColumnsMeasurableEquiv k p)
        (halfGaussianMatrix k p) =
      halfGaussianColumnProduct k p := by
  rw [← map_curriedMatrix_halfGaussianRowProduct k p]
  rw [Measure.map_map (matrixToColumnsMeasurableEquiv k p).measurable
    (curriedMatrixMeasurableEquiv k p).measurable]
  have hfun :
      (matrixToColumnsMeasurableEquiv k p) ∘
          (curriedMatrixMeasurableEquiv k p) =
        LogdetLean.piTransposeMeasurableEquiv (Fin k) (Fin p) ℝ := by
    funext x
    rfl
  rw [hfun]
  exact LogdetLean.map_pi_pi_piTranspose
    (I := Fin k) (J := Fin p)
    (gaussianReal 0 halfGaussianVariance)

/-- The actual matrix columns are almost surely linearly independent under
the matrix half-Gaussian law. -/
theorem ae_linearIndependent_halfGaussianMatrix_columns
    (k p : ℕ) (hp : p ≤ k) :
    ∀ᵐ R ∂halfGaussianMatrix k p,
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2 (fun a ↦ R a j) :
          Fin p → EuclideanSpace ℝ (Fin k)) := by
  have hmp : MeasurePreserving (matrixToColumnsMeasurableEquiv k p)
      (halfGaussianMatrix k p) (halfGaussianColumnProduct k p) :=
    ⟨(matrixToColumnsMeasurableEquiv k p).measurable,
      map_matrixToColumns_halfGaussianMatrix k p⟩
  have h := hmp.quasiMeasurePreserving.ae
    (ae_linearIndependent_pi_halfGaussianColumns k p hp)
  filter_upwards [h] with R hR
  change LinearIndependent ℝ
    (fun j ↦ WithLp.toLp 2 (fun a ↦ R a j)) at hR
  exact hR

/-- The literal matrix product `RᵀR` is the inner-product Gram matrix of the
Euclideanized columns of `R`. -/
theorem realWishartGram_eq_gram_toLp_columns
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    realWishartGram R =
      Matrix.gram ℝ
        (fun j ↦ WithLp.toLp 2 (fun a ↦ R a j) :
          Fin p → EuclideanSpace ℝ (Fin k)) := by
  ext i j
  simp [realWishartGram, Matrix.mul_apply, Matrix.gram_apply,
    EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]

/-- Full column rank, equivalently invertibility of the real Wishart Gram,
holds almost surely under the literal matrix law. -/
theorem ae_isUnit_det_realWishartGram_halfGaussianMatrix
    (k p : ℕ) (hp : p ≤ k) :
    ∀ᵐ R ∂halfGaussianMatrix k p,
      IsUnit (realWishartGram R).det := by
  filter_upwards [ae_linearIndependent_halfGaussianMatrix_columns k p hp]
    with R hR
  apply isUnit_iff_ne_zero.mpr
  rw [realWishartGram_eq_gram_toLp_columns]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hR

/-- Pulling matrix integrals back to the flat coordinate product. -/
theorem integral_comp_flatMatrixMeasurableEquiv
    (k p : ℕ) (f : Matrix (Fin k) (Fin p) ℝ → ℝ) :
    (∫ x, f (flatMatrixMeasurableEquiv k p x)
        ∂halfGaussianPi (k * p)) =
      ∫ R, f R ∂halfGaussianMatrix k p := by
  exact (measurePreserving_flatMatrixMeasurableEquiv k p).integral_comp' f

end Wishart

end

end LogdetLean.GramHafnian
