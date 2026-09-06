import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.InverseTraceBounds
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.MatrixGaussianBridge
import LogdetLean.Coherence.NestedTuplePermutation
/-!
# Integrability of the inverse real-Wishart trace

The singular Stein field is dominated by the trace of an inverse Gram
matrix.  At the sharp first inverse-Wishart threshold this trace is
integrable.  The proof below reuses the kernel-checked Bartlett--Mellin
transform with a small positive exponential tilt; that tilt absorbs the
polynomial adjugate numerator.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Positivity of a diagonal Bartlett transform at exponent `-1`, with an
arbitrary admissible Laplace tilt. -/
theorem wishartDiagonalStageTransform_neg_one_pos
    {k n : ℕ} (hk : 0 < k) (hnk : n < k)
    (hshape : 0 < (((k - n : ℕ) : ℝ) / 2) - 1)
    {c : ℝ} (hrate : 0 < (1 / 2 : ℝ) + c) :
    0 < wishartDiagonalStageTransform k n (-1) c := by
  unfold wishartDiagonalStageTransform
  have hbase : 0 < (((k - n : ℕ) : ℝ) / 2) := by
    have : 0 < k - n := Nat.sub_pos_of_lt hnk
    positivity
  have hkreal : 0 < (k : ℝ) / 2 := by positivity
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hGshape : 0 < Real.Gamma ((((k - n : ℕ) : ℝ) / 2) + (-1)) := by
    apply Real.Gamma_pos_of_pos
    linarith
  have hGbase : 0 < Real.Gamma (((k - n : ℕ) : ℝ) / 2) :=
    Real.Gamma_pos_of_pos hbase
  have hp₁ : 0 < (1 / 2 : ℝ) ^ ((k : ℝ) / 2) :=
    Real.rpow_pos_of_pos hhalf _
  have hp₂ : 0 < ((1 / 2 : ℝ) + c) ^ ((k : ℝ) / 2 + (-1)) :=
    Real.rpow_pos_of_pos hrate _
  positivity

/-- Reciprocal determinant remains integrable after every admissible common
quadratic exponential tilt. -/
theorem integrable_nestedGaussianWishartKernel_neg_one_const
    {k p : ℕ} (hk : 0 < k) (hp : p ≤ k) (hgap : p + 1 < k)
    {c : ℝ} (hrate : 0 < (1 / 2 : ℝ) + c) :
    Integrable
      (nestedGaussianWishartKernel
        (E := EuclideanSpace ℝ (Fin k)) (-1) (fun _ ↦ c) p)
      (nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin k))) p) := by
  have ht : ∀ n < p,
      0 < (((k - n : ℕ) : ℝ) / 2) + (-1) := by
    intro n hn
    have hnk : n < k := lt_of_lt_of_le hn hp
    have hnat : 3 ≤ k - n := by omega
    have hcast : (3 : ℝ) ≤ ((k - n : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hrate' : ∀ n < p, 0 < (1 / 2 : ℝ) + c := by
    intro _ _
    exact hrate
  have heval := integral_nestedGaussianWishartKernel_eq_diagonal
    hk hp (fun _ ↦ c) ht hrate'
  have hprodPos : 0 <
      ∏ n ∈ Finset.range p,
        wishartDiagonalStageTransform k n (-1) c := by
    apply Finset.prod_pos
    intro n hn
    have hnp : n < p := Finset.mem_range.mp hn
    have hnk : n < k := lt_of_lt_of_le hnp hp
    exact wishartDiagonalStageTransform_neg_one_pos hk hnk (by
      linarith [ht n hnp]) hrate
  apply Integrable.of_integral_ne_zero
  rw [heval]
  exact hprodPos.ne'

/-- A convenient explicit exponential domination of `(1+x)^p`. -/
theorem one_add_pow_le_exp_div
    {p : ℕ} (hp : 0 < p) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ p ≤
      ((4 * (p : ℝ)) ^ p * (p.factorial : ℝ) *
        Real.exp (1 / (4 * (p : ℝ)))) *
      Real.exp (x / (4 * (p : ℝ))) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hfourp : 0 < (4 * (p : ℝ)) := by positivity
  let y : ℝ := (1 + x) / (4 * (p : ℝ))
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have hbase := Real.pow_div_factorial_le_exp y hy p
  have hfact : 0 < (p.factorial : ℝ) := by positivity
  have hypow : y ^ p ≤ (p.factorial : ℝ) * Real.exp y := by
    have htmp : y ^ p ≤ Real.exp y * (p.factorial : ℝ) :=
      (div_le_iff₀ hfact).mp hbase
    calc
      y ^ p ≤ Real.exp y * (p.factorial : ℝ) := htmp
      _ = (p.factorial : ℝ) * Real.exp y := mul_comm _ _
  have hscale : 1 + x = (4 * (p : ℝ)) * y := by
    dsimp [y]
    field_simp
  rw [hscale, mul_pow]
  calc
    (4 * (p : ℝ)) ^ p * y ^ p ≤
        (4 * (p : ℝ)) ^ p *
          ((p.factorial : ℝ) * Real.exp y) := by
      gcongr
    _ = ((4 * (p : ℝ)) ^ p * (p.factorial : ℝ) *
          Real.exp (1 / (4 * (p : ℝ)))) *
        Real.exp (x / (4 * (p : ℝ))) := by
      have hyadd : y = 1 / (4 * (p : ℝ)) +
          x / (4 * (p : ℝ)) := by
        dsimp [y]
        ring
      rw [hyadd, Real.exp_add]
      ring

/-- Read standard Gaussian Euclidean columns as a real matrix after the
global `1/sqrt 2` scaling which produces entry variance `1/2`. -/
def nestedStandardToHalfMatrix (k p : ℕ) :
    NestedTuple (EuclideanSpace ℝ (Fin k)) p →
      Matrix (Fin k) (Fin p) ℝ :=
  fun z a i ↦ (Real.sqrt 2)⁻¹ * (nestedTupleToFin p z i) a

@[fun_prop]
theorem measurable_nestedStandardToHalfMatrix (k p : ℕ) :
    Measurable (nestedStandardToHalfMatrix k p) := by
  apply (curriedMatrixMeasurableEquiv k p).measurable.comp
  change Measurable (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
    fun a i ↦ (Real.sqrt 2)⁻¹ * (nestedTupleToFin p z i) a)
  rw [measurable_pi_iff]
  intro a
  rw [measurable_pi_iff]
  intro i
  exact measurable_const.mul
    ((measurable_pi_apply a).comp
      ((WithLp.measurable_ofLp 2 (Fin k → ℝ)).comp
        (measurable_nestedTupleToFin_apply p i)))

/-- Converting one scaled standard Euclidean column back to raw coordinates
has exactly the iid scalar half-Gaussian law. -/
theorem map_ofLp_scaledStdGaussian_eq_halfGaussianVector (k : ℕ) :
    Measure.map
        (fun x : EuclideanSpace ℝ (Fin k) ↦ x.ofLp)
        (Measure.map
          (fun x : EuclideanSpace ℝ (Fin k) ↦
            ((Real.sqrt 2)⁻¹ : ℝ) • x)
          (stdGaussian (EuclideanSpace ℝ (Fin k)))) =
      Measure.pi (fun _ : Fin k ↦
        gaussianReal 0 halfGaussianVariance) := by
  rw [← map_toLp_halfGaussianVector k]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun :
      (fun x : EuclideanSpace ℝ (Fin k) ↦ x.ofLp) ∘
          (WithLp.toLp 2) =
        (fun x : Fin k → ℝ ↦ x) := by
    funext x
    exact WithLp.ofLp_toLp 2 x
  rw [hfun]
  exact Measure.map_id

/-- The preceding conversion is measure preserving. -/
theorem measurePreserving_ofLp_scaledStdGaussian (k : ℕ) :
    MeasurePreserving
      (fun x : EuclideanSpace ℝ (Fin k) ↦ x.ofLp)
      (Measure.map
        (fun x : EuclideanSpace ℝ (Fin k) ↦
          ((Real.sqrt 2)⁻¹ : ℝ) • x)
        (stdGaussian (EuclideanSpace ℝ (Fin k))))
      (Measure.pi (fun _ : Fin k ↦
        gaussianReal 0 halfGaussianVariance)) := by
  exact ⟨by fun_prop, map_ofLp_scaledStdGaussian_eq_halfGaussianVector k⟩

/-- The explicit nested-column conversion pushes the standard Gaussian
product law to the literal half-Gaussian matrix law. -/
theorem map_nestedStandardToHalfMatrix (k p : ℕ) :
    Measure.map (nestedStandardToHalfMatrix k p)
        (nestedProductMeasure
          (stdGaussian (EuclideanSpace ℝ (Fin k))) p) =
      halfGaussianMatrix k p := by
  let E := EuclideanSpace ℝ (Fin k)
  let c : ℝ := (Real.sqrt 2)⁻¹
  let scaleColumns : (Fin p → E) → (Fin p → E) :=
    fun v i ↦ c • v i
  let rawColumns : (Fin p → E) → (Fin p → Fin k → ℝ) :=
    fun v i ↦ (v i).ofLp
  have hnest := measurePreserving_nestedTupleToFin
    (stdGaussian E) p
  have hscale : MeasurePreserving scaleColumns
      (Measure.pi fun _ : Fin p ↦ stdGaussian E)
      (Measure.pi fun _ : Fin p ↦
        (stdGaussian E).map (fun x ↦ c • x)) := by
    apply measurePreserving_pi
    intro i
    exact ⟨by fun_prop, rfl⟩
  have hraw : MeasurePreserving rawColumns
      (Measure.pi fun _ : Fin p ↦
        (stdGaussian E).map (fun x ↦ c • x))
      (halfGaussianColumnProduct k p) := by
    apply measurePreserving_pi
    intro i
    simpa [E, c, rawColumns] using
      measurePreserving_ofLp_scaledStdGaussian k
  have hmatrix : MeasurePreserving
      (matrixToColumnsMeasurableEquiv k p).symm
      (halfGaussianColumnProduct k p)
      (halfGaussianMatrix k p) := by
    refine ⟨(matrixToColumnsMeasurableEquiv k p).symm.measurable, ?_⟩
    rw [← map_matrixToColumns_halfGaussianMatrix k p]
    rw [Measure.map_map
      (matrixToColumnsMeasurableEquiv k p).symm.measurable
      (matrixToColumnsMeasurableEquiv k p).measurable]
    have hfun :
        (matrixToColumnsMeasurableEquiv k p).symm ∘
            (matrixToColumnsMeasurableEquiv k p) =
          id := by
      funext R
      exact (matrixToColumnsMeasurableEquiv k p).symm_apply_apply R
    rw [hfun, Measure.map_id]
  have htotal := hmatrix.comp (hraw.comp (hscale.comp hnest))
  rw [← htotal.map_eq]
  congr 1

/-- The squared Frobenius mass of the scaled matrix is half the total
standard-column energy. -/
theorem rectangularSqMass_nestedStandardToHalfMatrix
    (k p : ℕ) (z : NestedTuple (EuclideanSpace ℝ (Fin k)) p) :
    rectangularSqMass (nestedStandardToHalfMatrix k p z) =
      (1 / 2 : ℝ) *
        ∑ i : Fin p, ‖nestedTupleToFin p z i‖ ^ 2 := by
  have hc : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow]
    norm_num
  unfold rectangularSqMass nestedStandardToHalfMatrix
  simp_rw [mul_pow, hc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The Gram matrix of the scaled columns is exactly one half of the
standard-column Gram matrix. -/
theorem realWishartGram_nestedStandardToHalfMatrix
    (k p : ℕ) (z : NestedTuple (EuclideanSpace ℝ (Fin k)) p) :
    realWishartGram (nestedStandardToHalfMatrix k p z) =
      (1 / 2 : ℝ) •
        Matrix.gram ℝ (nestedTupleToFin p z) := by
  have hc : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow]
    norm_num
  ext i j
  simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply,
    nestedStandardToHalfMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.gram_apply, EuclideanSpace.inner_toLp_toLp, dotProduct,
    starRingEnd_apply, star_trivial]
  calc
    (∑ a, (Real.sqrt 2)⁻¹ * (nestedTupleToFin p z i) a *
        ((Real.sqrt 2)⁻¹ * (nestedTupleToFin p z j) a)) =
        (Real.sqrt 2)⁻¹ ^ 2 *
          ∑ a, (nestedTupleToFin p z i) a *
            (nestedTupleToFin p z j) a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (1 / 2 : ℝ) *
          ∑ a, (nestedTupleToFin p z j) a *
            (nestedTupleToFin p z i) a := by
      rw [hc]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      ring

/-- The same nested standard columns, without the global half-Gaussian
scaling. -/
def nestedStandardMatrix (k p : ℕ) :
    NestedTuple (EuclideanSpace ℝ (Fin k)) p →
      Matrix (Fin k) (Fin p) ℝ :=
  fun z a i ↦ (nestedTupleToFin p z i) a

theorem realWishartGram_nestedStandardMatrix
    (k p : ℕ) (z : NestedTuple (EuclideanSpace ℝ (Fin k)) p) :
    realWishartGram (nestedStandardMatrix k p z) =
      Matrix.gram ℝ (nestedTupleToFin p z) := by
  ext i j
  simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply,
    nestedStandardMatrix, Matrix.gram_apply,
    EuclideanSpace.inner_toLp_toLp, dotProduct, starRingEnd_apply,
    star_trivial]
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [Real.inner_apply]

theorem rectangularSqMass_nestedStandardMatrix
    (k p : ℕ) (z : NestedTuple (EuclideanSpace ℝ (Fin k)) p) :
    rectangularSqMass (nestedStandardMatrix k p z) =
      ∑ i : Fin p, ‖nestedTupleToFin p z i‖ ^ 2 := by
  unfold rectangularSqMass nestedStandardMatrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- For a positive number of columns, the elementary Gram-entry bound is a
fixed dimension constant times `1 +` the rectangular squared mass. -/
theorem matrixEntryUnitBound_realWishartGram_le
    {k p : ℕ} (hp : 0 < p) (R : Matrix (Fin k) (Fin p) ℝ) :
    matrixEntryUnitBound (realWishartGram R) ≤
      (2 * (p : ℝ) ^ 2) * (1 + rectangularSqMass R) := by
  have hmass := matrixEntryAbsMass_realWishartGram_le R
  rw [Fintype.card_fin] at hmass
  have hS := rectangularSqMass_nonneg R
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hC : 1 ≤ 2 * (p : ℝ) ^ 2 := by nlinarith [sq_nonneg (p : ℝ)]
  unfold matrixEntryUnitBound
  apply max_le
  · nlinarith
  · calc
      matrixEntryAbsMass (realWishartGram R) ≤
          (p : ℝ) ^ 2 * (2 * rectangularSqMass R) := hmass
      _ = (2 * (p : ℝ) ^ 2) * rectangularSqMass R := by ring
      _ ≤ (2 * (p : ℝ) ^ 2) * (1 + rectangularSqMass R) := by
        gcongr
        linarith

/-- On the full-rank event, inverse scaling by `1/2` contributes exactly a
factor two to the inverse trace. -/
theorem trace_inv_realWishartGram_nestedStandardToHalfMatrix
    {k p : ℕ} (z : NestedTuple (EuclideanSpace ℝ (Fin k)) p)
    (hz : LinearIndependent ℝ (nestedTupleToFin p z)) :
    Matrix.trace
        (realWishartGram (nestedStandardToHalfMatrix k p z))⁻¹ =
      2 * Matrix.trace
        (Matrix.gram ℝ (nestedTupleToFin p z))⁻¹ := by
  rw [realWishartGram_nestedStandardToHalfMatrix]
  let G := Matrix.gram ℝ (nestedTupleToFin p z)
  have hdet : G.det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hz
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible (1 / 2 : ℝ) :=
    invertibleOfNonzero (by norm_num)
  change Matrix.trace ((1 / 2 : ℝ) • G)⁻¹ =
    2 * Matrix.trace G⁻¹
  have hinv : ((1 / 2 : ℝ) • G)⁻¹ =
      (⅟ (1 / 2 : ℝ)) • G⁻¹ :=
    Matrix.inv_smul (A := G) (1 / 2 : ℝ) hunit
  rw [hinv, Matrix.trace_smul]
  change (⅟ (1 / 2 : ℝ)) * Matrix.trace G⁻¹ =
    2 * Matrix.trace G⁻¹
  norm_num

/-- Explicit constant in the tilted reciprocal-determinant majorant. -/
def inverseTraceMajorantConstant (p : ℕ) : ℝ :=
  2 * (p : ℝ) * (p.factorial : ℝ) *
      (2 * (p : ℝ) ^ 2) ^ p *
    ((4 * (p : ℝ)) ^ p * (p.factorial : ℝ) *
      Real.exp (1 / (4 * (p : ℝ))))

/-- Pointwise on the full-rank event, the inverse trace is dominated by the
negative-one Bartlett kernel with a small positive exponential tilt. -/
theorem abs_trace_inv_halfMatrix_le_tiltedKernel
    {k p : ℕ} (hp : 0 < p)
    (z : NestedTuple (EuclideanSpace ℝ (Fin k)) p)
    (hz : LinearIndependent ℝ (nestedTupleToFin p z)) :
    |Matrix.trace
        (realWishartGram (nestedStandardToHalfMatrix k p z))⁻¹| ≤
      inverseTraceMajorantConstant p *
        nestedGaussianWishartKernel
          (E := EuclideanSpace ℝ (Fin k)) (-1)
          (fun _ ↦ -(1 / (4 * (p : ℝ)))) p z := by
  let G := Matrix.gram ℝ (nestedTupleToFin p z)
  let energy : ℝ := ∑ i : Fin p, ‖nestedTupleToFin p z i‖ ^ 2
  let C : ℝ := 2 * (p : ℝ) ^ 2
  let D : ℝ :=
    (4 * (p : ℝ)) ^ p * (p.factorial : ℝ) *
      Real.exp (1 / (4 * (p : ℝ)))
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have henergy : 0 ≤ energy := by
    dsimp only [energy]
    positivity
  have hdet : 0 < G.det :=
    ((Matrix.posSemidef_gram ℝ
        (nestedTupleToFin p z)).posDef_iff_det_ne_zero.mpr
      (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hz)).det_pos
  have hunit : matrixEntryUnitBound G ≤ C * (1 + energy) := by
    have h := matrixEntryUnitBound_realWishartGram_le hp
      (nestedStandardMatrix k p z)
    rw [realWishartGram_nestedStandardMatrix,
      rectangularSqMass_nestedStandardMatrix] at h
    exact h
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hunitnonneg : 0 ≤ matrixEntryUnitBound G :=
    (one_le_matrixEntryUnitBound G).trans' (by norm_num)
  have hpow :
      (matrixEntryUnitBound G) ^ p ≤
        C ^ p * (1 + energy) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hunitnonneg hunit p
  have hpoly := one_add_pow_le_exp_div hp henergy
  have hunitExp :
      (matrixEntryUnitBound G) ^ p ≤
        C ^ p * D * Real.exp (energy / (4 * (p : ℝ))) := by
    calc
      (matrixEntryUnitBound G) ^ p ≤
          C ^ p * (1 + energy) ^ p := hpow
      _ ≤ C ^ p *
          (D * Real.exp (energy / (4 * (p : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [D] using hpoly
        · positivity
      _ = C ^ p * D *
          Real.exp (energy / (4 * (p : ℝ))) := by ring
  have htrace := abs_trace_nonsingInv_le G
  rw [Fintype.card_fin, abs_of_pos hdet] at htrace
  have hdetInv : 0 ≤ G.det⁻¹ := inv_nonneg.mpr hdet.le
  have htraceExp :
      |Matrix.trace G⁻¹| ≤
        G.det⁻¹ *
          ((p : ℝ) * ((p.factorial : ℝ) *
            (C ^ p * D * Real.exp (energy / (4 * (p : ℝ)))))) := by
    exact htrace.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hunitExp (by positivity))
          (by positivity)) hdetInv)
  have hkernel :
      nestedGaussianWishartKernel
          (E := EuclideanSpace ℝ (Fin k)) (-1)
          (fun _ ↦ -(1 / (4 * (p : ℝ)))) p z =
        G.det⁻¹ * Real.exp (energy / (4 * (p : ℝ))) := by
    unfold nestedGaussianWishartKernel
    rw [Real.rpow_neg_one]
    congr 1
    dsimp only [energy]
    rw [← Finset.mul_sum]
    field_simp
  calc
    |Matrix.trace
        (realWishartGram (nestedStandardToHalfMatrix k p z))⁻¹| =
        2 * |Matrix.trace G⁻¹| := by
      rw [trace_inv_realWishartGram_nestedStandardToHalfMatrix z hz]
      change |2 * Matrix.trace G⁻¹| = 2 * |Matrix.trace G⁻¹|
      rw [abs_mul]
      norm_num
    _ ≤ 2 * (G.det⁻¹ *
          ((p : ℝ) * ((p.factorial : ℝ) *
            (C ^ p * D * Real.exp (energy / (4 * (p : ℝ))))))) := by
      exact mul_le_mul_of_nonneg_left htraceExp (by norm_num)
    _ = inverseTraceMajorantConstant p *
        (G.det⁻¹ * Real.exp (energy / (4 * (p : ℝ)))) := by
      dsimp only [inverseTraceMajorantConstant, C, D]
      ring
    _ = inverseTraceMajorantConstant p *
        nestedGaussianWishartKernel
          (E := EuclideanSpace ℝ (Fin k)) (-1)
          (fun _ ↦ -(1 / (4 * (p : ℝ)))) p z := by
      rw [hkernel]

theorem measurable_trace_nonsingInv_realWishartGram
    (k p : ℕ) :
    Measurable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace (realWishartGram R)⁻¹) := by
  have hGram : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ realWishartGram R) := by
    unfold realWishartGram
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hentry (i j : Fin p) : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ realWishartGram R i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hGram)
  have measurable_det_of_measurable
      {A : Matrix (Fin k) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ}
      (hA : Measurable A) : Measurable (fun R ↦ (A R).det) := by
    simp_rw [Matrix.det_apply']
    exact Finset.measurable_sum _ fun σ _ ↦
      measurable_const.mul (Finset.measurable_prod _ fun i _ ↦
        (measurable_pi_apply i).comp
          ((measurable_pi_apply (σ i)).comp hA))
  have hdet : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R).det) :=
    measurable_det_of_measurable hGram
  have hadj : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R).adjugate) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.adjugate_apply]
    apply measurable_det_of_measurable
    refine measurable_pi_lambda _ fun a ↦ measurable_pi_lambda _ fun b ↦ ?_
    by_cases ha : a = j
    · simp [ha]
    · simpa [Matrix.updateRow_apply, ha] using hentry a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.trace, Matrix.diag_apply,
    Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have hdiag : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R).adjugate i i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hadj)
  exact hdet.fun_inv.fun_mul hdiag

/-- At the sharp first inverse-Wishart threshold `p+1 < k`, the trace of
the nonsingular inverse of a half-Gaussian real Gram matrix is integrable. -/
theorem integrable_trace_nonsingInv_realWishartGram_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 1 < k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (realWishartGram R)⁻¹)
      (halfGaussianMatrix k p) := by
  by_cases hpzero : p = 0
  · subst p
    simpa [realWishartGram] using
      (integrable_zero : Integrable
        (fun _R : Matrix (Fin k) (Fin 0) ℝ ↦ (0 : ℝ))
        (halfGaussianMatrix k 0))
  · have hp : 0 < p := Nat.pos_of_ne_zero hpzero
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
    have hpRone : 1 ≤ (p : ℝ) := by exact_mod_cast hp
    let mu := nestedProductMeasure
      (stdGaussian (EuclideanSpace ℝ (Fin k))) p
    let c : ℝ := -(1 / (4 * (p : ℝ)))
    have hrate : 0 < (1 / 2 : ℝ) + c := by
      have heq : (1 / 2 : ℝ) + c =
          (2 * (p : ℝ) - 1) / (4 * (p : ℝ)) := by
        dsimp only [c]
        field_simp [hpR.ne']
        ring
      rw [heq]
      exact div_pos (by linarith) (by positivity)
    have hkernel : Integrable
        (nestedGaussianWishartKernel
          (E := EuclideanSpace ℝ (Fin k)) (-1) (fun _ ↦ c) p)
        mu := by
      dsimp only [mu]
      exact integrable_nestedGaussianWishartKernel_neg_one_const
        (by omega) (by omega) hgap hrate
    have hmajor : Integrable
        (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
          inverseTraceMajorantConstant p *
            nestedGaussianWishartKernel (-1) (fun _ ↦ c) p z)
        mu := by
      simpa only [smul_eq_mul] using
        hkernel.const_mul (inverseTraceMajorantConstant p)
    have hli :
        ∀ᵐ z ∂mu, LinearIndependent ℝ (nestedTupleToFin p z) := by
      dsimp only [mu]
      exact ae_linearIndependent_nested_stdGaussian p (by
        simp
        omega)
    have hsource : Integrable
        (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
          Matrix.trace
            (realWishartGram (nestedStandardToHalfMatrix k p z))⁻¹)
        mu := by
      apply Integrable.mono' hmajor
        ((measurable_trace_nonsingInv_realWishartGram k p).comp
          (measurable_nestedStandardToHalfMatrix k p)).aestronglyMeasurable
      filter_upwards [hli] with z hz
      rw [Real.norm_eq_abs]
      dsimp only [c]
      exact abs_trace_inv_halfMatrix_le_tiltedKernel hp z hz
    rw [← map_nestedStandardToHalfMatrix k p]
    apply (integrable_map_measure
      (measurable_trace_nonsingInv_realWishartGram k p).aestronglyMeasurable
      (measurable_nestedStandardToHalfMatrix k p).aemeasurable).2
    change Integrable
      (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
        Matrix.trace
          (realWishartGram (nestedStandardToHalfMatrix k p z))⁻¹)
      (nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin k))) p)
    simpa only [mu] using hsource

end Wishart

end

end LogdetLean.GramHafnian
