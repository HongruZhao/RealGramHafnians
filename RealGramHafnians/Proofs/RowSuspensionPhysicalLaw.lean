import RealGramHafnians.Proofs.RowSuspensionGlobalCompression
import LogdetLean.MatrixSphericalExtension
import LogdetLean.GaussianColumnProduct
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealFourierGammaFactor
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealCofactorAlmostSurePositivity
/-!
# The physical cofactor-combination law

The older beta-one development packages the cofactor vector in its column
index space.  Row suspension instead acts on the physical vector

`q(A) = \sum_i C_i(A) A_i`.

This file defines its Euclidean law and proves the deterministic orthogonal
covariance needed to reduce every Fourier direction to the first physical
coordinate.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 4000000

/-- The physical cofactor combination for a finite Euclidean column family. -/
def finiteRealGramCofactorCombinationEuclidean {d k : ℕ}
    (A : Fin d → RealGaussianEuclideanSpace k) :
    RealGaussianEuclideanSpace k :=
  ∑ i : Fin d,
    finiteRealGramCofactorVector (fun j p ↦ A j p) i • A i

@[fun_prop] theorem measurable_finiteRealGramCofactorCombinationEuclidean
    {d k : ℕ} :
    Measurable (finiteRealGramCofactorCombinationEuclidean (d := d) (k := k)) := by
  unfold finiteRealGramCofactorCombinationEuclidean
  fun_prop

/-- Pushforward law of the physical cofactor combination. -/
def finiteRealGramCofactorCombinationEuclideanLaw (d k : ℕ) :
    Measure (RealGaussianEuclideanSpace k) :=
  Measure.map finiteRealGramCofactorCombinationEuclidean
    (Measure.pi fun _ : Fin d ↦ stdGaussian (RealGaussianEuclideanSpace k))

instance finiteRealGramCofactorCombinationEuclideanLaw_isProbabilityMeasure
    (d k : ℕ) :
    IsProbabilityMeasure (finiteRealGramCofactorCombinationEuclideanLaw d k) := by
  unfold finiteRealGramCofactorCombinationEuclideanLaw
  exact Measure.isProbabilityMeasure_map
    measurable_finiteRealGramCofactorCombinationEuclidean.aemeasurable

theorem finiteRealGramCofactorVector_map_linearIsometryEquiv
    {d k : ℕ} (T : RealGaussianEuclideanSpace k ≃ₗᵢ[ℝ]
      RealGaussianEuclideanSpace k)
    (A : Fin d → RealGaussianEuclideanSpace k) (i : Fin d) :
    finiteRealGramCofactorVector (fun j p ↦ T (A j) p) i =
      finiteRealGramCofactorVector (fun j p ↦ A j p) i := by
  unfold finiteRealGramCofactorVector
  congr 1
  funext a b
  unfold realColumnTransposeGram
  simpa only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
    star_trivial] using
    T.inner_map_map (A b.1) (A a.1)

theorem finiteRealGramCofactorCombinationEuclidean_map_linearIsometryEquiv
    {d k : ℕ} (T : RealGaussianEuclideanSpace k ≃ₗᵢ[ℝ]
      RealGaussianEuclideanSpace k)
    (A : Fin d → RealGaussianEuclideanSpace k) :
    finiteRealGramCofactorCombinationEuclidean (fun i ↦ T (A i)) =
      T (finiteRealGramCofactorCombinationEuclidean A) := by
  unfold finiteRealGramCofactorCombinationEuclidean
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul]
  congr 1
  exact finiteRealGramCofactorVector_map_linearIsometryEquiv T A i

/-- Applying one orthogonal transformation to every iid Gaussian column
preserves the product law. -/
theorem map_euclideanColumnFamily_linearIsometryEquiv
    {d k : ℕ} (T : RealGaussianEuclideanSpace k ≃ₗᵢ[ℝ]
      RealGaussianEuclideanSpace k) :
    Measure.map (fun A : Fin d → RealGaussianEuclideanSpace k ↦
        fun i ↦ T (A i))
      (Measure.pi fun _ : Fin d ↦ stdGaussian (RealGaussianEuclideanSpace k)) =
    Measure.pi fun _ : Fin d ↦ stdGaussian (RealGaussianEuclideanSpace k) := by
  have hfun :
      (fun A : Fin d → RealGaussianEuclideanSpace k ↦ fun i ↦ T (A i)) =
        LogdetLean.mapColumnIsometry (p := d) T.toLinearIsometry := by
    rfl
  rw [hfun]
  exact LogdetLean.map_mapColumnIsometry_pi_stdGaussian (p := d) T

theorem finiteRealGramCofactorCombinationEuclideanLaw_orthogonalInvariant
    {d k : ℕ} (T : RealGaussianEuclideanSpace k ≃ₗᵢ[ℝ]
      RealGaussianEuclideanSpace k) :
    Measure.map T (finiteRealGramCofactorCombinationEuclideanLaw d k) =
      finiteRealGramCofactorCombinationEuclideanLaw d k := by
  unfold finiteRealGramCofactorCombinationEuclideanLaw
  rw [Measure.map_map]
  · let F : (Fin d → RealGaussianEuclideanSpace k) →
        (Fin d → RealGaussianEuclideanSpace k) := fun A i ↦ T (A i)
    have hfun :
        (T : RealGaussianEuclideanSpace k → RealGaussianEuclideanSpace k) ∘
            finiteRealGramCofactorCombinationEuclidean =
          finiteRealGramCofactorCombinationEuclidean ∘ F := by
      funext A
      exact (finiteRealGramCofactorCombinationEuclidean_map_linearIsometryEquiv
        T A).symm
    rw [hfun, ← Measure.map_map]
    · rw [show Measure.map F
          (Measure.pi fun _ : Fin d ↦ stdGaussian (RealGaussianEuclideanSpace k)) =
          Measure.pi fun _ : Fin d ↦ stdGaussian (RealGaussianEuclideanSpace k) by
        exact map_euclideanColumnFamily_linearIsometryEquiv T]
    · fun_prop
    · fun_prop
  · fun_prop
  · fun_prop

theorem charFun_finiteRealGramCofactorCombinationEuclideanLaw_orthogonal
    {d k : ℕ} (T : RealGaussianEuclideanSpace k ≃ₗᵢ[ℝ]
      RealGaussianEuclideanSpace k)
    (xi : RealGaussianEuclideanSpace k) :
    charFun (finiteRealGramCofactorCombinationEuclideanLaw d k) xi =
      charFun (finiteRealGramCofactorCombinationEuclideanLaw d k) (T.symm xi) := by
  let mu := finiteRealGramCofactorCombinationEuclideanLaw d k
  calc
    charFun mu xi = charFun (Measure.map T mu) xi := by
      rw [finiteRealGramCofactorCombinationEuclideanLaw_orthogonalInvariant T]
    _ = charFun mu (T.symm xi) := by
      unfold charFun
      rw [integral_map T.continuous.measurable.aemeasurable (by fun_prop)]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [T.inner_map_eq_flip]

/-- In positive dimension, an orthogonal map can send the first coordinate
axis to any prescribed unit direction. -/
theorem exists_linearIsometryEquiv_axis_to_normalize
    {k : ℕ} (xi : RealGaussianEuclideanSpace (k + 1)) (hxi : xi ≠ 0) :
    ∃ T : RealGaussianEuclideanSpace (k + 1) ≃ₗᵢ[ℝ]
        RealGaussianEuclideanSpace (k + 1),
      T (EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) =
        NormedSpace.normalize xi := by
  let v : Fin (k + 1) → RealGaussianEuclideanSpace (k + 1) :=
    fun _ ↦ NormedSpace.normalize xi
  let s : Set (Fin (k + 1)) := {0}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro j
    simpa [v] using NormedSpace.norm_normalize hxi
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let T : RealGaussianEuclideanSpace (k + 1) ≃ₗᵢ[ℝ]
      RealGaussianEuclideanSpace (k + 1) :=
    (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).equiv b (Equiv.refl _)
  refine ⟨T, ?_⟩
  rw [show T (EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) = b 0 by
    exact OrthonormalBasis.equiv_apply_basis _ _ _ 0]
  simpa [s, v] using hb 0 (by simp [s])

theorem charFun_finiteRealGramCofactorCombinationEuclideanLaw_eq_axis
    {d k : ℕ} (xi : RealGaussianEuclideanSpace (k + 1)) :
    charFun (finiteRealGramCofactorCombinationEuclideanLaw d (k + 1)) xi =
      charFun (finiteRealGramCofactorCombinationEuclideanLaw d (k + 1))
        (‖xi‖ • EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) := by
  by_cases hxi : xi = 0
  · subst xi
    simp
  · obtain ⟨T, hT⟩ := exists_linearIsometryEquiv_axis_to_normalize xi hxi
    rw [charFun_finiteRealGramCofactorCombinationEuclideanLaw_orthogonal T xi]
    congr 1
    apply T.injective
    rw [T.apply_symm_apply, map_smul, hT,
      NormedSpace.norm_smul_normalize xi]

/-! ## Splitting the first physical row -/

def suspensionEuclideanColumnEquiv (k : ℕ) :
    (ℝ × (Fin k → ℝ)) ≃ᵐ RealGaussianEuclideanSpace (k + 1) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (k + 1) ↦ ℝ) 0).symm.trans
    (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ))

theorem suspensionEuclideanColumnEquiv_apply
    {k : ℕ} (x : ℝ) (X : Fin k → ℝ) :
    suspensionEuclideanColumnEquiv k (x, X) =
      WithLp.toLp 2 (prependRealCoordinate x X) := by
  apply (WithLp.linearEquiv 2 ℝ (Fin (k + 1) → ℝ)).injective
  change
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (k + 1) ↦ ℝ) 0).symm (x, X) =
      prependRealCoordinate x X
  funext p
  refine Fin.cases ?_ (fun i ↦ ?_) p
  · rfl
  · rfl

theorem measurePreserving_suspensionEuclideanColumnEquiv (k : ℕ) :
    MeasurePreserving (suspensionEuclideanColumnEquiv k)
      ((gaussianReal 0 1).prod (standardRealGaussianVectorMeasure k))
      (stdGaussian (RealGaussianEuclideanSpace (k + 1))) := by
  have hsplit :=
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (k + 1) ↦ gaussianReal 0 1) 0).symm
  have hlp : MeasurePreserving
      (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ))
      (Measure.pi fun _ : Fin (k + 1) ↦ gaussianReal 0 1)
      (stdGaussian (RealGaussianEuclideanSpace (k + 1))) := by
    refine ⟨(MeasurableEquiv.toLp 2 _).measurable, ?_⟩
    exact map_pi_eq_stdGaussian
  exact hlp.comp hsplit

def assembleRowSuspensionEuclideanColumns {d k : ℕ}
    (p : (Fin d → ℝ) × (Fin d → (Fin k → ℝ))) :
    Fin d → RealGaussianEuclideanSpace (k + 1) :=
  fun i ↦ suspensionEuclideanColumnEquiv k (p.1 i, p.2 i)

@[fun_prop] theorem measurable_assembleRowSuspensionEuclideanColumns
    {d k : ℕ} :
    Measurable (assembleRowSuspensionEuclideanColumns (d := d) (k := k)) := by
  unfold assembleRowSuspensionEuclideanColumns
  fun_prop

theorem measurePreserving_assembleRowSuspensionEuclideanColumns
    (d k : ℕ) :
    MeasurePreserving (assembleRowSuspensionEuclideanColumns (d := d) (k := k))
      ((Measure.pi fun _ : Fin d ↦ gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin d ↦ standardRealGaussianVectorMeasure k))
      (Measure.pi fun _ : Fin d ↦
        stdGaussian (RealGaussianEuclideanSpace (k + 1))) := by
  let pairLaw : Measure (ℝ × (Fin k → ℝ)) :=
    (gaussianReal 0 1).prod (standardRealGaussianVectorMeasure k)
  have hreorder : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin k → ℝ) (Fin d)).symm
      ((Measure.pi fun _ : Fin d ↦ gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin d ↦ standardRealGaussianVectorMeasure k))
      (Measure.pi fun _ : Fin d ↦ pairLaw) := by
    exact (measurePreserving_arrowProdEquivProdArrow
      ℝ (Fin k → ℝ) (Fin d)
      (fun _ ↦ gaussianReal 0 1)
      (fun _ ↦ standardRealGaussianVectorMeasure k)).symm
  have hcolumns : MeasurePreserving
      (fun P : Fin d → (ℝ × (Fin k → ℝ)) ↦
        fun i ↦ suspensionEuclideanColumnEquiv k (P i))
      (Measure.pi fun _ : Fin d ↦ pairLaw)
      (Measure.pi fun _ : Fin d ↦
        stdGaussian (RealGaussianEuclideanSpace (k + 1))) := by
    apply measurePreserving_pi
    intro i
    exact measurePreserving_suspensionEuclideanColumnEquiv k
  have h := hcolumns.comp hreorder
  convert h using 1
  funext p
  rfl

theorem finiteRealGramCofactorCombinationEuclidean_assemble_apply_zero
    {d k : ℕ} (z : Fin d → ℝ) (B : Fin d → (Fin k → ℝ)) :
    finiteRealGramCofactorCombinationEuclidean
        (assembleRowSuspensionEuclideanColumns (z, B)) 0 =
      rowSuspensionPhase z B := by
  have hA : assembleRowSuspensionEuclideanColumns (z, B) =
      fun i ↦ WithLp.toLp 2 (rowSuspensionColumns z B i) := by
    funext i
    exact suspensionEuclideanColumnEquiv_apply (z i) (B i)
  rw [hA]
  unfold finiteRealGramCofactorCombinationEuclidean rowSuspensionPhase
    finiteRealGramCofactorPhase
  change
    ((WithLp.linearEquiv 2 ℝ (Fin (k + 1) → ℝ))
      (∑ i : Fin d,
        finiteRealGramCofactorVector (rowSuspensionColumns z B) i •
          WithLp.toLp 2 (rowSuspensionColumns z B i))) 0 = _
  rw [map_sum]
  simp only [map_smul, WithLp.coe_linearEquiv, WithLp.ofLp_toLp,
    Finset.sum_apply, Pi.smul_apply, rowSuspensionColumns,
    prependRealCoordinate_zero, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The characteristic function on the first physical axis is exactly the
outer Gaussian average of the row-suspension characteristic. -/
theorem charFun_finiteRealGramCofactorCombinationEuclideanLaw_axis
    {d k : ℕ} (t : ℝ) :
    charFun (finiteRealGramCofactorCombinationEuclideanLaw d (k + 1))
        (t • EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) =
      ∫ z : Fin d → ℝ, rowSuspensionCharacteristic d k t z
        ∂(Measure.pi fun _ : Fin d ↦ gaussianReal 0 1) := by
  let muZ : Measure (Fin d → ℝ) :=
    Measure.pi fun _ : Fin d ↦ gaussianReal 0 1
  let muB : Measure (Fin d → (Fin k → ℝ)) :=
    Measure.pi fun _ : Fin d ↦ standardRealGaussianVectorMeasure k
  have hmp := measurePreserving_assembleRowSuspensionEuclideanColumns d k
  unfold finiteRealGramCofactorCombinationEuclideanLaw charFun
  rw [integral_map
    measurable_finiteRealGramCofactorCombinationEuclidean.aemeasurable
    (by fun_prop)]
  rw [← hmp.map_eq]
  rw [integral_map
    measurable_assembleRowSuspensionEuclideanColumns.aemeasurable
    (by fun_prop)]
  have hint : Integrable
      (fun p : (Fin d → ℝ) × (Fin d → (Fin k → ℝ)) ↦
        Complex.exp
          ((inner ℝ
            (finiteRealGramCofactorCombinationEuclidean
              (assembleRowSuspensionEuclideanColumns p))
            (t • EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) : ℝ) *
              Complex.I)) (muZ.prod muB) := by
    have hq : Measurable (fun p :
        (Fin d → ℝ) × (Fin d → (Fin k → ℝ)) ↦
        finiteRealGramCofactorCombinationEuclidean
          (assembleRowSuspensionEuclideanColumns p)) :=
      measurable_finiteRealGramCofactorCombinationEuclidean.comp
        measurable_assembleRowSuspensionEuclideanColumns
    have hinner : Measurable (fun p :
        (Fin d → ℝ) × (Fin d → (Fin k → ℝ)) ↦
        inner ℝ
          (finiteRealGramCofactorCombinationEuclidean
            (assembleRowSuspensionEuclideanColumns p))
          (t • EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0)) :=
      hq.inner measurable_const
    have hcomplex : Measurable (fun p :
        (Fin d → ℝ) × (Fin d → (Fin k → ℝ)) ↦
        ((inner ℝ
          (finiteRealGramCofactorCombinationEuclidean
            (assembleRowSuspensionEuclideanColumns p))
          (t • EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) : ℝ) : ℂ) *
            Complex.I) := by
      fun_prop
    apply Integrable.of_bound hcomplex.cexp.aestronglyMeasurable 1
    filter_upwards [] with p
    rw [Complex.norm_exp]
    simp
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [] with z
  unfold rowSuspensionCharacteristic
  apply integral_congr_ae
  filter_upwards [] with B
  unfold rowSuspensionPhaseCharacter
  rw [show inner ℝ
      (finiteRealGramCofactorCombinationEuclidean
        (assembleRowSuspensionEuclideanColumns (z, B)))
      (t • EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) =
      t * rowSuspensionPhase z B by
    rw [inner_smul_right, EuclideanSpace.inner_basisFun_real,
      finiteRealGramCofactorCombinationEuclidean_assemble_apply_zero]
    ]

end

end LogdetLean.GramHafnian
