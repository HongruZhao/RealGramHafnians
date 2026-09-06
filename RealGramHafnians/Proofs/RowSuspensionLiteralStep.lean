import RealGramHafnians.Proofs.RowSuspensionPhysicalLaw
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralFourierStep
/-!
# The lossless one-level row-suspension recursion

This file joins physical orthogonal invariance, row-suspension compression,
and the exact singleton Gaussian mixture.  Its final theorem is

`E[V_{k+1,r}^{-1/2}] ≤ γ_{k+1} γ_{2r-1} E[V_{k,r-1}^{-1/2}]`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 5000000

@[fun_prop] theorem measurable_realCoordinateEnergy_fin {d : ℕ} :
    Measurable (realCoordinateEnergy : (Fin d → ℝ) → ℝ) := by
  unfold realCoordinateEnergy
  fun_prop

theorem norm_rowSuspensionCharacteristic_le_lower_mixture
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r)
    (t : ℝ) (z : Fin (2 * r - 1) → ℝ) :
    ‖rowSuspensionCharacteristic (2 * r - 1) k t z‖ ≤
      ∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ),
        Real.exp (-(pastRealCofactorV (by omega) A *
          (t ^ 2 * realCoordinateEnergy z)) / 2)
        ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
          standardRealGaussianVectorMeasure k) := by
  let base := realFinOddFirstCofactorIndex r hr
  have hrad := rowSuspensionCharacteristic_radial_compression_dim
    (2 * r - 1) k (by omega) t base z
  calc
    ‖rowSuspensionCharacteristic (2 * r - 1) k t z‖ ≤
        ‖rowSuspensionCharacteristic (2 * r - 1) k t
          (realSingleCoordinate base
            (Real.sqrt (realCoordinateEnergy z)))‖ := hrad
    _ = ‖finiteRealGramCofactorCharacteristic (Fin (2 * r - 1)) k
          (realSingleCoordinate base
            (t * Real.sqrt (realCoordinateEnergy z)))‖ := by
      rw [rowSuspensionCharacteristic_singleton_eq_finite]
    _ = ‖realOddCofactorRawCharacteristic (k := k) hr
          (realSingleCoordinate base
            (t * Real.sqrt (realCoordinateEnergy z)))‖ := by
      rw [realOddCofactorRawCharacteristic_eq_finite]
    _ = ∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ),
        Real.exp (-(pastRealCofactorV (by omega) A *
          (t ^ 2 * realCoordinateEnergy z)) / 2)
        ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
          standardRealGaussianVectorMeasure k) := by
      rw [realOddCofactorRawCharacteristic_singleton_first hr hr2]
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hnonneg : 0 ≤
          ∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ),
            Real.exp (-(pastRealCofactorV (by omega) A *
              (t * Real.sqrt (realCoordinateEnergy z)) ^ 2) / 2)
            ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
              standardRealGaussianVectorMeasure k) :=
        integral_nonneg fun A ↦ (Real.exp_pos _).le
      rw [abs_of_nonneg hnonneg]
      apply integral_congr_ae
      filter_upwards [] with A
      rw [mul_pow, Real.sq_sqrt (realCoordinateEnergy_nonneg z)]

def rowSuspensionLowerProductVariance
    {r k : ℕ} (hr2 : 2 ≤ r)
    (p : (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) ×
      RealGaussianEuclideanSpace (2 * r - 1)) : ℝ :=
  pastRealCofactorV (by omega) p.1 * realAuxiliaryNormSq p.2

@[fun_prop] theorem measurable_rowSuspensionLowerProductVariance
    {r k : ℕ} (hr2 : 2 ≤ r) :
    Measurable (rowSuspensionLowerProductVariance (k := k) hr2) := by
  unfold rowSuspensionLowerProductVariance
  fun_prop

theorem rowSuspensionLowerProductVariance_nonneg
    {r k : ℕ} (hr2 : 2 ≤ r)
    (p : (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) ×
      RealGaussianEuclideanSpace (2 * r - 1)) :
    0 ≤ rowSuspensionLowerProductVariance hr2 p := by
  exact mul_nonneg (pastRealCofactorV_nonneg (by omega) p.1) (sq_nonneg _)

/-- Pointwise Fourier majorant for the physical cofactor combination. -/
theorem physicalCofactorCombination_charFun_re_le_rowSuspension_product
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r)
    (xi : RealGaussianEuclideanSpace (k + 1)) :
    (charFun
      (finiteRealGramCofactorCombinationEuclideanLaw (2 * r - 1) (k + 1))
      xi).re ≤
      ∫ p : (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) ×
          RealGaussianEuclideanSpace (2 * r - 1),
        Real.exp (-(rowSuspensionLowerProductVariance hr2 p * ‖xi‖ ^ 2) / 2)
        ∂((Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
            standardRealGaussianVectorMeasure k).prod
          (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))) := by
  rw [charFun_finiteRealGramCofactorCombinationEuclideanLaw_eq_axis xi]
  rw [charFun_finiteRealGramCofactorCombinationEuclideanLaw_axis]
  let muZ : Measure (Fin (2 * r - 1) → ℝ) :=
    Measure.pi fun _ : Fin (2 * r - 1) ↦ gaussianReal 0 1
  let nu : Measure (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
      standardRealGaussianVectorMeasure k
  let f : (Fin (2 * r - 1) → ℝ) ×
      (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) → ℝ :=
    fun p ↦ Real.exp (-(pastRealCofactorV (by omega) p.2 *
      (‖xi‖ ^ 2 * realCoordinateEnergy p.1)) / 2)
  have hfmeas : Measurable f := by
    unfold f
    exact (((measurable_pastRealCofactorV (by omega)).comp measurable_snd).mul
      (measurable_const.mul
        (measurable_realCoordinateEnergy_fin.comp measurable_fst))).neg.div_const 2 |>.exp
  have hf : Integrable f (muZ.prod nu) := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with p
    dsimp [f]
    rw [abs_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.mpr
    have hV := pastRealCofactorV_nonneg (by omega) p.2
    have hxi : 0 ≤ ‖xi‖ ^ 2 := sq_nonneg _
    have henergy := realCoordinateEnergy_nonneg p.1
    have hprod : 0 ≤ pastRealCofactorV (by omega) p.2 *
        (‖xi‖ ^ 2 * realCoordinateEnergy p.1) :=
      mul_nonneg hV (mul_nonneg hxi henergy)
    nlinarith
  have hnorm :
      ‖∫ z : Fin (2 * r - 1) → ℝ,
          rowSuspensionCharacteristic (2 * r - 1) k ‖xi‖ z ∂muZ‖ ≤
        ∫ z : Fin (2 * r - 1) → ℝ,
          ∫ A, Real.exp (-(pastRealCofactorV (by omega) A *
            (‖xi‖ ^ 2 * realCoordinateEnergy z)) / 2) ∂nu ∂muZ := by
    apply norm_integral_le_of_norm_le hf.integral_prod_left
    · filter_upwards [] with z
      exact norm_rowSuspensionCharacteristic_le_lower_mixture
        hr hr2 ‖xi‖ z
  calc
    (∫ z : Fin (2 * r - 1) → ℝ,
        rowSuspensionCharacteristic (2 * r - 1) k ‖xi‖ z ∂muZ).re ≤
      ‖∫ z : Fin (2 * r - 1) → ℝ,
        rowSuspensionCharacteristic (2 * r - 1) k ‖xi‖ z ∂muZ‖ :=
        Complex.re_le_norm _
    _ ≤ ∫ z : Fin (2 * r - 1) → ℝ,
          ∫ A, Real.exp (-(pastRealCofactorV (by omega) A *
            (‖xi‖ ^ 2 * realCoordinateEnergy z)) / 2) ∂nu ∂muZ := hnorm
    _ = ∫ p : (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) ×
          RealGaussianEuclideanSpace (2 * r - 1),
        Real.exp (-(rowSuspensionLowerProductVariance hr2 p * ‖xi‖ ^ 2) / 2)
        ∂(nu.prod (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))) := by
      have hprod : Integrable
          (fun p : (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) ×
              RealGaussianEuclideanSpace (2 * r - 1) ↦
            Real.exp (-(rowSuspensionLowerProductVariance hr2 p *
              ‖xi‖ ^ 2) / 2))
          (nu.prod (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))) := by
        have hmeas : Measurable
            (fun p : (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) ×
                RealGaussianEuclideanSpace (2 * r - 1) ↦
              Real.exp (-(rowSuspensionLowerProductVariance hr2 p *
                ‖xi‖ ^ 2) / 2)) :=
          ((measurable_rowSuspensionLowerProductVariance hr2).mul
            measurable_const).neg.div_const 2 |>.exp
        apply Integrable.of_bound hmeas.aestronglyMeasurable 1
        filter_upwards [] with p
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        apply Real.exp_le_one_iff.mpr
        have hp := rowSuspensionLowerProductVariance_nonneg hr2 p
        have hxi : 0 ≤ ‖xi‖ ^ 2 := sq_nonneg _
        nlinarith
      rw [integral_prod _ hprod]
      rw [integral_integral_swap hf]
      apply integral_congr_ae
      filter_upwards [] with A
      rw [← map_pi_eq_stdGaussian]
      have hinner : Measurable
          (fun y : RealGaussianEuclideanSpace (2 * r - 1) ↦
            Real.exp (-(rowSuspensionLowerProductVariance hr2 (A, y) *
              ‖xi‖ ^ 2) / 2)) :=
        (((measurable_rowSuspensionLowerProductVariance hr2).comp
          (measurable_const.prodMk measurable_id)).mul
          measurable_const).neg.div_const 2 |>.exp
      rw [integral_map (by fun_prop) hinner.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with z
      unfold rowSuspensionLowerProductVariance realAuxiliaryNormSq
      have henergy : realCoordinateEnergy z =
          ‖(WithLp.toLp 2 z : RealGaussianEuclideanSpace (2 * r - 1))‖ ^ 2 := by
        simpa using realCoordinateEnergy_euclideanSpace_coe
          (WithLp.toLp 2 z : RealGaussianEuclideanSpace (2 * r - 1))
      rw [henergy]
      congr 2
      ring

end

end LogdetLean.GramHafnian
