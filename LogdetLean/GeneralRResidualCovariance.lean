import LogdetLean.GaussianColumnProduct
import LogdetLean.ChebyshevKolmogorov
import LogdetLean.GeneralRConcreteRates
import LogdetLean.GeneralRPairLaplace
import LogdetLean.HermiteResidualProjection
import LogdetLean.KibbleCovarianceBounds
import Mathlib.Tactic
/-!
# Actual general-correlation nonlinear residual covariance

This module closes the model-specific Gaussian pair bridge for Zhao's
nonlinear log-radius remainder.  It realizes two correlated columns as the
canonical Mehler pair, verifies the second-chaos cancellations on that common
probability space, transfers them back to the Gaussian data model, and combines
them with the compact Frullani--Laplace tail estimate.  The headline result is
the unconditional sharp bound

`Var(E_R) <= 4 (p + a_R) / m^2`.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Module WithLp
open scoped BigOperators RealInnerProductSpace

namespace GeneralRDecomposition

lemma integral_e_m_stdGaussian_eq_zero {m : ℕ} (hm : 0 < m) :
    ∫ x, e_m m x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0 := by
  let R : CorrelationMatrix 1 := CorrelationMatrix.identity 1
  let i : Fin 1 := 0
  have hG := hasLaw_G_stdGaussian (m := m) R i
  have h := hG.integral_comp (measurable_e_m m).aestronglyMeasurable
  change (∫ z, e_m m (G R z i) ∂standardGaussianDataMeasure m 1) = _ at h
  rw [integral_e_m_G_eq_zero_unconditional hm R i] at h
  exact h.symm

lemma integral_u_m_stdGaussian_eq_zero {m : ℕ} :
    ∫ x, u_m m x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0 := by
  let R : CorrelationMatrix 1 := CorrelationMatrix.identity 1
  let i : Fin 1 := 0
  have hG := hasLaw_G_stdGaussian (m := m) R i
  have h := hG.integral_comp (measurable_u_m m).aestronglyMeasurable
  change (∫ z, u_m m (G R z i) ∂standardGaussianDataMeasure m 1) = _ at h
  rw [integral_u_m_G_eq_zero R i] at h
  exact h.symm

lemma memLp_u_m_stdGaussian_two {m : ℕ} (hm : 0 < m) :
    MemLp (u_m m) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  let R : CorrelationMatrix 1 := CorrelationMatrix.identity 1
  let i : Fin 1 := 0
  have hG := hasLaw_G_stdGaussian (m := m) R i
  have hid : HasLaw (id : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m))
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := HasLaw.id
  have hident := hG.identDistrib hid
  have huident := hident.comp (measurable_u_m m)
  exact huident.memLp_iff.mp (memLp_u_m_G_two hm R i)

lemma integral_coordinate_stdGaussian_eq_zero {m : ℕ} (k : Fin m) :
    ∫ x : EuclideanSpace ℝ (Fin m), x k
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0 := by
  let L := EuclideanSpace.proj (𝕜 := ℝ) k
  have hint : Integrable (id : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := IsGaussian.integrable_id
  have h := L.integral_comp_comm
    hint
  change (∫ x : EuclideanSpace ℝ (Fin m), x k
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
    L (∫ x : EuclideanSpace ℝ (Fin m), x
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) at h
  rw [integral_id_stdGaussian] at h
  simpa [L] using h

lemma u_m_mehler_expansion {m : ℕ} (hm : 0 < m)
    {rho c : ℝ} (hrc : rho ^ 2 + c ^ 2 = 1)
    (x y : EuclideanSpace ℝ (Fin m)) :
    u_m m (rho • x + c • y) =
      rho ^ 2 * u_m m x + c ^ 2 * u_m m y +
        (2 * rho * c / (m : ℝ)) * ∑ k, x k * y k := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold u_m
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  change ((∑ k, (rho * x k + c * y k) ^ 2) - (m : ℝ)) / (m : ℝ) = _
  simp_rw [add_pow_two, mul_pow]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp
  have hcross :
      (∑ k, rho * 2 * x k * c * y k) =
        rho * 2 * c * ∑ k, x k * y k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [hcross]
  nlinarith [hrc]

theorem integral_e_m_mul_u_m_mehler_eq_zero {m : ℕ} (hm : 0 < m)
    {rho : ℝ} (hrho : |rho| ≤ 1) :
    ∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        e_m m w.1 *
          u_m m (rho • w.1 + Real.sqrt (1 - rho ^ 2) • w.2)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m)))) = 0 := by
  let c := Real.sqrt (1 - rho ^ 2)
  have hrho2 : rho ^ 2 ≤ 1 := by
    rw [abs_le] at hrho
    nlinarith [sq_nonneg (rho - 1), sq_nonneg (rho + 1)]
  have hc2 : c ^ 2 = 1 - rho ^ 2 := by
    dsimp [c]
    exact Real.sq_sqrt (sub_nonneg.mpr hrho2)
  have hrc : rho ^ 2 + c ^ 2 = 1 := by rw [hc2]; ring
  change (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      e_m m w.1 * u_m m (rho • w.1 + c • w.2)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m))))) = 0
  simp_rw [u_m_mehler_expansion hm hrc]
  have hpoint : (fun w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
      e_m m w.1 *
        (rho ^ 2 * u_m m w.1 + c ^ 2 * u_m m w.2 +
          (2 * rho * c / (m : ℝ)) * ∑ k, w.1 k * w.2 k)) =
      (fun w ↦
        rho ^ 2 * (e_m m w.1 * u_m m w.1) * 1 +
        c ^ 2 * (e_m m w.1 * u_m m w.2) +
        (2 * rho * c / (m : ℝ)) *
          ∑ k, (e_m m w.1 * w.1 k) * w.2 k) := by
    funext w
    have hsum : e_m m w.1 *
        ((2 * rho * c / (m : ℝ)) * ∑ k, w.1 k * w.2 k) =
        (2 * rho * c / (m : ℝ)) *
          ∑ k, (e_m m w.1 * w.1 k) * w.2 k := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    rw [mul_add, mul_add, hsum]
    ring
  let μ := stdGaussian (EuclideanSpace ℝ (Fin m))
  have heu : Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦
      e_m m x * u_m m x) μ :=
    MemLp.integrable_mul (memLp_e_m_stdGaussian_two hm)
      (memLp_u_m_stdGaussian_two hm)
  have he : Integrable (e_m m) μ :=
    (memLp_e_m_stdGaussian_two hm).integrable (by norm_num)
  have hu : Integrable (u_m m) μ :=
    (memLp_u_m_stdGaussian_two hm).integrable (by norm_num)
  have hcoord (k : Fin m) : Integrable
      (fun x : EuclideanSpace ℝ (Fin m) ↦ x k) μ :=
    ((IsGaussian.memLp_id (μ := μ) 2 (by norm_num)).continuousLinearMap_comp
      (EuclideanSpace.proj (𝕜 := ℝ) k)).integrable (by norm_num)
  have hecoord (k : Fin m) : Integrable
      (fun x : EuclideanSpace ℝ (Fin m) ↦ e_m m x * x k) μ :=
    MemLp.integrable_mul (memLp_e_m_stdGaussian_two hm)
      ((IsGaussian.memLp_id (μ := μ) 2 (by norm_num)).continuousLinearMap_comp
        (EuclideanSpace.proj (𝕜 := ℝ) k))
  have hfirst : Integrable (fun w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
      rho ^ 2 * (e_m m w.1 * u_m m w.1) * 1) (μ.prod μ) := by
    simpa [mul_assoc] using
      (heu.mul_prod (integrable_const (μ := μ) (1 : ℝ))).const_mul (rho ^ 2)
  have hsecond : Integrable (fun w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
      c ^ 2 * (e_m m w.1 * u_m m w.2)) (μ.prod μ) := by
    exact (he.mul_prod hu).const_mul (c ^ 2)
  have hthirdTerm (k : Fin m) : Integrable
      (fun w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) ↦
        (e_m m w.1 * w.1 k) * w.2 k) (μ.prod μ) :=
    (hecoord k).mul_prod (hcoord k)
  have hthird : Integrable (fun w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
      (2 * rho * c / (m : ℝ)) *
        ∑ k, (e_m m w.1 * w.1 k) * w.2 k) (μ.prod μ) := by
    exact (integrable_finsetSum Finset.univ fun k _ ↦ hthirdTerm k).const_mul _
  rw [hpoint]
  change (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      (rho ^ 2 * (e_m m w.1 * u_m m w.1) * 1 +
        c ^ 2 * (e_m m w.1 * u_m m w.2)) +
        (2 * rho * c / (m : ℝ)) *
          ∑ k, (e_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) = 0
  have hfirstInt : (∫ w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m),
      rho ^ 2 * (e_m m w.1 * u_m m w.1) * 1 ∂μ.prod μ) = 0 := by
    have hp := integral_prod_mul
      (μ := μ) (ν := μ)
      (fun x : EuclideanSpace ℝ (Fin m) ↦ e_m m x * u_m m x)
      (fun _x : EuclideanSpace ℝ (Fin m) ↦ (1 : ℝ))
    calc
      (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
          rho ^ 2 * (e_m m w.1 * u_m m w.1) * 1 ∂μ.prod μ) =
          rho ^ 2 * ∫ w, (e_m m w.1 * u_m m w.1) * 1 ∂μ.prod μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with w
        ring
      _ = rho ^ 2 *
          ((∫ x, e_m m x * u_m m x ∂μ) * ∫ _x : EuclideanSpace ℝ (Fin m), 1 ∂μ) := by
        rw [hp]
      _ = 0 := by
        rw [integral_e_m_mul_u_m_stdGaussian_eq_zero hm]
        ring
  have hsecondInt : (∫ w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m),
      c ^ 2 * (e_m m w.1 * u_m m w.2) ∂μ.prod μ) = 0 := by
    rw [integral_const_mul, integral_prod_mul,
      integral_e_m_stdGaussian_eq_zero hm, zero_mul, mul_zero]
  have hthirdInt : (∫ w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m),
      (2 * rho * c / (m : ℝ)) *
        ∑ k, (e_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) = 0 := by
    rw [integral_const_mul,
      integral_finsetSum Finset.univ (fun k _ ↦ hthirdTerm k)]
    have hsumzero : (∑ k : Fin m,
        ∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
          (e_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      calc
        (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
            (e_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) =
            (∫ x, e_m m x * x k ∂μ) * (∫ y, y k ∂μ) := by
          exact integral_prod_mul
            (fun x : EuclideanSpace ℝ (Fin m) ↦ e_m m x * x k)
            (fun y : EuclideanSpace ℝ (Fin m) ↦ y k)
        _ = 0 := by
          rw [integral_e_m_mul_coordinate_eq_zero,
            integral_coordinate_stdGaussian_eq_zero]
          ring
    rw [hsumzero]
    ring
  calc
    (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        (rho ^ 2 * (e_m m w.1 * u_m m w.1) * 1 +
          c ^ 2 * (e_m m w.1 * u_m m w.2)) +
          (2 * rho * c / (m : ℝ)) *
            ∑ k, (e_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) =
        (∫ w, rho ^ 2 * (e_m m w.1 * u_m m w.1) * 1 +
          c ^ 2 * (e_m m w.1 * u_m m w.2) ∂μ.prod μ) +
        (∫ w, (2 * rho * c / (m : ℝ)) *
          ∑ k, (e_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) := by
      simpa only [Pi.add_apply] using
        integral_add (hfirst.add hsecond) hthird
    _ = ((∫ w, rho ^ 2 * (e_m m w.1 * u_m m w.1) * 1 ∂μ.prod μ) +
        (∫ w, c ^ 2 * (e_m m w.1 * u_m m w.2) ∂μ.prod μ)) +
        (∫ w, (2 * rho * c / (m : ℝ)) *
          ∑ k, (e_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) := by
      rw [integral_add hfirst hsecond]
    _ = 0 := by rw [hfirstInt, hsecondInt, hthirdInt]; ring

lemma integral_u_m_sq_stdGaussian_eq {m : ℕ} (hm : 0 < m) :
    ∫ x, u_m m x ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin m)) =
      2 / (m : ℝ) := by
  let R : CorrelationMatrix 1 := CorrelationMatrix.identity 1
  let i : Fin 1 := 0
  have hG := hasLaw_G_stdGaussian (m := m) R i
  have h := hG.integral_comp
    ((measurable_u_m m).pow_const 2).aestronglyMeasurable
  change (∫ z, u_m m (G R z i) ^ 2
    ∂standardGaussianDataMeasure m 1) = _ at h
  rw [integral_u_m_G_sq_eq hm R i] at h
  exact h.symm

theorem integral_u_m_mul_u_m_mehler_eq {m : ℕ} (hm : 0 < m)
    {rho : ℝ} (hrho : |rho| ≤ 1) :
    ∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        u_m m w.1 *
          u_m m (rho • w.1 + Real.sqrt (1 - rho ^ 2) • w.2)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m)))) =
      2 * rho ^ 2 / (m : ℝ) := by
  let c := Real.sqrt (1 - rho ^ 2)
  have hrho2 : rho ^ 2 ≤ 1 := by
    rw [abs_le] at hrho
    nlinarith [sq_nonneg (rho - 1), sq_nonneg (rho + 1)]
  have hc2 : c ^ 2 = 1 - rho ^ 2 := by
    dsimp [c]
    exact Real.sq_sqrt (sub_nonneg.mpr hrho2)
  have hrc : rho ^ 2 + c ^ 2 = 1 := by rw [hc2]; ring
  change (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      u_m m w.1 * u_m m (rho • w.1 + c • w.2)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m))))) = _
  simp_rw [u_m_mehler_expansion hm hrc]
  let μ := stdGaussian (EuclideanSpace ℝ (Fin m))
  have hu2 : Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦
      u_m m x * u_m m x) μ :=
    MemLp.integrable_mul (memLp_u_m_stdGaussian_two hm)
      (memLp_u_m_stdGaussian_two hm)
  have hu : Integrable (u_m m) μ :=
    (memLp_u_m_stdGaussian_two hm).integrable (by norm_num)
  have hcoord (k : Fin m) : Integrable
      (fun x : EuclideanSpace ℝ (Fin m) ↦ x k) μ :=
    ((IsGaussian.memLp_id (μ := μ) 2 (by norm_num)).continuousLinearMap_comp
      (EuclideanSpace.proj (𝕜 := ℝ) k)).integrable (by norm_num)
  have hucoord (k : Fin m) : Integrable
      (fun x : EuclideanSpace ℝ (Fin m) ↦ u_m m x * x k) μ :=
    MemLp.integrable_mul (memLp_u_m_stdGaussian_two hm)
      ((IsGaussian.memLp_id (μ := μ) 2 (by norm_num)).continuousLinearMap_comp
        (EuclideanSpace.proj (𝕜 := ℝ) k))
  have hpoint : (fun w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
      u_m m w.1 *
        (rho ^ 2 * u_m m w.1 + c ^ 2 * u_m m w.2 +
          (2 * rho * c / (m : ℝ)) * ∑ k, w.1 k * w.2 k)) =
      (fun w ↦
        rho ^ 2 * ((u_m m w.1 * u_m m w.1) * 1) +
        c ^ 2 * (u_m m w.1 * u_m m w.2) +
        (2 * rho * c / (m : ℝ)) *
          ∑ k, (u_m m w.1 * w.1 k) * w.2 k) := by
    funext w
    have hsum : u_m m w.1 *
        ((2 * rho * c / (m : ℝ)) * ∑ k, w.1 k * w.2 k) =
        (2 * rho * c / (m : ℝ)) *
          ∑ k, (u_m m w.1 * w.1 k) * w.2 k := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    rw [mul_add, mul_add, hsum]
    ring
  rw [hpoint]
  have hfirstInt : (∫ w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m),
      rho ^ 2 * ((u_m m w.1 * u_m m w.1) * 1) ∂μ.prod μ) =
      rho ^ 2 * (2 / (m : ℝ)) := by
    rw [integral_const_mul]
    have hp := integral_prod_mul
      (μ := μ) (ν := μ)
      (fun x : EuclideanSpace ℝ (Fin m) ↦ u_m m x * u_m m x)
      (fun _x : EuclideanSpace ℝ (Fin m) ↦ (1 : ℝ))
    calc
      rho ^ 2 *
          (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
            (u_m m w.1 * u_m m w.1) * 1 ∂μ.prod μ) =
        rho ^ 2 * ((∫ x, u_m m x * u_m m x ∂μ) *
          ∫ _x : EuclideanSpace ℝ (Fin m), 1 ∂μ) := by rw [hp]
      _ = rho ^ 2 * (2 / (m : ℝ)) := by
        rw [show (fun x : EuclideanSpace ℝ (Fin m) ↦
            u_m m x * u_m m x) = fun x ↦ u_m m x ^ 2 by
          funext x; ring]
        rw [integral_u_m_sq_stdGaussian_eq hm, integral_const]
        simp
  have hsecondInt : (∫ w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m),
      c ^ 2 * (u_m m w.1 * u_m m w.2) ∂μ.prod μ) = 0 := by
    rw [integral_const_mul, integral_prod_mul,
      integral_u_m_stdGaussian_eq_zero,
      zero_mul, mul_zero]
  have hthirdTerm (k : Fin m) : Integrable
      (fun w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) ↦
        (u_m m w.1 * w.1 k) * w.2 k) (μ.prod μ) :=
    (hucoord k).mul_prod (hcoord k)
  have hthirdInt : (∫ w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m),
      (2 * rho * c / (m : ℝ)) *
        ∑ k, (u_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) = 0 := by
    rw [integral_const_mul,
      integral_finsetSum Finset.univ (fun k _ ↦ hthirdTerm k)]
    have hsumzero : (∑ k : Fin m,
        ∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
          (u_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      calc
        (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
            (u_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) =
            (∫ x, u_m m x * x k ∂μ) * (∫ y, y k ∂μ) :=
          integral_prod_mul
            (fun x : EuclideanSpace ℝ (Fin m) ↦ u_m m x * x k)
            (fun y : EuclideanSpace ℝ (Fin m) ↦ y k)
        _ = 0 := by rw [integral_coordinate_stdGaussian_eq_zero, mul_zero]
    rw [hsumzero]
    ring
  have hfirst : Integrable (fun w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
      rho ^ 2 * ((u_m m w.1 * u_m m w.1) * 1)) (μ.prod μ) :=
    (hu2.mul_prod (integrable_const (μ := μ) (1 : ℝ))).const_mul _
  have hsecond : Integrable (fun w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
      c ^ 2 * (u_m m w.1 * u_m m w.2)) (μ.prod μ) :=
    (hu.mul_prod hu).const_mul _
  have hthird : Integrable (fun w : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
      (2 * rho * c / (m : ℝ)) *
        ∑ k, (u_m m w.1 * w.1 k) * w.2 k) (μ.prod μ) :=
    (integrable_finsetSum Finset.univ fun k _ ↦ hthirdTerm k).const_mul _
  calc
    (∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        (rho ^ 2 * ((u_m m w.1 * u_m m w.1) * 1) +
          c ^ 2 * (u_m m w.1 * u_m m w.2)) +
          (2 * rho * c / (m : ℝ)) *
            ∑ k, (u_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) =
        (∫ w, rho ^ 2 * ((u_m m w.1 * u_m m w.1) * 1) +
          c ^ 2 * (u_m m w.1 * u_m m w.2) ∂μ.prod μ) +
        (∫ w, (2 * rho * c / (m : ℝ)) *
          ∑ k, (u_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) := by
      simpa only [Pi.add_apply] using
        integral_add (hfirst.add hsecond) hthird
    _ = ((∫ w, rho ^ 2 * ((u_m m w.1 * u_m m w.1) * 1) ∂μ.prod μ) +
        (∫ w, c ^ 2 * (u_m m w.1 * u_m m w.2) ∂μ.prod μ)) +
        (∫ w, (2 * rho * c / (m : ℝ)) *
          ∑ k, (u_m m w.1 * w.1 k) * w.2 k ∂μ.prod μ) := by
      rw [integral_add hfirst hsecond]
    _ = 2 * rho ^ 2 / (m : ℝ) := by
      rw [hfirstInt, hsecondInt, hthirdInt]
      ring

/-! ## Exact transfer from a pair of correlated columns -/

def pairRows {m p : ℕ} (i j : Fin p) (x : GaussianData m p) :
    GaussianData m 2 :=
  fun k ↦ CorrelationMatrix.pairProjectionCLM i j (x k)

lemma measurable_pairRows {m p : ℕ} (i j : Fin p) :
    Measurable (pairRows (m := m) i j) := by
  unfold pairRows
  fun_prop

theorem map_pairRows_correlatedGaussianDataMeasure {m p : ℕ}
    (R : CorrelationMatrix p) (i j : Fin p) :
    Measure.map (pairRows (m := m) i j)
        (correlatedGaussianDataMeasure m R) =
      Measure.pi (fun _ : Fin m ↦
        multivariateGaussian 0
          (CorrelationMatrix.pairCorrelationMatrix (R.val i j))) := by
  unfold correlatedGaussianDataMeasure pairRows
  rw [Measure.pi_map_pi (fun _ ↦
    (CorrelationMatrix.pairProjectionCLM i j).continuous.measurable.aemeasurable)]
  congr 1
  funext k
  exact CorrelationMatrix.map_pairProjection_gaussianMeasure R i j

def canonicalPairRows {m : ℕ} (rho : ℝ) (x : GaussianData m 2) :
    GaussianData m 2 :=
  fun k ↦ canonicalCorrelationCLM rho (x k)

lemma measurable_canonicalPairRows {m : ℕ} (rho : ℝ) :
    Measurable (canonicalPairRows (m := m) rho) := by
  unfold canonicalPairRows
  fun_prop

theorem map_canonicalPairRows_standardGaussianDataMeasure {m : ℕ}
    {rho : ℝ} (hrho : |rho| ≤ 1) :
    Measure.map (canonicalPairRows (m := m) rho)
        (standardGaussianDataMeasure m 2) =
      Measure.pi (fun _ : Fin m ↦
        multivariateGaussian 0
          (CorrelationMatrix.pairCorrelationMatrix rho)) := by
  unfold standardGaussianDataMeasure canonicalPairRows
  rw [Measure.pi_map_pi (fun _ ↦
    (canonicalCorrelationCLM rho).continuous.measurable.aemeasurable)]
  congr 1
  funext k
  exact map_canonicalCorrelation_stdGaussian hrho

@[simp] lemma dataColumn_pairRows_zero {m p : ℕ} (i j : Fin p)
    (x : GaussianData m p) :
    dataColumn (pairRows i j x) 0 = dataColumn x i := by
  ext k
  simp [pairRows, dataColumn]

@[simp] lemma dataColumn_pairRows_one {m p : ℕ} (i j : Fin p)
    (x : GaussianData m p) :
    dataColumn (pairRows i j x) 1 = dataColumn x j := by
  ext k
  simp [pairRows, dataColumn]

@[simp] lemma dataColumn_canonicalPairRows_zero {m : ℕ} (rho : ℝ)
    (x : GaussianData m 2) :
    dataColumn (canonicalPairRows rho x) 0 = dataColumn x 0 := by
  ext k
  simp [canonicalPairRows, dataColumn]

@[simp] lemma dataColumn_canonicalPairRows_one {m : ℕ} (rho : ℝ)
    (x : GaussianData m 2) :
    dataColumn (canonicalPairRows rho x) 1 =
      rho • dataColumn x 0 + Real.sqrt (1 - rho ^ 2) • dataColumn x 1 := by
  ext k
  simp [canonicalPairRows, dataColumn]

theorem map_actual_pairRows_eq_canonical {m p : ℕ}
    (R : CorrelationMatrix p) (i j : Fin p) :
    Measure.map (pairRows (m := m) i j ∘ correlateRows R)
        (standardGaussianDataMeasure m p) =
      Measure.map (canonicalPairRows (m := m) (R.val i j))
        (standardGaussianDataMeasure m 2) := by
  calc
    Measure.map (pairRows (m := m) i j ∘ correlateRows R)
        (standardGaussianDataMeasure m p) =
      Measure.map (pairRows (m := m) i j)
        (Measure.map (correlateRows R)
          (standardGaussianDataMeasure m p)) := by
        exact (Measure.map_map (measurable_pairRows i j)
          (measurable_correlateRows R)).symm
    _ = Measure.map (pairRows (m := m) i j)
        (correlatedGaussianDataMeasure m R) := by
      rw [map_correlateRows_standardGaussianDataMeasure]
    _ = Measure.pi (fun _ : Fin m ↦
        multivariateGaussian 0
          (CorrelationMatrix.pairCorrelationMatrix (R.val i j))) :=
      map_pairRows_correlatedGaussianDataMeasure R i j
    _ = Measure.map (canonicalPairRows (m := m) (R.val i j))
        (standardGaussianDataMeasure m 2) :=
      (map_canonicalPairRows_standardGaussianDataMeasure
        (R.abs_apply_le_one i j)).symm

theorem integral_e_m_G_mul_u_m_G_eq_zero_cross {m p : ℕ}
    (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    ∫ z, e_m m (G R z i) * u_m m (G R z j)
        ∂standardGaussianDataMeasure m p = 0 := by
  let F : GaussianData m 2 → ℝ := fun x ↦
    e_m m (dataColumn x 0) * u_m m (dataColumn x 1)
  have hF : Measurable F := by
    unfold F
    exact ((measurable_e_m m).comp
      ((measurable_pi_apply 0).comp measurable_dataColumns)).mul
      ((measurable_u_m m).comp
        ((measurable_pi_apply 1).comp measurable_dataColumns))
  have hmap := map_actual_pairRows_eq_canonical (m := m) R i j
  have hleft :
      (∫ z, F (pairRows i j (correlateRows R z))
          ∂standardGaussianDataMeasure m p) =
        ∫ x, F x ∂Measure.map (pairRows i j ∘ correlateRows R)
          (standardGaussianDataMeasure m p) := by
    exact (integral_map
      ((measurable_pairRows i j).comp (measurable_correlateRows R)).aemeasurable
      hF.aestronglyMeasurable).symm
  have hright :
      (∫ z, F (canonicalPairRows (R.val i j) z)
          ∂standardGaussianDataMeasure m 2) =
        ∫ x, F x ∂Measure.map (canonicalPairRows (R.val i j))
          (standardGaussianDataMeasure m 2) := by
    exact (integral_map
      (measurable_canonicalPairRows (R.val i j)).aemeasurable
      hF.aestronglyMeasurable).symm
  have htransfer :
      (∫ z, F (pairRows i j (correlateRows R z))
          ∂standardGaussianDataMeasure m p) =
        ∫ z, F (canonicalPairRows (R.val i j) z)
          ∂standardGaussianDataMeasure m 2 := by
    rw [hleft, hright, hmap]
  change (∫ z, F (pairRows i j (correlateRows R z))
      ∂standardGaussianDataMeasure m p) = 0
  rw [htransfer]
  simp only [F, dataColumn_canonicalPairRows_zero,
    dataColumn_canonicalPairRows_one]
  have hcols := map_dataColumns_standardGaussianDataMeasure m 2
  let H : (Fin 2 → EuclideanSpace ℝ (Fin m)) → ℝ := fun x ↦
    e_m m (x 0) * u_m m
      ((R.val i j) • x 0 + Real.sqrt (1 - (R.val i j) ^ 2) • x 1)
  have hH : Measurable H := by
    unfold H
    exact ((measurable_e_m m).comp (measurable_pi_apply 0)).mul
      ((measurable_u_m m).comp (by fun_prop))
  calc
    (∫ z : GaussianData m 2,
        e_m m (dataColumn z 0) *
          u_m m ((R.val i j) • dataColumn z 0 +
            Real.sqrt (1 - (R.val i j) ^ 2) • dataColumn z 1)
        ∂standardGaussianDataMeasure m 2) =
      ∫ x, H x ∂Measure.map dataColumns
        (standardGaussianDataMeasure m 2) := by
          exact (integral_map measurable_dataColumns.aemeasurable
            hH.aestronglyMeasurable).symm
    _ = ∫ x, H x ∂Measure.pi (fun _ : Fin 2 ↦
        stdGaussian (EuclideanSpace ℝ (Fin m))) := by rw [hcols]
    _ = ∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        e_m m w.1 * u_m m
          ((R.val i j) • w.1 +
            Real.sqrt (1 - (R.val i j) ^ 2) • w.2)
        ∂((stdGaussian (EuclideanSpace ℝ (Fin m))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin m)))) := by
      exact (measurePreserving_finTwoArrow
        (stdGaussian (EuclideanSpace ℝ (Fin m)))).integral_comp'
          (fun w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) ↦
            e_m m w.1 * u_m m
              ((R.val i j) • w.1 +
                Real.sqrt (1 - (R.val i j) ^ 2) • w.2))
    _ = 0 := integral_e_m_mul_u_m_mehler_eq_zero hm
      (R.abs_apply_le_one i j)

theorem integral_u_m_G_mul_u_m_G_eq_cross {m p : ℕ}
    (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    ∫ z, u_m m (G R z i) * u_m m (G R z j)
        ∂standardGaussianDataMeasure m p =
      2 * (R.val i j) ^ 2 / (m : ℝ) := by
  let F : GaussianData m 2 → ℝ := fun x ↦
    u_m m (dataColumn x 0) * u_m m (dataColumn x 1)
  have hF : Measurable F := by
    unfold F
    exact ((measurable_u_m m).comp
      ((measurable_pi_apply 0).comp measurable_dataColumns)).mul
      ((measurable_u_m m).comp
        ((measurable_pi_apply 1).comp measurable_dataColumns))
  have hmap := map_actual_pairRows_eq_canonical (m := m) R i j
  have hleft :
      (∫ z, F (pairRows i j (correlateRows R z))
          ∂standardGaussianDataMeasure m p) =
        ∫ x, F x ∂Measure.map (pairRows i j ∘ correlateRows R)
          (standardGaussianDataMeasure m p) :=
    (integral_map
      ((measurable_pairRows i j).comp (measurable_correlateRows R)).aemeasurable
      hF.aestronglyMeasurable).symm
  have hright :
      (∫ z, F (canonicalPairRows (R.val i j) z)
          ∂standardGaussianDataMeasure m 2) =
        ∫ x, F x ∂Measure.map (canonicalPairRows (R.val i j))
          (standardGaussianDataMeasure m 2) :=
    (integral_map
      (measurable_canonicalPairRows (R.val i j)).aemeasurable
      hF.aestronglyMeasurable).symm
  have htransfer :
      (∫ z, F (pairRows i j (correlateRows R z))
          ∂standardGaussianDataMeasure m p) =
        ∫ z, F (canonicalPairRows (R.val i j) z)
          ∂standardGaussianDataMeasure m 2 := by
    rw [hleft, hright, hmap]
  change (∫ z, F (pairRows i j (correlateRows R z))
      ∂standardGaussianDataMeasure m p) = _
  rw [htransfer]
  simp only [F, dataColumn_canonicalPairRows_zero,
    dataColumn_canonicalPairRows_one]
  have hcols := map_dataColumns_standardGaussianDataMeasure m 2
  let H : (Fin 2 → EuclideanSpace ℝ (Fin m)) → ℝ := fun x ↦
    u_m m (x 0) * u_m m
      ((R.val i j) • x 0 + Real.sqrt (1 - (R.val i j) ^ 2) • x 1)
  have hH : Measurable H := by
    unfold H
    exact ((measurable_u_m m).comp (measurable_pi_apply 0)).mul
      ((measurable_u_m m).comp (by fun_prop))
  calc
    (∫ z : GaussianData m 2,
        u_m m (dataColumn z 0) *
          u_m m ((R.val i j) • dataColumn z 0 +
            Real.sqrt (1 - (R.val i j) ^ 2) • dataColumn z 1)
        ∂standardGaussianDataMeasure m 2) =
      ∫ x, H x ∂Measure.map dataColumns
        (standardGaussianDataMeasure m 2) :=
          (integral_map measurable_dataColumns.aemeasurable
            hH.aestronglyMeasurable).symm
    _ = ∫ x, H x ∂Measure.pi (fun _ : Fin 2 ↦
        stdGaussian (EuclideanSpace ℝ (Fin m))) := by rw [hcols]
    _ = ∫ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        u_m m w.1 * u_m m
          ((R.val i j) • w.1 +
            Real.sqrt (1 - (R.val i j) ^ 2) • w.2)
        ∂((stdGaussian (EuclideanSpace ℝ (Fin m))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin m)))) := by
      exact (measurePreserving_finTwoArrow
        (stdGaussian (EuclideanSpace ℝ (Fin m)))).integral_comp'
          (fun w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) ↦
            u_m m w.1 * u_m m
              ((R.val i j) • w.1 +
                Real.sqrt (1 - (R.val i j) ^ 2) • w.2))
    _ = 2 * (R.val i j) ^ 2 / (m : ℝ) :=
      integral_u_m_mul_u_m_mehler_eq hm (R.abs_apply_le_one i j)

theorem covariance_e_m_G_u_m_G_eq_zero_cross {m p : ℕ}
    (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    cov[fun z : GaussianData m p ↦ e_m m (G R z i),
      fun z ↦ u_m m (G R z j); standardGaussianDataMeasure m p] = 0 := by
  rw [covariance_eq_sub (memLp_e_m_G_two hm R i)
    (memLp_u_m_G_two hm R j),
    integral_e_m_G_eq_zero_unconditional hm R i,
    integral_u_m_G_eq_zero R j, mul_zero, sub_zero]
  exact integral_e_m_G_mul_u_m_G_eq_zero_cross hm R i j

theorem covariance_u_m_G_u_m_G_eq_cross {m p : ℕ}
    (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    cov[fun z : GaussianData m p ↦ u_m m (G R z i),
      fun z ↦ u_m m (G R z j); standardGaussianDataMeasure m p] =
      2 * (R.val i j) ^ 2 / (m : ℝ) := by
  rw [covariance_eq_sub (memLp_u_m_G_two hm R i)
    (memLp_u_m_G_two hm R j),
    integral_u_m_G_eq_zero R i,
    integral_u_m_G_eq_zero R j, mul_zero, sub_zero]
  exact integral_u_m_G_mul_u_m_G_eq_cross hm R i j

theorem covariance_e_m_G_eq_log_Q_sub_linear {m p : ℕ}
    (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    cov[fun z : GaussianData m p ↦ e_m m (G R z i),
      fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] =
      cov[fun z ↦ Real.log (Q R z i), fun z ↦ Real.log (Q R z j);
        standardGaussianDataMeasure m p] -
        2 * (R.val i j) ^ 2 / (m : ℝ) := by
  let hi : GaussianData m p → ℝ := fun z ↦ h_m m (G R z i)
  let hj : GaussianData m p → ℝ := fun z ↦ h_m m (G R z j)
  let ui : GaussianData m p → ℝ := fun z ↦ u_m m (G R z i)
  let uj : GaussianData m p → ℝ := fun z ↦ u_m m (G R z j)
  have hhi := memLp_h_m_G_two hm R i
  have hhj := memLp_h_m_G_two hm R j
  have hui := memLp_u_m_G_two hm R i
  have huj := memLp_u_m_G_two hm R j
  change cov[hi - ui, hj - uj; standardGaussianDataMeasure m p] = _
  rw [covariance_sub_sub hhi hui hhj huj]
  have heiuj := covariance_e_m_G_u_m_G_eq_zero_cross hm R i j
  have hejui := covariance_e_m_G_u_m_G_eq_zero_cross hm R j i
  have hcuiuj := covariance_u_m_G_u_m_G_eq_cross hm R i j
  have hhiuj : cov[hi, uj; standardGaussianDataMeasure m p] =
      2 * (R.val i j) ^ 2 / (m : ℝ) := by
    have h := covariance_add_left
      (memLp_e_m_G_two hm R i) hui huj
    change cov[(fun z ↦ e_m m (G R z i)) + ui, uj;
      standardGaussianDataMeasure m p] = _ at h
    rw [show (fun z : GaussianData m p ↦ e_m m (G R z i)) + ui = hi by
      funext z; simp [hi, ui, e_m]] at h
    rw [heiuj, zero_add] at h
    exact h.trans hcuiuj
  have huihj : cov[ui, hj; standardGaussianDataMeasure m p] =
      2 * (R.val i j) ^ 2 / (m : ℝ) := by
    have h := covariance_add_right hui
      (memLp_e_m_G_two hm R j) huj
    change cov[ui, (fun z ↦ e_m m (G R z j)) + uj;
      standardGaussianDataMeasure m p] = _ at h
    rw [show (fun z : GaussianData m p ↦ e_m m (G R z j)) + uj = hj by
      funext z; simp [hj, uj, e_m]] at h
    have hzero : cov[ui, fun z ↦ e_m m (G R z j);
        standardGaussianDataMeasure m p] = 0 := by
      rw [covariance_comm]
      exact hejui
    rw [hzero, zero_add] at h
    exact h.trans hcuiuj
  rw [hhiuj, huihj, hcuiuj]
  change cov[hi, hj; standardGaussianDataMeasure m p] -
      2 * (R.val i j) ^ 2 / (m : ℝ) -
      2 * (R.val i j) ^ 2 / (m : ℝ) +
      2 * (R.val i j) ^ 2 / (m : ℝ) = _
  have hconst :
      cov[hi, hj; standardGaussianDataMeasure m p] =
        cov[fun z ↦ Real.log (Q R z i), fun z ↦ Real.log (Q R z j);
          standardGaussianDataMeasure m p] := by
    unfold hi hj h_m
    change cov[fun z ↦ Real.log (Q R z i) - chiSquareLogMean m,
      fun z ↦ Real.log (Q R z j) - chiSquareLogMean m;
      standardGaussianDataMeasure m p] = _
    rw [covariance_sub_const_left
      ((memLp_log_Q_two hm R i).integrable (by norm_num)),
      covariance_sub_const_right
        ((memLp_log_Q_two hm R j).integrable (by norm_num))]
  rw [hconst]
  ring

/-- The actual nonlinear radial remainder starts in fourth Gaussian chaos,
expressed here without an abstract completeness hypothesis: its pair
covariance is nonnegative and has the sharp fourth-power bound. -/
theorem residual_covariance_nonneg_and_le_fourth_actual {m p : ℕ}
    (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    0 ≤ cov[fun z : GaussianData m p ↦ e_m m (G R z i),
        fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] ∧
    cov[fun z : GaussianData m p ↦ e_m m (G R z i),
        fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] ≤
      4 * (R.val i j) ^ 4 / (m : ℝ) ^ 2 := by
  rw [covariance_e_m_G_eq_log_Q_sub_linear hm R i j]
  exact actual_logRadiusCovariance_remainder_bounds hm R i j

/-- Unconditional sharp `L²` bound for the actual nonlinear remainder.
This discharges the former `HasResidualFourthChaosRepresentation` hypothesis
by the explicit canonical-pair and Laplace-tail calculation above. -/
theorem variance_E_R_le_dimension_add_energy {m p : ℕ}
    (hm : 0 < m) (R : CorrelationMatrix p) :
    Var[E_R m R; standardGaussianDataMeasure m p] ≤
      (4 / (m : ℝ) ^ 2) * ((p : ℝ) + R.deviationEnergy) := by
  have hmem (i : Fin p) :
      MemLp (fun z : GaussianData m p ↦ e_m m (G R z i)) 2
        (standardGaussianDataMeasure m p) :=
    memLp_e_m_G_two hm R i
  rw [show E_R m R = fun z ↦ ∑ i, e_m m (G R z i) by rfl,
    variance_fun_sum hmem]
  calc
    ∑ i, ∑ j,
        cov[fun z : GaussianData m p ↦ e_m m (G R z i),
          fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] ≤
        ∑ i, ∑ j,
          (4 / (m : ℝ) ^ 2) * (R.val i j) ^ 4 := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      calc
        cov[fun z : GaussianData m p ↦ e_m m (G R z i),
          fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] ≤
            4 * (R.val i j) ^ 4 / (m : ℝ) ^ 2 :=
          (residual_covariance_nonneg_and_le_fourth_actual hm R i j).2
        _ = (4 / (m : ℝ) ^ 2) * (R.val i j) ^ 4 := by ring
    _ = (4 / (m : ℝ) ^ 2) *
        (∑ i, ∑ j, (R.val i j) ^ 4) := by
      simp_rw [Finset.mul_sum]
    _ ≤ (4 / (m : ℝ) ^ 2) *
        ((p : ℝ) + R.deviationEnergy) :=
      mul_le_mul_of_nonneg_left
        R.sum_fourth_apply_le_dimension_add_energy (by positivity)

/-- A direct Kolmogorov perturbation consequence of the unconditional
remainder bound.  No independence between `M_R` and `E_R` is assumed.  The
parameter `s` is the positive normalization scale and `eps` is the smoothing
radius on the normalized scale. -/
theorem kolmogorovDistance_centeredDecomposition_le {m p : ℕ}
    (hm : 0 < m) (R : CorrelationMatrix p) {s eps : ℝ}
    (hs : 0 < s) (heps : 0 < eps) :
    kolmogorovDistance
        ((standardGaussianDataMeasure m p).map
          (fun z ↦ (M_R m R z - E_R m R z) / s))
        (gaussianReal 0 1) ≤
      kolmogorovDistance
          ((standardGaussianDataMeasure m p).map
            (fun z ↦ M_R m R z / s))
          (gaussianReal 0 1) +
        (((4 / (m : ℝ) ^ 2) * ((p : ℝ) + R.deviationEnergy)) /
          s ^ 2) / eps ^ 2 + eps / Real.sqrt (2 * Real.pi) := by
  let P : Measure (GaussianData m p) := standardGaussianDataMeasure m p
  let X : GaussianData m p → ℝ := fun z ↦ M_R m R z / s
  let Y : GaussianData m p → ℝ := fun z ↦ -(E_R m R z / s)
  have hE : MemLp (E_R m R) 2 P := by
    change MemLp (fun z : GaussianData m p ↦
      ∑ i, e_m m (G R z i)) 2 (standardGaussianDataMeasure m p)
    exact memLp_finsetSum Finset.univ fun i _ ↦ memLp_e_m_G_two hm R i
  have hY : MemLp Y 2 P := by
    apply (hE.mul_const s⁻¹).neg.ae_eq
    filter_upwards [] with z
    simp [Y, div_eq_mul_inv]
  have hEcenter :
      ∫ z, E_R m R z ∂standardGaussianDataMeasure m p = 0 :=
    integral_E_R_eq_zero hm R (integrable_log_Q hm R)
  have hYcenter : P[Y] = 0 := by
    change (∫ z, -(E_R m R z / s)
      ∂standardGaussianDataMeasure m p) = 0
    rw [integral_neg, integral_div, hEcenter, zero_div, neg_zero]
  have hvar : Var[Y; P] ≤
      ((4 / (m : ℝ) ^ 2) * ((p : ℝ) + R.deviationEnergy)) /
        s ^ 2 := by
    have hs0 : s ≠ 0 := ne_of_gt hs
    calc
      Var[Y; P] =
          Var[E_R m R; standardGaussianDataMeasure m p] * s⁻¹ ^ 2 := by
        simp only [Y, P, div_eq_mul_inv, variance_fun_neg,
          variance_mul_const]
      _ ≤ ((4 / (m : ℝ) ^ 2) *
          ((p : ℝ) + R.deviationEnergy)) * s⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (variance_E_R_le_dimension_add_energy hm R) (sq_nonneg s⁻¹)
      _ = s⁻¹ ^ 2 *
          ((4 / (m : ℝ) ^ 2) *
            ((p : ℝ) + R.deviationEnergy)) := by
        ring
      _ = ((4 / (m : ℝ) ^ 2) *
          ((p : ℝ) + R.deviationEnergy)) / s ^ 2 := by
        field_simp
  have hmain := kolmogorovDistance_standardGaussian_add_le_secondMomentBound
    P (X := X) (Y := Y)
    ((measurable_M_R m R).div_const s)
    ((measurable_E_R m R).div_const s).neg
    hY hYcenter hvar heps
  have hfun : (fun z ↦ X z + Y z) =
      (fun z ↦ (M_R m R z - E_R m R z) / s) := by
    funext z
    dsimp [X, Y]
    ring
  rw [hfun] at hmain
  simpa [P, X] using hmain

/-- The preceding perturbation theorem at the paper's proxy scale and at the
cube-root choice of smoothing radius.  This is the unconditional nonlinear
remainder term in the general-`R` Berry--Esseen bound. -/
theorem kolmogorovDistance_centeredDecomposition_proxyScale_le {m p : ℕ}
    (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        ((standardGaussianDataMeasure m p).map
          (fun z ↦ (M_R m R z - E_R m R z) /
            generalRProxyScale m R))
        (gaussianReal 0 1) ≤
      kolmogorovDistance
          ((standardGaussianDataMeasure m p).map
            (fun z ↦ M_R m R z / generalRProxyScale m R))
          (gaussianReal 0 1) +
        generalRNonlinearCubeRootRate m R +
          generalRNonlinearCubeRootRate m R /
            Real.sqrt (2 * Real.pi) := by
  have hm : 0 < m := by
    unfold Admissible at h
    omega
  have hs := generalRProxyScale_pos h R
  have hdelta := generalRNonlinearCubeRootRate_pos h R
  have hraw := kolmogorovDistance_centeredDecomposition_le hm R hs hdelta
  have hQ :
      ((4 / (m : ℝ) ^ 2) * ((p : ℝ) + R.deviationEnergy)) /
          generalRProxyScale m R ^ 2 =
        generalRNonlinearRateQ m R := by
    rw [← generalRProxyVarianceSq_eq_scale_sq h R]
    unfold generalRNonlinearRateQ generalRemainderRateQ
    ring
  have hdeltaReduce :
      generalRNonlinearRateQ m R /
          generalRNonlinearCubeRootRate m R ^ 2 =
        generalRNonlinearCubeRootRate m R := by
    rw [← generalRNonlinearCubeRootRate_cube h R]
    field_simp
  rw [hQ, hdeltaReduce] at hraw
  exact hraw

end GeneralRDecomposition

end

end LogdetLean
