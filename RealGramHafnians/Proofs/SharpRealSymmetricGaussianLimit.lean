import RealGramHafnians.Proofs.SharpRealSymmetricGaussianCoefficientLimit
import LogdetLean.GramHafnian.RealSymmetricGaussianLimit.RealGramHafnianLimit
import LogdetLean.GramHafnian.RealSymmetricGaussianLimit.RealSmallBallTransfer
/-!
# The real symmetric Gaussian theorem obtained from the finite Gram limit

This module follows the manuscript's limiting proof literally.  It combines
the concrete fixed-dimensional Gram central limit theorem, exact hafnian
homogeneity, the RMS and coefficient limits, and a real Portmanteau transfer.
The final small-ball theorem below does not invoke the separate direct
independent-edge proof.
-/

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped BigOperators Real ENNReal Nat Topology

namespace LogdetLean.GramHafnian

noncomputable section

open SymmetricGaussianHafnian
open RealSymmetricGaussianLimit

set_option maxHeartbeats 2000000

/-- RMS scale after the central-limit normalization of the finite real Gram
hafnian. -/
def normalizedRealGramHafnianRMS (n k : ℕ) : ℝ :=
  (Real.sqrt k)⁻¹ ^ n * realGramHafnianRMS n k

theorem normalizedRealGramHafnianRMS_eq_div (n k : ℕ) :
    normalizedRealGramHafnianRMS n k =
      realGramHafnianRMS n k / (Real.sqrt k) ^ n := by
  unfold normalizedRealGramHafnianRMS
  rw [inv_pow, div_eq_mul_inv]
  ring

/-- The normalized finite RMS converges to the exact RMS of the real
symmetric Gaussian hafnian. -/
theorem tendsto_normalizedRealGramHafnianRMS_fixedDegree (n : ℕ) :
    Tendsto (normalizedRealGramHafnianRMS n) atTop
      (nhds (sharpRealSymmetricHafnianRMS n)) := by
  apply (tendsto_normalized_realGramHafnianRMS_fixedDegree n).congr'
  filter_upwards with k
  exact (normalizedRealGramHafnianRMS_eq_div n k).symm

theorem eventually_normalizedRealGramHafnianRMS_pos (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, 0 < normalizedRealGramHafnianRMS n k := by
  filter_upwards [eventually_ge_atTop 1] with k hk
  unfold normalizedRealGramHafnianRMS
  exact mul_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.2 (by positivity))) _)
    (realGramHafnianRMS_pos n k (by omega))

/-- Literal second moment of the independent-edge limiting hafnian.  Together
with the square-root definition of `sharpRealSymmetricHafnianRMS`, this
certifies that the paper's limiting scale is the actual RMS. -/
theorem sharpRealSymmetricHafnian_exactSecondMoment (n : ℕ) :
    (∫⁻ x : Edge (Fin (2 * n)) → ℝ,
        ENNReal.ofReal ((realEdgeHafnian x) ^ 2)
        ∂realEdgeGaussian (Fin (2 * n))) =
      (((2 * n - 1)‼ : ℕ) : ENNReal) := by
  simpa [realEdgeHafnianSecondMoment,
    oddPairingNat_eq_doubleFactorial] using
    realEdgeHafnianSecondMoment_even n

/-- Exact finite small-ball estimate after scaling the observable and RMS by
the central-limit factor. -/
theorem normalizedRealGramHafnianLaw_shiftedSmallBall_le
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) (z eps : ℝ) (heps : 0 ≤ eps) :
    (normalizedRealGramHafnianLaw n k : Measure ℝ)
        (Metric.closedBall z (eps * normalizedRealGramHafnianRMS n k)) ≤
      ENNReal.ofReal (sharpRealSmallBallCoefficientB n k * eps) := by
  let c : ℝ := (Real.sqrt k)⁻¹ ^ n
  have hsqrt : 0 < Real.sqrt (k : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hc : 0 < c := pow_pos (inv_pos.mpr hsqrt) n
  have hset :
      (normalizedRealGramHafnianObservable n k) ⁻¹'
          Metric.closedBall z (eps * normalizedRealGramHafnianRMS n k) =
        {X | |realGramHafnianObservable n k X - z / c| ≤
          eps * realGramHafnianRMS n k} := by
    ext X
    simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq,
      Set.mem_ofPred_eq]
    change |c * realGramHafnianObservable n k X - z| ≤
        eps * (c * realGramHafnianRMS n k) ↔ _
    have hid : c * realGramHafnianObservable n k X - z =
        c * (realGramHafnianObservable n k X - z / c) := by
      field_simp [hc.ne']
    rw [hid, abs_mul, abs_of_pos hc]
    rw [show eps * (c * realGramHafnianRMS n k) =
      c * (eps * realGramHafnianRMS n k) by ring]
    constructor <;> intro h
    · nlinarith
    · exact mul_le_mul_of_nonneg_left h hc.le
  have hfinite :=
    standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
      hn hk hdim (z / c) eps heps
  change Measure.map (normalizedRealGramHafnianSample n k)
      (realStrictUpperGramStreamMeasure (2 * n))
        (Metric.closedBall z (eps * normalizedRealGramHafnianRMS n k)) ≤ _
  rw [map_normalizedRealGramHafnianSample_eq_columnMap]
  rw [Measure.map_apply
    (measurable_normalizedRealGramHafnianObservable n k)
    measurableSet_closedBall]
  rw [hset]
  calc
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z / c| ≤
          eps * realGramHafnianRMS n k} ≤
        sharpRealNormalizedCoefficient n k * ENNReal.ofReal eps := hfinite
    _ = ENNReal.ofReal (sharpRealSmallBallCoefficientB n k * eps) := by
      rw [sharpRealNormalizedCoefficient_eq_ofReal_coefficientB hn hk hdim]
      calc
        ENNReal.ofReal (sharpRealSmallBallCoefficientB n k) *
            ENNReal.ofReal eps =
            ENNReal.ofReal eps *
              ENNReal.ofReal (sharpRealSmallBallCoefficientB n k) := by
                rw [mul_comm]
        _ = ENNReal.ofReal
            (eps * sharpRealSmallBallCoefficientB n k) := by
              exact (ENNReal.ofReal_mul heps).symm
        _ = ENNReal.ofReal
            (sharpRealSmallBallCoefficientB n k * eps) := by
              rw [mul_comm]

/-- The shifted real symmetric Gaussian small-ball bound obtained by taking
the fixed-degree limit of the finite Gram theorem. -/
theorem sharpRealSymmetricGaussian_shiftedSmallBall_of_fixedDegreeLimit
    (n : ℕ) (hn : 1 ≤ n) (z eps : ℝ) (heps : 0 ≤ eps) :
    (realEdgeGaussian (Fin (2 * n)))
        {x | |realEdgeHafnian x - z| ≤
          eps * sharpRealSymmetricHafnianRMS n} ≤
      min 1 (ENNReal.ofReal
        (sharpRealSymmetricSmallBallCoefficient n * eps)) := by
  have htransfer := real_normalized_closedBall_measure_le_min_of_weakLimit
    (normalizedRealGramHafnianLaw n)
    (realSymmetricGaussianHafnianLaw n)
    (normalizedRealGramHafnianRMS n)
    (sharpRealSymmetricHafnianRMS n)
    (sharpRealSmallBallCoefficientB n)
    (sharpRealSymmetricSmallBallCoefficient n)
    (tendsto_normalizedRealGramHafnianLaw_realEdgeHafnianLaw n)
    (tendsto_normalizedRealGramHafnianRMS_fixedDegree n)
    (by
      unfold sharpRealSymmetricHafnianRMS SymmetricGaussianHafnian.sigma
      exact Real.sqrt_pos.2 (by
        exact_mod_cast oddPairingNat_pos n))
    (eventually_normalizedRealGramHafnianRMS_pos n)
    (tendsto_sharpRealSmallBallCoefficientB_fixedDegree hn)
    z
    (by
      filter_upwards [eventually_ge_atTop (max 2 (2 * n - 1))] with k hk
      intro delta hdelta
      exact normalizedRealGramHafnianLaw_shiftedSmallBall_le hn
        (by omega) (by omega) z delta hdelta.le)
    eps heps
  change (realSymmetricGaussianHafnianLaw n : Measure ℝ)
      (Metric.closedBall z (eps * sharpRealSymmetricHafnianRMS n)) ≤ _
      at htransfer
  have hmap :
      (realSymmetricGaussianHafnianLaw n : Measure ℝ)
          (Metric.closedBall z
            (eps * sharpRealSymmetricHafnianRMS n)) =
        (realEdgeGaussian (Fin (2 * n)))
          {x | |realEdgeHafnian x - z| ≤
            eps * sharpRealSymmetricHafnianRMS n} := by
    unfold realSymmetricGaussianHafnianLaw
    change (Measure.map realEdgeHafnian
        (realEdgeGaussian (Fin (2 * n))))
          (Metric.closedBall z
            (eps * sharpRealSymmetricHafnianRMS n)) = _
    rw [Measure.map_apply measurable_realEdgeHafnian measurableSet_closedBall]
    rfl
  rw [hmap] at htransfer
  exact htransfer

/-- Paper-facing certificate for the complete fixed-degree limiting proof. -/
structure SharpRealSymmetricGaussianLimitCertificate
    (n : ℕ) (hn : 1 ≤ n) : Prop where
  exactLimitingSecondMoment :
    (∫⁻ x : Edge (Fin (2 * n)) → ℝ,
        ENNReal.ofReal ((realEdgeHafnian x) ^ 2)
        ∂realEdgeGaussian (Fin (2 * n))) =
      (((2 * n - 1)‼ : ℕ) : ENNReal)
  normalizedHafnianWeakLimit :
    Tendsto (normalizedRealGramHafnianLaw n) atTop
      (nhds (realSymmetricGaussianHafnianLaw n))
  normalizedRMSLimit :
    Tendsto
      (fun k : ℕ ↦
        realGramHafnianRMS n k / (Real.sqrt (k : ℝ)) ^ n)
      atTop (nhds (sharpRealSymmetricHafnianRMS n))
  coefficientLimit :
    Tendsto (fun k : ℕ ↦ sharpRealSmallBallCoefficientB n k)
      atTop (nhds (sharpRealSymmetricSmallBallCoefficient n))
  shiftedSmallBallFromWeakLimit : ∀ (z eps : ℝ), 0 ≤ eps →
    (realEdgeGaussian (Fin (2 * n)))
        {x | |realEdgeHafnian x - z| ≤
          eps * sharpRealSymmetricHafnianRMS n} ≤
      min 1 (ENNReal.ofReal
        (sharpRealSymmetricSmallBallCoefficient n * eps))

/-- Complete unconditional certificate for the manuscript's `k → ∞`
proof of the real symmetric Gaussian theorem. -/
theorem sharpRealSymmetricGaussianLimitCertificate
    {n : ℕ} (hn : 1 ≤ n) :
    SharpRealSymmetricGaussianLimitCertificate n hn where
  exactLimitingSecondMoment :=
    sharpRealSymmetricHafnian_exactSecondMoment n
  normalizedHafnianWeakLimit :=
    tendsto_normalizedRealGramHafnianLaw_realEdgeHafnianLaw n
  normalizedRMSLimit :=
    tendsto_normalized_realGramHafnianRMS_fixedDegree n
  coefficientLimit :=
    tendsto_sharpRealSmallBallCoefficientB_fixedDegree hn
  shiftedSmallBallFromWeakLimit := fun z eps heps ↦
    sharpRealSymmetricGaussian_shiftedSmallBall_of_fixedDegreeLimit
      n hn z eps heps

end

end LogdetLean.GramHafnian
