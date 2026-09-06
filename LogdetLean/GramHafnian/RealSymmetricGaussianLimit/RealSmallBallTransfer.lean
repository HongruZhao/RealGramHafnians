import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# Linear small-ball bounds pass to real weak limits

This module isolates the Portmanteau step for the fixed-degree real
transpose-Gram limit.  A linear interval bound with convergent scale and
coefficient passes to the limiting real law.  No boundary-density assumption
is used: the proof enlarges a closed interval to open intervals and then lets
the enlargement decrease to zero.
-/

open Filter MeasureTheory Metric Set

namespace LogdetLean.GramHafnian.RealSymmetricGaussianLimit

noncomputable section

/-- Open-ball form of the real linear small-ball transfer. -/
theorem real_openBall_measure_le_of_weakLimit
    (muSeq : ℕ → ProbabilityMeasure ℝ) (mu : ProbabilityMeasure ℝ)
    (rawCoeffSeq : ℕ → ℝ) (rawCoeff : ℝ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (hcoeff : Tendsto rawCoeffSeq atTop (nhds rawCoeff))
    (z : ℝ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ r : ℝ, 0 < r →
      (muSeq k : Measure ℝ) (Metric.closedBall z r) ≤
        ENNReal.ofReal (rawCoeffSeq k * r))
    (r : ℝ) (hr : 0 < r) :
    (mu : Measure ℝ) (Metric.ball z r) ≤
      ENNReal.ofReal (rawCoeff * r) := by
  have hopen :
      (mu : Measure ℝ) (Metric.ball z r) ≤
        atTop.liminf (fun k ↦
          (muSeq k : Measure ℝ) (Metric.ball z r)) :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      hmu Metric.isOpen_ball
  have hpointwise : ∀ᶠ k : ℕ in atTop,
      (muSeq k : Measure ℝ) (Metric.ball z r) ≤
        ENNReal.ofReal (rawCoeffSeq k * r) := by
    filter_upwards [hfinite] with k hk
    exact (measure_mono Metric.ball_subset_closedBall).trans (hk r hr)
  have hliminf :
      atTop.liminf (fun k ↦
          (muSeq k : Measure ℝ) (Metric.ball z r)) ≤
        atTop.liminf (fun k ↦
          ENNReal.ofReal (rawCoeffSeq k * r)) :=
    Filter.liminf_le_liminf hpointwise
  have hrhs : Tendsto
      (fun k : ℕ ↦ ENNReal.ofReal (rawCoeffSeq k * r))
      atTop (nhds (ENNReal.ofReal (rawCoeff * r))) :=
    ENNReal.tendsto_ofReal (hcoeff.mul_const r)
  exact hopen.trans (hliminf.trans_eq hrhs.liminf_eq)

/-- Closed-ball form.  The target closed interval is first embedded in every
slightly larger open interval. -/
theorem real_closedBall_measure_le_of_weakLimit
    (muSeq : ℕ → ProbabilityMeasure ℝ) (mu : ProbabilityMeasure ℝ)
    (rawCoeffSeq : ℕ → ℝ) (rawCoeff : ℝ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (hcoeff : Tendsto rawCoeffSeq atTop (nhds rawCoeff))
    (z : ℝ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ r : ℝ, 0 < r →
      (muSeq k : Measure ℝ) (Metric.closedBall z r) ≤
        ENNReal.ofReal (rawCoeffSeq k * r))
    (r : ℝ) (hr : 0 ≤ r) :
    (mu : Measure ℝ) (Metric.closedBall z r) ≤
      ENNReal.ofReal (rawCoeff * r) := by
  let rSeq : ℕ → ℝ := fun m ↦ r + 1 / ((m : ℝ) + 1)
  have hrSeq_gt (m : ℕ) : r < rSeq m := by
    dsimp [rSeq]
    have hm : 0 < (m : ℝ) + 1 := by positivity
    linarith [one_div_pos.mpr hm]
  have hrSeq_pos (m : ℕ) : 0 < rSeq m :=
    lt_of_le_of_lt hr (hrSeq_gt m)
  have h_each (m : ℕ) :
      (mu : Measure ℝ) (Metric.closedBall z r) ≤
        ENNReal.ofReal (rawCoeff * rSeq m) := by
    exact (measure_mono (Metric.closedBall_subset_ball (hrSeq_gt m))).trans
      (real_openBall_measure_le_of_weakLimit muSeq mu rawCoeffSeq rawCoeff
        hmu hcoeff z hfinite (rSeq m) (hrSeq_pos m))
  have hrSeq_tendsto : Tendsto rSeq atTop (nhds r) := by
    simpa [rSeq, Nat.cast_add, Nat.cast_one] using
      tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun m : ℕ ↦ (1 : ℝ) / (m + 1)) atTop (nhds 0))
  have hrhs : Tendsto
      (fun m : ℕ ↦ ENNReal.ofReal (rawCoeff * rSeq m))
      atTop (nhds (ENNReal.ofReal (rawCoeff * r))) :=
    ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hrSeq_tendsto)
  exact ge_of_tendsto' hrhs h_each

/-- Normalized form used by the real Gaussian transpose-Gram limit.  Both
the finite root-mean-square scale and its dimensionless coefficient may
vary. -/
theorem real_normalized_closedBall_measure_le_of_weakLimit
    (muSeq : ℕ → ProbabilityMeasure ℝ) (mu : ProbabilityMeasure ℝ)
    (scaleSeq : ℕ → ℝ) (scale : ℝ)
    (coeffSeq : ℕ → ℝ) (coeff : ℝ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (hscale : Tendsto scaleSeq atTop (nhds scale))
    (hscale_pos : 0 < scale)
    (hscaleSeq_pos : ∀ᶠ k : ℕ in atTop, 0 < scaleSeq k)
    (hcoeff : Tendsto coeffSeq atTop (nhds coeff))
    (z : ℝ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ eps : ℝ, 0 < eps →
      (muSeq k : Measure ℝ)
          (Metric.closedBall z (eps * scaleSeq k)) ≤
        ENNReal.ofReal (coeffSeq k * eps))
    (eps : ℝ) (heps : 0 ≤ eps) :
    (mu : Measure ℝ) (Metric.closedBall z (eps * scale)) ≤
      ENNReal.ofReal (coeff * eps) := by
  let rawCoeffSeq : ℕ → ℝ := fun k ↦ coeffSeq k / scaleSeq k
  let rawCoeff : ℝ := coeff / scale
  have hrawCoeff : Tendsto rawCoeffSeq atTop (nhds rawCoeff) := by
    dsimp [rawCoeffSeq, rawCoeff]
    exact hcoeff.div hscale hscale_pos.ne'
  have hrawFinite : ∀ᶠ k : ℕ in atTop, ∀ r : ℝ, 0 < r →
      (muSeq k : Measure ℝ) (Metric.closedBall z r) ≤
        ENNReal.ofReal (rawCoeffSeq k * r) := by
    filter_upwards [hscaleSeq_pos, hfinite] with k hskpos hk
    intro r hr
    have hsk : scaleSeq k ≠ 0 := hskpos.ne'
    have h := hk (r / scaleSeq k) (div_pos hr hskpos)
    convert h using 1
    · field_simp
    · congr 1
      dsimp [rawCoeffSeq]
      field_simp
  have hraw := real_closedBall_measure_le_of_weakLimit
    muSeq mu rawCoeffSeq rawCoeff hmu hrawCoeff z hrawFinite
    (eps * scale) (mul_nonneg heps hscale_pos.le)
  convert hraw using 1
  congr 1
  dsimp [rawCoeff]
  field_simp

/-- Probability measures are automatically capped by one, yielding the
literal manuscript form of the transferred bound. -/
theorem real_normalized_closedBall_measure_le_min_of_weakLimit
    (muSeq : ℕ → ProbabilityMeasure ℝ) (mu : ProbabilityMeasure ℝ)
    (scaleSeq : ℕ → ℝ) (scale : ℝ)
    (coeffSeq : ℕ → ℝ) (coeff : ℝ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (hscale : Tendsto scaleSeq atTop (nhds scale))
    (hscale_pos : 0 < scale)
    (hscaleSeq_pos : ∀ᶠ k : ℕ in atTop, 0 < scaleSeq k)
    (hcoeff : Tendsto coeffSeq atTop (nhds coeff))
    (z : ℝ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ eps : ℝ, 0 < eps →
      (muSeq k : Measure ℝ)
          (Metric.closedBall z (eps * scaleSeq k)) ≤
        ENNReal.ofReal (coeffSeq k * eps))
    (eps : ℝ) (heps : 0 ≤ eps) :
    (mu : Measure ℝ) (Metric.closedBall z (eps * scale)) ≤
      min 1 (ENNReal.ofReal (coeff * eps)) := by
  refine le_min ?_ ?_
  · calc
      (mu : Measure ℝ) (Metric.closedBall z (eps * scale)) ≤
          (mu : Measure ℝ) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · exact real_normalized_closedBall_measure_le_of_weakLimit
      muSeq mu scaleSeq scale coeffSeq coeff hmu hscale hscale_pos
      hscaleSeq_pos hcoeff z hfinite eps heps

end

end LogdetLean.GramHafnian.RealSymmetricGaussianLimit
