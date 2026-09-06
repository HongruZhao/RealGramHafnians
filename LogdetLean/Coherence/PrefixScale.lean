import LogdetLean.Coherence.AllGapBetaTailIntensity
import LogdetLean.ScaleSeparation
/-!
# The coherence threshold is negligible at the log-determinant CLT scale

The rare matching changes a fixed prefix determinant by order
`classicalCoherenceThreshold / m`.  The global null standard deviation is at
least `sqrt (p * (p - 1)) / m`.  This file records the resulting all-gap
scale separation, uniformly over every admissible sequence `2 ≤ p ≤ m`.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real
open scoped Topology

/-- The elementary lower bound on the null standard deviation in the form
needed for a fixed-prefix perturbation. -/
theorem pred_div_dimension_le_sqrt_nullVSeries
    {m p : ℕ} (h : Admissible m p) :
    ((p : ℝ) - 1) / (m : ℝ) ≤ Real.sqrt (nullVSeries m p) := by
  have hm0N : 0 < m := lt_of_lt_of_le (by omega : 0 < 2) (h.1.trans h.2)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0N
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1
  have hlow := nullVSeries_lower_p_mul_pred_div_m_sq h
  apply Real.le_sqrt_of_sq_le
  calc
    (((p : ℝ) - 1) / (m : ℝ)) ^ 2 ≤
        (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
      have hpred : 0 ≤ (p : ℝ) - 1 := by linarith
      have hpredp : (p : ℝ) - 1 ≤ (p : ℝ) := by linarith
      rw [div_pow]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    _ ≤ nullVSeries m p := hlow

/-- Finite scale comparison: a nonnegative prefix perturbation of order
`a/m` is bounded, after global standardization, by `a/(p-1)`. -/
theorem threshold_div_dimension_div_sqrt_nullVSeries_le
    {m p : ℕ} (h : Admissible m p) {a : ℝ} (ha : 0 ≤ a) :
    (a / (m : ℝ)) / Real.sqrt (nullVSeries m p) ≤
      a / ((p : ℝ) - 1) := by
  have hm0N : 0 < m := lt_of_lt_of_le (by omega : 0 < 2) (h.1.trans h.2)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0N
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) h.1)
  have hpredpos : 0 < ((p : ℝ) - 1) / (m : ℝ) := div_pos (sub_pos.mpr hp1) hm0
  have hsqrtpos : 0 < Real.sqrt (nullVSeries m p) :=
    Real.sqrt_pos.2 (nullVSeries_pos h)
  have hscale := pred_div_dimension_le_sqrt_nullVSeries h
  calc
    (a / (m : ℝ)) / Real.sqrt (nullVSeries m p) ≤
        (a / (m : ℝ)) / (((p : ℝ) - 1) / (m : ℝ)) :=
      div_le_div_of_nonneg_left (div_nonneg ha hm0.le) hpredpos hscale
    _ = a / ((p : ℝ) - 1) := by field_simp [hm0.ne', sub_ne_zero.mpr hp1.ne']

/-- The deterministic upper envelope `a_p/(p-1)` tends to zero for the
classical coherence threshold. -/
theorem tendsto_classicalCoherenceThreshold_div_pred_zero (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      classicalCoherenceThreshold 0 p x / ((p : ℝ) - 1))
      atTop (nhds 0) := by
  have hbase := tendsto_classicalCoherenceThreshold_div_nat x
  have hupper : Tendsto (fun p : ℕ ↦
      2 * (classicalCoherenceThreshold 0 p x / (p : ℝ)))
      atTop (nhds 0) := by simpa using (tendsto_const_nhds.mul hbase :
        Tendsto (fun p : ℕ ↦
          (2 : ℝ) * (classicalCoherenceThreshold 0 p x / (p : ℝ)))
          atTop (nhds (2 * 0)))
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  apply squeeze_zero' (g := fun p : ℕ ↦
    2 * (classicalCoherenceThreshold 0 p x / (p : ℝ)))
  · filter_upwards [ha.eventually (eventually_ge_atTop 0),
      eventually_ge_atTop 2] with p hap hp
    exact div_nonneg (by simpa [classicalCoherenceThreshold] using hap)
      (by have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
          linarith)
  · filter_upwards [ha.eventually (eventually_ge_atTop 0),
      eventually_ge_atTop 2] with p hap hp
    have hpR : (0 : ℝ) < (p : ℝ) := by positivity
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hpredR : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hA : 0 ≤ classicalCoherenceThreshold 0 p x := by
      simpa [classicalCoherenceThreshold] using hap
    rw [div_le_iff₀ hpredR]
    have hratio : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by
      nlinarith
    field_simp [hpR.ne']
    nlinarith
  · exact hupper

/-- Uniform all-gap scale separation for the fixed-prefix log-determinant
perturbation. -/
theorem tendsto_classicalThreshold_over_globalNullScale_zero
    {mseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      (classicalCoherenceThreshold (mseq p) p x / (mseq p : ℝ)) /
        Real.sqrt (nullVSeries (mseq p) p))
      atTop (nhds 0) := by
  have ha := tendsto_classicalCoherenceThreshold_atTop x
  have hupper := tendsto_classicalCoherenceThreshold_div_pred_zero x
  apply squeeze_zero' (g := fun p : ℕ ↦
    classicalCoherenceThreshold 0 p x / ((p : ℝ) - 1))
  · filter_upwards [hadm, ha.eventually (eventually_ge_atTop 0)] with p hp hap
    exact div_nonneg
      (div_nonneg (by simpa [classicalCoherenceThreshold] using hap)
        (Nat.cast_nonneg _))
      (Real.sqrt_nonneg _)
  · filter_upwards [hadm, ha.eventually (eventually_ge_atTop 0)] with p hp hap
    exact threshold_div_dimension_div_sqrt_nullVSeries_le hp
      (by simpa [classicalCoherenceThreshold] using hap)
  · simpa [classicalCoherenceThreshold] using hupper

end

end LogdetLean.Coherence
