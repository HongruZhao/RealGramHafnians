import Mathlib.Analysis.Calculus.MeanValue
import LogdetLean.Coherence.PrefixScale
import LogdetLean.NullCenterStandardization
import LogdetLean.LogGammaPolygamma
/-!
# A fixed null center is negligible at the global scale

The conditional prefix argument controls the uncentered fixed-prefix log
determinant.  This file supplies the deterministic companion estimate: for
fixed `q`, its exact null center is `O_q(1/m)`, hence negligible after division
by the standard deviation of the full `p`-dimensional statistic.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real
open scoped Topology

/-- A direct mean-value bound for a positive digamma increment. -/
theorem abs_digammaSeries_sub_le
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |digammaSeries a - digammaSeries b| ≤
      (1 / a + 1 / a ^ 2) * (b - a) := by
  let C : ℝ := 1 / a + 1 / a ^ 2
  have hdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ digammaSeries x := by
    intro x hx
    exact (hasDerivAt_digammaSeries (ha.trans_le hx.1)).differentiableAt
  have hbound : ∀ x ∈ Set.Icc a b, ‖deriv digammaSeries x‖ ≤ C := by
    intro x hx
    rw [(hasDerivAt_digammaSeries (ha.trans_le hx.1)).deriv]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (trigammaSeries_nonneg (ha.trans_le hx.1))]
    calc
      trigammaSeries x ≤ trigammaSeries a :=
        trigammaSeries_antitone ha hx.1
      _ ≤ C := by
        exact trigammaSeries_le_one_div_add_one_div_sq ha
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := digammaSeries) (s := Set.Icc a b)
    hdiff hbound (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  simpa [C, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hab)] using hmv

/-- For a fixed prefix in the range `2q ≤ m`, the exact centering is bounded
by a deliberately loose constant times `q²/m`. -/
theorem abs_nullCenter_le_four_mul_sq_div
    {m q : ℕ} (hq : 2 ≤ q) (hlarge : 2 * q ≤ m) :
    |nullCenter m q| ≤ 4 * (q : ℝ) ^ 2 / (m : ℝ) := by
  have hqm : q ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  rw [nullCenter_eq_nullCenterDigammaSeries hqm]
  unfold nullCenterDigammaSeries
  calc
    |∑ j ∈ Finset.Icc 2 q,
        (digammaSeries (betaShapeA m j) -
          digammaSeries (betaShapeTotal m))| ≤
      ∑ j ∈ Finset.Icc 2 q,
        |digammaSeries (betaShapeA m j) -
          digammaSeries (betaShapeTotal m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Icc 2 q,
        4 * (q : ℝ) / (m : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjbounds := Finset.mem_Icc.mp hj
      have hjm : j ≤ m := hjbounds.2.trans hqm
      have ha : 0 < betaShapeA m j := betaShapeA_pos_of_le hjm
      have hat : betaShapeA m j ≤ betaShapeTotal m :=
        (betaShapeA_lt_total hjbounds.1).le
      have hmqR : (2 : ℝ) * (q : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hlarge
      have hjqR : (j : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hjbounds.2
      have hamin : (m : ℝ) / 4 ≤ betaShapeA m j := by
        unfold betaShapeA
        linarith
      have ha1 : 1 ≤ betaShapeA m j := by
        have hm4R : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
        linarith
      have hinv : 1 / betaShapeA m j ≤ 4 / (m : ℝ) := by
        calc
          1 / betaShapeA m j ≤ 1 / ((m : ℝ) / 4) :=
            one_div_le_one_div_of_le (by positivity) hamin
          _ = 4 / (m : ℝ) := by field_simp [hm0.ne']
      have hinvSq : 1 / (betaShapeA m j) ^ 2 ≤
          4 / (m : ℝ) := by
        calc
          1 / (betaShapeA m j) ^ 2 ≤ 1 / betaShapeA m j := by
            apply one_div_le_one_div_of_le ha
            nlinarith
          _ ≤ 4 / (m : ℝ) := hinv
      have hC : 1 / betaShapeA m j +
          1 / (betaShapeA m j) ^ 2 ≤ 8 / (m : ℝ) := by
        calc
          1 / betaShapeA m j + 1 / (betaShapeA m j) ^ 2 ≤
              4 / (m : ℝ) + 4 / (m : ℝ) := add_le_add hinv hinvSq
          _ = 8 / (m : ℝ) := by ring
      have hgap : betaShapeTotal m - betaShapeA m j ≤
          (q : ℝ) / 2 := by
        unfold betaShapeTotal betaShapeA
        linarith
      have hgap0 : 0 ≤ betaShapeTotal m - betaShapeA m j :=
        sub_nonneg.mpr hat
      calc
        |digammaSeries (betaShapeA m j) -
            digammaSeries (betaShapeTotal m)| ≤
          (1 / betaShapeA m j + 1 / (betaShapeA m j) ^ 2) *
            (betaShapeTotal m - betaShapeA m j) :=
              abs_digammaSeries_sub_le ha hat
        _ ≤ (8 / (m : ℝ)) * ((q : ℝ) / 2) :=
          mul_le_mul hC hgap hgap0 (by positivity)
        _ = 4 * (q : ℝ) / (m : ℝ) := by field_simp [hm0.ne'] <;> ring
    _ = ((Finset.Icc 2 q).card : ℝ) *
        (4 * (q : ℝ) / (m : ℝ)) := by simp
    _ ≤ (q : ℝ) * (4 * (q : ℝ) / (m : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · have hcard : (Finset.Icc 2 q).card ≤ q := by
          rw [Nat.card_Icc]
          omega
        exact_mod_cast hcard
      · positivity
    _ = 4 * (q : ℝ) ^ 2 / (m : ℝ) := by ring

/-- A fixed exact prefix center is negligible relative to the global null
standard deviation, uniformly over every eventual admissible sequence. -/
theorem tendsto_abs_fixedPrefix_nullCenter_over_sqrt_nullVSeries_zero
    (q : ℕ) (hq : 2 ≤ q) (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦
      |nullCenter (mseq p) q| /
        Real.sqrt (nullVSeries (mseq p) p))
      atTop (nhds 0) := by
  let C : ℝ := 4 * (q : ℝ) ^ 2
  have hpcast : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpred : Tendsto (fun p : ℕ ↦ (p : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) hpcast)
  have hupper : Tendsto (fun p : ℕ ↦ C / ((p : ℝ) - 1))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hpred
  apply squeeze_zero' (g := fun p : ℕ ↦ C / ((p : ℝ) - 1))
  · exact Eventually.of_forall fun _ ↦
      div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  · filter_upwards [hadm, eventually_ge_atTop (2 * q)] with p hp hp2q
    have hlarge : 2 * q ≤ mseq p := hp2q.trans hp.2
    have hcenter := abs_nullCenter_le_four_mul_sq_div hq hlarge
    have hVpos : 0 < Real.sqrt (nullVSeries (mseq p) p) :=
      Real.sqrt_pos.2 (nullVSeries_pos hp)
    calc
      |nullCenter (mseq p) q| /
          Real.sqrt (nullVSeries (mseq p) p) ≤
        (C / (mseq p : ℝ)) /
          Real.sqrt (nullVSeries (mseq p) p) := by
            apply div_le_div_of_nonneg_right
            · simpa [C] using hcenter
            · exact hVpos.le
      _ ≤ C / ((p : ℝ) - 1) :=
        threshold_div_dimension_div_sqrt_nullVSeries_le hp (by positivity)
  · exact hupper

/-- The same fixed-center result in the original `nullVariance` notation
used by the standardized sample statistic. -/
theorem tendsto_abs_fixedPrefix_nullCenter_over_sqrt_nullVariance_zero
    (q : ℕ) (hq : 2 ≤ q) (mseq : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p) :
    Tendsto (fun p : ℕ ↦
      |nullCenter (mseq p) q| /
        Real.sqrt (nullVariance (mseq p) p))
      atTop (nhds 0) := by
  apply (tendsto_abs_fixedPrefix_nullCenter_over_sqrt_nullVSeries_zero
    q hq mseq hadm).congr'
  filter_upwards [hadm] with p hp
  rw [nullVariance_eq_nullVSeries hp.2]

end

end LogdetLean.Coherence
