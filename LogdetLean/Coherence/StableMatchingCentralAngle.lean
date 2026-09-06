import LogdetLean.Coherence.OneEdgeLogPrefixBounds
import LogdetLean.Coherence.CanonicalOneEdgeMarkReplacement
import LogdetLean.Coherence.StableMatchingFrameIndependence
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic
/-!
# Negligibility of the central internal angles in a stable matching

The null log determinant differs from the orientation/frame log determinant
by the sum of the `s` internal two-column log-angle factors.  This file proves
a finite-sample `L¹` bound for the centered, null-standardized sum.  The bound
is deliberately based on the already verified one-edge logarithmic estimate;
no new variance identity is needed.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The centered internal null-angle contribution of `s` independent
Gaussian pairs, divided by the full `p`-column null scale. -/
def stableMatchingCentralAngleCorrection
    (m p s : ℕ) (v : Fin s → E × E) : ℝ :=
  ∑ e, oneEdgeCenteredPrefix (1 / 2)
    (((m - 1 : ℕ) : ℝ) / 2)
    (Real.sqrt (nullVSeries m p))
    (squaredNormalizedInner (v e).1 (v e).2)

theorem measurable_stableMatchingCentralAngleCorrection
    (m p s : ℕ) :
    Measurable (stableMatchingCentralAngleCorrection (E := E) m p s) := by
  unfold stableMatchingCentralAngleCorrection
  apply Finset.measurable_sum
  intro e _he
  exact (measurable_oneEdgeCenteredPrefix
    (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m p))).comp
        (measurable_uncurry_squaredNormalizedInner.comp (measurable_pi_apply e))

/-- Every coordinate summand is integrable under the independent-pair
product law. -/
theorem integrable_stableMatchingCentralAngleCoordinate
    {m p s : ℕ} (hdim : Module.finrank ℝ E = m)
    (hadm : Admissible m p) (hm6 : 6 ≤ m) (e : Fin s) :
    Integrable
      (fun v : Fin s → E × E ↦
        oneEdgeCenteredPrefix (1 / 2)
          (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m p))
          (squaredNormalizedInner (v e).1 (v e).2))
      (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) := by
  have hb : (1 : ℝ) < (((m - 1 : ℕ) : ℝ) / 2) := by
    have hmR : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm6
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
    linarith
  let corr : E × E → ℝ := fun z ↦ squaredNormalizedInner z.1 z.2
  have hcorr : MeasurePreserving corr
      ((stdGaussian E).prod (stdGaussian E))
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) :=
    ⟨measurable_uncurry_squaredNormalizedInner,
      map_squaredNormalizedInner_gaussianProduct
        (E := E) m hdim (by omega)⟩
  have hbase : Integrable
      (oneEdgeCenteredPrefix (1 / 2)
        (((m - 1 : ℕ) : ℝ) / 2)
        (Real.sqrt (nullVSeries m p)))
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) :=
    integrable_oneEdgeCenteredPrefix_betaMeasure (by norm_num) hb
  have hpair : Integrable
      (fun z : E × E ↦
        oneEdgeCenteredPrefix (1 / 2)
          (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m p))
          (squaredNormalizedInner z.1 z.2))
      ((stdGaussian E).prod (stdGaussian E)) := by
    simpa [corr, Function.comp_def] using
      hcorr.integrable_comp_of_integrable hbase
  exact (measurePreserving_eval
    (fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) e).integrable_comp_of_integrable
      hpair

/-- Finite-sample `L¹` bound for the complete centered internal-angle sum. -/
theorem integral_abs_stableMatchingCentralAngleCorrection_le
    {m p s : ℕ} (hdim : Module.finrank ℝ E = m)
    (hadm : Admissible m p) (hm6 : 6 ≤ m) :
    (∫ v : Fin s → E × E,
        |stableMatchingCentralAngleCorrection m p s v|
        ∂Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) ≤
      4 * (s : ℝ) /
        ((m : ℝ) * Real.sqrt (nullVSeries m p)) := by
  let mu : Measure (Fin s → E × E) :=
    Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)
  let X : Fin s → (Fin s → E × E) → ℝ := fun e v ↦
    oneEdgeCenteredPrefix (1 / 2)
      (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m p))
      (squaredNormalizedInner (v e).1 (v e).2)
  have hX : ∀ e, Integrable (X e) mu := fun e ↦ by
    simpa [mu, X] using
      integrable_stableMatchingCentralAngleCoordinate
        (E := E) hdim hadm hm6 e
  have hsum : Integrable (fun v ↦ ∑ e, X e v) mu := by
    exact integrable_finsetSum Finset.univ fun e _he ↦ hX e
  have habsSum : Integrable (fun v ↦ |∑ e, X e v|) mu := hsum.abs
  have habsTerms : Integrable (fun v ↦ ∑ e, |X e v|) mu := by
    exact integrable_finsetSum Finset.univ fun e _he ↦ (hX e).abs
  calc
    (∫ v : Fin s → E × E,
        |stableMatchingCentralAngleCorrection m p s v|
        ∂Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) =
        ∫ v, |∑ e, X e v| ∂mu := by rfl
    _ ≤ ∫ v, ∑ e, |X e v| ∂mu := by
      apply integral_mono habsSum habsTerms
      intro v
      simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using
        (Finset.abs_sum_le_sum_abs (fun e : Fin s ↦ X e v) Finset.univ)
    _ = ∑ e, ∫ v, |X e v| ∂mu := by
      rw [integral_finsetSum Finset.univ]
      intro e _he
      exact (hX e).abs
    _ ≤ ∑ _e : Fin s,
        4 / ((m : ℝ) * Real.sqrt (nullVSeries m p)) := by
      apply Finset.sum_le_sum
      intro e _he
      have hpairInt : Integrable
          (fun z : E × E ↦
            oneEdgeCenteredPrefix (1 / 2)
              (((m - 1 : ℕ) : ℝ) / 2)
              (Real.sqrt (nullVSeries m p))
              (squaredNormalizedInner z.1 z.2))
          ((stdGaussian E).prod (stdGaussian E)) := by
        have hb : (1 : ℝ) < (((m - 1 : ℕ) : ℝ) / 2) := by
          have hmR : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm6
          rw [Nat.cast_sub (by omega : 1 ≤ m)]
          norm_num
          linarith
        let corr : E × E → ℝ := fun z ↦ squaredNormalizedInner z.1 z.2
        have hcorr : MeasurePreserving corr
            ((stdGaussian E).prod (stdGaussian E))
            (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) :=
          ⟨measurable_uncurry_squaredNormalizedInner,
            map_squaredNormalizedInner_gaussianProduct
              (E := E) m hdim (by omega)⟩
        exact hcorr.integrable_comp_of_integrable
          (integrable_oneEdgeCenteredPrefix_betaMeasure (by norm_num) hb)
      have htransport :=
        (measurePreserving_eval
          (fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) e).hasLaw.integral_comp
          hpairInt.abs.aestronglyMeasurable
      have hbase :=
        integral_abs_oneEdgeCenteredPrefix_gaussianPair_nullVSeries_le
          (E := E) hdim hadm hm6
      change (∫ v : Fin s → E × E, |X e v| ∂mu) ≤ _
      rw [show (∫ v : Fin s → E × E, |X e v| ∂mu) =
          ∫ z : E × E,
            |oneEdgeCenteredPrefix (1 / 2)
              (((m - 1 : ℕ) : ℝ) / 2)
              (Real.sqrt (nullVSeries m p))
              (squaredNormalizedInner z.1 z.2)|
              ∂((stdGaussian E).prod (stdGaussian E)) by
        simpa [mu, X, Function.comp_def] using htransport]
      exact hbase
    _ = 4 * (s : ℝ) /
        ((m : ℝ) * Real.sqrt (nullVSeries m p)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
      ring

/-- The balanced block-count scaling forces the central internal-angle
correction to vanish in `L¹`, uniformly across every nonsingular regime. -/
theorem tendsto_balancedCentralAngleL1Envelope_zero
    {mseq sseq : ℕ → ℕ} {theta : ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hbalance : Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) * Real.log (p : ℝ) /
        ((mseq p : ℝ) * Real.sqrt (nullVSeries (mseq p) p)))
      atTop (nhds theta)) :
    Tendsto (fun p : ℕ ↦
      4 * (sseq p : ℝ) /
        ((mseq p : ℝ) * Real.sqrt (nullVSeries (mseq p) p)))
      atTop (nhds 0) := by
  have hinvLog : Tendsto (fun p : ℕ ↦ 1 / Real.log (p : ℝ))
      atTop (nhds 0) := by
    have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    simpa using hlog.const_div_atTop (1 : ℝ)
  have hprod := hbalance.mul hinvLog
  have hfour : Tendsto (fun _ : ℕ ↦ (4 : ℝ)) atTop (nhds 4) :=
    tendsto_const_nhds
  have hscaled := hfour.mul hprod
  simpa only [mul_zero] using hscaled.congr' (by
    filter_upwards [hadm, eventually_ge_atTop 2] with p hp hp2
    have hm : (mseq p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt
        (lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_two hp.1) hp.2))
    have hV : Real.sqrt (nullVSeries (mseq p) p) ≠ 0 :=
      (sqrt_nullVSeries_pos hp).ne'
    have hlog : Real.log (p : ℝ) ≠ 0 := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
      exact (Real.log_pos hp1).ne'
    field_simp [hm, hV, hlog])

end

end LogdetLean.Coherence
