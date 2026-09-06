import LogdetLean.Coherence.PearsonThresholdShift
import LogdetLean.Coherence.StandardGaussianSharpMills
import LogdetLean.Coherence.NoncentralPearsonUniformMD
import LogdetLean.Coherence.RareBernoulliPoisson
import Mathlib.Tactic
/-!
# Homogeneous planted-edge extreme intensity

This module derives the nonnull exponential height intensity from the exact
Pearson threshold and the sharp Gaussian tail ratio.  It is the deterministic
and Gaussian-tail core of the balanced homogeneous matching alternative.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real MeasureTheory ProbabilityTheory Set
open scoped Topology

/-- If the lower shifted threshold `t_p` is asymptotically `q_p(0)/sqrt 2`
and `s_p Q(t_p)` tends to `kappa`, then the two-sided Gaussian surrogate at
the exact Pearson height `x` has aggregate intensity
`kappa * exp(-x/(2*sqrt 2))`. -/
theorem tendsto_homogeneousPlantedGaussianIntensity
    {mseq sseq : ℕ → ℕ} {tseq : ℕ → ℝ} {kappa : ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (htRatio : Tendsto (fun p : ℕ ↦
      tseq p / pearsonExactThreshold (mseq p) p 0)
      atTop (nhds (1 / Real.sqrt 2)))
    (hbase : Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) * standardGaussianUpperTail (tseq p))
      atTop (nhds kappa))
    (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) *
        pearsonMDGaussianTailDenominator
          (pearsonExactThreshold (mseq p) p x)
          (pearsonExactThreshold (mseq p) p 0 - tseq p))
      atTop (nhds (kappa * Real.exp (-x / (2 * Real.sqrt 2)))) := by
  let q0 : ℕ → ℝ := fun p ↦ pearsonExactThreshold (mseq p) p 0
  let qx : ℕ → ℝ := fun p ↦ pearsonExactThreshold (mseq p) p x
  let h : ℕ → ℝ := fun p ↦ qx p - q0 p
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2ne : Real.sqrt 2 ≠ 0 := hsqrt2.ne'
  have hratioPos : 0 < (1 / Real.sqrt 2 : ℝ) := one_div_pos.mpr hsqrt2
  have hq0Top : Tendsto q0 atTop atTop :=
    tendsto_pearsonExactThreshold_zero_atTop hadm
  have htTop : Tendsto tseq atTop atTop := by
    have hprod := hq0Top.atTop_mul_pos hratioPos htRatio
    apply hprod.congr'
    filter_upwards [hq0Top.eventually (eventually_ne_atTop (0 : ℝ))]
      with p hp
    dsimp [q0] at hp ⊢
    field_simp [hp]
  have hscaled : Tendsto (fun p : ℕ ↦ q0 p * h p)
      atTop (nhds (x / 2)) := by
    simpa [q0, qx, h] using
      tendsto_pearsonExactThreshold_zero_mul_sub hadm x
  have hh : Tendsto h atTop (nhds 0) := by
    have hdiv := hscaled.div_atTop hq0Top
    apply hdiv.congr'
    filter_upwards [hq0Top.eventually (eventually_ne_atTop (0 : ℝ))]
      with p hp
    field_simp [hp]
  have htCross : Tendsto (fun p : ℕ ↦ tseq p * h p)
      atTop (nhds (x / (2 * Real.sqrt 2))) := by
    have hmul := htRatio.mul hscaled
    have hmul' : Tendsto (fun p : ℕ ↦
        (tseq p / q0 p) * (q0 p * h p))
        atTop (nhds (x / (2 * Real.sqrt 2))) := by
      convert hmul using 1 <;> field_simp [hsqrt2ne] <;> ring
    apply hmul'.congr'
    filter_upwards [hq0Top.eventually (eventually_ne_atTop (0 : ℝ))]
      with p hp
    field_simp [hp]
  have hfirst := tendsto_standardGaussianUpperTail_add_div
    htTop hh htCross
  have hfirst' : Tendsto (fun p : ℕ ↦
      standardGaussianUpperTail (tseq p + h p) /
        standardGaussianUpperTail (tseq p))
      atTop (nhds (Real.exp (-x / (2 * Real.sqrt 2)))) := by
    convert hfirst using 1 <;> ring
  have hq0DivT : Tendsto (fun p : ℕ ↦ q0 p / tseq p)
      atTop (nhds (Real.sqrt 2)) := by
    have hinv := htRatio.inv₀ (by exact one_div_ne_zero hsqrt2ne)
    have heq : (fun p : ℕ ↦ (tseq p / q0 p)⁻¹) =ᶠ[atTop]
        (fun p : ℕ ↦ q0 p / tseq p) := by
      filter_upwards [hq0Top.eventually (eventually_ne_atTop (0 : ℝ)),
          htTop.eventually (eventually_ne_atTop (0 : ℝ))]
        with p hq ht
      field_simp [hq, ht]
    have hsimp : (1 / Real.sqrt 2 : ℝ)⁻¹ = Real.sqrt 2 := by
      field_simp [hsqrt2ne]
    simpa [hsimp] using hinv.congr' heq
  have hhDivT : Tendsto (fun p : ℕ ↦ h p / tseq p)
      atTop (nhds 0) := hh.div_atTop htTop
  let y : ℕ → ℝ := fun p ↦ qx p + (q0 p - tseq p)
  have hyRatio : Tendsto (fun p : ℕ ↦ y p / tseq p)
      atTop (nhds (2 * Real.sqrt 2 - 1)) := by
    have hlim := (hq0DivT.const_mul 2).add hhDivT |>.sub_const 1
    have hlim' : Tendsto (fun p : ℕ ↦
        2 * (q0 p / tseq p) + h p / tseq p - 1)
        atTop (nhds (2 * Real.sqrt 2 - 1)) := by simpa using hlim
    apply hlim'.congr'
    filter_upwards [htTop.eventually (eventually_ne_atTop (0 : ℝ))]
      with p ht
    dsimp [y, h, qx, q0]
    field_simp [ht]
    ring
  have hr : (1 : ℝ) < 2 * Real.sqrt 2 - 1 := by
    have hsquare : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have hyTop : Tendsto y atTop atTop := by
    have hprod := htTop.atTop_mul_pos (by nlinarith : 0 < 2 * Real.sqrt 2 - 1)
      hyRatio
    apply hprod.congr'
    filter_upwards [htTop.eventually (eventually_ne_atTop (0 : ℝ))]
      with p ht
    field_simp [ht]
  have hsecond := tendsto_standardGaussianUpperTail_div_zero_of_ratio
    htTop hyTop hyRatio hr
  have hdenRatio : Tendsto (fun p : ℕ ↦
      pearsonMDGaussianTailDenominator (qx p) (q0 p - tseq p) /
        standardGaussianUpperTail (tseq p))
      atTop (nhds (Real.exp (-x / (2 * Real.sqrt 2)))) := by
    have hadd := hfirst'.add hsecond
    have hadd' : Tendsto (fun p : ℕ ↦
        standardGaussianUpperTail (tseq p + h p) /
            standardGaussianUpperTail (tseq p) +
          standardGaussianUpperTail (y p) /
            standardGaussianUpperTail (tseq p))
        atTop (nhds (Real.exp (-x / (2 * Real.sqrt 2)))) := by
      simpa using hadd
    apply hadd'.congr'
    filter_upwards [htTop.eventually (eventually_ne_atTop (0 : ℝ))]
      with p ht
    have hQt := (standardGaussianUpperTail_pos (tseq p)).ne'
    unfold pearsonMDGaussianTailDenominator
    dsimp [y, h]
    field_simp [hQt]
    ring
  have hfinal := hbase.mul hdenRatio
  apply hfinal.congr'
  filter_upwards with p
  have hQt : 1 - standardNormalCDF (tseq p) ≠ 0 := by
    simpa only [standardGaussianUpperTail_eq_one_sub_standardNormalCDF] using
      (standardGaussianUpperTail_pos (tseq p)).ne'
  dsimp [q0, qx]
  field_simp [hQt]

/-- The preceding Gaussian intensity is the actual aggregate two-sided
Pearson tail intensity.  The only additional input is the kernel-verified
uniform noncentral Pearson approximation. -/
theorem tendsto_homogeneousPlantedPearsonIntensity
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hgap : C ^ 2 / 2 < L)
    {mseq sseq : ℕ → ℕ} {rhoSeq tseq : ℕ → ℝ} {kappa : ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hrho : ∀ᶠ p in atTop, |rhoSeq p| < 1)
    (hlambda : ∀ᶠ p in atTop,
      pearsonRubenNoncentrality (mseq p) (rhoSeq p) =
        pearsonExactThreshold (mseq p) p 0 - tseq p)
    (x_placeholder : ℝ)
    (hscale : ∀ᶠ p in atTop,
      pearsonExactThreshold (mseq p) p x_placeholder +
          |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ)))
    (htRatio : Tendsto (fun p : ℕ ↦
      tseq p / pearsonExactThreshold (mseq p) p 0)
      atTop (nhds (1 / Real.sqrt 2)))
    (hbase : Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) * standardGaussianUpperTail (tseq p))
      atTop (nhds kappa)) :
    Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) *
        gaussianPearsonTwoSidedTail
          (E := EuclideanSpace ℝ (Fin (mseq p)))
          (mseq p) (rhoSeq p)
          (pearsonExactThreshold (mseq p) p x_placeholder))
      atTop
      (nhds (kappa *
        Real.exp (-x_placeholder / (2 * Real.sqrt 2)))) := by
  let q : ℕ → ℝ := fun p ↦
    pearsonExactThreshold (mseq p) p x_placeholder
  let lambda : ℕ → ℝ := fun p ↦
    pearsonRubenNoncentrality (mseq p) (rhoSeq p)
  let D : ℕ → ℝ := fun p ↦
    pearsonMDGaussianTailDenominator (q p) (lambda p)
  let P : ℕ → ℝ := fun p ↦
    gaussianPearsonTwoSidedTail
      (E := EuclideanSpace ℝ (Fin (mseq p)))
      (mseq p) (rhoSeq p) (q p)
  have hq : ∀ᶠ p in atTop, 0 ≤ q p := by
    filter_upwards with p
    exact Real.sqrt_nonneg _
  have hMD : Tendsto (fun p : ℕ ↦ P p / D p)
      atTop (nhds 1) := by
    dsimp [P, D, q, lambda]
    exact tendsto_gaussianPearsonTwoSidedTail_div_gaussianTail_one
      hC hL hgap hadm hrho (by simpa [q] using hq)
        (by simpa [q, lambda] using hscale)
  have hDIntensity : Tendsto (fun p : ℕ ↦ (sseq p : ℝ) * D p)
      atTop
      (nhds (kappa *
        Real.exp (-x_placeholder / (2 * Real.sqrt 2)))) := by
    have hraw := tendsto_homogeneousPlantedGaussianIntensity
      hadm htRatio hbase x_placeholder
    apply hraw.congr'
    filter_upwards [hlambda] with p hp
    dsimp [D, q, lambda]
    rw [hp]
  have hprod := hDIntensity.mul hMD
  have hprod' : Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) * D p * (P p / D p))
      atTop
      (nhds (kappa *
        Real.exp (-x_placeholder / (2 * Real.sqrt 2)))) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards with p
  have hDpos : 0 < D p := by
    dsimp [D]
    exact pearsonMDGaussianTailDenominator_pos _ _
  dsimp [P, q]
  field_simp [hDpos.ne']

/-- Exact homogeneous planted-block void limit.  The probability on the left
is taken under the product of `s_p` independent Gaussian pair blocks. -/
theorem tendsto_homogeneousPlantedPearsonVoid
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hgap : C ^ 2 / 2 < L)
    {mseq sseq : ℕ → ℕ} {rhoSeq tseq : ℕ → ℝ} {kappa : ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hs : Tendsto (fun p ↦ (sseq p : ℝ)) atTop atTop)
    (hrho : ∀ᶠ p in atTop, |rhoSeq p| < 1)
    (hlambda : ∀ᶠ p in atTop,
      pearsonRubenNoncentrality (mseq p) (rhoSeq p) =
        pearsonExactThreshold (mseq p) p 0 - tseq p)
    (x : ℝ)
    (hscale : ∀ᶠ p in atTop,
      pearsonExactThreshold (mseq p) p x +
          |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ)))
    (htRatio : Tendsto (fun p : ℕ ↦
      tseq p / pearsonExactThreshold (mseq p) p 0)
      atTop (nhds (1 / Real.sqrt 2)))
    (hbase : Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) * standardGaussianUpperTail (tseq p))
      atTop (nhds kappa)) :
    Tendsto (fun p : ℕ ↦
      (Measure.pi (fun _ : Fin (sseq p) ↦
          (stdGaussian (EuclideanSpace ℝ (Fin (mseq p)))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin (mseq p)))))).real
        (Set.univ.pi fun _ : Fin (sseq p) ↦
          (plantedPearsonExceedanceEvent
            (E := EuclideanSpace ℝ (Fin (mseq p)))
            (mseq p) (rhoSeq p)
            (pearsonExactThreshold (mseq p) p x))ᶜ))
      atTop
      (nhds (Real.exp (-(kappa *
        Real.exp (-x / (2 * Real.sqrt 2)))))) := by
  let qprob : ℕ → ℝ := fun p ↦
    gaussianPearsonTwoSidedTail
      (E := EuclideanSpace ℝ (Fin (mseq p)))
      (mseq p) (rhoSeq p) (pearsonExactThreshold (mseq p) p x)
  let intensity : ℝ := kappa * Real.exp (-x / (2 * Real.sqrt 2))
  have hIntensity : Tendsto (fun p ↦ (sseq p : ℝ) * qprob p)
      atTop (nhds intensity) := by
    dsimp [qprob, intensity]
    exact tendsto_homogeneousPlantedPearsonIntensity
      hC hL hgap hadm hrho hlambda x hscale htRatio hbase
  have hqzero := tendsto_rareBernoulliProbability_zero hs hIntensity
  have hq0 : ∀ᶠ p in atTop, 0 ≤ qprob p := by
    filter_upwards with p
    unfold qprob gaussianPearsonTwoSidedTail
    exact add_nonneg (measureReal_nonneg) (measureReal_nonneg)
  have hq1 : ∀ᶠ p in atTop, qprob p < 1 :=
    hqzero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hvoid := tendsto_rareBernoulliVoid hs hIntensity hq0 hq1
  apply hvoid.congr'
  filter_upwards [eventually_classicalCoherenceThreshold_scoreRange hadm x]
    with p hrange
  have hqnonneg : 0 ≤ pearsonExactThreshold (mseq p) p x :=
    Real.sqrt_nonneg _
  exact (real_pi_all_plantedPearson_noExceedance_eq_pow
    (E := EuclideanSpace ℝ (Fin (mseq p)))
    (mseq p) (sseq p) (rhoSeq p)
    (pearsonExactThreshold (mseq p) p x) hqnonneg).symm

/-- Planted intensity of one bounded score window `(a,b]`, obtained by
subtracting its two upper-tail intensities. -/
theorem tendsto_homogeneousPlantedPearsonWindowIntensity
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hgap : C ^ 2 / 2 < L)
    {mseq sseq : ℕ → ℕ} {rhoSeq tseq : ℕ → ℝ} {kappa : ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hrho : ∀ᶠ p in atTop, |rhoSeq p| < 1)
    (hlambda : ∀ᶠ p in atTop,
      pearsonRubenNoncentrality (mseq p) (rhoSeq p) =
        pearsonExactThreshold (mseq p) p 0 - tseq p)
    (a b : ℝ)
    (hscaleA : ∀ᶠ p in atTop,
      pearsonExactThreshold (mseq p) p a +
          |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ)))
    (hscaleB : ∀ᶠ p in atTop,
      pearsonExactThreshold (mseq p) p b +
          |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ)))
    (htRatio : Tendsto (fun p : ℕ ↦
      tseq p / pearsonExactThreshold (mseq p) p 0)
      atTop (nhds (1 / Real.sqrt 2)))
    (hbase : Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) * standardGaussianUpperTail (tseq p))
      atTop (nhds kappa)) :
    Tendsto (fun p : ℕ ↦
      (sseq p : ℝ) *
        (gaussianPearsonTwoSidedTail
            (E := EuclideanSpace ℝ (Fin (mseq p)))
            (mseq p) (rhoSeq p)
            (pearsonExactThreshold (mseq p) p a) -
          gaussianPearsonTwoSidedTail
            (E := EuclideanSpace ℝ (Fin (mseq p)))
            (mseq p) (rhoSeq p)
            (pearsonExactThreshold (mseq p) p b)))
      atTop
      (nhds (kappa * Real.exp (-a / (2 * Real.sqrt 2)) -
        kappa * Real.exp (-b / (2 * Real.sqrt 2)))) := by
  have ha := tendsto_homogeneousPlantedPearsonIntensity
    hC hL hgap hadm hrho hlambda a hscaleA htRatio hbase
  have hb := tendsto_homogeneousPlantedPearsonIntensity
    hC hL hgap hadm hrho hlambda b hscaleB htRatio hbase
  have hsub := ha.sub hb
  apply hsub.congr'
  filter_upwards with p
  ring

end

end LogdetLean.Coherence
