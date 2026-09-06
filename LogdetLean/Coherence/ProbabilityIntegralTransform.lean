import LogdetLean.Coherence.PaperWeakConvergence
import LogdetLean.NormalScaleComparison
import Mathlib.Probability.Distributions.Uniform
/-!
# Probability integral transforms used by the combined tests

This file proves the probability integral transform needed by the paper for
the standard normal and standard Gumbel coordinates.  The proof is stated for
an arbitrary continuous strictly increasing distribution function and is then
specialized to the two laws used in the article.
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

/-- Every value of a continuous strictly increasing probability distribution
function lies strictly between zero and one. -/
theorem cdf_mem_Ioo_of_strictMono
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hstrict : StrictMono (cdf μ)) (x : ℝ) :
    cdf μ x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · have hlt := hstrict (sub_lt_self x zero_lt_one)
    exact (cdf_nonneg μ (x - 1)).trans_lt hlt
  · have hlt := hstrict (lt_add_of_pos_right x zero_lt_one)
    exact hlt.trans_le (cdf_le_one μ (x + 1))

/-- A continuous strictly increasing probability distribution function takes
every value strictly between zero and one. -/
theorem exists_eq_cdf_of_mem_Ioo
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (cdf μ))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ∃ x : ℝ, cdf μ x = u := by
  obtain ⟨a, ha⟩ :=
    ((tendsto_order.1 (tendsto_cdf_atBot μ)).2 u hu.1).exists
  obtain ⟨b, hb⟩ :=
    ((tendsto_order.1 (tendsto_cdf_atTop μ)).1 u hu.2).exists
  have hab : a ≤ b := by
    by_contra hba
    have hle := monotone_cdf μ (le_of_not_ge hba)
    linarith
  have huIcc : u ∈ Icc (cdf μ a) (cdf μ b) := ⟨ha.le, hb.le⟩
  rcases (intermediate_value_Icc hab hcont.continuousOn) huIcc with
    ⟨x, _hx, hxu⟩
  exact ⟨x, hxu⟩

/-- A continuous strictly increasing distribution function maps its own law
to the unit uniform law on `(0,1]`. -/
theorem map_cdf_eq_fisherUnitUniformMeasure
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (cdf μ))
    (hstrict : StrictMono (cdf μ)) :
    Measure.map (cdf μ) μ = fisherUnitUniformMeasure := by
  apply Measure.ext_of_Iic
  intro u
  rw [Measure.map_apply hcont.measurable measurableSet_Iic]
  unfold fisherUnitUniformMeasure
  rw [Measure.restrict_apply measurableSet_Iic]
  by_cases hu0 : u < 0
  · have hpre : cdf μ ⁻¹' Iic u = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hx ↦ (not_le_of_gt hu0) ((cdf_nonneg μ x).trans hx)
    have hinter : Iic u ∩ Ioc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
      intro hx
      linarith
    simp only [hpre, hinter, measure_empty]
  · have hu0' : 0 ≤ u := le_of_not_gt hu0
    by_cases hu1 : 1 ≤ u
    · have hpre : cdf μ ⁻¹' Iic u = univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (cdf_le_one μ x).trans hu1
      have hinter : Iic u ∩ Ioc (0 : ℝ) 1 = Ioc 0 1 := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · exact fun hx ↦ hx.2
        · exact fun hx ↦ ⟨hx.2.trans hu1, hx⟩
      rw [hpre, measure_univ, hinter, Real.volume_Ioc]
      norm_num
    · have hu1' : u < 1 := lt_of_not_ge hu1
      by_cases hueq : u = 0
      · subst u
        have hpre : cdf μ ⁻¹' Iic 0 = ∅ := by
          ext x
          simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
          exact fun hx ↦ (not_le_of_gt (cdf_mem_Ioo_of_strictMono μ hstrict x).1) hx
        have hinter : Iic (0 : ℝ) ∩ Ioc 0 1 = ∅ := by
          ext x
          simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
          intro hx
          linarith
        simp only [hpre, hinter, measure_empty]
      · have huIoo : u ∈ Ioo (0 : ℝ) 1 :=
          ⟨lt_of_le_of_ne hu0' (Ne.symm hueq), hu1'⟩
        obtain ⟨q, hq⟩ := exists_eq_cdf_of_mem_Ioo μ hcont huIoo
        have hpre : cdf μ ⁻¹' Iic u = Iic q := by
          ext x
          simp only [mem_preimage, mem_Iic]
          rw [← hq, hstrict.le_iff_le]
        have hinter : Iic u ∩ Ioc (0 : ℝ) 1 = Ioc 0 u := by
          ext x
          simp only [mem_inter_iff, mem_Iic, mem_Ioc]
          constructor
          · exact fun hx ↦ ⟨hx.2.1, hx.1⟩
          · exact fun hx ↦ ⟨hx.2, hx.1, hx.2.trans hu1'.le⟩
        rw [hpre, ← ofReal_cdf μ q, hq, hinter, Real.volume_Ioc]
        simp only [sub_zero]

/-- The standard normal distribution function is continuous. -/
theorem continuous_standardNormalCDF : Continuous standardNormalCDF := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (LogdetLean.hasDerivAt_standardGaussian_cdf x).continuousAt

/-- The standard normal distribution function is strictly increasing. -/
theorem strictMono_standardNormalCDF : StrictMono standardNormalCDF := by
  exact strictMono_of_hasDerivAt_pos
    LogdetLean.hasDerivAt_standardGaussian_cdf
    (fun x ↦ gaussianPDFReal_pos 0 1 x one_ne_zero)

/-- Exact probability integral transform for the standard normal law. -/
theorem map_standardNormalCDF_standardNormal :
    Measure.map standardNormalCDF (gaussianReal 0 1) =
      fisherUnitUniformMeasure := by
  exact map_cdf_eq_fisherUnitUniformMeasure (gaussianReal 0 1)
    continuous_standardNormalCDF strictMono_standardNormalCDF

/-- The standard Gumbel distribution function. -/
def standardGumbelCDF (t : ℝ) : ℝ :=
  Real.exp (-Real.exp (-t))

theorem continuous_standardGumbelCDF : Continuous standardGumbelCDF := by
  unfold standardGumbelCDF
  fun_prop

theorem strictMono_standardGumbelCDF : StrictMono standardGumbelCDF := by
  intro a b hab
  dsimp [standardGumbelCDF]
  exact Real.exp_lt_exp.mpr (neg_lt_neg (Real.exp_lt_exp.mpr (neg_lt_neg hab)))

theorem cdf_standardGumbelMeasure :
    cdf standardGumbelMeasure = standardGumbelCDF := by
  funext t
  rw [cdf_eq_real, standardGumbelMeasure_real_Iic]
  rfl

/-- Exact probability integral transform for the standard Gumbel law. -/
theorem map_standardGumbelCDF_standardGumbel :
    Measure.map standardGumbelCDF standardGumbelMeasure =
      fisherUnitUniformMeasure := by
  have hcont : Continuous (cdf standardGumbelMeasure) := by
    rw [cdf_standardGumbelMeasure]
    exact continuous_standardGumbelCDF
  have hstrict : StrictMono (cdf standardGumbelMeasure) := by
    rw [cdf_standardGumbelMeasure]
    exact strictMono_standardGumbelCDF
  simpa only [cdf_standardGumbelMeasure] using
    map_cdf_eq_fisherUnitUniformMeasure standardGumbelMeasure hcont hstrict

end

end LogdetLean.Coherence
