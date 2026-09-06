import Mathlib.Probability.Distributions.Exponential
import LogdetLean.ScalarGammaBetaBridge
/-!
# Fisher's two component reference law

This module proves the exact finite reference law used by Fisher's method.
The unit uniform distribution is Lebesgue measure restricted to `(0,1]`.
The chi square distribution with `nu` degrees of freedom is represented by
the mathematically equivalent Gamma distribution with shape `nu / 2` and
rate `1 / 2`.
-/

namespace LogdetLean.Coherence

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

noncomputable section

/-- The uniform probability measure on the unit interval. -/
def fisherUnitUniformMeasure : Measure ℝ :=
  volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure fisherUnitUniformMeasure := by
  refine ⟨?_⟩
  simp [fisherUnitUniformMeasure, Real.volume_Ioc]

/-- The chi square law with `nu` degrees of freedom, represented as the
Gamma law with shape `nu / 2` and rate `1 / 2`. -/
def chiSquareMeasure (nu : ℝ) : Measure ℝ :=
  gammaMeasure (nu / 2) (1 / 2)

/-- If `U` is uniform on `(0,1]`, then `-2 log U` is exponential with rate
`1/2`, equivalently chi square with two degrees of freedom. -/
theorem map_negTwoLog_fisherUnitUniform :
    Measure.map (fun u : ℝ ↦ -2 * Real.log u) fisherUnitUniformMeasure =
      expMeasure (1 / 2) := by
  let _ : IsProbabilityMeasure (expMeasure (1 / 2)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  unfold fisherUnitUniformMeasure
  rw [Measure.restrict_apply
    (measurableSet_Iic.preimage (by fun_prop))]
  rw [← ofReal_cdf (expMeasure (1 / 2)) x]
  rw [cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1 / 2)]
  split_ifs with hx
  · have hexp0 : 0 < Real.exp (-x / 2) := Real.exp_pos _
    have hexp1 : Real.exp (-x / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hset :
        Ioc (0 : ℝ) 1 ∩ (fun u : ℝ ↦ -2 * Real.log u) ⁻¹' Iic x =
          Icc (Real.exp (-x / 2)) 1 := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_preimage, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨⟨hu0, hu1⟩, hlog⟩
        refine ⟨?_, hu1⟩
        have hdiv : -x / 2 ≤ Real.log u := by linarith
        exact (Real.le_log_iff_exp_le hu0).mp hdiv
      · rintro ⟨hlo, hu1⟩
        have hu0 : 0 < u := hexp0.trans_le hlo
        refine ⟨⟨hu0, hu1⟩, ?_⟩
        have hlog : -x / 2 ≤ Real.log u :=
          (Real.le_log_iff_exp_le hu0).mpr hlo
        linarith
    rw [inter_comm, hset, Real.volume_Icc]
    rw [show (1 : ℝ) - Real.exp (-x / 2) =
        1 - Real.exp (-(1 / 2 * x)) by ring]
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hset :
        Ioc (0 : ℝ) 1 ∩ (fun u : ℝ ↦ -2 * Real.log u) ⁻¹' Iic x = ∅ := by
      ext u
      constructor
      · rintro ⟨⟨hu0, hu1⟩, hlog⟩
        have hlognonpos : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
        have hstat : 0 ≤ -2 * Real.log u :=
          mul_nonneg_of_nonpos_of_nonpos (by norm_num) hlognonpos
        change -2 * Real.log u ≤ x at hlog
        linarith
      · simp
    rw [inter_comm, hset]
    simp

/-- The sum of the two transformed independent uniforms has the chi square
law with four degrees of freedom. -/
theorem map_fisherSum_fisherUnitUniform :
    Measure.map
        (fun u : ℝ × ℝ ↦ (-2 * Real.log u.1) + (-2 * Real.log u.2))
        (fisherUnitUniformMeasure.prod fisherUnitUniformMeasure) =
      chiSquareMeasure 4 := by
  let f : ℝ → ℝ := fun u ↦ -2 * Real.log u
  calc
    Measure.map (fun u : ℝ × ℝ ↦ f u.1 + f u.2)
        (fisherUnitUniformMeasure.prod fisherUnitUniformMeasure) =
        Measure.map (fun z : ℝ × ℝ ↦ z.1 + z.2)
          ((Measure.map f fisherUnitUniformMeasure).prod
            (Measure.map f fisherUnitUniformMeasure)) := by
      rw [Measure.map_prod_map fisherUnitUniformMeasure fisherUnitUniformMeasure
        (by fun_prop) (by fun_prop)]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (expMeasure (1 / 2)) ∗ (expMeasure (1 / 2)) := by
      rw [map_negTwoLog_fisherUnitUniform]
      rfl
    _ = gammaMeasure 2 (1 / 2) := by
      change gammaMeasure 1 (1 / 2) ∗ gammaMeasure 1 (1 / 2) = _
      convert
        (LogdetLean.gammaMeasure_conv (a := 1) (b := 1) (r := (1 / 2 : ℝ))
          (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num
    _ = chiSquareMeasure 4 := by
      congr 2 <;> norm_num [chiSquareMeasure]

/-- The additive Fisher expression equals `-2 log(U₁U₂)` almost
everywhere under the product unit uniform law. -/
theorem fisherSum_eq_negTwoLogProduct_ae :
    (fun u : ℝ × ℝ ↦ (-2 * Real.log u.1) + (-2 * Real.log u.2)) =ᵐ[
      fisherUnitUniformMeasure.prod fisherUnitUniformMeasure]
      (fun u ↦ -2 * Real.log (u.1 * u.2)) := by
  have hset : MeasurableSet
      {u : ℝ × ℝ | (-2 * Real.log u.1) + (-2 * Real.log u.2) =
        -2 * Real.log (u.1 * u.2)} := by
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae hset).2
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  rw [Real.log_mul hu.1.ne' hv.1.ne']
  ring

/-- **Fisher's exact two component reference law.**  For two independent
unit uniform coordinates, `-2 log(U₁U₂)` has the chi square law with four
degrees of freedom. -/
theorem fisher_two_unitUniform_chiSquareFour :
    Measure.map
        (fun u : ℝ × ℝ ↦ -2 * Real.log (u.1 * u.2))
        (fisherUnitUniformMeasure.prod fisherUnitUniformMeasure) =
      chiSquareMeasure 4 := by
  rw [← Measure.map_congr fisherSum_eq_negTwoLogProduct_ae]
  exact map_fisherSum_fisherUnitUniform

end

end LogdetLean.Coherence
