import Mathlib.MeasureTheory.Measure.LevyConvergence
import LogdetLean.Coherence.WeakCDF
/-!
# Slutsky transport for varying joint laws

The rare matching event changes with the ambient dimension, so the
conditioned random variables need not live on one fixed probability space.
We instead work with their joint laws on the fixed space `ℝ × ℝ`.

The first coordinate below is the fixed-prefix perturbation and the second
is the deleted Bartlett tail.  If the first coordinate concentrates in a
shrinking interval and the second marginal has a Gaussian limit, then the
sum has the same Gaussian limit.  No independence is required for this final
transport step.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A characteristic-function perturbation bound.  On the event
`|x.1| ≤ r`, adding the first coordinate changes the complex exponential by
at most `|t| r`; off this event the universal bound is `2`. -/
theorem norm_charFun_map_add_sub_map_snd_le
    (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (t r : ℝ) (hr : 0 ≤ r) :
    ‖charFun (ρ.map (fun x : ℝ × ℝ ↦ x.1 + x.2)) t -
        charFun (ρ.map Prod.snd) t‖ ≤
      |t| * r +
        2 * ρ.real (((fun x : ℝ × ℝ ↦ x.1) ⁻¹' Icc (-r) r)ᶜ) := by
  let f : ℝ × ℝ → ℂ := fun x ↦
    Complex.exp ((t : ℂ) * ((x.1 + x.2 : ℝ) : ℂ) * Complex.I) -
      Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I)
  have hf : Integrable f ρ := by
    refine (integrable_const (2 : ℂ)).mono (by fun_prop) ?_
    filter_upwards [] with x
    dsimp [f]
    calc
      ‖Complex.exp ((t : ℂ) * ((x.1 + x.2 : ℝ) : ℂ) * Complex.I) -
          Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I)‖ ≤
          ‖Complex.exp ((t : ℂ) * ((x.1 + x.2 : ℝ) : ℂ) * Complex.I)‖ +
            ‖Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]
        norm_num
      _ = ‖(2 : ℂ)‖ := by norm_num
  let good : Set (ℝ × ℝ) :=
    (fun x : ℝ × ℝ ↦ x.1) ⁻¹' Icc (-r) r
  have hgoodMeas : MeasurableSet good :=
    measurableSet_Icc.preimage measurable_fst
  have hfiniteGood : ρ good < ∞ := measure_lt_top ρ _
  have hfiniteBad : ρ goodᶜ < ∞ := measure_lt_top ρ _
  have hgood : ‖∫ x in good, f x ∂ρ‖ ≤
      (|t| * r) * ρ.real good := by
    apply norm_setIntegral_le_of_norm_le_const hfiniteGood
    intro x hx
    have hxr : |x.1| ≤ r := by
      rw [abs_le]
      exact hx
    have hsmall := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * x.1)
    have hexp :
        Complex.exp ((t : ℂ) * ((x.1 + x.2 : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I) *
            Complex.exp ((t : ℂ) * (x.1 : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      ‖f x‖ =
          ‖Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I) *
            (Complex.exp ((t : ℂ) * (x.1 : ℂ) * Complex.I) - 1)‖ := by
        dsimp [f]
        rw [hexp]
        congr 1
        ring
      _ = ‖Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I)‖ *
          ‖Complex.exp ((t : ℂ) * (x.1 : ℂ) * Complex.I) - 1‖ :=
        norm_mul _ _
      _ = ‖Complex.exp ((t : ℂ) * (x.1 : ℂ) * Complex.I) - 1‖ := by
        rw [Complex.norm_exp]
        norm_num
      _ ≤ |t * x.1| := by
        simpa [mul_assoc, mul_comm, mul_left_comm, Real.norm_eq_abs] using hsmall
      _ = |t| * |x.1| := abs_mul _ _
      _ ≤ |t| * r := mul_le_mul_of_nonneg_left hxr (abs_nonneg t)
  have hbad : ‖∫ x in goodᶜ, f x ∂ρ‖ ≤
      2 * ρ.real goodᶜ := by
    apply norm_setIntegral_le_of_norm_le_const hfiniteBad
    intro x hx
    dsimp [f]
    calc
      ‖Complex.exp ((t : ℂ) * ((x.1 + x.2 : ℝ) : ℂ) * Complex.I) -
          Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I)‖ ≤
          ‖Complex.exp ((t : ℂ) * ((x.1 + x.2 : ℝ) : ℂ) * Complex.I)‖ +
            ‖Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]
        norm_num
  have hmass : ρ.real good ≤ 1 := by
    simpa using measureReal_le_one
  rw [charFun_apply_real]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [charFun_apply_real]
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hrepr :
      (∫ x : ℝ × ℝ,
          Complex.exp ((t : ℂ) * ((x.1 + x.2 : ℝ) : ℂ) * Complex.I) ∂ρ) -
        ∫ x : ℝ × ℝ,
          Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I) ∂ρ =
        ∫ x : ℝ × ℝ, f x ∂ρ := by
    have hsumInt : Integrable (fun x : ℝ × ℝ ↦
        Complex.exp ((t : ℂ) * ((x.1 + x.2 : ℝ) : ℂ) * Complex.I)) ρ := by
      refine (integrable_const (1 : ℂ)).mono (by fun_prop) ?_
      filter_upwards [] with x
      rw [Complex.norm_exp]
      simp
    have hsndInt : Integrable (fun x : ℝ × ℝ ↦
        Complex.exp ((t : ℂ) * (x.2 : ℂ) * Complex.I)) ρ := by
      refine (integrable_const (1 : ℂ)).mono (by fun_prop) ?_
      filter_upwards [] with x
      rw [Complex.norm_exp]
      simp
    rw [← integral_sub hsumInt hsndInt]
  rw [hrepr, ← integral_add_compl hgoodMeas hf]
  calc
    ‖(∫ x in good, f x ∂ρ) + ∫ x in goodᶜ, f x ∂ρ‖ ≤
        ‖∫ x in good, f x ∂ρ‖ + ‖∫ x in goodᶜ, f x ∂ρ‖ :=
      norm_add_le _ _
    _ ≤ (|t| * r) * ρ.real good + 2 * ρ.real goodᶜ :=
      add_le_add hgood hbad
    _ ≤ |t| * r + 2 * ρ.real goodᶜ := by
      apply add_le_add
      · calc
          (|t| * r) * ρ.real good ≤ (|t| * r) * 1 :=
            mul_le_mul_of_nonneg_left hmass
              (mul_nonneg (abs_nonneg t) hr)
          _ = |t| * r := by ring
      · exact le_rfl

/-- A varying family of joint laws whose first coordinate vanishes and whose
second marginal has a Gaussian limit has an asymptotically Gaussian sum. -/
theorem tendsto_probabilityMeasure_map_add_of_first_shrinks
    (ρ : ℕ → ProbabilityMeasure (ℝ × ℝ)) (r : ℕ → ℝ)
    (hr : ∀ᶠ n in atTop, 0 ≤ r n)
    (hr0 : Tendsto r atTop (nhds 0))
    (hbad : Tendsto
      (fun n ↦ (ρ n : Measure (ℝ × ℝ)).real
        (((fun x : ℝ × ℝ ↦ x.1) ⁻¹' Icc (-(r n)) (r n))ᶜ))
      atTop (nhds 0))
    (htail : Tendsto
      (fun n ↦ (ρ n).map measurable_snd.aemeasurable)
      atTop
      (nhds (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) :
    Tendsto
      (fun n ↦ (ρ n).map
        (measurable_fst.add measurable_snd).aemeasurable)
      atTop
      (nhds (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have htailCF :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp htail) t
  have hupper : Tendsto
      (fun n ↦ |t| * r n + 2 * (ρ n : Measure (ℝ × ℝ)).real
        (((fun x : ℝ × ℝ ↦ x.1) ⁻¹' Icc (-(r n)) (r n))ᶜ))
      atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hr0).add
      (tendsto_const_nhds.mul hbad) using 1 <;> simp
  have hnorm : Tendsto
      (fun n ↦ ‖charFun
          ((ρ n).map (measurable_fst.add measurable_snd).aemeasurable :
            Measure ℝ) t -
        charFun ((ρ n).map measurable_snd.aemeasurable : Measure ℝ) t‖)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ norm_nonneg _
    · filter_upwards [hr] with n hrn
      exact norm_charFun_map_add_sub_map_snd_le (ρ n : Measure (ℝ × ℝ))
        t (r n) hrn
    · exact hupper
  have hdiff : Tendsto
      (fun n ↦ charFun
          ((ρ n).map (measurable_fst.add measurable_snd).aemeasurable :
            Measure ℝ) t -
        charFun ((ρ n).map measurable_snd.aemeasurable : Measure ℝ) t)
      atTop (nhds 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hadd := hdiff.add htailCF
  convert hadd using 1
  · funext n
    ring
  · simp

/-- CDF form of `tendsto_probabilityMeasure_map_add_of_first_shrinks`. -/
theorem tendsto_map_add_CDF_of_first_shrinks
    (ρ : ℕ → ProbabilityMeasure (ℝ × ℝ)) (r : ℕ → ℝ)
    (hr : ∀ᶠ n in atTop, 0 ≤ r n)
    (hr0 : Tendsto r atTop (nhds 0))
    (hbad : Tendsto
      (fun n ↦ (ρ n : Measure (ℝ × ℝ)).real
        (((fun x : ℝ × ℝ ↦ x.1) ⁻¹' Icc (-(r n)) (r n))ᶜ))
      atTop (nhds 0))
    (htail : Tendsto
      (fun n ↦ (ρ n).map measurable_snd.aemeasurable)
      atTop
      (nhds (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)))
    (z : ℝ) :
    Tendsto
      (fun n ↦
        (((ρ n).map
          (measurable_fst.add measurable_snd).aemeasurable :
            ProbabilityMeasure ℝ) : Measure ℝ).real (Iic z))
      atTop (nhds (standardNormalCDF z)) :=
  tendsto_measureReal_Iic_standardGaussian_of_weak
    (tendsto_probabilityMeasure_map_add_of_first_shrinks
      ρ r hr hr0 hbad htail) z

end

end LogdetLean.Coherence
