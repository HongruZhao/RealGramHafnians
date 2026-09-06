import LogdetLean.KolmogorovCLTBridge
import LogdetLean.KolmogorovPerturbation
import LogdetLean.GaussianAntiConcentration
/-!
# Concentration inherited from a Kolmogorov bound

The marked one-edge proof replaces the full standardized log determinant by
an independent deleted tail.  This file records the model-independent
anti-concentration estimate used in that replacement.  A real probability
law within Kolmogorov distance `d` of the standard Gaussian puts at most

`h / sqrt (2*pi) + 2*d`

mass in any interval of length `h`.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- The mass of a right-closed interval is the corresponding CDF increment. -/
theorem measureReal_Ioc_eq_cdf_sub
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {a b : ℝ} (hab : a ≤ b) :
    mu.real (Ioc a b) = cdf mu b - cdf mu a := by
  rw [cdf_eq_real, cdf_eq_real]
  have hsub : Iic a ⊆ Iic b := Iic_subset_Iic.mpr hab
  rw [← measureReal_sdiff hsub measurableSet_Iic]
  congr 1
  ext y
  simp

/-- A Kolmogorov bound against the standard Gaussian yields a uniform
interval anti-concentration bound. -/
theorem measureReal_Ioc_le_length_add_two_kolmogorov
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {a h : ℝ} (hh : 0 ≤ h) :
    mu.real (Ioc a (a + h)) ≤
      h / Real.sqrt (2 * Real.pi) +
        2 * kolmogorovDistance mu (gaussianReal 0 1) := by
  let d := kolmogorovDistance mu (gaussianReal 0 1)
  have hb := LogdetLean.abs_cdf_sub_le_kolmogorovDistance
    mu (gaussianReal 0 1) (a + h)
  have ha := LogdetLean.abs_cdf_sub_le_kolmogorovDistance
    mu (gaussianReal 0 1) a
  have hnormal := LogdetLean.standardGaussian_cdf_increment_le a h hh
  rw [measureReal_Ioc_eq_cdf_sub mu (by linarith)]
  change cdf mu (a + h) - cdf mu a ≤ _
  change |cdf mu (a + h) - cdf (gaussianReal 0 1) (a + h)| ≤ d at hb
  change |cdf mu a - cdf (gaussianReal 0 1) a| ≤ d at ha
  rw [abs_le] at hb ha
  linarith

/-- If a coupled full statistic is close to standard Gaussian and differs
from a deleted statistic by at most `delta` outside an event of mass `q`,
then the deleted statistic inherits an explicit interval concentration
bound. -/
theorem map_measureReal_Ioc_le_of_coupling_and_kolmogorov
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    {X T : Omega → ℝ} (hX : Measurable X) (hT : Measurable T)
    {B delta q a h : ℝ}
    (hdelta : 0 ≤ delta) (hh : 0 ≤ h)
    (hbad : P.real (LogdetLean.couplingBadEvent X T delta) ≤ q)
    (hK : kolmogorovDistance (Measure.map T P) (gaussianReal 0 1) ≤ B) :
    (Measure.map X P).real (Ioc a (a + h)) ≤
      h / Real.sqrt (2 * Real.pi) +
        2 * (B + q + delta / Real.sqrt (2 * Real.pi)) := by
  have hcouple := LogdetLean.kolmogorovDistance_standardGaussian_le_of_coupling
    P hX hT hdelta hbad
  have hprob : IsProbabilityMeasure (Measure.map X P) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hinterval := measureReal_Ioc_le_length_add_two_kolmogorov
    (Measure.map X P) hh (a := a)
  exact hinterval.trans (by nlinarith)

end

end LogdetLean.Coherence
