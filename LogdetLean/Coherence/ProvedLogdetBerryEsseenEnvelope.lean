import LogdetLean.Coherence.QuantitativeJointBerryEsseen
import LogdetLean.NullUniformEdgeworthTarget
/-!
# A proved finite null log-determinant Berry--Esseen envelope

The sharp signed scale alone is an asymptotic equivalent and should not be
silently used as a finite upper bound.  This file packages the finite
inequality already proved in `NullUniformEdgeworthTarget` into an honest
nonnegative envelope.  It will be one summand in the quantitative joint
normal--coherence theorem.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Real

/-- A finite, explicit upper envelope for the null log-determinant
Kolmogorov distance.  The first term is the sharp signed-cumulant scale and
the second is the already verified finite Fourier/Edgeworth remainder. -/
def provedNullLogdetKolmogorovEnvelope (m p : ℕ) : ℝ :=
  |nullLambdaSeries m p / (6 * Real.sqrt (2 * Real.pi))| +
    |nullLambdaSeries m p * nullUniformEdgeworthRelativeRemainder m p|

theorem provedNullLogdetKolmogorovEnvelope_nonneg (m p : ℕ) :
    0 ≤ provedNullLogdetKolmogorovEnvelope m p := by
  unfold provedNullLogdetKolmogorovEnvelope
  positivity

/-- On every admissible finite index, the actual standardized null law is
bounded by `provedNullLogdetKolmogorovEnvelope`. -/
theorem kolmogorovDistance_standardizedNullLaw_le_provedEnvelope
    {m p : ℕ} (h : Admissible m p) :
    kolmogorovDistance (standardizedNullLaw m p) (gaussianReal 0 1) ≤
      provedNullLogdetKolmogorovEnvelope m p := by
  have hfinite := uniformNullSharpKolmogorov_finite h
  unfold provedNullLogdetKolmogorovEnvelope
  have hdnonneg : 0 ≤
      kolmogorovDistance (standardizedNullLaw m p) (gaussianReal 0 1) :=
    kolmogorovDistance_nonneg _ _
  let d : ℝ :=
    kolmogorovDistance (standardizedNullLaw m p) (gaussianReal 0 1)
  let a : ℝ := nullLambdaSeries m p / (6 * Real.sqrt (2 * Real.pi))
  let r : ℝ :=
    nullLambdaSeries m p * nullUniformEdgeworthRelativeRemainder m p
  have herr : |d - a| ≤ |r| := by
    exact hfinite.trans (le_abs_self r)
  change d ≤ |a| + |r|
  calc
    d = |d| := (abs_of_nonneg hdnonneg).symm
    _ = |(d - a) + a| := by ring_nf
    _ ≤ |d - a| + |a| := abs_add_le _ _
    _ ≤ |r| + |a| := add_le_add herr le_rfl
    _ = |a| + |r| := add_comm _ _

/-- The same proved finite bound for the concrete Gaussian statistic. -/
theorem kolmogorovDistance_actualZ0mp_le_provedEnvelope
    {m p : ℕ} (h : Admissible m p) :
    kolmogorovDistance
        (Measure.map (Z0mpStatistic m p)
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) p))
        (gaussianReal 0 1) ≤
      provedNullLogdetKolmogorovEnvelope m p := by
  rw [map_Z0mpStatistic_eq_standardizedNullLaw m p h.2]
  exact kolmogorovDistance_standardizedNullLaw_le_provedEnvelope h

end

end LogdetLean.Coherence
