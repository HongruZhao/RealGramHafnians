import LogdetLean.NullLocalCharacteristic
import LogdetLean.NullCenterStandardization
/-!
# Nonvacuous weak null CLT for the actual sample statistic

`Admissible m p` includes `2 ≤ p`, so it cannot hold for every natural
index `p`.  This file packages the finitely many irrelevant initial indices
with a standard-Gaussian default.  The resulting theorem assumes only
*eventual* admissibility and is therefore the faithful triangular-array CLT.

It is the qualitative null statement in Zhao (2026), Lemma 5.5 / Appendix
Lemma D.1, but the Lean proof uses the stronger exact characteristic-function
package developed here.  The Beta factorization used upstream is credited to
Rouault (2007), Proposition 2.1(2), pp. 185--187; see the module provenance
ledgers for the full proof relation.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- A total measure version of the standardized null law. -/
def standardizedNullMeasureOrGaussian (m p : ℕ) : Measure ℝ := by
  classical
  exact if Admissible m p then standardizedNullLaw m p
    else gaussianReal 0 1

theorem standardizedNullMeasureOrGaussian_isProbability (m p : ℕ) :
    IsProbabilityMeasure (standardizedNullMeasureOrGaussian m p) := by
  classical
  unfold standardizedNullMeasureOrGaussian
  by_cases h : Admissible m p
  · rw [if_pos h]
    exact isProbabilityMeasure_standardizedNullLaw h.2
  · rw [if_neg h]
    infer_instance

/-- A total probability-measure version of the standardized null law.  The
fallback affects only indices outside the theorem's eventual admissible set. -/
def standardizedNullProbabilityMeasureOrGaussian (m p : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨standardizedNullMeasureOrGaussian m p,
    standardizedNullMeasureOrGaussian_isProbability m p⟩

/-- The total measure formed from the actual Gaussian sample statistic. -/
def actualZ0mpMeasureOrGaussian (m p : ℕ) : Measure ℝ := by
  classical
  exact if Admissible m p then
      Measure.map (Z0mpStatistic m p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p)
    else gaussianReal 0 1

theorem actualZ0mpMeasureOrGaussian_isProbability (m p : ℕ) :
    IsProbabilityMeasure (actualZ0mpMeasureOrGaussian m p) := by
  classical
  unfold actualZ0mpMeasureOrGaussian
  by_cases h : Admissible m p
  · rw [if_pos h, map_Z0mpStatistic_eq_standardizedNullLaw m p h.2]
    exact isProbabilityMeasure_standardizedNullLaw h.2
  · rw [if_neg h]
    infer_instance

/-- Probability-measure wrapper for the actual statistic. -/
def actualZ0mpProbabilityMeasureOrGaussian (m p : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨actualZ0mpMeasureOrGaussian m p,
    actualZ0mpMeasureOrGaussian_isProbability m p⟩

theorem actualZ0mpProbabilityMeasureOrGaussian_eq_standardized
    (m p : ℕ) :
    actualZ0mpProbabilityMeasureOrGaussian m p =
      standardizedNullProbabilityMeasureOrGaussian m p := by
  classical
  apply Subtype.ext
  change actualZ0mpMeasureOrGaussian m p =
    standardizedNullMeasureOrGaussian m p
  classical
  unfold actualZ0mpMeasureOrGaussian standardizedNullMeasureOrGaussian
  by_cases h : Admissible m p
  · rw [if_pos h, if_pos h]
    exact map_Z0mpStatistic_eq_standardizedNullLaw m p h.2
  · rw [if_neg h, if_neg h]

/-- Weak convergence of the exact standardized null law under the sole
asymptotic assumption `2 ≤ p ≤ m(p)` eventually. -/
theorem tendsto_standardizedNullProbabilityMeasureOrGaussian
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto
      (fun p ↦ standardizedNullProbabilityMeasureOrGaussian (m p) p)
      atTop (nhds (⟨gaussianReal 0 1, inferInstance⟩ :
        ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hcf := tendsto_charFun_standardizedNullLaw_fixed_frequency m hadm t
  change Tendsto
    (fun p ↦ charFun
      (standardizedNullProbabilityMeasureOrGaussian (m p) p : Measure ℝ) t)
    atTop (nhds (charFun (gaussianReal 0 1) t))
  have hgauss : charFun (gaussianReal 0 1) t =
      Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [charFun_gaussianReal]
    congr 1
    push_cast
    ring
  rw [hgauss]
  apply hcf.congr'
  filter_upwards [hadm] with p hp
  change charFun (standardizedNullLaw (m p) p) t =
    charFun (standardizedNullMeasureOrGaussian (m p) p) t
  rw [standardizedNullMeasureOrGaussian, if_pos hp]

/-- Faithful actual-statistic form of the null CLT.  This is the theorem that
should be cited as the Lean formulation of the old paper's null CLT. -/
theorem tendsto_actual_Z0mp_gaussian
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto
      (fun p ↦ actualZ0mpProbabilityMeasureOrGaussian (m p) p)
      atTop (nhds (⟨gaussianReal 0 1, inferInstance⟩ :
        ProbabilityMeasure ℝ)) := by
  have h := tendsto_standardizedNullProbabilityMeasureOrGaussian m hadm
  apply h.congr'
  exact Eventually.of_forall fun p ↦
    (actualZ0mpProbabilityMeasureOrGaussian_eq_standardized (m p) p).symm

end
end LogdetLean
