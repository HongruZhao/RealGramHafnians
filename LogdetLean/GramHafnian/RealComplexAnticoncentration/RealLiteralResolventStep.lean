import LogdetLean.GramHafnian.RealComplexAnticoncentration.ExactAuxiliaryGammaRecurrence
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralFourierStep
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealTransposeGramGood
/-!
# One exact literal beta-one resolvent step

This module combines three fully internal ingredients at one hafnian level:

* the entrywise transpose-Gram good event;
* literal real cofactor Fourier compression;
* exact integration of the independent chi-square radius.

The result propagates an affine `sqrt lambda` envelope without thresholding
the auxiliary radius.  Its only additive cost is the complement probability
of the matrix good event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Half-resolvent of the literal real conditional cofactor energy at level
`r`. -/
def pastRealCofactorHalfResolvent (r k : ℕ) (hr : 1 ≤ r)
    (lambda : ℝ) : ENNReal :=
  ennHalfResolvent
    (Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k)
    (pastRealCofactorV hr) lambda

/-- Probability of failure of the literal entrywise transpose-Gram event at
level `r`. -/
def pastRealCofactorGramBadProbability (r k : ℕ) (hr : 1 ≤ r)
    (delta : ℝ) : ENNReal :=
  (Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k)
    {A | ¬ realTransposeGramGood k delta A}

/-- Deterministic coefficient acquired at level `r`: inverse square root of
the Gram lower-bound scale times the exact chi-square negative-half moment. -/
def pastRealCofactorLevelHalfFactor (r k : ℕ) (delta : ℝ) : ENNReal :=
  ENNReal.ofReal
      (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ *
    realAuxiliaryGammaHalfFactor (2 * r - 1)

/-- Exact one-level propagation of an affine square-root envelope.  This is
the literal beta-one recursion used by the finite theorem. -/
theorem pastRealCofactorHalfResolvent_le_of_lower_sqrt_envelope
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r)
    (hk : 0 < k) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdeltalt : delta < 1)
    (E C : ENNReal)
    (henvelope : ∀ t : ℝ, 0 < t →
      pastRealCofactorHalfResolvent (r - 1) k (by omega) t ≤
        E + C * ENNReal.ofReal (Real.sqrt t))
    (lambda : ℝ) (hlambda : 0 < lambda) :
    pastRealCofactorHalfResolvent r k hr lambda ≤
      (E + pastRealCofactorGramBadProbability r k hr delta) +
        (C * pastRealCofactorLevelHalfFactor r k delta) *
          ENNReal.ofReal (Real.sqrt lambda) := by
  let mu : Measure (OddCofactorIndex r hr → Fin k → ℝ) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let nu : Measure (OddCofactorIndex (r - 1) (by omega) → Fin k → ℝ) :=
    Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
      standardRealGaussianVectorMeasure k
  let good : Set (OddCofactorIndex r hr → Fin k → ℝ) :=
    {A | realTransposeGramGood k delta A}
  let tau : ℝ := (k : ℝ) * (1 - delta)
  have htau : 0 < tau := by
    dsimp [tau]
    exact mul_pos (by exact_mod_cast hk) (sub_pos.mpr hdeltalt)
  have hsplit :
      ennHalfResolvent mu (pastRealCofactorV hr) lambda ≤
        ennHalfResolvent mu (pastRealCofactorW hr) (lambda / tau) +
          mu goodᶜ := by
    apply ennHalfResolvent_le_rescaled_add_compl
      mu (pastRealCofactorV hr) (pastRealCofactorW hr)
      (measurable_pastRealCofactorV hr)
      (measurable_pastRealCofactorW hr)
      good
      (by
        dsimp [good]
        exact measurableSet_realTransposeGramGood k delta)
      (Filter.Eventually.of_forall (pastRealCofactorV_nonneg hr))
      (Filter.Eventually.of_forall (pastRealCofactorW_nonneg hr))
      tau lambda htau hlambda
    filter_upwards [] with A hA
    dsimp [good, tau] at hA ⊢
    exact pastRealCofactorV_ge_mul_pastRealCofactorW_of_good
      hr hdelta A hA
  have hfourier :
      ennHalfResolvent mu (pastRealCofactorW hr) (lambda / tau) ≤
        ennHalfResolvent
          (nu.prod (stdGaussian
            (RealGaussianEuclideanSpace (2 * r - 1))))
          (fun p ↦ pastRealCofactorV (by omega) p.1 *
            realAuxiliaryNormSq p.2) (lambda / tau) := by
    simpa [mu, nu] using
      ennHalfResolvent_pastRealCofactorW_le_product
        hr hr2 (lambda / tau) (div_pos hlambda htau)
  have hgamma :
      ennHalfResolvent
          (nu.prod (stdGaussian
            (RealGaussianEuclideanSpace (2 * r - 1))))
          (fun p ↦ pastRealCofactorV (by omega) p.1 *
            realAuxiliaryNormSq p.2) (lambda / tau) ≤
        E + C * ENNReal.ofReal (Real.sqrt (lambda / tau)) *
          realAuxiliaryGammaHalfFactor (2 * r - 1) := by
    apply ennHalfResolvent_mul_realAuxiliaryNormSq_le_of_sqrt_envelope
      (d := 2 * r - 1) (by omega) nu
      (pastRealCofactorV (by omega))
      (measurable_pastRealCofactorV (by omega))
      (pastRealCofactorV_nonneg (by omega)) E C
    · simpa [pastRealCofactorHalfResolvent, nu] using henvelope
    · exact div_pos hlambda htau
  have hscale :
      ENNReal.ofReal (Real.sqrt (lambda / tau)) =
        ENNReal.ofReal (Real.sqrt lambda) *
          ENNReal.ofReal (Real.sqrt tau)⁻¹ :=
    ennreal_ofReal_sqrt_div hlambda htau
  calc
    pastRealCofactorHalfResolvent r k hr lambda =
        ennHalfResolvent mu (pastRealCofactorV hr) lambda := by
      rfl
    _ ≤ ennHalfResolvent mu (pastRealCofactorW hr) (lambda / tau) +
          mu goodᶜ := hsplit
    _ ≤ ennHalfResolvent
          (nu.prod (stdGaussian
            (RealGaussianEuclideanSpace (2 * r - 1))))
          (fun p ↦ pastRealCofactorV (by omega) p.1 *
            realAuxiliaryNormSq p.2) (lambda / tau) +
          mu goodᶜ := add_le_add hfourier le_rfl
    _ ≤ (E + C * ENNReal.ofReal (Real.sqrt (lambda / tau)) *
          realAuxiliaryGammaHalfFactor (2 * r - 1)) +
          mu goodᶜ := add_le_add hgamma le_rfl
    _ = (E + pastRealCofactorGramBadProbability r k hr delta) +
        (C * pastRealCofactorLevelHalfFactor r k delta) *
          ENNReal.ofReal (Real.sqrt lambda) := by
      rw [hscale]
      unfold pastRealCofactorGramBadProbability
        pastRealCofactorLevelHalfFactor
      dsimp [mu, good, tau]
      -- The remaining equality is only associativity and commutativity.
      ac_rfl

end

end LogdetLean.GramHafnian
