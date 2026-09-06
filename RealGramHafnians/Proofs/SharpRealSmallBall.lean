import RealGramHafnians.Proofs.RowSuspensionIteration
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealSecondMoment
/-!
# Sharp shifted anticoncentration for real Gaussian Gram hafnians
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 5000000

/-- Literal real small-ball estimate in terms of the negative-half moment
of the physical cofactor energy. -/
theorem standardRealGaussianColumnMatrix_shiftedSmallBall_le_inverseSqrtMoment
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k), 0 < pastRealCofactorV hr A)
    (z rho : ℝ) (hrho : 0 ≤ rho) :
    (standardRealGaussianColumnMatrixMeasure r k)
        {X | |realGramHafnianObservable r k X - z| ≤ rho} ≤
      ENNReal.ofReal (realGaussianIntervalPrefactor rho) *
        sharpRealCofactorInverseSqrtMoment r k hr := by
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let e := realLastColumnProductEquiv r k hr
  let target : Set (RealColumnMatrix r k) :=
    {X | |realGramHafnianObservable r k X - z| ≤ rho}
  let source : Set
      ((OddCofactorIndex r hr → (Fin k → ℝ)) × (Fin k → ℝ)) :=
    {p | |conditionalRealLinearForm (pastRealCofactorCombination hr) p - z| ≤ rho}
  have htarget : MeasurableSet target := by
    dsimp [target]
    exact measurableSet_le
      ((measurable_realGramHafnianObservable r k).sub_const z).abs
        measurable_const
  have hpre : e ⁻¹' target = source := by
    ext p
    simp only [Set.mem_preimage]
    change (|realGramHafnianObservable r k (e p) - z| ≤ rho) ↔
      |conditionalRealLinearForm (pastRealCofactorCombination hr) p - z| ≤ rho
    rw [realGramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm]
  have hmap := (measurePreserving_realLastColumnProductEquiv r k hr).map_eq
  rw [← hmap, Measure.map_apply e.measurable htarget, hpre]
  have hconditional :=
    prod_pi_realGaussian_shiftedSmallBall_le_inverseSqrtMoment
      nu (pastRealCofactorCombination hr)
      (measurable_pastRealCofactorCombination hr)
      (by
        filter_upwards [show ∀ᵐ A ∂nu, 0 < pastRealCofactorV hr A by
          simpa [nu] using hVpos] with A hA
        simpa [conditionalRealEnergy,
          pastRealCofactorV_eq_realCoefficientEnergy] using hA)
      z rho hrho
  have henergy :
      (conditionalRealEnergy (pastRealCofactorCombination hr) :
        (OddCofactorIndex r hr → (Fin k → ℝ)) → ℝ) =
      (pastRealCofactorV hr :
        (OddCofactorIndex r hr → (Fin k → ℝ)) → ℝ) := by
    funext A
    exact (pastRealCofactorV_eq_realCoefficientEnergy hr A).symm
  rw [henergy] at hconditional
  simpa [nu, source, standardRealGaussianVectorMeasure,
    sharpRealCofactorInverseSqrtMoment] using hconditional

/-- Exact normalized ENNReal coefficient. -/
def sharpRealNormalizedCoefficient (n k : ℕ) : ENNReal :=
  ENNReal.ofReal (realGaussianIntervalPrefactor (realGramHafnianRMS n k)) *
    sharpRealGammaCoefficient n k

/-- Exact finite shifted-anticoncentration theorem at RMS scale. -/
theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      sharpRealNormalizedCoefficient n k * ENNReal.ofReal epsilon := by
  have hV := ae_pastRealCofactorV_pos_standardRealGaussian hn hdim
  have hrms := realGramHafnianRMS_nonneg n k
  have hsmall :=
    standardRealGaussianColumnMatrix_shiftedSmallBall_le_inverseSqrtMoment
      hn hV z (epsilon * realGramHafnianRMS n k) (mul_nonneg hepsilon hrms)
  have hmoment :=
    sharpRealCofactorInverseSqrtMoment_le_coefficient hn hk hdim
  calc
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      ENNReal.ofReal
          (realGaussianIntervalPrefactor
            (epsilon * realGramHafnianRMS n k)) *
        sharpRealCofactorInverseSqrtMoment n k hn := hsmall
    _ ≤ ENNReal.ofReal
          (realGaussianIntervalPrefactor
            (epsilon * realGramHafnianRMS n k)) *
        sharpRealGammaCoefficient n k := by gcongr
    _ = sharpRealNormalizedCoefficient n k * ENNReal.ofReal epsilon := by
      have hpref : realGaussianIntervalPrefactor
          (epsilon * realGramHafnianRMS n k) =
          epsilon * realGaussianIntervalPrefactor (realGramHafnianRMS n k) := by
        unfold realGaussianIntervalPrefactor
        ring
      rw [hpref, ENNReal.ofReal_mul hepsilon]
      unfold sharpRealNormalizedCoefficient
      ac_rfl

end

end LogdetLean.GramHafnian
