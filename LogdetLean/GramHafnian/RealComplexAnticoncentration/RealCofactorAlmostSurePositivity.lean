import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGaussianFullRank
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralCofactorLaw
/-!
# Almost-sure positivity of the literal real cofactor energy

The proof is a simultaneous induction.  Full real column rank turns a
nonzero cofactor vector into positive energy.  A canonical cofactor is the
lower-level Gram hafnian, while conditioning on the fresh last Gaussian
column shows that positive energy makes that Gram hafnian nonzero almost
surely.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The finite real linear combination of the past columns is exactly the
literal cofactor combination. -/
theorem sum_smul_pastRealColumns_eq_pastRealCofactorCombination
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → Fin k → ℝ) :
    (∑ j : OddCofactorIndex r hr,
        pastRealHafnianCofactorVector hr A j •
          (WithLp.toLp 2 (A j) : RealCofactorSpace k)) =
      WithLp.toLp 2 (pastRealCofactorCombination hr A) := by
  apply (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).injective
  simp only [map_sum, map_smul, WithLp.coe_linearEquiv,
    WithLp.ofLp_toLp]
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold pastRealCofactorCombination realOddCofactorColumnCombination
    pastRealHafnianCofactorVector
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show pastRealCofactorMatrix hr A j.1 = A j by
    unfold pastRealCofactorMatrix
    exact realLastColumnProductEquiv_apply_nonlast hr (A, 0) j]
  exact mul_comm _ _

/-- Full rank makes the past-column map injective on the real cofactor
vector. -/
theorem pastRealCofactorCombination_ne_zero_of_linearIndependent
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → Fin k → ℝ)
    (hLI : LinearIndependent ℝ
      (fun j : OddCofactorIndex r hr ↦
        (WithLp.toLp 2 (A j) : RealCofactorSpace k)))
    (hC : pastRealHafnianCofactorVector hr A ≠ 0) :
    pastRealCofactorCombination hr A ≠ 0 := by
  intro hzero
  have hsum : (∑ j : OddCofactorIndex r hr,
      pastRealHafnianCofactorVector hr A j •
        (WithLp.toLp 2 (A j) : RealCofactorSpace k)) = 0 := by
    rw [sum_smul_pastRealColumns_eq_pastRealCofactorCombination hr A,
      hzero]
    rfl
  have hall := (Fintype.linearIndependent_iff.mp hLI)
    (pastRealHafnianCofactorVector hr A) hsum
  apply hC
  funext j
  exact hall j

/-- Deterministic positivity of the literal real past energy under full
rank and a nonzero cofactor vector. -/
theorem pastRealCofactorV_pos_of_linearIndependent_of_cofactor_ne_zero
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → Fin k → ℝ)
    (hLI : LinearIndependent ℝ
      (fun j : OddCofactorIndex r hr ↦
        (WithLp.toLp 2 (A j) : RealCofactorSpace k)))
    (hC : pastRealHafnianCofactorVector hr A ≠ 0) :
    0 < pastRealCofactorV hr A := by
  rw [pastRealCofactorV_eq_realCoefficientEnergy]
  unfold realCoefficientEnergy
  have hraw :=
    pastRealCofactorCombination_ne_zero_of_linearIndependent hr A hLI hC
  have hlp : (WithLp.toLp 2 (pastRealCofactorCombination hr A) :
      RealCofactorSpace k) ≠ 0 := by
    exact (WithLp.toLp_eq_zero 2).not.mpr hraw
  have hnorm : 0 < ‖(WithLp.toLp 2
      (pastRealCofactorCombination hr A) : RealCofactorSpace k)‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hlp)
  simpa [EuclideanSpace.real_norm_sq_eq] using hnorm

/-- The unique level-one cofactor is deterministically nonzero. -/
theorem pastRealHafnianCofactorVector_ne_zero_level_one
    {k : ℕ} (A : OddCofactorIndex 1 (by omega) → Fin k → ℝ) :
    pastRealHafnianCofactorVector (by omega) A ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero default
  unfold pastRealHafnianCofactorVector at hcoord
  rw [realOddHafnianCofactorVector_level_one] at hcoord
  norm_num at hcoord

/-- The canonical first past cofactor is the lower-level real Gram
hafnian. -/
theorem pastRealFirstCofactor_eq_realGramHafnian_canonicalPastSubmatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → Fin k → ℝ) :
    pastRealHafnianCofactorVector hr A (oddFirstCofactorIndex r hr) =
      realGramHafnianObservable (r - 1) k
        (realCanonicalPastCofactorSubmatrix hr A) := by
  exact realOddFirstCofactor_eq_realGramHafnian_canonicalSubmatrix
    hr (pastRealCofactorMatrix hr A)

/-- Pulling back lower-level nonvanishing along the canonical iid Gaussian
submatrix makes the current cofactor vector nonzero almost surely. -/
theorem ae_pastRealCofactorVector_ne_zero_of_ae_lower_realGramHafnian_ne_zero
    {r k : ℕ} (hr : 1 ≤ r) (_hr2 : 2 ≤ r)
    (hlower :
      ∀ᵐ X ∂(standardRealGaussianColumnMatrixMeasure (r - 1) k),
        realGramHafnianObservable (r - 1) k X ≠ 0) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        standardRealGaussianVectorMeasure k),
      pastRealHafnianCofactorVector hr A ≠ 0 := by
  let nu : Measure (OddCofactorIndex r hr → Fin k → ℝ) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let f := realCanonicalPastCofactorSubmatrix (k := k) hr
  have hmp : MeasurePreserving f nu
      (standardRealGaussianColumnMatrixMeasure (r - 1) k) := by
    refine ⟨measurable_realCanonicalPastCofactorSubmatrix hr, ?_⟩
    simpa [nu, f] using map_realCanonicalPastCofactorSubmatrix r k hr
  have hpull : ∀ᵐ A ∂nu,
      realGramHafnianObservable (r - 1) k (f A) ≠ 0 :=
    hmp.quasiMeasurePreserving.ae hlower
  filter_upwards [hpull] with A hA
  intro hzero
  have hcoord := congrFun hzero (oddFirstCofactorIndex r hr)
  rw [pastRealFirstCofactor_eq_realGramHafnian_canonicalPastSubmatrix]
    at hcoord
  exact hA hcoord

/-- A positive random coefficient energy makes the conditionally Gaussian
real linear form avoid every fixed point almost surely. -/
theorem ae_conditionalRealLinearForm_ne_const_of_ae_energy_pos
    {Omega : Type*} [MeasurableSpace Omega]
    {k : ℕ} (nu : Measure Omega) [IsProbabilityMeasure nu]
    (y : Omega → Fin k → ℝ) (hy : Measurable y)
    (henergy : ∀ᵐ w ∂nu, 0 < conditionalRealEnergy y w) (z : ℝ) :
    ∀ᵐ p ∂(nu.prod (standardRealGaussianVectorMeasure k)),
      conditionalRealLinearForm y p ≠ z := by
  have hbound :=
    prod_pi_realGaussian_shiftedSmallBall_le_inverseSqrtMoment
      nu y hy henergy z 0 (by norm_num)
  have hzero :
      (nu.prod (standardRealGaussianVectorMeasure k))
        {p | |conditionalRealLinearForm y p - z| ≤ 0} = 0 := by
    apply nonpos_iff_eq_zero.mp
    simpa [standardRealGaussianVectorMeasure,
      realGaussianIntervalPrefactor] using hbound
  rw [ae_iff]
  simpa [sub_eq_zero] using hzero

/-- Zero-specialization used in the nonvanishing induction. -/
theorem ae_conditionalRealLinearForm_ne_zero_of_ae_energy_pos
    {Omega : Type*} [MeasurableSpace Omega]
    {k : ℕ} (nu : Measure Omega) [IsProbabilityMeasure nu]
    (y : Omega → Fin k → ℝ) (hy : Measurable y)
    (henergy : ∀ᵐ w ∂nu, 0 < conditionalRealEnergy y w) :
    ∀ᵐ p ∂(nu.prod (standardRealGaussianVectorMeasure k)),
      conditionalRealLinearForm y p ≠ 0 :=
  ae_conditionalRealLinearForm_ne_const_of_ae_energy_pos
    nu y hy henergy 0

/-- Positive past energy and the fresh final standard real Gaussian column
make the full literal real Gram hafnian avoid every fixed point almost
surely. -/
theorem ae_realGramHafnian_ne_const_of_ae_pastRealCofactorV_pos
    {r k : ℕ} (hr : 1 ≤ r)
    (hV : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k), 0 < pastRealCofactorV hr A)
    (z : ℝ) :
    ∀ᵐ X ∂(standardRealGaussianColumnMatrixMeasure r k),
      realGramHafnianObservable r k X ≠ z := by
  let nu : Measure (OddCofactorIndex r hr → Fin k → ℝ) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let mu : Measure (Fin k → ℝ) := standardRealGaussianVectorMeasure k
  let e := realLastColumnProductEquiv r k hr
  have henergy : ∀ᵐ A ∂nu,
      0 < conditionalRealEnergy (pastRealCofactorCombination hr) A := by
    filter_upwards [show ∀ᵐ A ∂nu, 0 < pastRealCofactorV hr A by
      simpa [nu] using hV] with A hA
    simpa [conditionalRealEnergy,
      pastRealCofactorV_eq_realCoefficientEnergy] using hA
  have hprod : ∀ᵐ p ∂nu.prod mu,
      conditionalRealLinearForm (pastRealCofactorCombination hr) p ≠ z := by
    simpa [mu] using
      ae_conditionalRealLinearForm_ne_const_of_ae_energy_pos
        nu (pastRealCofactorCombination hr)
          (measurable_pastRealCofactorCombination hr) henergy z
  have he : MeasurePreserving e (nu.prod mu)
      (standardRealGaussianColumnMatrixMeasure r k) := by
    simpa [nu, mu, e] using
      measurePreserving_realLastColumnProductEquiv r k hr
  have hinv : MeasurePreserving e.symm
      (standardRealGaussianColumnMatrixMeasure r k) (nu.prod mu) :=
    he.symm e
  have hfull : ∀ᵐ X ∂(standardRealGaussianColumnMatrixMeasure r k),
      conditionalRealLinearForm (pastRealCofactorCombination hr)
        (e.symm X) ≠ z :=
    hinv.quasiMeasurePreserving.ae hprod
  filter_upwards [hfull] with X hX
  rw [← e.apply_symm_apply X,
    realGramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm]
  exact hX

/-- Zero-specialization used by the simultaneous nonvanishing induction. -/
theorem ae_realGramHafnian_ne_zero_of_ae_pastRealCofactorV_pos
    {r k : ℕ} (hr : 1 ≤ r)
    (hV : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k), 0 < pastRealCofactorV hr A) :
    ∀ᵐ X ∂(standardRealGaussianColumnMatrixMeasure r k),
      realGramHafnianObservable r k X ≠ 0 :=
  ae_realGramHafnian_ne_const_of_ae_pastRealCofactorV_pos hr hV 0

/-- Almost-sure full rank of the literal real past columns. -/
theorem ae_pastRealColumns_linearIndependent
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        standardRealGaussianVectorMeasure k),
      LinearIndependent ℝ
        (fun j : OddCofactorIndex r hr ↦
          (WithLp.toLp 2 (A j) : RealCofactorSpace k)) := by
  apply ae_realLinearIndependent_pi_standardRealGaussianVectors_fintype
  simpa [card_oddCofactorIndex] using hk

/-- Full rank upgrades almost-sure nonvanishing of the past cofactor vector
to strict positivity of its energy. -/
theorem ae_pastRealCofactorV_pos_of_ae_cofactorVector_ne_zero
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k)
    (hC : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k),
      pastRealHafnianCofactorVector hr A ≠ 0) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        standardRealGaussianVectorMeasure k),
      0 < pastRealCofactorV hr A := by
  have hLI := ae_pastRealColumns_linearIndependent hr hk
  filter_upwards [hLI, hC] with A hALI hAC
  exact pastRealCofactorV_pos_of_linearIndependent_of_cofactor_ne_zero
    hr A hALI hAC

/-- Simultaneous axiom-free induction proving past-energy positivity and
full-hafnian nonvanishing at every admissible real level. -/
theorem ae_pastRealCofactorV_pos_and_realGramHafnian_ne_zero
    (k : ℕ) :
    ∀ r : ℕ, ∀ hr : 1 ≤ r, 2 * r - 1 ≤ k →
      (∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
          standardRealGaussianVectorMeasure k),
        0 < pastRealCofactorV hr A) ∧
      (∀ᵐ X ∂(standardRealGaussianColumnMatrixMeasure r k),
        realGramHafnianObservable r k X ≠ 0) := by
  intro r
  induction r with
  | zero =>
      intro hr
      omega
  | succ n ih =>
      intro hr hk
      by_cases hn : n = 0
      · subst n
        have hC : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex 1 hr ↦
            standardRealGaussianVectorMeasure k),
            pastRealHafnianCofactorVector hr A ≠ 0 :=
          Filter.Eventually.of_forall fun A ↦
            pastRealHafnianCofactorVector_ne_zero_level_one A
        have hV :=
          ae_pastRealCofactorV_pos_of_ae_cofactorVector_ne_zero hr hk hC
        exact ⟨hV,
          ae_realGramHafnian_ne_zero_of_ae_pastRealCofactorV_pos hr hV⟩
      · have hnpos : 1 ≤ n := by omega
        have hnk : 2 * n - 1 ≤ k := by omega
        have hprev := ih hnpos hnk
        have hC : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex (n + 1) hr ↦
            standardRealGaussianVectorMeasure k),
            pastRealHafnianCofactorVector hr A ≠ 0 := by
          apply
            ae_pastRealCofactorVector_ne_zero_of_ae_lower_realGramHafnian_ne_zero
              hr (by omega)
          simpa using hprev.2
        have hV :=
          ae_pastRealCofactorV_pos_of_ae_cofactorVector_ne_zero hr hk hC
        exact ⟨hV,
          ae_realGramHafnian_ne_zero_of_ae_pastRealCofactorV_pos hr hV⟩

/-- Public positivity endpoint used by the literal real small-ball theorem. -/
theorem ae_pastRealCofactorV_pos_standardRealGaussian
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        standardRealGaussianVectorMeasure k),
      0 < pastRealCofactorV hr A :=
  (ae_pastRealCofactorV_pos_and_realGramHafnian_ne_zero k r hr hk).1

/-- Public nonvanishing endpoint for the literal real Gram hafnian. -/
theorem ae_realGramHafnian_ne_zero_standardRealGaussian
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ X ∂(standardRealGaussianColumnMatrixMeasure r k),
      realGramHafnianObservable r k X ≠ 0 :=
  (ae_pastRealCofactorV_pos_and_realGramHafnian_ne_zero k r hr hk).2

end

end LogdetLean.GramHafnian
