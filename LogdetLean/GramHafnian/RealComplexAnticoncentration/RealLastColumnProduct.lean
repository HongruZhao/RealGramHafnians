import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralCofactor
import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Exposing the final real Gaussian column

The literal real matrix law is identified measure-preservingly with its
`2r-1` past columns and one fresh standard real Gaussian column.  Under this
identification the real Gram hafnian is exactly the conditional transpose
linear form with energy `V_r`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

abbrev RealLastCofactorComplement (r : ℕ) (hr : 1 ≤ r) :=
  {j : Fin (2 * r) // ¬ j ≠ evenLastIndex r hr}

instance uniqueRealLastCofactorComplement (r : ℕ) (hr : 1 ≤ r) :
    Unique (RealLastCofactorComplement r hr) where
  default := ⟨evenLastIndex r hr, by simp⟩
  uniq j := by
    apply Subtype.ext
    simpa using not_ne_iff.mp j.2

/-- Insert the real past columns and the fresh final column into their
literal positions. -/
def realLastColumnProductEquiv (r k : ℕ) (hr : 1 ≤ r) :
    ((OddCofactorIndex r hr → (Fin k → ℝ)) × (Fin k → ℝ)) ≃ᵐ
      RealColumnMatrix r k :=
  let Col := Fin k → ℝ
  let p : Fin (2 * r) → Prop := fun j ↦ j ≠ evenLastIndex r hr
  (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (OddCofactorIndex r hr → Col))
      (MeasurableEquiv.funUnique (RealLastCofactorComplement r hr) Col).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : OddCofactorIndex r hr ⊕
        RealLastCofactorComplement r hr ↦ Col)).symm.trans
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (2 * r) ↦ Col) (Equiv.sumCompl p)))

theorem realLastColumnProductEquiv_apply_nonlast
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr → (Fin k → ℝ)) × (Fin k → ℝ))
    (j : OddCofactorIndex r hr) :
    realLastColumnProductEquiv r k hr p j.1 = p.1 j := by
  let e := Equiv.sumCompl (fun i : Fin (2 * r) ↦
    i ≠ evenLastIndex r hr)
  rw [show (j.1 : Fin (2 * r)) = e (Sum.inl j) by rfl]
  change Equiv.piCongrLeft (fun _ : Fin (2 * r) ↦ Fin k → ℝ) e
      ((Equiv.sumPiEquivProdPi
        (fun _ : OddCofactorIndex r hr ⊕
          RealLastCofactorComplement r hr ↦ Fin k → ℝ)).symm
        (p.1, fun _ ↦ p.2)) (e (Sum.inl j)) = p.1 j
  exact Equiv.piCongrLeft_sumInl
    (fun _ : Fin (2 * r) ↦ Fin k → ℝ) e p.1 (fun _ ↦ p.2) j

theorem realLastColumnProductEquiv_apply_last
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr → (Fin k → ℝ)) × (Fin k → ℝ)) :
    realLastColumnProductEquiv r k hr p (evenLastIndex r hr) = p.2 := by
  let e := Equiv.sumCompl (fun i : Fin (2 * r) ↦
    i ≠ evenLastIndex r hr)
  have hlast : (evenLastIndex r hr : Fin (2 * r)) =
      e (Sum.inr default) := by rfl
  rw [hlast]
  change Equiv.piCongrLeft (fun _ : Fin (2 * r) ↦ Fin k → ℝ) e
      ((Equiv.sumPiEquivProdPi
        (fun _ : OddCofactorIndex r hr ⊕
          RealLastCofactorComplement r hr ↦ Fin k → ℝ)).symm
        (p.1, fun _ ↦ p.2)) (e (Sum.inr default)) = p.2
  exact Equiv.piCongrLeft_sumInr
    (fun _ : Fin (2 * r) ↦ Fin k → ℝ) e p.1 (fun _ ↦ p.2) default

/-- Exact product-measure preservation for the real last-column split. -/
theorem measurePreserving_realLastColumnProductEquiv
    (r k : ℕ) (hr : 1 ≤ r) :
    MeasurePreserving (realLastColumnProductEquiv r k hr)
      ((Measure.pi fun _ : OddCofactorIndex r hr ↦
          standardRealGaussianVectorMeasure k).prod
        (standardRealGaussianVectorMeasure k))
      (standardRealGaussianColumnMatrixMeasure r k) := by
  letI : Fintype (RealLastCofactorComplement r hr) := Unique.fintype
  let Col := Fin k → ℝ
  let mu : Measure Col := standardRealGaussianVectorMeasure k
  let p : Fin (2 * r) → Prop := fun j ↦ j ≠ evenLastIndex r hr
  let eUnique := MeasurableEquiv.funUnique
    (RealLastCofactorComplement r hr) Col
  have hUnique : MeasurePreserving eUnique
      (Measure.pi fun _ : RealLastCofactorComplement r hr ↦ mu) mu :=
    measurePreserving_funUnique mu (RealLastCofactorComplement r hr)
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl (OddCofactorIndex r hr → Col)) eUnique.symm)
      ((Measure.pi fun _ : OddCofactorIndex r hr ↦ mu).prod mu)
      ((Measure.pi fun _ : OddCofactorIndex r hr ↦ mu).prod
        (Measure.pi fun _ : RealLastCofactorComplement r hr ↦ mu)) := by
    have hid := MeasurePreserving.id
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ mu)
    have hs := hUnique.symm eUnique
    have hp := hid.prod hs
    have hfun :
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (OddCofactorIndex r hr → Col)) eUnique.symm :
            ((OddCofactorIndex r hr → Col) × Col) →
              ((OddCofactorIndex r hr → Col) ×
                (RealLastCofactorComplement r hr → Col))) =
          Prod.map id eUnique.symm := by
      funext q
      rfl
    rw [hfun]
    exact hp
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : OddCofactorIndex r hr ⊕
          RealLastCofactorComplement r hr ↦ Col)).symm
      ((Measure.pi fun _ : OddCofactorIndex r hr ↦ mu).prod
        (Measure.pi fun _ : RealLastCofactorComplement r hr ↦ mu))
      (Measure.pi fun _ : OddCofactorIndex r hr ⊕
        RealLastCofactorComplement r hr ↦ mu) := by
    simpa using measurePreserving_sumPiEquivProdPi_symm
      (fun _ : OddCofactorIndex r hr ⊕
        RealLastCofactorComplement r hr ↦ mu)
  have h3 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (2 * r) ↦ Col) (Equiv.sumCompl p))
      (Measure.pi fun _ : OddCofactorIndex r hr ⊕
        RealLastCofactorComplement r hr ↦ mu)
      (Measure.pi fun _ : Fin (2 * r) ↦ mu) := by
    simpa [p] using measurePreserving_piCongrLeft
      (fun _ : Fin (2 * r) ↦ mu) (Equiv.sumCompl p)
  have h := h3.comp (h2.comp h1)
  refine ⟨(realLastColumnProductEquiv r k hr).measurable, ?_⟩
  have hfun :
      (realLastColumnProductEquiv r k hr :
        ((OddCofactorIndex r hr → (Fin k → ℝ)) × (Fin k → ℝ)) →
          RealColumnMatrix r k) =
        (MeasurableEquiv.piCongrLeft
            (fun _ : Fin (2 * r) ↦ Col) (Equiv.sumCompl p)) ∘
          (MeasurableEquiv.sumPiEquivProdPi
            (fun _ : OddCofactorIndex r hr ⊕
              RealLastCofactorComplement r hr ↦ Col)).symm ∘
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl (OddCofactorIndex r hr → Col))
            eUnique.symm) := by rfl
  rw [hfun]
  simpa [mu, standardRealGaussianColumnMatrixMeasure] using h.map_eq

/-- Canonical literal matrix with the exposed final column set to zero. -/
def pastRealCofactorMatrix {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    RealColumnMatrix r k :=
  realLastColumnProductEquiv r k hr (A, 0)

def pastRealHafnianCofactorVector {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    OddCofactorIndex r hr → ℝ :=
  realOddHafnianCofactorVector hr (pastRealCofactorMatrix hr A)

def pastRealCofactorCombination {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) : Fin k → ℝ :=
  realOddCofactorColumnCombination hr (pastRealCofactorMatrix hr A)

def pastRealCofactorW {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) : ℝ :=
  realOddCofactorW hr (pastRealCofactorMatrix hr A)

def pastRealCofactorV {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) : ℝ :=
  realOddCofactorV hr (pastRealCofactorMatrix hr A)

@[fun_prop] theorem measurable_pastRealCofactorCombination
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastRealCofactorCombination (k := k) hr) := by
  unfold pastRealCofactorCombination pastRealCofactorMatrix
  exact (measurable_realOddCofactorColumnCombination hr).comp
    ((realLastColumnProductEquiv r k hr).measurable.comp
      (measurable_id.prodMk measurable_const))

@[fun_prop] theorem measurable_pastRealCofactorW
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastRealCofactorW (k := k) hr) := by
  unfold pastRealCofactorW pastRealCofactorMatrix
  exact (measurable_realOddCofactorW hr).comp
    ((realLastColumnProductEquiv r k hr).measurable.comp
      (measurable_id.prodMk measurable_const))

@[fun_prop] theorem measurable_pastRealCofactorV
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastRealCofactorV (k := k) hr) := by
  unfold pastRealCofactorV pastRealCofactorMatrix
  exact (measurable_realOddCofactorV hr).comp
    ((realLastColumnProductEquiv r k hr).measurable.comp
      (measurable_id.prodMk measurable_const))

theorem pastRealCofactorW_nonneg {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    0 ≤ pastRealCofactorW hr A :=
  realOddCofactorW_nonneg hr (pastRealCofactorMatrix hr A)

theorem pastRealCofactorV_nonneg {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    0 ≤ pastRealCofactorV hr A :=
  realOddCofactorV_nonneg hr (pastRealCofactorMatrix hr A)

theorem pastRealCofactorV_eq_realCoefficientEnergy
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    pastRealCofactorV hr A =
      realCoefficientEnergy (pastRealCofactorCombination hr A) := by
  rfl

/-- Under the product split, the full real hafnian is exactly the fresh
column transpose-linear form. -/
theorem realGramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr → (Fin k → ℝ)) × (Fin k → ℝ)) :
    realGramHafnianObservable r k (realLastColumnProductEquiv r k hr p) =
      conditionalRealLinearForm (pastRealCofactorCombination hr) p := by
  rw [realGramHafnian_eq_lastColumn_dot_cofactorCombination hr]
  unfold conditionalRealLinearForm iidRealTransposeLinearForm
  rw [realLastColumnProductEquiv_apply_last]
  have hXY : ∀ i : Fin (2 * r), i ≠ evenLastIndex r hr →
      realLastColumnProductEquiv r k hr p i =
        pastRealCofactorMatrix hr p.1 i := by
    intro i hi
    unfold pastRealCofactorMatrix
    rw [realLastColumnProductEquiv_apply_nonlast hr p ⟨i, hi⟩,
      realLastColumnProductEquiv_apply_nonlast hr (p.1, 0) ⟨i, hi⟩]
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  unfold pastRealCofactorCombination realOddCofactorColumnCombination
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hXY j.1 j.2]
  rw [realOddHafnianCofactorVector_congr_off_last hr hXY j]

/-- Literal real shifted-small-ball estimate in terms of the bounded
fractional resolvent of `V_r`. -/
theorem standardRealGaussianColumnMatrix_shiftedSmallBall_le_halfResolvent
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k), 0 < pastRealCofactorV hr A)
    (z rho : ℝ) (hrho : 0 < rho) :
    (standardRealGaussianColumnMatrixMeasure r k)
        {X | |realGramHafnianObservable r k X - z| ≤ rho} ≤
      ENNReal.ofReal 2 *
        ennHalfResolvent
          (Measure.pi fun _ : OddCofactorIndex r hr ↦
            standardRealGaussianVectorMeasure k)
          (pastRealCofactorV hr) (rho ^ 2) := by
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let mu : Measure (Fin k → ℝ) := standardRealGaussianVectorMeasure k
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
    prod_pi_realGaussian_shiftedSmallBall_le_halfResolvent
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
  simpa [nu, mu, source, standardRealGaussianVectorMeasure] using hconditional

end

end LogdetLean.GramHafnian
