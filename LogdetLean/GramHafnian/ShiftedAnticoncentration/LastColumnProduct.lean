import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorMeasurable
import LogdetLean.GramHafnian.ShiftedAnticoncentration.ConditionalSmallBall
import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Separating the exposed final Gaussian column

The existing literal matrix model is a finite iid family indexed by
`Fin (2*r)`.  Here it is identified, measure preservingly, with the product
of the `2*r-1` non-final columns and one fresh final column.  The cofactor
expansion then becomes exactly the conditional transpose-linear form used by
`ConditionalSmallBall`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The singleton complementary subtype containing only the exposed final
index. -/
abbrev LastCofactorComplement (r : ℕ) (hr : 1 ≤ r) :=
  {j : Fin (2 * r) // ¬ j ≠ evenLastIndex r hr}

instance uniqueLastCofactorComplement (r : ℕ) (hr : 1 ≤ r) :
    Unique (LastCofactorComplement r hr) where
  default := ⟨evenLastIndex r hr, by simp⟩
  uniq j := by
    apply Subtype.ext
    simpa using not_ne_iff.mp j.2

/-- Measurable equivalence which inserts the non-final columns and the final
column into their literal `Fin (2*r)` positions. -/
def lastColumnProductEquiv (r k : ℕ) (hr : 1 ≤ r) :
    ((OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ)) ≃ᵐ
      ComplexColumnMatrix r k :=
  let Col := Fin k -> ℂ
  let p : Fin (2 * r) -> Prop := fun j => j ≠ evenLastIndex r hr
  (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (OddCofactorIndex r hr -> Col))
      (MeasurableEquiv.funUnique (LastCofactorComplement r hr) Col).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : OddCofactorIndex r hr ⊕ LastCofactorComplement r hr => Col)).symm.trans
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (2 * r) => Col) (Equiv.sumCompl p)))

theorem lastColumnProductEquiv_apply_nonlast
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ))
    (j : OddCofactorIndex r hr) :
    lastColumnProductEquiv r k hr p j.1 = p.1 j := by
  let e := Equiv.sumCompl (fun i : Fin (2 * r) =>
    i ≠ evenLastIndex r hr)
  rw [show (j.1 : Fin (2 * r)) = e (Sum.inl j) by rfl]
  change Equiv.piCongrLeft (fun _ : Fin (2 * r) => Fin k -> ℂ) e
      ((Equiv.sumPiEquivProdPi
        (fun _ : OddCofactorIndex r hr ⊕ LastCofactorComplement r hr =>
          Fin k -> ℂ)).symm (p.1, fun _ => p.2))
      (e (Sum.inl j)) = p.1 j
  exact Equiv.piCongrLeft_sumInl
    (fun _ : Fin (2 * r) => Fin k -> ℂ) e p.1 (fun _ => p.2) j

theorem lastColumnProductEquiv_apply_last
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ)) :
    lastColumnProductEquiv r k hr p (evenLastIndex r hr) = p.2 := by
  let e := Equiv.sumCompl (fun i : Fin (2 * r) =>
    i ≠ evenLastIndex r hr)
  have hlast : (evenLastIndex r hr : Fin (2 * r)) =
      e (Sum.inr default) := by
    rfl
  rw [hlast]
  change Equiv.piCongrLeft (fun _ : Fin (2 * r) => Fin k -> ℂ) e
      ((Equiv.sumPiEquivProdPi
        (fun _ : OddCofactorIndex r hr ⊕ LastCofactorComplement r hr =>
          Fin k -> ℂ)).symm (p.1, fun _ => p.2))
      (e (Sum.inr default)) = p.2
  exact Equiv.piCongrLeft_sumInr
    (fun _ : Fin (2 * r) => Fin k -> ℂ) e p.1 (fun _ => p.2) default

/-- The last-column insertion equivalence preserves the iid circular column
law exactly. -/
theorem measurePreserving_lastColumnProductEquiv
    (r k : ℕ) (hr : 1 ≤ r) :
    MeasurePreserving (lastColumnProductEquiv r k hr)
      ((Measure.pi fun _ : OddCofactorIndex r hr =>
          circularGaussianVector k).prod (circularGaussianVector k))
      (circularGaussianColumnMatrixMeasure r k) := by
  letI : Fintype (LastCofactorComplement r hr) := Unique.fintype
  let Col := Fin k -> ℂ
  let mu : Measure Col := circularGaussianVector k
  let p : Fin (2 * r) -> Prop := fun j => j ≠ evenLastIndex r hr
  let eUnique := MeasurableEquiv.funUnique
    (LastCofactorComplement r hr) Col
  have hUnique : MeasurePreserving eUnique
      (Measure.pi fun _ : LastCofactorComplement r hr => mu) mu :=
    measurePreserving_funUnique mu (LastCofactorComplement r hr)
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl (OddCofactorIndex r hr -> Col)) eUnique.symm)
      ((Measure.pi fun _ : OddCofactorIndex r hr => mu).prod mu)
      ((Measure.pi fun _ : OddCofactorIndex r hr => mu).prod
        (Measure.pi fun _ : LastCofactorComplement r hr => mu)) := by
    have hid := MeasurePreserving.id
      (Measure.pi fun _ : OddCofactorIndex r hr => mu)
    have hs := hUnique.symm eUnique
    have hp := hid.prod hs
    have hfun :
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (OddCofactorIndex r hr -> Col)) eUnique.symm :
            ((OddCofactorIndex r hr -> Col) × Col) ->
              ((OddCofactorIndex r hr -> Col) ×
                (LastCofactorComplement r hr -> Col))) =
          Prod.map id eUnique.symm := by
      funext q
      rfl
    rw [hfun]
    exact hp
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : OddCofactorIndex r hr ⊕ LastCofactorComplement r hr => Col)).symm
      ((Measure.pi fun _ : OddCofactorIndex r hr => mu).prod
        (Measure.pi fun _ : LastCofactorComplement r hr => mu))
      (Measure.pi fun _ : OddCofactorIndex r hr ⊕
        LastCofactorComplement r hr => mu) := by
    simpa using measurePreserving_sumPiEquivProdPi_symm
      (fun _ : OddCofactorIndex r hr ⊕ LastCofactorComplement r hr => mu)
  have h3 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (2 * r) => Col) (Equiv.sumCompl p))
      (Measure.pi fun _ : OddCofactorIndex r hr ⊕
        LastCofactorComplement r hr => mu)
      (Measure.pi fun _ : Fin (2 * r) => mu) := by
    simpa [p] using measurePreserving_piCongrLeft
      (fun _ : Fin (2 * r) => mu) (Equiv.sumCompl p)
  have h := h3.comp (h2.comp h1)
  refine ⟨(lastColumnProductEquiv r k hr).measurable, ?_⟩
  have hfun :
      (lastColumnProductEquiv r k hr :
        ((OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ)) ->
          ComplexColumnMatrix r k) =
        (MeasurableEquiv.piCongrLeft
            (fun _ : Fin (2 * r) => Col) (Equiv.sumCompl p)) ∘
          (MeasurableEquiv.sumPiEquivProdPi
            (fun _ : OddCofactorIndex r hr ⊕
              LastCofactorComplement r hr => Col)).symm ∘
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl (OddCofactorIndex r hr -> Col))
            eUnique.symm) := by
    rfl
  rw [hfun]
  simpa [mu, circularGaussianColumnMatrixMeasure] using h.map_eq

/-- Fill the exposed final column with zero.  Since every odd cofactor ignores
that column, this is a canonical matrix representative of the past. -/
def pastCofactorMatrix {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr -> (Fin k -> ℂ)) :
    ComplexColumnMatrix r k :=
  lastColumnProductEquiv r k hr (A, 0)

/-- Coefficient vector `A_r C_r`, viewed solely as a function of the past
columns. -/
def pastCofactorCombination {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr -> (Fin k -> ℂ)) : Fin k -> ℂ :=
  oddCofactorColumnCombination hr (pastCofactorMatrix hr A)

/-- Its squared norm, the literal conditional variance `V_r`. -/
def pastCofactorV {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr -> (Fin k -> ℂ)) : ℝ :=
  oddCofactorV hr (pastCofactorMatrix hr A)

@[fun_prop]
theorem measurable_pastCofactorCombination {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastCofactorCombination (k := k) hr) := by
  unfold pastCofactorCombination pastCofactorMatrix
  exact (measurable_oddCofactorColumnCombination hr).comp
    ((lastColumnProductEquiv r k hr).measurable.comp
      (measurable_id.prodMk measurable_const))

@[fun_prop]
theorem measurable_pastCofactorV {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastCofactorV (k := k) hr) := by
  unfold pastCofactorV pastCofactorMatrix
  exact (measurable_oddCofactorV hr).comp
    ((lastColumnProductEquiv r k hr).measurable.comp
      (measurable_id.prodMk measurable_const))

theorem pastCofactorV_eq_coefficientEnergy {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr -> (Fin k -> ℂ)) :
    pastCofactorV hr A =
      circularCoefficientEnergy (pastCofactorCombination hr A) := by
  unfold pastCofactorV pastCofactorCombination oddCofactorV
    circularCoefficientEnergy
  simp_rw [Complex.normSq_eq_norm_sq]

/-- Under the product decomposition, the full Gram hafnian is exactly the
fresh-column transpose-linear form with the past cofactor combination. -/
theorem gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ)) :
    gramHafnianObservable r k (lastColumnProductEquiv r k hr p) =
      conditionalCircularLinearForm (pastCofactorCombination hr) p := by
  rw [gramHafnianObservable,
    gramHafnian_eq_lastColumn_dot_cofactorCombination hr]
  unfold conditionalCircularLinearForm iidCircularTransposeLinearForm
  rw [lastColumnProductEquiv_apply_last]
  have hXY : ∀ i : Fin (2 * r), i ≠ evenLastIndex r hr ->
      lastColumnProductEquiv r k hr p i = pastCofactorMatrix hr p.1 i := by
    intro i hi
    unfold pastCofactorMatrix
    rw [lastColumnProductEquiv_apply_nonlast hr p ⟨i, hi⟩,
      lastColumnProductEquiv_apply_nonlast hr (p.1, 0) ⟨i, hi⟩]
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  unfold pastCofactorCombination
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hXY j.1 j.2]
  rw [oddHafnianCofactorVector_congr_off_last hr hXY j]

@[fun_prop]
theorem measurable_gramHafnianObservable (r k : ℕ) :
    Measurable (gramHafnianObservable r k) := by
  have hfun : gramHafnianObservable r k =
      fun X : ComplexColumnMatrix r k =>
        typeHafnian (transposeGram (rowMatrix X)) := by
    funext X
    unfold gramHafnianObservable gramHafnian
    exact (typeHafnian_fin_eq_hafnian _).symm
  rw [hfun]
  have hcont : Continuous (fun X : ComplexColumnMatrix r k =>
      typeHafnian (transposeGram (rowMatrix X))) :=
    (continuous_typeHafnian (α := Fin (2 * r))).comp (by
      unfold transposeGram rowMatrix
      fun_prop)
  exact hcont.measurable

/-- Literal raw shifted disk estimate for the Gram hafnian.  The only input
left explicit here is almost-sure positivity of the cofactor variance; later
the level induction proves that property together with the inverse-moment
bound. -/
theorem circularGaussianColumnMatrix_shiftedSmallBall_le_pastInverseMoment
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr =>
      circularGaussianVector k), 0 < pastCofactorV hr A)
    (z : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (circularGaussianColumnMatrixMeasure r k)
        {X | ‖gramHafnianObservable r k X - z‖ ≤ rho} ≤
      ENNReal.ofReal (rho ^ 2) *
        ennInverseMoment
          (Measure.pi fun _ : OddCofactorIndex r hr =>
            circularGaussianVector k)
          (pastCofactorV hr) := by
  let nu : Measure (OddCofactorIndex r hr -> (Fin k -> ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr => circularGaussianVector k
  let mu : Measure (Fin k -> ℂ) := circularGaussianVector k
  let e := lastColumnProductEquiv r k hr
  let target : Set (ComplexColumnMatrix r k) :=
    {X | ‖gramHafnianObservable r k X - z‖ ≤ rho}
  let source : Set
      ((OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ)) :=
    {p | ‖conditionalCircularLinearForm (pastCofactorCombination hr) p - z‖ ≤ rho}
  have htarget : MeasurableSet target := by
    dsimp [target]
    exact measurableSet_le
      ((measurable_gramHafnianObservable r k).sub_const z).norm measurable_const
  have hpre : e ⁻¹' target = source := by
    ext p
    simp only [Set.mem_preimage]
    change (‖gramHafnianObservable r k (e p) - z‖ ≤ rho) ↔
      ‖conditionalCircularLinearForm (pastCofactorCombination hr) p - z‖ ≤ rho
    rw [gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm]
  have hmap := (measurePreserving_lastColumnProductEquiv r k hr).map_eq
  rw [← hmap, Measure.map_apply e.measurable htarget, hpre]
  have hconditional :=
    prod_pi_circularGaussian_shiftedSmallBall_le_inverseMoment
      nu (pastCofactorCombination hr)
      (measurable_pastCofactorCombination hr)
      (by
        filter_upwards [show ∀ᵐ A ∂nu, 0 < pastCofactorV hr A by
          simpa [nu] using hVpos] with A hA
        simpa [conditionalCircularEnergy,
          pastCofactorV_eq_coefficientEnergy] using hA)
      z rho hrho
  have henergy :
      (conditionalCircularEnergy (pastCofactorCombination hr) :
        (OddCofactorIndex r hr -> (Fin k -> ℂ)) -> ℝ) =
      (pastCofactorV hr :
        (OddCofactorIndex r hr -> (Fin k -> ℂ)) -> ℝ) := by
    funext A
    exact (pastCofactorV_eq_coefficientEnergy hr A).symm
  rw [henergy] at hconditional
  simpa [nu, mu, source, circularGaussianVector] using hconditional

end

end LogdetLean.GramHafnian
