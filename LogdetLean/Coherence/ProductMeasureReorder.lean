import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
/-! Small exact product-measure reorderings used by the Gaussian frame law. -/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C]

/-- Move the middle coordinate of `A × (B × C)` to the front. -/
def middleToFront (x : A × (B × C)) : B × (A × C) :=
  (x.2.1, (x.1, x.2.2))

theorem measurable_middleToFront :
    Measurable (middleToFront : A × (B × C) → B × (A × C)) := by
  unfold middleToFront
  fun_prop

/-- The corresponding exact permutation of three product measures. -/
theorem map_middleToFront_prod
    (mu : Measure A) (nu : Measure B) (tau : Measure C)
    [SFinite mu] [SFinite nu] [SFinite tau] :
    Measure.map (middleToFront : A × (B × C) → B × (A × C))
        (mu.prod (nu.prod tau)) =
      nu.prod (mu.prod tau) := by
  let assocInv : A × (B × C) → (A × B) × C :=
    MeasurableEquiv.prodAssoc.symm
  let swapLeft : (A × B) × C → (B × A) × C :=
    Prod.map Prod.swap id
  let assocFwd : (B × A) × C → B × (A × C) :=
    MeasurableEquiv.prodAssoc
  have hassocInv :
      Measure.map assocInv (mu.prod (nu.prod tau)) = (mu.prod nu).prod tau := by
    exact ((measurePreserving_prodAssoc mu nu tau).symm
      MeasurableEquiv.prodAssoc).map_eq
  have hswap :
      Measure.map swapLeft ((mu.prod nu).prod tau) =
        (nu.prod mu).prod tau := by
    calc
      Measure.map swapLeft ((mu.prod nu).prod tau) =
          (Measure.map Prod.swap (mu.prod nu)).prod (Measure.map id tau) := by
        exact (Measure.map_prod_map (mu.prod nu) tau measurable_swap measurable_id).symm
      _ = (nu.prod mu).prod tau := by
        rw [Measure.prod_swap, Measure.map_id]
  have hassocFwd :
      Measure.map assocFwd ((nu.prod mu).prod tau) =
        nu.prod (mu.prod tau) := by
    exact (measurePreserving_prodAssoc nu mu tau).map_eq
  have hfun :
      (middleToFront : A × (B × C) → B × (A × C)) =
        assocFwd ∘ swapLeft ∘ assocInv := by
    funext x
    rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), hassocInv, hswap,
    hassocFwd]

/-- Move the middle coordinate of `(A × B) × C` to the end. -/
def middleToLast (x : (A × B) × C) : (A × C) × B :=
  ((x.1.1, x.2), x.1.2)

theorem measurable_middleToLast :
    Measurable (middleToLast : (A × B) × C → (A × C) × B) := by
  unfold middleToLast
  fun_prop

/-- Exact product-measure law for `middleToLast`. -/
theorem map_middleToLast_prod
    (mu : Measure A) (nu : Measure B) (tau : Measure C)
    [SFinite mu] [SFinite nu] [SFinite tau] :
    Measure.map (middleToLast : (A × B) × C → (A × C) × B)
        ((mu.prod nu).prod tau) =
      (mu.prod tau).prod nu := by
  let assocFwd : (A × B) × C → A × (B × C) :=
    MeasurableEquiv.prodAssoc
  let finalSwap : B × (A × C) → (A × C) × B := Prod.swap
  have hassoc :
      Measure.map assocFwd ((mu.prod nu).prod tau) =
        mu.prod (nu.prod tau) :=
    (measurePreserving_prodAssoc mu nu tau).map_eq
  have hmiddle :
      Measure.map (middleToFront : A × (B × C) → B × (A × C))
          (mu.prod (nu.prod tau)) =
        nu.prod (mu.prod tau) := map_middleToFront_prod mu nu tau
  have hswap :
      Measure.map finalSwap (nu.prod (mu.prod tau)) =
        (mu.prod tau).prod nu := Measure.prod_swap
  have hfun :
      (middleToLast : (A × B) × C → (A × C) × B) =
        finalSwap ∘ middleToFront ∘ assocFwd := by
    funext x
    rfl
  rw [hfun, ← Measure.map_map measurable_swap
      (measurable_middleToFront.comp MeasurableEquiv.prodAssoc.measurable),
    ← Measure.map_map measurable_middleToFront
      MeasurableEquiv.prodAssoc.measurable, hassoc, hmiddle, hswap]

end

end LogdetLean.Coherence
