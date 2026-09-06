import LogdetLean.Coherence.StableMatchingFrameIndependence
import LogdetLean.GaussianColumnProduct
import Mathlib.Tactic
/-!
# IID Gaussian law of the flattened stable-matching base sample

The base sample groups the first `2s` columns into `s` pairs.  This file
proves that forgetting that grouping gives exactly an ordinary iid Gaussian
column family on `(Fin 2 × Fin s) ⊕ Fin r`.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Read a product pair as a `Fin 2` family. -/
def gaussianPairToFinTwo : E × E → Fin 2 → E :=
  (MeasurableEquiv.finTwoArrow : (Fin 2 → E) ≃ᵐ E × E).symm

theorem measurable_gaussianPairToFinTwo :
    Measurable (gaussianPairToFinTwo (E := E)) :=
  (MeasurableEquiv.finTwoArrow : (Fin 2 → E) ≃ᵐ E × E).symm.measurable

@[simp] theorem gaussianPairToFinTwo_zero (x : E × E) :
    gaussianPairToFinTwo x 0 = x.1 := by
  rfl

@[simp] theorem gaussianPairToFinTwo_one (x : E × E) :
    gaussianPairToFinTwo x 1 = x.2 := by
  rfl

theorem map_gaussianPairToFinTwo_gaussianProduct :
    Measure.map (gaussianPairToFinTwo (E := E))
        ((stdGaussian E).prod (stdGaussian E)) =
      Measure.pi fun _ : Fin 2 ↦ stdGaussian E := by
  exact ((measurePreserving_finTwoArrow (stdGaussian E)).symm
    (MeasurableEquiv.finTwoArrow : (Fin 2 → E) ≃ᵐ E × E)).map_eq

/-- Apply the pair-to-two conversion coordinatewise. -/
def gaussianPairArrayToFinTwo (s : ℕ) :
    (Fin s → E × E) → (Fin s → Fin 2 → E) :=
  fun v e ↦ gaussianPairToFinTwo (v e)

theorem measurable_gaussianPairArrayToFinTwo (s : ℕ) :
    Measurable (gaussianPairArrayToFinTwo (E := E) s) := by
  unfold gaussianPairArrayToFinTwo
  refine measurable_pi_lambda _ fun e ↦ ?_
  exact measurable_gaussianPairToFinTwo.comp (measurable_pi_apply e)

theorem map_gaussianPairArrayToFinTwo (s : ℕ) :
    Measure.map (gaussianPairArrayToFinTwo (E := E) s)
        (Measure.pi fun _ : Fin s ↦
          (stdGaussian E).prod (stdGaussian E)) =
      Measure.pi fun _ : Fin s ↦
        Measure.pi fun _ : Fin 2 ↦ stdGaussian E := by
  change Measure.map
      (fun v : Fin s → E × E ↦ fun e ↦ gaussianPairToFinTwo (v e))
      (Measure.pi fun _ : Fin s ↦
        (stdGaussian E).prod (stdGaussian E)) = _
  rw [Measure.pi_map_pi (fun _ ↦ measurable_gaussianPairToFinTwo.aemeasurable)]
  congr 1
  funext e
  exact map_gaussianPairToFinTwo_gaussianProduct (E := E)

/-- Transpose and uncurry the pair array into columns indexed by
`Fin 2 × Fin s`. -/
def gaussianPairArrayColumns (s : ℕ) :
    (Fin s → E × E) → (Fin 2 × Fin s → E) :=
  (MeasurableEquiv.curry (Fin 2) (Fin s) E).symm ∘
    LogdetLean.piTransposeMeasurableEquiv (Fin s) (Fin 2) E ∘
      gaussianPairArrayToFinTwo s

theorem measurable_gaussianPairArrayColumns (s : ℕ) :
    Measurable (gaussianPairArrayColumns (E := E) s) := by
  unfold gaussianPairArrayColumns
  exact (MeasurableEquiv.curry (Fin 2) (Fin s) E).symm.measurable.comp
    ((LogdetLean.piTransposeMeasurableEquiv
      (Fin s) (Fin 2) E).measurable.comp
        (measurable_gaussianPairArrayToFinTwo s))

@[simp] theorem gaussianPairArrayColumns_zero
    (s : ℕ) (v : Fin s → E × E) (e : Fin s) :
    gaussianPairArrayColumns s v (0, e) = (v e).1 := by
  rfl

@[simp] theorem gaussianPairArrayColumns_one
    (s : ℕ) (v : Fin s → E × E) (e : Fin s) :
    gaussianPairArrayColumns s v (1, e) = (v e).2 := by
  rfl

theorem map_curry_symm_pi_pi_gaussian (s : ℕ) :
    Measure.map (MeasurableEquiv.curry (Fin 2) (Fin s) E).symm
        (Measure.pi fun _ : Fin 2 ↦
          Measure.pi fun _ : Fin s ↦ stdGaussian E) =
      Measure.pi fun _ : Fin 2 × Fin s ↦ stdGaussian E := by
  rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  simp_rw [← Measure.infinitePi_eq_pi]
  exact Measure.infinitePi_map_curry_symm
    (fun _ : Fin 2 ↦ fun _ : Fin s ↦ stdGaussian E)

theorem map_gaussianPairArrayColumns (s : ℕ) :
    Measure.map (gaussianPairArrayColumns (E := E) s)
        (Measure.pi fun _ : Fin s ↦
          (stdGaussian E).prod (stdGaussian E)) =
      Measure.pi fun _ : Fin 2 × Fin s ↦ stdGaussian E := by
  calc
    Measure.map (gaussianPairArrayColumns (E := E) s)
        (Measure.pi fun _ : Fin s ↦
          (stdGaussian E).prod (stdGaussian E)) =
        Measure.map (MeasurableEquiv.curry (Fin 2) (Fin s) E).symm
          (Measure.map (LogdetLean.piTransposeMeasurableEquiv
              (Fin s) (Fin 2) E)
            (Measure.map (gaussianPairArrayToFinTwo (E := E) s)
              (Measure.pi fun _ : Fin s ↦
                (stdGaussian E).prod (stdGaussian E)))) := by
      let A := (MeasurableEquiv.curry (Fin 2) (Fin s) E).symm
      let B := LogdetLean.piTransposeMeasurableEquiv (Fin s) (Fin 2) E
      let C := gaussianPairArrayToFinTwo (E := E) s
      let mu := Measure.pi fun _ : Fin s ↦
        (stdGaussian E).prod (stdGaussian E)
      have hA : Measurable A :=
        (MeasurableEquiv.curry (Fin 2) (Fin s) E).symm.measurable
      have hB : Measurable B :=
        (LogdetLean.piTransposeMeasurableEquiv (Fin s) (Fin 2) E).measurable
      have hC : Measurable C := measurable_gaussianPairArrayToFinTwo s
      change Measure.map (A ∘ B ∘ C) mu =
        Measure.map A (Measure.map B (Measure.map C mu))
      calc
        Measure.map (A ∘ B ∘ C) mu =
            Measure.map ((A ∘ B) ∘ C) mu := by
          congr 1
        _ = Measure.map (A ∘ B) (Measure.map C mu) := by
          rw [Measure.map_map (hA.comp hB) hC]
        _ = Measure.map A (Measure.map B (Measure.map C mu)) := by
          rw [Measure.map_map hA hB]
    _ = Measure.map (MeasurableEquiv.curry (Fin 2) (Fin s) E).symm
        (Measure.map (LogdetLean.piTransposeMeasurableEquiv
            (Fin s) (Fin 2) E)
          (Measure.pi fun _ : Fin s ↦
            Measure.pi fun _ : Fin 2 ↦ stdGaussian E)) := by
      rw [map_gaussianPairArrayToFinTwo]
    _ = Measure.map (MeasurableEquiv.curry (Fin 2) (Fin s) E).symm
        (Measure.pi fun _ : Fin 2 ↦
          Measure.pi fun _ : Fin s ↦ stdGaussian E) := by
      rw [LogdetLean.map_pi_pi_piTranspose]
    _ = _ := map_curry_symm_pi_pi_gaussian (E := E) s

/-- The flattened raw family is the sum-family equivalence applied to the
pair columns and singleton columns. -/
theorem stableMatchingRawColumns_eq_sumPi
    (s r : ℕ) (w : StableMatchingBaseSample E s r) :
    stableMatchingRawColumns s r w =
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Sum (Fin 2 × Fin s) (Fin r) ↦ E)).symm
        (gaussianPairArrayColumns s w.1, w.2) := by
  funext i
  rcases i with ⟨i, e⟩ | j
  · fin_cases i <;> rfl
  · rfl

/-- Exact iid Gaussian law of the flattened stable-matching base columns. -/
theorem map_stableMatchingRawColumns_eq_pi (s r : ℕ) :
    Measure.map (stableMatchingRawColumns (E := E) s r)
        (stableMatchingBaseMeasure E s r) =
      Measure.pi fun _ : Sum (Fin 2 × Fin s) (Fin r) ↦ stdGaussian E := by
  let pairColumns := gaussianPairArrayColumns (E := E) s
  let pairMeasure : Measure (Fin s → E × E) :=
    Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)
  let singletonMeasure : Measure (Fin r → E) :=
    Measure.pi fun _ : Fin r ↦ stdGaussian E
  let sumEquiv := (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Sum (Fin 2 × Fin s) (Fin r) ↦ E)).symm
  have hpair : Measurable pairColumns := measurable_gaussianPairArrayColumns s
  have hmapPair : Measure.map pairColumns pairMeasure =
      Measure.pi fun _ : Fin 2 × Fin s ↦ stdGaussian E := by
    exact map_gaussianPairArrayColumns (E := E) s
  have hprod : Measure.map (Prod.map pairColumns id)
      (pairMeasure.prod singletonMeasure) =
      (Measure.pi fun _ : Fin 2 × Fin s ↦ stdGaussian E).prod
        singletonMeasure := by
    calc
      Measure.map (Prod.map pairColumns id)
          (pairMeasure.prod singletonMeasure) =
          (Measure.map pairColumns pairMeasure).prod
            (Measure.map id singletonMeasure) :=
        (Measure.map_prod_map pairMeasure singletonMeasure
          hpair measurable_id).symm
      _ = _ := by rw [hmapPair, Measure.map_id]
  have hfun : stableMatchingRawColumns (E := E) s r =
      sumEquiv ∘ Prod.map pairColumns id := by
    funext w
    rw [stableMatchingRawColumns_eq_sumPi]
    rfl
  rw [hfun]
  change Measure.map (sumEquiv ∘ Prod.map pairColumns id)
      (pairMeasure.prod singletonMeasure) = _
  rw [← Measure.map_map (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Sum (Fin 2 × Fin s) (Fin r) ↦ E)).symm.measurable
      (hpair.prodMap measurable_id)]
  rw [hprod]
  exact (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Sum (Fin 2 × Fin s) (Fin r) ↦ stdGaussian E)).map_eq

/-! ## Reindexing by an ordinary `Fin (2s+r)` coordinate set -/

/-- A canonical, though mathematically irrelevant, equivalence between the
block/singleton coordinate type and `Fin (2s+r)`. -/
def stableMatchingIndexEquiv (s r : ℕ) :
    Sum (Fin 2 × Fin s) (Fin r) ≃ Fin (2 * s + r) :=
  (Fintype.equivFin (Sum (Fin 2 × Fin s) (Fin r))).trans
    (finCongr (by simp [Fintype.card_sum, Fintype.card_prod]))

/-- Reindex a block/singleton family as an ordinary `Fin` family. -/
def stableMatchingToFinColumns (s r : ℕ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E) : Fin (2 * s + r) → E :=
  fun i ↦ v ((stableMatchingIndexEquiv s r).symm i)

theorem measurable_stableMatchingToFinColumns (s r : ℕ) :
    Measurable (stableMatchingToFinColumns (E := E) s r) := by
  unfold stableMatchingToFinColumns
  exact measurable_pi_lambda _ fun i ↦
    measurable_pi_apply ((stableMatchingIndexEquiv s r).symm i)

/-- Reindexing the block/singleton family by the canonical finite equivalence
only reindexes its normalized Gram matrix. -/
theorem normalizedGram_stableMatchingToFinColumns
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E) :
    normalizedGram (stableMatchingToFinColumns s r v) =
      Matrix.reindex (stableMatchingIndexEquiv s r)
        (stableMatchingIndexEquiv s r) (normalizedGram v) := by
  ext i j
  rfl

/-- Consequently the normalized-Gram determinant is invariant under the
canonical block-to-`Fin` reindexing. -/
theorem det_normalizedGram_stableMatchingToFinColumns
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E) :
    (normalizedGram (stableMatchingToFinColumns s r v)).det =
      (normalizedGram v).det := by
  rw [normalizedGram_stableMatchingToFinColumns]
  exact Matrix.det_reindex_self (stableMatchingIndexEquiv s r)
    (normalizedGram v)

theorem measurePreserving_stableMatchingToFinColumns
    (s r : ℕ) :
    MeasurePreserving (stableMatchingToFinColumns (E := E) s r)
      (Measure.pi fun _ : Sum (Fin 2 × Fin s) (Fin r) ↦ stdGaussian E)
      (Measure.pi fun _ : Fin (2 * s + r) ↦ stdGaussian E) := by
  let e := stableMatchingIndexEquiv s r
  have hfun : stableMatchingToFinColumns (E := E) s r =
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (2 * s + r) ↦ E) e :
          (Sum (Fin 2 × Fin s) (Fin r) → E) →
            (Fin (2 * s + r) → E)) := by
    funext v
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    change v (e.symm (e j)) =
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (2 * s + r) ↦ E) e) v (e j)
    rw [e.symm_apply_apply]
    exact (MeasurableEquiv.piCongrLeft_apply_apply
      (e := e) (β := fun _ : Fin (2 * s + r) ↦ E) (x := v) j).symm
  rw [hfun]
  simpa [e] using
    (measurePreserving_piCongrLeft
      (α := fun _ : Fin (2 * s + r) ↦ E)
      (fun _ : Fin (2 * s + r) ↦ stdGaussian E) e)

/-- Consequently, the ordinary-`Fin` flattened raw columns are exactly iid
standard Gaussian. -/
theorem map_stableMatchingFinRawColumns_eq_pi (s r : ℕ) :
    Measure.map
        (stableMatchingToFinColumns (E := E) s r ∘
          stableMatchingRawColumns (E := E) s r)
        (stableMatchingBaseMeasure E s r) =
      Measure.pi fun _ : Fin (2 * s + r) ↦ stdGaussian E := by
  rw [← Measure.map_map (measurable_stableMatchingToFinColumns s r)
    (measurable_stableMatchingRawColumns s r)]
  rw [map_stableMatchingRawColumns_eq_pi]
  exact (measurePreserving_stableMatchingToFinColumns
    (E := E) s r).map_eq

/-- Whenever the number of columns is at most the ambient dimension, the
flattened stable-matching base columns are linearly independent almost
surely. -/
theorem ae_linearIndependent_stableMatchingRawColumns
    (s r m : ℕ) (hdim : Module.finrank ℝ E = m)
    (hcols : 2 * s + r ≤ m) :
    ∀ᵐ w ∂stableMatchingBaseMeasure E s r,
      LinearIndependent ℝ (stableMatchingRawColumns s r w) := by
  let F : StableMatchingBaseSample E s r → Fin (2 * s + r) → E :=
    stableMatchingToFinColumns s r ∘ stableMatchingRawColumns s r
  have hF : Measurable F :=
    (measurable_stableMatchingToFinColumns s r).comp
      (measurable_stableMatchingRawColumns s r)
  have hset : MeasurableSet
      {v : Fin (2 * s + r) → E | LinearIndependent ℝ v} :=
    measurableSet_linearlyIndependentTuples (E := E) (2 * s + r)
  have htarget : ∀ᵐ v ∂Measure.pi
      (fun _ : Fin (2 * s + r) ↦ stdGaussian E),
      LinearIndependent ℝ v :=
    ae_linearIndependent_pi_stdGaussian (2 * s + r) (by simpa [hdim])
  have hpull : ∀ᵐ w ∂stableMatchingBaseMeasure E s r,
      LinearIndependent ℝ (F w) := by
    rw [← map_stableMatchingFinRawColumns_eq_pi (E := E) s r] at htarget
    exact (ae_map_iff hF.aemeasurable hset).1 htarget
  filter_upwards [hpull] with w hw
  simpa [F, stableMatchingToFinColumns, Function.comp_def] using
    (linearIndependent_equiv (stableMatchingIndexEquiv s r)).mpr hw

end

end LogdetLean.Coherence
