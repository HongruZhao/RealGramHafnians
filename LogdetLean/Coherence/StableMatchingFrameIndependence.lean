import LogdetLean.Coherence.GaussianPairFrameAlgebra
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic
/-!
# Array-level Gaussian frame/Ruben independence

This file lifts the exact one-pair independence theorem to a finite array of
independent Gaussian pairs.  The resulting array of orthonormal two-frames is
independent of the complete array of scalar Ruben coordinates.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Coordinatewise joint frame/Ruben map for a finite array of pairs. -/
def gaussianPairArrayFrameScalar (s : ℕ)
    (v : Fin s → E × E) : Fin s → (E × E) × (ℝ × (ℝ × ℝ)) :=
  fun e ↦ (gaussianPairFrame (v e), gaussianRubenCoordinates (v e))

theorem measurable_gaussianPairArrayFrameScalar (s : ℕ) :
    Measurable (gaussianPairArrayFrameScalar (E := E) s) := by
  unfold gaussianPairArrayFrameScalar
  refine measurable_pi_lambda _ fun e ↦ ?_
  exact (measurable_gaussianPairFrame.prodMk measurable_gaussianRubenCoordinates).comp
    (measurable_pi_apply e)

/-- Reorder a coordinatewise array of pairs into a pair of arrays. -/
def gaussianPairArrayReorder (s : ℕ) :
    (Fin s → (E × E) × (ℝ × (ℝ × ℝ))) →
      (Fin s → E × E) × (Fin s → ℝ × (ℝ × ℝ)) :=
  MeasurableEquiv.arrowProdEquivProdArrow (E × E) (ℝ × (ℝ × ℝ)) (Fin s)

theorem measurable_gaussianPairArrayReorder (s : ℕ) :
    Measurable (gaussianPairArrayReorder (E := E) s) := by
  exact (MeasurableEquiv.arrowProdEquivProdArrow
    (E × E) (ℝ × (ℝ × ℝ)) (Fin s)).measurable

/-- The array of two-frames. -/
def gaussianPairFrameArray (s : ℕ) (v : Fin s → E × E) : Fin s → E × E :=
  fun e ↦ gaussianPairFrame (v e)

theorem measurable_gaussianPairFrameArray (s : ℕ) :
    Measurable (gaussianPairFrameArray (E := E) s) := by
  unfold gaussianPairFrameArray
  refine measurable_pi_lambda _ fun e ↦ ?_
  exact measurable_gaussianPairFrame.comp (measurable_pi_apply e)

/-- The array of all scalar Ruben coordinates. -/
def gaussianRubenCoordinateArray (s : ℕ)
    (v : Fin s → E × E) : Fin s → ℝ × (ℝ × ℝ) :=
  fun e ↦ gaussianRubenCoordinates (v e)

theorem measurable_gaussianRubenCoordinateArray (s : ℕ) :
    Measurable (gaussianRubenCoordinateArray (E := E) s) := by
  unfold gaussianRubenCoordinateArray
  refine measurable_pi_lambda _ fun e ↦ ?_
  exact measurable_gaussianRubenCoordinates.comp (measurable_pi_apply e)

theorem gaussianPairArrayReorder_comp_frameScalar (s : ℕ) :
    gaussianPairArrayReorder (E := E) s ∘
        gaussianPairArrayFrameScalar (E := E) s =
      fun v ↦ (gaussianPairFrameArray s v, gaussianRubenCoordinateArray s v) := by
  funext v
  apply Prod.ext
  · funext e
    rfl
  · funext e
    rfl

theorem map_gaussianPairFrameArray
    (s : ℕ) :
    Measure.map (gaussianPairFrameArray (E := E) s)
        (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) =
      Measure.pi fun _ : Fin s ↦
        Measure.map gaussianPairFrame ((stdGaussian E).prod (stdGaussian E)) := by
  change Measure.map
      (fun v : Fin s → E × E ↦ fun e ↦ gaussianPairFrame (v e))
      (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) = _
  rw [Measure.pi_map_pi (fun _ ↦ measurable_gaussianPairFrame.aemeasurable)]

theorem map_gaussianRubenCoordinateArray
    (s : ℕ) :
    Measure.map (gaussianRubenCoordinateArray (E := E) s)
        (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) =
      Measure.pi fun _ : Fin s ↦
        Measure.map gaussianRubenCoordinates
          ((stdGaussian E).prod (stdGaussian E)) := by
  change Measure.map
      (fun v : Fin s → E × E ↦ fun e ↦ gaussianRubenCoordinates (v e))
      (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) = _
  rw [Measure.pi_map_pi (fun _ ↦ measurable_gaussianRubenCoordinates.aemeasurable)]

/-- Exact product law for the full array of Gaussian frames and the full
array of Ruben coordinates. -/
theorem map_gaussianPairFrameArray_rubenArray_eq_prod
    (s m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    Measure.map
        (fun v : Fin s → E × E ↦
          (gaussianPairFrameArray s v, gaussianRubenCoordinateArray s v))
        (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) =
      (Measure.pi fun _ : Fin s ↦
          Measure.map gaussianPairFrame ((stdGaussian E).prod (stdGaussian E))).prod
        (Measure.pi fun _ : Fin s ↦
          Measure.map gaussianRubenCoordinates
            ((stdGaussian E).prod (stdGaussian E))) := by
  let pairLaw : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let frameLaw : Measure (E × E) := Measure.map gaussianPairFrame pairLaw
  let scalarLaw : Measure (ℝ × (ℝ × ℝ)) :=
    Measure.map gaussianRubenCoordinates pairLaw
  have hcoordinate : ∀ e : Fin s,
      Measure.map (fun p : E × E ↦
          (gaussianPairFrame p, gaussianRubenCoordinates p)) pairLaw =
        frameLaw.prod scalarLaw := by
    intro e
    exact (indepFun_gaussianPairFrame_gaussianRubenCoordinates
      m hdim hm).map_prod_eq_prod_map_map
        measurable_gaussianPairFrame.aemeasurable
        measurable_gaussianRubenCoordinates.aemeasurable
  have hpi :
      Measure.map (gaussianPairArrayFrameScalar (E := E) s)
          (Measure.pi fun _ : Fin s ↦ pairLaw) =
        Measure.pi fun _ : Fin s ↦ frameLaw.prod scalarLaw := by
    change Measure.map
        (fun v : Fin s → E × E ↦ fun e ↦
          (gaussianPairFrame (v e), gaussianRubenCoordinates (v e)))
        (Measure.pi fun _ : Fin s ↦ pairLaw) = _
    rw [Measure.pi_map_pi (fun _ ↦
      (measurable_gaussianPairFrame.prodMk
        measurable_gaussianRubenCoordinates).aemeasurable)]
    congr 1
    funext e
    exact hcoordinate e
  calc
    Measure.map
        (fun v : Fin s → E × E ↦
          (gaussianPairFrameArray s v, gaussianRubenCoordinateArray s v))
        (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) =
        Measure.map (gaussianPairArrayReorder (E := E) s)
          (Measure.map (gaussianPairArrayFrameScalar (E := E) s)
            (Measure.pi fun _ : Fin s ↦ pairLaw)) := by
      rw [Measure.map_map (measurable_gaussianPairArrayReorder s)
        (measurable_gaussianPairArrayFrameScalar s)]
      rw [gaussianPairArrayReorder_comp_frameScalar]
    _ = Measure.map (gaussianPairArrayReorder (E := E) s)
        (Measure.pi fun _ : Fin s ↦ frameLaw.prod scalarLaw) := by rw [hpi]
    _ = (Measure.pi fun _ : Fin s ↦ frameLaw).prod
        (Measure.pi fun _ : Fin s ↦ scalarLaw) := by
      simpa [gaussianPairArrayReorder] using
        (measurePreserving_arrowProdEquivProdArrow
        (E × E) (ℝ × (ℝ × ℝ)) (Fin s)
        (fun _ ↦ frameLaw) (fun _ ↦ scalarLaw)).map_eq
    _ = _ := by rfl

/-- Independence form of the array product law. -/
theorem indepFun_gaussianPairFrameArray_rubenArray
    (s m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun (gaussianPairFrameArray (E := E) s)
      (gaussianRubenCoordinateArray (E := E) s)
      (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_gaussianPairFrameArray s).aemeasurable
    (measurable_gaussianRubenCoordinateArray s).aemeasurable).2
  rw [map_gaussianPairFrameArray (E := E) s,
    map_gaussianRubenCoordinateArray (E := E) s]
  exact map_gaussianPairFrameArray_rubenArray_eq_prod
    (E := E) s m hdim hm

/-! ## Adding the independent singleton columns -/

/-- Product sample space: `s` independent Gaussian pairs and `r` independent
singleton Gaussian columns. -/
abbrev StableMatchingBaseSample (E : Type*) (s r : ℕ) :=
  (Fin s → E × E) × (Fin r → E)

/-- Exact product law on the stable-matching base sample. -/
def stableMatchingBaseMeasure (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (s r : ℕ) :
    Measure (StableMatchingBaseSample E s r) :=
  (Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)).prod
    (Measure.pi fun _ : Fin r ↦ stdGaussian E)

/-- Pair frames together with singleton directions. -/
def stableMatchingFrameData (s r : ℕ)
    (w : StableMatchingBaseSample E s r) :
    (Fin s → E × E) × (Fin r → E) :=
  (gaussianPairFrameArray s w.1,
    fun j ↦ LogdetLean.unitDirection (w.2 j))

theorem measurable_stableMatchingFrameData (s r : ℕ) :
    Measurable (stableMatchingFrameData (E := E) s r) := by
  unfold stableMatchingFrameData
  refine ((measurable_gaussianPairFrameArray s).comp measurable_fst).prodMk ?_
  refine measurable_pi_lambda _ fun j ↦ ?_
  exact LogdetLean.measurable_unitDirection.comp
    ((measurable_pi_apply j).comp measurable_snd)

/-- The complete Ruben scalar array of the planted blocks. -/
def stableMatchingRubenData (s r : ℕ)
    (w : StableMatchingBaseSample E s r) :
    Fin s → ℝ × (ℝ × ℝ) :=
  gaussianRubenCoordinateArray s w.1

theorem measurable_stableMatchingRubenData (s r : ℕ) :
    Measurable (stableMatchingRubenData (E := E) s r) := by
  exact (measurable_gaussianRubenCoordinateArray s).comp measurable_fst

/-- Exact product law after independent singleton directions are added. -/
theorem map_stableMatchingFrameData_rubenData_eq_prod
    (s r m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    Measure.map
        (fun w : StableMatchingBaseSample E s r ↦
          (stableMatchingFrameData s r w, stableMatchingRubenData s r w))
        (stableMatchingBaseMeasure E s r) =
      (Measure.map (stableMatchingFrameData (E := E) s r)
          (stableMatchingBaseMeasure E s r)).prod
        (Measure.map (stableMatchingRubenData (E := E) s r)
          (stableMatchingBaseMeasure E s r)) := by
  let pairMeasure : Measure (Fin s → E × E) :=
    Measure.pi fun _ : Fin s ↦ (stdGaussian E).prod (stdGaussian E)
  let singletonMeasure : Measure (Fin r → E) :=
    Measure.pi fun _ : Fin r ↦ stdGaussian E
  let frameArray := gaussianPairFrameArray (E := E) s
  let scalarArray := gaussianRubenCoordinateArray (E := E) s
  let singletonDirections : (Fin r → E) → (Fin r → E) :=
    fun v j ↦ LogdetLean.unitDirection (v j)
  have hframe : Measurable frameArray := measurable_gaussianPairFrameArray s
  have hscalar : Measurable scalarArray := measurable_gaussianRubenCoordinateArray s
  have hsingle : Measurable singletonDirections := by
    refine measurable_pi_lambda _ fun j ↦ ?_
    exact LogdetLean.measurable_unitDirection.comp (measurable_pi_apply j)
  have hpair : Measure.map (fun v ↦ (frameArray v, scalarArray v)) pairMeasure =
      (Measure.map frameArray pairMeasure).prod
        (Measure.map scalarArray pairMeasure) := by
    rw [map_gaussianPairFrameArray (E := E) s,
      map_gaussianRubenCoordinateArray (E := E) s]
    simpa [pairMeasure, frameArray, scalarArray] using
      map_gaussianPairFrameArray_rubenArray_eq_prod (E := E) s m hdim hm
  have hfirstMap :
      Measure.map
          (Prod.map (fun v ↦ (frameArray v, scalarArray v)) singletonDirections)
          (pairMeasure.prod singletonMeasure) =
        ((Measure.map frameArray pairMeasure).prod
          (Measure.map scalarArray pairMeasure)).prod
            (Measure.map singletonDirections singletonMeasure) := by
    calc
      Measure.map
          (Prod.map (fun v ↦ (frameArray v, scalarArray v)) singletonDirections)
          (pairMeasure.prod singletonMeasure) =
          (Measure.map (fun v ↦ (frameArray v, scalarArray v)) pairMeasure).prod
            (Measure.map singletonDirections singletonMeasure) :=
        (Measure.map_prod_map pairMeasure singletonMeasure
          (hframe.prodMk hscalar) hsingle).symm
      _ = _ := by rw [hpair]
  let reorder :
      ((Fin s → E × E) × (Fin s → ℝ × (ℝ × ℝ))) ×
          (Fin r → E) →
        ((Fin s → E × E) × (Fin r → E)) ×
          (Fin s → ℝ × (ℝ × ℝ)) :=
    middleToLast
  have hreorder : Measurable reorder := measurable_middleToLast
  have hfun :
      (fun w : StableMatchingBaseSample E s r ↦
        (stableMatchingFrameData s r w, stableMatchingRubenData s r w)) =
        reorder ∘
          Prod.map (fun v ↦ (frameArray v, scalarArray v)) singletonDirections := by
    funext w
    rfl
  have hjoint :
      Measure.map
          (fun w : StableMatchingBaseSample E s r ↦
            (stableMatchingFrameData s r w, stableMatchingRubenData s r w))
          (stableMatchingBaseMeasure E s r) =
        ((Measure.map frameArray pairMeasure).prod
          (Measure.map singletonDirections singletonMeasure)).prod
            (Measure.map scalarArray pairMeasure) := by
    have hprodMap : Measurable
        (Prod.map (fun v ↦ (frameArray v, scalarArray v)) singletonDirections) :=
      (hframe.prodMk hscalar).prodMap hsingle
    rw [hfun]
    change Measure.map
        (reorder ∘ Prod.map (fun v ↦ (frameArray v, scalarArray v)) singletonDirections)
        (pairMeasure.prod singletonMeasure) = _
    rw [← Measure.map_map hreorder hprodMap]
    change Measure.map reorder
        (Measure.map
          (Prod.map (fun v ↦ (frameArray v, scalarArray v)) singletonDirections)
          (pairMeasure.prod singletonMeasure)) = _
    rw [hfirstMap]
    exact map_middleToLast_prod
      (Measure.map frameArray pairMeasure)
      (Measure.map scalarArray pairMeasure)
      (Measure.map singletonDirections singletonMeasure)
  have hframeMap :
      Measure.map (stableMatchingFrameData (E := E) s r)
          (stableMatchingBaseMeasure E s r) =
        (Measure.map frameArray pairMeasure).prod
          (Measure.map singletonDirections singletonMeasure) := by
    change Measure.map (fun w ↦ (frameArray w.1, singletonDirections w.2))
        (pairMeasure.prod singletonMeasure) = _
    exact (Measure.map_prod_map pairMeasure singletonMeasure hframe hsingle).symm
  have hscalarMap :
      Measure.map (stableMatchingRubenData (E := E) s r)
          (stableMatchingBaseMeasure E s r) =
        Measure.map scalarArray pairMeasure := by
    change Measure.map (scalarArray ∘ Prod.fst)
        (pairMeasure.prod singletonMeasure) = Measure.map scalarArray pairMeasure
    rw [← Measure.map_map hscalar measurable_fst, Measure.map_fst_prod]
    simp
  rw [hjoint, hframeMap, hscalarMap]

/-- The complete stable-matching frame data are independent of all planted
block Ruben coordinates. -/
theorem indepFun_stableMatchingFrameData_rubenData
    (s r m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun (stableMatchingFrameData (E := E) s r)
      (stableMatchingRubenData (E := E) s r)
      (stableMatchingBaseMeasure E s r) := by
  let _ : IsProbabilityMeasure (stableMatchingBaseMeasure E s r) := by
    unfold stableMatchingBaseMeasure
    infer_instance
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_stableMatchingFrameData s r).aemeasurable
    (measurable_stableMatchingRubenData s r).aemeasurable).2
  exact map_stableMatchingFrameData_rubenData_eq_prod
    (E := E) s r m hdim hm

/-- Flatten the pair-frame/singleton data into the column family used by the
determinant decomposition. -/
def stableMatchingFrameColumns (s r : ℕ)
    (d : (Fin s → E × E) × (Fin r → E)) :
    Sum (Fin 2 × Fin s) (Fin r) → E
  | Sum.inl (i, e) => if i = 0 then (d.1 e).1 else (d.1 e).2
  | Sum.inr j => d.2 j

theorem measurable_stableMatchingFrameColumns (s r : ℕ) :
    Measurable (stableMatchingFrameColumns (E := E) s r) := by
  unfold stableMatchingFrameColumns
  refine measurable_pi_lambda _ fun i ↦ ?_
  rcases i with ⟨i, e⟩ | j
  · fin_cases i
    · exact measurable_fst.comp ((measurable_pi_apply e).comp measurable_fst)
    · exact measurable_snd.comp ((measurable_pi_apply e).comp measurable_fst)
  · exact (measurable_pi_apply j).comp measurable_snd

/-- Exact finite-sample separation in the column-family representation. -/
theorem indepFun_stableMatchingFrameColumns_rubenData
    (s r m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun
      (stableMatchingFrameColumns (E := E) s r ∘
        stableMatchingFrameData (E := E) s r)
      (stableMatchingRubenData (E := E) s r)
      (stableMatchingBaseMeasure E s r) := by
  exact (indepFun_stableMatchingFrameData_rubenData
    (E := E) s r m hdim hm).comp
      (measurable_stableMatchingFrameColumns s r) measurable_id

/-- Flatten the original independent Gaussian pairs and singleton columns. -/
def stableMatchingRawColumns (s r : ℕ)
    (w : StableMatchingBaseSample E s r) :
    Sum (Fin 2 × Fin s) (Fin r) → E
  | Sum.inl (i, e) => if i = 0 then (w.1 e).1 else (w.1 e).2
  | Sum.inr j => w.2 j

theorem measurable_stableMatchingRawColumns (s r : ℕ) :
    Measurable (stableMatchingRawColumns (E := E) s r) := by
  unfold stableMatchingRawColumns
  refine measurable_pi_lambda _ fun i ↦ ?_
  rcases i with ⟨i, e⟩ | j
  · fin_cases i
    · exact measurable_fst.comp ((measurable_pi_apply e).comp measurable_fst)
    · exact measurable_snd.comp ((measurable_pi_apply e).comp measurable_fst)
  · exact (measurable_pi_apply j).comp measurable_snd

/-- The abstract frame data constructed from the independent blocks agree
pointwise with the deterministic frame extraction applied to the flattened
raw columns. -/
theorem stableMatchingFrameColumns_frameData_eq_frameFamily
    (s r : ℕ) (w : StableMatchingBaseSample E s r) :
    stableMatchingFrameColumns s r (stableMatchingFrameData s r w) =
      stableMatchingFrameFamily (E := E) s r
        (stableMatchingRawColumns s r w) := by
  funext i
  rcases i with ⟨i, e⟩ | j
  · fin_cases i <;> rfl
  · rfl

/-- Log determinant of the orientation/frame part of the sample correlation
matrix.  This omits the internal sample-angle factors of the planted pairs. -/
def stableMatchingFrameLogdet (s r : ℕ)
    (w : StableMatchingBaseSample E s r) : ℝ :=
  Real.log (normalizedGram
    (stableMatchingFrameColumns s r (stableMatchingFrameData s r w))).det

/-- Measurability of the normalized-Gram determinant for the sum-indexed
stable matching family. -/
theorem measurable_det_normalizedGram_stableMatchingIndex (s r : ℕ) :
    Measurable (fun v : Sum (Fin 2 × Fin s) (Fin r) → E ↦
      (normalizedGram v).det) := by
  rw [show (fun v : Sum (Fin 2 × Fin s) (Fin r) → E ↦
      (normalizedGram v).det) =
      fun v ↦ (Matrix.gram ℝ v).det / ∏ i, ‖v i‖ ^ 2 by
    funext v
    exact det_normalizedGram v]
  have hgram : Continuous (fun v : Sum (Fin 2 × Fin s) (Fin r) → E ↦
      Matrix.gram ℝ v) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simpa [Matrix.gram] using (continuous_apply i).inner (continuous_apply j)
  exact hgram.matrix_det.measurable.div (by fun_prop)

theorem measurable_stableMatchingFrameLogdet (s r : ℕ) :
    Measurable (stableMatchingFrameLogdet (E := E) s r) := by
  unfold stableMatchingFrameLogdet
  exact ((measurable_det_normalizedGram_stableMatchingIndex
    (E := E) s r).log).comp
      ((measurable_stableMatchingFrameColumns s r).comp
        (measurable_stableMatchingFrameData s r))

/-- The exact frame log determinant is independent of the full array of
planted-block Ruben coordinates.  This is the finite-sample separation at the
heart of the stable matching theorem. -/
theorem indepFun_stableMatchingFrameLogdet_rubenData
    (s r m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun (stableMatchingFrameLogdet (E := E) s r)
      (stableMatchingRubenData (E := E) s r)
      (stableMatchingBaseMeasure E s r) := by
  have h := indepFun_stableMatchingFrameColumns_rubenData
    (E := E) s r m hdim hm
  exact h.comp
    ((measurable_det_normalizedGram_stableMatchingIndex
      (E := E) s r).log)
    measurable_id

end

end LogdetLean.Coherence
