import LogdetLean.WishartBetaGammaFactors
import LogdetLean.GaussianSampleCorrelation
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
/-!
# Independent-column form of standard Gaussian data

The Gaussian scatter model is defined row by row, whereas the Bartlett proof
uses independent variable columns.  This file supplies the exact
measure-preserving bridge.  Its only probabilistic input is Mathlib's product
measure and the orthogonal invariance of `stdGaussian`.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory WithLp

/-- Reading a right-nested iid tuple as a `Fin n` family preserves the
ordinary finite product measure. -/
theorem measurePreserving_nestedTupleToFin
    {E : Type*} [MeasurableSpace E] (mu : Measure E) [SigmaFinite mu] :
    ∀ n, MeasurePreserving (nestedTupleToFin (α := E) n)
      (nestedProductMeasure mu n) (Measure.pi fun _ : Fin n ↦ mu) := by
  intro n
  induction n with
  | zero =>
      refine ⟨measurable_nestedTupleToFin (α := E) 0, ?_⟩
      rw [nestedProductMeasure, Measure.map_dirac'
        (measurable_nestedTupleToFin (α := E) 0)]
      rw [Measure.pi_of_empty (fun _ : Fin 0 ↦ mu)
        (nestedTupleToFin 0 (ULift.up Unit.unit))]
  | succ n ih =>
      have hprod := ih.prod (MeasurePreserving.id mu)
      have hswap : MeasurePreserving Prod.swap
          ((Measure.pi fun _ : Fin n ↦ mu).prod mu)
          (mu.prod (Measure.pi fun _ : Fin n ↦ mu)) :=
        Measure.measurePreserving_swap
      have hsplit :=
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ mu) (Fin.last n)).symm
      have hcomp := hsplit.comp (hswap.comp hprod)
      refine ⟨measurable_nestedTupleToFin (α := E) (n + 1), ?_⟩
      have hfun :
          (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) ↦ E) (Fin.last n)).symm ∘
              Prod.swap ∘
              Prod.map (nestedTupleToFin (α := E) n) id =
            nestedTupleToFin (α := E) (n + 1) := by
        funext z
        ext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [nestedTupleToFin]
        · simp [nestedTupleToFin]
      rw [← hfun]
      exact hcomp.map_eq

/-- Pushforward form of the preceding measure-preserving equivalence. -/
theorem map_nestedTupleToFin_nestedProductMeasure
    {E : Type*} [MeasurableSpace E] (mu : Measure E) [SigmaFinite mu] (n : ℕ) :
    Measure.map (nestedTupleToFin (α := E) n)
        (nestedProductMeasure mu n) =
      Measure.pi fun _ : Fin n ↦ mu :=
  (measurePreserving_nestedTupleToFin mu n).map_eq

/-! ## Transposing a finite iid array -/

/-- Transpose a finite function-valued array.  The measurable structure on
both sides is the coordinatewise product structure. -/
def piTransposeMeasurableEquiv (I J E : Type*) [MeasurableSpace E] :
    (I → J → E) ≃ᵐ (J → I → E) where
  toFun x j i := x i j
  invFun x i j := x j i
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ fun j ↦ measurable_pi_lambda _ fun i ↦ ?_
    exact (measurable_pi_apply j).comp (measurable_pi_apply i)
  measurable_invFun := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    exact (measurable_pi_apply i).comp (measurable_pi_apply j)

@[simp]
theorem piTransposeMeasurableEquiv_apply
    {I J E : Type*} [MeasurableSpace E] (x : I → J → E) (j : J) (i : I) :
    piTransposeMeasurableEquiv I J E x j i = x i j := rfl

/-- A finite iid scalar array remains an iid array after transposition.  This
is proved from Mathlib's infinite-product curry and reindexing theorems, then
specialized back to finite `Measure.pi` products. -/
theorem map_pi_pi_piTranspose
    {I J E : Type*} [Fintype I] [Fintype J] [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] :
    Measure.map (piTransposeMeasurableEquiv I J E)
        (Measure.pi fun _ : I ↦ Measure.pi fun _ : J ↦ mu) =
      Measure.pi fun _ : J ↦ Measure.pi fun _ : I ↦ mu := by
  let uncurryRows := (MeasurableEquiv.curry I J E).symm
  let swapIndices := MeasurableEquiv.piCongrLeft
    (fun _ : J × I ↦ E) (Equiv.prodComm I J)
  let curryColumns := MeasurableEquiv.curry J I E
  have hfun :
      curryColumns ∘ swapIndices ∘ uncurryRows =
        piTransposeMeasurableEquiv I J E := by
    funext x
    ext j i
    rfl
  have huncurry :
      Measure.map uncurryRows
          (Measure.infinitePi fun _ : I ↦
            Measure.infinitePi fun _ : J ↦ mu) =
        Measure.infinitePi fun _ : I × J ↦ mu := by
    simpa only [uncurryRows] using
      (Measure.infinitePi_map_curry_symm
        (fun _ : I ↦ fun _ : J ↦ mu))
  have hswap :
      Measure.map swapIndices
          (Measure.infinitePi fun _ : I × J ↦ mu) =
        Measure.infinitePi fun _ : J × I ↦ mu := by
    simpa only [swapIndices] using
      (Measure.infinitePi_map_piCongrLeft
        (fun _ : J × I ↦ mu) (Equiv.prodComm I J))
  have hcurry :
      Measure.map curryColumns
          (Measure.infinitePi fun _ : J × I ↦ mu) =
        Measure.infinitePi fun _ : J ↦
          Measure.infinitePi fun _ : I ↦ mu := by
    simpa only [curryColumns] using
      (Measure.infinitePi_map_curry
        (fun _ : J ↦ fun _ : I ↦ mu))
  rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  simp_rw [← Measure.infinitePi_eq_pi]
  rw [← hfun]
  calc
    Measure.map (curryColumns ∘ swapIndices ∘ uncurryRows)
        (Measure.infinitePi fun _ : I ↦ Measure.infinitePi fun _ : J ↦ mu) =
      Measure.map curryColumns
        (Measure.map swapIndices
          (Measure.map uncurryRows
            (Measure.infinitePi fun _ : I ↦
              Measure.infinitePi fun _ : J ↦ mu))) := by
        rw [Measure.map_map, Measure.map_map]
        · rfl
        all_goals fun_prop
    _ = Measure.map curryColumns
        (Measure.map swapIndices
          (Measure.infinitePi fun _ : I × J ↦ mu)) := by
      rw [huncurry]
    _ = Measure.map curryColumns
        (Measure.infinitePi fun _ : J × I ↦ mu) := by
      rw [hswap]
    _ = Measure.infinitePi fun _ : J ↦
        Measure.infinitePi fun _ : I ↦ mu := by
      exact hcurry

/-! ## Standard Gaussian rows are independent standard Gaussian columns -/

/-- Turn a scalar array into row-valued Euclidean observations. -/
def rawRowsToGaussianData (m p : ℕ) :
    (Fin m → Fin p → ℝ) → GaussianData m p :=
  fun x k ↦ WithLp.toLp 2 (x k)

theorem measurable_rawRowsToGaussianData (m p : ℕ) :
    Measurable (rawRowsToGaussianData m p) := by
  unfold rawRowsToGaussianData
  fun_prop

/-- Turn the transposed scalar array into Euclidean variable columns. -/
def rawColumnsToEuclidean (m p : ℕ) :
    (Fin p → Fin m → ℝ) →
      (Fin p → EuclideanSpace ℝ (Fin m)) :=
  fun x j ↦ WithLp.toLp 2 (x j)

theorem measurable_rawColumnsToEuclidean (m p : ℕ) :
    Measurable (rawColumnsToEuclidean m p) := by
  unfold rawColumnsToEuclidean
  fun_prop

/-- Rowwise application of `toLp` sends the scalar iid product to the
standard Gaussian row-product measure. -/
theorem map_rawRowsToGaussianData (m p : ℕ) :
    Measure.map (rawRowsToGaussianData m p)
        (Measure.pi fun _ : Fin m ↦
          Measure.pi fun _ : Fin p ↦ gaussianReal 0 1) =
      standardGaussianDataMeasure m p := by
  let _ (k : Fin m) : IsProbabilityMeasure
      ((Measure.pi fun _ : Fin p ↦ gaussianReal 0 1).map
        (WithLp.toLp 2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold standardGaussianDataMeasure
  change Measure.map
      (fun x : Fin m → Fin p → ℝ ↦ fun k ↦ WithLp.toLp 2 (x k))
      (Measure.pi fun _ : Fin m ↦
        Measure.pi fun _ : Fin p ↦ gaussianReal 0 1) =
    Measure.pi fun _ : Fin m ↦
      stdGaussian (EuclideanSpace ℝ (Fin p))
  rw [Measure.pi_map_pi (fun _ ↦
    (show Measurable (WithLp.toLp 2 :
      (Fin p → ℝ) → EuclideanSpace ℝ (Fin p)) by fun_prop).aemeasurable)]
  congr 1
  funext k
  exact map_pi_eq_stdGaussian

/-- Columnwise application of `toLp` sends the transposed scalar iid product
to independent standard Gaussian columns. -/
theorem map_rawColumnsToEuclidean (m p : ℕ) :
    Measure.map (rawColumnsToEuclidean m p)
        (Measure.pi fun _ : Fin p ↦
          Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) =
      Measure.pi fun _ : Fin p ↦
        stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let _ (j : Fin p) : IsProbabilityMeasure
      ((Measure.pi fun _ : Fin m ↦ gaussianReal 0 1).map
        (WithLp.toLp 2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  change Measure.map
      (fun x : Fin p → Fin m → ℝ ↦ fun j ↦ WithLp.toLp 2 (x j))
      (Measure.pi fun _ : Fin p ↦
        Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) =
    Measure.pi fun _ : Fin p ↦
      stdGaussian (EuclideanSpace ℝ (Fin m))
  rw [Measure.pi_map_pi (fun _ ↦
    (show Measurable (WithLp.toLp 2 :
      (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) by fun_prop).aemeasurable)]
  congr 1
  funext j
  exact map_pi_eq_stdGaussian

/-- Exact row-to-column law for a finite standard Gaussian data matrix:
the variable columns are mutually independent standard Gaussian vectors. -/
theorem map_dataColumns_standardGaussianDataMeasure (m p : ℕ) :
    Measure.map dataColumns (standardGaussianDataMeasure m p) =
      Measure.pi fun _ : Fin p ↦
        stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let rawRows : Measure (Fin m → Fin p → ℝ) :=
    Measure.pi fun _ : Fin m ↦
      Measure.pi fun _ : Fin p ↦ gaussianReal 0 1
  let rawColumns : Measure (Fin p → Fin m → ℝ) :=
    Measure.pi fun _ : Fin p ↦
      Measure.pi fun _ : Fin m ↦ gaussianReal 0 1
  have hrow : Measure.map (rawRowsToGaussianData m p) rawRows =
      standardGaussianDataMeasure m p := by
    exact map_rawRowsToGaussianData m p
  have htranspose :
      Measure.map (piTransposeMeasurableEquiv (Fin m) (Fin p) ℝ) rawRows =
        rawColumns := by
    exact map_pi_pi_piTranspose
      (I := Fin m) (J := Fin p) (gaussianReal 0 1)
  have hcolumn : Measure.map (rawColumnsToEuclidean m p) rawColumns =
      Measure.pi fun _ : Fin p ↦
        stdGaussian (EuclideanSpace ℝ (Fin m)) := by
    exact map_rawColumnsToEuclidean m p
  rw [← hrow]
  calc
    Measure.map dataColumns
        (Measure.map (rawRowsToGaussianData m p) rawRows) =
      Measure.map (dataColumns ∘ rawRowsToGaussianData m p) rawRows := by
        rw [Measure.map_map measurable_dataColumns
          (measurable_rawRowsToGaussianData m p)]
    _ = Measure.map
        (rawColumnsToEuclidean m p ∘
          piTransposeMeasurableEquiv (Fin m) (Fin p) ℝ) rawRows := by
      rfl
    _ = Measure.map (rawColumnsToEuclidean m p)
        (Measure.map (piTransposeMeasurableEquiv (Fin m) (Fin p) ℝ)
          rawRows) := by
      rw [Measure.map_map]
      · exact measurable_rawColumnsToEuclidean m p
      · exact (piTransposeMeasurableEquiv (Fin m) (Fin p) ℝ).measurable
    _ = Measure.map (rawColumnsToEuclidean m p) rawColumns := by
      rw [htranspose]
    _ = Measure.pi fun _ : Fin p ↦
        stdGaussian (EuclideanSpace ℝ (Fin m)) := hcolumn

end

end LogdetLean
