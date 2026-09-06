import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic
import LogdetLean.GaussianSubspace
/-!
# Almost-sure linear independence of Gaussian columns

The full sequential statement is developed in the Gaussian-to-Beta bridge.
This file first records the measurable event used there.  Expressing linear
independence through the nonvanishing Gram determinant avoids any
measurability question about bases or Gram--Schmidt choices.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The set of linearly independent `n`-tuples in `E`. -/
def linearlyIndependentTuples (n : ℕ) : Set (Fin n → E) :=
  {v | LinearIndependent ℝ v}

/-- Linear independence of a finite family is a measurable condition. -/
theorem measurableSet_linearlyIndependentTuples (n : ℕ) :
    MeasurableSet (linearlyIndependentTuples (E := E) n) := by
  have hdet : Measurable (fun v : Fin n → E ↦ (Matrix.gram ℝ v).det) := by
    have hgram : Continuous (fun v : Fin n → E ↦ Matrix.gram ℝ v) := by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      simpa [Matrix.gram] using (continuous_apply i).inner (continuous_apply j)
    exact hgram.matrix_det.measurable
  rw [linearlyIndependentTuples]
  have heq : {v : Fin n → E | LinearIndependent ℝ v} =
      {v | (Matrix.gram ℝ v).det ≠ 0} := by
    ext v
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.symm
  rw [heq]
  exact (hdet.eq_const 0).setOf.compl

set_option linter.unusedSectionVars false in
/-- The span of `n` linearly independent vectors is proper whenever
`n < finrank E`. -/
theorem span_range_ne_top_of_linearIndependent {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (hn : n < finrank ℝ E) :
    Submodule.span ℝ (Set.range v) ≠ ⊤ := by
  intro htop
  have hfin : finrank ℝ (Submodule.span ℝ (Set.range v)) = n := by
    simpa using finrank_span_eq_card hv
  have hall : finrank ℝ (Submodule.span ℝ (Set.range v)) = finrank ℝ E := by
    rw [htop, finrank_top]
  omega

/-- Given a fixed linearly independent past of length below the ambient
dimension, a fresh standard Gaussian column extends it linearly independently
with probability one. -/
theorem ae_linearIndependent_snoc_stdGaussian {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (hn : n < finrank ℝ E) :
    ∀ᵐ x ∂(stdGaussian E), LinearIndependent ℝ (Fin.snoc v x) := by
  rw [ae_iff]
  have hproper := span_range_ne_top_of_linearIndependent hv hn
  have hnull := stdGaussian_proper_submodule_null
    (Submodule.span ℝ (Set.range v)) hproper
  have hbad : {x : E | ¬ LinearIndependent ℝ (Fin.snoc v x)} =
      (Submodule.span ℝ (Set.range v) : Set E) := by
    ext x
    simp [linearIndependent_finSnoc, hv]
  rw [hbad]
  exact hnull

/-- At most `finrank E` independent standard Gaussian columns are linearly
independent almost surely.  This is the rank statement used at every stage of
the sequential Beta-factor construction. -/
theorem ae_linearIndependent_pi_stdGaussian (n : ℕ) (hn : n ≤ finrank ℝ E) :
    ∀ᵐ v ∂(Measure.pi fun _ : Fin n ↦ stdGaussian E), LinearIndependent ℝ v := by
  induction n with
  | zero =>
      exact Filter.Eventually.of_forall fun _ ↦ linearIndependent_empty_type
  | succ n ih =>
      have hnlt : n < finrank ℝ E := Nat.lt_of_succ_le hn
      have hpast :
          ∀ᵐ v ∂(Measure.pi fun _ : Fin n ↦ stdGaussian E), LinearIndependent ℝ v :=
        ih (Nat.le_of_lt hnlt)
      have hsnocMeas : Measurable (fun z : (Fin n → E) × E ↦
          @Fin.snoc n (fun _ : Fin (n + 1) ↦ E) z.1 z.2) := by
        fun_prop
      have hset : MeasurableSet
          {z : (Fin n → E) × E | LinearIndependent ℝ
            (@Fin.snoc n (fun _ : Fin (n + 1) ↦ E) z.1 z.2)} := by
        exact (measurableSet_linearlyIndependentTuples (E := E) (n + 1)).preimage hsnocMeas
      have hprod :
          ∀ᵐ z ∂((Measure.pi fun _ : Fin n ↦ stdGaussian E).prod (stdGaussian E)),
            LinearIndependent ℝ
              (@Fin.snoc n (fun _ : Fin (n + 1) ↦ E) z.1 z.2) := by
        rw [Measure.ae_prod_iff_ae_ae hset]
        filter_upwards [hpast] with v hv
        exact ae_linearIndependent_snoc_stdGaussian hv hnlt
      let split : (Fin (n + 1) → E) → (Fin n → E) × E :=
        fun v ↦ (Fin.init v, v (Fin.last n))
      have hsplit : MeasurePreserving split
          (Measure.pi fun _ : Fin (n + 1) ↦ stdGaussian E)
          ((Measure.pi fun _ : Fin n ↦ stdGaussian E).prod (stdGaussian E)) := by
        have hfirst := measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ stdGaussian E) (Fin.last n)
        have hcomp := (Measure.measurePreserving_swap).comp hfirst
        simpa [split, Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply,
          Fin.succAbove_last] using hcomp
      have hcomp :
          ∀ᵐ v ∂(Measure.pi fun _ : Fin (n + 1) ↦ stdGaussian E),
            LinearIndependent ℝ (Fin.snoc (Fin.init v) (v (Fin.last n))) := by
        have hmapped :
            ∀ᵐ z ∂(Measure.map split
                (Measure.pi fun _ : Fin (n + 1) ↦ stdGaussian E)),
              LinearIndependent ℝ
                (@Fin.snoc n (fun _ : Fin (n + 1) ↦ E) z.1 z.2) := by
          rw [hsplit.map_eq]
          exact hprod
        exact (ae_map_iff hsplit.measurable.aemeasurable hset).mp hmapped
      filter_upwards [hcomp] with v hv
      simpa using hv

end

end LogdetLean
