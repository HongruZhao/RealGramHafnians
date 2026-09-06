import LogdetLean.GaussianLinearIndependence
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLocalCofactorCompression
/-!
# Almost-sure full rank for literal real Gaussian columns

This module transports the generic standard-Gaussian linear-independence
theorem to the literal iid real-column model used by the real Gram-hafnian
endpoint.  It also provides an arbitrary finite-index version for deleted
cofactor families.
-/

open MeasureTheory ProbabilityTheory Matrix Module

namespace LogdetLean.GramHafnian

noncomputable section

/-- Literal iid standard real Gaussian columns are linearly independent
almost surely whenever their number does not exceed the row dimension. -/
theorem ae_realLinearIndependent_pi_standardRealGaussianVectors
    (k n : ℕ) (hn : n ≤ k) :
    ∀ᵐ A ∂Measure.pi
        (fun _ : Fin n ↦ standardRealGaussianVectorMeasure k),
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2 (A j) :
          Fin n → RealCofactorSpace k) := by
  let E := RealCofactorSpace k
  have hdim : finrank ℝ E = k := by
    simp [E, RealCofactorSpace, RealGaussianEuclideanSpace]
  have hbase :
      ∀ᵐ v ∂Measure.pi (fun _ : Fin n ↦ stdGaussian E),
        LinearIndependent ℝ v := by
    apply LogdetLean.ae_linearIndependent_pi_stdGaussian
    simpa [hdim] using hn
  have hfamily : MeasurePreserving
      (fun A : Fin n → (Fin k → ℝ) ↦
        (fun j ↦ WithLp.toLp 2 (A j) : Fin n → E))
      (Measure.pi fun _ : Fin n ↦ standardRealGaussianVectorMeasure k)
      (Measure.pi fun _ : Fin n ↦ stdGaussian E) := by
    apply measurePreserving_pi
    intro j
    exact measurePreserving_toLp_standardRealGaussianVector k
  exact hfamily.quasiMeasurePreserving.ae hbase

/-- Real linear independence is a Borel event for an arbitrary finite index
type. -/
theorem measurableSet_realLinearlyIndependentFamilies
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] :
    MeasurableSet {v : ι → E | LinearIndependent ℝ v} := by
  classical
  have hdet : Measurable (fun v : ι → E ↦ (Matrix.gram ℝ v).det) := by
    have hgram : Continuous (fun v : ι → E ↦ Matrix.gram ℝ v) := by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      simpa [Matrix.gram] using (continuous_apply i).inner (continuous_apply j)
    exact hgram.matrix_det.measurable
  have heq : {v : ι → E | LinearIndependent ℝ v} =
      {v | (Matrix.gram ℝ v).det ≠ 0} := by
    ext v
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.symm
  rw [heq]
  exact (hdet.eq_const 0).setOf.compl

/-- Arbitrary finite-index version, used for the odd real cofactor subtype. -/
theorem ae_realLinearIndependent_pi_standardRealGaussianVectors_fintype
    (k : ℕ) (ι : Type*) [Fintype ι]
    (hcard : Fintype.card ι ≤ k) :
    ∀ᵐ A ∂Measure.pi
        (fun _ : ι ↦ standardRealGaussianVectorMeasure k),
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2 (A j) :
          ι → RealCofactorSpace k) := by
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let reindex : (Fin n → (Fin k → ℝ)) ≃ᵐ (ι → (Fin k → ℝ)) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι ↦ Fin k → ℝ) e
  have hmp : MeasurePreserving reindex
      (Measure.pi fun _ : Fin n ↦ standardRealGaussianVectorMeasure k)
      (Measure.pi fun _ : ι ↦ standardRealGaussianVectorMeasure k) := by
    simpa [reindex] using
      (measurePreserving_piCongrLeft
        (fun _ : ι ↦ standardRealGaussianVectorMeasure k) e)
  have hfin :
      ∀ᵐ A ∂Measure.pi
          (fun _ : Fin n ↦ standardRealGaussianVectorMeasure k),
        LinearIndependent ℝ
          (fun j ↦ WithLp.toLp 2 (A j) :
            Fin n → RealCofactorSpace k) :=
    ae_realLinearIndependent_pi_standardRealGaussianVectors k n hcard
  have hset : MeasurableSet
      {A : ι → (Fin k → ℝ) |
        LinearIndependent ℝ
          (fun j ↦ WithLp.toLp 2 (A j) :
            ι → RealCofactorSpace k)} := by
    exact (measurableSet_realLinearlyIndependentFamilies
      (E := RealCofactorSpace k) (ι := ι)).preimage (by fun_prop)
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable hset).2
  filter_upwards [hfin] with A hA
  apply (linearIndependent_equiv e).mp
  have hfun :
      ((fun j : ι ↦ WithLp.toLp 2 (reindex A j) :
          ι → RealCofactorSpace k) ∘ e) =
        (fun j : Fin n ↦ WithLp.toLp 2 (A j) :
          Fin n → RealCofactorSpace k) := by
    funext j
    have hj : reindex A (e j) = A j := by
      simpa [reindex] using
        (@MeasurableEquiv.piCongrLeft_apply_apply
          (Fin n) ι e (fun _ : ι ↦ Fin k → ℝ)
          (fun _ ↦ inferInstance) A j)
    exact congrArg (WithLp.toLp 2) hj
  rw [hfun]
  exact hA

end

end LogdetLean.GramHafnian
