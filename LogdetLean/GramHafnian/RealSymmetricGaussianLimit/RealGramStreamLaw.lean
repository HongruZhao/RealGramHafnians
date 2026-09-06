import LogdetLean.GramHafnian.RealSymmetricGaussianLimit.RealEdgeGramCLT
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralCofactor
import LogdetLean.GaussianColumnProduct
/-!
# Exact finite law of the real strict-upper Gram stream

The first `k` rows of the canonical iid stream are transposed into the
column-major matrix used by the finite real Gram-hafnian theorem.  This file
proves both the exact product-law identity and the coordinate formula for the
normalized strict-upper quadratic sum.
-/

open MeasureTheory ProbabilityTheory
open scoped Real BigOperators

namespace LogdetLean.GramHafnian.RealSymmetricGaussianLimit

open LogdetLean
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Transpose the first `k` rows of the canonical stream into the literal
column-major real Gaussian matrix. -/
def realStrictUpperGramStreamToColumnMatrix (n k : ℕ)
    (omega : RealStrictUpperGramStream (2 * n)) : RealColumnMatrix n k :=
  fun j a ↦ omega a j

@[fun_prop] theorem measurable_realStrictUpperGramStreamToColumnMatrix
    (n k : ℕ) :
    Measurable (realStrictUpperGramStreamToColumnMatrix n k) := by
  unfold realStrictUpperGramStreamToColumnMatrix
  fun_prop

/-- Exact law bridge from the infinite iid row stream to the finite literal
column matrix. -/
theorem map_realStrictUpperGramStreamToColumnMatrix (n k : ℕ) :
    Measure.map (realStrictUpperGramStreamToColumnMatrix n k)
        (realStrictUpperGramStreamMeasure (2 * n)) =
      standardRealGaussianColumnMatrixMeasure n k := by
  let restrictRows : RealStrictUpperGramStream (2 * n) →
      (Fin k → Fin (2 * n) → ℝ) :=
    fun omega a j ↦ omega a j
  let transposeRows :=
    piTransposeMeasurableEquiv (Fin k) (Fin (2 * n)) ℝ
  have hrestrict :
      Measure.map restrictRows
          (realStrictUpperGramStreamMeasure (2 * n)) =
        Measure.pi
          (fun _ : Fin k ↦ standardRealGaussianProduct (Fin (2 * n))) := by
    simpa only [realStrictUpperGramStreamMeasure,
      standardRealGaussianProduct, Measure.infinitePi_eq_pi, restrictRows] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ ↦
          Measure.pi fun _ : Fin (2 * n) ↦ gaussianReal 0 1)
        (f := fun a : Fin k ↦ a.1) Fin.val_injective)
  have htranspose :
      Measure.map transposeRows
          (Measure.pi
            (fun _ : Fin k ↦ standardRealGaussianProduct (Fin (2 * n)))) =
        standardRealGaussianColumnMatrixMeasure n k := by
    unfold standardRealGaussianProduct
      standardRealGaussianColumnMatrixMeasure
      standardRealGaussianVectorMeasure
    exact map_pi_pi_piTranspose
      (I := Fin k) (J := Fin (2 * n)) (gaussianReal 0 1)
  rw [← htranspose, ← hrestrict]
  rw [Measure.map_map]
  · apply Measure.map_congr
    filter_upwards with omega
    rfl
  · exact transposeRows.measurable
  · unfold restrictRows
    fun_prop

/-- Coordinate formula for the normalized real strict-upper Gram sum. -/
theorem normalizedPartialSum_realStrictUpperGramRowStream_apply
    (N k : ℕ) (omega : RealStrictUpperGramStream N)
    (p : RealStrictUpperPair N) :
    normalizedPartialSum (realStrictUpperGramRowStream N) k omega p =
      (Real.sqrt k)⁻¹ *
        ∑ i ∈ Finset.range k, omega i p.1.1 * omega i p.1.2 := by
  classical
  unfold normalizedPartialSum realStrictUpperGramRowStream
    realStrictUpperGramRow
  simp only [Finset.smul_sum, Finset.mul_sum]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  change (Real.sqrt k)⁻¹ •
      (omega i p.1.1 * omega i p.1.2) = _
  rw [smul_eq_mul]

end

end LogdetLean.GramHafnian.RealSymmetricGaussianLimit
