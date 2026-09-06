import LogdetLean.GramHafnian.RealSymmetricGaussianLimit.RealStrictUpperEdgeBridge
import LogdetLean.GramHafnian.RealSymmetricGaussianLimit.RealGramStreamLaw
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseSymmetry
/-!
# Fixed-degree real Gram-hafnian limit

This file turns the strict-upper Gram central limit theorem into the literal
fixed-degree hafnian limit.  The deterministic bridge is exact: the hafnian
of the normalized strict-upper sum is the finite real Gram hafnian multiplied
by one inverse square-root of the row dimension for each matched pair.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace LogdetLean.GramHafnian.RealSymmetricGaussianLimit

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Decoding an ordered strict-upper coordinate and then forgetting the
order returns that coordinate. -/
@[simp] theorem realEdgesOfStrictUpper_edgeOfNe_of_lt
    {N : ℕ} (y : RealStrictUpperSpace N) {i j : Fin N} (hij : i < j) :
    realEdgesOfStrictUpper N y (edgeOfNe i j hij.ne) =
      y ⟨(i, j), hij⟩ := by
  unfold realEdgesOfStrictUpper
  apply congrArg (fun p ↦ y p)
  apply (realStrictUpperPairEdgeEquiv N).injective
  simp only [Equiv.apply_symm_apply, realStrictUpperPairEdgeEquiv_apply]
  apply Subtype.ext
  rfl

/-- A finite-type hafnian depends only on off-diagonal matrix entries. -/
theorem typeHafnian_congr_offDiagonal
    {α R : Type*} [Fintype α] [LinearOrder α] [CommSemiring R]
    {A B : Matrix α α R}
    (hAB : ∀ i j, i ≠ j → A i j = B i j) :
    typeHafnian A = typeHafnian B := by
  classical
  unfold typeHafnian typeMatchingMonomial
  apply Finset.sum_congr rfl
  intro M _hM
  apply Finset.prod_congr rfl
  intro i _hi
  exact hAB i (M i) (M.mate_ne i).symm

/-- The decoded normalized strict-upper Gram matrix agrees off the diagonal
with the scalar-normalized literal transpose Gram matrix. -/
theorem realMatrixOfEdges_normalizedPartialSum_eq_offDiagonal
    (n k : ℕ) (omega : RealStrictUpperGramStream (2 * n))
    (i j : Fin (2 * n)) (hij : i ≠ j) :
    realMatrixOfEdges
        (realEdgesOfStrictUpper (2 * n)
          (normalizedPartialSum
            (realStrictUpperGramRowStream (2 * n)) k omega)) i j =
      (Real.sqrt k)⁻¹ *
        transposeGram
          (realRowMatrix
            (realStrictUpperGramStreamToColumnMatrix n k omega)) i j := by
  classical
  rw [realMatrixOfEdges_apply_ne _ _ _ hij]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [realEdgesOfStrictUpper_edgeOfNe_of_lt _ hlt]
    rw [normalizedPartialSum_realStrictUpperGramRowStream_apply]
    simp only [transposeGram_apply, realRowMatrix,
      realStrictUpperGramStreamToColumnMatrix]
    rw [Fin.sum_univ_eq_sum_range
      (fun a : ℕ ↦ omega a i * omega a j) k]
  · rw [edgeOfNe_swap i j hij]
    rw [realEdgesOfStrictUpper_edgeOfNe_of_lt _ hgt]
    rw [normalizedPartialSum_realStrictUpperGramRowStream_apply]
    simp only [transposeGram_apply, realRowMatrix,
      realStrictUpperGramStreamToColumnMatrix]
    rw [Fin.sum_univ_eq_sum_range
      (fun a : ℕ ↦ omega a i * omega a j) k]
    apply congrArg ((Real.sqrt k)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro a _ha
    ring

/-- Exact deterministic homogeneity bridge from the normalized strict-upper
sum to the literal finite real Gram hafnian. -/
theorem realStrictUpperHafnian_normalizedPartialSum_eq_scaledGramHafnian
    (n k : ℕ) (omega : RealStrictUpperGramStream (2 * n)) :
    realStrictUpperHafnian n
        (normalizedPartialSum
          (realStrictUpperGramRowStream (2 * n)) k omega) =
      (Real.sqrt k)⁻¹ ^ n *
        realGramHafnianObservable n k
          (realStrictUpperGramStreamToColumnMatrix n k omega) := by
  unfold realStrictUpperHafnian realEdgeHafnian
  calc
    typeHafnian
        (realMatrixOfEdges
          (realEdgesOfStrictUpper (2 * n)
            (normalizedPartialSum
              (realStrictUpperGramRowStream (2 * n)) k omega))) =
        typeHafnian
          (fun i j ↦ (Real.sqrt k)⁻¹ *
            transposeGram
              (realRowMatrix
                (realStrictUpperGramStreamToColumnMatrix n k omega)) i j) := by
      apply typeHafnian_congr_offDiagonal
      exact realMatrixOfEdges_normalizedPartialSum_eq_offDiagonal n k omega
    _ = (Real.sqrt k)⁻¹ ^ n *
        typeHafnian
          (transposeGram
            (realRowMatrix
              (realStrictUpperGramStreamToColumnMatrix n k omega))) := by
      exact typeHafnian_const_mul_of_card n (by simp) _ _
    _ = (Real.sqrt k)⁻¹ ^ n *
        realGramHafnianObservable n k
          (realStrictUpperGramStreamToColumnMatrix n k omega) := by
      unfold realGramHafnianObservable gramHafnian
      rw [typeHafnian_fin_eq_hafnian]

/-- Literal central-limit normalization of the finite real Gram hafnian. -/
def normalizedRealGramHafnianSample (n k : ℕ)
    (omega : RealStrictUpperGramStream (2 * n)) : ℝ :=
  (Real.sqrt k)⁻¹ ^ n *
    realGramHafnianObservable n k
      (realStrictUpperGramStreamToColumnMatrix n k omega)

/-- The same central-limit normalization on the literal finite column model. -/
def normalizedRealGramHafnianObservable (n k : ℕ)
    (X : RealColumnMatrix n k) : ℝ :=
  (Real.sqrt k)⁻¹ ^ n * realGramHafnianObservable n k X

@[fun_prop] theorem measurable_normalizedRealGramHafnianObservable
    (n k : ℕ) : Measurable (normalizedRealGramHafnianObservable n k) := by
  exact (measurable_realGramHafnianObservable n k).const_mul
    ((Real.sqrt k)⁻¹ ^ n)

/-- Exact finite-law bridge for the normalized observable. -/
theorem map_normalizedRealGramHafnianSample_eq_columnMap (n k : ℕ) :
    Measure.map (normalizedRealGramHafnianSample n k)
        (realStrictUpperGramStreamMeasure (2 * n)) =
      Measure.map (normalizedRealGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) := by
  rw [← map_realStrictUpperGramStreamToColumnMatrix n k]
  rw [Measure.map_map
    (measurable_normalizedRealGramHafnianObservable n k)
    (measurable_realStrictUpperGramStreamToColumnMatrix n k)]
  rfl

/-- **Fixed-degree real Gram-hafnian CLT.**  The literal finite real Gram
hafnian, normalized by one inverse square root of `k` per matched pair,
converges in distribution to the hafnian of the independent-edge real
symmetric Gaussian matrix. -/
theorem tendstoInDistribution_normalizedRealGramHafnianSample (n : ℕ) :
    TendstoInDistribution
      (normalizedRealGramHafnianSample n) atTop
      (realStrictUpperHafnian n)
      (fun _ ↦ realStrictUpperGramStreamMeasure (2 * n))
      (stdGaussian (RealStrictUpperSpace (2 * n))) := by
  have h :=
    (tendstoInDistribution_realStrictUpperGramNormalizedSum_stdGaussian
      (2 * n)).continuous_comp (continuous_realStrictUpperHafnian n)
  apply h.congr
  · intro k
    exact ae_of_all _ fun omega ↦ by
      change realStrictUpperHafnian n
          (normalizedPartialSum
            (realStrictUpperGramRowStream (2 * n)) k omega) =
        normalizedRealGramHafnianSample n k omega
      exact realStrictUpperHafnian_normalizedPartialSum_eq_scaledGramHafnian
        n k omega
  · exact ae_of_all _ fun _ ↦ rfl

/-- Probability law of the normalized finite real Gram hafnian. -/
def normalizedRealGramHafnianLaw (n k : ℕ) : ProbabilityMeasure ℝ :=
  MeasureTheory.ProbabilityMeasure.map
    (⟨realStrictUpperGramStreamMeasure (2 * n), inferInstance⟩ :
      ProbabilityMeasure (RealStrictUpperGramStream (2 * n)))
    ((tendstoInDistribution_normalizedRealGramHafnianSample n).forall_aemeasurable k)

/-- Literal independent-edge real symmetric Gaussian hafnian law. -/
def realSymmetricGaussianHafnianLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  MeasureTheory.ProbabilityMeasure.map
    (⟨realEdgeGaussian (Fin (2 * n)), inferInstance⟩ :
      ProbabilityMeasure (Edge (Fin (2 * n)) → ℝ))
    measurable_realEdgeHafnian.aemeasurable

/-- Law-level form of the fixed-degree real Gram-hafnian CLT, with the target
identified exactly as the literal independent-edge symmetric Gaussian
hafnian law. -/
theorem tendsto_normalizedRealGramHafnianLaw_realEdgeHafnianLaw (n : ℕ) :
    Tendsto
      (normalizedRealGramHafnianLaw n)
      atTop
      (nhds (realSymmetricGaussianHafnianLaw n)) := by
  have h := (tendstoInDistribution_normalizedRealGramHafnianSample n).tendsto
  change Tendsto (normalizedRealGramHafnianLaw n) atTop
      (nhds
        (MeasureTheory.ProbabilityMeasure.map
          (⟨stdGaussian (RealStrictUpperSpace (2 * n)), inferInstance⟩ :
            ProbabilityMeasure (RealStrictUpperSpace (2 * n)))
          (continuous_realStrictUpperHafnian n).aemeasurable)) at h
  have htarget :
      (MeasureTheory.ProbabilityMeasure.map
        (⟨stdGaussian (RealStrictUpperSpace (2 * n)), inferInstance⟩ :
          ProbabilityMeasure (RealStrictUpperSpace (2 * n)))
        (continuous_realStrictUpperHafnian n).aemeasurable) =
      realSymmetricGaussianHafnianLaw n := by
    apply ProbabilityMeasure.toMeasure_injective
    exact map_stdGaussian_realStrictUpperHafnian n
  rw [htarget] at h
  exact h

end

end LogdetLean.GramHafnian.RealSymmetricGaussianLimit
