import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorMeasurable
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealConditionalResolventSmallBall
/-!
# Literal real Gaussian Gram-hafnian cofactors

This is the beta-one counterpart of the existing complex literal model.  It
uses the same finite matching expansion but keeps every column, cofactor and
energy in `ℝ`.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- A literal family of `2n` real columns in `ℝ^k`. -/
abbrev RealColumnMatrix (n k : ℕ) :=
  Fin (2 * n) → (Fin k → ℝ)

/-- The corresponding `k × 2n` real matrix. -/
def realRowMatrix {n k : ℕ} (X : RealColumnMatrix n k) :
    Matrix (Fin k) (Fin (2 * n)) ℝ :=
  fun a i ↦ X i a

/-- Product law of independent standard real Gaussian columns. -/
def standardRealGaussianColumnMatrixMeasure (n k : ℕ) :
    Measure (RealColumnMatrix n k) :=
  Measure.pi fun _ : Fin (2 * n) ↦ standardRealGaussianVectorMeasure k

instance (n k : ℕ) : SigmaFinite
    (standardRealGaussianColumnMatrixMeasure n k) := by
  unfold standardRealGaussianColumnMatrixMeasure
  infer_instance

instance (n k : ℕ) : IsProbabilityMeasure
    (standardRealGaussianColumnMatrixMeasure n k) := by
  unfold standardRealGaussianColumnMatrixMeasure
  infer_instance

/-- The literal beta-one Gram-hafnian observable. -/
def realGramHafnianObservable (n k : ℕ) (X : RealColumnMatrix n k) : ℝ :=
  gramHafnian (realRowMatrix X)

/-- The real odd hafnian-cofactor vector after exposing the last column. -/
def realOddHafnianCofactorVector {r k : ℕ} (hr : 1 ≤ r)
    (X : RealColumnMatrix r k) : OddCofactorIndex r hr → ℝ :=
  fun j ↦ hafnianPairCofactor (transposeGram (realRowMatrix X))
    (evenLastIndex r hr) j

/-- The real coefficient vector `A_r C_r`. -/
def realOddCofactorColumnCombination {r k : ℕ} (hr : 1 ≤ r)
    (X : RealColumnMatrix r k) : Fin k → ℝ :=
  fun a ↦ ∑ j : OddCofactorIndex r hr,
    X j.1 a * realOddHafnianCofactorVector hr X j

/-- Squared Euclidean norm `W_r = ||C_r||^2`. -/
def realOddCofactorW {r k : ℕ} (hr : 1 ≤ r)
    (X : RealColumnMatrix r k) : ℝ :=
  ∑ j : OddCofactorIndex r hr,
    (realOddHafnianCofactorVector hr X j) ^ 2

/-- Conditional energy `V_r = ||A_r C_r||^2`. -/
def realOddCofactorV {r k : ℕ} (hr : 1 ≤ r)
    (X : RealColumnMatrix r k) : ℝ :=
  ∑ a : Fin k, (realOddCofactorColumnCombination hr X a) ^ 2

theorem realOddCofactorW_nonneg {r k : ℕ} (hr : 1 ≤ r)
    (X : RealColumnMatrix r k) : 0 ≤ realOddCofactorW hr X := by
  unfold realOddCofactorW
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem realOddCofactorV_nonneg {r k : ℕ} (hr : 1 ≤ r)
    (X : RealColumnMatrix r k) : 0 ≤ realOddCofactorV hr X := by
  unfold realOddCofactorV
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- At level one the unique real cofactor is the empty hafnian, hence one. -/
theorem realOddHafnianCofactorVector_level_one
    {k : ℕ} (X : RealColumnMatrix 1 k)
    (j : OddCofactorIndex 1 (by omega)) :
    realOddHafnianCofactorVector (by omega) X j = 1 := by
  letI : IsEmpty
      (TypePerfectMatching.PairComplement (evenLastIndex 1 (by omega)) j.1) :=
    ⟨fun p ↦ by
      have hjlt : j.1 < evenLastIndex 1 (by omega) :=
        lt_evenLastIndex (by omega) j.1 j.2
      have hplt : p.1 < evenLastIndex 1 (by omega) :=
        lt_evenLastIndex (by omega) p.1 p.2.1
      apply p.2.2
      apply Fin.ext
      change p.1.1 = j.1.1
      change p.1.1 < 1 at hplt
      change j.1.1 < 1 at hjlt
      omega⟩
  unfold realOddHafnianCofactorVector hafnianPairCofactor
  exact typeHafnian_eq_one_of_isEmpty _

theorem realOddCofactorW_level_one {k : ℕ} (X : RealColumnMatrix 1 k) :
    realOddCofactorW (by omega) X = 1 := by
  unfold realOddCofactorW
  simp_rw [realOddHafnianCofactorVector_level_one X]
  simp [card_oddCofactorIndex]

/-- Exact last-column cofactor expansion over `ℝ`. -/
theorem realGramHafnian_eq_lastColumn_dot_cofactorCombination
    {r k : ℕ} (hr : 1 ≤ r) (X : RealColumnMatrix r k) :
    realGramHafnianObservable r k X =
      ∑ a : Fin k, X (evenLastIndex r hr) a *
        realOddCofactorColumnCombination hr X a := by
  unfold realGramHafnianObservable gramHafnian
  rw [← typeHafnian_fin_eq_hafnian]
  rw [typeHafnian_expand_greatest (transposeGram (realRowMatrix X))
    (evenLastIndex r hr) (lt_evenLastIndex hr)]
  unfold realOddCofactorColumnCombination realOddHafnianCofactorVector
  simp only [transposeGram_apply, realRowMatrix]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- A real cofactor is independent of the exposed final column. -/
theorem realOddHafnianCofactorVector_congr_off_last
    {r k : ℕ} (hr : 1 ≤ r) {X Y : RealColumnMatrix r k}
    (hXY : ∀ i : Fin (2 * r), i ≠ evenLastIndex r hr → X i = Y i)
    (j : OddCofactorIndex r hr) :
    realOddHafnianCofactorVector hr X j =
      realOddHafnianCofactorVector hr Y j := by
  unfold realOddHafnianCofactorVector hafnianPairCofactor
  congr 1
  funext p q
  unfold transposeGram
  simp only [Matrix.mul_apply, Matrix.transpose_apply, realRowMatrix]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [hXY p.1 p.2.1, hXY q.1 q.2.1]

theorem continuous_realOddHafnianCofactorVector_apply
    {r k : ℕ} (hr : 1 ≤ r) (j : OddCofactorIndex r hr) :
    Continuous (fun X : RealColumnMatrix r k ↦
      realOddHafnianCofactorVector hr X j) := by
  unfold realOddHafnianCofactorVector hafnianPairCofactor typeHafnian
    typeMatchingMonomial transposeGram realRowMatrix
  fun_prop

theorem continuous_realOddHafnianCofactorVector
    {r k : ℕ} (hr : 1 ≤ r) :
    Continuous (realOddHafnianCofactorVector (k := k) hr) :=
  continuous_pi fun j ↦ continuous_realOddHafnianCofactorVector_apply hr j

theorem continuous_realOddCofactorColumnCombination_apply
    {r k : ℕ} (hr : 1 ≤ r) (a : Fin k) :
    Continuous (fun X : RealColumnMatrix r k ↦
      realOddCofactorColumnCombination hr X a) := by
  unfold realOddCofactorColumnCombination
  apply continuous_finsetSum
  intro j _hj
  exact (by fun_prop : Continuous (fun X : RealColumnMatrix r k ↦ X j.1 a)) |>.mul
    (continuous_realOddHafnianCofactorVector_apply hr j)

theorem continuous_realOddCofactorColumnCombination
    {r k : ℕ} (hr : 1 ≤ r) :
    Continuous (realOddCofactorColumnCombination (k := k) hr) :=
  continuous_pi fun a ↦
    continuous_realOddCofactorColumnCombination_apply hr a

theorem continuous_realOddCofactorW {r k : ℕ} (hr : 1 ≤ r) :
    Continuous (realOddCofactorW (k := k) hr) := by
  unfold realOddCofactorW
  apply continuous_finsetSum
  intro j _hj
  exact (continuous_realOddHafnianCofactorVector_apply hr j).pow 2

theorem continuous_realOddCofactorV {r k : ℕ} (hr : 1 ≤ r) :
    Continuous (realOddCofactorV (k := k) hr) := by
  unfold realOddCofactorV
  apply continuous_finsetSum
  intro a _ha
  exact (continuous_realOddCofactorColumnCombination_apply hr a).pow 2

@[fun_prop] theorem measurable_realOddHafnianCofactorVector
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (realOddHafnianCofactorVector (k := k) hr) :=
  (continuous_realOddHafnianCofactorVector hr).measurable

@[fun_prop] theorem measurable_realOddCofactorColumnCombination
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (realOddCofactorColumnCombination (k := k) hr) :=
  (continuous_realOddCofactorColumnCombination hr).measurable

@[fun_prop] theorem measurable_realOddCofactorW
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (realOddCofactorW (k := k) hr) :=
  (continuous_realOddCofactorW hr).measurable

@[fun_prop] theorem measurable_realOddCofactorV
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (realOddCofactorV (k := k) hr) :=
  (continuous_realOddCofactorV hr).measurable

@[fun_prop] theorem measurable_realGramHafnianObservable (r k : ℕ) :
    Measurable (realGramHafnianObservable r k) := by
  have hfun : realGramHafnianObservable r k =
      fun X : RealColumnMatrix r k ↦
        typeHafnian (transposeGram (realRowMatrix X)) := by
    funext X
    unfold realGramHafnianObservable gramHafnian
    exact (typeHafnian_fin_eq_hafnian _).symm
  rw [hfun]
  have hcont : Continuous (fun X : RealColumnMatrix r k ↦
      typeHafnian (transposeGram (realRowMatrix X))) := by
    unfold typeHafnian typeMatchingMonomial transposeGram realRowMatrix
    fun_prop
  exact hcont.measurable

end

end LogdetLean.GramHafnian
