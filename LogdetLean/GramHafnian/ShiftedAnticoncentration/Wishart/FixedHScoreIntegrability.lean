import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FixedHPreservedSScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.InverseTraceBounds
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RegularizedCofactorWeights
/-!
# Integrability of bounded fixed-direction Wishart scores

The inverse-Gram score in a fixed matrix direction needs only the first
inverse-Wishart trace moment.  The deterministic reason is the elementary
positive-semidefinite estimate

`|trace (G * D)| <= (sum_ij |D_ij|) * trace G`.

This file records that estimate and exposes the two integrability facts used
when a bounded measurable function of the preserved `S` coordinate is tested
against the fixed score identity.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every entry of a real positive-semidefinite matrix is bounded in absolute
value by its trace. -/
theorem abs_apply_le_trace_of_posSemidef
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (i j : n) :
    |A i j| ≤ Matrix.trace A := by
  have hii : 0 ≤ A i i := hA.diag_nonneg
  have hjj : 0 ≤ A j j := hA.diag_nonneg
  have hdiag_i : A i i ≤ Matrix.trace A := by
    simpa [Matrix.trace] using
      (Finset.single_le_sum (s := Finset.univ) (f := fun l : n ↦ A l l)
        (fun l _ ↦ hA.diag_nonneg) (Finset.mem_univ i))
  by_cases hij : i = j
  · subst j
    simpa [abs_of_nonneg hii] using hdiag_i
  have hji : A j i = A i j := by
    have hs := hA.1.eq
    simpa [Matrix.conjTranspose_apply] using
      (congrArg (fun M ↦ M j i) hs).symm
  have hplus := hA.2
    (Finsupp.single i (1 : ℝ) + Finsupp.single j 1)
  have hminus := hA.2
    (Finsupp.single i (1 : ℝ) - Finsupp.single j 1)
  simp [Finsupp.sum_add_index', Finsupp.sum_sub_index, mul_add, add_mul,
    mul_sub, sub_mul, hji] at hplus hminus
  have hsum : A i i + A j j ≤ Matrix.trace A := by
    have hs : ∑ x ∈ ({i, j} : Finset n), A x x ≤
        ∑ x ∈ Finset.univ, A x x :=
      Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by
        intro x _ _
        exact hA.diag_nonneg)
    simpa [Finset.sum_pair hij, Matrix.trace] using hs
  rw [abs_le]
  constructor <;> nlinarith

/-- A real Gram matrix is positive semidefinite. -/
theorem realWishartGram_posSemidef
    {k p : Type*} [Fintype k] [Fintype p]
    (R : Matrix k p ℝ) : (realWishartGram R).PosSemidef := by
  simpa [realWishartGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self R)

/-- The nonsingular inverse convention preserves positive semidefiniteness,
including on the singular set where it is zero. -/
theorem realWishartGram_inv_posSemidef
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (R : Matrix k p ℝ) : ((realWishartGram R)⁻¹).PosSemidef :=
  (realWishartGram_posSemidef R).inv

/-- Fixed-direction trace pairing is controlled by the trace of a
positive-semidefinite matrix. -/
theorem abs_trace_mul_le_matrixEntryAbsMass_mul_trace
    (A D : Matrix n n ℝ) (hA : A.PosSemidef) :
    |Matrix.trace (A * D)| ≤ matrixEntryAbsMass D * Matrix.trace A := by
  calc
    |Matrix.trace (A * D)| = |∑ i, ∑ j, A i j * D j i| := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    _ ≤ ∑ i, ∑ j, |A i j * D j i| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, Matrix.trace A * |D j i| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_apply_le_trace_of_posSemidef A hA i j) (abs_nonneg _)
    _ = matrixEntryAbsMass D * Matrix.trace A := by
      unfold matrixEntryAbsMass
      rw [Finset.sum_comm, mul_comm]
      simp only [Finset.mul_sum]

/-- Measurability of a fixed inverse-Gram trace pairing. -/
theorem measurable_trace_nonsingInv_realWishartGram_mul_const
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (D : Matrix p p ℝ) :
    Measurable (fun R : Matrix k p ℝ ↦
      Matrix.trace ((realWishartGram R)⁻¹ * D)) := by
  have hGram : Measurable
      (fun R : Matrix k p ℝ ↦ realWishartGram R) := by
    unfold realWishartGram
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hentry (i j : p) : Measurable
      (fun R : Matrix k p ℝ ↦ realWishartGram R i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hGram)
  have measurable_det_of_measurable
      {A : Matrix k p ℝ → Matrix p p ℝ}
      (hA : Measurable A) : Measurable (fun R ↦ (A R).det) := by
    simp_rw [Matrix.det_apply']
    exact Finset.measurable_sum _ fun σ _ ↦
      measurable_const.mul (Finset.measurable_prod _ fun i _ ↦
        (measurable_pi_apply i).comp
          ((measurable_pi_apply (σ i)).comp hA))
  have hdet : Measurable
      (fun R : Matrix k p ℝ ↦ (realWishartGram R).det) :=
    measurable_det_of_measurable hGram
  have hadj : Measurable
      (fun R : Matrix k p ℝ ↦ (realWishartGram R).adjugate) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.adjugate_apply]
    apply measurable_det_of_measurable
    refine measurable_pi_lambda _ fun a ↦ measurable_pi_lambda _ fun b ↦ ?_
    by_cases ha : a = j
    · simp [ha]
    · simpa [Matrix.updateRow_apply, ha] using hentry a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun i _ ↦
    Finset.measurable_sum _ fun j _ ↦ ?_
  have hadjEntry : Measurable
      (fun R : Matrix k p ℝ ↦ (realWishartGram R).adjugate i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hadj)
  exact (hdet.fun_inv.fun_mul hadjEntry).mul measurable_const

/-- Under the split half-Gaussian law, every fixed inverse-Gram trace
pairing is integrable at the sharp first inverse-Wishart threshold. -/
theorem integrable_trace_nonsingInv_realWishartGram_mul_const_halfGaussianMatrixSum
    {k m : ℕ} (hgap : 2 * m + 1 < k)
    (D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        Matrix.trace ((realWishartGram R)⁻¹ * D))
      (halfGaussianMatrixSum k (Fin m)) := by
  let C := matrixEntryAbsMass D
  have htrace :=
    integrable_trace_nonsingInv_realWishartGram_halfGaussianMatrixSum hgap
  have hmajor : Integrable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        C * Matrix.trace (realWishartGram R)⁻¹)
      (halfGaussianMatrixSum k (Fin m)) := htrace.const_mul C
  apply hmajor.mono'
  · exact (measurable_trace_nonsingInv_realWishartGram_mul_const D).aestronglyMeasurable
  · filter_upwards [] with R
    simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (matrixEntryAbsMass_nonneg D)
      (realWishartGram_inv_posSemidef R).trace_nonneg)] using
      (abs_trace_mul_le_matrixEntryAbsMass_mul_trace
        (realWishartGram R)⁻¹ D (realWishartGram_inv_posSemidef R))

/-- The preserved `S` coordinate is continuous, hence measurable. -/
theorem continuous_preservedSCoordinate
    {k m : Type*} [Fintype k] [Fintype m] :
    Continuous (preservedSCoordinate :
      Matrix k (m ⊕ m) ℝ → Matrix m m ℂ) := by
  rw [continuous_iff_continuousAt]
  intro R
  exact (hasFDerivAt_preservedSCoordinate R).continuousAt

/-- Coordinatewise measurability of the preserved `S` coordinate.  This is
stated separately from continuity because the explicit matrix measurable
space is not registered as a Borel space in all imported instance sets. -/
theorem measurable_preservedSCoordinate
    {k m : Type*} [Fintype k] [Fintype m] :
    Measurable (preservedSCoordinate :
      Matrix k (m ⊕ m) ℝ → Matrix m m ℂ) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [preservedSCoordinate, sCoordinateOfRealGram, sOfRealBlocks,
    realGramBlock11, realGramBlock12, realGramBlock22, realWishartGram,
    Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

/-- A bounded measurable preserved-coordinate weight times the fixed
inverse-Gram score density is integrable. -/
theorem integrable_bounded_preservedSWeight_inverseGram_scoreDelta
    {k m : ℕ}
    (u : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (hu : Measurable u) (C : ℝ) (huC : ∀ S, |u S| ≤ C)
    {H : Matrix (Fin m) (Fin m) ℂ}
    (hgap : 2 * m + 1 < k) :
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      preservedSWeight u R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)))
      (halfGaussianMatrixSum k (Fin m)) := by
  have hscore :=
    (integrable_trace_nonsingInv_realWishartGram_mul_const_halfGaussianMatrixSum
      hgap (scoreDeltaM H)).const_mul
      (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m))
  have huMeas : Measurable (preservedSWeight u :
      Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ) := by
    exact hu.comp measurable_preservedSCoordinate
  apply hscore.bdd_mul huMeas.aestronglyMeasurable
  filter_upwards [] with R
  simpa [preservedSWeight, Real.norm_eq_abs] using
    huC (preservedSCoordinate R)

/-- A bounded measurable preserved-coordinate weight times the fixed
constant score density is integrable. -/
theorem integrable_bounded_preservedSWeight_trace_scoreDelta
    {k m : ℕ}
    (u : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (hu : Measurable u) (C : ℝ) (huC : ∀ S, |u S| ≤ C)
    (H : Matrix (Fin m) (Fin m) ℂ) :
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      preservedSWeight u R * Matrix.trace (scoreDeltaM H))
      (halfGaussianMatrixSum k (Fin m)) := by
  have hconst : Integrable
      (fun _R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        Matrix.trace (scoreDeltaM H))
      (halfGaussianMatrixSum k (Fin m)) := integrable_const _
  have huMeas : Measurable (preservedSWeight u :
      Matrix (Fin k) (Fin m ⊕ Fin m) ℝ → ℝ) := by
    exact hu.comp measurable_preservedSCoordinate
  apply hconst.bdd_mul huMeas.aestronglyMeasurable
  filter_upwards [] with R
  simpa [preservedSWeight, Real.norm_eq_abs] using
    huC (preservedSCoordinate R)

/-- Both integrability facts required by the bounded fixed-H score test. -/
theorem integrable_bounded_preservedSWeight_fixedH_score_pair
    {k m : ℕ}
    (u : Matrix (Fin m) (Fin m) ℂ → ℝ)
    (hu : Measurable u) (C : ℝ) (huC : ∀ S, |u S| ≤ C)
    {H : Matrix (Fin m) (Fin m) ℂ}
    (hgap : 2 * m + 1 < k) :
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      preservedSWeight u R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)))
      (halfGaussianMatrixSum k (Fin m)) ∧
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      preservedSWeight u R * Matrix.trace (scoreDeltaM H))
      (halfGaussianMatrixSum k (Fin m)) := by
  exact ⟨integrable_bounded_preservedSWeight_inverseGram_scoreDelta
      u hu C huC hgap,
    integrable_bounded_preservedSWeight_trace_scoreDelta u hu C huC H⟩

end Wishart

end

end LogdetLean.GramHafnian
