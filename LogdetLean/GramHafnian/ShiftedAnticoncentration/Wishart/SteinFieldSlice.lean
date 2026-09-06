import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.DeletedSliceFullRank
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GaussianIBPIntegrable
import Mathlib.Analysis.Calculus.LineDeriv.Basic
/-!
# Flattened Stein-field derivatives on coordinate slices

This file packages the uniform full-rank result from
`DeletedSliceFullRank` in the exact `HasDerivAt` form consumed by the
coordinatewise Gaussian integration-by-parts theorem.  The scalar component
corresponding to a flat coordinate is the matching entry of the weighted
inverse-Gram Stein field.
-/

open MeasureTheory
open scoped Matrix.Norms.Operator

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Matrix unit corresponding to a selected flat scalar coordinate. -/
def flatCoordinateMatrixUnit {k p n : ℕ}
    (hdim : n + 1 = k * p) (i : Fin (n + 1)) :
    Matrix (Fin k) (Fin p) ℝ :=
  Matrix.single (flatCoordinateRow hdim i)
    (flatCoordinateColumn hdim i) 1

/-- Exposing one flat coordinate is exactly an affine matrix line in the
matching matrix-unit direction. -/
theorem flatSuccMatrix_insertNth_eq_matrixLine
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) (y : Fin n → ℝ) (s t : ℝ) :
    flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y) =
      matrixLine
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y))
        (flatCoordinateMatrixUnit hdim i) (s - t) := by
  ext b l
  let q : Fin (n + 1) :=
    (finCongr hdim).symm (finProdFinEquiv (b, l))
  change (@Fin.insertNth n (fun _ : Fin (n + 1) ↦ ℝ) i s y q) =
    (@Fin.insertNth n (fun _ : Fin (n + 1) ↦ ℝ) i t y q) +
      (s - t) * flatCoordinateMatrixUnit hdim i b l
  by_cases hqi : q = i
  · have hflat : finProdFinEquiv (b, l) = finCongr hdim i := by
      apply (finCongr hdim).symm.injective
      simpa [q] using hqi
    have hpair : (b, l) = flatCoordinatePair hdim i := by
      have hp := congrArg finProdFinEquiv.symm hflat
      simpa only [Equiv.symm_apply_apply, flatCoordinatePair] using hp
    have hb : b = flatCoordinateRow hdim i := by
      exact congrArg Prod.fst hpair
    have hl : l = flatCoordinateColumn hdim i := by
      exact congrArg Prod.snd hpair
    subst b
    subst l
    rw [hqi, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
    simp [flatCoordinateMatrixUnit]
  · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hqi
    have hpairne : (b, l) ≠ flatCoordinatePair hdim i := by
      intro hpair
      apply hqi
      unfold q
      rw [hpair]
      change (finCongr hdim).symm
        (finProdFinEquiv (finProdFinEquiv.symm (finCongr hdim i))) = i
      rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    have hunit : flatCoordinateMatrixUnit hdim i b l = 0 := by
      by_cases hb : b = flatCoordinateRow hdim i
      · have hl : l ≠ flatCoordinateColumn hdim i := by
          intro hl
          apply hpairne
          exact Prod.ext hb hl
        subst b
        have hl' : flatCoordinateColumn hdim i ≠ l := Ne.symm hl
        simp [flatCoordinateMatrixUnit, Matrix.single_apply, hl']
      · have hb' : flatCoordinateRow hdim i ≠ b := Ne.symm hb
        simp [flatCoordinateMatrixUnit, Matrix.single_apply, hb']
    rw [← hz, Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_succAbove, hunit, mul_zero, add_zero]

/-- The flat-to-matrix slice has derivative equal to its selected matrix
unit at every scalar parameter. -/
theorem hasDerivAt_flatSuccMatrix_insertNth
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y))
      (flatCoordinateMatrixUnit hdim i) t := by
  let R := flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y)
  let E := flatCoordinateMatrixUnit hdim i
  have hshift : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hfun :
      (fun s : ℝ ↦
        flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y)) =
      (fun s : ℝ ↦ matrixLine R E (s - t)) := by
    funext s
    exact flatSuccMatrix_insertNth_eq_matrixLine hdim i y s t
  rw [hfun]
  apply hasDerivAt_pi.mpr
  intro b
  apply hasDerivAt_pi.mpr
  intro l
  unfold matrixLine
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  convert
    (hasDerivAt_const (x := t) (c := R b l)).add
      (hshift.mul_const (E b l)) using 1 <;>
    first | rfl | simp [E] | exact Subsingleton.elim _ _

/-- The inverse-Gram Stein field has its advertised linearization along a
flat coordinate slice whenever the base point is full rank. -/
theorem hasDerivAt_steinVectorFieldValue_flatSucc_insertNth
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram
      (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y))).det) :
    HasDerivAt
      (fun s : ℝ ↦ steinVectorFieldValue
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y)) D)
      (steinVectorFieldLinearization
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y)) D
        (flatCoordinateMatrixUnit hdim i)) t := by
  let R := flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y)
  let E := flatCoordinateMatrixUnit hdim i
  have hshift : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hbase := hasDerivAt_steinVectorFieldValue_matrixLine R E D hfull
  have hfun :
      (fun s : ℝ ↦ steinVectorFieldValue
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y)) D) =
      (fun s : ℝ ↦ steinVectorFieldValue
        (matrixLine R E (s - t)) D) := by
    funext s
    rw [flatSuccMatrix_insertNth_eq_matrixLine hdim i y s t]
  rw [hfun]
  apply hasDerivAt_pi.mpr
  intro b
  apply hasDerivAt_pi.mpr
  intro l
  have hentry := hasDerivAt_pi.mp (hasDerivAt_pi.mp hbase b) l
  have ht : (0 : ℝ) = t - t := by ring
  rw [ht] at hentry
  have hcomp := hentry.comp (h := fun s : ℝ ↦ s - t) t hshift
  simpa [Function.comp_def] using hcomp

/-- One scalar component of the weighted flattened Stein field. -/
def flattenedWeightedSteinComponent
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : ℝ :=
  let R := flatSuccMatrixMeasurableEquiv hdim x
  g R * steinVectorFieldValue R D
    (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i)

/-- Explicit derivative of one scalar component of the weighted flattened
Stein field. -/
def flattenedWeightedSteinComponentDerivative
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : ℝ :=
  let R := flatSuccMatrixMeasurableEquiv hdim x
  let E := flatCoordinateMatrixUnit hdim i
  g' R E * steinVectorFieldValue R D
      (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i) +
    g R * steinVectorFieldLinearization R D E
      (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i)

/-- Product and chain rules identify the explicit derivative on every
full-rank point of a scalar slice. -/
theorem hasDerivAt_flattenedWeightedSteinComponent_insertNth
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ)
    (hfull : IsUnit (realWishartGram
      (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y))).det) :
    HasDerivAt
      (fun s : ℝ ↦ flattenedWeightedSteinComponent
        hdim g D i (i.insertNth s y))
      (flattenedWeightedSteinComponentDerivative
        hdim g g' D i (i.insertNth t y)) t := by
  let R := flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y)
  let E := flatCoordinateMatrixUnit hdim i
  let a := flatCoordinateRow hdim i
  let j := flatCoordinateColumn hdim i
  have hgline : HasDerivAt
      (fun s : ℝ ↦ g
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y)))
      (g' R E) t := by
    have hbase : HasDerivAt
        (fun u : ℝ ↦ g (R + u • E)) (g' R E) 0 := by
      exact (hg R).hasLineDerivAt E
    have hshift : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
      simpa using (hasDerivAt_id t).sub_const t
    have ht : (0 : ℝ) = t - t := by ring
    rw [ht] at hbase
    have hcomp := hbase.comp (h := fun s : ℝ ↦ s - t) t hshift
    have hfun :
        (fun s : ℝ ↦ g
          (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y))) =
        (fun s : ℝ ↦ g (R + (s - t) • E)) := by
      funext s
      rw [flatSuccMatrix_insertNth_eq_matrixLine hdim i y s t]
      rfl
    rw [hfun]
    simpa [Function.comp_def] using hcomp
  have hVmat := hasDerivAt_steinVectorFieldValue_flatSucc_insertNth
    hdim i y t D hfull
  have hVa := hasDerivAt_pi.mp hVmat a
  have hVaj := hasDerivAt_pi.mp hVa j
  change HasDerivAt
    ((fun s : ℝ ↦ g
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y))) *
      (fun s : ℝ ↦ steinVectorFieldValue
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y)) D a j))
    (g' R E * steinVectorFieldValue R D a j +
      g R * steinVectorFieldLinearization R D E a j) t
  exact hgline.mul hVaj

/-- All scalar components satisfy the exact slice derivative premise of
`integral_halfGaussianPi_divergence` under strict rectangularity. -/
theorem forall_ae_hasDerivAt_flattenedWeightedSteinComponent
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R) :
    ∀ i : Fin (n + 1),
      ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
        HasDerivAt
          (fun s : ℝ ↦ flattenedWeightedSteinComponent
            hdim g D i (i.insertNth s y))
          (flattenedWeightedSteinComponentDerivative
            hdim g g' D i (i.insertNth t y)) t := by
  intro i
  filter_upwards [
    ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_slice_of_lt
      hdim i hp] with y hy
  intro t
  exact hasDerivAt_flattenedWeightedSteinComponent_insertNth
    hdim g g' D hg i y t (hy t)

/-- Concrete realified `2m`-column version in the two-row-gap regime. -/
theorem forall_ae_hasDerivAt_flattenedWeightedSteinComponent_twoMul
    {k m n : ℕ} (hdim : n + 1 = k * (2 * m))
    (hgap : 2 * m + 2 ≤ k)
    (g : Matrix (Fin k) (Fin (2 * m)) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin (2 * m)) ℝ →
      Matrix (Fin k) (Fin (2 * m)) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R) :
    ∀ i : Fin (n + 1),
      ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
        HasDerivAt
          (fun s : ℝ ↦ flattenedWeightedSteinComponent
            hdim g D i (i.insertNth s y))
          (flattenedWeightedSteinComponentDerivative
            hdim g g' D i (i.insertNth t y)) t := by
  apply forall_ae_hasDerivAt_flattenedWeightedSteinComponent hdim
  · omega
  · exact hg

/-- The flattened weighted Stein field now plugs directly into the global
integrability version of Gaussian integration by parts. -/
theorem integral_flattenedWeightedSteinComponent_divergence_of_integrable
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (hvalue : ∀ i, Integrable
      (flattenedWeightedSteinComponent hdim g D i)
      (halfGaussianPi (n + 1)))
    (hderiv : ∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)
      (halfGaussianPi (n + 1)))
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1))) :
    (∫ x, ∑ i, flattenedWeightedSteinComponentDerivative
      hdim g g' D i x ∂halfGaussianPi (n + 1)) =
      ∫ x, ∑ i, 2 * x i * flattenedWeightedSteinComponent
        hdim g D i x ∂halfGaussianPi (n + 1) := by
  exact integral_halfGaussianPi_divergence_of_integrable
    (fun i x ↦ flattenedWeightedSteinComponent hdim g D i x)
    (fun i x ↦ flattenedWeightedSteinComponentDerivative
      hdim g g' D i x)
    (forall_ae_hasDerivAt_flattenedWeightedSteinComponent
      hdim hp g g' D hg)
    hvalue hderiv hradial

/-- Concrete `2m`-column Gaussian divergence identity in the two-row-gap
regime, reduced entirely to the three global integrability conditions. -/
theorem integral_flattenedWeightedSteinComponent_divergence_twoMul_of_integrable
    {k m n : ℕ} (hdim : n + 1 = k * (2 * m))
    (hgap : 2 * m + 2 ≤ k)
    (g : Matrix (Fin k) (Fin (2 * m)) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin (2 * m)) ℝ →
      Matrix (Fin k) (Fin (2 * m)) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (hvalue : ∀ i, Integrable
      (flattenedWeightedSteinComponent hdim g D i)
      (halfGaussianPi (n + 1)))
    (hderiv : ∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)
      (halfGaussianPi (n + 1)))
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1))) :
    (∫ x, ∑ i, flattenedWeightedSteinComponentDerivative
      hdim g g' D i x ∂halfGaussianPi (n + 1)) =
      ∫ x, ∑ i, 2 * x i * flattenedWeightedSteinComponent
        hdim g D i x ∂halfGaussianPi (n + 1) := by
  apply integral_flattenedWeightedSteinComponent_divergence_of_integrable
    hdim (by omega) g g' D hg hvalue hderiv hradial

end Wishart

end

end LogdetLean.GramHafnian
