import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GaussianIBP
import Mathlib.Analysis.Matrix.Normed
/-!
# Weighted lifted-field divergence

This module isolates the cancellation that makes conditioning possible.  A
scalar test function whose differential annihilates the lifted Gram direction
may multiply the singular Stein field without producing an extra divergence
term.  Later the scalar test is a function of the preserved transpose-Gram
coordinate `S`.
-/

open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*} [Fintype k] [Fintype m]
  [DecidableEq k] [DecidableEq m]

/-- Every finite matrix is the sum of its coordinate matrix units. -/
theorem matrix_eq_sum_smul_single (V : Matrix k m ℝ) :
    V = ∑ a, ∑ i, (V a i) • Matrix.single a i 1 := by
  classical
  calc
    V = ∑ a, ∑ i, Matrix.single a i (V a i) :=
      Matrix.matrix_eq_sum_single V
    _ = ∑ a, ∑ i, (V a i) • Matrix.single a i 1 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      ext b j
      simp [Matrix.single_apply]

/-- Genuine coordinate divergence of a scalar-weighted Stein field. -/
def weightedSteinCoordinateDivergence
    (g : Matrix k m ℝ → ℝ) (R : Matrix k m ℝ) (D : Matrix m m ℝ) : ℝ :=
  ∑ a, ∑ i,
    deriv
      (fun t : ℝ ↦
        g (matrixLine R (Matrix.single a i 1) t) *
          steinVectorFieldValue
            (matrixLine R (Matrix.single a i 1) t) D a i)
      0

/-- If the differential of `g` kills the lifted direction, multiplying by
`g` simply multiplies the divergence. -/
theorem weightedSteinCoordinateDivergence_eq_mul
    (g : Matrix k m ℝ → ℝ) (g' : Matrix k m ℝ →L[ℝ] ℝ)
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hg : HasFDerivAt g g' R)
    (hgzero : g' (steinVectorFieldValue R D) = 0)
    (hM : IsUnit (realWishartGram R).det) :
    weightedSteinCoordinateDivergence g R D =
      g R * steinVectorFieldCoordinateDivergence R D := by
  classical
  unfold weightedSteinCoordinateDivergence
  have hcoordinate (a : k) (i : m) :
      deriv
        (fun t : ℝ ↦
          g (matrixLine R (Matrix.single a i 1) t) *
            steinVectorFieldValue
              (matrixLine R (Matrix.single a i 1) t) D a i)
        0 =
      g' (Matrix.single a i 1) * steinVectorFieldValue R D a i +
        g R * steinVectorFieldLinearization R D
          (Matrix.single a i 1) a i := by
    have hline := hasDerivAt_matrixLine R (Matrix.single a i 1)
    have hg0 : HasFDerivAt g g'
        (matrixLine R (Matrix.single a i 1) 0) := by
      simpa [matrixLine] using hg
    have hgline0 := HasFDerivAt.comp
      (𝕜 := ℝ)
      (f := matrixLine R (Matrix.single a i 1))
      (f' := ContinuousLinearMap.toSpanSingleton ℝ (Matrix.single a i 1))
      (g := g) (g' := g')
      (0 : ℝ) hg0 hline.hasFDerivAt
    have hgline : HasDerivAt
        (fun t : ℝ ↦ g (matrixLine R (Matrix.single a i 1) t))
        (g' (Matrix.single a i 1)) 0 := by
      refine hgline0.hasDerivAt.congr_deriv ?_
      change g' ((1 : ℝ) • Matrix.single a i 1) =
        g' (Matrix.single a i 1)
      rw [one_smul]
    have hVmat := hasDerivAt_steinVectorFieldValue_matrixLine R
      (Matrix.single a i 1) D hM
    have hVa := hasDerivAt_pi.mp hVmat a
    have hVai := hasDerivAt_pi.mp hVa i
    have hfun :
        (fun t : ℝ ↦
          g (matrixLine R (Matrix.single a i 1) t) *
            steinVectorFieldValue
              (matrixLine R (Matrix.single a i 1) t) D a i) =
        (fun t : ℝ ↦ g (matrixLine R (Matrix.single a i 1) t)) *
          (fun t : ℝ ↦ steinVectorFieldValue
            (matrixLine R (Matrix.single a i 1) t) D a i) := by
      funext t
      rfl
    rw [hfun]
    simpa [matrixLine] using (hgline.mul hVai).deriv
  simp_rw [hcoordinate]
  rw [show (∑ a, ∑ i,
      (g' (Matrix.single a i 1) * steinVectorFieldValue R D a i +
        g R * steinVectorFieldLinearization R D
          (Matrix.single a i 1) a i)) =
      (∑ a, ∑ i,
        g' (Matrix.single a i 1) * steinVectorFieldValue R D a i) +
      g R * rectangularCoordinateTrace
        (steinVectorFieldLinearization R D) by
    simp [rectangularCoordinateTrace, Finset.sum_add_distrib,
      Finset.mul_sum]]
  have hfirst :
      (∑ a, ∑ i,
        g' (Matrix.single a i 1) * steinVectorFieldValue R D a i) = 0 := by
    let V := steinVectorFieldValue R D
    have hlinExpanded :
        g' V = ∑ a, ∑ i, (V a i) * g' (Matrix.single a i 1) := by
      calc
        g' V = g' (∑ a, ∑ i, (V a i) • Matrix.single a i 1) :=
          congrArg g' (matrix_eq_sum_smul_single V)
        _ = ∑ a, ∑ i, g' ((V a i) • Matrix.single a i 1) := by
          simp only [map_sum]
        _ = ∑ a, ∑ i, (V a i) * g' (Matrix.single a i 1) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro i _
          simpa [smul_eq_mul] using
            g'.map_smul (V a i) (Matrix.single a i (1 : ℝ))
    have hlin' :
        (∑ a, ∑ i,
          g' (Matrix.single a i 1) * steinVectorFieldValue R D a i) =
          g' (steinVectorFieldValue R D) := by
      change (∑ a, ∑ i, g' (Matrix.single a i 1) * V a i) = g' V
      rw [hlinExpanded]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      (∑ a, ∑ i,
          g' (Matrix.single a i 1) * steinVectorFieldValue R D a i) =
          g' (steinVectorFieldValue R D) := hlin'
      _ = 0 := hgzero
  rw [hfirst, zero_add,
    ← steinVectorFieldCoordinateDivergence_eq_coordinateTrace R D hM]

/-- Pointwise radial term for a scalar-weighted Stein field. -/
theorem two_mul_weighted_frobenius_steinVectorFieldValue
    (g : Matrix k m ℝ → ℝ) (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    2 * realFrobeniusInner R
        (g R • steinVectorFieldValue R D) =
      g R * Matrix.trace D := by
  rw [show realFrobeniusInner R
      (g R • steinVectorFieldValue R D) =
        g R * realFrobeniusInner R (steinVectorFieldValue R D) by
    unfold realFrobeniusInner
    simp_rw [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [← two_mul_frobenius_steinVectorFieldValue R D hM]
  ring

end Wishart

end

end LogdetLean.GramHafnian
