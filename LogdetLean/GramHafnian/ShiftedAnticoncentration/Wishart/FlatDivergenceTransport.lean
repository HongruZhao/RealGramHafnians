import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SteinFieldIntegrability
/-!
# Transporting flat Gaussian divergence to matrix coordinates

This file identifies the sums over flattened scalar coordinates with the
genuine matrix-coordinate divergence and Frobenius radial term.  It then
transports the Gaussian integration-by-parts identity through the exact
measure-preserving flattening equivalence.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- The selected flat coordinate as an equivalence with a matrix-entry
pair. -/
def flatCoordinatePairEquiv {k p n : ℕ} (hdim : n + 1 = k * p) :
    Fin (n + 1) ≃ Fin k × Fin p :=
  (finCongr hdim).trans finProdFinEquiv.symm

@[simp] theorem flatCoordinatePairEquiv_apply
    {k p n : ℕ} (hdim : n + 1 = k * p) (i : Fin (n + 1)) :
    flatCoordinatePairEquiv hdim i = flatCoordinatePair hdim i :=
  rfl

@[simp] theorem flatSuccMatrix_apply_flatCoordinatePair
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    flatSuccMatrixMeasurableEquiv hdim x
        (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i) =
      x i := by
  change x ((finCongr hdim).symm
      (finProdFinEquiv (finProdFinEquiv.symm (finCongr hdim i)))) = x i
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- On the full-rank locus, the derivative-defined weighted divergence is
the sum of its explicit product-rule coordinate derivatives. -/
theorem weightedSteinCoordinateDivergence_eq_explicit
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (g : Matrix k p ℝ → ℝ)
    (g' : Matrix k p ℝ →L[ℝ] ℝ)
    (R : Matrix k p ℝ) (D : Matrix p p ℝ)
    (hg : HasFDerivAt g g' R)
    (hfull : IsUnit (realWishartGram R).det) :
    weightedSteinCoordinateDivergence g R D =
      ∑ a, ∑ j,
        (g' (Matrix.single a j 1) * steinVectorFieldValue R D a j +
          g R * steinVectorFieldLinearization R D
            (Matrix.single a j 1) a j) := by
  unfold weightedSteinCoordinateDivergence
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  have hline := hasDerivAt_matrixLine R (Matrix.single a j 1)
  have hg0 : HasFDerivAt g g'
      (matrixLine R (Matrix.single a j 1) 0) := by
    simpa [matrixLine] using hg
  have hgline0 := HasFDerivAt.comp
    (𝕜 := ℝ)
    (f := matrixLine R (Matrix.single a j 1))
    (f' := ContinuousLinearMap.toSpanSingleton ℝ (Matrix.single a j 1))
    (g := g) (g' := g')
    (0 : ℝ) hg0 hline.hasFDerivAt
  have hgline : HasDerivAt
      (fun t : ℝ ↦ g (matrixLine R (Matrix.single a j 1) t))
      (g' (Matrix.single a j 1)) 0 := by
    refine hgline0.hasDerivAt.congr_deriv ?_
    change g' ((1 : ℝ) • Matrix.single a j 1) =
      g' (Matrix.single a j 1)
    rw [one_smul]
  have hVmat := hasDerivAt_steinVectorFieldValue_matrixLine R
    (Matrix.single a j 1) D hfull
  have hVa := hasDerivAt_pi.mp hVmat a
  have hVaj := hasDerivAt_pi.mp hVa j
  have hproduct := hgline.mul hVaj
  have hfun :
      (fun t : ℝ ↦
        g (matrixLine R (Matrix.single a j 1) t) *
          steinVectorFieldValue
            (matrixLine R (Matrix.single a j 1) t) D a j) =
      (fun t : ℝ ↦ g (matrixLine R (Matrix.single a j 1) t)) *
        (fun t : ℝ ↦ steinVectorFieldValue
          (matrixLine R (Matrix.single a j 1) t) D a j) := by
    funext t
    rfl
  rw [hfun]
  simpa [matrixLine] using hproduct.deriv

/-- The sum of explicit flattened derivatives is the genuine weighted
matrix-coordinate divergence on the full-rank locus. -/
theorem sum_flattenedWeightedSteinComponentDerivative_eq_divergence
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (x : Fin (n + 1) → ℝ)
    (hg : HasFDerivAt g (g'
      (flatSuccMatrixMeasurableEquiv hdim x))
      (flatSuccMatrixMeasurableEquiv hdim x))
    (hfull : IsUnit (realWishartGram
      (flatSuccMatrixMeasurableEquiv hdim x)).det) :
    (∑ i, flattenedWeightedSteinComponentDerivative
      hdim g g' D i x) =
      weightedSteinCoordinateDivergence g
        (flatSuccMatrixMeasurableEquiv hdim x) D := by
  let R := flatSuccMatrixMeasurableEquiv hdim x
  let e := flatCoordinatePairEquiv hdim
  let T : Fin k × Fin p → ℝ := fun q ↦
    g' R (Matrix.single q.1 q.2 1) *
        steinVectorFieldValue R D q.1 q.2 +
      g R * steinVectorFieldLinearization R D
        (Matrix.single q.1 q.2 1) q.1 q.2
  have hreindex :
      (∑ i, flattenedWeightedSteinComponentDerivative
        hdim g g' D i x) = ∑ q : Fin k × Fin p, T q := by
    simpa [flattenedWeightedSteinComponentDerivative,
      flatCoordinateMatrixUnit, flatCoordinateRow,
      flatCoordinateColumn, flatCoordinatePair, e, T, R] using
      (e.sum_comp T)
  rw [hreindex, Fintype.sum_prod_type]
  exact (weightedSteinCoordinateDivergence_eq_explicit
    g (g' R) R D hg hfull).symm

/-- The flat radial sum is exactly twice the Frobenius pairing with the
scalar-weighted Stein field. -/
theorem sum_flattenedWeightedSteinComponent_radial_eq
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (x : Fin (n + 1) → ℝ) :
    (∑ i, 2 * x i * flattenedWeightedSteinComponent hdim g D i x) =
      2 * realFrobeniusInner
        (flatSuccMatrixMeasurableEquiv hdim x)
        (g (flatSuccMatrixMeasurableEquiv hdim x) •
          steinVectorFieldValue
            (flatSuccMatrixMeasurableEquiv hdim x) D) := by
  let R := flatSuccMatrixMeasurableEquiv hdim x
  let e := flatCoordinatePairEquiv hdim
  let T : Fin k × Fin p → ℝ := fun q ↦
    2 * R q.1 q.2 * (g R * steinVectorFieldValue R D q.1 q.2)
  have hreindex :
      (∑ i, 2 * x i * flattenedWeightedSteinComponent hdim g D i x) =
        ∑ q : Fin k × Fin p, T q := by
    calc
      (∑ i, 2 * x i * flattenedWeightedSteinComponent hdim g D i x) =
          ∑ i, T (e i) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [flattenedWeightedSteinComponent, T, e,
          flatCoordinatePairEquiv_apply]
        change 2 * x i *
            (g R * steinVectorFieldValue R D
              (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i)) =
          2 * R (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i) *
            (g R * steinVectorFieldValue R D
              (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i))
        have hRi :
            R (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i) = x i := by
          dsimp [R]
          exact flatSuccMatrix_apply_flatCoordinatePair hdim x i
        rw [hRi]
      _ = ∑ q : Fin k × Fin p, T q := e.sum_comp T
  rw [hreindex, Fintype.sum_prod_type]
  unfold realFrobeniusInner
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [T, R]
  ring

/-- Pulling matrix integrals back through the successor-dimensional flat
equivalence. -/
theorem integral_comp_flatSuccMatrixMeasurableEquiv
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (f : Matrix (Fin k) (Fin p) ℝ → ℝ) :
    (∫ x, f (flatSuccMatrixMeasurableEquiv hdim x)
        ∂halfGaussianPi (n + 1)) =
      ∫ R, f R ∂halfGaussianMatrix k p := by
  exact (measurePreserving_flatSuccMatrixMeasurableEquiv hdim).integral_comp' f

/-- The flat Gaussian divergence theorem transported to the literal iid
half-Gaussian matrix law. -/
theorem integral_weightedSteinCoordinateDivergence_halfGaussianMatrix_of_integrable
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
    (∫ R, weightedSteinCoordinateDivergence g R D
        ∂halfGaussianMatrix k p) =
      ∫ R, 2 * realFrobeniusInner R
        (g R • steinVectorFieldValue R D)
        ∂halfGaussianMatrix k p := by
  have hflat := integral_flattenedWeightedSteinComponent_divergence_of_integrable
    hdim hp g g' D hg hvalue hderiv hradial
  have hfullMatrix : ∀ᵐ R ∂halfGaussianMatrix k p,
      IsUnit (realWishartGram R).det :=
    ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (Nat.le_of_lt hp)
  have hfullFlat : ∀ᵐ x ∂halfGaussianPi (n + 1),
      IsUnit (realWishartGram
        (flatSuccMatrixMeasurableEquiv hdim x)).det :=
    (measurePreserving_flatSuccMatrixMeasurableEquiv hdim).quasiMeasurePreserving.ae
      hfullMatrix
  have hleft :
      (∫ x, ∑ i, flattenedWeightedSteinComponentDerivative
          hdim g g' D i x ∂halfGaussianPi (n + 1)) =
        ∫ R, weightedSteinCoordinateDivergence g R D
          ∂halfGaussianMatrix k p := by
    calc
      (∫ x, ∑ i, flattenedWeightedSteinComponentDerivative
          hdim g g' D i x ∂halfGaussianPi (n + 1)) =
          ∫ x, weightedSteinCoordinateDivergence g
            (flatSuccMatrixMeasurableEquiv hdim x) D
            ∂halfGaussianPi (n + 1) := by
        apply integral_congr_ae
        filter_upwards [hfullFlat] with x hx
        exact sum_flattenedWeightedSteinComponentDerivative_eq_divergence
          hdim g g' D x (hg _) hx
      _ = ∫ R, weightedSteinCoordinateDivergence g R D
          ∂halfGaussianMatrix k p :=
        integral_comp_flatSuccMatrixMeasurableEquiv hdim
          (fun R ↦ weightedSteinCoordinateDivergence g R D)
  have hright :
      (∫ x, ∑ i, 2 * x i * flattenedWeightedSteinComponent
          hdim g D i x ∂halfGaussianPi (n + 1)) =
        ∫ R, 2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D)
          ∂halfGaussianMatrix k p := by
    calc
      (∫ x, ∑ i, 2 * x i * flattenedWeightedSteinComponent
          hdim g D i x ∂halfGaussianPi (n + 1)) =
          ∫ x, 2 * realFrobeniusInner
            (flatSuccMatrixMeasurableEquiv hdim x)
            (g (flatSuccMatrixMeasurableEquiv hdim x) •
              steinVectorFieldValue
                (flatSuccMatrixMeasurableEquiv hdim x) D)
            ∂halfGaussianPi (n + 1) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact sum_flattenedWeightedSteinComponent_radial_eq hdim g D x
      _ = ∫ R, 2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D)
          ∂halfGaussianMatrix k p :=
        integral_comp_flatSuccMatrixMeasurableEquiv hdim
          (fun R ↦ 2 * realFrobeniusInner R
            (g R • steinVectorFieldValue R D))
  exact hleft.symm.trans (hflat.trans hright)

/-- Compact-support version of the transported matrix divergence identity. -/
theorem
    integral_weightedSteinCoordinateDivergence_halfGaussianMatrix_of_continuous_compactSupport
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (hFcont : ∀ i, Continuous
      (flattenedWeightedSteinComponent hdim g D i))
    (hdFcont : ∀ i, Continuous
      (flattenedWeightedSteinComponentDerivative hdim g g' D i))
    (hFcomp : ∀ i, HasCompactSupport
      (flattenedWeightedSteinComponent hdim g D i))
    (hdFcomp : ∀ i, HasCompactSupport
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)) :
    (∫ R, weightedSteinCoordinateDivergence g R D
        ∂halfGaussianMatrix k p) =
      ∫ R, 2 * realFrobeniusInner R
        (g R • steinVectorFieldValue R D)
        ∂halfGaussianMatrix k p := by
  obtain ⟨hvalue, hderiv, hradial⟩ :=
    integrable_flattenedWeightedSteinComponent_families_of_compactSupport
      hdim g g' D hFcont hdFcont hFcomp hdFcomp
  exact
    integral_weightedSteinCoordinateDivergence_halfGaussianMatrix_of_integrable
      hdim hp g g' D hg hvalue hderiv hradial

end Wishart

end

end LogdetLean.GramHafnian
