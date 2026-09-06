import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FlatDivergenceTransport
/-!
# Closing the matrix Gaussian divergence argument

`FlatDivergenceTransport` proves the Gaussian divergence identity from the
three genuine coordinate-family integrability hypotheses.  `IntegratedScore`
then identifies the two sides pointwise on the almost-sure full-rank locus.
This file records the missing analytic closure: those same hypotheses also
imply the two `Integrable` conclusions in the classical fixed-direction
Stein--Haff statement.

The result is deliberately stated for numeric matrix indices.  Reindexing a
finite column type is a separate measure-preserving algebraic operation and
does not belong to the singular-field cutoff argument.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- The explicit flat derivative sum is integrable whenever every coordinate
derivative is integrable. -/
theorem integrable_sum_flattenedWeightedSteinComponentDerivative
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hderiv : ∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)
      (halfGaussianPi (n + 1))) :
    Integrable
      (fun x ↦ ∑ i, flattenedWeightedSteinComponentDerivative
        hdim g g' D i x)
      (halfGaussianPi (n + 1)) := by
  exact integrable_finsetSum _ (fun i _ ↦ hderiv i)

/-- The explicit flat radial sum is integrable whenever every coordinate
radial term is integrable. -/
theorem integrable_sum_flattenedWeightedSteinComponent_radial
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1))) :
    Integrable
      (fun x ↦ ∑ i, 2 * x i *
        flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1)) := by
  exact integrable_finsetSum _ (fun i _ ↦ hradial i)

/-- Product-rule form of the weighted Stein-field divergence, without the
preserved-coordinate assumption.  The first term is the differential of the
scalar weight in the lifted Gram direction. -/
theorem weightedSteinCoordinateDivergence_eq_fderiv_add_mul
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (g : Matrix k p ℝ → ℝ) (g' : Matrix k p ℝ →L[ℝ] ℝ)
    (R : Matrix k p ℝ) (D : Matrix p p ℝ)
    (hg : HasFDerivAt g g' R)
    (hM : IsUnit (realWishartGram R).det) :
    weightedSteinCoordinateDivergence g R D =
      g' (steinVectorFieldValue R D) +
        g R * steinVectorFieldCoordinateDivergence R D := by
  rw [weightedSteinCoordinateDivergence_eq_explicit g g' R D hg hM]
  rw [show (∑ a, ∑ j,
      (g' (Matrix.single a j 1) * steinVectorFieldValue R D a j +
        g R * steinVectorFieldLinearization R D
          (Matrix.single a j 1) a j)) =
      (∑ a, ∑ j,
        g' (Matrix.single a j 1) * steinVectorFieldValue R D a j) +
      g R * rectangularCoordinateTrace
        (steinVectorFieldLinearization R D) by
    simp [rectangularCoordinateTrace, Finset.sum_add_distrib,
      Finset.mul_sum]]
  have hfirst :
      (∑ a, ∑ j,
        g' (Matrix.single a j 1) * steinVectorFieldValue R D a j) =
        g' (steinVectorFieldValue R D) := by
    let V := steinVectorFieldValue R D
    calc
      (∑ a, ∑ j, g' (Matrix.single a j 1) * V a j) =
          ∑ a, ∑ j, (V a j) * g' (Matrix.single a j 1) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = g' (∑ a, ∑ j, (V a j) • Matrix.single a j 1) := by
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro j _
        simpa [smul_eq_mul] using
          (g'.map_smul (V a j) (Matrix.single a j (1 : ℝ))).symm
      _ = g' V := by rw [← matrix_eq_sum_smul_single V]
  rw [hfirst,
    ← steinVectorFieldCoordinateDivergence_eq_coordinateTrace R D hM]

/-- A full atom-shaped Stein--Haff conclusion on the literal numeric
half-Gaussian matrix law.

Unlike an abstract premise containing the desired integral equality, the
hypotheses here are exactly the componentwise value, derivative, and radial
integrability conditions consumed by one-dimensional Gaussian integration by
parts.  Thus this theorem can be instantiated directly by a singular-field
cutoff construction. -/
theorem steinHaff_halfGaussianMatrix_of_flattenedSteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (q : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (hchain : ∀ R, IsUnit (realWishartGram R).det →
      g' R (steinVectorFieldValue R D) = q R)
    (hq : Integrable q (halfGaussianMatrix k p))
    (hvalue : ∀ i, Integrable
      (flattenedWeightedSteinComponent hdim g D i)
      (halfGaussianPi (n + 1)))
    (hderiv : ∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)
      (halfGaussianPi (n + 1)))
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1))) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          g R * (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          g R * Matrix.trace D - q R)
        (halfGaussianMatrix k p) ∧
      ((∫ R, g R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, g R * Matrix.trace D - q R
          ∂halfGaussianMatrix k p) := by
  let e := flatSuccMatrixMeasurableEquiv hdim
  let μ := halfGaussianMatrix k p
  let ν := halfGaussianPi (n + 1)
  have hfull : ∀ᵐ R ∂μ, IsUnit (realWishartGram R).det :=
    ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (Nat.le_of_lt hp)
  have hfullFlat : ∀ᵐ x ∂ν,
      IsUnit (realWishartGram (e x)).det :=
    (measurePreserving_flatSuccMatrixMeasurableEquiv hdim).quasiMeasurePreserving.ae
      hfull
  have hinv : MeasurePreserving e.symm μ ν :=
    (measurePreserving_flatSuccMatrixMeasurableEquiv hdim).symm e

  have hflatDeriv : Integrable
      (fun x ↦ ∑ i, flattenedWeightedSteinComponentDerivative
        hdim g g' D i x) ν :=
    integrable_sum_flattenedWeightedSteinComponentDerivative
      hdim g g' D hderiv
  have hdivComp : Integrable
      (fun x ↦ weightedSteinCoordinateDivergence g (e x) D) ν := by
    apply hflatDeriv.congr
    filter_upwards [hfullFlat] with x hx
    simpa [e] using
      (sum_flattenedWeightedSteinComponentDerivative_eq_divergence
        hdim g g' D x (hg _) hx)
  have hdiv : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        weightedSteinCoordinateDivergence g R D) μ := by
    have h := hinv.integrable_comp_of_integrable hdivComp
    simpa [Function.comp_def, e] using h
  have hscoreInt : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        g R * (inverseGramScoreCoefficient (Fin k) (Fin p) *
          Matrix.trace ((realWishartGram R)⁻¹ * D))) μ := by
    apply (hdiv.sub hq).congr
    filter_upwards [hfull] with R hR
    change weightedSteinCoordinateDivergence g R D - q R = _
    rw [weightedSteinCoordinateDivergence_eq_fderiv_add_mul
      g (g' R) R D (hg R) hR, hchain R hR,
      steinVectorFieldCoordinateDivergence_eq R D hR]
    unfold inverseGramScoreCoefficient
    simp only [Fintype.card_fin]
    ring

  have hflatRadial : Integrable
      (fun x ↦ ∑ i, 2 * x i *
        flattenedWeightedSteinComponent hdim g D i x) ν :=
    integrable_sum_flattenedWeightedSteinComponent_radial
      hdim g D hradial
  have hradialComp : Integrable
      (fun x ↦ 2 * realFrobeniusInner (e x)
        (g (e x) • steinVectorFieldValue (e x) D)) ν := by
    apply hflatRadial.congr
    filter_upwards [] with x
    simpa [e] using
      (sum_flattenedWeightedSteinComponent_radial_eq hdim g D x)
  have hradialMatrix : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D)) μ := by
    have h := hinv.integrable_comp_of_integrable hradialComp
    simpa [Function.comp_def, e] using h
  have hconstantInt : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        g R * Matrix.trace D - q R) μ := by
    apply (hradialMatrix.sub hq).congr
    filter_upwards [hfull] with R hR
    change (2 * realFrobeniusInner R
      (g R • steinVectorFieldValue R D)) - q R = _
    rw [two_mul_weighted_frobenius_steinVectorFieldValue g R D hR]

  have hIBP :=
    integral_weightedSteinCoordinateDivergence_halfGaussianMatrix_of_integrable
      hdim hp g g' D hg hvalue hderiv hradial
  have hscore :
      (∫ R, g R *
          (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)) ∂μ) =
        ∫ R, g R * Matrix.trace D - q R ∂μ := by
    calc
      (∫ R, g R *
          (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)) ∂μ) =
          ∫ R, weightedSteinCoordinateDivergence g R D - q R ∂μ := by
        apply integral_congr_ae
        filter_upwards [hfull] with R hR
        rw [weightedSteinCoordinateDivergence_eq_fderiv_add_mul
          g (g' R) R D (hg R) hR, hchain R hR,
          steinVectorFieldCoordinateDivergence_eq R D hR]
        unfold inverseGramScoreCoefficient
        simp only [Fintype.card_fin]
        ring
      _ = (∫ R, weightedSteinCoordinateDivergence g R D ∂μ) -
          ∫ R, q R ∂μ := integral_sub hdiv hq
      _ = (∫ R, 2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D) ∂μ) -
          ∫ R, q R ∂μ := by rw [hIBP]
      _ = ∫ R, (2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D)) - q R ∂μ :=
        (integral_sub hradialMatrix hq).symm
      _ = ∫ R, g R * Matrix.trace D - q R ∂μ := by
        apply integral_congr_ae
        filter_upwards [hfull] with R hR
        rw [two_mul_weighted_frobenius_steinVectorFieldValue g R D hR]
  exact ⟨hscoreInt, hconstantInt, hscore⟩

/-- Preserved-coordinate specialization: when the differential of the test
annihilates the lifted Gram direction, the directional term in the general
closure vanishes.  This is the direct interface needed by the conditional
Wishart argument after its singular-field estimates are discharged. -/
theorem preservedScore_halfGaussianMatrix_of_flattenedSteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (hgzero : ∀ R, IsUnit (realWishartGram R).det →
      g' R (steinVectorFieldValue R D) = 0)
    (hvalue : ∀ i, Integrable
      (flattenedWeightedSteinComponent hdim g D i)
      (halfGaussianPi (n + 1)))
    (hderiv : ∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)
      (halfGaussianPi (n + 1)))
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1))) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          g R * (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          g R * Matrix.trace D)
        (halfGaussianMatrix k p) ∧
      ((∫ R, g R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, g R * Matrix.trace D ∂halfGaussianMatrix k p) := by
  have h := steinHaff_halfGaussianMatrix_of_flattenedSteinFamilies
    hdim hp g g' D (fun _ ↦ (0 : ℝ)) hg (by
      intro R hR
      exact hgzero R hR)
    (integrable_zero (Matrix (Fin k) (Fin p) ℝ) ℝ
      (halfGaussianMatrix k p))
    hvalue hderiv hradial
  simpa using h

end Wishart

end

end LogdetLean.GramHafnian
