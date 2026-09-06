import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SteinFieldSlice
/-!
# Compact-support closure for the flattened Stein field

At the cutoff stage, continuity and compact support imply every global
integrability premise required by Gaussian integration by parts.  In
particular, multiplication by the radial coordinate preserves compact
support, so no separate inverse-tail estimate is needed here.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Continuous compactly supported component and derivative families satisfy
all three global integrability hypotheses used by
`integral_halfGaussianPi_divergence_of_integrable`. -/
theorem integrable_flattenedWeightedSteinComponent_families_of_compactSupport
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hFcont : ∀ i, Continuous
      (flattenedWeightedSteinComponent hdim g D i))
    (hdFcont : ∀ i, Continuous
      (flattenedWeightedSteinComponentDerivative hdim g g' D i))
    (hFcomp : ∀ i, HasCompactSupport
      (flattenedWeightedSteinComponent hdim g D i))
    (hdFcomp : ∀ i, HasCompactSupport
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)) :
    (∀ i, Integrable
        (flattenedWeightedSteinComponent hdim g D i)
        (halfGaussianPi (n + 1))) ∧
      (∀ i, Integrable
        (flattenedWeightedSteinComponentDerivative hdim g g' D i)
        (halfGaussianPi (n + 1))) ∧
      (∀ i, Integrable
        (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
        (halfGaussianPi (n + 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (hFcont i).integrable_of_hasCompactSupport (hFcomp i)
  · intro i
    exact (hdFcont i).integrable_of_hasCompactSupport (hdFcomp i)
  · intro i
    have hradialCont : Continuous
        (fun x : Fin (n + 1) → ℝ ↦
          2 * x i * flattenedWeightedSteinComponent hdim g D i x) :=
      (continuous_const.mul (continuous_apply i)).mul (hFcont i)
    have hradialComp : HasCompactSupport
        (fun x : Fin (n + 1) → ℝ ↦
          2 * x i * flattenedWeightedSteinComponent hdim g D i x) := by
      exact (hFcomp i).mul_left
    exact hradialCont.integrable_of_hasCompactSupport hradialComp

/-- Gaussian divergence for the flattened weighted Stein field follows from
continuous compact support of its component and explicit derivative
families. -/
theorem
    integral_flattenedWeightedSteinComponent_divergence_of_continuous_compactSupport
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
    (∫ x, ∑ i, flattenedWeightedSteinComponentDerivative
      hdim g g' D i x ∂halfGaussianPi (n + 1)) =
      ∫ x, ∑ i, 2 * x i * flattenedWeightedSteinComponent
        hdim g D i x ∂halfGaussianPi (n + 1) := by
  obtain ⟨hvalue, hderiv, hradial⟩ :=
    integrable_flattenedWeightedSteinComponent_families_of_compactSupport
      hdim g g' D hFcont hdFcont hFcomp hdFcomp
  exact integral_flattenedWeightedSteinComponent_divergence_of_integrable
    hdim hp g g' D hg hvalue hderiv hradial

/-- Concrete `2m`-column compact-support closure in the two-row-gap regime. -/
theorem
    integral_flattenedWeightedSteinComponent_divergence_twoMul_of_continuous_compactSupport
    {k m n : ℕ} (hdim : n + 1 = k * (2 * m))
    (hgap : 2 * m + 2 ≤ k)
    (g : Matrix (Fin k) (Fin (2 * m)) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin (2 * m)) ℝ →
      Matrix (Fin k) (Fin (2 * m)) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hg : ∀ R, HasFDerivAt g (g' R) R)
    (hFcont : ∀ i, Continuous
      (flattenedWeightedSteinComponent hdim g D i))
    (hdFcont : ∀ i, Continuous
      (flattenedWeightedSteinComponentDerivative hdim g g' D i))
    (hFcomp : ∀ i, HasCompactSupport
      (flattenedWeightedSteinComponent hdim g D i))
    (hdFcomp : ∀ i, HasCompactSupport
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)) :
    (∫ x, ∑ i, flattenedWeightedSteinComponentDerivative
      hdim g g' D i x ∂halfGaussianPi (n + 1)) =
      ∫ x, ∑ i, 2 * x i * flattenedWeightedSteinComponent
        hdim g D i x ∂halfGaussianPi (n + 1) := by
  apply
    integral_flattenedWeightedSteinComponent_divergence_of_continuous_compactSupport
      hdim (by omega) g g' D hg hFcont hdFcont hFcomp hdFcomp

end Wishart

end

end LogdetLean.GramHafnian
