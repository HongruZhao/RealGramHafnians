import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.FixedHScoreIntegrability
/-!
# Integrability for the internal Stein--Haff theorem

This module supplies the absolute-integrability conclusions used by the
internal preserved-`S` Stein--Haff argument, without using the external
Stein--Haff atom.  The only singular quantity is a fixed trace pairing with
the inverse real Gram matrix.  It is dominated by the first inverse-Wishart
trace moment already proved in `InverseTraceIntegrability`.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/- Keep the finite matrix topology compatible with the coordinatewise
measurable spaces used by the Gaussian matrix laws. -/
local instance genericSteinHaffMatrixNormedAddCommGroup
    {a b 𝕜 : Type*} [Fintype a] [Fintype b]
    [NormedAddCommGroup 𝕜] : NormedAddCommGroup (Matrix a b 𝕜) :=
  Matrix.normedAddCommGroup

local instance genericSteinHaffMatrixNormedSpace
    {a b 𝕜 𝔽 : Type*} [Fintype a] [Fintype b]
    [NormedField 𝔽] [NormedAddCommGroup 𝕜] [NormedSpace 𝔽 𝕜] :
    NormedSpace 𝔽 (Matrix a b 𝕜) :=
  Matrix.normedSpace

local instance genericSteinHaffMatrixBorelSpace
    (a b : Type*) [Fintype a] [Fintype b] :
    BorelSpace (Matrix a b ℝ) := by
  change BorelSpace (a → b → ℝ)
  infer_instance

/-- A fixed inverse-Gram trace pairing is integrable under the numeric
half-Gaussian matrix law at the sharp first inverse-Wishart threshold. -/
theorem integrable_trace_nonsingInv_realWishartGram_mul_const_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 1 < k)
    (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((realWishartGram R)⁻¹ * D))
      (halfGaussianMatrix k p) := by
  let C := matrixEntryAbsMass D
  have htrace :=
    integrable_trace_nonsingInv_realWishartGram_halfGaussianMatrix hgap
  have hmajor : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        C * Matrix.trace (realWishartGram R)⁻¹)
      (halfGaussianMatrix k p) := htrace.const_mul C
  apply hmajor.mono'
  · exact
      (measurable_trace_nonsingInv_realWishartGram_mul_const D).aestronglyMeasurable
  · filter_upwards [] with R
    simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (matrixEntryAbsMass_nonneg D)
      (realWishartGram_inv_posSemidef R).trace_nonneg)] using
      (abs_trace_mul_le_matrixEntryAbsMass_mul_trace
        (realWishartGram R)⁻¹ D (realWishartGram_inv_posSemidef R))

/-- The real Gram map is continuous in the finite-dimensional matrix
topology used in this module. -/
theorem continuous_realWishartGram_genericSteinHaff
    {k p : Type*} [Fintype k] [Fintype p] :
    Continuous (realWishartGram : Matrix k p ℝ → Matrix p p ℝ) := by
  rw [continuous_iff_continuousAt]
  intro R
  exact (hasFDerivAt_realWishartGram R).continuousAt

/-- Coordinatewise measurability of the real Gram map, avoiding any
dependence on which equivalent finite-dimensional matrix norm is active. -/
theorem measurable_realWishartGram_genericSteinHaff
    {k p : Type*} [Fintype k] [Fintype p] :
    Measurable (realWishartGram : Matrix k p ℝ → Matrix p p ℝ) := by
  unfold realWishartGram
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

/-- A continuous real-valued function on a finite real matrix space is
measurable for the coordinatewise matrix sigma algebra. -/
theorem measurable_of_continuous_matrix_real_genericSteinHaff
    {a b : Type*} [Fintype a] [Fintype b]
    (f : Matrix a b ℝ → ℝ) (hf : Continuous f) : Measurable f := by
  exact hf.borel_measurable.mono
    (ge_of_eq
      (genericSteinHaffMatrixBorelSpace a b).measurable_eq)
    (le_of_eq BorelSpace.measurable_eq)

/-- The inverse-score density in the Stein--Haff identity is integrable for
every bounded continuous test. -/
theorem integrable_steinHaff_inverseScore_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 1 < k)
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (hphi : ContDiff ℝ 1 phi)
    (C₀ : ℝ) (hphiBound : ∀ M, |phi M| ≤ C₀)
    (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        phi (realWishartGram R) *
          (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)))
      (halfGaussianMatrix k p) := by
  have hscore :=
    (integrable_trace_nonsingInv_realWishartGram_mul_const_halfGaussianMatrix
      hgap D).const_mul
        (inverseGramScoreCoefficient (Fin k) (Fin p))
  have hphiMeas : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ phi (realWishartGram R)) :=
    (measurable_of_continuous_matrix_real_genericSteinHaff
      phi hphi.continuous).comp
        measurable_realWishartGram_genericSteinHaff
  apply hscore.bdd_mul hphiMeas.aestronglyMeasurable
  filter_upwards [] with R
  simpa [Real.norm_eq_abs] using hphiBound (realWishartGram R)

/-- The nonsingular right-hand density in the preserved-direction score
identity is integrable for every bounded continuous test.  The directional
derivative vanishes in that application, so no generic derivative
measurability lemma is needed here. -/
theorem integrable_steinHaff_preservedRight_halfGaussianMatrix
    {k p : ℕ}
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (hphi : ContDiff ℝ 1 phi)
    (C₀ : ℝ) (hphiBound : ∀ M, |phi M| ≤ C₀)
    (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        phi (realWishartGram R) * Matrix.trace D)
      (halfGaussianMatrix k p) := by
  have hGramMeas : Measurable
      (realWishartGram :
        Matrix (Fin k) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ) :=
    measurable_realWishartGram_genericSteinHaff
  have hphiMeas : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ phi (realWishartGram R)) :=
    (measurable_of_continuous_matrix_real_genericSteinHaff
      phi hphi.continuous).comp hGramMeas
  have hleft : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        phi (realWishartGram R) * Matrix.trace D)
      (halfGaussianMatrix k p) := by
    have hconst : Integrable
        (fun _R : Matrix (Fin k) (Fin p) ℝ ↦ Matrix.trace D)
        (halfGaussianMatrix k p) := integrable_const _
    apply hconst.bdd_mul hphiMeas.aestronglyMeasurable
    filter_upwards [] with R
    simpa [Real.norm_eq_abs] using hphiBound (realWishartGram R)
  exact hleft

/-- Both integrability conclusions of the internal numeric Stein--Haff
theorem. -/
theorem integrable_steinHaff_preservedPair_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 1 < k)
    (phi : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (hphi : ContDiff ℝ 1 phi)
    (C₀ : ℝ) (hphiBound : ∀ M, |phi M| ≤ C₀)
    (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        phi (realWishartGram R) *
          (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)))
      (halfGaussianMatrix k p) ∧
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        phi (realWishartGram R) * Matrix.trace D)
      (halfGaussianMatrix k p) := by
  exact ⟨integrable_steinHaff_inverseScore_halfGaussianMatrix
      hgap phi hphi C₀ hphiBound D,
    integrable_steinHaff_preservedRight_halfGaussianMatrix
      phi hphi C₀ hphiBound D⟩

end Wishart

end

end LogdetLean.GramHafnian
