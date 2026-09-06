import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.InverseTraceIntegrability
/-!
# A common integrable majorant for half-Gaussian matrices

The singular Stein-field estimates repeatedly reduce to the same scalar
majorant

`1 + rectangularSqMass R + trace ((Rᵀ R)⁻¹)`.

This file packages its measurability and integrability at the sharp first
inverse-Wishart threshold.  The proof of the rectangular mass moment is
coordinatewise: each scalar entry has every finite Gaussian moment, and the
matrix law is the measurable-equivalence image of the finite product law.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- The squared Frobenius mass is a measurable function of a finite real
matrix. -/
theorem measurable_rectangularSqMass
    {k p : Type*} [Fintype k] [Fintype p] :
    Measurable (rectangularSqMass : Matrix k p ℝ → ℝ) := by
  unfold rectangularSqMass
  fun_prop

/-- Every scalar coordinate square is integrable under the iid
variance-one-half Gaussian product law. -/
theorem integrable_halfGaussianPi_coordinate_sq
    {n : ℕ} (i : Fin n) :
    Integrable (fun x : Fin n → ℝ ↦ (x i) ^ 2) (halfGaussianPi n) := by
  have hLp : MemLp (fun x : Fin n → ℝ ↦ x i) 2 (halfGaussianPi n) := by
    have hscalar : MemLp id 2
        (gaussianReal 0 halfGaussianVariance) :=
      memLp_id_gaussianReal 2
    have h := hscalar.comp_measurePreserving
      (measurePreserving_eval
        (fun _ : Fin n ↦ gaussianReal 0 halfGaussianVariance) i)
    simpa [halfGaussianPi, Function.comp_def] using h
  exact hLp.integrable_sq

/-- The squared Frobenius mass of an iid half-Gaussian numeric matrix is
integrable. -/
theorem integrable_rectangularSqMass_halfGaussianMatrix (k p : ℕ) :
    Integrable
      (rectangularSqMass : Matrix (Fin k) (Fin p) ℝ → ℝ)
      (halfGaussianMatrix k p) := by
  let e := flatMatrixMeasurableEquiv k p
  let ν := halfGaussianPi (k * p)
  let μ := halfGaussianMatrix k p
  have hflat : Integrable
      (fun x : Fin (k * p) → ℝ ↦
        ∑ a : Fin k, ∑ i : Fin p,
          (x (finProdFinEquiv (a, i))) ^ 2) ν := by
    apply integrable_finsetSum
    intro a _ha
    apply integrable_finsetSum
    intro i _hi
    exact integrable_halfGaussianPi_coordinate_sq
      (finProdFinEquiv (a, i))
  have hsource : Integrable
      (fun x : Fin (k * p) → ℝ ↦ rectangularSqMass (e x)) ν := by
    simpa [e, rectangularSqMass] using hflat
  have hinv : MeasurePreserving e.symm μ ν :=
    (measurePreserving_flatMatrixMeasurableEquiv k p).symm e
  have h := hinv.integrable_comp_of_integrable hsource
  simpa [Function.comp_def, e, μ, ν] using h

/-- Constant real functions are integrable under the half-Gaussian matrix
probability law. -/
theorem integrable_const_halfGaussianMatrix
    (k p : ℕ) (c : ℝ) :
    Integrable (fun _R : Matrix (Fin k) (Fin p) ℝ ↦ c)
      (halfGaussianMatrix k p) :=
  integrable_const c

/-- The nonsingular inverse of a real Gram matrix is positive semidefinite,
so its trace is nonnegative, including on the singular set where the
nonsingular-inverse convention is zero. -/
theorem trace_nonsingInv_realWishartGram_nonneg
    {k p : Type*} [Fintype k] [Fintype p] [DecidableEq p]
    (R : Matrix k p ℝ) :
    0 ≤ Matrix.trace (realWishartGram R)⁻¹ := by
  have hGram : (realWishartGram R).PosSemidef := by
    simpa [realWishartGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self R)
  exact hGram.inv.trace_nonneg

/-- The common scalar majorant used for all singular Stein-field
components. -/
def halfGaussianMatrixMassMajorant (k p : ℕ)
    (R : Matrix (Fin k) (Fin p) ℝ) : ℝ :=
  1 + rectangularSqMass R + Matrix.trace (realWishartGram R)⁻¹

theorem halfGaussianMatrixMassMajorant_nonneg
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    0 ≤ halfGaussianMatrixMassMajorant k p R := by
  unfold halfGaussianMatrixMassMajorant
  have hm := rectangularSqMass_nonneg R
  have ht := trace_nonsingInv_realWishartGram_nonneg R
  positivity

theorem measurable_halfGaussianMatrixMassMajorant (k p : ℕ) :
    Measurable (halfGaussianMatrixMassMajorant k p) := by
  unfold halfGaussianMatrixMassMajorant
  exact (measurable_const.add measurable_rectangularSqMass).add
    (measurable_trace_nonsingInv_realWishartGram k p)

/-- At `p + 1 < k`, the common matrix-mass/inverse-trace majorant is
integrable. -/
theorem integrable_halfGaussianMatrixMassMajorant
    {k p : ℕ} (hgap : p + 1 < k) :
    Integrable (halfGaussianMatrixMassMajorant k p)
      (halfGaussianMatrix k p) := by
  unfold halfGaussianMatrixMassMajorant
  exact ((integrable_const_halfGaussianMatrix k p 1).add
    (integrable_rectangularSqMass_halfGaussianMatrix k p)).add
      (integrable_trace_nonsingInv_realWishartGram_halfGaussianMatrix hgap)

/-- Generic dominated-integrability endpoint.  It is intentionally stated
with an almost-everywhere bound, so cutoff modifications on the singular set
can be fed into it directly. -/
theorem integrable_of_abs_le_const_mul_halfGaussianMatrixMassMajorant
    {k p : ℕ} (hgap : p + 1 < k)
    {f : Matrix (Fin k) (Fin p) ℝ → ℝ}
    (hf : AEStronglyMeasurable f (halfGaussianMatrix k p))
    (C : ℝ)
    (hbound : ∀ᵐ R ∂halfGaussianMatrix k p,
      |f R| ≤ C * halfGaussianMatrixMassMajorant k p R) :
    Integrable f (halfGaussianMatrix k p) := by
  have hmajor : Integrable
      (fun R ↦ C * halfGaussianMatrixMassMajorant k p R)
      (halfGaussianMatrix k p) :=
    (integrable_halfGaussianMatrixMassMajorant hgap).const_mul C
  apply hmajor.mono' hf
  filter_upwards [hbound] with R hR
  exact hR

/-- Pointwise-bound convenience form of the common domination endpoint. -/
theorem integrable_of_abs_le_const_mul_halfGaussianMatrixMassMajorant_all
    {k p : ℕ} (hgap : p + 1 < k)
    {f : Matrix (Fin k) (Fin p) ℝ → ℝ}
    (hf : AEStronglyMeasurable f (halfGaussianMatrix k p))
    (C : ℝ)
    (hbound : ∀ R,
      |f R| ≤ C * halfGaussianMatrixMassMajorant k p R) :
    Integrable f (halfGaussianMatrix k p) :=
  integrable_of_abs_le_const_mul_halfGaussianMatrixMassMajorant
    hgap hf C (Filter.Eventually.of_forall hbound)

end Wishart

end


end LogdetLean.GramHafnian
