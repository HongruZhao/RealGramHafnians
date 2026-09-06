import LogdetLean.GramHafnian.ShiftedAnticoncentration.AssemblyAlgebra
import Mathlib.Probability.Distributions.Gaussian.Multivariate
/-!
# Auxiliary-Gaussian representation of radial Laplace kernels

This replaces an explicit Fourier-inversion calculation: averaging a
characteristic function over an independent standard real Gaussian gives the
radial kernel `exp (-t ‖x‖²)` with its exact normalization.
-/

open MeasureTheory ProbabilityTheory Real

namespace LogdetLean.GramHafnian

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem auxiliaryGaussian_charFun_identity
    (x : E) (t : ℝ) (ht : 0 ≤ t) :
    charFun (stdGaussian E) (Real.sqrt (2 * t) • x) =
      Complex.exp (-(t * ‖x‖ ^ 2)) := by
  rw [charFun_stdGaussian]
  have hsqrt : Real.sqrt (2 * t) ^ 2 = 2 * t := by
    rw [sq_sqrt]
    linarith
  have hnorm : ‖Real.sqrt (2 * t) • x‖ ^ 2 =
      (2 * t) * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hsqrt]
  congr 1
  norm_cast
  rw [hnorm]
  ring

end

end LogdetLean.GramHafnian
