import LogdetLean.GeneralRDecomposition
import Mathlib.RingTheory.Polynomial.Hermite.Basic
/-!
# Elementary Hermite algebra for the logarithmic radial residual

This is the pointwise algebra in Zhao, arXiv:2608.00565v1, Lemma 5.2,
printed p. 11, expanded in the manuscript subsection “Direct computation of
the second chaos projection.”  Mathlib supplies the probabilists' Hermite
polynomials.  We verify that `u_m` is exactly the displayed sum of `H_2`
terms and that the residual is even in every coordinate separately.

These identities identify the *candidate* second-chaos polynomial and remove
all odd-coordinate coefficients.  They do not by themselves prove the L2
completeness/Mehler expansion or the orthogonal-projection coefficient of the
logarithm.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Module WithLp
open scoped BigOperators MatrixOrder RealInnerProductSpace

/-- Evaluation of Mathlib's probabilists' Hermite polynomial in `ℝ`. -/
def probabilistsHermiteEval (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.eval₂ (Int.castRingHom ℝ) x (Polynomial.hermite n)

@[simp]
theorem probabilistsHermiteEval_zero (x : ℝ) :
    probabilistsHermiteEval 0 x = 1 := by
  simp [probabilistsHermiteEval, Polynomial.hermite_zero]

@[simp]
theorem probabilistsHermiteEval_one (x : ℝ) :
    probabilistsHermiteEval 1 x = x := by
  simp [probabilistsHermiteEval]

@[simp]
theorem probabilistsHermiteEval_two (x : ℝ) :
    probabilistsHermiteEval 2 x = x ^ 2 - 1 := by
  norm_num [probabilistsHermiteEval, Polynomial.hermite_succ,
    Polynomial.hermite_one, Polynomial.hermite_zero]
  ring

/-- Multivariate tensor-product Hermite polynomial. -/
def multiHermite {m : ℕ} (alpha : Fin m → ℕ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∏ k, probabilistsHermiteEval (alpha k) (x k)

/-- Total Hermite degree of a multi-index. -/
def hermiteTotalDegree {m : ℕ} (alpha : Fin m → ℕ) : ℕ :=
  ∑ k, alpha k

/-- Multi-index factorial appearing in Hermite orthogonality. -/
def hermiteMultiFactorial {m : ℕ} (alpha : Fin m → ℕ) : ℕ :=
  ∏ k, (alpha k).factorial

namespace GeneralRDecomposition

/-- The paper's linear fluctuation is pointwise the average of the
coordinatewise second probabilists' Hermite polynomials. -/
theorem u_m_eq_average_hermite_two (m : ℕ)
    (x : EuclideanSpace ℝ (Fin m)) :
    u_m m x = (1 / (m : ℝ)) *
      ∑ k, probabilistsHermiteEval 2 (x k) := by
  unfold u_m
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [probabilistsHermiteEval_two, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  ring

/-- Flip one coordinate of a Euclidean vector. -/
def flipCoordinate {m : ℕ} (k : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (Function.update (fun i ↦ x i) k (-x k))

@[simp]
theorem flipCoordinate_apply_same {m : ℕ} (k : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) : flipCoordinate k x k = -x k := by
  simp [flipCoordinate]

@[simp]
theorem flipCoordinate_apply_of_ne {m : ℕ} {k l : Fin m}
    (h : l ≠ k) (x : EuclideanSpace ℝ (Fin m)) :
    flipCoordinate k x l = x l := by
  simp [flipCoordinate, h]

theorem flipCoordinate_norm_sq {m : ℕ} (k : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖flipCoordinate k x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases h : l = k
  · subst l
    simp
  · simp [h]

theorem h_m_flipCoordinate {m : ℕ} (k : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    h_m m (flipCoordinate k x) = h_m m x := by
  simp only [h_m, flipCoordinate_norm_sq]

theorem u_m_flipCoordinate {m : ℕ} (k : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    u_m m (flipCoordinate k x) = u_m m x := by
  simp only [u_m, flipCoordinate_norm_sq]

/-- The nonlinear residual is even in each coordinate separately, the exact
symmetry used in the paper to eliminate Hermite multi-indices containing an
odd component. -/
theorem e_m_flipCoordinate {m : ℕ} (k : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    e_m m (flipCoordinate k x) = e_m m x := by
  simp only [e_m, h_m_flipCoordinate, u_m_flipCoordinate]

end GeneralRDecomposition

end

end LogdetLean
