import LogdetLean.GramHafnian.Final
import Mathlib.MeasureTheory.Measure.Real
/-!
# Shifted small balls for Gaussian Gram hafnians

This file fixes the literal event, probability, normalization, and explicit
constant in the shifted anticoncentration theorem.  The random matrix is the
existing product of standard circular complex Gaussian columns, and the
observable is the existing literal finite hafnian of the transpose Gram
matrix.  No asymptotic surrogate is introduced.
-/

open scoped BigOperators
open MeasureTheory Set

namespace LogdetLean.GramHafnian

noncomputable section

/-- The literal complex Gaussian Gram-hafnian observable. -/
def gramHafnianObservable (n k : ℕ) (X : ComplexColumnMatrix n k) : ℂ :=
  gramHafnian (rowMatrix X)

/-- The exact standard-deviation normalization used in the paper. -/
def gramHafnianSigma (k n : ℕ) : ℝ :=
  Real.sqrt (closedFirstMoment k n)

/-- A closed disk of radius `ε σ_{k,n}` centered at an arbitrary complex
shift `z`, pulled back by the literal Gram-hafnian observable. -/
def gramHafnianShiftedSmallBallEvent
    (k n : ℕ) (z : ℂ) (ε : ℝ) : Set (ComplexColumnMatrix n k) :=
  {X | ‖gramHafnianObservable n k X - z‖ ≤
      ε * gramHafnianSigma k n}

/-- The real-valued probability of the shifted small-ball event. -/
def gramHafnianShiftedSmallBallProbability
    (k n : ℕ) (z : ℂ) (ε : ℝ) : ℝ :=
  (circularGaussianColumnMatrixMeasure n k).real
    (gramHafnianShiftedSmallBallEvent k n z ε)

/-- The exact finite coefficient in the shifted `ε²` bound.  Writing every
factor in `ℝ` avoids any hidden truncated subtraction in the denominators. -/
def shiftedAnticoncentrationConstant (k n : ℕ) : ℝ :=
  (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n *
    ((k : ℝ) / ((k : ℝ) - 1)) *
    ∏ r ∈ Finset.Icc 2 n,
      (((k : ℝ) + 2 * (r : ℝ) - 2) /
        ((k : ℝ) - 4 * (r : ℝ) + 1))

/-- The finite shifted-anticoncentration assertion proved in the paper.  It is
recorded as a proposition before its proof is assembled so every intermediate
module can target the exact public endpoint. -/
def GaussianGramHafnianShiftedAnticoncentration : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 4 * n ≤ k →
    ∀ z : ℂ, ∀ ε : ℝ, 0 ≤ ε →
      gramHafnianShiftedSmallBallProbability k n z ε ≤
        shiftedAnticoncentrationConstant k n * ε ^ 2

end

end LogdetLean.GramHafnian
