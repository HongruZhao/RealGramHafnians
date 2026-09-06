import LogdetLean.GramHafnian.RankTwoOrthogonalInvariance
/-!
# Algebraic eigen-reduction of the rank-two kernel

For deterministic vectors `g₁,g₂`, the symmetric operator

`x ↦ <g₂,x> g₁ + <g₁,x> g₂`

has its two possible nonzero eigenvalues at `C ± A B`, where
`A²=<g₁,g₁>`, `B²=<g₂,g₂>`, and `C=<g₁,g₂>`.  The proof below
is elementary inner-product algebra and has no probability assumptions.
-/

namespace LogdetLean.GramHafnian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- The symmetric rank-two action associated with `(g₁,g₂)`. -/
def rankTwoAction (g₁ g₂ x : E) : E :=
  (inner Real g₂ x) • g₁ + (inner Real g₁ x) • g₂

/-- Candidate eigenvector for the eigenvalue `C + A*B`. -/
def rankTwoEigenPlus (A B : Real) (g₁ g₂ : E) : E :=
  B • g₁ + A • g₂

/-- Candidate eigenvector for the eigenvalue `C - A*B`. -/
def rankTwoEigenMinus (A B : Real) (g₁ g₂ : E) : E :=
  B • g₁ - A • g₂

/-- The bilinear statistic is the matrix coefficient of `rankTwoAction`. -/
theorem inner_rankTwoAction_eq_innerRankTwoBilinear
    (g₁ g₂ : E) (w : E × E) :
    inner Real w.1 (rankTwoAction g₁ g₂ w.2) =
      innerRankTwoBilinear g₁ g₂ w := by
  unfold rankTwoAction innerRankTwoBilinear
  simp only [inner_add_right, inner_smul_right]
  rw [real_inner_comm w.1 g₁, real_inner_comm w.1 g₂]
  ring

/-- Exact plus-eigenvector calculation. -/
theorem rankTwoAction_eigenPlus
    (g₁ g₂ : E) (A B C : Real)
    (h₁₁ : inner Real g₁ g₁ = A ^ 2)
    (h₂₂ : inner Real g₂ g₂ = B ^ 2)
    (h₁₂ : inner Real g₁ g₂ = C) :
    rankTwoAction g₁ g₂ (rankTwoEigenPlus A B g₁ g₂) =
      (C + A * B) • rankTwoEigenPlus A B g₁ g₂ := by
  have h₂₁ : inner Real g₂ g₁ = C := by
    rw [real_inner_comm]
    exact h₁₂
  unfold rankTwoAction rankTwoEigenPlus
  simp only [inner_add_right, inner_smul_right, smul_add, smul_smul]
  rw [h₁₁, h₂₂, h₁₂, h₂₁]
  module

/-- Exact minus-eigenvector calculation. -/
theorem rankTwoAction_eigenMinus
    (g₁ g₂ : E) (A B C : Real)
    (h₁₁ : inner Real g₁ g₁ = A ^ 2)
    (h₂₂ : inner Real g₂ g₂ = B ^ 2)
    (h₁₂ : inner Real g₁ g₂ = C) :
    rankTwoAction g₁ g₂ (rankTwoEigenMinus A B g₁ g₂) =
      (C - A * B) • rankTwoEigenMinus A B g₁ g₂ := by
  have h₂₁ : inner Real g₂ g₁ = C := by
    rw [real_inner_comm]
    exact h₁₂
  unfold rankTwoAction rankTwoEigenMinus
  simp only [inner_sub_right, inner_smul_right, smul_sub, smul_smul]
  rw [h₁₁, h₂₂, h₁₂, h₂₁]
  module

/-- The two candidate eigenvectors are orthogonal. -/
theorem inner_rankTwoEigenPlus_eigenMinus
    (g₁ g₂ : E) (A B C : Real)
    (h₁₁ : inner Real g₁ g₁ = A ^ 2)
    (h₂₂ : inner Real g₂ g₂ = B ^ 2)
    (h₁₂ : inner Real g₁ g₂ = C) :
    inner Real (rankTwoEigenPlus A B g₁ g₂)
      (rankTwoEigenMinus A B g₁ g₂) = 0 := by
  have h₂₁ : inner Real g₂ g₁ = C := by
    rw [real_inner_comm]
    exact h₁₂
  unfold rankTwoEigenPlus rankTwoEigenMinus
  simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [h₁₁, h₂₂, h₁₂, h₂₁]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- Every vector orthogonal to both inputs lies in the zero eigenspace. -/
theorem rankTwoAction_eq_zero_of_inner_eq_zero
    (g₁ g₂ x : E)
    (h₁ : inner Real g₁ x = 0) (h₂ : inner Real g₂ x = 0) :
    rankTwoAction g₁ g₂ x = 0 := by
  simp [rankTwoAction, h₁, h₂]

end LogdetLean.GramHafnian
