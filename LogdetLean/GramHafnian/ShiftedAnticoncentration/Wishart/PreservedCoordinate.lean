import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.WeightedDivergence
/-!
# The preserved transpose-Gram coordinate

The conditional Wishart score changes the Hermitian Gram coordinate `Q`
while preserving the symmetric transpose-Gram coordinate `S`.  This file
expresses that cancellation directly at the first-variation level and then
feeds it into the genuine weighted-divergence theorem.
-/

open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*}

/-- Upper-left block of a real matrix indexed by `m ⊕ m`. -/
def realGramBlock11 (M : Matrix (m ⊕ m) (m ⊕ m) ℝ) : Matrix m m ℝ :=
  fun i j ↦ M (Sum.inl i) (Sum.inl j)

/-- Upper-right block of a real matrix indexed by `m ⊕ m`. -/
def realGramBlock12 (M : Matrix (m ⊕ m) (m ⊕ m) ℝ) : Matrix m m ℝ :=
  fun i j ↦ M (Sum.inl i) (Sum.inr j)

/-- Lower-right block of a real matrix indexed by `m ⊕ m`. -/
def realGramBlock22 (M : Matrix (m ⊕ m) (m ⊕ m) ℝ) : Matrix m m ℝ :=
  fun i j ↦ M (Sum.inr i) (Sum.inr j)

/-- The symmetric complex coordinate extracted from a real block matrix. -/
def sCoordinateOfRealGram (M : Matrix (m ⊕ m) (m ⊕ m) ℝ) :
    Matrix m m ℂ :=
  sOfRealBlocks (realGramBlock11 M) (realGramBlock12 M)
    (realGramBlock22 M)

@[simp] theorem realGramBlock11_realBlockMatrix
    (U C V : Matrix m m ℝ) :
    realGramBlock11 (realBlockMatrix U C V) = U := by
  ext i j
  simp [realGramBlock11, realBlockMatrix]

@[simp] theorem realGramBlock12_realBlockMatrix
    (U C V : Matrix m m ℝ) :
    realGramBlock12 (realBlockMatrix U C V) = C := by
  ext i j
  simp [realGramBlock12, realBlockMatrix]

@[simp] theorem realGramBlock22_realBlockMatrix
    (U C V : Matrix m m ℝ) :
    realGramBlock22 (realBlockMatrix U C V) = V := by
  ext i j
  simp [realGramBlock22, realBlockMatrix]

@[simp] theorem sCoordinateOfRealGram_realBlockMatrix
    (U C V : Matrix m m ℝ) :
    sCoordinateOfRealGram (realBlockMatrix U C V) =
      sOfRealBlocks U C V := by
  simp [sCoordinateOfRealGram]

/-- First variation of the preserved `S` coordinate in rectangular
direction `F`. -/
def sCoordinateFirstVariation [Fintype k]
    (R F : Matrix k (m ⊕ m) ℝ) : Matrix m m ℂ :=
  sCoordinateOfRealGram (F.transpose * R + R.transpose * F)

/-- The score lift has zero first variation in the `S` coordinate. -/
theorem sCoordinateFirstVariation_stein_scoreDelta
    [Fintype k] [Fintype m] [DecidableEq m]
    (R : Matrix k (m ⊕ m) ℝ) {H : Matrix m m ℂ}
    (hH : H.IsHermitian)
    (hM : IsUnit (realWishartGram R).det) :
    sCoordinateFirstVariation R
        (steinVectorFieldValue R (scoreDeltaM H)) = 0 := by
  rw [sCoordinateFirstVariation,
    gram_firstVariation_steinVectorFieldValue R
      (scoreDeltaM_isSymm hH) hM]
  simpa [scoreDeltaM] using sOf_scoreDelta hH

/-- A scalar differential that factors through the `S` first variation
annihilates the conditional-Wishart score direction. -/
theorem differential_stein_scoreDelta_eq_zero
    [Fintype k] [Fintype m] [DecidableEq m]
    (g' : Matrix k (m ⊕ m) ℝ →L[ℝ] ℝ)
    (psi' : Matrix m m ℂ →L[ℝ] ℝ)
    (R : Matrix k (m ⊕ m) ℝ) {H : Matrix m m ℂ}
    (hH : H.IsHermitian)
    (hfactor : ∀ F, g' F = psi' (sCoordinateFirstVariation R F))
    (hM : IsUnit (realWishartGram R).det) :
    g' (steinVectorFieldValue R (scoreDeltaM H)) = 0 := by
  rw [hfactor, sCoordinateFirstVariation_stein_scoreDelta R hH hM,
    map_zero]

/-- Public pointwise conditional-score endpoint for a smooth scalar test
whose differential factors through the preserved `S` coordinate. -/
theorem weightedSteinCoordinateDivergence_scoreDelta_eq_mul
    [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
    (g : Matrix k (m ⊕ m) ℝ → ℝ)
    (g' : Matrix k (m ⊕ m) ℝ →L[ℝ] ℝ)
    (psi' : Matrix m m ℂ →L[ℝ] ℝ)
    (R : Matrix k (m ⊕ m) ℝ) {H : Matrix m m ℂ}
    (hH : H.IsHermitian)
    (hg : HasFDerivAt g g' R)
    (hfactor : ∀ F, g' F = psi' (sCoordinateFirstVariation R F))
    (hM : IsUnit (realWishartGram R).det) :
    weightedSteinCoordinateDivergence g R (scoreDeltaM H) =
      g R * steinVectorFieldCoordinateDivergence R (scoreDeltaM H) := by
  exact weightedSteinCoordinateDivergence_eq_mul g g' R (scoreDeltaM H) hg
    (differential_stein_scoreDelta_eq_zero g' psi' R hH hfactor hM) hM

end Wishart

end

end LogdetLean.GramHafnian
