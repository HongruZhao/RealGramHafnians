import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.ScoreTransformPairing
/-!
# Splitting a realified complex matrix into real and imaginary blocks

The Gaussian IBP layer is naturally phrased on a real matrix with twice as
many columns.  These identities connect that literal matrix to the `(X,Y)`
notation used by the real-to-complex transform.
-/

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {k m : Type*} [Fintype k] [Fintype m]
  [DecidableEq k] [DecidableEq m]

def realMatrixLeft (R : Matrix k (m ⊕ m) ℝ) : Matrix k m ℝ :=
  fun a i ↦ R a (Sum.inl i)

def realMatrixRight (R : Matrix k (m ⊕ m) ℝ) : Matrix k m ℝ :=
  fun a i ↦ R a (Sum.inr i)

theorem realColumnPair_left_right (R : Matrix k (m ⊕ m) ℝ) :
    realColumnPair (realMatrixLeft R) (realMatrixRight R) = R := by
  ext a i
  cases i <;> rfl

theorem realPairGram_left_right (R : Matrix k (m ⊕ m) ℝ) :
    realPairGram (realMatrixLeft R) (realMatrixRight R) =
      realWishartGram R := by
  unfold realPairGram realWishartGram
  rw [realColumnPair_left_right]

/-- Complex matrix represented by a real matrix whose left and right blocks
are its real and imaginary parts. -/
def complexOfRealMatrix (R : Matrix k (m ⊕ m) ℝ) : Matrix k m ℂ :=
  complexOfRealPair (realMatrixLeft R) (realMatrixRight R)

/-- Nonsingularity of the real Gram implies nonsingularity of the coupled
complex Gram by the fixed invertible congruence. -/
theorem coupledGramKernel_det_isUnit_of_realPairGram
    (X Y : Matrix k m ℝ)
    (hM : IsUnit (realPairGram X Y).det) :
    IsUnit (coupledGramKernel (complexOfRealPair X Y)).det := by
  have hMc : IsUnit ((realPairGram X Y).map Complex.ofReal).det := by
    change IsUnit (Complex.ofRealHom.mapMatrix (realPairGram X Y)).det
    rw [← Complex.ofRealHom.map_det]
    exact hM.map Complex.ofRealHom
  have hMmat : IsUnit ((realPairGram X Y).map Complex.ofReal) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hMc
  have hL : IsUnit
      (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ) :=
    complexPairTransform_isUnit
  have hLH : IsUnit
      (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ).conjTranspose :=
    (Matrix.isUnit_conjTranspose _).mpr hL
  have hKmat : IsUnit (coupledGramKernel (complexOfRealPair X Y)) := by
    rw [coupledGramKernel_eq_transform_congruence]
    exact (hLH.mul hMmat).mul hL
  exact (Matrix.isUnit_iff_isUnit_det _).mp hKmat

/-- Factor-two trace pairing directly on the realified matrix model. -/
theorem realWishartGram_inverse_rankOne_score_trace_eq_coupled
    (R : Matrix k (m ⊕ m) ℝ) (c : m → ℂ)
    (hM : IsUnit (realWishartGram R).det) :
    Matrix.trace
        ((realWishartGram R)⁻¹ * scoreDeltaM (hermitianRankOne c)) =
      2 * quadraticFormReal
        (Matrix.toBlocks₁₁ (coupledGramKernel (complexOfRealMatrix R))⁻¹) c := by
  have hMpair : IsUnit
      (realPairGram (realMatrixLeft R) (realMatrixRight R)).det := by
    simpa [realPairGram_left_right] using hM
  have hK := coupledGramKernel_det_isUnit_of_realPairGram
    (realMatrixLeft R) (realMatrixRight R) hMpair
  simpa [complexOfRealMatrix, realPairGram_left_right] using
    (realPairGram_inverse_rankOne_score_trace_eq_coupled
      (realMatrixLeft R) (realMatrixRight R) c hMpair hK)

end Wishart

end

end LogdetLean.GramHafnian
