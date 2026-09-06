import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseRealification
/-!
# Assembly of the deterministic Fourier-compression phase

The two endpoint cofactors are represented by the same matrix `L(q_R)`.
The background cofactors assemble into the sum of the exact `T(w_j,M_j)`
blocks.  No Gaussian integration is used here.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- Sum of the real block matrices associated with the background Fourier
weights. -/
def cofactorBackgroundPhaseMatrix {m k : ℕ}
    (A : TwoExposedColumnFamily m k) (w : Fin (m + 2) → ℂ) :
    Matrix (ComplexRealificationIndex k) (ComplexRealificationIndex k) ℝ :=
  fun i l ↦ ∑ j : Fin m,
    cofactorBilinearPhaseMatrix (w (remainingIndex m j)) (cofactorM A j) i l

theorem realTransposeBilinearPhase_fintype_sum
    {ι : Type*} [Fintype ι] {κ δ : Type*} [Fintype κ] [Fintype δ]
    (g : κ → ℝ) (T : ι → Matrix κ δ ℝ) (h : δ → ℝ) :
    realTransposeBilinearPhase g (fun p q ↦ ∑ i : ι, T i p q) h =
      ∑ i : ι, realTransposeBilinearPhase g (T i) h := by
  unfold realTransposeBilinearPhase
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    enter [2, p]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Each background Fourier coordinate contributes the exact real bilinear
block `T(w_j,M_{j,R})`. -/
theorem background_cofactor_phase_realification
    {m k : ℕ} (A : TwoExposedColumnFamily m k)
    (w : Fin (m + 2) → ℂ) (j : Fin m) :
    (w (remainingIndex m j) *
        twoExposedCofactorVector A (remainingIndex m j)).re =
      realTransposeBilinearPhase
        (complexRealification (A (exposedXIndex m)))
        (cofactorBilinearPhaseMatrix (w (remainingIndex m j)) (cofactorM A j))
        (complexRealification (A (exposedYIndex m))) := by
  rw [twoExposedCofactor_background_eq_transposeBilinear_X_M_Y]
  exact complex_bilinear_phase_realification _ _ _ _

/-- The background phase is one real bilinear form with matrix equal to the
sum of its exact coordinate blocks. -/
theorem background_cofactor_phase_sum_realification
    {m k : ℕ} (A : TwoExposedColumnFamily m k)
    (w : Fin (m + 2) → ℂ) :
    (∑ j : Fin m,
        w (remainingIndex m j) *
          twoExposedCofactorVector A (remainingIndex m j)).re =
      realTransposeBilinearPhase
        (complexRealification (A (exposedXIndex m)))
        (cofactorBackgroundPhaseMatrix A w)
        (complexRealification (A (exposedYIndex m))) := by
  rw [complex_sum_re]
  calc
    (∑ j : Fin m,
        (w (remainingIndex m j) *
          twoExposedCofactorVector A (remainingIndex m j)).re) =
        ∑ j : Fin m,
          realTransposeBilinearPhase
            (complexRealification (A (exposedXIndex m)))
            (cofactorBilinearPhaseMatrix
              (w (remainingIndex m j)) (cofactorM A j))
            (complexRealification (A (exposedYIndex m))) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact background_cofactor_phase_realification A w j
    _ = realTransposeBilinearPhase
        (complexRealification (A (exposedXIndex m)))
        (cofactorBackgroundPhaseMatrix A w)
        (complexRealification (A (exposedYIndex m))) := by
      symm
      exact realTransposeBilinearPhase_fintype_sum _ _ _

/-- The two endpoint terms use literally the same `L(q_R)`, with the
weights attached in the opposite displayed variable as required by
`C_X=Y^Tq_R` and `C_Y=X^Tq_R`. -/
theorem endpoint_cofactor_phase_same_linear_matrix
    {m k : ℕ} (A : TwoExposedColumnFamily m k)
    (wX wY : ℂ) :
    (wX * twoExposedCofactorVector A (exposedXIndex m)).re +
        (wY * twoExposedCofactorVector A (exposedYIndex m)).re =
      realTransposeLinearPhase
          (complexRealification (A (exposedXIndex m)))
          (cofactorLinearPhaseMatrix (cofactorQ A))
          (complexPhaseCoordinates wY) +
        realTransposeLinearPhase
          (complexRealification (A (exposedYIndex m)))
          (cofactorLinearPhaseMatrix (cofactorQ A))
          (complexPhaseCoordinates wX) := by
  rw [twoExposedCofactor_X_eq_transposeDot_Y_q,
    twoExposedCofactor_Y_eq_transposeDot_X_q,
    complex_linear_phase_realification,
    complex_linear_phase_realification]
  ring

/-- Exact deterministic conditional phase in the manuscript's
`g^T T_R h + g^T L_R b + h^T L_R a` form. -/
theorem two_exposed_cofactor_phase_exact_T_L_form
    {m k : ℕ} (A : TwoExposedColumnFamily m k)
    (w : Fin (m + 2) → ℂ) :
    (∑ j : Fin m,
        w (remainingIndex m j) *
          twoExposedCofactorVector A (remainingIndex m j)).re +
      (w (exposedXIndex m) *
        twoExposedCofactorVector A (exposedXIndex m)).re +
      (w (exposedYIndex m) *
        twoExposedCofactorVector A (exposedYIndex m)).re =
    realTransposeBilinearPhase
        (complexRealification (A (exposedXIndex m)))
        (cofactorBackgroundPhaseMatrix A w)
        (complexRealification (A (exposedYIndex m))) +
      realTransposeLinearPhase
        (complexRealification (A (exposedXIndex m)))
        (cofactorLinearPhaseMatrix (cofactorQ A))
        (complexPhaseCoordinates (w (exposedYIndex m))) +
      realTransposeLinearPhase
        (complexRealification (A (exposedYIndex m)))
        (cofactorLinearPhaseMatrix (cofactorQ A))
        (complexPhaseCoordinates (w (exposedXIndex m))) := by
  rw [background_cofactor_phase_sum_realification]
  have hend := endpoint_cofactor_phase_same_linear_matrix A
    (w (exposedXIndex m)) (w (exposedYIndex m))
  linarith

end

end LogdetLean.GramHafnian
