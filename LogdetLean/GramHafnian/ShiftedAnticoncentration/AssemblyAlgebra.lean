import LogdetLean.GramHafnian.ShiftedAnticoncentration.LaplaceOrder
/-!
# Final normalization assembly

This file records the last deterministic implication in the proof.  Its
analytic hypothesis is supplied later by the literal cofactor-energy theorem;
no public result will retain that hypothesis.
-/

namespace LogdetLean.GramHafnian

noncomputable section

/-- A raw disk estimate with coefficient bounded by the inverse-variance
product yields the exact normalized coefficient `B_{k,n}`. -/
theorem normalizedSmallBall_of_rawInverseVarianceBound
    (k n : ℕ) (hn : 1 ≤ n) (hk : 0 < k)
    (z : ℂ) (ε inverseCoefficient : ℝ)
    (hε : 0 ≤ ε)
    (hraw : gramHafnianShiftedSmallBallProbability k n z ε ≤
      (ε * gramHafnianSigma k n) ^ 2 * inverseCoefficient)
    (hinv : inverseCoefficient ≤ inverseVarianceBound k n) :
    gramHafnianShiftedSmallBallProbability k n z ε ≤
      shiftedAnticoncentrationConstant k n * ε ^ 2 := by
  calc
    gramHafnianShiftedSmallBallProbability k n z ε ≤
        (ε * gramHafnianSigma k n) ^ 2 * inverseCoefficient := hraw
    _ ≤ (ε * gramHafnianSigma k n) ^ 2 *
        inverseVarianceBound k n :=
      mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = shiftedAnticoncentrationConstant k n * ε ^ 2 := by
      rw [mul_pow, gramHafnianSigma_sq k n hk]
      rw [← closedFirstMoment_mul_inverseVarianceBound k n hn]
      ring

/-- Paper-range specialization; `k ≥ 4n`, `n ≥ 1` automatically supplies
the positivity needed by the exact variance normalization. -/
theorem normalizedSmallBall_of_paperInverseVarianceBound
    (k n : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (z : ℂ) (ε inverseCoefficient : ℝ)
    (hε : 0 ≤ ε)
    (hraw : gramHafnianShiftedSmallBallProbability k n z ε ≤
      (ε * gramHafnianSigma k n) ^ 2 * inverseCoefficient)
    (hinv : inverseCoefficient ≤ inverseVarianceBound k n) :
    gramHafnianShiftedSmallBallProbability k n z ε ≤
      shiftedAnticoncentrationConstant k n * ε ^ 2 := by
  apply normalizedSmallBall_of_rawInverseVarianceBound
    k n hn (by omega) z ε inverseCoefficient hε hraw hinv

end

end LogdetLean.GramHafnian
