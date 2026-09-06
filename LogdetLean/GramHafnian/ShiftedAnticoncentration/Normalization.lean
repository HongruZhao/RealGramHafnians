import LogdetLean.GramHafnian.ShiftedAnticoncentration.ConstantAlgebra
/-!
# Positivity and exact standard-deviation normalization
-/

namespace LogdetLean.GramHafnian

noncomputable section

theorem oddPairingNat_pos (n : ℕ) : 0 < oddPairingNat n := by
  unfold oddPairingNat
  apply Finset.prod_pos
  intro i hi
  omega

theorem closedFirstMoment_pos (k n : ℕ) (hk : 0 < k) :
    0 < closedFirstMoment k n := by
  rw [closedFirstMoment]
  have hodd : 0 < (oddPairingNat n : ℝ) := by
    exact_mod_cast oddPairingNat_pos n
  exact mul_pos hodd (dimensionProduct_pos k n hk)

theorem gramHafnianSigma_nonneg (k n : ℕ) :
    0 ≤ gramHafnianSigma k n := by
  exact Real.sqrt_nonneg _

theorem gramHafnianSigma_pos (k n : ℕ) (hk : 0 < k) :
    0 < gramHafnianSigma k n := by
  rw [gramHafnianSigma]
  exact Real.sqrt_pos.2 (closedFirstMoment_pos k n hk)

theorem gramHafnianSigma_sq (k n : ℕ) (hk : 0 < k) :
    gramHafnianSigma k n ^ 2 = closedFirstMoment k n := by
  rw [gramHafnianSigma, sq]
  exact Real.mul_self_sqrt (le_of_lt (closedFirstMoment_pos k n hk))

/-- The standard deviation in the shifted theorem is exactly the literal
second absolute moment of the existing Gaussian Gram-hafnian model. -/
theorem gramHafnianSigma_sq_eq_actualSecondMoment
    (k n : ℕ) (hk : 0 < k) :
    gramHafnianSigma k n ^ 2 = actualGramFirstMomentReal k n := by
  rw [gramHafnianSigma_sq k n hk,
    actualGramFirstMomentReal_eq_closedFirstMoment k n hk]

end

end LogdetLean.GramHafnian
