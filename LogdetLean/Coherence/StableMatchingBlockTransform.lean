import LogdetLean.Coherence.StableMatchingColumnMix
import LogdetLean.Coherence.NoncentralPearsonRuben
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
/-!
# The explicit disjoint `2 × 2` matching transform

The coordinate type is `(Fin 2 × Fin s) ⊕ Fin r`: `s` correlated pairs and
`r` untouched singleton columns.  Each pair is generated from two independent
columns by the upper-triangular block

`[[1, rho_e], [0, sqrt(1-rho_e²)]]`.

The determinant calculation is exact and finite-sample.
-/

namespace LogdetLean.Coherence

noncomputable section

open scoped BigOperators

/-- One upper-triangular Gaussian correlation-generating block. -/
def pairMixBlock (rho : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, rho; 0, Real.sqrt (1 - rho ^ 2)]

@[simp] theorem det_pairMixBlock (rho : ℝ) :
    (pairMixBlock rho).det = Real.sqrt (1 - rho ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [pairMixBlock]

/-- Block-diagonal matching transform, followed by an identity singleton
block. -/
def matchingMixMatrix (s r : ℕ) (rho : Fin s → ℝ) :
    Matrix (Sum (Fin 2 × Fin s) (Fin r))
      (Sum (Fin 2 × Fin s) (Fin r)) ℝ :=
  Matrix.fromBlocks
    (Matrix.blockDiagonal fun e : Fin s ↦ pairMixBlock (rho e)) 0 0 1

/-- Exact determinant of the full matching transform. -/
theorem det_matchingMixMatrix (s r : ℕ) (rho : Fin s → ℝ) :
    (matchingMixMatrix s r rho).det =
      ∏ e, Real.sqrt (1 - rho e ^ 2) := by
  unfold matchingMixMatrix
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_blockDiagonal,
    Matrix.det_one, mul_one]
  apply Finset.prod_congr rfl
  intro e _he
  exact det_pairMixBlock (rho e)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The mixed first column of a planted pair is unchanged. -/
@[simp] theorem mixColumnFamily_matchingMixMatrix_pair_zero
    (s r : ℕ) (rho : Fin s → ℝ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E) (e : Fin s) :
    mixColumnFamily (matchingMixMatrix s r rho) v (Sum.inl (0, e)) =
      v (Sum.inl (0, e)) := by
  classical
  unfold mixColumnFamily matchingMixMatrix pairMixBlock
  simp [Matrix.blockDiagonal_apply, ← Finset.univ_product_univ,
    Finset.sum_product]

/-- The mixed second column has the desired correlated-Gaussian form. -/
@[simp] theorem mixColumnFamily_matchingMixMatrix_pair_one
    (s r : ℕ) (rho : Fin s → ℝ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E) (e : Fin s) :
    mixColumnFamily (matchingMixMatrix s r rho) v (Sum.inl (1, e)) =
      correlatedSecondColumn (rho e)
        (v (Sum.inl (0, e))) (v (Sum.inl (1, e))) := by
  classical
  unfold mixColumnFamily matchingMixMatrix pairMixBlock correlatedSecondColumn
  simp [Matrix.blockDiagonal_apply, ← Finset.univ_product_univ,
    Finset.sum_product]

/-- Singleton columns are untouched. -/
@[simp] theorem mixColumnFamily_matchingMixMatrix_singleton
    (s r : ℕ) (rho : Fin s → ℝ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E) (j : Fin r) :
    mixColumnFamily (matchingMixMatrix s r rho) v (Sum.inr j) =
      v (Sum.inr j) := by
  classical
  unfold mixColumnFamily matchingMixMatrix
  simp [Matrix.one_apply]

/-- Exact cancellation of unchanged first and singleton column norms. -/
theorem matchingMix_normProduct_ratio
    (s r : ℕ) (rho : Fin s → ℝ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hv : ∀ i, v i ≠ 0)
    (hTv : ∀ i, mixColumnFamily (matchingMixMatrix s r rho) v i ≠ 0) :
    (∏ i, ‖v i‖ ^ 2) /
        (∏ i, ‖mixColumnFamily (matchingMixMatrix s r rho) v i‖ ^ 2) =
      (∏ e, ‖v (Sum.inl (1, e))‖ ^ 2) /
        (∏ e,
          ‖correlatedSecondColumn (rho e)
            (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))‖ ^ 2) := by
  classical
  let A : ℝ := ∏ e, ‖v (Sum.inl (0, e))‖ ^ 2
  let B : ℝ := ∏ e, ‖v (Sum.inl (1, e))‖ ^ 2
  let C : ℝ := ∏ j, ‖v (Sum.inr j)‖ ^ 2
  let D : ℝ := ∏ e,
    ‖correlatedSecondColumn (rho e)
      (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))‖ ^ 2
  have hA : A ≠ 0 := by
    dsimp [A]
    apply Finset.prod_ne_zero_iff.mpr
    intro e _he
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv (Sum.inl (0, e))))
  have hB : B ≠ 0 := by
    dsimp [B]
    apply Finset.prod_ne_zero_iff.mpr
    intro e _he
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv (Sum.inl (1, e))))
  have hC : C ≠ 0 := by
    dsimp [C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _hj
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv (Sum.inr j)))
  have hD : D ≠ 0 := by
    dsimp [D]
    apply Finset.prod_ne_zero_iff.mpr
    intro e _he
    have h := hTv (Sum.inl (1, e))
    rw [mixColumnFamily_matchingMixMatrix_pair_one] at h
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  have hnull : (∏ i, ‖v i‖ ^ 2) = A * B * C := by
    rw [Fintype.prod_sum_type, Fintype.prod_prod_type_right]
    simp only [Fin.prod_univ_two]
    dsimp [A, B, C]
    rw [Finset.prod_mul_distrib]
  have halt :
      (∏ i, ‖mixColumnFamily (matchingMixMatrix s r rho) v i‖ ^ 2) =
        A * D * C := by
    rw [Fintype.prod_sum_type, Fintype.prod_prod_type_right]
    simp only [Fin.prod_univ_two]
    simp_rw [mixColumnFamily_matchingMixMatrix_pair_zero,
      mixColumnFamily_matchingMixMatrix_pair_one,
      mixColumnFamily_matchingMixMatrix_singleton]
    dsimp [A, D, C]
    rw [Finset.prod_mul_distrib]
  rw [hnull, halt]
  change A * B * C / (A * D * C) = B / D
  field_simp [hA, hB, hC, hD]

/-- Exact normalized-Gram determinant identity for `s` planted pairs and
`r` untouched columns. -/
theorem det_normalizedGram_matchingMix
    (s r : ℕ) (rho : Fin s → ℝ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hrho : ∀ e, |rho e| ≤ 1)
    (hv : ∀ i, v i ≠ 0)
    (hTv : ∀ i, mixColumnFamily (matchingMixMatrix s r rho) v i ≠ 0) :
    (normalizedGram
        (mixColumnFamily (matchingMixMatrix s r rho) v)).det =
      (∏ e, (1 - rho e ^ 2)) * (normalizedGram v).det *
        (∏ i, ‖v i‖ ^ 2) /
          (∏ i,
            ‖mixColumnFamily (matchingMixMatrix s r rho) v i‖ ^ 2) := by
  rw [det_normalizedGram_mixColumnFamily _ _ hv hTv,
    det_matchingMixMatrix]
  have hprod : (∏ e, Real.sqrt (1 - rho e ^ 2)) ^ 2 =
      ∏ e, (1 - rho e ^ 2) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro e _he
    rw [Real.sq_sqrt]
    exact sub_nonneg.mpr ((sq_le_one_iff_abs_le_one (rho e)).2 (hrho e))
  rw [hprod]

/-- Refined determinant coupling: only second-column radial normalization
survives after cancellation. -/
theorem det_normalizedGram_matchingMix_refined
    (s r : ℕ) (rho : Fin s → ℝ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hrho : ∀ e, |rho e| ≤ 1)
    (hv : ∀ i, v i ≠ 0)
    (hTv : ∀ i, mixColumnFamily (matchingMixMatrix s r rho) v i ≠ 0) :
    (normalizedGram
        (mixColumnFamily (matchingMixMatrix s r rho) v)).det =
      (∏ e, (1 - rho e ^ 2)) * (normalizedGram v).det *
        ((∏ e, ‖v (Sum.inl (1, e))‖ ^ 2) /
          (∏ e,
            ‖correlatedSecondColumn (rho e)
              (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))‖ ^ 2)) := by
  rw [det_normalizedGram_matchingMix s r rho v hrho hv hTv]
  have hden : (∏ i,
      ‖mixColumnFamily (matchingMixMatrix s r rho) v i‖ ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _hi
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hTv i))
  calc
    ((∏ e, (1 - rho e ^ 2)) * (normalizedGram v).det *
          (∏ i, ‖v i‖ ^ 2)) /
        (∏ i,
          ‖mixColumnFamily (matchingMixMatrix s r rho) v i‖ ^ 2) =
      (∏ e, (1 - rho e ^ 2)) * (normalizedGram v).det *
        ((∏ i, ‖v i‖ ^ 2) /
          (∏ i,
            ‖mixColumnFamily (matchingMixMatrix s r rho) v i‖ ^ 2)) := by
        field_simp [hden]
    _ = _ := by
      rw [matchingMix_normProduct_ratio s r rho v hv hTv]

/-- Exact logarithmic determinant correction for the entire matching model.
It is the sum of the population log-determinant shift and independent-block
log-radius corrections. -/
theorem logdet_normalizedGram_matchingMix_sub
    (s r : ℕ) (rho : Fin s → ℝ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hrho : ∀ e, |rho e| < 1)
    (hv : ∀ i, v i ≠ 0)
    (hTv : ∀ i, mixColumnFamily (matchingMixMatrix s r rho) v i ≠ 0)
    (hdet : 0 < (normalizedGram v).det) :
    Real.log
          (normalizedGram
            (mixColumnFamily (matchingMixMatrix s r rho) v)).det -
        Real.log (normalizedGram v).det =
      (∑ e, Real.log (1 - rho e ^ 2)) +
        ∑ e,
          (Real.log (‖v (Sum.inl (1, e))‖ ^ 2) -
            Real.log
              (‖correlatedSecondColumn (rho e)
                (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))‖ ^ 2)) := by
  let A : ℝ := ∏ e, (1 - rho e ^ 2)
  let B : ℝ := (normalizedGram v).det
  let C : ℝ := ∏ e, ‖v (Sum.inl (1, e))‖ ^ 2
  let D : ℝ := ∏ e,
    ‖correlatedSecondColumn (rho e)
      (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))‖ ^ 2
  have hgap : ∀ e, 0 < 1 - rho e ^ 2 := fun e ↦
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one (rho e)).2 (hrho e))
  have hA : A ≠ 0 := by
    dsimp [A]
    apply Finset.prod_ne_zero_iff.mpr
    intro e _he
    exact (hgap e).ne'
  have hB : B ≠ 0 := by simpa [B] using hdet.ne'
  have hC : C ≠ 0 := by
    dsimp [C]
    apply Finset.prod_ne_zero_iff.mpr
    intro e _he
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv (Sum.inl (1, e))))
  have hD : D ≠ 0 := by
    dsimp [D]
    apply Finset.prod_ne_zero_iff.mpr
    intro e _he
    have h := hTv (Sum.inl (1, e))
    rw [mixColumnFamily_matchingMixMatrix_pair_one] at h
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  rw [det_normalizedGram_matchingMix_refined s r rho v
    (fun e ↦ (hrho e).le) hv hTv]
  change Real.log (A * B * (C / D)) - Real.log B = _
  rw [Real.log_mul (mul_ne_zero hA hB) (div_ne_zero hC hD),
    Real.log_mul hA hB, Real.log_div hC hD]
  have hlogA : Real.log A = ∑ e, Real.log (1 - rho e ^ 2) := by
    dsimp [A]
    exact Real.log_prod fun e _he ↦ (hgap e).ne'
  have hlogC : Real.log C =
      ∑ e, Real.log (‖v (Sum.inl (1, e))‖ ^ 2) := by
    dsimp [C]
    exact Real.log_prod fun e _he ↦
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv (Sum.inl (1, e))))
  have hlogD : Real.log D =
      ∑ e, Real.log
        (‖correlatedSecondColumn (rho e)
          (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))‖ ^ 2) := by
    dsimp [D]
    apply Real.log_prod
    intro e _he
    have h := hTv (Sum.inl (1, e))
    rw [mixColumnFamily_matchingMixMatrix_pair_one] at h
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  rw [hlogA, hlogC, hlogD, Finset.sum_sub_distrib]
  ring

end

end LogdetLean.Coherence
