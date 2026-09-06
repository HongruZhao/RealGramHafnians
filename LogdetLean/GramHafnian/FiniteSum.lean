import Mathlib
/-!
# The finite correction factor for Gaussian Gram hafnians

This file contains the deterministic algebra behind the exact fourth-moment
formula.  No probability-space assumptions occur here.  In particular, the
correction factor is represented by a finite sum of nonnegative terms, and the
basic recurrence and all-regime maximum-term bounds are proved without any
new axioms.
-/

open scoped BigOperators
open Finset

namespace LogdetLean.GramHafnian

/-- The ratio `(1/2)_j / (k/2)_j`, written as a product with all factors of two
cancelled.  This representation is convenient because it is manifestly
nonnegative for positive integral `k`. -/
noncomputable def pochhammerRatio (k j : ℕ) : ℝ :=
  ∏ i ∈ range j, ((2 * i + 1 : ℕ) : ℝ) / ((k + 2 * i : ℕ) : ℝ)

/-- The `j`th summand in the finite Gram--hafnian correction factor. -/
noncomputable def finiteTerm (k n j : ℕ) : ℝ :=
  ((n.choose j : ℕ) : ℝ) ^ 2 * pochhammerRatio k j

/-- The exact terminating correction factor
`sum_{j=0}^n binom(n,j)^2 (1/2)_j/(k/2)_j`. -/
noncomputable def finiteCorrection (k n : ℕ) : ℝ :=
  ∑ j ∈ range (n + 1), finiteTerm k n j

/-- The independent-complex-Gaussian central-binomial baseline. -/
noncomputable def centralBaseline (n : ℕ) : ℝ :=
  ((Nat.choose (2 * n) n : ℕ) : ℝ) / (4 : ℝ) ^ n

/-- The exact normalized second moment once the moment reduction has identified
`finiteCorrection`. -/
noncomputable def gramSecondMomentRatio (k n : ℕ) : ℝ :=
  centralBaseline n / finiteCorrection k n

@[simp] theorem pochhammerRatio_zero (k : ℕ) : pochhammerRatio k 0 = 1 := by
  simp [pochhammerRatio]

theorem pochhammerRatio_succ (k j : ℕ) :
    pochhammerRatio k (j + 1) =
      pochhammerRatio k j *
        (((2 * j + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) := by
  simp [pochhammerRatio, Finset.prod_range_succ, div_eq_mul_inv]

@[simp] theorem finiteTerm_zero (k n : ℕ) : finiteTerm k n 0 = 1 := by
  simp [finiteTerm]

theorem pochhammerRatio_nonneg (k j : ℕ) : 0 ≤ pochhammerRatio k j := by
  unfold pochhammerRatio
  positivity

theorem pochhammerRatio_pos (k j : ℕ) (hk : 0 < k) :
    0 < pochhammerRatio k j := by
  unfold pochhammerRatio
  apply Finset.prod_pos
  intro i hi
  exact div_pos (by positivity) (by positivity)

theorem finiteTerm_nonneg (k n j : ℕ) : 0 ≤ finiteTerm k n j := by
  unfold finiteTerm
  exact mul_nonneg (sq_nonneg _) (pochhammerRatio_nonneg k j)

theorem finiteTerm_pos (k n j : ℕ) (hk : 0 < k) (hj : j ≤ n) :
    0 < finiteTerm k n j := by
  rw [finiteTerm]
  have hc : 0 < n.choose j := Nat.choose_pos hj
  exact mul_pos (sq_pos_of_pos (by exact_mod_cast hc)) (pochhammerRatio_pos k j hk)

theorem finiteCorrection_nonneg (k n : ℕ) : 0 ≤ finiteCorrection k n := by
  exact Finset.sum_nonneg fun _ _ ↦ finiteTerm_nonneg _ _ _

theorem one_le_finiteCorrection (k n : ℕ) : 1 ≤ finiteCorrection k n := by
  rw [finiteCorrection]
  have hmem : 0 ∈ range (n + 1) := by simp
  simpa using
    (Finset.single_le_sum (s := range (n + 1))
      (fun j _ ↦ finiteTerm_nonneg k n j) hmem)

theorem finiteCorrection_pos (k n : ℕ) : 0 < finiteCorrection k n :=
  lt_of_lt_of_le zero_lt_one (one_le_finiteCorrection k n)

/-- Exact consecutive-term ratio, in cross-multiplied form.  The formulation
contains no division and remains valid without a side condition on `k`. -/
theorem finiteTerm_succ_cross (k n j : ℕ) (hk : 0 < k) :
    finiteTerm k n (j + 1) *
        (((j + 1 : ℕ) : ℝ) ^ 2 * ((k + 2 * j : ℕ) : ℝ)) =
      finiteTerm k n j *
        (((n - j : ℕ) : ℝ) ^ 2 * ((2 * j + 1 : ℕ) : ℝ)) := by
  have hcNat := Nat.choose_succ_right_eq n j
  have hc :
      ((n.choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) =
        ((n.choose j : ℕ) : ℝ) * ((n - j : ℕ) : ℝ) := by
    exact_mod_cast hcNat
  rw [finiteTerm, finiteTerm, pochhammerRatio_succ]
  have hden : ((k + 2 * j : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  calc
    ((n.choose (j + 1) : ℕ) : ℝ) ^ 2 * pochhammerRatio k j *
          ((j + 1 : ℕ) : ℝ) ^ 2 =
        pochhammerRatio k j *
          (((n.choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ 2 := by ring
    _ = pochhammerRatio k j *
          (((n.choose j : ℕ) : ℝ) * ((n - j : ℕ) : ℝ)) ^ 2 := by rw [hc]
    _ = pochhammerRatio k j * ((n.choose j : ℕ) : ℝ) ^ 2 *
          ((n - j : ℕ) : ℝ) ^ 2 := by ring

/-- The usual quotient form of the exact consecutive-term recurrence. -/
theorem finiteTerm_succ_ratio (k n j : ℕ) (hk : 0 < k) (hjn : j < n) :
    finiteTerm k n (j + 1) / finiteTerm k n j =
      (((n - j : ℕ) : ℝ) ^ 2 * ((2 * j + 1 : ℕ) : ℝ)) /
        (((j + 1 : ℕ) : ℝ) ^ 2 * ((k + 2 * j : ℕ) : ℝ)) := by
  have hterm : finiteTerm k n j ≠ 0 := by
    have hjle : j ≤ n := Nat.le_of_lt hjn
    have hchoose : 0 < n.choose j := Nat.choose_pos hjle
    rw [finiteTerm]
    apply mul_ne_zero
    · exact pow_ne_zero _ (by positivity)
    · unfold pochhammerRatio
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply div_ne_zero
      · positivity
      · positivity
  have hfac :
      (((j + 1 : ℕ) : ℝ) ^ 2 * ((k + 2 * j : ℕ) : ℝ)) ≠ 0 := by
    positivity
  apply (div_eq_div_iff hterm hfac).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using finiteTerm_succ_cross k n j hk

/-- Maximum-summand lower bound for the finite correction factor. -/
theorem finiteTerm_le_finiteCorrection (k n j : ℕ) (hj : j ≤ n) :
    finiteTerm k n j ≤ finiteCorrection k n := by
  rw [finiteCorrection]
  exact Finset.single_le_sum
    (fun i _ ↦ finiteTerm_nonneg k n i)
    (by simpa [Finset.mem_range] using Nat.lt_succ_iff.mpr hj)

/-- If `jStar` indexes a maximum summand, the whole finite sum is at most
`n+1` times that summand. -/
theorem finiteCorrection_le_card_mul_max
    (k n jStar : ℕ)
    (hmax : ∀ j, j ≤ n → finiteTerm k n j ≤ finiteTerm k n jStar) :
    finiteCorrection k n ≤ (n + 1 : ℝ) * finiteTerm k n jStar := by
  rw [finiteCorrection]
  calc
    (∑ j ∈ range (n + 1), finiteTerm k n j)
        ≤ ∑ _j ∈ range (n + 1), finiteTerm k n jStar := by
          apply Finset.sum_le_sum
          intro j hj
          exact hmax j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = (n + 1 : ℝ) * finiteTerm k n jStar := by simp

/-- The exact factor-`n+1` maximum-summand bracket. -/
theorem max_summand_bracket
    (k n jStar : ℕ) (hjStar : jStar ≤ n)
    (hmax : ∀ j, j ≤ n → finiteTerm k n j ≤ finiteTerm k n jStar) :
    finiteTerm k n jStar ≤ finiteCorrection k n ∧
      finiteCorrection k n ≤ (n + 1 : ℝ) * finiteTerm k n jStar :=
  ⟨finiteTerm_le_finiteCorrection k n jStar hjStar,
    finiteCorrection_le_card_mul_max k n jStar hmax⟩

/-- The maximum-summand bracket expressed directly for the normalized second
moment.  This is a unified finite bound valid in every `(k,n)` regime. -/
theorem max_summand_ratio_bracket
    (k n jStar : ℕ) (hk : 0 < k) (hjStar : jStar ≤ n)
    (hmax : ∀ j, j ≤ n → finiteTerm k n j ≤ finiteTerm k n jStar) :
    centralBaseline n / ((n + 1 : ℝ) * finiteTerm k n jStar) ≤
        gramSecondMomentRatio k n ∧
      gramSecondMomentRatio k n ≤
        centralBaseline n / finiteTerm k n jStar := by
  have hbracket := max_summand_bracket k n jStar hjStar hmax
  have hT : 0 < finiteTerm k n jStar := finiteTerm_pos k n jStar hk hjStar
  have hF : 0 < finiteCorrection k n := finiteCorrection_pos k n
  have hq : 0 ≤ centralBaseline n := by
    unfold centralBaseline
    positivity
  rw [gramSecondMomentRatio]
  constructor
  · exact div_le_div_of_nonneg_left hq hF hbracket.2
  · exact div_le_div_of_nonneg_left hq hT hbracket.1

/-- A maximizing summand always exists, so the factor-`n+1` bracket is
available without supplying an index by hand. -/
theorem exists_max_summand_bracket (k n : ℕ) :
    ∃ jStar, jStar ≤ n ∧
      finiteTerm k n jStar ≤ finiteCorrection k n ∧
      finiteCorrection k n ≤ (n + 1 : ℝ) * finiteTerm k n jStar := by
  obtain ⟨jStar, hjStar, hmax⟩ :=
    Finset.exists_max_image (range (n + 1)) (finiteTerm k n) (by simp)
  have hjle : jStar ≤ n :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hjStar)
  refine ⟨jStar, hjle, finiteTerm_le_finiteCorrection k n jStar hjle, ?_⟩
  apply finiteCorrection_le_card_mul_max k n jStar
  intro j hj
  exact hmax j (by simpa [Finset.mem_range] using Nat.lt_succ_iff.mpr hj)

/-- Existence form of the unified normalized second-moment bracket. -/
theorem exists_max_summand_ratio_bracket (k n : ℕ) (hk : 0 < k) :
    ∃ jStar, jStar ≤ n ∧
      centralBaseline n / ((n + 1 : ℝ) * finiteTerm k n jStar) ≤
        gramSecondMomentRatio k n ∧
      gramSecondMomentRatio k n ≤
        centralBaseline n / finiteTerm k n jStar := by
  obtain ⟨jStar, hjStar, hmax⟩ :=
    Finset.exists_max_image (range (n + 1)) (finiteTerm k n) (by simp)
  have hjle : jStar ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjStar)
  refine ⟨jStar, hjle, ?_⟩
  exact max_summand_ratio_bracket k n jStar hk hjle
    (fun j hj ↦ hmax j (by simpa [Finset.mem_range] using Nat.lt_succ_iff.mpr hj))

theorem pochhammerRatio_le_one (k j : ℕ) (hk : 0 < k) :
    pochhammerRatio k j ≤ 1 := by
  unfold pochhammerRatio
  apply Finset.prod_le_one
  · intro i hi
    positivity
  · intro i hi
    apply (div_le_one (by positivity : (0 : ℝ) < ((k + 2 * i : ℕ) : ℝ))).2
    norm_num
    exact_mod_cast (show 2 * i + 1 ≤ k + 2 * i by omega)

theorem finiteTerm_le_choose_sq (k n j : ℕ) (hk : 0 < k) :
    finiteTerm k n j ≤ ((n.choose j : ℕ) : ℝ) ^ 2 := by
  rw [finiteTerm]
  nlinarith [pochhammerRatio_nonneg k j, pochhammerRatio_le_one k j hk,
    sq_nonneg (((n.choose j : ℕ) : ℝ))]

/-- Vandermonde's identity bounds the whole correction factor by the central
binomial coefficient, uniformly for every positive integral dimension. -/
theorem finiteCorrection_le_centralBinom (k n : ℕ) (hk : 0 < k) :
    finiteCorrection k n ≤ ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
  rw [finiteCorrection]
  calc
    (∑ j ∈ range (n + 1), finiteTerm k n j)
        ≤ ∑ j ∈ range (n + 1), (((n.choose j : ℕ) : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          exact finiteTerm_le_choose_sq k n j hk
    _ = ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
      exact_mod_cast Nat.sum_range_choose_sq n

/-- Increasing the row dimension decreases every Pochhammer correction
factor. -/
theorem pochhammerRatio_antitone_dimension
    {k₁ k₂ j : ℕ} (hk₁ : 0 < k₁) (hkk : k₁ ≤ k₂) :
    pochhammerRatio k₂ j ≤ pochhammerRatio k₁ j := by
  unfold pochhammerRatio
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    have hden : k₁ + 2 * i ≤ k₂ + 2 * i := Nat.add_le_add_right hkk _
    exact div_le_div_of_nonneg_left (by positivity)
      (by positivity : (0 : ℝ) < ((k₁ + 2 * i : ℕ) : ℝ))
      (by exact_mod_cast hden)

theorem finiteTerm_antitone_dimension
    {k₁ k₂ n j : ℕ} (hk₁ : 0 < k₁) (hkk : k₁ ≤ k₂) :
    finiteTerm k₂ n j ≤ finiteTerm k₁ n j := by
  rw [finiteTerm, finiteTerm]
  exact mul_le_mul_of_nonneg_left
    (pochhammerRatio_antitone_dimension hk₁ hkk) (sq_nonneg _)

theorem finiteCorrection_antitone_dimension
    {k₁ k₂ n : ℕ} (hk₁ : 0 < k₁) (hkk : k₁ ≤ k₂) :
    finiteCorrection k₂ n ≤ finiteCorrection k₁ n := by
  rw [finiteCorrection, finiteCorrection]
  exact Finset.sum_le_sum fun j _ ↦ finiteTerm_antitone_dimension hk₁ hkk

theorem centralBaseline_nonneg (n : ℕ) : 0 ≤ centralBaseline n := by
  unfold centralBaseline
  positivity

theorem centralBaseline_pos (n : ℕ) : 0 < centralBaseline n := by
  unfold centralBaseline
  have hc : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  positivity

theorem gramSecondMomentRatio_pos (k n : ℕ) :
    0 < gramSecondMomentRatio k n := by
  unfold gramSecondMomentRatio
  exact div_pos (centralBaseline_pos n) (finiteCorrection_pos k n)

/-- Consequently the exact normalized second moment is monotone increasing in
the row dimension. -/
theorem gramSecondMomentRatio_monotone_dimension
    {k₁ k₂ n : ℕ} (hk₁ : 0 < k₁) (hkk : k₁ ≤ k₂) :
    gramSecondMomentRatio k₁ n ≤ gramSecondMomentRatio k₂ n := by
  rw [gramSecondMomentRatio, gramSecondMomentRatio]
  exact div_le_div_of_nonneg_left (centralBaseline_nonneg n)
    (finiteCorrection_pos k₂ n)
    (finiteCorrection_antitone_dimension hk₁ hkk)

/-- The finite correction can only reduce the normalized second moment from
the independent-complex-Gaussian baseline. -/
theorem gramSecondMomentRatio_le_baseline (k n : ℕ) :
    gramSecondMomentRatio k n ≤ centralBaseline n := by
  rw [gramSecondMomentRatio]
  apply (div_le_iff₀ (finiteCorrection_pos k n)).2
  have hq := centralBaseline_nonneg n
  have hF := one_le_finiteCorrection k n
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hF)]

/-- Universal lower endpoint: for every positive `k`, the normalized second
moment is at least `4^{-n}`. -/
theorem four_pow_recip_le_gramSecondMomentRatio
    (k n : ℕ) (hk : 0 < k) :
    1 / (4 : ℝ) ^ n ≤ gramSecondMomentRatio k n := by
  rw [gramSecondMomentRatio, centralBaseline]
  apply (le_div_iff₀ (finiteCorrection_pos k n)).2
  calc
    1 / (4 : ℝ) ^ n * finiteCorrection k n
        ≤ 1 / (4 : ℝ) ^ n * ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (finiteCorrection_le_centralBinom k n hk) (by positivity)
    _ = ((Nat.choose (2 * n) n : ℕ) : ℝ) / (4 : ℝ) ^ n := by ring

/-- At `k=1`, every Pochhammer ratio is exactly one. -/
@[simp] theorem pochhammerRatio_one (j : ℕ) : pochhammerRatio 1 j = 1 := by
  unfold pochhammerRatio
  apply Finset.prod_eq_one
  intro i hi
  have heq : 1 + 2 * i = 2 * i + 1 := by omega
  rw [heq]
  apply div_self
  positivity

@[simp] theorem finiteCorrection_one (n : ℕ) :
    finiteCorrection 1 n = ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
  rw [finiteCorrection]
  simp only [finiteTerm, pochhammerRatio_one, mul_one]
  exact_mod_cast Nat.sum_range_choose_sq n

/-- The exact `k=1` endpoint of the normalized second moment. -/
theorem gramSecondMomentRatio_one (n : ℕ) :
    gramSecondMomentRatio 1 n = 1 / (4 : ℝ) ^ n := by
  rw [gramSecondMomentRatio, centralBaseline, finiteCorrection_one]
  have hc : (((Nat.choose (2 * n) n : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : n ≤ 2 * n)))
  field_simp [hc]

end LogdetLean.GramHafnian
