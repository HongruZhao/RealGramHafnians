import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGaussianGramTail
/-!
# Sharp elementary union bound for a symmetric real Gaussian Gram matrix

For a linearly ordered finite column set, symmetry means that only the
strict upper triangle needs to be counted.  The `m` diagonal events cost
`2 exp(-k eta²/8)` each and the `m.choose 2` off-diagonal events cost
`4 exp(-k eta²/8)` each.  Their sum is exactly
`2 m² exp(-k eta²/8)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

section SharpColumnFamily

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]

/-- The diagonal entry uses the chi-square estimate directly and therefore
has constant `2`, rather than the common conservative constant `4`. -/
theorem standardRealGaussianColumnFamily_diagonalEntryBad_le
    {k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) (i : ι) :
    (standardRealGaussianColumnFamilyMeasure ι k).real
        (realTransposeGramEntryBad k delta i i) ≤
      2 * Real.exp (-((k : ℝ) *
        (delta / (Fintype.card ι : ℝ)) ^ 2 / 8)) := by
  let m : ℝ := Fintype.card ι
  let eta : ℝ := delta / m
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have heta0 : 0 ≤ eta := div_nonneg hdelta0 (by positivity)
  have heta1 : eta ≤ 1 := by
    dsimp [eta]
    exact (div_le_one (by positivity : 0 < m)).mpr (hdelta1.trans hm)
  let mu := standardRealGaussianColumnFamilyMeasure ι k
  have heval : HasLaw (fun A : ι → Fin k → ℝ ↦ A i)
      (standardRealGaussianVectorMeasure k) mu := by
    exact (measurePreserving_eval
      (fun _ : ι ↦ standardRealGaussianVectorMeasure k) i).hasLaw
  let badVec : Set (Fin k → ℝ) :=
    {x | |realGaussianVectorNormSq x - (k : ℝ)| > (k : ℝ) * eta}
  have hmeas : MeasurableSet badVec := by
    dsimp [badVec]
    exact measurableSet_lt measurable_const
      ((measurable_realGaussianVectorNormSq k).sub_const _).abs
  have heq := heval.measureReal_eq
    (p := fun x : Fin k → ℝ ↦ x ∈ badVec) hmeas
  have htail := standardRealGaussianVector_normSq_deviation_le
    hk heta0 heta1
  have hset : realTransposeGramEntryBad (ι := ι) k delta i i =
      {A : ι → Fin k → ℝ | A i ∈ badVec} := by
    ext A
    simp only [realTransposeGramEntryBad, Set.mem_setOf_eq, badVec,
      centeredRealTransposeGramEntry, if_pos, realTransposeGramEntry,
      realGaussianVectorNormSq]
    dsimp [eta, m]
    have hthreshold :
        delta * (k : ℝ) / (Fintype.card ι : ℝ) =
          (k : ℝ) * (delta / (Fintype.card ι : ℝ)) := by ring
    rw [hthreshold]
    simp [pow_two]
  rw [hset, heq]
  simpa [eta, m] using htail

/-- Gram-entry bad events are symmetric in their two column indices. -/
theorem realTransposeGramEntryBad_comm
    (k : ℕ) (delta : ℝ) (i j : ι) :
    realTransposeGramEntryBad k delta i j =
      realTransposeGramEntryBad k delta j i := by
  have hgram : ∀ A : ι → Fin k → ℝ,
      realTransposeGramEntry A i j = realTransposeGramEntry A j i := by
    intro A
    unfold realTransposeGramEntry
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  ext A
  simp only [realTransposeGramEntryBad, Set.mem_setOf_eq]
  congr 1
  congr 1
  unfold centeredRealTransposeGramEntry
  rw [hgram]
  simp only [eq_comm]

/-- Every failure is either diagonal or belongs to the strict upper
triangle. -/
theorem not_realTransposeGramGood_set_subset_diagonal_union_upper
    (k : ℕ) (delta : ℝ) :
    {A : ι → Fin k → ℝ | ¬ realTransposeGramGood k delta A} ⊆
      (⋃ i : ι, realTransposeGramEntryBad k delta i i) ∪
        ⋃ p : {p : ι × ι // p.1 < p.2},
          realTransposeGramEntryBad k delta p.1.1 p.1.2 := by
  intro A hA
  rw [not_realTransposeGramGood_set_eq_iUnion_entryBad] at hA
  simp only [Set.mem_iUnion] at hA
  rcases hA with ⟨i, j, hijBad⟩
  by_cases hij : i = j
  · left
    subst j
    exact Set.mem_iUnion_of_mem i hijBad
  · rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · right
      exact Set.mem_iUnion_of_mem ⟨(i, j), hijlt⟩ hijBad
    · right
      apply Set.mem_iUnion_of_mem ⟨(j, i), hjilt⟩
      rw [realTransposeGramEntryBad_comm]
      exact hijBad

private theorem card_strictUpperGramPair :
    Fintype.card {p : ι × ι // p.1 < p.2} =
      Nat.choose (Fintype.card ι) 2 := by
  rw [Fintype.card_subtype]
  simpa [Finset.univ_product_univ] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset ι)))

private theorem diagonal_add_strictUpper_cost
    (B : ℝ) :
    (∑ _i : ι, 2 * B) +
        (∑ _p : {p : ι × ι // p.1 < p.2}, 4 * B) =
      2 * (Fintype.card ι : ℝ) ^ 2 * B := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_strictUpperGramPair]
  rw [Nat.cast_choose_two]
  norm_num
  ring

/-- Sharp real-valued elementary union bound. -/
theorem standardRealGaussianColumnFamily_not_good_le_sharp
    {k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (standardRealGaussianColumnFamilyMeasure ι k).real
        {A | ¬ realTransposeGramGood k delta A} ≤
      2 * (Fintype.card ι : ℝ) ^ 2 *
        Real.exp (-((k : ℝ) *
          (delta / (Fintype.card ι : ℝ)) ^ 2 / 8)) := by
  let mu := standardRealGaussianColumnFamilyMeasure ι k
  let B := Real.exp (-((k : ℝ) *
    (delta / (Fintype.card ι : ℝ)) ^ 2 / 8))
  let diagonal : Set (ι → Fin k → ℝ) :=
    ⋃ i : ι, realTransposeGramEntryBad k delta i i
  let upper : Set (ι → Fin k → ℝ) :=
    ⋃ p : {p : ι × ι // p.1 < p.2},
      realTransposeGramEntryBad k delta p.1.1 p.1.2
  calc
    mu.real {A | ¬ realTransposeGramGood k delta A} ≤
        mu.real (diagonal ∪ upper) := by
      exact measureReal_mono
        (not_realTransposeGramGood_set_subset_diagonal_union_upper k delta)
        (measure_ne_top _ _)
    _ ≤ mu.real diagonal + mu.real upper := measureReal_union_le _ _
    _ ≤ (∑ i : ι, mu.real
          (realTransposeGramEntryBad k delta i i)) +
        ∑ p : {p : ι × ι // p.1 < p.2}, mu.real
          (realTransposeGramEntryBad k delta p.1.1 p.1.2) := by
      exact add_le_add (measureReal_iUnion_fintype_le _)
        (measureReal_iUnion_fintype_le _)
    _ ≤ (∑ _i : ι, 2 * B) +
        ∑ _p : {p : ι × ι // p.1 < p.2}, 4 * B := by
      gcongr with i p
      · exact standardRealGaussianColumnFamily_diagonalEntryBad_le
          hk hdelta0 hdelta1 i
      · exact standardRealGaussianColumnFamily_entryBad_le
          hk hdelta0 hdelta1 p.1.1 p.1.2
    _ = 2 * (Fintype.card ι : ℝ) ^ 2 * B :=
      diagonal_add_strictUpper_cost B
    _ = 2 * (Fintype.card ι : ℝ) ^ 2 *
        Real.exp (-((k : ℝ) *
          (delta / (Fintype.card ι : ℝ)) ^ 2 / 8)) := rfl

/-- ENNReal form used directly by the literal fractional-resolvent
recurrence. -/
theorem standardRealGaussianColumnFamily_not_good_le_ennreal_sharp
    {k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (standardRealGaussianColumnFamilyMeasure ι k)
        {A | ¬ realTransposeGramGood k delta A} ≤
      ENNReal.ofReal
        (2 * (Fintype.card ι : ℝ) ^ 2 *
          Real.exp (-((k : ℝ) *
            (delta / (Fintype.card ι : ℝ)) ^ 2 / 8))) := by
  apply (ENNReal.toReal_le_toReal
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal]
  · exact standardRealGaussianColumnFamily_not_good_le_sharp
      hk hdelta0 hdelta1
  · positivity

end SharpColumnFamily

end

end LogdetLean.GramHafnian
