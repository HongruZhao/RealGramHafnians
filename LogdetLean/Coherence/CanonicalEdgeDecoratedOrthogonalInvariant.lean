import LogdetLean.Coherence.CanonicalEdgeDecoratedTailIndependence
/-!
# Orthogonal invariance of the canonical decorated tail

This module supplies the geometric adapter isolated in
`CanonicalEdgeDecoratedTailIndependence`.  The proof works in the centered
`m`-dimensional Gaussian space.  It extends an isometry between the spans of
two linearly independent prefixes to an orthogonal operator on the whole
space, rotates all remaining iid Gaussian columns, and uses the exact
invariance of normalized Gram determinants and remote correlations.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set Module
open scoped ProbabilityTheory

/-! ## Coordinatewise action on right-nested tuples -/

/-- Apply a function to every coordinate of a right-nested tuple. -/
def nestedTupleMap {E F : Type} (T : E → F) :
    ∀ n, NestedTuple E n → NestedTuple F n
  | 0, _ => ULift.up Unit.unit
  | n + 1, z => (nestedTupleMap T n z.1, T z.2)

theorem measurable_nestedTupleMap
    {E F : Type} [MeasurableSpace E] [MeasurableSpace F]
    {T : E → F} (hT : Measurable T) :
    ∀ n, Measurable (nestedTupleMap T n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).prodMk (hT.comp measurable_snd)

@[simp] theorem nestedTupleToFin_nestedTupleMap
    {E F : Type} (T : E → F) : ∀ n (z : NestedTuple E n),
    nestedTupleToFin n (nestedTupleMap T n z) =
      T ∘ nestedTupleToFin n z := by
  intro n
  induction n with
  | zero =>
      intro z
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro z
      rcases z with ⟨z, y⟩
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [nestedTupleMap, nestedTupleToFin, Function.comp_apply]
      · simpa [nestedTupleMap, nestedTupleToFin] using congrFun (ih z) j

@[simp] theorem nestedTupleMap_nestedTupleAppend
    {E F : Type} (T : E → F) (q : ℕ) : ∀ r
    (pref : NestedTuple E q) (tail : NestedTuple E r),
    nestedTupleMap T (q + r) (nestedTupleAppend q pref r tail) =
      nestedTupleAppend q (nestedTupleMap T q pref) r
        (nestedTupleMap T r tail) := by
  intro r
  induction r with
  | zero =>
      intro pref tail
      rfl
  | succ r ih =>
      intro pref tail
      rcases tail with ⟨tail, y⟩
      simp only [nestedTupleAppend, nestedTupleMap]
      apply Prod.ext
      · exact ih pref tail
      · rfl

/-- An orthogonal equivalence acts measure-preservingly on every finite iid
standard-Gaussian nested tuple. -/
theorem map_nestedTupleMap_stdGaussian
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : E ≃ₗᵢ[ℝ] E) : ∀ n,
    Measure.map (nestedTupleMap T n)
        (nestedProductMeasure (stdGaussian E) n) =
      nestedProductMeasure (stdGaussian E) n := by
  intro n
  induction n with
  | zero =>
      simp [nestedTupleMap, nestedProductMeasure]
  | succ n ih =>
      change Measure.map
          (Prod.map (nestedTupleMap T n) T)
          ((nestedProductMeasure (stdGaussian E) n).prod (stdGaussian E)) =
        (nestedProductMeasure (stdGaussian E) n).prod (stdGaussian E)
      rw [← Measure.map_prod_map _ _
        (measurable_nestedTupleMap T.continuous.measurable n)
        T.continuous.measurable]
      rw [ih, stdGaussian_map T]

/-! ## Exact isometry invariance of both decorations -/

/-- Every normalized-Gram determinant ratio is invariant under a linear
isometry, including on singular inputs. -/
theorem nestedNormalizedGramFactor_nestedTupleMap
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (n : ℕ)
    (past : NestedTuple E n) (y : E) :
    nestedNormalizedGramFactor n (nestedTupleMap T n past) (T y) =
      nestedNormalizedGramFactor n past y := by
  unfold nestedNormalizedGramFactor nestedNormalizedGramDet
  rw [show (nestedTupleMap T n past, T y) =
      nestedTupleMap T (n + 1) (past, y) by rfl]
  rw [nestedTupleToFin_nestedTupleMap, nestedTupleToFin_nestedTupleMap]
  have hnum := det_normalizedGram_linearIsometry T
    (nestedTupleToFin (n + 1) (past, y))
  have hden := det_normalizedGram_linearIsometry T
    (nestedTupleToFin n past)
  rw [show (normalizedGram
      (T ∘ nestedTupleToFin (n + 1) (past, y))).det =
        (normalizedGram (nestedTupleToFin (n + 1) (past, y))).det by
      change (normalizedGram (fun i ↦
        T (nestedTupleToFin (n + 1) (past, y) i))).det = _
      exact hnum]
  rw [show (normalizedGram (T ∘ nestedTupleToFin n past)).det =
        (normalizedGram (nestedTupleToFin n past)).det by
      change (normalizedGram (fun i ↦
        T (nestedTupleToFin n past i))).det = _
      exact hden]

/-- The logarithmic retained-tail statistic is invariant when the same
linear isometry is applied to every prefix and tail column. -/
theorem retainedTailLogSum_nestedTupleMap
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗᵢ[ℝ] F) (q : ℕ) : ∀ r
    (z : NestedTuple E (q + r)),
    retainedTailLogSum q r
        (retainedPrefixTailStatistic
          (nestedNormalizedGramFactor (E := F)) q r
          (nestedTupleMap T (q + r) z)) =
      retainedTailLogSum q r
        (retainedPrefixTailStatistic
          (nestedNormalizedGramFactor (E := E)) q r z) := by
  intro r
  induction r with
  | zero =>
      intro z
      rfl
  | succ r ih =>
      intro z
      rcases z with ⟨z, y⟩
      simp only [nestedTupleMap, retainedPrefixTailStatistic,
        retainedTailLogSum]
      have htail : retainedTailLogSum q r
          (retainedPrefixTailStatistic
            (nestedNormalizedGramFactor (E := F)) q r
            (nestedTupleMap T (q.add r) z)) =
          retainedTailLogSum q r
            (retainedPrefixTailStatistic
              (nestedNormalizedGramFactor (E := E)) q r z) := by
        simpa using ih z
      have hfactor : nestedNormalizedGramFactor (q + r)
          (nestedTupleMap T (q.add r) z) (T y) =
          nestedNormalizedGramFactor (q + r) z y := by
        change nestedNormalizedGramFactor (q + r)
          (nestedTupleMap T (q + r) z) (T y) = _
        exact nestedNormalizedGramFactor_nestedTupleMap T (q + r) z y
      rw [htail, hfactor]

/-- The centered remote count is invariant under a common linear isometry. -/
theorem centeredRemoteCoherenceExceedanceCount_nestedTupleMap
    (m r : ℕ) (x : ℝ)
    (T : centeredSubspace (m + 1) →ₗᵢ[ℝ]
      centeredSubspace (m + 1))
    (tail : NestedTuple (centeredSubspace (m + 1)) r) :
    centeredRemoteCoherenceExceedanceCount m r x
        (nestedTupleMap T r tail) =
      centeredRemoteCoherenceExceedanceCount m r x tail := by
  unfold centeredRemoteCoherenceExceedanceCount
  apply Finset.sum_congr rfl
  intro e he
  have hscore : centeredScaledSquaredCorrelationScore m r
      (nestedTupleMap T r tail) e =
      centeredScaledSquaredCorrelationScore m r tail e := by
    unfold centeredScaledSquaredCorrelationScore
    rw [nestedTupleToFin_nestedTupleMap]
    have hgram := normalizedGram_linearIsometry T
      (nestedTupleToFin r tail)
    rw [show normalizedGram (T ∘ nestedTupleToFin r tail) =
        normalizedGram (nestedTupleToFin r tail) by
      change normalizedGram (fun i ↦ T (nestedTupleToFin r tail i)) = _
      exact hgram]
  rw [hscore]

/-- Exact simultaneous orthogonal invariance of the centered decorated tail. -/
theorem centeredCanonicalDecoratedTailGivenPrefix_nestedTupleMap
    (m r : ℕ) (x : ℝ)
    (T : centeredSubspace (m + 1) →ₗᵢ[ℝ]
      centeredSubspace (m + 1))
    (pref : NestedTuple (centeredSubspace (m + 1)) 2)
    (tail : NestedTuple (centeredSubspace (m + 1)) r) :
    centeredCanonicalDecoratedTailGivenPrefix m r x
        (nestedTupleMap T 2 pref) (nestedTupleMap T r tail) =
      centeredCanonicalDecoratedTailGivenPrefix m r x pref tail := by
  apply Prod.ext
  · unfold centeredCanonicalDecoratedTailGivenPrefix
    unfold standardizedRetainedTailLogStatistic
    simp only [Prod.fst]
    rw [← nestedTupleMap_nestedTupleAppend]
    rw [retainedTailLogSum_nestedTupleMap]
  · exact centeredRemoteCoherenceExceedanceCount_nestedTupleMap
      m r x T tail

/-! ## Replacing a prefix by another basis of the same span -/

/-- Appending the same last vector preserves equality of spans. -/
theorem span_range_finSnoc_eq_of_span_eq
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} {v w : Fin n → E} (y : E)
    (hspan : Submodule.span ℝ (Set.range v) =
      Submodule.span ℝ (Set.range w)) :
    Submodule.span ℝ (Set.range (Fin.snoc v y)) =
      Submodule.span ℝ (Set.range (Fin.snoc w y)) := by
  simp only [Fin.range_snoc, Submodule.span_insert, hspan]

/-- Appending the same finite tail to two prefixes with equal spans leaves
their full spans equal. -/
theorem span_range_nestedTupleAppend_eq_of_span_eq
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (q : ℕ) : ∀ r
    (pref₁ pref₂ : NestedTuple E q) (tail : NestedTuple E r),
    Submodule.span ℝ (Set.range (nestedTupleToFin q pref₁)) =
      Submodule.span ℝ (Set.range (nestedTupleToFin q pref₂)) →
    Submodule.span ℝ
        (Set.range (nestedTupleToFin (q + r)
          (nestedTupleAppend q pref₁ r tail))) =
      Submodule.span ℝ
        (Set.range (nestedTupleToFin (q + r)
          (nestedTupleAppend q pref₂ r tail))) := by
  intro r
  induction r with
  | zero =>
      intro pref₁ pref₂ tail hspan
      exact hspan
  | succ r ih =>
      intro pref₁ pref₂ tail hspan
      rcases tail with ⟨tail, y⟩
      change Submodule.span ℝ
          (Set.range (Fin.snoc
            (nestedTupleToFin (q.add r)
              (nestedTupleAppend q pref₁ r tail)) y)) =
        Submodule.span ℝ
          (Set.range (Fin.snoc
            (nestedTupleToFin (q.add r)
              (nestedTupleAppend q pref₂ r tail)) y))
      apply span_range_finSnoc_eq_of_span_eq y
      simpa using ih pref₁ pref₂ tail hspan

/-- On linearly independent extensions, the next normalized-Gram factor
depends on the past only through its linear span. -/
theorem nestedNormalizedGramFactor_eq_of_span_eq
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} (past₁ past₂ : NestedTuple E n) (y : E)
    (hspan : Submodule.span ℝ
        (Set.range (nestedTupleToFin n past₁)) =
      Submodule.span ℝ
        (Set.range (nestedTupleToFin n past₂)))
    (hfull₁ : LinearIndependent ℝ
      (Fin.snoc (nestedTupleToFin n past₁) y))
    (hfull₂ : LinearIndependent ℝ
      (Fin.snoc (nestedTupleToFin n past₂) y)) :
    nestedNormalizedGramFactor n past₁ y =
      nestedNormalizedGramFactor n past₂ y := by
  rw [nestedNormalizedGramFactor_eq_orthogonalProjection past₁ y hfull₁]
  rw [nestedNormalizedGramFactor_eq_orthogonalProjection past₂ y hfull₂]
  rw [gramSchmidtPastSpan_snoc_eq_span_range,
    gramSchmidtPastSpan_snoc_eq_span_range, hspan]

/-- Consequently, the entire retained logarithmic tail is unchanged when a
linearly independent prefix is replaced by another basis of the same span,
outside only the usual singular full-family set. -/
theorem retainedTailLogSum_eq_of_prefix_span_eq
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (q : ℕ) : ∀ r
    (pref₁ pref₂ : NestedTuple E q) (tail : NestedTuple E r),
    Submodule.span ℝ (Set.range (nestedTupleToFin q pref₁)) =
      Submodule.span ℝ (Set.range (nestedTupleToFin q pref₂)) →
    LinearIndependent ℝ
      (nestedTupleToFin (q + r) (nestedTupleAppend q pref₁ r tail)) →
    LinearIndependent ℝ
      (nestedTupleToFin (q + r) (nestedTupleAppend q pref₂ r tail)) →
    retainedTailLogSum q r
        (retainedPrefixTailStatistic
          (nestedNormalizedGramFactor (E := E)) q r
          (nestedTupleAppend q pref₁ r tail)) =
      retainedTailLogSum q r
        (retainedPrefixTailStatistic
          (nestedNormalizedGramFactor (E := E)) q r
          (nestedTupleAppend q pref₂ r tail)) := by
  intro r
  induction r with
  | zero =>
      intro pref₁ pref₂ tail hspan hfull₁ hfull₂
      rfl
  | succ r ih =>
      intro pref₁ pref₂ tail hspan hfull₁ hfull₂
      rcases tail with ⟨tail, y⟩
      have hpast₁ := (linearIndependent_finSnoc.mp hfull₁).1
      have hpast₂ := (linearIndependent_finSnoc.mp hfull₂).1
      have hspanPast := span_range_nestedTupleAppend_eq_of_span_eq
        q r pref₁ pref₂ tail hspan
      have htail := ih pref₁ pref₂ tail hspan hpast₁ hpast₂
      have hfactor := nestedNormalizedGramFactor_eq_of_span_eq
        (nestedTupleAppend q pref₁ r tail)
        (nestedTupleAppend q pref₂ r tail) y hspanPast hfull₁ hfull₂
      simp only [nestedTupleAppend, retainedPrefixTailStatistic,
        retainedTailLogSum]
      rw [htail, hfactor]

/-! ## Almost-sure nonsingularity after a fixed independent prefix -/

/-- A fixed linearly independent prefix followed by sufficiently few iid
standard Gaussian columns remains linearly independent almost surely. -/
theorem ae_linearIndependent_nestedTupleAppend_stdGaussian
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (q : ℕ) (pref : NestedTuple E q)
    (hpref : LinearIndependent ℝ (nestedTupleToFin q pref)) :
    ∀ r, q + r ≤ finrank ℝ E →
    ∀ᵐ tail ∂nestedProductMeasure (stdGaussian E) r,
      LinearIndependent ℝ
        (nestedTupleToFin (q + r)
          (nestedTupleAppend q pref r tail)) := by
  intro r
  induction r with
  | zero =>
      intro hq
      filter_upwards [] with tail
      change LinearIndependent ℝ (nestedTupleToFin q pref)
      exact hpref
  | succ r ih =>
      intro hqr
      have hprev := ih (by omega)
      have hlt : q + r < finrank ℝ E := by omega
      have hmeas : Measurable (fun z : NestedTuple E r × E ↦
          nestedTupleToFin (q + (r + 1))
            (nestedTupleAppend q pref (r + 1) z)) :=
        (measurable_nestedTupleToFin (q + (r + 1))).comp
          (measurable_nestedTupleAppend q pref (r + 1))
      have hset : MeasurableSet
          {z : NestedTuple E r × E |
            LinearIndependent ℝ
              (nestedTupleToFin (q + (r + 1))
                (nestedTupleAppend q pref (r + 1) z))} :=
        (measurableSet_linearlyIndependentTuples
          (E := E) (q + (r + 1))).preimage hmeas
      change ∀ᵐ z ∂(nestedProductMeasure (stdGaussian E) r).prod
          (stdGaussian E),
        LinearIndependent ℝ
          (nestedTupleToFin (q + (r + 1))
            (nestedTupleAppend q pref (r + 1) z))
      rw [Measure.ae_prod_iff_ae_ae hset]
      filter_upwards [hprev] with tail hpast
      have hfresh := ae_linearIndependent_snoc_stdGaussian hpast hlt
      simpa [nestedTupleAppend, nestedTupleToFin] using hfresh

/-! ## Extending an isometry between two prefix spans -/

/-- Two linearly independent two-vector families can have their spans
matched by an orthogonal equivalence of the entire ambient Euclidean space. -/
theorem exists_linearIsometryEquiv_map_span_pair
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (u v : Fin 2 → E)
    (hu : LinearIndependent ℝ u) (hv : LinearIndependent ℝ v) :
    ∃ T : E ≃ₗᵢ[ℝ] E,
      Submodule.span ℝ (Set.range (fun i ↦ T (u i))) =
        Submodule.span ℝ (Set.range v) := by
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range u)
  let R : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hdimS : finrank ℝ S = 2 := by
    simpa [S] using finrank_span_eq_card hu
  have hdimR : finrank ℝ R = 2 := by
    simpa [R] using finrank_span_eq_card hv
  have hdim : finrank ℝ S = finrank ℝ R := hdimS.trans hdimR.symm
  let bS := stdOrthonormalBasis ℝ S
  let bR₀ := stdOrthonormalBasis ℝ R
  let bR : OrthonormalBasis (Fin (finrank ℝ S)) ℝ R :=
    bR₀.reindex (finCongr hdim.symm)
  let eSR : S ≃ₗᵢ[ℝ] R := bS.equiv bR (Equiv.refl _)
  let L : S →ₗᵢ[ℝ] E := R.subtypeₗᵢ.comp eSR.toLinearIsometry
  let A : E →ₗᵢ[ℝ] E := L.extend
  let T : E ≃ₗᵢ[ℝ] E := A.toLinearIsometryEquiv rfl
  refine ⟨T, ?_⟩
  have himage (i : Fin 2) : T (u i) ∈ R := by
    let ui : S := ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩
    have hA : A (u i) = L ui := by
      simpa [ui, A] using LinearIsometry.extend_apply L ui
    change A (u i) ∈ R
    rw [hA]
    change (eSR ui : E) ∈ R
    exact (eSR ui).property
  have hle : Submodule.span ℝ
      (Set.range (fun i ↦ T (u i))) ≤ R := by
    apply Submodule.span_le.2
    rintro y ⟨i, rfl⟩
    exact himage i
  have hker : LinearMap.ker T.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr T.injective
  have hLI : LinearIndependent ℝ (fun i ↦ T (u i)) := by
    change LinearIndependent ℝ (T.toLinearMap ∘ u)
    exact hu.map' T.toLinearMap hker
  apply Submodule.eq_of_le_of_finrank_eq hle
  calc
    finrank ℝ (Submodule.span ℝ
        (Set.range (fun i ↦ T (u i)))) = 2 := by
      simpa using finrank_span_eq_card hLI
    _ = finrank ℝ R := hdimR.symm

/-! ## Constancy of the centered conditional decorated law -/

/-- With the same tail, two nonsingular prefixes spanning the same plane
give the same centered decoration. -/
theorem centeredCanonicalDecoratedTailGivenPrefix_eq_of_span_eq
    (m r : ℕ) (x : ℝ)
    (pref₁ pref₂ : NestedTuple (centeredSubspace (m + 1)) 2)
    (tail : NestedTuple (centeredSubspace (m + 1)) r)
    (hspan : Submodule.span ℝ
        (Set.range (nestedTupleToFin 2 pref₁)) =
      Submodule.span ℝ
        (Set.range (nestedTupleToFin 2 pref₂)))
    (hfull₁ : LinearIndependent ℝ
      (nestedTupleToFin (2 + r)
        (nestedTupleAppend 2 pref₁ r tail)))
    (hfull₂ : LinearIndependent ℝ
      (nestedTupleToFin (2 + r)
        (nestedTupleAppend 2 pref₂ r tail))) :
    centeredCanonicalDecoratedTailGivenPrefix m r x pref₁ tail =
      centeredCanonicalDecoratedTailGivenPrefix m r x pref₂ tail := by
  apply Prod.ext
  · unfold centeredCanonicalDecoratedTailGivenPrefix
    unfold standardizedRetainedTailLogStatistic
    simp only [Prod.fst]
    rw [retainedTailLogSum_eq_of_prefix_span_eq
      2 r pref₁ pref₂ tail hspan hfull₁ hfull₂]
  · rfl

/-- Any two linearly independent centered prefixes induce the same joint
law of the retained Bartlett tail and the remote count. -/
theorem map_centeredCanonicalDecoratedTailGivenPrefix_eq_of_linearIndependent
    (m r : ℕ) (x : ℝ) (hqr : 2 + r ≤ m)
    (pref₁ pref₂ : NestedTuple (centeredSubspace (m + 1)) 2)
    (hpref₁ : LinearIndependent ℝ (nestedTupleToFin 2 pref₁))
    (hpref₂ : LinearIndependent ℝ (nestedTupleToFin 2 pref₂)) :
    Measure.map
        (centeredCanonicalDecoratedTailGivenPrefix m r x pref₁)
        (nestedProductMeasure
          (stdGaussian (centeredSubspace (m + 1))) r) =
      Measure.map
        (centeredCanonicalDecoratedTailGivenPrefix m r x pref₂)
        (nestedProductMeasure
          (stdGaussian (centeredSubspace (m + 1))) r) := by
  let E := centeredSubspace (m + 1)
  let μ := nestedProductMeasure (stdGaussian E) r
  obtain ⟨T, hTspan⟩ := exists_linearIsometryEquiv_map_span_pair
    (nestedTupleToFin 2 pref₁) (nestedTupleToFin 2 pref₂)
    hpref₁ hpref₂
  let prefT : NestedTuple E 2 := nestedTupleMap T 2 pref₁
  have hprefT : LinearIndependent ℝ (nestedTupleToFin 2 prefT) := by
    have hker : LinearMap.ker T.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr T.injective
    have hLI := hpref₁.map' T.toLinearMap hker
    rw [nestedTupleToFin_nestedTupleMap]
    change LinearIndependent ℝ (T.toLinearMap ∘ nestedTupleToFin 2 pref₁)
    exact hLI
  have hspan : Submodule.span ℝ
      (Set.range (nestedTupleToFin 2 prefT)) =
      Submodule.span ℝ
        (Set.range (nestedTupleToFin 2 pref₂)) := by
    rw [nestedTupleToFin_nestedTupleMap]
    change Submodule.span ℝ
        (Set.range (fun i ↦ T (nestedTupleToFin 2 pref₁ i))) = _
    exact hTspan
  let D₁ := centeredCanonicalDecoratedTailGivenPrefix m r x pref₁
  let DT := centeredCanonicalDecoratedTailGivenPrefix m r x prefT
  let D₂ := centeredCanonicalDecoratedTailGivenPrefix m r x pref₂
  have hrotate : D₁ = DT ∘ nestedTupleMap T r := by
    funext tail
    exact (centeredCanonicalDecoratedTailGivenPrefix_nestedTupleMap
      m r x T.toLinearIsometry pref₁ tail).symm
  have hDT : Measurable DT :=
    measurable_centeredCanonicalDecoratedTailGivenPrefix m r x prefT
  have hmapT : Measurable (nestedTupleMap T r) :=
    measurable_nestedTupleMap T.continuous.measurable r
  rw [show centeredCanonicalDecoratedTailGivenPrefix m r x pref₁ = D₁ by rfl]
  rw [hrotate, ← Measure.map_map hDT hmapT]
  rw [show Measure.map (nestedTupleMap T r) μ = μ by
    exact map_nestedTupleMap_stdGaussian T r]
  change Measure.map DT μ = Measure.map D₂ μ
  apply Measure.map_congr
  have hdim : finrank ℝ E = m := by
    exact finrank_centeredSubspace (Nat.zero_lt_succ m)
  have hbound : 2 + r ≤ finrank ℝ E := by
    simpa [hdim] using hqr
  have haeT := ae_linearIndependent_nestedTupleAppend_stdGaussian
    2 prefT hprefT r hbound
  have hae₂ := ae_linearIndependent_nestedTupleAppend_stdGaussian
    2 pref₂ hpref₂ r hbound
  filter_upwards [haeT, hae₂] with tail hfullT hfull₂
  exact centeredCanonicalDecoratedTailGivenPrefix_eq_of_span_eq
    m r x prefT pref₂ tail hspan hfullT hfull₂

/-- Turn an ordinary two-vector family into the right-nested tuple used by
the Gaussian product model. -/
def nestedTupleTwoOfFin {E : Type} (v : Fin 2 → E) : NestedTuple E 2 :=
  ((ULift.up Unit.unit, v ⟨0, by omega⟩), v ⟨1, by omega⟩)

@[simp] theorem nestedTupleToFin_nestedTupleTwoOfFin
    {E : Type} (v : Fin 2 → E) :
    nestedTupleToFin 2 (nestedTupleTwoOfFin v) = v := by
  funext i
  fin_cases i <;> rfl

/-- The centered decorated-tail law is indeed constant over almost every
two-column Gaussian prefix throughout the admissible range. -/
theorem centeredCanonicalDecoratedTailLawInvariant
    (m r : ℕ) (x : ℝ) (hqr : 2 + r ≤ m) :
    CenteredCanonicalDecoratedTailLawInvariant m r x := by
  let E := centeredSubspace (m + 1)
  have hdim : finrank ℝ E = m :=
    finrank_centeredSubspace (Nat.zero_lt_succ m)
  have htwo : 2 ≤ finrank ℝ E := by
    rw [hdim]
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
    (R := ℝ) (M := E) htwo
  let pref₀ : NestedTuple E 2 := nestedTupleTwoOfFin v
  have hpref₀ : LinearIndependent ℝ (nestedTupleToFin 2 pref₀) := by
    rw [show nestedTupleToFin 2 pref₀ = v by
      exact nestedTupleToFin_nestedTupleTwoOfFin v]
    exact hv
  let μ := nestedProductMeasure (stdGaussian E) r
  let D₀ := centeredCanonicalDecoratedTailGivenPrefix m r x pref₀
  have hD₀ : Measurable D₀ :=
    measurable_centeredCanonicalDecoratedTailGivenPrefix m r x pref₀
  letI : IsProbabilityMeasure (stdGaussian E) :=
    ProbabilityTheory.isProbabilityMeasure_stdGaussian
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact nestedProductMeasure_isProbability (stdGaussian E) r
  letI : IsProbabilityMeasure (Measure.map D₀ μ) :=
    Measure.isProbabilityMeasure_map hD₀.aemeasurable
  let κ : ProbabilityMeasure (ℝ × ℕ) :=
    ⟨Measure.map D₀ μ, inferInstance⟩
  refine ⟨κ, ?_⟩
  have hprefAE : ∀ᵐ pref ∂nestedProductMeasure (stdGaussian E) 2,
      LinearIndependent ℝ (nestedTupleToFin 2 pref) :=
    ae_linearIndependent_nested_stdGaussian 2 htwo
  filter_upwards [hprefAE] with pref hpref
  change Measure.map
      (centeredCanonicalDecoratedTailGivenPrefix m r x pref) μ =
    Measure.map D₀ μ
  exact map_centeredCanonicalDecoratedTailGivenPrefix_eq_of_linearIndependent
    m r x hqr pref pref₀ hpref hpref₀

/-- Raw-space formulation of the proved invariant. -/
theorem canonicalDecoratedTailLawInvariant_admissible
    (m r : ℕ) (x : ℝ) (hqr : 2 + r ≤ m) :
    CanonicalDecoratedTailLawInvariant m r x :=
  canonicalDecoratedTailLawInvariant_of_centered
    (centeredCanonicalDecoratedTailLawInvariant m r x hqr)

/-! ## Unconditional exact independence endpoints -/

/-- The entire raw two-column prefix, not merely its exceedance indicator,
is independent of the decorated tail once the geometric invariant is known. -/
theorem nestedTuplePrefix_indep_canonicalDecoratedTail_of_invariant
    {m r : ℕ} {x : ℝ}
    (hinv : CanonicalDecoratedTailLawInvariant m r x) :
    IndepFun (nestedTuplePrefix
        (E := ObservationSpace (m + 1)) 2 r)
      (canonicalDecoratedTail m r x)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) := by
  obtain ⟨κ, hκ⟩ := hinv
  let μpref := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) 2
  let μtail := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) r
  letI : IsProbabilityMeasure
      (stdGaussian (ObservationSpace (m + 1))) :=
    ProbabilityTheory.isProbabilityMeasure_stdGaussian
  letI : IsProbabilityMeasure μpref := by
    dsimp [μpref]
    exact nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) 2
  letI : IsProbabilityMeasure μtail := by
    dsimp [μtail]
    exact nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) r
  letI : IsProbabilityMeasure
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) :=
    nestedProductMeasure_isProbability
      (stdGaussian (ObservationSpace (m + 1))) (2 + r)
  have hprod : IndepFun
      (fun z : NestedTuple (ObservationSpace (m + 1)) 2 ×
          NestedTuple (ObservationSpace (m + 1)) r ↦ z.1)
      (fun z ↦ canonicalDecoratedTailGivenPrefix m r x z.1 z.2)
      (μpref.prod μtail) :=
    indepFun_prefix_decorated_of_ae_map_eq
      μpref μtail id
      (canonicalDecoratedTailGivenPrefix m r x)
      measurable_id
      (measurable_uncurry_canonicalDecoratedTailGivenPrefix m r x)
      κ hκ
  let F := nestedTupleSplit
    (α := ObservationSpace (m + 1)) 2 r
  have hF : Measurable F := measurable_nestedTupleSplit 2 r
  have hmap : Measure.map F
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) =
      μpref.prod μtail :=
    map_nestedTupleSplit_nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) 2 r
  have hcomp := IndepFun.comp_of_map_eq hprod hF
    measurable_fst
    (measurable_uncurry_canonicalDecoratedTailGivenPrefix m r x) hmap
  change IndepFun
    (nestedTuplePrefix (E := ObservationSpace (m + 1)) 2 r)
    (fun data ↦
      (standardizedGaussianRetainedTailStatistic m 2 r data,
        remoteCoherenceExceedanceCount m r x
          (nestedTupleTail 2 r data)))
    (nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) (2 + r))
  simpa [F, μpref, μtail, nestedTupleSplit,
    canonicalDecoratedTailGivenPrefix, Function.comp_def] using hcomp

/-- Admissible-range form of actual-prefix/decorated-tail independence. -/
theorem nestedTuplePrefix_indep_canonicalDecoratedTail
    (m r : ℕ) (x : ℝ) (hqr : 2 + r ≤ m) :
    IndepFun (nestedTuplePrefix
        (E := ObservationSpace (m + 1)) 2 r)
      (canonicalDecoratedTail m r x)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) :=
  nestedTuplePrefix_indep_canonicalDecoratedTail_of_invariant
    (canonicalDecoratedTailLawInvariant_admissible m r x hqr)

/-- Every measurable mark computed from the actual canonical two-column
prefix is independent of the decorated tail.  This is the form needed by
Fubini and `L¹` mark-replacement arguments. -/
theorem prefixStatistic_indep_canonicalDecoratedTail
    {G : Type*} [MeasurableSpace G]
    (m r : ℕ) (x : ℝ) (hqr : 2 + r ≤ m)
    (X : NestedTuple (ObservationSpace (m + 1)) 2 → G)
    (hX : Measurable X) :
    IndepFun (X ∘ nestedTuplePrefix
        (E := ObservationSpace (m + 1)) 2 r)
      (canonicalDecoratedTail m r x)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) := by
  have h := nestedTuplePrefix_indep_canonicalDecoratedTail m r x hqr
  simpa only [Function.id_comp] using h.comp hX measurable_id

/-- In particular, the canonical exceedance indicator has the requested
exact joint independence from the retained Bartlett tail and remote count. -/
theorem canonicalEdgeExceedanceIndicator_indep_canonicalDecoratedTail_admissible
    (m r : ℕ) (x : ℝ) (hqr : 2 + r ≤ m) :
    IndepFun (canonicalEdgeExceedanceIndicator m r x)
      (canonicalDecoratedTail m r x)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) :=
  canonicalEdgeExceedanceIndicator_indep_canonicalDecoratedTail
    (canonicalDecoratedTailLawInvariant_admissible m r x hqr)

end

end LogdetLean.Coherence
