import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseAssembly
/-!
# Deterministic symmetry of the finite cofactor vector

This file records common-phase homogeneity and permutation covariance in a
form ready for the exchangeability step of Fourier compression.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

theorem columnTransposeGram_commonPhase
    {ι : Type*} [Fintype ι] {k : ℕ} (c : ℂ)
    (A : ι → (Fin k → ℂ)) :
    columnTransposeGram (fun i p ↦ c * A i p) =
      fun i j ↦ c ^ 2 * columnTransposeGram A i j := by
  funext i j
  unfold columnTransposeGram
  calc
    (∑ p : Fin k, (c * A i p) * (c * A j p)) =
        ∑ p : Fin k, c ^ 2 * (A i p * A j p) := by
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ = c ^ 2 * ∑ p : Fin k, A i p * A j p := by
      rw [Finset.mul_sum]

theorem typeMatchingMonomial_const_mul
    {α R : Type*} [Fintype α] [LinearOrder α] [CommMonoid R]
    (s : R) (B : Matrix α α R) (M : TypePerfectMatching α) :
    typeMatchingMonomial (fun i j ↦ s * B i j) M =
      s ^ (TypePerfectMatching.genericPairReps M).card *
        typeMatchingMonomial B M := by
  classical
  unfold typeMatchingMonomial
  rw [Finset.prod_mul_distrib]
  simp

theorem typeHafnian_const_mul_of_card
    {α R : Type*} [Fintype α] [LinearOrder α] [CommSemiring R]
    (r : ℕ) (hcard : Fintype.card α = 2 * r)
    (s : R) (B : Matrix α α R) :
    typeHafnian (fun i j ↦ s * B i j) = s ^ r * typeHafnian B := by
  classical
  unfold typeHafnian
  calc
    (∑ M : TypePerfectMatching α,
        typeMatchingMonomial (fun i j ↦ s * B i j) M) =
        ∑ M : TypePerfectMatching α,
          s ^ r * typeMatchingMonomial B M := by
      apply Finset.sum_congr rfl
      intro M _hM
      rw [typeMatchingMonomial_const_mul]
      have hrep := TypePerfectMatching.card_genericPairReps_two_mul M
      congr 2
      omega
    _ = s ^ r * ∑ M : TypePerfectMatching α,
        typeMatchingMonomial B M := by
      rw [Finset.mul_sum]

/-- A common complex phase on every column scales each odd cofactor by its
total column degree `m+1`. -/
theorem finiteGramCofactorVector_commonPhase
    {m k r : ℕ} (hdegree : m + 1 = 2 * r)
    (c : ℂ) (A : TwoExposedColumnFamily m k) (j : Fin (m + 2)) :
    finiteGramCofactorVector (fun i p ↦ c * A i p) j =
      c ^ (m + 1) * finiteGramCofactorVector A j := by
  unfold finiteGramCofactorVector
  rw [columnTransposeGram_commonPhase]
  have hcard : Fintype.card {i : Fin (m + 2) // i ≠ j} = 2 * r := by
    rw [Fintype.card_subtype_compl]
    have hone : Fintype.card {i : Fin (m + 2) // i = j} = 1 := by
      simp
    rw [hone]
    simp only [Fintype.card_fin]
    omega
  rw [typeHafnian_const_mul_of_card r hcard]
  rw [← pow_mul, ← hdegree]

theorem twoExposedCofactorVector_commonPhase
    {m k r : ℕ} (hdegree : m + 1 = 2 * r)
    (c : ℂ) (A : TwoExposedColumnFamily m k) :
    twoExposedCofactorVector (fun i p ↦ c * A i p) =
      fun j ↦ c ^ (m + 1) * twoExposedCofactorVector A j := by
  funext j
  exact finiteGramCofactorVector_commonPhase hdegree c A j

namespace TypePerfectMatching

/-- The lower endpoint, in the target order, of the transported pair
containing `i`.  This construction does not require the relabelling to
preserve order. -/
def transportedPairRepresentative
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃ β)
    (M : TypePerfectMatching α) (i : α) : β :=
  if e i < e (M i) then e i else e (M i)

theorem transportedPairRepresentative_mem
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃ β)
    (M : TypePerfectMatching α) (i : α) :
    transportedPairRepresentative e M i ∈
      genericPairReps (congr e M) := by
  classical
  by_cases h : e i < e (M i)
  · unfold genericPairReps
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold transportedPairRepresentative
    rw [if_pos h]
    change e i < e (M (e.symm (e i)))
    simpa using h
  · have hne : e i ≠ e (M i) := by
      exact fun heq ↦ M.mate_ne i (e.injective heq).symm
    have hlt : e (M i) < e i := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    unfold genericPairReps
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold transportedPairRepresentative
    rw [if_neg h]
    change e (M i) < e (M (e.symm (e (M i))))
    simpa [M.mate_mate] using hlt

def pairRepresentativeTransport
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃ β)
    (M : TypePerfectMatching α) :
    {i : α // i ∈ genericPairReps M} →
      {j : β // j ∈ genericPairReps (congr e M)} :=
  fun i ↦ ⟨transportedPairRepresentative e M i.1,
    transportedPairRepresentative_mem e M i.1⟩

theorem pairRepresentativeTransport_injective
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃ β)
    (M : TypePerfectMatching α) :
    Function.Injective (pairRepresentativeTransport e M) := by
  classical
  intro a b hab
  apply Subtype.ext
  have haold : a.1 < M a.1 := by
    simpa [genericPairReps] using a.2
  have hbold : b.1 < M b.1 := by
    simpa [genericPairReps] using b.2
  have hv : transportedPairRepresentative e M a.1 =
      transportedPairRepresentative e M b.1 :=
    congrArg Subtype.val hab
  by_cases ha : e a.1 < e (M a.1)
  · by_cases hb : e b.1 < e (M b.1)
    · simp only [transportedPairRepresentative, if_pos ha, if_pos hb] at hv
      exact e.injective hv
    · simp only [transportedPairRepresentative, if_pos ha, if_neg hb] at hv
      have hamb : a.1 = M b.1 := e.injective hv
      have hmab : M a.1 = b.1 := by
        rw [hamb, M.mate_mate]
      have hab : a.1 < b.1 := haold.trans_eq hmab
      have hba : b.1 < a.1 := hbold.trans_eq hamb.symm
      exfalso
      exact (lt_asymm hab hba)
  · by_cases hb : e b.1 < e (M b.1)
    · simp only [transportedPairRepresentative, if_neg ha, if_pos hb] at hv
      have hmahb : M a.1 = b.1 := e.injective hv
      have habm : a.1 = M b.1 := by
        have := congrArg M hmahb
        simpa [M.mate_mate] using this
      have hab : a.1 < b.1 := haold.trans_eq hmahb
      have hba : b.1 < a.1 := hbold.trans_eq habm.symm
      exfalso
      exact (lt_asymm hab hba)
    · simp only [transportedPairRepresentative, if_neg ha, if_neg hb] at hv
      exact M.mate.injective (e.injective hv)

theorem pairRepresentativeTransport_bijective
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃ β)
    (M : TypePerfectMatching α) :
    Function.Bijective (pairRepresentativeTransport e M) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨pairRepresentativeTransport_injective e M, ?_⟩
  simp only [Fintype.card_coe]
  have hα := card_genericPairReps_two_mul M
  have hβ := card_genericPairReps_two_mul (congr e M)
  have hecard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  omega

def pairRepresentativeTransportEquiv
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃ β)
    (M : TypePerfectMatching α) :
    {i : α // i ∈ genericPairReps M} ≃
      {j : β // j ∈ genericPairReps (congr e M)} :=
  Equiv.ofBijective (pairRepresentativeTransport e M)
    (pairRepresentativeTransport_bijective e M)

end TypePerfectMatching

/-- A matching monomial of a symmetric matrix is invariant under an
arbitrary relabelling; order changes merely select the other endpoint of
some unordered pairs. -/
theorem typeMatchingMonomial_reindex_equiv_of_symmetric
    {α β R : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] [CommMonoid R]
    (e : α ≃ β) (B : Matrix β β R)
    (hB : ∀ i j, B i j = B j i)
    (M : TypePerfectMatching α) :
    typeMatchingMonomial (fun i j ↦ B (e i) (e j)) M =
      typeMatchingMonomial B (TypePerfectMatching.congr e M) := by
  classical
  unfold typeMatchingMonomial
  refine Finset.prod_nbij
    (s := TypePerfectMatching.genericPairReps M)
    (t := TypePerfectMatching.genericPairReps
      (TypePerfectMatching.congr e M))
    (fun i ↦ TypePerfectMatching.transportedPairRepresentative e M i)
    ?_ ?_ ?_ ?_
  · intro i _hi
    exact TypePerfectMatching.transportedPairRepresentative_mem e M i
  · intro i hi j hj hij
    have hsub :
        TypePerfectMatching.pairRepresentativeTransport e M ⟨i, hi⟩ =
          TypePerfectMatching.pairRepresentativeTransport e M ⟨j, hj⟩ := by
      apply Subtype.ext
      exact hij
    exact congrArg Subtype.val
      (TypePerfectMatching.pairRepresentativeTransport_injective e M hsub)
  · intro y hy
    obtain ⟨x, hx⟩ :=
      (TypePerfectMatching.pairRepresentativeTransport_bijective e M).2
        ⟨y, hy⟩
    refine ⟨x.1, x.2, ?_⟩
    exact congrArg Subtype.val hx
  · intro i hi
    by_cases h : e i < e (M i)
    · unfold TypePerfectMatching.transportedPairRepresentative
      rw [if_pos h]
      change B (e i) (e (M i)) = B (e i) (e (M (e.symm (e i))))
      simp
    · unfold TypePerfectMatching.transportedPairRepresentative
      rw [if_neg h]
      change
        B (e i) (e (M i)) =
          B (e (M i)) (e (M (e.symm (e (M i)))))
      simpa [M.mate_mate] using hB (e i) (e (M i))

/-- Hafnians of symmetric matrices are invariant under arbitrary finite
relabellings, not only order isomorphisms. -/
theorem typeHafnian_reindex_equiv_of_symmetric
    {α β R : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] [CommSemiring R]
    (e : α ≃ β) (B : Matrix β β R)
    (hB : ∀ i j, B i j = B j i) :
    typeHafnian (fun i j ↦ B (e i) (e j)) = typeHafnian B := by
  classical
  unfold typeHafnian
  apply Fintype.sum_equiv (TypePerfectMatching.congr e)
  intro M
  exact typeMatchingMonomial_reindex_equiv_of_symmetric e B hB M

/-- Relabelling equivalence restricted to the complements of corresponding
deleted indices. -/
def deleteIndexEquiv {α β : Type*} (e : α ≃ β) (j : α) :
    {i : α // i ≠ j} ≃ {u : β // u ≠ e j} where
  toFun i := ⟨e i.1, by
    intro h
    exact i.2 (e.injective h)⟩
  invFun u := ⟨e.symm u.1, by
    intro h
    apply u.2
    have := congrArg e h
    simpa using this⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv u := by apply Subtype.ext; simp

/-- Cofactor vectors of transpose-Gram matrices are covariant under every
finite column relabelling. -/
theorem finiteGramCofactorVector_reindex_equiv
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] {k : ℕ}
    (e : α ≃ β) (A : β → (Fin k → ℂ)) (j : α) :
    finiteGramCofactorVector (fun i ↦ A (e i)) j =
      finiteGramCofactorVector A (e j) := by
  unfold finiteGramCofactorVector
  let eDelete := deleteIndexEquiv e j
  let B : Matrix {u : β // u ≠ e j} {u : β // u ≠ e j} ℂ :=
    columnTransposeGram (fun u : {u : β // u ≠ e j} ↦ A u.1)
  calc
    typeHafnian (columnTransposeGram
        (fun i : {i : α // i ≠ j} ↦ A (e i.1))) =
      typeHafnian (fun i l ↦ B (eDelete i) (eDelete l)) := by
        rfl
    _ = typeHafnian B := by
      exact typeHafnian_reindex_equiv_of_symmetric eDelete B
        (columnTransposeGram_comm _)

theorem twoExposedCofactorVector_reindex_perm
    {m k : ℕ} (σ : Equiv.Perm (Fin (m + 2)))
    (A : TwoExposedColumnFamily m k) (j : Fin (m + 2)) :
    twoExposedCofactorVector (fun i ↦ A (σ i)) j =
      twoExposedCofactorVector A (σ j) := by
  exact finiteGramCofactorVector_reindex_equiv σ A j

/-- Simultaneously permuting columns and Fourier weights leaves their
cofactor pairing unchanged.  This is the deterministic identity used with
exchangeability of iid columns. -/
theorem weightedCofactorSum_reindex_perm
    {m k : ℕ} (σ : Equiv.Perm (Fin (m + 2)))
    (A : TwoExposedColumnFamily m k) (w : Fin (m + 2) → ℂ) :
    (∑ j : Fin (m + 2),
        w (σ j) * twoExposedCofactorVector (fun i ↦ A (σ i)) j) =
      ∑ j : Fin (m + 2), w j * twoExposedCofactorVector A j := by
  simp_rw [twoExposedCofactorVector_reindex_perm]
  apply Fintype.sum_equiv σ
  intro j
  rfl

theorem weightedCofactorRealPhase_reindex_perm
    {m k : ℕ} (σ : Equiv.Perm (Fin (m + 2)))
    (A : TwoExposedColumnFamily m k) (w : Fin (m + 2) → ℂ) :
    (∑ j : Fin (m + 2),
        w (σ j) * twoExposedCofactorVector (fun i ↦ A (σ i)) j).re =
      (∑ j : Fin (m + 2),
        w j * twoExposedCofactorVector A j).re := by
  rw [weightedCofactorSum_reindex_perm]

end

end LogdetLean.GramHafnian
