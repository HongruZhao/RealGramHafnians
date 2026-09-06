import LogdetLean.GramHafnian.SymmetricGaussianHafnian.Ensemble
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseDefinitions
/-!
# Independent edge exposure

The literal independent-edge Gaussian data split into a background, two
independent edge vectors, and the independent edge between the exposed
vertices.  Every measure equality is proved by an injective coordinate map
and finite product measure preservation.
-/

open MeasureTheory ProbabilityTheory Complex

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Combine two embeddings whose images are disjoint. -/
def disjointSumEmbedding {α β γ : Type*} (f : α ↪ γ) (g : β ↪ γ)
    (h : ∀ a b, f a ≠ g b) : α ⊕ β ↪ γ where
  toFun := Sum.elim f g
  inj' := by
    rintro (a | b) (a' | b') he
    · exact congrArg Sum.inl (f.injective he)
    · exact False.elim (h a b' he)
    · exact False.elim (h a' b he.symm)
    · exact congrArg Sum.inr (g.injective he)

/-- A background edge never contains a vertex outside the background. -/
theorem not_mem_edgeEmbedding {ι κ : Type*} (f : ι ↪ κ) (c : κ)
    (hc : ∀ i, f i ≠ c) (e : Edge ι) : c ∉ (edgeEmbedding f e).1 := by
  change c ∉ e.1.map f
  intro hm
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hm
  exact hc i hi

/-- An independently indexed family of edges from a background to one
external vertex. -/
def starEdgeEmbedding {ι κ : Type*} [DecidableEq κ] (f : ι ↪ κ)
    (c : κ) (hc : ∀ i, f i ≠ c) : ι ↪ Edge κ where
  toFun i := edgeOfNe (f i) c (hc i)
  inj' := by
    intro i j he
    have hs : ({f i, c} : Finset κ) = {f j, c} := congrArg Subtype.val he
    have hi : f i ∈ ({f j, c} : Finset κ) := by rw [← hs]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact f.injective hi
    · exact False.elim (hc i hi)

theorem backgroundEdge_ne_star {ι κ : Type*} [DecidableEq κ]
    (f : ι ↪ κ) (c : κ) (hc : ∀ i, f i ≠ c) (e : Edge ι) (i : ι) :
    edgeEmbedding f e ≠ starEdgeEmbedding f c hc i := by
  intro he
  apply not_mem_edgeEmbedding f c hc e
  rw [he]
  change c ∈ ({f i, c} : Finset κ)
  simp

/-- One external vertex yields background edges plus an independent star. -/
def oneVertexEdgeEmbedding {ι κ : Type*} [DecidableEq κ]
    (f : ι ↪ κ) (c : κ) (hc : ∀ i, f i ≠ c) : Edge ι ⊕ ι ↪ Edge κ :=
  disjointSumEmbedding (edgeEmbedding f) (starEdgeEmbedding f c hc)
    (backgroundEdge_ne_star f c hc)

/-- A singleton coordinate for the edge joining two exposed vertices. -/
def exposedPairEmbedding {κ : Type*} [DecidableEq κ]
    (c d : κ) (hcd : c ≠ d) : Unit ↪ Edge κ where
  toFun _ := edgeOfNe c d hcd
  inj' := fun _ _ _ ↦ Subsingleton.elim _ _

theorem distinctStars_disjoint {ι κ : Type*} [DecidableEq κ]
    (f : ι ↪ κ) (c d : κ) (hc : ∀ i, f i ≠ c) (hd : ∀ i, f i ≠ d)
    (hcd : c ≠ d) (i j : ι) :
    starEdgeEmbedding f c hc i ≠ starEdgeEmbedding f d hd j := by
  intro he
  have hs : ({f i, c} : Finset κ) = {f j, d} := congrArg Subtype.val he
  have hm : c ∈ ({f j, d} : Finset κ) := by rw [← hs]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact hc j hm.symm
  · exact hcd hm

theorem exposedPair_ne_starLeft {ι κ : Type*} [DecidableEq κ]
    (f : ι ↪ κ) (c d : κ) (hc : ∀ i, f i ≠ c) (hd : ∀ i, f i ≠ d)
    (hcd : c ≠ d) (u : Unit) (i : ι) :
    exposedPairEmbedding c d hcd u ≠ starEdgeEmbedding f c hc i := by
  intro he
  have hs : ({c, d} : Finset κ) = {f i, c} := congrArg Subtype.val he
  have hm : d ∈ ({f i, c} : Finset κ) := by rw [← hs]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact hd i hm.symm
  · exact hcd hm.symm

theorem exposedPair_ne_starRight {ι κ : Type*} [DecidableEq κ]
    (f : ι ↪ κ) (c d : κ) (hc : ∀ i, f i ≠ c) (hd : ∀ i, f i ≠ d)
    (hcd : c ≠ d) (u : Unit) (i : ι) :
    exposedPairEmbedding c d hcd u ≠ starEdgeEmbedding f d hd i := by
  intro he
  have hs : ({c, d} : Finset κ) = {f i, d} := congrArg Subtype.val he
  have hm : c ∈ ({f i, d} : Finset κ) := by rw [← hs]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact hc i hm.symm
  · exact hcd hm

/-- The four disjoint edge-coordinate classes for two exposed vertices. -/
def twoVertexEdgeEmbedding {ι κ : Type*} [DecidableEq κ]
    (f : ι ↪ κ) (c d : κ) (hc : ∀ i, f i ≠ c) (hd : ∀ i, f i ≠ d)
    (hcd : c ≠ d) : Edge ι ⊕ (Unit ⊕ (ι ⊕ ι)) ↪ Edge κ :=
  disjointSumEmbedding (edgeEmbedding f)
    (disjointSumEmbedding (exposedPairEmbedding c d hcd)
      (disjointSumEmbedding (starEdgeEmbedding f c hc) (starEdgeEmbedding f d hd)
        (distinctStars_disjoint f c d hc hd hcd))
      (by
        intro u i
        cases i with
        | inl i => exact exposedPair_ne_starLeft f c d hc hd hcd u i
        | inr i => exact exposedPair_ne_starRight f c d hc hd hcd u i))
    (by
      intro e i
      rcases i with u | (i | i)
      · intro he
        apply not_mem_edgeEmbedding f c hc e
        rw [he]
        change c ∈ ({c, d} : Finset κ)
        simp
      · exact backgroundEdge_ne_star f c hc e i
      · exact backgroundEdge_ne_star f d hd e i)

/-- Splitting a product Gaussian indexed by a sum into its two products. -/
theorem measurePreserving_standardGaussianProduct_splitSum
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurePreserving
      (fun x : (ι ⊕ κ) → ℂ ↦ (fun i ↦ x (.inl i), fun j ↦ x (.inr j)))
      (standardGaussianProduct (ι ⊕ κ))
      ((standardGaussianProduct ι).prod (standardGaussianProduct κ)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ ↦ circularGaussian)

/-- The data order used by the literal cofactor phase: background, scalar,
then the two exposed edge vectors. -/
def unpackTwoVertexCoordinates {ι : Type*}
    (x : (Edge ι ⊕ (Unit ⊕ (ι ⊕ ι))) → ℂ) :
    (Edge ι → ℂ) × (ℂ × ((ι → ℂ) × (ι → ℂ))) :=
  (fun e ↦ x (.inl e),
    (x (.inr (.inl ())),
      (fun i ↦ x (.inr (.inr (.inl i))), fun i ↦ x (.inr (.inr (.inr i))))))

theorem measurePreserving_unpackTwoVertexCoordinates
    {ι : Type*} [Fintype ι] :
    MeasurePreserving (unpackTwoVertexCoordinates (ι := ι))
      (standardGaussianProduct (Edge ι ⊕ (Unit ⊕ (ι ⊕ ι))))
      ((edgeGaussian ι).prod (circularGaussian.prod
        ((standardGaussianProduct ι).prod (standardGaussianProduct ι)))) := by
  have hxy := measurePreserving_standardGaussianProduct_splitSum (ι := ι) (κ := ι)
  have hu : MeasurePreserving (fun x : Unit → ℂ ↦ x ())
      (standardGaussianProduct Unit) circularGaussian :=
    ⟨measurable_pi_apply (), standardGaussianProduct_map_eval ()⟩
  have huxy := (hu.prod hxy).comp
    (measurePreserving_standardGaussianProduct_splitSum (ι := Unit) (κ := ι ⊕ ι))
  have hall := ((MeasurePreserving.id (edgeGaussian ι)).prod huxy).comp
    (measurePreserving_standardGaussianProduct_splitSum
      (ι := Edge ι) (κ := Unit ⊕ (ι ⊕ ι)))
  exact hall

/-- Simultaneously expose both stars and their common scalar edge. -/
def twoVertexSplit {ι κ : Type*} [DecidableEq κ]
    (f : ι ↪ κ) (c d : κ) (hc : ∀ i, f i ≠ c) (hd : ∀ i, f i ≠ d)
    (hcd : c ≠ d) (x : Edge κ → ℂ) :
    (Edge ι → ℂ) × (ℂ × ((ι → ℂ) × (ι → ℂ))) :=
  unpackTwoVertexCoordinates (fun e ↦ x (twoVertexEdgeEmbedding f c d hc hd hcd e))

theorem measurePreserving_twoVertexSplit {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι ↪ κ) (c d : κ) (hc : ∀ i, f i ≠ c) (hd : ∀ i, f i ≠ d)
    (hcd : c ≠ d) :
    MeasurePreserving (twoVertexSplit f c d hc hd hcd) (edgeGaussian κ)
      ((edgeGaussian ι).prod (circularGaussian.prod
        ((standardGaussianProduct ι).prod (standardGaussianProduct ι)))) :=
  measurePreserving_unpackTwoVertexCoordinates.comp
    (measurePreserving_standardGaussianProduct_restrict
      (twoVertexEdgeEmbedding f c d hc hd hcd))

def remainingVertexEmbedding (m : ℕ) : Fin m ↪ Fin (m + 2) where
  toFun := remainingIndex m
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun a : Fin (m + 2) ↦ a.1) h

abbrev twoExposedEdgeEmbedding (m : ℕ) :
    (Edge (Fin m) ⊕ (Unit ⊕ (Fin m ⊕ Fin m))) ↪ Edge (Fin (m + 2)) :=
  twoVertexEdgeEmbedding (remainingVertexEmbedding m)
    (exposedXIndex m) (exposedYIndex m)
    (ne_exposedXIndex_of_remaining m) (ne_exposedYIndex_of_remaining m)
    (exposedXIndex_ne_exposedYIndex m)

def twoExposedSplit (m : ℕ) (x : Edge (Fin (m + 2)) → ℂ) :
    (Edge (Fin m) → ℂ) × (ℂ × ((Fin m → ℂ) × (Fin m → ℂ))) :=
  twoVertexSplit (remainingVertexEmbedding m)
    (exposedXIndex m) (exposedYIndex m)
    (ne_exposedXIndex_of_remaining m) (ne_exposedYIndex_of_remaining m)
    (exposedXIndex_ne_exposedYIndex m) x

theorem measurePreserving_twoExposedSplit (m : ℕ) :
    MeasurePreserving (twoExposedSplit m) (edgeGaussian (Fin (m + 2)))
      ((edgeGaussian (Fin m)).prod (circularGaussian.prod
        ((standardGaussianProduct (Fin m)).prod (standardGaussianProduct (Fin m))))) :=
  measurePreserving_twoVertexSplit _ _ _ _ _ _

@[simp] theorem twoExposedSplit_background (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℂ) :
    (twoExposedSplit m x).1 = restrictEdges (remainingVertexEmbedding m) x := rfl

@[simp] theorem matrixOfEdges_twoExposedSplit_background (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℂ) (i j : Fin m) :
    matrixOfEdges (twoExposedSplit m x).1 i j =
      matrixOfEdges x (remainingIndex m i) (remainingIndex m j) := by
  rw [twoExposedSplit_background, matrixOfEdges_restrict]
  rfl

@[simp] theorem twoExposedSplit_scalar (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℂ) :
    (twoExposedSplit m x).2.1 =
      matrixOfEdges x (exposedXIndex m) (exposedYIndex m) := by
  change x (edgeOfNe (exposedXIndex m) (exposedYIndex m)
    (exposedXIndex_ne_exposedYIndex m)) = _
  exact (matrixOfEdges_apply_ne x _ _ _).symm

@[simp] theorem twoExposedSplit_X (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℂ) (i : Fin m) :
    (twoExposedSplit m x).2.2.1 i =
      matrixOfEdges x (remainingIndex m i) (exposedXIndex m) := by
  change x (edgeOfNe (remainingIndex m i) (exposedXIndex m)
    (ne_exposedXIndex_of_remaining m i)) = _
  exact (matrixOfEdges_apply_ne x _ _ _).symm

@[simp] theorem twoExposedSplit_Y (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℂ) (i : Fin m) :
    (twoExposedSplit m x).2.2.2 i =
      matrixOfEdges x (remainingIndex m i) (exposedYIndex m) := by
  change x (edgeOfNe (remainingIndex m i) (exposedYIndex m)
    (ne_exposedYIndex_of_remaining m i)) = _
  exact (matrixOfEdges_apply_ne x _ _ _).symm

def initialVertexEmbedding (m : ℕ) : Fin m ↪ Fin (m + 1) where
  toFun := Fin.castSucc
  inj' := Fin.castSucc_injective m

def lastVertexSplit (m : ℕ) (x : Edge (Fin (m + 1)) → ℂ) :
    (Edge (Fin m) → ℂ) × (Fin m → ℂ) :=
  (restrictEdges (initialVertexEmbedding m) x,
    fun i ↦ matrixOfEdges x i.castSucc (Fin.last m))

@[simp] theorem lastVertexSplit_background (m : ℕ)
    (x : Edge (Fin (m + 1)) → ℂ) :
    (lastVertexSplit m x).1 = restrictEdges (initialVertexEmbedding m) x := rfl

@[simp] theorem lastVertexSplit_star (m : ℕ)
    (x : Edge (Fin (m + 1)) → ℂ) (i : Fin m) :
    (lastVertexSplit m x).2 i = matrixOfEdges x i.castSucc (Fin.last m) := rfl

@[simp] theorem matrixOfEdges_lastVertexSplit_background (m : ℕ)
    (x : Edge (Fin (m + 1)) → ℂ) (i j : Fin m) :
    matrixOfEdges (lastVertexSplit m x).1 i j = matrixOfEdges x i.castSucc j.castSucc := by
  rw [lastVertexSplit_background, matrixOfEdges_restrict]
  rfl

theorem measurePreserving_lastVertexSplit (m : ℕ) :
    MeasurePreserving (lastVertexSplit m) (edgeGaussian (Fin (m + 1)))
      ((edgeGaussian (Fin m)).prod (standardGaussianProduct (Fin m))) := by
  let emb := oneVertexEdgeEmbedding (initialVertexEmbedding m) (Fin.last m)
    (fun i ↦ Fin.castSucc_ne_last i)
  have h := measurePreserving_standardGaussianProduct_splitSum.comp
    (measurePreserving_standardGaussianProduct_restrict emb)
  convert h using 1
  funext x
  apply Prod.ext
  · rfl
  · funext i
    simp [lastVertexSplit, emb, oneVertexEdgeEmbedding, disjointSumEmbedding,
      starEdgeEmbedding, matrixOfEdges, initialVertexEmbedding]

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
