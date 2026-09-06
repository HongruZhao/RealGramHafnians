import LogdetLean.GramHafnian.CircularGaussianMoments
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorTypeHafnian
import Mathlib.Probability.Independence.Basic
/-!
# Literal independent-edge symmetric Gaussian ensemble

One independent standard circular complex Gaussian is assigned to each
unordered pair of distinct vertices.  The assembled matrix has zero diagonal;
this is the off-diagonal model used by ordinary hafnians, not a claim that the
full matrix has the variance-two diagonal convention of symmetric-Gaussian
hiding theorems.  All probability laws below are pushforwards of actual finite
products of the existing two-real-Gaussian construction `circularGaussian`.

The restriction theorem holds for every injective vertex map.  In particular,
deleting any vertex gives exactly the same independent-edge Gaussian law on
the remaining subtype; no cofactor-law axiom is introduced.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Unordered pairs of distinct vertices. -/
abbrev Edge (ι : Type*) := {e : Finset ι // e.card = 2}

/-- The genuine finite product of standard circular complex Gaussian laws. -/
def standardGaussianProduct (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  Measure.pi fun _ : ι ↦ circularGaussian

instance standardGaussianProduct_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (standardGaussianProduct ι) := by
  unfold standardGaussianProduct
  infer_instance

/-- Every coordinate of the finite product is standard circular Gaussian. -/
theorem standardGaussianProduct_map_eval {ι : Type*} [Fintype ι] (i : ι) :
    (standardGaussianProduct ι).map (fun x ↦ x i) = circularGaussian := by
  classical
  exact (measurePreserving_eval (fun _ : ι ↦ circularGaussian) i).map_eq

/-- Coordinates are jointly independent, not merely pairwise independent. -/
theorem iIndepFun_standardGaussianProduct {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (x : ι → ℂ) ↦ x i) (standardGaussianProduct ι) := by
  exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)

/-- An injective coordinate restriction preserves the corresponding product
Gaussian law, including restrictions to an empty index type. -/
theorem measurePreserving_standardGaussianProduct_restrict
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    MeasurePreserving (fun x : κ → ℂ ↦ fun i : ι ↦ x (f i))
      (standardGaussianProduct κ) (standardGaussianProduct ι) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  have hi : iIndepFun (fun i (x : κ → ℂ) ↦ x (f i))
      (standardGaussianProduct κ) :=
    iIndepFun_standardGaussianProduct.precomp f.injective
  rw [iIndepFun.map_fun_eq_pi_map
    (fun i ↦ (measurable_pi_apply (f i)).aemeasurable) hi]
  change (Measure.pi fun i : ι ↦
    (standardGaussianProduct κ).map (fun x ↦ x (f i))) =
      Measure.pi (fun _ : ι ↦ circularGaussian)
  congr 1
  funext i
  exact standardGaussianProduct_map_eval (f i)

/-- The law of all unordered edge variables. -/
abbrev edgeGaussian (ι : Type*) [Fintype ι] : Measure (Edge ι → ℂ) :=
  standardGaussianProduct (Edge ι)

/-- The edge joining two distinct vertices. -/
def edgeOfNe {ι : Type*} [DecidableEq ι] (i j : ι) (h : i ≠ j) : Edge ι :=
  ⟨{i, j}, by simp [h]⟩

theorem edgeOfNe_swap {ι : Type*} [DecidableEq ι]
    (i j : ι) (h : i ≠ j) : edgeOfNe i j h = edgeOfNe j i h.symm := by
  apply Subtype.ext
  exact Finset.pair_comm i j

/-- Assemble the literal symmetric, zero-diagonal matrix from edge data. -/
def matrixOfEdges {ι : Type*} [DecidableEq ι]
    (x : Edge ι → ℂ) : Matrix ι ι ℂ :=
  fun i j ↦ if h : i = j then 0 else x (edgeOfNe i j h)

@[simp] theorem matrixOfEdges_diag {ι : Type*} [DecidableEq ι]
    (x : Edge ι → ℂ) (i : ι) : matrixOfEdges x i i = 0 := by
  simp [matrixOfEdges]

@[simp] theorem matrixOfEdges_apply_ne {ι : Type*} [DecidableEq ι]
    (x : Edge ι → ℂ) (i j : ι) (h : i ≠ j) :
    matrixOfEdges x i j = x (edgeOfNe i j h) := by
  simp [matrixOfEdges, h]

theorem matrixOfEdges_symmetric {ι : Type*} [DecidableEq ι]
    (x : Edge ι → ℂ) (i j : ι) : matrixOfEdges x i j = matrixOfEdges x j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp only [matrixOfEdges_apply_ne x i j h,
      matrixOfEdges_apply_ne x j i h']
    rw [edgeOfNe_swap i j h]

@[fun_prop] theorem continuous_matrixOfEdges {ι : Type*} [DecidableEq ι] :
    Continuous (matrixOfEdges : (Edge ι → ℂ) → Matrix ι ι ℂ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i = j
  · simpa [matrixOfEdges, h] using
      (continuous_const : Continuous (fun _ : Edge ι → ℂ ↦ (0 : ℂ)))
  · simpa [matrixOfEdges, h] using continuous_apply (edgeOfNe i j h)

@[fun_prop] theorem measurable_matrixOfEdges {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    Measurable (fun (x : Edge ι → ℂ) (i j : ι) ↦ matrixOfEdges x i j) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  by_cases h : i = j
  · simpa [matrixOfEdges, h] using
      (measurable_const : Measurable (fun _ : Edge ι → ℂ ↦ (0 : ℂ)))
  · simpa [matrixOfEdges, h] using measurable_pi_apply (edgeOfNe i j h)

/-- Map an unordered edge along an injective vertex map. -/
def edgeEmbedding {ι κ : Type*} (f : ι ↪ κ) : Edge ι ↪ Edge κ where
  toFun e := ⟨e.1.map f, by simpa using e.2⟩
  inj' := by
    intro e d h
    apply Subtype.ext
    exact Finset.map_injective f (congrArg Subtype.val h)

@[simp] theorem edgeEmbedding_edgeOfNe {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] (f : ι ↪ κ)
    (i j : ι) (h : i ≠ j) :
    edgeEmbedding f (edgeOfNe i j h) =
      edgeOfNe (f i) (f j) (fun hij ↦ h (f.injective hij)) := by
  apply Subtype.ext
  change ({i, j} : Finset ι).map f = {f i, f j}
  simp

/-- Pull back edge coordinates to an injectively indexed vertex submatrix. -/
def restrictEdges {ι κ : Type*} (f : ι ↪ κ)
    (x : Edge κ → ℂ) : Edge ι → ℂ := fun e ↦ x (edgeEmbedding f e)

@[fun_prop] theorem measurable_restrictEdges {ι κ : Type*} (f : ι ↪ κ) :
    Measurable (restrictEdges f) := by
  unfold restrictEdges
  fun_prop

/-- Principal submatrices have the exact independent-edge product law. -/
theorem measurePreserving_restrictEdges {ι κ : Type*}
    [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    MeasurePreserving (restrictEdges f) (edgeGaussian κ) (edgeGaussian ι) :=
  measurePreserving_standardGaussianProduct_restrict (edgeEmbedding f)

theorem matrixOfEdges_restrict {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] (f : ι ↪ κ) (x : Edge κ → ℂ) :
    matrixOfEdges (restrictEdges f x) = fun i j ↦ matrixOfEdges x (f i) (f j) := by
  funext i j
  by_cases h : i = j
  · subst j
    simp
  · have hf : f i ≠ f j := fun hij ↦ h (f.injective hij)
    simp [matrixOfEdges, h, hf, restrictEdges]

/-- An arbitrary vertex equivalence induces an unordered-edge equivalence. -/
def edgeEquiv {ι κ : Type*} (e : ι ≃ κ) : Edge ι ≃ Edge κ where
  toFun := edgeEmbedding e.toEmbedding
  invFun := edgeEmbedding e.symm.toEmbedding
  left_inv x := by
    apply Subtype.ext
    change (x.1.map e.toEmbedding).map e.symm.toEmbedding = x.1
    simp [Finset.map_map]
  right_inv x := by
    apply Subtype.ext
    change (x.1.map e.symm.toEmbedding).map e.toEmbedding = x.1
    simp [Finset.map_map]

/-- The literal matching-sum hafnian of the independent-edge matrix. -/
def edgeHafnian {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℂ) : ℂ := typeHafnian (matrixOfEdges x)

@[simp] theorem edgeHafnian_eq_one_of_isEmpty {ι : Type*} [Fintype ι]
    [LinearOrder ι] [IsEmpty ι] (x : Edge ι → ℂ) : edgeHafnian x = 1 :=
  typeHafnian_eq_one_of_isEmpty _

@[fun_prop] theorem continuous_edgeHafnian {ι : Type*} [Fintype ι]
    [LinearOrder ι] : Continuous (edgeHafnian : (Edge ι → ℂ) → ℂ) :=
  continuous_typeHafnian.comp continuous_matrixOfEdges

@[fun_prop] theorem measurable_edgeHafnian {ι : Type*} [Fintype ι]
    [LinearOrder ι] : Measurable (edgeHafnian : (Edge ι → ℂ) → ℂ) :=
  continuous_edgeHafnian.measurable

/-- Literal principal hafnian cofactors, not a surrogate Gaussian vector. -/
def edgeCofactor {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℂ) (j : ι) : ℂ :=
  typeHafnian (fun a b : {i : ι // i ≠ j} ↦ matrixOfEdges x a.1 b.1)

@[simp] theorem edgeCofactor_fin_one (x : Edge (Fin 1) → ℂ) (j : Fin 1) :
    edgeCofactor x j = 1 := by
  letI : IsEmpty {i : Fin 1 // i ≠ j} :=
    ⟨fun i ↦ i.2 (Subsingleton.elim i.1 j)⟩
  exact typeHafnian_eq_one_of_isEmpty _

@[fun_prop] theorem continuous_edgeCofactor {ι : Type*} [Fintype ι]
    [LinearOrder ι] : Continuous (edgeCofactor : (Edge ι → ℂ) → (ι → ℂ)) := by
  apply continuous_pi
  intro j
  unfold edgeCofactor
  apply continuous_typeHafnian.comp
  fun_prop

@[fun_prop] theorem measurable_edgeCofactor {ι : Type*} [Fintype ι]
    [LinearOrder ι] : Measurable (edgeCofactor : (Edge ι → ℂ) → (ι → ℂ)) :=
  continuous_edgeCofactor.measurable

/-- The squared Euclidean energy of the literal cofactor vector. -/
def edgeCofactorEnergy {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℂ) : ℝ := ∑ j, ‖edgeCofactor x j‖ ^ 2

@[simp] theorem edgeCofactorEnergy_fin_one (x : Edge (Fin 1) → ℂ) :
    edgeCofactorEnergy x = 1 := by
  simp [edgeCofactorEnergy]

@[fun_prop] theorem continuous_edgeCofactorEnergy {ι : Type*} [Fintype ι]
    [LinearOrder ι] : Continuous (edgeCofactorEnergy : (Edge ι → ℂ) → ℝ) := by
  unfold edgeCofactorEnergy
  fun_prop

@[fun_prop] theorem measurable_edgeCofactorEnergy {ι : Type*} [Fintype ι]
    [LinearOrder ι] : Measurable (edgeCofactorEnergy : (Edge ι → ℂ) → ℝ) :=
  continuous_edgeCofactorEnergy.measurable

theorem edgeCofactorEnergy_nonneg {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℂ) : 0 ≤ edgeCofactorEnergy x := by
  unfold edgeCofactorEnergy
  exact Finset.sum_nonneg fun j _ ↦ sq_nonneg _

/-- The actual independent-edge hafnian law. -/
def edgeHafnianLaw (ι : Type*) [Fintype ι] [LinearOrder ι] : Measure ℂ :=
  (edgeGaussian ι).map edgeHafnian

/-- The actual odd cofactor vector law. -/
def edgeCofactorLaw (ι : Type*) [Fintype ι] [LinearOrder ι] : Measure (ι → ℂ) :=
  (edgeGaussian ι).map edgeCofactor

/-- The actual cofactor energy law. -/
def edgeCofactorEnergyLaw (ι : Type*) [Fintype ι] [LinearOrder ι] : Measure ℝ :=
  (edgeGaussian ι).map edgeCofactorEnergy

instance edgeHafnianLaw_isProbabilityMeasure (ι : Type*) [Fintype ι] [LinearOrder ι] :
    IsProbabilityMeasure (edgeHafnianLaw ι) := by
  unfold edgeHafnianLaw
  exact Measure.isProbabilityMeasure_map measurable_edgeHafnian.aemeasurable

instance edgeCofactorLaw_isProbabilityMeasure (ι : Type*) [Fintype ι] [LinearOrder ι] :
    IsProbabilityMeasure (edgeCofactorLaw ι) := by
  unfold edgeCofactorLaw
  exact Measure.isProbabilityMeasure_map measurable_edgeCofactor.aemeasurable

instance edgeCofactorEnergyLaw_isProbabilityMeasure
    (ι : Type*) [Fintype ι] [LinearOrder ι] :
    IsProbabilityMeasure (edgeCofactorEnergyLaw ι) := by
  unfold edgeCofactorEnergyLaw
  exact Measure.isProbabilityMeasure_map measurable_edgeCofactorEnergy.aemeasurable

/-- Every principal hafnian has the smaller independent-edge hafnian law. -/
theorem principalHafnianLaw {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [DecidableEq κ] (f : ι ↪ κ) :
    (edgeGaussian κ).map
      (fun x ↦ typeHafnian (fun i j ↦ matrixOfEdges x (f i) (f j))) =
      edgeHafnianLaw ι := by
  have hfun : (fun x ↦ typeHafnian (fun i j ↦ matrixOfEdges x (f i) (f j))) =
      edgeHafnian ∘ restrictEdges f := by
    funext x
    simp only [Function.comp_apply, edgeHafnian, matrixOfEdges_restrict]
  rw [hfun, ← Measure.map_map measurable_edgeHafnian (measurable_restrictEdges f),
    (measurePreserving_restrictEdges f).map_eq]
  rfl

/-- A coordinate of the literal cofactor vector is exactly a hafnian on
the deleted vertex subtype, under its genuine independent-edge Gaussian law. -/
theorem edgeCofactor_component_law {ι : Type*} [Fintype ι] [LinearOrder ι]
    (j : ι) :
    (edgeGaussian ι).map (fun x ↦ edgeCofactor x j) =
      edgeHafnianLaw {i : ι // i ≠ j} := by
  exact principalHafnianLaw (Function.Embedding.subtype fun i : ι ↦ i ≠ j)

/-- Zero mean of every edge variable, inherited from the actual scalar law. -/
theorem integral_edge_coordinate {ι : Type*} [Fintype ι] (e : Edge ι) :
    (∫ x, x e ∂edgeGaussian ι) = 0 := by
  have h := integral_id_circularGaussian
  rw [← standardGaussianProduct_map_eval e,
    integral_map (measurable_pi_apply e).aemeasurable (by fun_prop)] at h
  exact h

/-- Unit second moment of every off-diagonal entry. -/
theorem integral_edge_coordinate_mul_conj {ι : Type*} [Fintype ι] (e : Edge ι) :
    (∫ x, x e * conj (x e) ∂edgeGaussian ι) = 1 := by
  have h := integral_mul_conj_circularGaussian
  rw [← standardGaussianProduct_map_eval e,
    integral_map (measurable_pi_apply e).aemeasurable (by fun_prop)] at h
  exact h

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
