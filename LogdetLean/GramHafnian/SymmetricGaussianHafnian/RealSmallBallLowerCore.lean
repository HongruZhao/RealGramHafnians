import LogdetLean.GramHafnian.SymmetricGaussianHafnian.LastVertex
import Mathlib.Probability.Independence.CharacteristicFunction
/-!
# Literal real independent-edge Gaussian hafnians

This isolated module develops the real counterpart of the literal complex
independent-edge ensemble.  Its scalar law is `gaussianReal 0 1`; no complex
surrogate or scientific axiom is used.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- A finite product of genuine standard real Gaussian coordinates. -/
def standardRealGaussianProduct (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι ↦ gaussianReal 0 1

instance standardRealGaussianProduct_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (standardRealGaussianProduct ι) := by
  unfold standardRealGaussianProduct
  infer_instance

theorem standardRealGaussianProduct_map_eval {ι : Type*} [Fintype ι] (i : ι) :
    (standardRealGaussianProduct ι).map (fun x ↦ x i) = gaussianReal 0 1 := by
  classical
  exact (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).map_eq

/-- A real Gaussian linear form in genuine independent coordinates. -/
def iidRealLinearForm {ι : Type*} [Fintype ι] (y g : ι → ℝ) : ℝ :=
  ∑ j, g j * y j

def realCoefficientEnergy {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ :=
  ∑ j, y j ^ 2

theorem realCoefficientEnergy_nonneg {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    0 ≤ realCoefficientEnergy y := by
  unfold realCoefficientEnergy
  positivity

@[fun_prop] theorem measurable_iidRealLinearForm {ι : Type*} [Fintype ι]
    (y : ι → ℝ) : Measurable (iidRealLinearForm y) := by
  unfold iidRealLinearForm
  fun_prop

@[fun_prop] theorem measurable_iidRealLinearForm_joint {ι : Type*} [Fintype ι] :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) ↦ iidRealLinearForm p.1 p.2) := by
  unfold iidRealLinearForm
  fun_prop

theorem charFun_iidRealLinearForm_product {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (t : ℝ) :
    charFun ((standardRealGaussianProduct ι).map (iidRealLinearForm y)) t =
      ∏ j, charFun (gaussianReal 0 1) (t * y j) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  change (∫ x : ι → ℝ, _ ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1)) = _
  simp_rw [iidRealLinearForm, sum_inner, Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]
  convert integral_fintype_prod_eq_prod
    (fun (j : ι) (g : ℝ) ↦
      Complex.exp (((g * y j * t : ℝ) : ℂ) * Complex.I))
    (μ := fun _ : ι ↦ gaussianReal 0 1) using 1 <;>
    simp [charFun_apply, real_inner_comm, mul_assoc, mul_left_comm, mul_comm]

theorem charFun_iidRealLinearForm {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (t : ℝ) :
    charFun ((standardRealGaussianProduct ι).map (iidRealLinearForm y)) t =
      Complex.exp (-((realCoefficientEnergy y * t ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFun_iidRealLinearForm_product]
  simp_rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero, zero_mul, NNReal.coe_one,
    Complex.ofReal_one, one_mul, zero_sub, ← Complex.exp_sum]
  congr 1
  simp only [realCoefficientEnergy, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sum]
  simp only [mul_zero, zero_mul, zero_sub]
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]
  have hs : (∑ j, (t * y j : ℂ) ^ 2) =
      ∑ j, (y j : ℂ) ^ 2 * (t : ℂ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  rw [← Finset.sum_mul]
  ring

/-- Exact law of a real Gaussian linear form, including zero energy. -/
theorem iidRealLinearForm_law {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    (standardRealGaussianProduct ι).map (iidRealLinearForm y) =
      (gaussianReal 0 1).map
        (fun z : ℝ ↦ Real.sqrt (realCoefficientEnergy y) * z) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_iidRealLinearForm]
  have hmap :
      charFun ((gaussianReal 0 1).map
        (fun z : ℝ ↦ Real.sqrt (realCoefficientEnergy y) * z)) t =
        charFun (gaussianReal 0 1) (Real.sqrt (realCoefficientEnergy y) * t) := by
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
    congr 1
    funext z
    congr 1
    push_cast
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hmap]
  rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one,
    one_mul, zero_sub]
  congr 1
  simp only [mul_zero, zero_mul, zero_sub]
  have hreal : (Real.sqrt (realCoefficientEnergy y) * t) ^ 2 =
      realCoefficientEnergy y * t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (realCoefficientEnergy_nonneg y)]
  rw [← Complex.ofReal_pow, hreal]
  push_cast
  ring

/-! ## Literal real independent-edge ensemble -/

abbrev realEdgeGaussian (ι : Type*) [Fintype ι] : Measure (Edge ι → ℝ) :=
  standardRealGaussianProduct (Edge ι)

def realMatrixOfEdges {ι : Type*} [DecidableEq ι]
    (x : Edge ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ if h : i = j then 0 else x (edgeOfNe i j h)

@[simp] theorem realMatrixOfEdges_diag {ι : Type*} [DecidableEq ι]
    (x : Edge ι → ℝ) (i : ι) : realMatrixOfEdges x i i = 0 := by
  simp [realMatrixOfEdges]

@[simp] theorem realMatrixOfEdges_apply_ne {ι : Type*} [DecidableEq ι]
    (x : Edge ι → ℝ) (i j : ι) (h : i ≠ j) :
    realMatrixOfEdges x i j = x (edgeOfNe i j h) := by
  simp [realMatrixOfEdges, h]

theorem realMatrixOfEdges_symmetric {ι : Type*} [DecidableEq ι]
    (x : Edge ι → ℝ) (i j : ι) :
    realMatrixOfEdges x i j = realMatrixOfEdges x j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp only [realMatrixOfEdges_apply_ne x i j h,
      realMatrixOfEdges_apply_ne x j i h']
    rw [edgeOfNe_swap i j h]

@[fun_prop] theorem continuous_realMatrixOfEdges {ι : Type*} [DecidableEq ι] :
    Continuous (realMatrixOfEdges : (Edge ι → ℝ) → Matrix ι ι ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i = j
  · simpa [realMatrixOfEdges, h] using
      (continuous_const : Continuous (fun _ : Edge ι → ℝ ↦ (0 : ℝ)))
  · simpa [realMatrixOfEdges, h] using continuous_apply (edgeOfNe i j h)

@[fun_prop] theorem measurable_realMatrixOfEdges {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    Measurable (fun (x : Edge ι → ℝ) (i j : ι) ↦ realMatrixOfEdges x i j) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  by_cases h : i = j
  · simpa [realMatrixOfEdges, h] using
      (measurable_const : Measurable (fun _ : Edge ι → ℝ ↦ (0 : ℝ)))
  · simpa [realMatrixOfEdges, h] using measurable_pi_apply (edgeOfNe i j h)

def realRestrictEdges {ι κ : Type*} (f : ι ↪ κ)
    (x : Edge κ → ℝ) : Edge ι → ℝ := fun e ↦ x (edgeEmbedding f e)

@[fun_prop] theorem measurable_realRestrictEdges {ι κ : Type*} (f : ι ↪ κ) :
    Measurable (realRestrictEdges f) := by
  unfold realRestrictEdges
  fun_prop

theorem measurePreserving_standardRealGaussianProduct_restrict
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    MeasurePreserving (fun x : κ → ℝ ↦ fun i : ι ↦ x (f i))
      (standardRealGaussianProduct κ) (standardRealGaussianProduct ι) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  have hi : iIndepFun (fun i (x : κ → ℝ) ↦ x (f i))
      (standardRealGaussianProduct κ) :=
    (iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)).precomp f.injective
  rw [iIndepFun.map_fun_eq_pi_map
    (fun i ↦ (measurable_pi_apply (f i)).aemeasurable) hi]
  change (Measure.pi fun i : ι ↦
    (standardRealGaussianProduct κ).map (fun x ↦ x (f i))) =
      Measure.pi (fun _ : ι ↦ gaussianReal 0 1)
  congr 1
  funext i
  exact standardRealGaussianProduct_map_eval (f i)

theorem measurePreserving_realRestrictEdges {ι κ : Type*}
    [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    MeasurePreserving (realRestrictEdges f)
      (realEdgeGaussian κ) (realEdgeGaussian ι) :=
  measurePreserving_standardRealGaussianProduct_restrict (edgeEmbedding f)

theorem realMatrixOfEdges_restrict {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] (f : ι ↪ κ) (x : Edge κ → ℝ) :
    realMatrixOfEdges (realRestrictEdges f x) =
      fun i j ↦ realMatrixOfEdges x (f i) (f j) := by
  funext i j
  by_cases h : i = j
  · subst j
    simp
  · have hf : f i ≠ f j := fun hij ↦ h (f.injective hij)
    simp [realMatrixOfEdges, h, hf, realRestrictEdges]

def realEdgeHafnian {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℝ) : ℝ := typeHafnian (realMatrixOfEdges x)

@[simp] theorem realEdgeHafnian_eq_one_of_isEmpty {ι : Type*} [Fintype ι]
    [LinearOrder ι] [IsEmpty ι] (x : Edge ι → ℝ) : realEdgeHafnian x = 1 :=
  typeHafnian_eq_one_of_isEmpty _

@[fun_prop] theorem continuous_realEdgeHafnian {ι : Type*} [Fintype ι]
    [LinearOrder ι] : Continuous (realEdgeHafnian : (Edge ι → ℝ) → ℝ) := by
  unfold realEdgeHafnian typeHafnian typeMatchingMonomial
  fun_prop

@[fun_prop] theorem measurable_realEdgeHafnian {ι : Type*} [Fintype ι]
    [LinearOrder ι] : Measurable (realEdgeHafnian : (Edge ι → ℝ) → ℝ) :=
  continuous_realEdgeHafnian.measurable

def realEdgeCofactor {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℝ) (j : ι) : ℝ :=
  matrixCofactor (realMatrixOfEdges x) j

@[fun_prop] theorem continuous_realEdgeCofactor {ι : Type*} [Fintype ι]
    [LinearOrder ι] :
    Continuous (realEdgeCofactor : (Edge ι → ℝ) → (ι → ℝ)) := by
  apply continuous_pi
  intro j
  unfold realEdgeCofactor matrixCofactor typeHafnian typeMatchingMonomial
  fun_prop

@[fun_prop] theorem measurable_realEdgeCofactor {ι : Type*} [Fintype ι]
    [LinearOrder ι] :
    Measurable (realEdgeCofactor : (Edge ι → ℝ) → (ι → ℝ)) :=
  continuous_realEdgeCofactor.measurable

def realEdgeCofactorEnergy {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℝ) : ℝ := ∑ j, (realEdgeCofactor x j) ^ 2

@[fun_prop] theorem continuous_realEdgeCofactorEnergy {ι : Type*} [Fintype ι]
    [LinearOrder ι] :
    Continuous (realEdgeCofactorEnergy : (Edge ι → ℝ) → ℝ) := by
  unfold realEdgeCofactorEnergy
  fun_prop

@[fun_prop] theorem measurable_realEdgeCofactorEnergy {ι : Type*} [Fintype ι]
    [LinearOrder ι] :
    Measurable (realEdgeCofactorEnergy : (Edge ι → ℝ) → ℝ) :=
  continuous_realEdgeCofactorEnergy.measurable

theorem realEdgeCofactorEnergy_nonneg {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℝ) : 0 ≤ realEdgeCofactorEnergy x := by
  unfold realEdgeCofactorEnergy
  positivity

def realEdgeHafnianLaw (ι : Type*) [Fintype ι] [LinearOrder ι] : Measure ℝ :=
  (realEdgeGaussian ι).map realEdgeHafnian

/-! ## Last-vertex split and exact conditional law -/

theorem measurePreserving_standardRealGaussianProduct_splitSum
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurePreserving
      (fun x : (ι ⊕ κ) → ℝ ↦ (fun i ↦ x (.inl i), fun j ↦ x (.inr j)))
      (standardRealGaussianProduct (ι ⊕ κ))
      ((standardRealGaussianProduct ι).prod (standardRealGaussianProduct κ)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ ↦ gaussianReal 0 1)

def realLastVertexSplit (m : ℕ) (x : Edge (Fin (m + 1)) → ℝ) :
    (Edge (Fin m) → ℝ) × (Fin m → ℝ) :=
  (realRestrictEdges (initialVertexEmbedding m) x,
    fun i ↦ realMatrixOfEdges x i.castSucc (Fin.last m))

theorem measurePreserving_realLastVertexSplit (m : ℕ) :
    MeasurePreserving (realLastVertexSplit m) (realEdgeGaussian (Fin (m + 1)))
      ((realEdgeGaussian (Fin m)).prod (standardRealGaussianProduct (Fin m))) := by
  let emb := oneVertexEdgeEmbedding (initialVertexEmbedding m) (Fin.last m)
    (fun i ↦ Fin.castSucc_ne_last i)
  have h := measurePreserving_standardRealGaussianProduct_splitSum.comp
    (measurePreserving_standardRealGaussianProduct_restrict emb)
  convert h using 1
  funext x
  apply Prod.ext
  · rfl
  · funext i
    simp [realLastVertexSplit, emb, oneVertexEdgeEmbedding, disjointSumEmbedding,
      starEdgeEmbedding, realMatrixOfEdges, initialVertexEmbedding]

theorem realAppendMatrix_lastVertexSplit (m : ℕ)
    (x : Edge (Fin (m + 1)) → ℝ) :
    appendMatrix (realMatrixOfEdges (realLastVertexSplit m x).1)
      (realLastVertexSplit m x).2 = realMatrixOfEdges x := by
  unfold realLastVertexSplit
  rw [realMatrixOfEdges_restrict]
  exact appendMatrix_reconstruct (realMatrixOfEdges x)
    (realMatrixOfEdges_symmetric x) (realMatrixOfEdges_diag x (Fin.last m))

theorem realEdgeHafnian_eq_lastVertexLinearForm {n : ℕ}
    (x : Edge (Fin (n + 1)) → ℝ) :
    realEdgeHafnian x =
      iidRealLinearForm (realEdgeCofactor (realLastVertexSplit n x).1)
        (realLastVertexSplit n x).2 := by
  unfold realEdgeHafnian
  rw [← realAppendMatrix_lastVertexSplit n x, typeHafnian_appendMatrix_eq_sum]
  rfl

theorem realEdgeHafnianLaw_eq_lastVertexProduct (n : ℕ) :
    realEdgeHafnianLaw (Fin (n + 1)) =
      ((realEdgeGaussian (Fin n)).prod (standardRealGaussianProduct (Fin n))).map
        (fun p ↦ iidRealLinearForm (realEdgeCofactor p.1) p.2) := by
  rw [← (measurePreserving_realLastVertexSplit n).map_eq,
    Measure.map_map (by fun_prop) (measurePreserving_realLastVertexSplit n).measurable]
  unfold realEdgeHafnianLaw
  congr 1
  funext x
  exact realEdgeHafnian_eq_lastVertexLinearForm x

/-! ## Exact real second moment -/

theorem integrable_sq_gaussianReal :
    Integrable (fun z : ℝ ↦ z ^ 2) (gaussianReal 0 1) :=
  integrable_pow_gaussianReal 2

theorem integral_sq_gaussianReal :
    (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
  simpa using integral_pow_two_gaussianReal 1

theorem lintegral_sq_gaussianReal :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ 2) ∂gaussianReal 0 1) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_sq_gaussianReal
    (Filter.Eventually.of_forall (fun z ↦ sq_nonneg z)), integral_sq_gaussianReal]
  simp

theorem lintegral_sq_iidRealLinearForm
    {n : ℕ} (y : Fin n → ℝ) :
    (∫⁻ g : Fin n → ℝ, ENNReal.ofReal ((iidRealLinearForm y g) ^ 2)
      ∂standardRealGaussianProduct (Fin n)) =
      ENNReal.ofReal (realCoefficientEnergy y) := by
  have hmap := iidRealLinearForm_law y
  have hm : Measurable (fun z : ℝ ↦ ENNReal.ofReal (z ^ 2)) := by fun_prop
  have hV := realCoefficientEnergy_nonneg y
  calc
    _ = ∫⁻ z : ℝ, ENNReal.ofReal (z ^ 2)
        ∂((standardRealGaussianProduct (Fin n)).map (iidRealLinearForm y)) := by
      rw [lintegral_map hm (measurable_iidRealLinearForm y)]
    _ = ∫⁻ z : ℝ, ENNReal.ofReal (z ^ 2)
        ∂((gaussianReal 0 1).map
          (fun z : ℝ ↦ Real.sqrt (realCoefficientEnergy y) * z)) := by
      rw [hmap]
    _ = ∫⁻ z : ℝ, ENNReal.ofReal
        ((Real.sqrt (realCoefficientEnergy y) * z) ^ 2)
        ∂gaussianReal 0 1 := by
      rw [lintegral_map hm (by fun_prop)]
    _ = ∫⁻ z : ℝ, ENNReal.ofReal (realCoefficientEnergy y) *
        ENNReal.ofReal (z ^ 2) ∂gaussianReal 0 1 := by
      apply lintegral_congr
      intro z
      rw [mul_pow, Real.sq_sqrt hV, ENNReal.ofReal_mul hV]
    _ = ENNReal.ofReal (realCoefficientEnergy y) := by
      rw [lintegral_const_mul _ hm, lintegral_sq_gaussianReal, mul_one]

theorem realEdgeHafnian_restrict_equiv
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) (x : Edge β → ℝ) :
    realEdgeHafnian (realRestrictEdges e.toEmbedding x) = realEdgeHafnian x := by
  unfold realEdgeHafnian
  rw [realMatrixOfEdges_restrict]
  exact typeHafnian_reindex_equiv_of_symmetric e (realMatrixOfEdges x)
    (realMatrixOfEdges_symmetric x)

theorem realEdgeHafnianLaw_reindex
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) : realEdgeHafnianLaw α = realEdgeHafnianLaw β := by
  unfold realEdgeHafnianLaw
  rw [← (measurePreserving_realRestrictEdges e.toEmbedding).map_eq,
    Measure.map_map measurable_realEdgeHafnian
      (measurable_realRestrictEdges e.toEmbedding)]
  congr 1
  funext x
  exact realEdgeHafnian_restrict_equiv e x

theorem realEdgeCofactor_component_law
    {ι : Type*} [Fintype ι] [LinearOrder ι] (j : ι) :
    (realEdgeGaussian ι).map (fun x ↦ realEdgeCofactor x j) =
      realEdgeHafnianLaw {i : ι // i ≠ j} := by
  let f : {i : ι // i ≠ j} ↪ ι := Function.Embedding.subtype fun i : ι ↦ i ≠ j
  have hfun : (fun x : Edge ι → ℝ ↦ realEdgeCofactor x j) =
      realEdgeHafnian ∘ realRestrictEdges f := by
    funext x
    unfold realEdgeCofactor matrixCofactor realEdgeHafnian
    simp only [Function.comp_apply]
    change typeHafnian (fun a b : {i : ι // i ≠ j} ↦
      realMatrixOfEdges x a.1 b.1) =
      typeHafnian (realMatrixOfEdges (realRestrictEdges f x))
    rw [realMatrixOfEdges_restrict]
    rfl
  rw [hfun, ← Measure.map_map measurable_realEdgeHafnian
    (measurable_realRestrictEdges f),
    (measurePreserving_realRestrictEdges f).map_eq]
  rfl

def realEdgeHafnianSecondMoment (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : Edge (Fin n) → ℝ, ENNReal.ofReal ((realEdgeHafnian x) ^ 2)
    ∂realEdgeGaussian (Fin n)

@[simp] theorem realEdgeHafnianSecondMoment_zero :
    realEdgeHafnianSecondMoment 0 = 1 := by
  simp [realEdgeHafnianSecondMoment]

theorem lintegral_sq_realEdgeHafnian_of_card
    {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hcard : Fintype.card ι = n) :
    (∫⁻ x : Edge ι → ℝ, ENNReal.ofReal ((realEdgeHafnian x) ^ 2)
      ∂realEdgeGaussian ι) = realEdgeHafnianSecondMoment n := by
  have hm : Measurable (fun z : ℝ ↦ ENNReal.ofReal (z ^ 2)) := by fun_prop
  rw [← lintegral_map hm measurable_realEdgeHafnian]
  change (∫⁻ z : ℝ, ENNReal.ofReal (z ^ 2) ∂realEdgeHafnianLaw ι) = _
  rw [realEdgeHafnianLaw_reindex (Fintype.equivFinOfCardEq hcard)]
  unfold realEdgeHafnianLaw realEdgeHafnianSecondMoment
  rw [lintegral_map hm measurable_realEdgeHafnian]

theorem lintegral_sq_realEdgeCofactor {n : ℕ} (j : Fin (n + 1)) :
    (∫⁻ x : Edge (Fin (n + 1)) → ℝ,
      ENNReal.ofReal ((realEdgeCofactor x j) ^ 2)
      ∂realEdgeGaussian (Fin (n + 1))) = realEdgeHafnianSecondMoment n := by
  have hm : Measurable (fun z : ℝ ↦ ENNReal.ofReal (z ^ 2)) := by fun_prop
  have hj : Measurable
      (fun x : Edge (Fin (n + 1)) → ℝ ↦ realEdgeCofactor x j) := by fun_prop
  rw [← lintegral_map hm hj, realEdgeCofactor_component_law]
  unfold realEdgeHafnianLaw
  rw [lintegral_map hm measurable_realEdgeHafnian]
  apply lintegral_sq_realEdgeHafnian_of_card
  rw [Fintype.card_subtype_compl]
  simp

theorem lintegral_realEdgeCofactorEnergy (n : ℕ) :
    (∫⁻ x : Edge (Fin (n + 1)) → ℝ,
      ENNReal.ofReal (realEdgeCofactorEnergy x)
      ∂realEdgeGaussian (Fin (n + 1))) =
      (n + 1 : ℕ) * realEdgeHafnianSecondMoment n := by
  classical
  unfold realEdgeCofactorEnergy
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun j _ ↦ by fun_prop)]
  simp_rw [lintegral_sq_realEdgeCofactor]
  simp

theorem realEdgeHafnianSecondMoment_succ (n : ℕ) :
    realEdgeHafnianSecondMoment (n + 1) =
      ∫⁻ x : Edge (Fin n) → ℝ, ENNReal.ofReal (realEdgeCofactorEnergy x)
        ∂realEdgeGaussian (Fin n) := by
  have hm : Measurable (fun z : ℝ ↦ ENNReal.ofReal (z ^ 2)) := by fun_prop
  have hform : Measurable
      (fun p : (Edge (Fin n) → ℝ) × (Fin n → ℝ) ↦
        iidRealLinearForm (realEdgeCofactor p.1) p.2) := by
    unfold iidRealLinearForm
    fun_prop
  unfold realEdgeHafnianSecondMoment
  rw [← lintegral_map hm measurable_realEdgeHafnian]
  change (∫⁻ z : ℝ, ENNReal.ofReal (z ^ 2)
    ∂realEdgeHafnianLaw (Fin (n + 1))) = _
  rw [realEdgeHafnianLaw_eq_lastVertexProduct n,
    lintegral_map hm hform]
  let F : ((Edge (Fin n) → ℝ) × (Fin n → ℝ)) → ℝ≥0∞ :=
    fun p ↦ ENNReal.ofReal
      ((iidRealLinearForm (realEdgeCofactor p.1) p.2) ^ 2)
  have hF : AEMeasurable F
      ((realEdgeGaussian (Fin n)).prod (standardRealGaussianProduct (Fin n))) := by
    exact (hm.comp hform).aemeasurable
  change (∫⁻ p, F p ∂((realEdgeGaussian (Fin n)).prod
    (standardRealGaussianProduct (Fin n)))) = _
  rw [lintegral_prod F hF]
  apply lintegral_congr
  intro x
  exact lintegral_sq_iidRealLinearForm (realEdgeCofactor x)

theorem realEdgeHafnianSecondMoment_step (n : ℕ) :
    realEdgeHafnianSecondMoment (n + 2) =
      (n + 1 : ℕ) * realEdgeHafnianSecondMoment n := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    realEdgeHafnianSecondMoment_succ, lintegral_realEdgeCofactorEnergy]

theorem realEdgeHafnianSecondMoment_even (n : ℕ) :
    realEdgeHafnianSecondMoment (2 * n) = (oddPairingNat n : ℝ≥0∞) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega,
        realEdgeHafnianSecondMoment_step, ih, oddPairingNat_succ, Nat.cast_mul]
      exact mul_comm _ _

theorem lintegral_realEdgeCofactorEnergy_odd (n : ℕ) :
    (∫⁻ x : Edge (Fin (2 * n + 1)) → ℝ,
      ENNReal.ofReal (realEdgeCofactorEnergy x)
      ∂realEdgeGaussian (Fin (2 * n + 1))) =
      (oddPairingNat (n + 1) : ℝ≥0∞) := by
  rw [lintegral_realEdgeCofactorEnergy, realEdgeHafnianSecondMoment_even,
    oddPairingNat_succ, Nat.cast_mul]
  exact mul_comm _ _

theorem integrable_realEdgeCofactorEnergy_odd (n : ℕ) :
    Integrable realEdgeCofactorEnergy
      (realEdgeGaussian (Fin (2 * n + 1))) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall realEdgeCofactorEnergy_nonneg),
    lintegral_realEdgeCofactorEnergy_odd]
  exact ENNReal.natCast_lt_top _

theorem integral_realEdgeCofactorEnergy_odd (n : ℕ) :
    (∫ x : Edge (Fin (2 * n + 1)) → ℝ, realEdgeCofactorEnergy x
      ∂realEdgeGaussian (Fin (2 * n + 1))) =
      (oddPairingNat (n + 1) : ℝ) := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg realEdgeCofactorEnergy_nonneg) (Nat.cast_nonneg _)).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_realEdgeCofactorEnergy_odd n)
    (Filter.Eventually.of_forall realEdgeCofactorEnergy_nonneg),
    lintegral_realEdgeCofactorEnergy_odd]
  simp


end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
