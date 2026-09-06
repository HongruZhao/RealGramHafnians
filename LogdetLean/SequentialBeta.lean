import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Beta
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic
import LogdetLean.GramSchmidtDeterminant
import LogdetLean.GramSchmidtProjection
import LogdetLean.GaussianLinearIndependence
/-!
# Sequentially constant conditional laws give an independent product law

This file isolates the probability-independence induction used in the
Gaussian-to-Beta bridge.  A sample is represented as a right-nested tuple:
after `n` observations the state has type `NestedTuple α n`, and adjoining a
fresh observation produces a pair `NestedTuple α n × α`.

At stage `n`, a statistic may depend on the whole past and on the fresh
observation.  If, for almost every past, its pushforward law under the fresh
observation is the same fixed measure `ν n`, then all stage statistics have
the product law.  The proof is an induction using mathlib's rigorously proved
`MeasurePreserving.skew_product` theorem (a Fubini/Tonelli argument).

This is exactly the abstract step that converts the fixed-subspace Beta law
for one fresh Gaussian column into mutual independence of all successive
Gram--Schmidt factors.

Mathematical provenance: Rouault (2005), proof of Proposition 2.1, printed
p. 6, concludes independence because the fixed-past law does not depend on
the past.  This file formalizes that argument using mathlib's
`MeasurePreserving.skew_product` theorem.  The abstract finite-horizon wrapper
is proof infrastructure, not a claim of a new probability theorem.  See
`PROVENANCE.md`.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory

universe u v

/-- Right-nested tuples, convenient for exposing the newest observation as a
Cartesian-product coordinate. -/
abbrev NestedTuple (α : Type u) : ℕ → Type u
  | 0 => ULift.{u, 0} Unit
  | n + 1 => NestedTuple α n × α

/-- Product measurable structure on a right-nested tuple.  This is defined
recursively because the tuple length is itself an index. -/
instance instMeasurableSpaceNestedTuple {α : Type u} [MeasurableSpace α] :
    (n : ℕ) → MeasurableSpace (NestedTuple α n)
  | 0 => ⊤
  | n + 1 => @Prod.instMeasurableSpace (NestedTuple α n) α
      (instMeasurableSpaceNestedTuple n) inferInstance

/-- The corresponding iterated product measure. -/
def nestedProductMeasure {α : Type u} [MeasurableSpace α]
  (μ : Measure α) : (n : ℕ) → Measure (NestedTuple α n)
  | 0 => Measure.dirac (ULift.up Unit.unit)
  | n + 1 => (nestedProductMeasure μ n).prod μ

/-- An iterated product whose `n`th coordinate has law `ν n`. -/
def nestedProductMeasureFamily {β : Type v} [MeasurableSpace β]
  (ν : ℕ → Measure β) : (n : ℕ) → Measure (NestedTuple β n)
  | 0 => Measure.dirac (ULift.up Unit.unit)
  | n + 1 => (nestedProductMeasureFamily ν n).prod (ν n)

instance nestedProductMeasure_sFinite {α : Type u} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (n : ℕ) :
    SFinite (nestedProductMeasure μ n) := by
  induction n with
  | zero =>
      simp only [nestedProductMeasure]
      let _ : SigmaFinite (Measure.dirac (ULift.up Unit.unit) :
          Measure (NestedTuple α 0)) := Measure.dirac.instSigmaFinite
      infer_instance
  | succ n ih =>
      let _ : SFinite (nestedProductMeasure μ n) := ih
      simp only [nestedProductMeasure]
      infer_instance

instance nestedProductMeasureFamily_sFinite {β : Type v} [MeasurableSpace β]
    (ν : ℕ → Measure β) [hν : ∀ n, SFinite (ν n)] (n : ℕ) :
    SFinite (nestedProductMeasureFamily ν n) := by
  induction n with
  | zero =>
      simp only [nestedProductMeasureFamily]
      let _ : SigmaFinite (Measure.dirac (ULift.up Unit.unit) :
          Measure (NestedTuple β 0)) := Measure.dirac.instSigmaFinite
      infer_instance
  | succ n ih =>
      let _ : SFinite (nestedProductMeasureFamily ν n) := ih
      let _ : SFinite (ν n) := hν n
      simp only [nestedProductMeasureFamily]
      infer_instance

/-- Apply the stage-`n` statistic to the old state and its newest observation,
recursively retaining all earlier stage statistics. -/
def sequentialStatistic {α : Type u} {β : Type v}
    (g : ∀ n, NestedTuple α n → α → β) :
  ∀ n, NestedTuple α n → NestedTuple β n
  | 0, _ => ULift.up Unit.unit
  | n + 1, z => (sequentialStatistic g n z.1, g n z.1 z.2)

/-- Read a right-nested tuple as an ordinary `Fin n`-indexed family. -/
def nestedTupleToFin {α : Type u} :
    (n : ℕ) → NestedTuple α n → Fin n → α
  | 0, _ => Fin.elim0
  | n + 1, z => Fin.snoc (nestedTupleToFin n z.1) z.2

/-- Jointly append a newest point to the family represented by a nested
tuple. -/
def nestedSnocFamily {α : Type u} (n : ℕ) :
    NestedTuple α n × α → Fin (n + 1) → α :=
  fun z ↦ Fin.snoc (nestedTupleToFin n z.1) z.2

theorem measurable_nestedTupleToFin_apply
    {α : Type u} [MeasurableSpace α] :
    ∀ (n : ℕ) (i : Fin n),
      Measurable (fun z : NestedTuple α n ↦ nestedTupleToFin n z i) := by
  intro n
  induction n with
  | zero => exact fun i ↦ Fin.elim0 i
  | succ n ih =>
      intro i
      have hms : instMeasurableSpaceNestedTuple (α := α) (n + 1) =
          @Prod.instMeasurableSpace (NestedTuple α n) α
            (instMeasurableSpaceNestedTuple n) inferInstance := rfl
      rw [hms]
      refine Fin.lastCases (by simpa [nestedTupleToFin] using
        (measurable_snd : Measurable (Prod.snd : NestedTuple α n × α → α)))
        (fun j ↦ ?_) i
      simp only [nestedTupleToFin, Fin.snoc_castSucc]
      simpa only [Function.comp_def] using
        (ih j).comp (measurable_fst :
          Measurable (Prod.fst : NestedTuple α n × α → NestedTuple α n))

/-- The conversion from nested tuples to finite families is measurable. -/
theorem measurable_nestedTupleToFin
    {α : Type u} [MeasurableSpace α] (n : ℕ) :
    Measurable (nestedTupleToFin (α := α) n) :=
  measurable_pi_lambda _ (measurable_nestedTupleToFin_apply n)

/-- Appending a newest observation to a nested family is jointly measurable. -/
theorem measurable_nestedSnocFamily
    {α : Type u} [MeasurableSpace α] (n : ℕ) :
    Measurable (nestedSnocFamily (α := α) n) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  refine Fin.lastCases (by simpa [nestedSnocFamily] using
    (measurable_snd : Measurable (Prod.snd : NestedTuple α n × α → α)))
    (fun j ↦ ?_) i
  simp only [nestedSnocFamily, Fin.snoc_castSucc]
  simpa only [Function.comp_def] using
    (measurable_nestedTupleToFin_apply n j).comp
      (measurable_fst : Measurable
        (Prod.fst : NestedTuple α n × α → NestedTuple α n))

/-- Joint measurability of every one-step statistic implies measurability of
the whole sequential statistic. -/
theorem measurable_sequentialStatistic {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    (g : ∀ n, NestedTuple α n → α → β)
    (hg : ∀ n, Measurable (Function.uncurry (g n))) :
    ∀ n, Measurable (sequentialStatistic g n) := by
  intro n
  induction n with
  | zero =>
      exact measurable_const
  | succ n ih =>
      exact (ih.comp measurable_fst).prodMk (hg n)

/-- **Sequential product-law theorem.**  Suppose that, conditional on almost
every past, the newest statistic has the same law `ν n`.  Then the vector of
all successive statistics has the iterated product law, hence its coordinates
are mutually independent with their prescribed marginals.

No regular conditional probability is assumed: the hypothesis is the direct
pushforward identity for the fresh coordinate, and the proof uses the product
measure/Fubini theorem packaged as `MeasurePreserving.skew_product`. -/
theorem measurePreserving_sequentialStatistic
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : ℕ → Measure β)
    [∀ n, SFinite (ν n)]
    (g : ∀ n, NestedTuple α n → α → β)
    (hg : ∀ n, Measurable (Function.uncurry (g n)))
    (hlaw : ∀ n, ∀ᵐ past ∂nestedProductMeasure μ n,
      Measure.map (g n past) μ = ν n) :
    ∀ n, MeasurePreserving (sequentialStatistic g n)
      (nestedProductMeasure μ n) (nestedProductMeasureFamily ν n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨measurable_const, ?_⟩
      rw [nestedProductMeasure, nestedProductMeasureFamily]
      simp only [sequentialStatistic]
      rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
      simpa only [sequentialStatistic, nestedProductMeasure,
        nestedProductMeasureFamily] using
        ih.skew_product (hg n) (hlaw n)

/-- Pushforward formulation of `measurePreserving_sequentialStatistic`.
This is often the most convenient statement when the goal is equality in
distribution. -/
theorem map_sequentialStatistic_eq_nestedProduct
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : ℕ → Measure β)
    [∀ n, SFinite (ν n)]
    (g : ∀ n, NestedTuple α n → α → β)
    (hg : ∀ n, Measurable (Function.uncurry (g n)))
    (hlaw : ∀ n, ∀ᵐ past ∂nestedProductMeasure μ n,
      Measure.map (g n past) μ = ν n) (n : ℕ) :
    Measure.map (sequentialStatistic g n) (nestedProductMeasure μ n) =
      nestedProductMeasureFamily ν n :=
  (measurePreserving_sequentialStatistic μ ν g hg hlaw n).map_eq

/-- Finite-horizon form of the sequential product-law theorem.  It requires
the one-step law only at stages actually used before `p`; this is essential in
the Gaussian application, where at most `m` independent columns exist in an
`m`-dimensional residual space. -/
theorem measurePreserving_sequentialStatistic_of_lt
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : ℕ → Measure β)
    [∀ n, SFinite (ν n)]
    (g : ∀ n, NestedTuple α n → α → β)
    (hg : ∀ n, Measurable (Function.uncurry (g n))) :
    ∀ p : ℕ,
      (∀ n, n < p → ∀ᵐ past ∂nestedProductMeasure μ n,
        Measure.map (g n past) μ = ν n) →
      MeasurePreserving (sequentialStatistic g p)
        (nestedProductMeasure μ p) (nestedProductMeasureFamily ν p) := by
  intro p
  induction p with
  | zero =>
      intro hlaw
      refine ⟨measurable_const, ?_⟩
      rw [nestedProductMeasure, nestedProductMeasureFamily]
      simp only [sequentialStatistic]
      rw [Measure.map_dirac' measurable_const]
  | succ p ih =>
      intro hlaw
      have hpast := ih (fun n hn ↦ hlaw n (Nat.lt_succ_of_lt hn))
      simpa only [sequentialStatistic, nestedProductMeasure,
        nestedProductMeasureFamily] using
        hpast.skew_product (hg p) (hlaw p (Nat.lt_add_one p))

/-- Pushforward equality corresponding to the finite-horizon theorem. -/
theorem map_sequentialStatistic_eq_nestedProduct_of_lt
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : ℕ → Measure β)
    [∀ n, SFinite (ν n)]
    (g : ∀ n, NestedTuple α n → α → β)
    (hg : ∀ n, Measurable (Function.uncurry (g n))) (p : ℕ)
    (hlaw : ∀ n, n < p → ∀ᵐ past ∂nestedProductMeasure μ n,
      Measure.map (g n past) μ = ν n) :
    Measure.map (sequentialStatistic g p) (nestedProductMeasure μ p) =
      nestedProductMeasureFamily ν p :=
  (measurePreserving_sequentialStatistic_of_lt μ ν g hg p hlaw).map_eq

/-! ## The normalized Gram-determinant statistic -/

open Matrix Module InnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normalized leading Gram determinant of a nested family. -/
def nestedNormalizedGramDet (n : ℕ) (z : NestedTuple E n) : ℝ :=
  (normalizedGram (nestedTupleToFin n z)).det

/-- The newest determinant ratio.  On the linearly-independent event this is
the newest squared Gram--Schmidt residual divided by the squared column norm.
Using determinant ratios makes global measurability transparent, including on
the null singular set. -/
def nestedNormalizedGramFactor (n : ℕ) (past : NestedTuple E n) (x : E) : ℝ :=
  nestedNormalizedGramDet (n + 1) (past, x) /
    nestedNormalizedGramDet n past

/-- Gram--Schmidt at an old index is unaffected by appending a new last
column. -/
theorem gramSchmidt_snoc_castSucc {n : ℕ}
    (v : Fin n → E) (x : E) (i : Fin n) :
    gramSchmidt ℝ (Fin.snoc v x) i.castSucc = gramSchmidt ℝ v i := by
  induction i using (wellFounded_lt (α := Fin n)).induction with
  | h i ih =>
      rw [gramSchmidt_def, gramSchmidt_def, Fin.snoc_castSucc]
      rw [← Fin.map_castSuccEmb_Iio]
      simp only [Finset.sum_map]
      apply congrArg (fun z ↦ v i - z)
      apply Finset.sum_congr rfl
      intro j hj
      change (ℝ ∙ gramSchmidt ℝ (Fin.snoc v x) j.castSucc).starProjection (v i) = _
      rw [ih j (Finset.mem_Iio.mp hj)]

/-- On the linearly-independent event, a normalized-Gram determinant ratio
is exactly the newest normalized Gram--Schmidt residual factor. -/
theorem normalizedGram_det_ratio_eq_gramSchmidt_last_ratio {n : ℕ}
    (v : Fin n → E) (x : E)
    (hfull : LinearIndependent ℝ (Fin.snoc v x)) :
    (normalizedGram (Fin.snoc v x)).det / (normalizedGram v).det =
      ‖gramSchmidt ℝ (Fin.snoc v x) (Fin.last n)‖ ^ 2 / ‖x‖ ^ 2 := by
  have hpast : LinearIndependent ℝ v := (linearIndependent_finSnoc.mp hfull).1
  have hden : (normalizedGram v).det ≠ 0 := by
    rw [det_normalizedGram]
    apply div_ne_zero
    · exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hpast
    · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
        pow_ne_zero 2 (norm_ne_zero_iff.mpr (hpast.ne_zero i))
  rw [det_normalizedGram_eq_prod_gramSchmidt_ratio _ hfull,
    det_normalizedGram_eq_prod_gramSchmidt_ratio _ hpast,
    Fin.prod_univ_castSucc]
  simp_rw [gramSchmidt_snoc_castSucc, Fin.snoc_castSucc]
  simp only [Fin.snoc_last]
  have hprod : (∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 / ‖v i‖ ^ 2) ≠ 0 := by
    rw [← det_normalizedGram_eq_prod_gramSchmidt_ratio v hpast]
    exact hden
  have hx : x ≠ 0 := by
    have hx' := hfull.ne_zero (Fin.last n)
    simpa using hx'
  have hnormx : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  field_simp [hprod, hnormx]

/-- Fixed-past geometric form of the newest determinant factor. -/
theorem nestedNormalizedGramFactor_eq_orthogonalProjection
    [FiniteDimensional ℝ E] {n : ℕ} (past : NestedTuple E n) (x : E)
    (hfull : LinearIndependent ℝ
      (Fin.snoc (nestedTupleToFin n past) x)) :
    nestedNormalizedGramFactor n past x =
      ‖(gramSchmidtPastSpan
          (Fin.snoc (nestedTupleToFin n past) x))ᗮ.orthogonalProjectionOnto x‖ ^ 2 /
        ‖x‖ ^ 2 := by
  simp only [nestedNormalizedGramFactor, nestedNormalizedGramDet, nestedTupleToFin]
  rw [normalizedGram_det_ratio_eq_gramSchmidt_last_ratio _ _ hfull]
  rw [norm_gramSchmidt_last_eq_norm_orthogonalProjectionOnto]
  simp only [Fin.snoc_last]

/-- The determinant of a normalized Gram matrix is a measurable function of
its columns. -/
theorem measurable_det_normalizedGram [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (n : ℕ) :
    Measurable (fun v : Fin n → E ↦ (normalizedGram v).det) := by
  rw [show (fun v : Fin n → E ↦ (normalizedGram v).det) =
      fun v ↦ (Matrix.gram ℝ v).det / ∏ i, ‖v i‖ ^ 2 by
    funext v
    exact det_normalizedGram v]
  have hgram : Continuous (fun v : Fin n → E ↦ Matrix.gram ℝ v) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simpa [Matrix.gram] using (continuous_apply i).inner (continuous_apply j)
  exact hgram.matrix_det.measurable.div (by fun_prop)

/-- The newest normalized-Gram determinant ratio is jointly measurable in
the past and the fresh column. -/
theorem measurable_uncurry_nestedNormalizedGramFactor
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (n : ℕ) :
    Measurable (Function.uncurry (nestedNormalizedGramFactor (E := E) n)) := by
  have hnum := (measurable_det_normalizedGram (E := E) (n + 1)).comp
    (measurable_nestedSnocFamily (α := E) n)
  have hpast : Measurable
      (fun z : NestedTuple E n × E ↦ nestedTupleToFin n z.1) := by
    simpa only [Function.comp_def] using
      (measurable_nestedTupleToFin (α := E) n).comp
        (measurable_fst : Measurable
          (Prod.fst : NestedTuple E n × E → NestedTuple E n))
  have hden := (measurable_det_normalizedGram (E := E) n).comp hpast
  exact hnum.div hden

/-- Linear independence makes a normalized Gram determinant nonzero. -/
theorem det_normalizedGram_ne_zero_of_linearIndependent
    {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v) :
    (normalizedGram v).det ≠ 0 := by
  rw [det_normalizedGram]
  apply div_ne_zero
  · exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv.ne_zero i))

/-- Multiply all entries in a nested real tuple. -/
def nestedRealProduct : (n : ℕ) → NestedTuple ℝ n → ℝ
  | 0, _ => 1
  | n + 1, z => nestedRealProduct n z.1 * z.2

/-- Multiplication of the coordinates of a nested real tuple is measurable. -/
theorem measurable_nestedRealProduct :
    ∀ n : ℕ, Measurable (nestedRealProduct n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hms : instMeasurableSpaceNestedTuple (α := ℝ) (n + 1) =
          @Prod.instMeasurableSpace (NestedTuple ℝ n) ℝ
            (instMeasurableSpaceNestedTuple n) inferInstance := rfl
      rw [hms]
      exact (ih.comp measurable_fst).mul measurable_snd

/-- Telescoping the successive determinant ratios returns the final normalized
Gram determinant.  Thus the sequential statistic below is exactly the
factorization of the correlation determinant, not merely an auxiliary vector
with the right marginal laws. -/
theorem nestedRealProduct_sequentialGramFactor_eq_det :
    ∀ (n : ℕ) (z : NestedTuple E n),
      LinearIndependent ℝ (nestedTupleToFin n z) →
      nestedRealProduct n
          (sequentialStatistic (nestedNormalizedGramFactor (E := E)) n z) =
        nestedNormalizedGramDet n z := by
  intro n
  induction n with
  | zero =>
      intro z hz
      simp [nestedRealProduct, nestedNormalizedGramDet,
        nestedTupleToFin, normalizedGram, Matrix.gram]
  | succ n ih =>
      rintro ⟨past, x⟩ hfull
      have hpast : LinearIndependent ℝ (nestedTupleToFin n past) :=
        (linearIndependent_finSnoc.mp hfull).1
      have hdet : nestedNormalizedGramDet n past ≠ 0 := by
        exact det_normalizedGram_ne_zero_of_linearIndependent
          (nestedTupleToFin n past) hpast
      rw [sequentialStatistic, nestedRealProduct,
        nestedNormalizedGramFactor, ih past hpast]
      field_simp

/-! ## The exact Beta specialization -/

/-- Law of the `n`th sequential determinant factor in an `m`-dimensional
Gaussian residual space.  The first factor (`n=0`, the first column) is
deterministically one.  For `n≥1` it is Beta with residual dimension `m-n`
and past dimension `n`. -/
def gaussianGramSchmidtFactorMeasure (m : ℕ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 1
  | n + 1 => betaMeasure (((m - (n + 1) : ℕ) : ℝ) / 2)
      (((n + 1 : ℕ) : ℝ) / 2)

instance gaussianGramSchmidtFactorMeasure_sFinite (m n : ℕ) :
    SFinite (gaussianGramSchmidtFactorMeasure m n) := by
  cases n with
  | zero =>
      unfold gaussianGramSchmidtFactorMeasure
      let _ : SigmaFinite (Measure.dirac (1 : ℝ)) :=
        Measure.dirac.instSigmaFinite
      infer_instance
  | succ n =>
      unfold gaussianGramSchmidtFactorMeasure betaMeasure
      infer_instance

@[simp] theorem gaussianGramSchmidtFactorMeasure_succ (m n : ℕ) :
    gaussianGramSchmidtFactorMeasure m (n + 1) =
      betaMeasure (((m - (n + 1) : ℕ) : ℝ) / 2)
        (((n + 1 : ℕ) : ℝ) / 2) := rfl

/-- A nested tuple of at most `finrank E` independent standard Gaussian
columns is linearly independent almost surely.  This is the nested-product
counterpart of `ae_linearIndependent_pi_stdGaussian`, proved directly by the
same fresh-column induction. -/
theorem ae_linearIndependent_nested_stdGaussian
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∀ (n : ℕ), n ≤ finrank ℝ E →
      ∀ᵐ z ∂nestedProductMeasure (stdGaussian E) n,
        LinearIndependent ℝ (nestedTupleToFin n z) := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact Filter.Eventually.of_forall fun _ ↦ linearIndependent_empty_type
  | succ n ih =>
      intro hn
      have hnlt : n < finrank ℝ E := Nat.lt_of_succ_le hn
      have hpast := ih (Nat.le_of_lt hnlt)
      have hset : MeasurableSet
          {z : NestedTuple E n × E |
            LinearIndependent ℝ (nestedSnocFamily n z)} :=
        (measurableSet_linearlyIndependentTuples (E := E) (n + 1)).preimage
          (measurable_nestedSnocFamily (α := E) n)
      have hprod :
          ∀ᵐ z ∂((nestedProductMeasure (stdGaussian E) n).prod (stdGaussian E)),
            LinearIndependent ℝ (nestedSnocFamily n z) := by
        rw [Measure.ae_prod_iff_ae_ae hset]
        filter_upwards [hpast] with past hpastLI
        have hfresh := ae_linearIndependent_snoc_stdGaussian hpastLI hnlt
        simpa [nestedSnocFamily] using hfresh
      simpa [nestedProductMeasure, nestedSnocFamily, nestedTupleToFin] using hprod

/-- If the one-fresh-column determinant ratio has its asserted fixed-past
law for every linearly independent past, then the actual sequential Gaussian
ratios have the full independent product law.  Almost-sure linear independence
discharges the exceptional singular pasts automatically. -/
theorem map_sequentialNormalizedGramFactors_eq_betaProduct_of_fixedPast
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m p : ℕ) (hdim : finrank ℝ E = m) (hp : p ≤ m)
    (hfixed : ∀ (n : ℕ) (past : NestedTuple E n),
      LinearIndependent ℝ (nestedTupleToFin n past) → n < m →
        Measure.map (nestedNormalizedGramFactor (E := E) n past)
            (stdGaussian E) = gaussianGramSchmidtFactorMeasure m n) :
    Measure.map
        (sequentialStatistic (nestedNormalizedGramFactor (E := E)) p)
        (nestedProductMeasure (stdGaussian E) p) =
      nestedProductMeasureFamily (gaussianGramSchmidtFactorMeasure m) p := by
  apply map_sequentialStatistic_eq_nestedProduct_of_lt
    (stdGaussian E) (gaussianGramSchmidtFactorMeasure m)
    (nestedNormalizedGramFactor (E := E))
    measurable_uncurry_nestedNormalizedGramFactor p
  intro n hnp
  have hnm : n < m := lt_of_lt_of_le hnp hp
  have hnrank : n ≤ finrank ℝ E := by omega
  filter_upwards [ae_linearIndependent_nested_stdGaussian n hnrank] with past hpast
  exact hfixed n past hpast hnm

/-- **Scalar determinant product law.**  Under the same fixed-past input, the
pushforward law of the normalized Gram determinant is the pushforward of
multiplication under the independent factor-product measure.  This is the
formal scalar statement corresponding to Rouault's Beta-product identity. -/
theorem map_nestedNormalizedGramDet_eq_map_product_betaFactors
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m p : ℕ) (hdim : finrank ℝ E = m) (hp : p ≤ m)
    (hfixed : ∀ (n : ℕ) (past : NestedTuple E n),
      LinearIndependent ℝ (nestedTupleToFin n past) → n < m →
        Measure.map (nestedNormalizedGramFactor (E := E) n past)
            (stdGaussian E) = gaussianGramSchmidtFactorMeasure m n) :
    Measure.map (nestedNormalizedGramDet (E := E) p)
        (nestedProductMeasure (stdGaussian E) p) =
      Measure.map (nestedRealProduct p)
        (nestedProductMeasureFamily (gaussianGramSchmidtFactorMeasure m) p) := by
  let seq : NestedTuple E p → NestedTuple ℝ p :=
    sequentialStatistic (nestedNormalizedGramFactor (E := E)) p
  have hseq : Measurable seq :=
    measurable_sequentialStatistic
      (nestedNormalizedGramFactor (E := E))
      measurable_uncurry_nestedNormalizedGramFactor p
  have hvec := map_sequentialNormalizedGramFactors_eq_betaProduct_of_fixedPast
    (E := E) m p hdim hp hfixed
  have hdetprod : nestedNormalizedGramDet (E := E) p =ᵐ[
      nestedProductMeasure (stdGaussian E) p]
      (nestedRealProduct p ∘ seq) := by
    have hprank : p ≤ finrank ℝ E := by omega
    filter_upwards [ae_linearIndependent_nested_stdGaussian p hprank] with z hz
    exact (nestedRealProduct_sequentialGramFactor_eq_det p z hz).symm
  calc
    Measure.map (nestedNormalizedGramDet (E := E) p)
        (nestedProductMeasure (stdGaussian E) p) =
        Measure.map (nestedRealProduct p ∘ seq)
          (nestedProductMeasure (stdGaussian E) p) :=
      Measure.map_congr hdetprod
    _ = Measure.map (nestedRealProduct p)
          (Measure.map seq (nestedProductMeasure (stdGaussian E) p)) :=
      (Measure.map_map (measurable_nestedRealProduct p) hseq).symm
    _ = Measure.map (nestedRealProduct p)
          (nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p) := by
      rw [show Measure.map seq (nestedProductMeasure (stdGaussian E) p) =
          nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p from hvec]

/-- Concrete sequential independence transfer for normalized Gram determinant
ratios.  Its sole probabilistic input is the one-fresh-column pushforward
identity `hlaw`; joint measurability and the entire independence induction are
proved here. -/
theorem map_sequentialNormalizedGramFactors_eq_betaProduct
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (μ : Measure E) [SFinite μ]
    (hlaw : ∀ n, ∀ᵐ past ∂nestedProductMeasure μ n,
      Measure.map (nestedNormalizedGramFactor (E := E) n past) μ =
        gaussianGramSchmidtFactorMeasure m n)
    (p : ℕ) :
    Measure.map
        (sequentialStatistic (nestedNormalizedGramFactor (E := E)) p)
        (nestedProductMeasure μ p) =
      nestedProductMeasureFamily (gaussianGramSchmidtFactorMeasure m) p := by
  exact map_sequentialStatistic_eq_nestedProduct μ
    (gaussianGramSchmidtFactorMeasure m)
    (nestedNormalizedGramFactor (E := E))
    measurable_uncurry_nestedNormalizedGramFactor hlaw p

end

end LogdetLean
