import LogdetLean.GaussianSubspace
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianDisk
import LogdetLean.GramHafnian.CircularGaussianVectorWick
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Almost-sure complex full column rank

The generic Gaussian rank result in `GaussianLinearIndependence` is over the
real scalar field.  Hafnian cofactors require injectivity over `ℂ`.  This
module repeats the short sequential argument for complex spans, viewed as
proper real subspaces when applying the standard-Gaussian null-set theorem,
and then transports it to the paper's circular normalization.
-/

open MeasureTheory ProbabilityTheory Matrix Module Set

namespace LogdetLean.GramHafnian

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [IsScalarTower ℝ ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Complex linear independence is Borel measurable for every finite index
type. -/
theorem measurableSet_complexLinearlyIndependentFamilies
    {ι : Type*} [Fintype ι] :
    MeasurableSet {v : ι → E | LinearIndependent ℂ v} := by
  classical
  have hdet : Measurable (fun v : ι → E ↦ (Matrix.gram ℂ v).det) := by
    have hgram : Continuous (fun v : ι → E ↦ Matrix.gram ℂ v) := by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      simpa [Matrix.gram] using (continuous_apply i).inner (continuous_apply j)
    exact hgram.matrix_det.measurable
  have heq : {v : ι → E | LinearIndependent ℂ v} =
      {v | (Matrix.gram ℂ v).det ≠ 0} := by
    ext v
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.symm
  rw [heq]
  exact (hdet.eq_const 0).setOf.compl

/-- Complex linear independence of a finite tuple is Borel measurable. -/
theorem measurableSet_complexLinearlyIndependentTuples (n : ℕ) :
    MeasurableSet {v : Fin n → E | LinearIndependent ℂ v} := by
  exact measurableSet_complexLinearlyIndependentFamilies

/-- A complex span of fewer independent vectors than the complex ambient
dimension is a proper real subspace as well. -/
theorem complexSpan_restrictScalars_ne_top
    {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℂ v)
    (hn : n < finrank ℂ E) :
    (Submodule.span ℂ (Set.range v)).restrictScalars ℝ ≠ ⊤ := by
  let S : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  have hS : S ≠ ⊤ := by
    intro htop
    have hfin : finrank ℂ S = n := by
      simpa [S] using finrank_span_eq_card hv
    have hall : finrank ℂ S = finrank ℂ E := by
      rw [htop, finrank_top]
    omega
  intro hreal
  apply hS
  apply top_unique
  intro x _hx
  have hxR : x ∈ S.restrictScalars ℝ := by
    rw [hreal]
    trivial
  exact hxR

/-- A fresh real-standard Gaussian vector escapes the complex span of a
fixed independent past almost surely. -/
theorem ae_complexLinearIndependent_snoc_stdGaussian
    {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℂ v)
    (hn : n < finrank ℂ E) :
    ∀ᵐ x ∂(stdGaussian E), LinearIndependent ℂ (Fin.snoc v x) := by
  rw [ae_iff]
  let S : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  have hproper : S.restrictScalars ℝ ≠ ⊤ := by
    exact complexSpan_restrictScalars_ne_top hv hn
  have hnull := LogdetLean.stdGaussian_proper_submodule_null
    (S.restrictScalars ℝ) hproper
  have hbad : {x : E | ¬ LinearIndependent ℂ (Fin.snoc v x)} =
      (S : Set E) := by
    ext x
    simp [linearIndependent_finSnoc, hv, S]
  rw [hbad]
  exact hnull

/-- At most the complex dimension many iid real-standard Gaussian vectors
are complex-linearly independent almost surely. -/
theorem ae_complexLinearIndependent_pi_stdGaussian
    (n : ℕ) (hn : n ≤ finrank ℂ E) :
    ∀ᵐ v ∂(Measure.pi fun _ : Fin n ↦ stdGaussian E),
      LinearIndependent ℂ v := by
  induction n with
  | zero =>
      exact Filter.Eventually.of_forall fun _ ↦ linearIndependent_empty_type
  | succ n ih =>
      have hnlt : n < finrank ℂ E := Nat.lt_of_succ_le hn
      have hpast :
          ∀ᵐ v ∂(Measure.pi fun _ : Fin n ↦ stdGaussian E),
            LinearIndependent ℂ v := ih (Nat.le_of_lt hnlt)
      have hsnocMeas : Measurable (fun z : (Fin n → E) × E ↦
          @Fin.snoc n (fun _ : Fin (n + 1) ↦ E) z.1 z.2) := by
        fun_prop
      have hset : MeasurableSet
          {z : (Fin n → E) × E | LinearIndependent ℂ
            (@Fin.snoc n (fun _ : Fin (n + 1) ↦ E) z.1 z.2)} := by
        exact (measurableSet_complexLinearlyIndependentTuples
          (E := E) (n + 1)).preimage hsnocMeas
      have hprod :
          ∀ᵐ z ∂((Measure.pi fun _ : Fin n ↦ stdGaussian E).prod (stdGaussian E)),
            LinearIndependent ℂ
              (@Fin.snoc n (fun _ : Fin (n + 1) ↦ E) z.1 z.2) := by
        rw [Measure.ae_prod_iff_ae_ae hset]
        filter_upwards [hpast] with v hv
        exact ae_complexLinearIndependent_snoc_stdGaussian hv hnlt
      let split : (Fin (n + 1) → E) → (Fin n → E) × E :=
        fun v ↦ (Fin.init v, v (Fin.last n))
      have hsplit : MeasurePreserving split
          (Measure.pi fun _ : Fin (n + 1) ↦ stdGaussian E)
          ((Measure.pi fun _ : Fin n ↦ stdGaussian E).prod (stdGaussian E)) := by
        have hfirst := measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ stdGaussian E) (Fin.last n)
        have hcomp := (Measure.measurePreserving_swap).comp hfirst
        simpa [split, Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply,
          Fin.succAbove_last] using hcomp
      have hmapped :
          ∀ᵐ z ∂Measure.map split
              (Measure.pi fun _ : Fin (n + 1) ↦ stdGaussian E),
            LinearIndependent ℂ
              (@Fin.snoc n (fun _ : Fin (n + 1) ↦ E) z.1 z.2) := by
        rw [hsplit.map_eq]
        exact hprod
      have hcomp :
          ∀ᵐ v ∂(Measure.pi fun _ : Fin (n + 1) ↦ stdGaussian E),
            LinearIndependent ℂ (Fin.snoc (Fin.init v) (v (Fin.last n))) :=
        (ae_map_iff hsplit.measurable.aemeasurable hset).mp hmapped
      filter_upwards [hcomp] with v hv
      simpa using hv

/-- Nonzero common real scaling preserves complex linear independence. -/
theorem complexLinearIndependent_const_smul
    {ι : Type*} {v : ι → E} (hv : LinearIndependent ℂ v)
    {c : ℝ} (hc : c ≠ 0) :
    LinearIndependent ℂ (fun i ↦ c • v i) := by
  let f : E →ₗ[ℂ] E := (c : ℂ) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    change (c : ℂ) • x = (c : ℂ) • y at hxy
    exact smul_right_injective E (by exact_mod_cast hc) hxy
  have hmap := hv.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hfun : (f ∘ v) = fun i ↦ c • v i := by
    funext i
    change (c : ℂ) • v i = c • v i
    exact algebraMap_smul ℂ c (v i)
  rwa [hfun] at hmap

/-- The scaled standard-Gaussian product appearing in the circular
normalization is complex full rank almost surely. -/
theorem ae_complexLinearIndependent_pi_scaledStdGaussian
    (k n : ℕ) (hn : n ≤ k) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n ↦
        (stdGaussian (CircularEuclideanSpace k)).map
          (fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • x)),
      LinearIndependent ℂ v := by
  let E := CircularEuclideanSpace k
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hdim : finrank ℂ E = k := by simp [E, CircularEuclideanSpace]
  have hbase : ∀ᵐ v ∂Measure.pi (fun _ : Fin n ↦ stdGaussian E),
      LinearIndependent ℂ v := by
    apply ae_complexLinearIndependent_pi_stdGaussian
    simpa [hdim] using hn
  let scale : (Fin n → E) → (Fin n → E) := fun v i ↦ c • v i
  have hmp : MeasurePreserving scale
      (Measure.pi fun _ : Fin n ↦ stdGaussian E)
      (Measure.pi fun _ : Fin n ↦
        (stdGaussian E).map (fun x ↦ c • x)) := by
    apply measurePreserving_pi
    intro i
    exact ⟨by fun_prop, rfl⟩
  have hset : MeasurableSet {v : Fin n → E | LinearIndependent ℂ v} :=
    measurableSet_complexLinearlyIndependentTuples n
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable hset).2
  filter_upwards [hbase] with v hv
  exact complexLinearIndependent_const_smul hv hc

/-- Literal iid circular complex columns are complex full rank almost
surely whenever their number does not exceed the row dimension. -/
theorem ae_complexLinearIndependent_pi_circularGaussianVectors
    (k n : ℕ) (hn : n ≤ k) :
    ∀ᵐ A ∂Measure.pi (fun _ : Fin n ↦ circularGaussianVector k),
      LinearIndependent ℂ
        (fun j ↦ WithLp.toLp 2 (A j) :
          Fin n → CircularEuclideanSpace k) := by
  let E := CircularEuclideanSpace k
  let target : Measure E :=
    (stdGaussian E).map (fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • x)
  have hcoord : MeasurePreserving (WithLp.toLp 2)
      (circularGaussianVector k) target := by
    refine ⟨by fun_prop, ?_⟩
    simpa [target, circularGaussianVector] using
      map_toLp_pi_circularGaussian_eq_scaled_stdGaussian k
  have hfamily : MeasurePreserving
      (fun A : Fin n → (Fin k → ℂ) =>
        (fun j ↦ WithLp.toLp 2 (A j) : Fin n → E))
      (Measure.pi fun _ : Fin n ↦ circularGaussianVector k)
      (Measure.pi fun _ : Fin n ↦ target) := by
    apply measurePreserving_pi
    intro j
    exact hcoord
  exact hfamily.quasiMeasurePreserving.ae
    (ae_complexLinearIndependent_pi_scaledStdGaussian k n hn)

/-- Arbitrary finite-index version, used for the odd cofactor subtype. -/
theorem ae_complexLinearIndependent_pi_circularGaussianVectors_fintype
    (k : ℕ) (ι : Type*) [Fintype ι]
    (hn : Fintype.card ι ≤ k) :
    ∀ᵐ A ∂Measure.pi (fun _ : ι ↦ circularGaussianVector k),
      LinearIndependent ℂ
        (fun j ↦ WithLp.toLp 2 (A j) :
          ι → CircularEuclideanSpace k) := by
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let reindex : (Fin n → (Fin k → ℂ)) ≃ᵐ (ι → (Fin k → ℂ)) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι ↦ Fin k → ℂ) e
  have hmp : MeasurePreserving reindex
      (Measure.pi fun _ : Fin n ↦ circularGaussianVector k)
      (Measure.pi fun _ : ι ↦ circularGaussianVector k) := by
    simpa [reindex] using
      (measurePreserving_piCongrLeft
        (fun _ : ι ↦ circularGaussianVector k) e)
  have hfin :
      ∀ᵐ A ∂Measure.pi (fun _ : Fin n ↦ circularGaussianVector k),
        LinearIndependent ℂ
          (fun j ↦ WithLp.toLp 2 (A j) :
            Fin n → CircularEuclideanSpace k) :=
    ae_complexLinearIndependent_pi_circularGaussianVectors k n hn
  have hset : MeasurableSet
      {A : ι → (Fin k → ℂ) |
        LinearIndependent ℂ
          (fun j ↦ WithLp.toLp 2 (A j) :
            ι → CircularEuclideanSpace k)} := by
    exact (measurableSet_complexLinearlyIndependentFamilies
      (E := CircularEuclideanSpace k) (ι := ι)).preimage (by fun_prop)
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable hset).2
  filter_upwards [hfin] with A hA
  apply (linearIndependent_equiv e).mp
  have hfun :
      ((fun j : ι ↦ WithLp.toLp 2 (reindex A j) :
          ι → CircularEuclideanSpace k) ∘ e) =
        (fun j : Fin n ↦ WithLp.toLp 2 (A j) :
          Fin n → CircularEuclideanSpace k) := by
    funext j
    have hj : reindex A (e j) = A j := by
      simpa [reindex] using
        (@MeasurableEquiv.piCongrLeft_apply_apply
          (Fin n) ι e (fun _ : ι ↦ Fin k → ℂ)
          (fun _ ↦ inferInstance) A j)
    exact congrArg (WithLp.toLp 2) hj
  rw [hfun]
  exact hA

end

end LogdetLean.GramHafnian
