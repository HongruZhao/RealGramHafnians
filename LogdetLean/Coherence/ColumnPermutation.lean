import LogdetLean.GaussianColumnProduct
import LogdetLean.SampleCorrelationBeta
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic
/-!
# Permuting Gaussian columns

The null model is exchangeable in its variable columns.  This file turns the
usual phrase "by relabeling the columns" into exact deterministic and
measure-theoretic statements.

The primary representation is a finite family `Fin p → E`.  A permutation
of `Fin p`

* preserves every iid finite product law;
* reindexes the normalized Gram matrix on both axes;
* preserves its determinant and log determinant; and
* transports a squared-correlation edge event to the relabeled edge.

At the end, these results are composed with the existing measure-preserving
map from right-nested tuples to finite families, including the centered
Gaussian sample model.
-/

namespace LogdetLean.Coherence

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Relabel a finite family by `σ`.  The new coordinate `σ i` contains the
old coordinate `i`. -/
def permuteColumns {p : ℕ} {E : Type*} (σ : Equiv.Perm (Fin p))
    (v : Fin p → E) : Fin p → E :=
  fun i ↦ v (σ.symm i)

@[simp]
theorem permuteColumns_apply {p : ℕ} {E : Type*}
    (σ : Equiv.Perm (Fin p)) (v : Fin p → E) (i : Fin p) :
    permuteColumns σ v i = v (σ.symm i) := rfl

@[simp]
theorem permuteColumns_apply_image {p : ℕ} {E : Type*}
    (σ : Equiv.Perm (Fin p)) (v : Fin p → E) (i : Fin p) :
    permuteColumns σ v (σ i) = v i := by
  simp [permuteColumns]

/-- Relabeling finitely many measurable coordinates is measurable. -/
theorem measurable_permuteColumns
    {p : ℕ} {E : Type*} [MeasurableSpace E]
    (σ : Equiv.Perm (Fin p)) :
    Measurable (permuteColumns (E := E) σ) := by
  unfold permuteColumns
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (σ.symm i)

/-- Every iid finite product measure is invariant under a permutation of its
coordinates.  This is the direct finite-family specialization of mathlib's
`measurePreserving_piCongrLeft`. -/
theorem measurePreserving_permuteColumns_pi
    {p : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (permuteColumns (E := E) σ)
      (Measure.pi fun _ : Fin p ↦ μ)
      (Measure.pi fun _ : Fin p ↦ μ) := by
  have hfun :
      permuteColumns (E := E) σ =
        (MeasurableEquiv.piCongrLeft (fun _ : Fin p ↦ E) σ :
          (Fin p → E) → (Fin p → E)) := by
    funext v
    ext i
    obtain ⟨j, rfl⟩ := σ.surjective i
    rw [permuteColumns_apply_image]
    exact (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin p ↦ E) σ v j).symm
  rw [hfun]
  simpa using
    (measurePreserving_piCongrLeft
      (α := fun _ : Fin p ↦ E) (fun _ : Fin p ↦ μ) σ)

/-- Pushforward form of iid column-permutation invariance. -/
theorem map_permuteColumns_pi
    {p : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (σ : Equiv.Perm (Fin p)) :
    Measure.map (permuteColumns (E := E) σ)
        (Measure.pi fun _ : Fin p ↦ μ) =
      Measure.pi fun _ : Fin p ↦ μ :=
  (measurePreserving_permuteColumns_pi μ σ).map_eq

/-- In particular, a finite family of independent standard Gaussian columns
is invariant under every column permutation. -/
theorem measurePreserving_permuteGaussianColumns
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (permuteColumns (E := E) σ)
      (Measure.pi fun _ : Fin p ↦ stdGaussian E)
      (Measure.pi fun _ : Fin p ↦ stdGaussian E) :=
  measurePreserving_permuteColumns_pi (stdGaussian E) σ

/-- Permuting a family reindexes its normalized Gram matrix by the same
permutation on rows and columns. -/
theorem normalizedGram_permuteColumns
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ : Equiv.Perm (Fin p)) (v : Fin p → E) :
    normalizedGram (permuteColumns σ v) =
      Matrix.reindex σ σ (normalizedGram v) := by
  ext i j
  simp [permuteColumns, normalizedGram, Matrix.gram_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Entrywise form of the normalized-Gram reindexing identity. -/
@[simp]
theorem normalizedGram_permuteColumns_apply_image
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ : Equiv.Perm (Fin p)) (v : Fin p → E) (i j : Fin p) :
    normalizedGram (permuteColumns σ v) (σ i) (σ j) =
      normalizedGram v i j := by
  rw [normalizedGram_permuteColumns]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Simultaneous row-and-column relabeling preserves the normalized-Gram
determinant. -/
theorem det_normalizedGram_permuteColumns
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ : Equiv.Perm (Fin p)) (v : Fin p → E) :
    (normalizedGram (permuteColumns σ v)).det =
      (normalizedGram v).det := by
  rw [normalizedGram_permuteColumns, Matrix.det_reindex_self]

/-- The log determinant is invariant under column relabeling, including at
singular matrices because the real logarithm is a total function. -/
theorem log_det_normalizedGram_permuteColumns
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ : Equiv.Perm (Fin p)) (v : Fin p → E) :
    Real.log (normalizedGram (permuteColumns σ v)).det =
      Real.log (normalizedGram v).det := by
  rw [det_normalizedGram_permuteColumns]

/-- The strict squared-correlation event attached to one ordered pair.  No
off-diagonal assumption is built into this definition, so it can also be
used before discharging distinctness conditions. -/
def squaredCorrelationEdgeEvent
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (i j : Fin p) (t : ℝ) : Set (Fin p → E) :=
  {v | t < (normalizedGram v i j) ^ 2}

/-- Pointwise transport of a squared-correlation edge event. -/
@[simp]
theorem mem_squaredCorrelationEdgeEvent_permuteColumns_iff
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ : Equiv.Perm (Fin p)) (v : Fin p → E)
    (i j : Fin p) (t : ℝ) :
    permuteColumns σ v ∈ squaredCorrelationEdgeEvent (σ i) (σ j) t ↔
      v ∈ squaredCorrelationEdgeEvent i j t := by
  simp [squaredCorrelationEdgeEvent]

/-- Set-level transport of the same edge event.  This is the form used when
taking probabilities or intersections of finitely many edge events. -/
theorem preimage_squaredCorrelationEdgeEvent_permuteColumns
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ : Equiv.Perm (Fin p)) (i j : Fin p) (t : ℝ) :
    permuteColumns (E := E) σ ⁻¹'
        squaredCorrelationEdgeEvent (σ i) (σ j) t =
      squaredCorrelationEdgeEvent i j t := by
  ext v
  simp

/-! ## Transport from the nested representation -/

/-- Reading a right-nested iid tuple as a finite family and then permuting
its columns still has the ordinary iid product law. -/
theorem measurePreserving_permuteColumns_nestedTupleToFin
    {p : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving
      (fun z : NestedTuple E p ↦ permuteColumns σ (nestedTupleToFin p z))
      (nestedProductMeasure μ p)
      (Measure.pi fun _ : Fin p ↦ μ) := by
  have h := (measurePreserving_permuteColumns_pi μ σ).comp
    (measurePreserving_nestedTupleToFin μ p)
  change MeasurePreserving
    (permuteColumns (E := E) σ ∘ nestedTupleToFin p)
    (nestedProductMeasure μ p) (Measure.pi fun _ : Fin p ↦ μ)
  exact h

/-- The corresponding deterministic normalized-Gram identity for nested
tuples. -/
theorem normalizedGram_permuteColumns_nestedTupleToFin
    {p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ : Equiv.Perm (Fin p)) (z : NestedTuple E p) :
    normalizedGram (permuteColumns σ (nestedTupleToFin p z)) =
      Matrix.reindex σ σ (normalizedGram (nestedTupleToFin p z)) :=
  normalizedGram_permuteColumns σ (nestedTupleToFin p z)

/-- Full centered-Gaussian transport: center the raw observation columns,
read them as a finite family, and relabel them.  The result is still a family
of independent standard Gaussians in the centered subspace. -/
theorem measurePreserving_permuteCenteredNestedColumns
    (N p : ℕ) (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving
      (fun z : NestedTuple (ObservationSpace N) p ↦
        permuteColumns σ (nestedTupleToFin p (centerNested N p z)))
      (nestedProductMeasure (stdGaussian (ObservationSpace N)) p)
      (Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace N)) := by
  have hcenter : MeasurePreserving (centerNested N p)
      (nestedProductMeasure (stdGaussian (ObservationSpace N)) p)
      (nestedProductMeasure (stdGaussian (centeredSubspace N)) p) :=
    ⟨measurable_centerNested N p,
      map_centerNested_nestedProductMeasure N p⟩
  have hread := measurePreserving_nestedTupleToFin
    (stdGaussian (centeredSubspace N)) p
  have hperm := measurePreserving_permuteColumns_pi
    (stdGaussian (centeredSubspace N)) σ
  have h := hperm.comp (hread.comp hcenter)
  change MeasurePreserving
    (permuteColumns σ ∘ nestedTupleToFin p ∘ centerNested N p)
    (nestedProductMeasure (stdGaussian (ObservationSpace N)) p)
    (Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace N))
  exact h

/-- Centering and then permuting columns reindexes the centered normalized
Gram matrix exactly. -/
theorem normalizedGram_permuteColumns_centerNested
    (N p : ℕ) (σ : Equiv.Perm (Fin p))
    (z : NestedTuple (ObservationSpace N) p) :
    normalizedGram
        (permuteColumns σ (nestedTupleToFin p (centerNested N p z))) =
      Matrix.reindex σ σ
        (normalizedGram (nestedTupleToFin p (centerNested N p z))) :=
  normalizedGram_permuteColumns σ
    (nestedTupleToFin p (centerNested N p z))

end

end LogdetLean.Coherence
