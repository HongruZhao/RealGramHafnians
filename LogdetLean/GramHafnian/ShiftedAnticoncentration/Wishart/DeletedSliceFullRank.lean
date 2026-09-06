import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.MatrixGaussianBridge
/-!
# Full rank on every one-coordinate Gaussian slice

The coordinatewise Gaussian integration-by-parts theorem needs smoothness on
an entire scalar slice, not merely almost everywhere on the full matrix
space.  When one scalar entry in row `a` is varied, deleting row `a` removes
that entry altogether.  If the row-deleted matrix already has full column
rank, every point of the scalar slice has full column rank.  This file proves
that row-deleted event almost surely and transports it to flat coordinates.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Half-Gaussian coordinates indexed by any finite type form a scaled
standard Euclidean Gaussian vector. -/
theorem map_toLp_halfGaussianVector_fintype
    (ι : Type*) [Fintype ι] :
    Measure.map (WithLp.toLp 2)
        (Measure.pi (fun _ : ι ↦ gaussianReal 0 halfGaussianVariance)) =
      Measure.map
        (fun x : EuclideanSpace ℝ ι ↦
          ((Real.sqrt 2)⁻¹ : ℝ) • x)
        (stdGaussian (EuclideanSpace ℝ ι)) := by
  let c : ℝ := (Real.sqrt 2)⁻¹
  let scaleRaw : (ι → ℝ) → (ι → ℝ) := fun x i ↦ c * x i
  have hscaleRaw :
      Measure.map scaleRaw
          (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) =
        Measure.pi (fun _ : ι ↦
          gaussianReal 0 halfGaussianVariance) := by
    rw [Measure.pi_map_pi (fun _ ↦
      (show Measurable (fun x : ℝ ↦ c * x) by fun_prop).aemeasurable)]
    congr 1
    funext i
    simpa [c] using map_invSqrtTwo_gaussianReal_zero_one
  rw [← hscaleRaw]
  rw [Measure.map_map (show Measurable (WithLp.toLp 2 :
      (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop)
    (show Measurable scaleRaw by fun_prop)]
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map
    (show Measurable (fun x : EuclideanSpace ℝ ι ↦ c • x) by fun_prop)
    (show Measurable (WithLp.toLp 2 :
      (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with x
  ext i
  rfl

/-- Scaled standard Gaussian columns in an arbitrary finite-dimensional
coordinate Euclidean space are almost surely independent. -/
theorem ae_linearIndependent_pi_scaledStdGaussian_real_fintype
    (ι : Type*) [Fintype ι] (p : ℕ)
    (hp : p ≤ Fintype.card ι) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin p ↦
        (stdGaussian (EuclideanSpace ℝ ι)).map
          (fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • x)),
      LinearIndependent ℝ v := by
  let E := EuclideanSpace ℝ ι
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hc : c ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hbase : ∀ᵐ v ∂Measure.pi (fun _ : Fin p ↦ stdGaussian E),
      LinearIndependent ℝ v := by
    apply LogdetLean.ae_linearIndependent_pi_stdGaussian
    simpa [E] using hp
  let scale : (Fin p → E) → (Fin p → E) := fun v i ↦ c • v i
  have hmp : MeasurePreserving scale
      (Measure.pi fun _ : Fin p ↦ stdGaussian E)
      (Measure.pi fun _ : Fin p ↦
        (stdGaussian E).map (fun x ↦ c • x)) := by
    apply measurePreserving_pi
    intro i
    exact ⟨by fun_prop, rfl⟩
  have hset : MeasurableSet
      {v : Fin p → E | LinearIndependent ℝ v} :=
    LogdetLean.measurableSet_linearlyIndependentTuples p
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable hset).2
  filter_upwards [hbase] with v hv
  exact realLinearIndependent_const_smul hv hc

/-- Raw half-Gaussian columns over an arbitrary finite row type are almost
surely linearly independent. -/
theorem ae_linearIndependent_pi_halfGaussianColumns_fintype
    (ι : Type*) [Fintype ι] (p : ℕ)
    (hp : p ≤ Fintype.card ι) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin p ↦
        Measure.pi (fun _ : ι ↦ gaussianReal 0 halfGaussianVariance)),
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2 (v j) :
          Fin p → EuclideanSpace ℝ ι) := by
  let E := EuclideanSpace ℝ ι
  let target : Measure E :=
    (stdGaussian E).map
      (fun x ↦ ((Real.sqrt 2)⁻¹ : ℝ) • x)
  have hcoord : MeasurePreserving (WithLp.toLp 2)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 halfGaussianVariance))
      target := by
    refine ⟨by fun_prop, ?_⟩
    simpa [target] using map_toLp_halfGaussianVector_fintype ι
  have hfamily : MeasurePreserving
      (fun v : Fin p → (ι → ℝ) ↦
        (fun j ↦ WithLp.toLp 2 (v j) : Fin p → E))
      (Measure.pi (fun _ : Fin p ↦
        Measure.pi (fun _ : ι ↦ gaussianReal 0 halfGaussianVariance)))
      (Measure.pi fun _ : Fin p ↦ target) := by
    apply measurePreserving_pi
    intro j
    exact hcoord
  exact hfamily.quasiMeasurePreserving.ae
    (ae_linearIndependent_pi_scaledStdGaussian_real_fintype ι p hp)

/-- Delete one coordinate of a raw row vector. -/
def deleteRawRowCoordinate {k : ℕ} (a₀ : Fin k) :
    (Fin k → ℝ) → ({a : Fin k // a ≠ a₀} → ℝ) :=
  fun x a ↦ x a.1

/-- Coordinate deletion preserves the iid half-Gaussian product law. -/
theorem measurePreserving_deleteRawRowCoordinate
    {k : ℕ} (a₀ : Fin k) :
    MeasurePreserving (deleteRawRowCoordinate a₀)
      (Measure.pi (fun _ : Fin k ↦
        gaussianReal 0 halfGaussianVariance))
      (Measure.pi (fun _ : {a : Fin k // a ≠ a₀} ↦
        gaussianReal 0 halfGaussianVariance)) := by
  refine ⟨?_, ?_⟩
  · unfold deleteRawRowCoordinate
    exact measurable_pi_lambda _ fun a ↦ measurable_pi_apply a.1
  have h := Measure.infinitePi_map_restrict'
    (μ := fun _ : Fin k ↦ gaussianReal 0 halfGaussianVariance)
    (I := {a : Fin k | a ≠ a₀})
  rw [Measure.infinitePi_eq_pi] at h
  simp_rw [Measure.infinitePi_eq_pi] at h
  exact h

/-- Delete the same row coordinate from every raw matrix column. -/
def deleteRawMatrixRow {k p : ℕ} (a₀ : Fin k) :
    (Fin p → Fin k → ℝ) →
      (Fin p → {a : Fin k // a ≠ a₀} → ℝ) :=
  fun v j a ↦ v j a.1

/-- Row deletion maps independent half-Gaussian columns to independent
half-Gaussian columns on the smaller row type. -/
theorem measurePreserving_deleteRawMatrixRow
    {k p : ℕ} (a₀ : Fin k) :
    MeasurePreserving (deleteRawMatrixRow (p := p) a₀)
      (halfGaussianColumnProduct k p)
      (Measure.pi (fun _ : Fin p ↦
        Measure.pi (fun _ : {a : Fin k // a ≠ a₀} ↦
          gaussianReal 0 halfGaussianVariance))) := by
  change MeasurePreserving
    (fun v : Fin p → (Fin k → ℝ) ↦
      fun j ↦ deleteRawRowCoordinate a₀ (v j))
    (halfGaussianColumnProduct k p)
    (Measure.pi (fun _ : Fin p ↦
      Measure.pi (fun _ : {a : Fin k // a ≠ a₀} ↦
        gaussianReal 0 halfGaussianVariance)))
  apply measurePreserving_pi
  intro j
  exact measurePreserving_deleteRawRowCoordinate a₀

/-- Almost-sure linear independence survives deletion of any fixed row when
`p ≤ k-1`. -/
theorem ae_linearIndependent_deletedRow_halfGaussianColumns
    {k p : ℕ} (a₀ : Fin k)
    (hp : p ≤ Fintype.card {a : Fin k // a ≠ a₀}) :
    ∀ᵐ v ∂halfGaussianColumnProduct k p,
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2
          (fun a : {a : Fin k // a ≠ a₀} ↦ v j a.1) :
          Fin p → EuclideanSpace ℝ {a : Fin k // a ≠ a₀}) := by
  exact (measurePreserving_deleteRawMatrixRow (p := p) a₀).quasiMeasurePreserving.ae
      (ae_linearIndependent_pi_halfGaussianColumns_fintype
        {a : Fin k // a ≠ a₀} p hp)

/-- Delete one row of a matrix while retaining all columns. -/
def deleteMatrixRow {k p : ℕ} (a₀ : Fin k)
    (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix {a : Fin k // a ≠ a₀} (Fin p) ℝ :=
  fun a j ↦ R a.1 j

/-- Under the literal matrix law, deleting any fixed row leaves full column
rank whenever the number of columns fits in the remaining row space. -/
theorem ae_linearIndependent_deleteMatrixRow_halfGaussianMatrix
    {k p : ℕ} (a₀ : Fin k)
    (hp : p ≤ Fintype.card {a : Fin k // a ≠ a₀}) :
    ∀ᵐ R ∂halfGaussianMatrix k p,
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2
          (fun a : {a : Fin k // a ≠ a₀} ↦ R a.1 j) :
          Fin p → EuclideanSpace ℝ {a : Fin k // a ≠ a₀}) := by
  have hmp : MeasurePreserving (matrixToColumnsMeasurableEquiv k p)
      (halfGaussianMatrix k p) (halfGaussianColumnProduct k p) :=
    ⟨(matrixToColumnsMeasurableEquiv k p).measurable,
      map_matrixToColumns_halfGaussianMatrix k p⟩
  have h := hmp.quasiMeasurePreserving.ae
    (ae_linearIndependent_deletedRow_halfGaussianColumns a₀ hp)
  filter_upwards [h] with R hR
  change LinearIndependent ℝ
    (fun j ↦ WithLp.toLp 2
      (fun a : {a : Fin k // a ≠ a₀} ↦ R a.1 j)) at hR
  exact hR

/-- Restriction from the full Euclidean row space to all rows except one. -/
def deleteEuclideanCoordinate {k : ℕ} (a₀ : Fin k) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ]
      EuclideanSpace ℝ {a : Fin k // a ≠ a₀} where
  toFun x := WithLp.toLp 2 (fun a ↦ (WithLp.ofLp x) a.1)
  map_add' x y := by
    ext a
    rfl
  map_smul' c x := by
    ext a
    rfl

/-- Linear independence after deleting a row implies linear independence of
the original columns. -/
theorem linearIndependent_of_deleteMatrixRow
    {k p : ℕ} (a₀ : Fin k) (R : Matrix (Fin k) (Fin p) ℝ)
    (hR : LinearIndependent ℝ
      (fun j ↦ WithLp.toLp 2
        (fun a : {a : Fin k // a ≠ a₀} ↦ R a.1 j) :
        Fin p → EuclideanSpace ℝ {a : Fin k // a ≠ a₀})) :
    LinearIndependent ℝ
      (fun j ↦ WithLp.toLp 2 (fun a ↦ R a j) :
        Fin p → EuclideanSpace ℝ (Fin k)) := by
  apply LinearIndependent.of_comp (deleteEuclideanCoordinate a₀)
  simpa [Function.comp_def, deleteEuclideanCoordinate] using hR

/-- Flattening when the scalar dimension is presented syntactically as a
successor, as required by coordinatewise Gaussian integration by parts. -/
def flatSuccMatrixMeasurableEquiv {k p n : ℕ}
    (hdim : n + 1 = k * p) :
    (Fin (n + 1) → ℝ) ≃ᵐ Matrix (Fin k) (Fin p) ℝ :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (k * p) ↦ ℝ)
    (finCongr hdim)).trans (flatMatrixMeasurableEquiv k p)

@[simp]
theorem flatSuccMatrixMeasurableEquiv_apply
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (x : Fin (n + 1) → ℝ) (a : Fin k) (j : Fin p) :
    flatSuccMatrixMeasurableEquiv hdim x a j =
      x ((finCongr hdim).symm (finProdFinEquiv (a, j))) := by
  rfl

/-- The successor-dimension flattening equivalence preserves the literal iid
half-Gaussian law. -/
theorem measurePreserving_flatSuccMatrixMeasurableEquiv
    {k p n : ℕ} (hdim : n + 1 = k * p) :
    MeasurePreserving (flatSuccMatrixMeasurableEquiv hdim)
      (halfGaussianPi (n + 1)) (halfGaussianMatrix k p) := by
  have hreindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (k * p) ↦ ℝ)
        (finCongr hdim))
      (halfGaussianPi (n + 1)) (halfGaussianPi (k * p)) := by
    simpa [halfGaussianPi] using
      (measurePreserving_piCongrLeft
        (fun _ : Fin (k * p) ↦
          gaussianReal 0 halfGaussianVariance) (finCongr hdim))
  exact (measurePreserving_flatMatrixMeasurableEquiv k p).comp hreindex

/-- The matrix entry corresponding to a selected flat scalar coordinate. -/
def flatCoordinatePair {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) : Fin k × Fin p :=
  finProdFinEquiv.symm (finCongr hdim i)

/-- The matrix row containing a selected flat scalar coordinate. -/
def flatCoordinateRow {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) : Fin k :=
  (flatCoordinatePair hdim i).1

/-- The matrix column containing a selected flat scalar coordinate. -/
def flatCoordinateColumn {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) : Fin p :=
  (flatCoordinatePair hdim i).2

/-- After deleting the row containing the selected flat coordinate, the
remaining matrix is independent of the value inserted at that coordinate. -/
theorem deleteMatrixRow_flatSucc_insertNth_eq
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) (y : Fin n → ℝ) (s t : ℝ) :
    deleteMatrixRow (flatCoordinateRow hdim i)
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y)) =
      deleteMatrixRow (flatCoordinateRow hdim i)
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y)) := by
  ext a j
  let q : Fin (n + 1) :=
    (finCongr hdim).symm (finProdFinEquiv (a.1, j))
  have hqi : q ≠ i := by
    intro hq
    have hflat : finProdFinEquiv (a.1, j) = finCongr hdim i := by
      apply (finCongr hdim).symm.injective
      simpa [q] using hq
    have hpair : (a.1, j) = finProdFinEquiv.symm (finCongr hdim i) := by
      have hp := congrArg finProdFinEquiv.symm hflat
      simpa only [Equiv.symm_apply_apply] using hp
    exact a.property (congrArg Prod.fst hpair)
  obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hqi
  change (@Fin.insertNth n (fun _ : Fin (n + 1) ↦ ℝ) i s y q) =
    @Fin.insertNth n (fun _ : Fin (n + 1) ↦ ℝ) i t y q
  rw [← hz, Fin.insertNth_apply_succAbove,
    Fin.insertNth_apply_succAbove]

/-- The row-deleted Euclidean column family associated with a flat scalar
array and a distinguished coordinate. -/
def deletedFlatColumns {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    Fin p → EuclideanSpace ℝ
      {a : Fin k // a ≠ flatCoordinateRow hdim i} :=
  fun j ↦ WithLp.toLp 2
    (fun a ↦ flatSuccMatrixMeasurableEquiv hdim x a.1 j)

/-- The deleted-column family is a measurable function of all scalar
coordinates. -/
theorem measurable_deletedFlatColumns
    {k p n : ℕ} (hdim : n + 1 = k * p) (i : Fin (n + 1)) :
    Measurable (deletedFlatColumns hdim i) := by
  unfold deletedFlatColumns
  fun_prop

/-- Splitting a flat iid Gaussian array into all coordinates except `i` and
the exposed scalar at `i` preserves the exact product law. -/
theorem measurePreserving_insertNthPair_halfGaussianPi
    {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving
      (fun z : (Fin n → ℝ) × ℝ ↦ i.insertNth z.2 z.1)
      ((halfGaussianPi n).prod
        (gaussianReal 0 halfGaussianVariance))
      (halfGaussianPi (n + 1)) := by
  let μ : Fin (n + 1) → Measure ℝ :=
    fun _ ↦ gaussianReal 0 halfGaussianVariance
  have hsplit := (measurePreserving_piFinSuccAbove μ i).symm
  have hswap : MeasurePreserving Prod.swap
      ((Measure.pi (fun j : Fin n ↦ μ (i.succAbove j))).prod (μ i))
      ((μ i).prod
        (Measure.pi (fun j : Fin n ↦ μ (i.succAbove j)))) :=
    Measure.measurePreserving_swap
  have hcomp := hsplit.comp hswap
  simpa [μ, halfGaussianPi, Function.comp_def,
    MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv] using hcomp

/-- For almost every choice of the unexposed scalar coordinates, every point
of the exposed one-dimensional slice has full column rank.  The stronger
row-deleted event is used internally to make the conclusion uniform in the
slice parameter. -/
theorem ae_forall_linearIndependent_flatSuccMatrix_slice
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1))
    (hp : p ≤ Fintype.card
      {a : Fin k // a ≠ flatCoordinateRow hdim i}) :
    ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2
          (fun a ↦ flatSuccMatrixMeasurableEquiv hdim
            (i.insertNth t y) a j) :
          Fin p → EuclideanSpace ℝ (Fin k)) := by
  have hmatrix :=
    ae_linearIndependent_deleteMatrixRow_halfGaussianMatrix
      (flatCoordinateRow hdim i) hp
  have hflat : ∀ᵐ x ∂halfGaussianPi (n + 1),
      LinearIndependent ℝ (deletedFlatColumns hdim i x) := by
    have h := (measurePreserving_flatSuccMatrixMeasurableEquiv hdim).quasiMeasurePreserving.ae
      hmatrix
    filter_upwards [h] with x hx
    exact hx
  let cols : ((Fin n → ℝ) × ℝ) →
      (Fin p → EuclideanSpace ℝ
        {a : Fin k // a ≠ flatCoordinateRow hdim i}) :=
    fun z ↦ deletedFlatColumns hdim i (i.insertNth z.2 z.1)
  have hprod : ∀ᵐ z ∂((halfGaussianPi n).prod
      (gaussianReal 0 halfGaussianVariance)),
      LinearIndependent ℝ (cols z) := by
    have h := (measurePreserving_insertNthPair_halfGaussianPi i).quasiMeasurePreserving.ae
      hflat
    simpa [cols] using h
  have hcols : Measurable cols := by
    apply (measurable_deletedFlatColumns hdim i).comp
    fun_prop
  have hset : MeasurableSet
      {z : (Fin n → ℝ) × ℝ | LinearIndependent ℝ (cols z)} :=
    (LogdetLean.measurableSet_linearlyIndependentTuples p).preimage hcols
  rw [Measure.ae_prod_iff_ae_ae hset] at hprod
  filter_upwards [hprod] with y hy
  obtain ⟨t₀, ht₀⟩ := hy.exists
  intro t
  have hmatrixEq :=
    deleteMatrixRow_flatSucc_insertNth_eq hdim i y t₀ t
  have hcolsEq :
      deletedFlatColumns hdim i (i.insertNth t₀ y) =
        deletedFlatColumns hdim i (i.insertNth t y) := by
    funext j
    ext a
    exact congrFun (congrFun hmatrixEq a) j
  have hdeleted : LinearIndependent ℝ
      (deletedFlatColumns hdim i (i.insertNth t y)) := by
    rw [← hcolsEq]
    simpa [cols] using ht₀
  exact linearIndependent_of_deleteMatrixRow
    (flatCoordinateRow hdim i)
    (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y)) hdeleted

/-- Uniform one-coordinate-slice invertibility of the literal real Wishart
Gram matrix.  This is the full-rank premise needed to differentiate inverse
Gram fields on every scalar slice in Gaussian integration by parts. -/
theorem ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_slice
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1))
    (hp : p ≤ Fintype.card
      {a : Fin k // a ≠ flatCoordinateRow hdim i}) :
    ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
      IsUnit (realWishartGram
        (flatSuccMatrixMeasurableEquiv hdim
          (i.insertNth t y))).det := by
  filter_upwards [ae_forall_linearIndependent_flatSuccMatrix_slice
    hdim i hp] with y hy
  intro t
  apply isUnit_iff_ne_zero.mpr
  rw [realWishartGram_eq_gram_toLp_columns]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (hy t)

/-- The deleted row has cardinality `k-1`, so strict rectangularity is the
transparent numerical hypothesis for uniform slice invertibility. -/
theorem ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_slice_of_lt
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (i : Fin (n + 1)) (hp : p < k) :
    ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
      IsUnit (realWishartGram
        (flatSuccMatrixMeasurableEquiv hdim
          (i.insertNth t y))).det := by
  apply ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_slice hdim i
  have hcard : Fintype.card
      {a : Fin k // a ≠ flatCoordinateRow hdim i} = k - 1 := by
    rw [Fintype.card_of_subtype
      {a : Fin k | a ≠ flatCoordinateRow hdim i}]
    · rw [Finset.filter_not,
        Finset.filter_eq' _ (flatCoordinateRow hdim i),
        if_pos (Finset.mem_univ _), Finset.card_sdiff,
        Finset.card_univ, Fintype.card_fin]
      simp
    · simp
  rw [hcard]
  omega

/-- All coordinate slices are uniformly full rank under the single numerical
condition `p < k`.  The quantifier order exactly matches the slice premise of
`integral_halfGaussianPi_divergence`. -/
theorem forall_ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_slice
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k) :
    ∀ i : Fin (n + 1),
      ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
        IsUnit (realWishartGram
          (flatSuccMatrixMeasurableEquiv hdim
            (i.insertNth t y))).det := by
  intro i
  exact ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_slice_of_lt
    hdim i hp

/-- Concrete `2m`-column form used by the realification of `m` complex
columns.  The stated two-row gap is stronger than the one-row deletion
needed for full rank and is the natural first inverse-moment regime. -/
theorem forall_ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_twoMul
    {k m n : ℕ} (hdim : n + 1 = k * (2 * m))
    (hgap : 2 * m + 2 ≤ k) :
    ∀ i : Fin (n + 1),
      ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
        IsUnit (realWishartGram
          (flatSuccMatrixMeasurableEquiv hdim
            (i.insertNth t y))).det := by
  apply forall_ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_slice
    hdim
  omega

end Wishart

end

end LogdetLean.GramHafnian
