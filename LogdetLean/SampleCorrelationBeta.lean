import LogdetLean.CenteredGaussianSample
import LogdetLean.GaussianBetaBridge
/-!
# Exact Beta-product law for a centered Gaussian sample-correlation determinant

This file composes two previously independent reductions:

* `CenteredGaussianSample`: subtracting the sample mean is orthogonal projection
  onto an `(N - 1)`-dimensional subspace, and projected standard Gaussian
  columns remain independent standard Gaussian columns in that subspace;
* `GaussianBetaBridge`: the normalized-Gram determinant of `p ≤ m`
  independent standard Gaussian vectors in dimension `m` has the exact
  independent Beta-product law.

The Gaussian--Beta theorem uses recursively nested tuples rather than
`Fin p`-indexed products.  We therefore center nested tuples coordinatewise
and prove their product-law identity directly.  The final theorem is stated
for the usual determinant obtained after subtracting the coordinatewise
sample mean in the ambient observation space.

Provenance: the independent normalized-Gram factors are exactly Rouault
(2007), Proposition 2.1(2), after setting his ambient dimension `n=m`.
The present centered `N=m+1` statement is a formally proved corollary obtained
by the projection reduction in `CenteredGaussianSample`; it is not quoted as
a verbatim theorem of Rouault.  See `PROVENANCE.md` for the exact equations,
pages, historical sources, and credit policy.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Module

/-- Apply the subtype-valued centering projection to every column of a nested
tuple.  This is the nested-tuple analogue of `centerColumns`. -/
def centerNested (N : ℕ) :
    (p : ℕ) → NestedTuple (ObservationSpace N) p →
      NestedTuple (centeredSubspace N) p
  | 0, _ => ULift.up Unit.unit
  | p + 1, z =>
      (centerNested N p z.1,
        (centeredSubspace N).orthogonalProjectionOnto z.2)

/-- Coordinatewise centering of nested tuples is measurable. -/
theorem measurable_centerNested (N : ℕ) :
    ∀ p, Measurable (centerNested N p) := by
  intro p
  induction p with
  | zero => exact measurable_const
  | succ p ih =>
      exact (ih.comp measurable_fst).prodMk
        ((by fun_prop : Measurable
          ((centeredSubspace N).orthogonalProjectionOnto :
            ObservationSpace N → centeredSubspace N)).comp measurable_snd)

/-- Converting a centered nested tuple to a finite family agrees pointwise
with applying `centerColumns` after converting the original tuple. -/
theorem nestedTupleToFin_centerNested (N : ℕ) :
    ∀ (p : ℕ) (z : NestedTuple (ObservationSpace N) p),
      nestedTupleToFin p (centerNested N p z) =
        centerColumns N p (nestedTupleToFin p z) := by
  intro p
  induction p with
  | zero =>
      intro z
      funext i
      exact Fin.elim0 i
  | succ p ih =>
      intro z
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [nestedTupleToFin, centerNested, centerColumns]
      · simp [nestedTupleToFin, centerNested, centerColumns, ih]

/-- Centering every coordinate of an iterated product of ambient standard
Gaussian laws gives the iterated product of standard Gaussian laws on the
centered subspace. -/
theorem map_centerNested_nestedProductMeasure (N : ℕ) :
    ∀ p,
      Measure.map (centerNested N p)
          (nestedProductMeasure (stdGaussian (ObservationSpace N)) p) =
        nestedProductMeasure (stdGaussian (centeredSubspace N)) p := by
  intro p
  induction p with
  | zero =>
      simp [centerNested, nestedProductMeasure]
  | succ p ih =>
      simp only [centerNested, nestedProductMeasure]
      change Measure.map
          (Prod.map (centerNested N p)
            (centeredSubspace N).orthogonalProjectionOnto)
          ((nestedProductMeasure (stdGaussian (ObservationSpace N)) p).prod
            (stdGaussian (ObservationSpace N))) =
        (nestedProductMeasure (stdGaussian (centeredSubspace N)) p).prod
          (stdGaussian (centeredSubspace N))
      rw [← Measure.map_prod_map _ _ (measurable_centerNested N p)
        (by
          exact (centeredSubspace N).orthogonalProjectionOnto.continuous.measurable)]
      rw [ih, (hasLaw_centerProjection_stdGaussian N).map_eq]

/-- The centered sample-correlation determinant, written in the usual ambient
coordinates: subtract each column's sample mean, normalize the columns, form
their Gram matrix, and take its determinant. -/
def centeredSampleCorrelationDet (N p : ℕ)
    (z : NestedTuple (ObservationSpace N) p) : ℝ :=
  (normalizedGram
    (fun j ↦ centerVector (nestedTupleToFin p z j))).det

/-- An equivalent subtype-valued version of the centered determinant. -/
def nestedCenteredNormalizedGramDet (N p : ℕ)
    (z : NestedTuple (ObservationSpace N) p) : ℝ :=
  nestedNormalizedGramDet p (centerNested N p z)

/-- The ambient mean-subtraction statistic equals the normalized-Gram
determinant of the projected vectors inside the centered subspace. -/
theorem centeredSampleCorrelationDet_eq_nestedCenteredNormalizedGramDet
    {N p : ℕ} (hN : 0 < N)
    (z : NestedTuple (ObservationSpace N) p) :
    centeredSampleCorrelationDet N p z =
      nestedCenteredNormalizedGramDet N p z := by
  rw [centeredSampleCorrelationDet, nestedCenteredNormalizedGramDet,
    nestedNormalizedGramDet]
  rw [det_normalizedGram_centerColumns_ambient hN]
  rw [nestedTupleToFin_centerNested]

/-- The subtype-valued centered determinant is measurable. -/
theorem measurable_nestedCenteredNormalizedGramDet (N p : ℕ) :
    Measurable (nestedCenteredNormalizedGramDet N p) := by
  exact ((measurable_det_normalizedGram (E := centeredSubspace N) p).comp
    (measurable_nestedTupleToFin (α := centeredSubspace N) p)).comp
      (measurable_centerNested N p)

/-- The usual ambient centered determinant is measurable for `N > 0`. -/
theorem measurable_centeredSampleCorrelationDet {N p : ℕ} (hN : 0 < N) :
    Measurable (centeredSampleCorrelationDet N p) := by
  convert measurable_nestedCenteredNormalizedGramDet N p using 1
  funext z
  exact centeredSampleCorrelationDet_eq_nestedCenteredNormalizedGramDet hN z

/-- General `N` form of the exact centered Gaussian sample-correlation law.
There are `N` observations, hence centering leaves dimension `N - 1`; for
`p ≤ N - 1`, the determinant has the corresponding independent Beta-product
law. -/
theorem map_centeredSampleCorrelationDet_eq_map_product_betaFactors
    (N p : ℕ) (hN : 0 < N) (hp : p ≤ N - 1) :
    Measure.map (centeredSampleCorrelationDet N p)
        (nestedProductMeasure (stdGaussian (ObservationSpace N)) p) =
      Measure.map (nestedRealProduct p)
        (nestedProductMeasureFamily
          (gaussianGramSchmidtFactorMeasure (N - 1)) p) := by
  rw [Measure.map_congr (Filter.Eventually.of_forall fun z ↦
    centeredSampleCorrelationDet_eq_nestedCenteredNormalizedGramDet hN z)]
  rw [show nestedCenteredNormalizedGramDet N p =
      nestedNormalizedGramDet p ∘ centerNested N p by rfl]
  have hdet : Measurable
      (nestedNormalizedGramDet (E := centeredSubspace N) p) := by
    exact (measurable_det_normalizedGram (E := centeredSubspace N) p).comp
      (measurable_nestedTupleToFin (α := centeredSubspace N) p)
  rw [← Measure.map_map hdet (measurable_centerNested N p)]
  rw [map_centerNested_nestedProductMeasure]
  exact map_gaussianNormalizedGramDet_eq_map_product_betaFactors
    (E := centeredSubspace N) (N - 1) p
      (finrank_centeredSubspace hN) hp

/-- Exact form requested for a centered Gaussian sample with `N = m + 1`
observations and `p ≤ m` variables.  Its sample-correlation determinant has
the independent factor law with stage `j` factor
`Beta((m-j+1)/2,(j-1)/2)` (and the first factor equal to one). -/
theorem map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors
    (m p : ℕ) (hp : p ≤ m) :
    Measure.map (centeredSampleCorrelationDet (m + 1) p)
        (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) =
      Measure.map (nestedRealProduct p)
        (nestedProductMeasureFamily
          (gaussianGramSchmidtFactorMeasure m) p) := by
  simpa using
    map_centeredSampleCorrelationDet_eq_map_product_betaFactors
      (m + 1) p (Nat.zero_lt_succ m) hp

/-- `HasLaw` form of the `N = m + 1` centered sample-correlation determinant
theorem. -/
theorem hasLaw_centeredSampleCorrelationDet_succ_betaProduct
    (m p : ℕ) (hp : p ≤ m) :
    HasLaw (centeredSampleCorrelationDet (m + 1) p)
      (Measure.map (nestedRealProduct p)
        (nestedProductMeasureFamily
          (gaussianGramSchmidtFactorMeasure m) p))
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p) := by
  refine ⟨(measurable_centeredSampleCorrelationDet
    (Nat.zero_lt_succ m)).aemeasurable, ?_⟩
  exact map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors
    m p hp

end

end LogdetLean
