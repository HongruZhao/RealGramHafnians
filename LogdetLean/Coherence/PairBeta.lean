import LogdetLean.FixedSubspaceGaussian
import LogdetLean.GaussianSubspace
/-!
# Exact Beta law of one squared Gaussian correlation

This module supplies the pair-level distributional input for the coherence
point process.  It proves both the marginal Beta law and the stronger joint
law retaining the first Gaussian vector.  The latter makes explicit that the
squared normalized inner product has a conditional law independent of the
first vector.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The square of the normalized real inner product.  Mathlib's totalized
division assigns a value also when one vector is zero; that Gaussian-null set
is removed explicitly in the law proof. -/
def squaredNormalizedInner (u v : E) : ℝ :=
  (inner ℝ u v) ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)

/-- Joint measurability of the squared normalized inner product. -/
theorem measurable_uncurry_squaredNormalizedInner :
    Measurable (Function.uncurry (squaredNormalizedInner (E := E))) := by
  unfold squaredNormalizedInner
  fun_prop

/-- Projection onto the line through a nonzero vector gives the usual
squared normalized inner product. -/
theorem normSq_spanProjection_ratio_eq_squaredNormalizedInner
    (u v : E) (hu : u ≠ 0) :
    ‖(ℝ ∙ u).orthogonalProjectionOnto v‖ ^ 2 / ‖v‖ ^ 2 =
      squaredNormalizedInner u v := by
  change ‖(ℝ ∙ u).starProjection v‖ ^ 2 / ‖v‖ ^ 2 = _
  rw [Submodule.starProjection_singleton]
  unfold squaredNormalizedInner
  rw [norm_smul]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  by_cases hv : v = 0
  · subst v
    simp
  have hnormv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [Real.norm_eq_abs, abs_div,
    abs_of_nonneg (sq_nonneg ‖u‖), ← sq_abs (inner ℝ u v)]
  field_simp [hnorm, hnormv]

/-- For a fixed nonzero first vector in dimension `m ≥ 2`, a fresh standard
Gaussian vector has squared normalized inner product
`Beta(1/2,(m-1)/2)`. -/
theorem map_squaredNormalizedInner_stdGaussian_fixed
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (u : E) (hu : u ≠ 0) :
    Measure.map (squaredNormalizedInner u) (stdGaussian E) =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
  let K : Submodule ℝ E := ℝ ∙ u
  have hfinK : finrank ℝ K = 1 := by
    simpa [K] using finrank_span_singleton hu
  have hfinPerp : finrank ℝ Kᗮ = m - 1 := by
    have hadd := K.finrank_add_finrank_orthogonal
    rw [hfinK, hdim] at hadd
    omega
  let _ : Nontrivial K :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ K)
  let _ : Nontrivial Kᗮ :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ Kᗮ)
  have hbeta := hasLaw_orthogonalProjection_normSq_ratio_beta (K := K)
  have heq : (squaredNormalizedInner u) =ᵐ[(stdGaussian E)]
      (fun v : E ↦ ‖K.orthogonalProjectionOnto v‖ ^ 2 / ‖v‖ ^ 2) := by
    exact Filter.Eventually.of_forall fun v ↦
      (normSq_spanProjection_ratio_eq_squaredNormalizedInner u v hu).symm
  calc
    Measure.map (squaredNormalizedInner u) (stdGaussian E) =
        Measure.map
          (fun v : E ↦ ‖K.orthogonalProjectionOnto v‖ ^ 2 / ‖v‖ ^ 2)
          (stdGaussian E) := Measure.map_congr heq
    _ = betaMeasure ((finrank ℝ K : ℝ) / 2)
          ((finrank ℝ Kᗮ : ℝ) / 2) := hbeta.map_eq
    _ = betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
      rw [hfinK, hfinPerp]
      norm_num

/-- The pair map retaining the first vector and appending its squared
correlation with the second vector. -/
def retainFirstAndSquaredInner (z : E × E) : E × ℝ :=
  (z.1, squaredNormalizedInner z.1 z.2)

/-- Exact joint law: the first Gaussian vector is independent of its squared
normalized inner product with a second independent Gaussian vector. -/
theorem map_retainFirstAndSquaredInner_gaussianProduct
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m) :
    Measure.map (retainFirstAndSquaredInner (E := E))
        ((stdGaussian E).prod (stdGaussian E)) =
      (stdGaussian E).prod
        (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  have hnonzero : ∀ᵐ u ∂stdGaussian E, u ≠ 0 := by
    simpa [ae_iff] using
      stdGaussian_zero_singleton (E := E)
  have hlaw : ∀ᵐ u ∂stdGaussian E,
      Measure.map (squaredNormalizedInner u) (stdGaussian E) =
        betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
    filter_upwards [hnonzero] with u hu
    exact map_squaredNormalizedInner_stdGaussian_fixed m hdim hm u hu
  exact ((MeasurePreserving.id (stdGaussian E)).skew_product
    measurable_uncurry_squaredNormalizedInner hlaw).map_eq

/-- Marginal exact Beta law of the squared normalized inner product of two
independent `m`-dimensional standard Gaussian vectors. -/
theorem map_squaredNormalizedInner_gaussianProduct
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m) :
    Measure.map (fun z : E × E ↦ squaredNormalizedInner z.1 z.2)
        ((stdGaussian E).prod (stdGaussian E)) =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
  let _ : SFinite (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) := by
    unfold betaMeasure
    infer_instance
  have hjoint := map_retainFirstAndSquaredInner_gaussianProduct
    (E := E) m hdim hm
  have hsnd : Measurable (Prod.snd : E × ℝ → ℝ) := measurable_snd
  have hpair : Measurable (retainFirstAndSquaredInner (E := E)) :=
    measurable_fst.prodMk measurable_uncurry_squaredNormalizedInner
  calc
    Measure.map (fun z : E × E ↦ squaredNormalizedInner z.1 z.2)
        ((stdGaussian E).prod (stdGaussian E)) =
        Measure.map Prod.snd
          (Measure.map (retainFirstAndSquaredInner (E := E))
            ((stdGaussian E).prod (stdGaussian E))) := by
      rw [Measure.map_map hsnd hpair]
      rfl
    _ = Measure.map Prod.snd
          ((stdGaussian E).prod
            (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2))) := by
      rw [hjoint]
    _ = betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
      rw [Measure.map_snd_prod]
      simp

end

end LogdetLean.Coherence
