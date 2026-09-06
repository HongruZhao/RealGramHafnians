import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic
import LogdetLean.FixedSubspaceGaussian
import LogdetLean.NormalizedGram
/-!
# Centered Gaussian samples

This file formalizes the deterministic and probabilistic reduction from a
Gaussian data column to its centered version.  Centering is the orthogonal
projection onto the orthogonal complement of the constant vector.  We also
record that applying this projection independently to finitely many Gaussian
columns preserves their product structure, and that normalized Gram
determinants do not depend on whether subspace vectors are viewed in their
subtype or in the ambient space.

Mathematical provenance: sample-mean removal as orthogonal projection and the
resulting `N-1` Gaussian degrees of freedom are classical consequences of
Gaussian orthogonal decomposition (historically connected with
Wishart--Bartlett (1933) and Cochran (1934)).  This exact Hilbert-space wrapper
is proved directly here and is not a verbatim theorem from Rouault.  See
`PROVENANCE.md`.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

/-- The ambient Euclidean space for one data column with `N` observations. -/
abbrev ObservationSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- The all-ones vector in observation space. -/
def constantVector (N : ℕ) : ObservationSpace N :=
  WithLp.toLp 2 (fun _ : Fin N ↦ (1 : ℝ))

@[simp] theorem constantVector_apply (N : ℕ) (i : Fin N) :
    constantVector N i = 1 := by simp [constantVector, PiLp.toLp_apply]

/-- The arithmetic mean of the coordinates of a data column. -/
def sampleMean {N : ℕ} (x : ObservationSpace N) : ℝ :=
  (∑ i, x i) / (N : ℝ)

/-- Coordinatewise centering by the sample mean. -/
def centerVector {N : ℕ} (x : ObservationSpace N) : ObservationSpace N :=
  WithLp.toLp 2 (fun i ↦ x i - sampleMean x)

@[simp] theorem centerVector_apply {N : ℕ} (x : ObservationSpace N) (i : Fin N) :
    centerVector x i = x i - sampleMean x := by
  simp [centerVector, PiLp.toLp_apply]

/-- The zero-sum subspace, expressed geometrically as the orthogonal
complement of the constant direction. -/
def centeredSubspace (N : ℕ) : Submodule ℝ (ObservationSpace N) :=
  (ℝ ∙ constantVector N)ᗮ

/-- Membership in the centered subspace is exactly the zero-sum condition. -/
theorem mem_centeredSubspace_iff_sum_eq_zero {N : ℕ} (x : ObservationSpace N) :
    x ∈ centeredSubspace N ↔ ∑ i, x i = 0 := by
  rw [centeredSubspace, Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [PiLp.inner_apply]

/-- The constant vector is nonzero as soon as the sample size is positive. -/
theorem constantVector_ne_zero {N : ℕ} (hN : 0 < N) : constantVector N ≠ 0 := by
  intro h
  let i : Fin N := ⟨0, hN⟩
  have hi : constantVector N i = 0 := by
    rw [h]
    simp
  norm_num at hi

/-- The centered subspace has dimension `N-1`. -/
theorem finrank_centeredSubspace {N : ℕ} (hN : 0 < N) :
    Module.finrank ℝ (centeredSubspace N) = N - 1 := by
  let _ : Fact
      (Module.finrank ℝ (ObservationSpace N) = (N - 1) + 1) :=
    ⟨by simp [Nat.sub_add_cancel hN]⟩
  exact Submodule.finrank_orthogonal_span_singleton
    (n := N - 1) (constantVector_ne_zero hN)

/-- The usual coordinatewise centering formula is exactly the ambient-valued
orthogonal projection onto `centeredSubspace N`. -/
theorem centerVector_eq_starProjection {N : ℕ} (hN : 0 < N)
    (x : ObservationSpace N) :
    centerVector x = (centeredSubspace N).starProjection x := by
  rw [centeredSubspace, Submodule.starProjection_orthogonal_val]
  rw [Submodule.starProjection_singleton]
  ext i
  simp only [centerVector_apply, PiLp.inner_apply, constantVector_apply,
    RCLike.inner_apply, conj_trivial, EuclideanSpace.real_norm_sq_eq,
    one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, sampleMean, WithLp.ofLp_sub,
    WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']
  norm_num
  ring

/-- Subtype-valued version of `centerVector_eq_starProjection`: the fixed
projection used in the Gaussian law theorem has centered coordinates. -/
theorem coe_orthogonalProjectionOnto_centeredSubspace {N : ℕ} (hN : 0 < N)
    (x : ObservationSpace N) :
    (((centeredSubspace N).orthogonalProjectionOnto x : centeredSubspace N) :
        ObservationSpace N) = centerVector x := by
  change (centeredSubspace N).starProjection x = centerVector x
  exact (centerVector_eq_starProjection hN x).symm

/-- The centered coordinates sum to zero. -/
theorem sum_centerVector_eq_zero {N : ℕ} (hN : 0 < N)
    (x : ObservationSpace N) : ∑ i, centerVector x i = 0 := by
  rw [← mem_centeredSubspace_iff_sum_eq_zero]
  rw [centerVector_eq_starProjection hN x]
  exact Submodule.starProjection_apply_mem _ _

/-- Orthogonal projection of a standard Gaussian column has standard
Gaussian law in the centered subspace. -/
theorem hasLaw_centerProjection_stdGaussian (N : ℕ) :
    HasLaw (centeredSubspace N).orthogonalProjectionOnto
      (stdGaussian (centeredSubspace N))
      (stdGaussian (ObservationSpace N)) :=
  hasLaw_orthogonalProjectionOnto_stdGaussian (centeredSubspace N)

/-- Apply centering independently to every one of `p` columns. -/
def centerColumns (N p : ℕ) :
    (Fin p → ObservationSpace N) → (Fin p → centeredSubspace N) :=
  fun x j ↦ (centeredSubspace N).orthogonalProjectionOnto (x j)

theorem measurable_centerColumns (N p : ℕ) : Measurable (centerColumns N p) := by
  unfold centerColumns
  fun_prop

/-- Coordinatewise centering preserves the finite product law: independent
standard Gaussian columns become independent standard Gaussian columns in the
centered subspace. -/
theorem map_centerColumns_pi_stdGaussian (N p : ℕ) :
    Measure.map (centerColumns N p)
        (Measure.pi fun _ : Fin p ↦ stdGaussian (ObservationSpace N)) =
      Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace N) := by
  let _ (j : Fin p) : IsProbabilityMeasure
      ((stdGaussian (ObservationSpace N)).map
        (centeredSubspace N).orthogonalProjectionOnto) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  change Measure.map
      (fun x : Fin p → ObservationSpace N ↦ fun j ↦
        (centeredSubspace N).orthogonalProjectionOnto (x j))
      (Measure.pi fun _ : Fin p ↦ stdGaussian (ObservationSpace N)) =
    Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace N)
  rw [Measure.pi_map_pi (fun _ ↦ (by fun_prop))]
  congr 1
  funext j
  exact (hasLaw_centerProjection_stdGaussian N).map_eq

/-- Has-law form of `map_centerColumns_pi_stdGaussian`. -/
theorem hasLaw_centerColumns_pi_stdGaussian (N p : ℕ) :
    HasLaw (centerColumns N p)
      (Measure.pi fun _ : Fin p ↦ stdGaussian (centeredSubspace N))
      (Measure.pi fun _ : Fin p ↦ stdGaussian (ObservationSpace N)) where
  aemeasurable := (measurable_centerColumns N p).aemeasurable
  map_eq := map_centerColumns_pi_stdGaussian N p

section GramInvariance

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [Fintype ι] [DecidableEq ι] in
/-- A linear isometry leaves the normalized Gram matrix unchanged. -/
theorem normalizedGram_linearIsometry (T : E →ₗᵢ[ℝ] F) (v : ι → E) :
    normalizedGram (fun i ↦ T (v i)) = normalizedGram v := by
  ext i j
  simp only [normalizedGram, Matrix.gram_apply, normalizeVector]
  rw [T.norm_map, T.norm_map, ← T.map_smul, ← T.map_smul,
    T.inner_map_map]

/-- Consequently, a linear isometry leaves the normalized Gram determinant
unchanged. -/
theorem det_normalizedGram_linearIsometry (T : E →ₗᵢ[ℝ] F) (v : ι → E) :
    (normalizedGram (fun i ↦ T (v i))).det = (normalizedGram v).det := by
  rw [normalizedGram_linearIsometry T v]

omit [Fintype ι] [DecidableEq ι] in
/-- Viewing vectors in a subspace as ambient vectors leaves their normalized
Gram matrix unchanged. -/
theorem normalizedGram_subtype_coe (K : Submodule ℝ E) (v : ι → K) :
    normalizedGram (fun i ↦ (v i : E)) = normalizedGram v := by
  simpa using normalizedGram_linearIsometry K.subtypeₗᵢ v

/-- Determinant version of `normalizedGram_subtype_coe`. -/
theorem det_normalizedGram_subtype_coe (K : Submodule ℝ E) (v : ι → K) :
    (normalizedGram (fun i ↦ (v i : E))).det = (normalizedGram v).det := by
  rw [normalizedGram_subtype_coe K v]

end GramInvariance

/-- The normalized Gram matrix computed from explicitly mean-centered ambient
columns is the same matrix as the one computed from subtype-valued orthogonal
projections. -/
theorem normalizedGram_centerColumns_ambient {N p : ℕ} (hN : 0 < N)
    (x : Fin p → ObservationSpace N) :
    normalizedGram (fun j ↦ centerVector (x j)) =
      normalizedGram (centerColumns N p x) := by
  rw [show (fun j ↦ centerVector (x j)) =
      (fun j ↦ ((centerColumns N p x j : centeredSubspace N) : ObservationSpace N)) by
    funext j
    exact (coe_orthogonalProjectionOnto_centeredSubspace hN (x j)).symm]
  exact normalizedGram_subtype_coe (centeredSubspace N) (centerColumns N p x)

/-- Determinant form of `normalizedGram_centerColumns_ambient`. -/
theorem det_normalizedGram_centerColumns_ambient {N p : ℕ} (hN : 0 < N)
    (x : Fin p → ObservationSpace N) :
    (normalizedGram (fun j ↦ centerVector (x j))).det =
      (normalizedGram (centerColumns N p x)).det := by
  rw [normalizedGram_centerColumns_ambient hN x]

end

end LogdetLean
