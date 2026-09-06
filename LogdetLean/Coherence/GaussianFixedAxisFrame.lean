import LogdetLean.Coherence.GaussianNormDirectionIndependence
import LogdetLean.Coherence.ProductMeasureReorder
import Mathlib.Tactic
/-!
# A Gaussian residual direction separated from the Ruben coordinates

For a fixed nonzero axis `u`, decompose a fresh standard Gaussian vector into
its signed axial coordinate, its orthogonal residual direction, and its
orthogonal residual energy.  This file proves the exact product law saying
that the residual direction is independent of the two scalar coordinates.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Unit direction of the Gaussian residual orthogonal to `u`, subtype-valued. -/
def gaussianAxisResidualDirectionSubtype (u v : E) : (ℝ ∙ u).orthogonal :=
  LogdetLean.unitDirection ((ℝ ∙ u).orthogonal.orthogonalProjectionOnto v)

theorem measurable_gaussianAxisResidualDirectionSubtype (u : E) :
    Measurable (gaussianAxisResidualDirectionSubtype u) := by
  unfold gaussianAxisResidualDirectionSubtype
  exact LogdetLean.measurable_unitDirection.comp
    ((ℝ ∙ u).orthogonal.orthogonalProjectionOnto.continuous.measurable)

/-- Marginal residual-direction law obtained by projecting to the orthogonal
complement and then normalizing. -/
theorem map_gaussianAxisResidualDirectionSubtype_stdGaussian (u : E) :
    Measure.map (gaussianAxisResidualDirectionSubtype u) (stdGaussian E) =
      Measure.map LogdetLean.unitDirection
        (stdGaussian ((ℝ ∙ u).orthogonal)) := by
  let K : Submodule ℝ E := ℝ ∙ u
  have hprojection :=
    LogdetLean.hasLaw_orthogonalComplementProjection_stdGaussian K
  calc
    Measure.map (gaussianAxisResidualDirectionSubtype u) (stdGaussian E) =
        Measure.map LogdetLean.unitDirection
          (Measure.map K.orthogonal.orthogonalProjectionOnto (stdGaussian E)) := by
      rw [Measure.map_map LogdetLean.measurable_unitDirection
        K.orthogonal.orthogonalProjectionOnto.continuous.measurable]
      rfl
    _ = Measure.map LogdetLean.unitDirection (stdGaussian K.orthogonal) := by
      rw [hprojection.map_eq]

/-- The residual direction together with the signed axial coordinate and
residual energy. -/
def gaussianFixedAxisFrameCoordinates (u v : E) :
    (ℝ ∙ u).orthogonal × (ℝ × ℝ) :=
  (gaussianAxisResidualDirectionSubtype u v, gaussianAxisCoordinates u v)

theorem measurable_gaussianFixedAxisFrameCoordinates (u : E) :
    Measurable (gaussianFixedAxisFrameCoordinates u) := by
  exact (measurable_gaussianAxisResidualDirectionSubtype u).prodMk
    ((measurable_uncurry_gaussianAxisCoordinates (E := E)).comp
      (measurable_const.prodMk measurable_id))

/-- Keep the signed axial coordinate together with the complete orthogonal
Gaussian residual vector. -/
def gaussianAxisCoordinateResidual (u v : E) : ℝ × (ℝ ∙ u).orthogonal :=
  (gaussianAxisCoordinate u v, (ℝ ∙ u).orthogonal.orthogonalProjectionOnto v)

theorem measurable_gaussianAxisCoordinateResidual (u : E) :
    Measurable (gaussianAxisCoordinateResidual u) := by
  exact (measurable_gaussianAxisCoordinate u).prodMk
    ((ℝ ∙ u).orthogonal.orthogonalProjectionOnto.continuous.measurable)

/-- Exact product law for the axial coordinate and the complete orthogonal
residual vector. -/
theorem map_gaussianAxisCoordinateResidual_stdGaussian
    (u : E) (hu : u ≠ 0) :
    Measure.map (gaussianAxisCoordinateResidual u) (stdGaussian E) =
      (gaussianReal 0 1).prod (stdGaussian ((ℝ ∙ u).orthogonal)) := by
  let K : Submodule ℝ E := ℝ ∙ u
  let phi : K → ℝ := fun q ↦ gaussianAxisCoordinate u (q : E)
  let psi : K.orthogonal → K.orthogonal := id
  have hcoordinate : HasLaw (gaussianAxisCoordinate u)
      (gaussianReal 0 1) (stdGaussian E) :=
    ⟨(measurable_gaussianAxisCoordinate u).aemeasurable,
      map_gaussianAxisCoordinate_stdGaussian u hu⟩
  have hresidual : HasLaw K.orthogonal.orthogonalProjectionOnto
      (stdGaussian K.orthogonal) (stdGaussian E) :=
    LogdetLean.hasLaw_orthogonalComplementProjection_stdGaussian K
  have hindepProjection :=
    LogdetLean.indepFun_orthogonalProjections_stdGaussian K
  have hindepComposed := hindepProjection.comp
    (φ := phi) (ψ := psi)
    ((measurable_gaussianAxisCoordinate u).comp measurable_subtype_coe)
    measurable_id
  have hleft :
      (phi ∘ K.orthogonalProjectionOnto) =ᵐ[stdGaussian E]
        gaussianAxisCoordinate u := by
    filter_upwards [] with v
    unfold phi gaussianAxisCoordinate
    change inner ℝ u (K.orthogonalProjectionOnto v : E) / ‖u‖ =
      inner ℝ u v / ‖u‖
    have hi := K.inner_orthogonalProjectionOnto_eq_of_mem_left
      (⟨u, Submodule.mem_span_singleton_self u⟩ : K) v
    have hi' : inner ℝ u (K.orthogonalProjectionOnto v : E) =
        inner ℝ u v := by
      simpa only [K.coe_inner] using hi
    rw [hi']
  have hright :
      (psi ∘ K.orthogonal.orthogonalProjectionOnto) =ᵐ[stdGaussian E]
        K.orthogonal.orthogonalProjectionOnto := by
    filter_upwards [] with v
    rfl
  have hindep : IndepFun (gaussianAxisCoordinate u)
      K.orthogonal.orthogonalProjectionOnto (stdGaussian E) :=
    hindepComposed.congr hleft hright
  change Measure.map (fun v ↦
      (gaussianAxisCoordinate u v, K.orthogonal.orthogonalProjectionOnto v))
      (stdGaussian E) = _
  exact (hindep.hasLaw_prod hcoordinate hresidual).map_eq

/-- Fixed-axis frame product law.  The residual direction is exactly
independent of the standard-normal axial coordinate and Gamma residual
energy. -/
theorem map_gaussianFixedAxisFrameCoordinates_stdGaussian
    (m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m)
    (u : E) (hu : u ≠ 0) :
    Measure.map (gaussianFixedAxisFrameCoordinates u) (stdGaussian E) =
      (Measure.map LogdetLean.unitDirection (stdGaussian ((ℝ ∙ u).orthogonal))).prod
        ((gaussianReal 0 1).prod
          (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2))) := by
  let K : Submodule ℝ E := ℝ ∙ u
  have hfinK : Module.finrank ℝ K = 1 := by
    simpa [K] using finrank_span_singleton hu
  have hfinPerp : Module.finrank ℝ K.orthogonal = m - 1 := by
    have hadd := K.finrank_add_finrank_orthogonal
    rw [hfinK, hdim] at hadd
    omega
  let _ : Nontrivial K.orthogonal :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ K.orthogonal)
  let dirEnergy : K.orthogonal → K.orthogonal × ℝ := gaussianDirectionEnergy
  let liftDirEnergy : ℝ × K.orthogonal → ℝ × (K.orthogonal × ℝ) :=
    Prod.map id dirEnergy
  have hdirEnergy :
      Measure.map dirEnergy (stdGaussian K.orthogonal) =
        (Measure.map LogdetLean.unitDirection (stdGaussian K.orthogonal)).prod
          (Measure.map (fun x : K.orthogonal ↦ ‖x‖ ^ 2) (stdGaussian K.orthogonal)) := by
    exact map_gaussianDirectionEnergy_stdGaussian_eq_prod (E := K.orthogonal)
  have hgamma :
      Measure.map (fun x : K.orthogonal ↦ ‖x‖ ^ 2) (stdGaussian K.orthogonal) =
        gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2) := by
    change LogdetLean.stdGaussianNormSqMeasure K.orthogonal = _
    rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma K.orthogonal, hfinPerp]
  have hshape : 0 < ((((m - 1 : ℕ) : ℝ)) / 2) := by
    have hm1 : 0 < m - 1 := by omega
    positivity
  let _ : IsProbabilityMeasure
      (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hshape (by norm_num)
  have haxisResidual := map_gaussianAxisCoordinateResidual_stdGaussian u hu
  have hlift :
      Measure.map liftDirEnergy
          ((gaussianReal 0 1).prod (stdGaussian K.orthogonal)) =
        (gaussianReal 0 1).prod
          ((Measure.map LogdetLean.unitDirection (stdGaussian K.orthogonal)).prod
            (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2))) := by
    calc
      Measure.map liftDirEnergy
          ((gaussianReal 0 1).prod (stdGaussian K.orthogonal)) =
          (Measure.map id (gaussianReal 0 1)).prod
            (Measure.map dirEnergy (stdGaussian K.orthogonal)) := by
        exact (Measure.map_prod_map _ _ measurable_id
          measurable_gaussianDirectionEnergy).symm
      _ = (gaussianReal 0 1).prod
          ((Measure.map LogdetLean.unitDirection (stdGaussian K.orthogonal)).prod
            (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2))) := by
        rw [Measure.map_id, hdirEnergy, hgamma]
  have hreorder := map_middleToFront_prod
    (gaussianReal 0 1)
    (Measure.map LogdetLean.unitDirection (stdGaussian K.orthogonal))
    (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2))
  have mlift : Measurable liftDirEnergy := by
    simpa [liftDirEnergy, dirEnergy] using
      (measurable_id.prodMap
        (measurable_gaussianDirectionEnergy (E := K.orthogonal)))
  calc
    Measure.map (gaussianFixedAxisFrameCoordinates u) (stdGaussian E) =
        Measure.map middleToFront
          (Measure.map liftDirEnergy
            (Measure.map (gaussianAxisCoordinateResidual u) (stdGaussian E))) := by
      rw [Measure.map_map measurable_middleToFront mlift,
        Measure.map_map (measurable_middleToFront.comp mlift)
          (measurable_gaussianAxisCoordinateResidual u)]
      apply Measure.map_congr
      filter_upwards [] with v
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · exact gaussianAxisResidualEnergy_eq_orthogonalProjection u v hu
    _ = Measure.map middleToFront
          (Measure.map liftDirEnergy
            ((gaussianReal 0 1).prod (stdGaussian K.orthogonal))) := by
      rw [haxisResidual]
    _ = Measure.map middleToFront
          ((gaussianReal 0 1).prod
            ((Measure.map LogdetLean.unitDirection (stdGaussian K.orthogonal)).prod
              (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2)))) := by
      rw [hlift]
    _ = (Measure.map LogdetLean.unitDirection (stdGaussian K.orthogonal)).prod
        ((gaussianReal 0 1).prod
          (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2))) := hreorder

/-- Independence form of the fixed-axis frame law. -/
theorem indepFun_gaussianAxisResidualDirection_axisCoordinates
    (m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m)
    (u : E) (hu : u ≠ 0) :
    IndepFun (gaussianAxisResidualDirectionSubtype u)
      (gaussianAxisCoordinates u) (stdGaussian E) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_gaussianAxisResidualDirectionSubtype u).aemeasurable
    ((measurable_uncurry_gaussianAxisCoordinates (E := E)).comp
      (measurable_const.prodMk measurable_id)).aemeasurable).2
  change Measure.map (gaussianFixedAxisFrameCoordinates u) (stdGaussian E) = _
  rw [map_gaussianFixedAxisFrameCoordinates_stdGaussian m hdim hm u hu]
  rw [map_gaussianAxisResidualDirectionSubtype_stdGaussian u]
  have hcoordfun :
      (Function.uncurry (gaussianAxisCoordinates (E := E)) ∘
        fun a : E ↦ (u, id a)) = gaussianAxisCoordinates u := by
    funext v
    rfl
  rw [hcoordfun,
    (hasLaw_gaussianAxisCoordinates_stdGaussian_fixed m hdim hm u hu).map_eq]

end

end LogdetLean.Coherence
