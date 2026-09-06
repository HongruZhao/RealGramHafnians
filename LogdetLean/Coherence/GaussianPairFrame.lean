import LogdetLean.Coherence.GaussianFixedAxisFrame
import LogdetLean.Coherence.VaryingProductIndependence
import Mathlib.Tactic
/-!
# The orthonormal frame of a Gaussian pair

This file passes from the subtype-valued fixed-axis statement to an ambient
two-vector frame and then lets the first Gaussian axis be random.  It proves
that the full first vector together with the residual frame direction is
independent of the two scalar Ruben coordinates of the second vector.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal residual vector written without a dependent subtype. -/
def gaussianAxisResidualVector (u v : E) : E :=
  v - gaussianAxisCoordinate u v • LogdetLean.unitDirection u

/-- Ambient unit direction of the orthogonal residual. -/
def gaussianAmbientResidualDirection (u v : E) : E :=
  LogdetLean.unitDirection (gaussianAxisResidualVector u v)

theorem measurable_uncurry_gaussianAxisResidualVector :
    Measurable (Function.uncurry (gaussianAxisResidualVector (E := E))) := by
  have hinner : Measurable (fun z : E × E ↦ inner ℝ z.1 z.2) :=
    continuous_inner.measurable
  have hcoordinate : Measurable
      (fun z : E × E ↦ gaussianAxisCoordinate z.1 z.2) := by
    exact hinner.div measurable_fst.norm
  unfold Function.uncurry gaussianAxisResidualVector
  exact measurable_snd.sub
    (hcoordinate.smul (LogdetLean.measurable_unitDirection.comp measurable_fst))

theorem measurable_uncurry_gaussianAmbientResidualDirection :
    Measurable (Function.uncurry (gaussianAmbientResidualDirection (E := E))) := by
  exact LogdetLean.measurable_unitDirection.comp
    measurable_uncurry_gaussianAxisResidualVector

/-- Unit direction commutes with the coercion of a subspace vector. -/
theorem unitDirection_subtype_coe
    {K : Submodule ℝ E} (q : K) :
    LogdetLean.unitDirection (q : E) =
      (LogdetLean.unitDirection q : K) := by
  classical
  unfold LogdetLean.unitDirection
  by_cases hq : q = 0
  · have hcoe : (q : E) = 0 := by simp [hq]
    simp [hq, hcoe]
  · have hcoe : (q : E) ≠ 0 := by
      intro h
      apply hq
      exact Subtype.ext h
    rw [if_neg hcoe, if_neg hq]
    simp

/-- The algebraic residual vector is the ambient orthogonal projection. -/
theorem gaussianAxisResidualVector_eq_orthogonalProjection
    (u v : E) (hu : u ≠ 0) :
    gaussianAxisResidualVector u v =
      (((ℝ ∙ u).orthogonal.orthogonalProjectionOnto v :
        (ℝ ∙ u).orthogonal) : E) := by
  change v - gaussianAxisCoordinate u v • LogdetLean.unitDirection u =
    (ℝ ∙ u).orthogonal.starProjection v
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton]
  unfold gaussianAxisCoordinate LogdetLean.unitDirection
  rw [if_neg hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  congr 1
  rw [smul_smul]
  congr 1
  field_simp [hn]
  norm_cast

/-- Ambient and subtype residual directions agree for a nonzero axis. -/
theorem gaussianAmbientResidualDirection_eq_subtype
    (u v : E) (hu : u ≠ 0) :
    gaussianAmbientResidualDirection u v =
      (gaussianAxisResidualDirectionSubtype u v : E) := by
  unfold gaussianAmbientResidualDirection gaussianAxisResidualDirectionSubtype
  rw [gaussianAxisResidualVector_eq_orthogonalProjection u v hu]
  exact unitDirection_subtype_coe
    ((ℝ ∙ u).orthogonal.orthogonalProjectionOnto v)

/-- For a fixed nonzero axis, the ambient residual direction is independent
of the two scalar Ruben coordinates. -/
theorem map_gaussianAmbientResidualDirection_axisCoordinates
    (m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m)
    (u : E) (hu : u ≠ 0) :
    Measure.map (fun v ↦
        (gaussianAmbientResidualDirection u v, gaussianAxisCoordinates u v))
        (stdGaussian E) =
      (Measure.map (gaussianAmbientResidualDirection u) (stdGaussian E)).prod
        ((gaussianReal 0 1).prod
          (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2))) := by
  have hshape : 0 < ((((m - 1 : ℕ) : ℝ)) / 2) := by
    have hm1 : 0 < m - 1 := by omega
    positivity
  let _ : IsProbabilityMeasure
      (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hshape (by norm_num)
  have hsub := map_gaussianFixedAxisFrameCoordinates_stdGaussian
    m hdim hm u hu
  let coeFirst : (ℝ ∙ u).orthogonal × (ℝ × ℝ) →
      E × (ℝ × ℝ) := Prod.map Subtype.val id
  have hcoeFirst : Measurable coeFirst := measurable_subtype_coe.prodMap measurable_id
  have hpair :
      Measure.map (fun v ↦
          ((gaussianAxisResidualDirectionSubtype u v : E),
            gaussianAxisCoordinates u v)) (stdGaussian E) =
        (Measure.map (fun q : (ℝ ∙ u).orthogonal ↦ (q : E))
            (Measure.map LogdetLean.unitDirection
              (stdGaussian ((ℝ ∙ u).orthogonal)))).prod
          ((gaussianReal 0 1).prod
            (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2))) := by
    calc
      Measure.map (fun v ↦
          ((gaussianAxisResidualDirectionSubtype u v : E),
            gaussianAxisCoordinates u v)) (stdGaussian E) =
          Measure.map coeFirst
            (Measure.map (gaussianFixedAxisFrameCoordinates u) (stdGaussian E)) := by
        rw [Measure.map_map hcoeFirst
          (measurable_gaussianFixedAxisFrameCoordinates u)]
        rfl
      _ = Measure.map coeFirst
          ((Measure.map LogdetLean.unitDirection
              (stdGaussian ((ℝ ∙ u).orthogonal))).prod
            ((gaussianReal 0 1).prod
              (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2)))) := by
        rw [hsub]
      _ = _ := by
        simpa [coeFirst] using
          (Measure.map_prod_map
            (Measure.map LogdetLean.unitDirection
              (stdGaussian ((ℝ ∙ u).orthogonal)))
            ((gaussianReal 0 1).prod
              (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2)))
            measurable_subtype_coe measurable_id).symm
  have hambient :
      (fun v ↦ (gaussianAmbientResidualDirection u v,
        gaussianAxisCoordinates u v)) =ᵐ[stdGaussian E]
      (fun v ↦ ((gaussianAxisResidualDirectionSubtype u v : E),
        gaussianAxisCoordinates u v)) := by
    filter_upwards [] with v
    rw [gaussianAmbientResidualDirection_eq_subtype u v hu]
  have hfirst :
    Measure.map (gaussianAmbientResidualDirection u) (stdGaussian E) =
        Measure.map (fun q : (ℝ ∙ u).orthogonal ↦ (q : E))
          (Measure.map LogdetLean.unitDirection
            (stdGaussian ((ℝ ∙ u).orthogonal))) := by
    calc
      Measure.map (gaussianAmbientResidualDirection u) (stdGaussian E) =
          Measure.map (fun q : (ℝ ∙ u).orthogonal ↦ (q : E))
            (Measure.map (gaussianAxisResidualDirectionSubtype u)
              (stdGaussian E)) := by
        rw [Measure.map_map measurable_subtype_coe
          (measurable_gaussianAxisResidualDirectionSubtype u)]
        apply Measure.map_congr
        filter_upwards [] with v
        exact gaussianAmbientResidualDirection_eq_subtype u v hu
    _ = _ := by
      rw [map_gaussianAxisResidualDirectionSubtype_stdGaussian u]
  rw [Measure.map_congr hambient, hpair, hfirst]

/-- With a random first Gaussian vector, its full value and the residual
direction are jointly independent of the axial coordinate and residual
energy of the second Gaussian vector. -/
theorem indepFun_firstAndResidualDirection_axisCoordinates_gaussianProduct
    (m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun
      (fun p : E × E ↦ (p.1, gaussianAmbientResidualDirection p.1 p.2))
      (fun p : E × E ↦ gaussianAxisCoordinates p.1 p.2)
      ((stdGaussian E).prod (stdGaussian E)) := by
  let tau : Measure (ℝ × ℝ) :=
    (gaussianReal 0 1).prod
      (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2))
  have hshape : 0 < ((((m - 1 : ℕ) : ℝ)) / 2) := by
    have hm1 : 0 < m - 1 := by omega
    positivity
  let _ : IsProbabilityMeasure
      (gammaMeasure ((((m - 1 : ℕ) : ℝ)) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hshape (by norm_num)
  let _ : IsProbabilityMeasure tau := by
    dsimp [tau]
    infer_instance
  have hnonzero : ∀ᵐ u ∂stdGaussian E, u ≠ 0 := by
    let _ : Nontrivial E :=
      Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
    simpa [ae_iff] using LogdetLean.stdGaussian_zero_singleton (E := E)
  have hlaw : ∀ᵐ u ∂stdGaussian E,
      Measure.map (fun v ↦
          (gaussianAmbientResidualDirection u v,
            gaussianAxisCoordinates u v)) (stdGaussian E) =
        (Measure.map (gaussianAmbientResidualDirection u) (stdGaussian E)).prod
          tau := by
    filter_upwards [hnonzero] with u hu
    exact map_gaussianAmbientResidualDirection_axisCoordinates
      m hdim hm u hu
  exact indepFun_baseFirst_second_of_conditional_products
    (stdGaussian E) (stdGaussian E) tau
    gaussianAmbientResidualDirection gaussianAxisCoordinates
    measurable_uncurry_gaussianAmbientResidualDirection
    measurable_uncurry_gaussianAxisCoordinates hlaw

/-- The orthonormal two-frame extracted from a Gaussian pair. -/
def gaussianPairFrame (p : E × E) : E × E :=
  (LogdetLean.unitDirection p.1,
    gaussianAmbientResidualDirection p.1 p.2)

theorem measurable_gaussianPairFrame :
    Measurable (gaussianPairFrame : E × E → E × E) := by
  exact (LogdetLean.measurable_unitDirection.comp measurable_fst).prodMk
    measurable_uncurry_gaussianAmbientResidualDirection

/-- Replacing a nonzero axis by its unit direction does not alter the
orthogonal residual direction. -/
theorem gaussianAmbientResidualDirection_unitDirection_left
    (u v : E) (hu : u ≠ 0) :
    gaussianAmbientResidualDirection (LogdetLean.unitDirection u) v =
      gaussianAmbientResidualDirection u v := by
  classical
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hunit : LogdetLean.unitDirection u = ‖u‖⁻¹ • u := by
    simp [LogdetLean.unitDirection, hu]
  have hunitne : LogdetLean.unitDirection u ≠ 0 := by
    rw [hunit]
    exact smul_ne_zero (inv_ne_zero hn) hu
  have hnormUnit : ‖LogdetLean.unitDirection u‖ = 1 := by
    rw [hunit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hn]
  have hunitUnit :
      LogdetLean.unitDirection (LogdetLean.unitDirection u) =
        LogdetLean.unitDirection u := by
    change (if LogdetLean.unitDirection u = 0 then 0 else
      ‖LogdetLean.unitDirection u‖⁻¹ • LogdetLean.unitDirection u) =
        LogdetLean.unitDirection u
    rw [if_neg hunitne, hnormUnit]
    simp
  unfold gaussianAmbientResidualDirection gaussianAxisResidualVector
  congr 1
  unfold gaussianAxisCoordinate
  rw [hnormUnit, hunitUnit, hunit]
  simp only [div_one, inner_smul_left, RCLike.ofReal_real_eq_id, id_eq,
    smul_smul]
  congr 1
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- Put a Gaussian pair into `(direction, second vector; radius)` order. -/
def gaussianPairPolarReorder (p : E × E) : (E × E) × ℝ :=
  ((LogdetLean.unitDirection p.1, p.2), ‖p.1‖)

theorem measurable_gaussianPairPolarReorder :
    Measurable (gaussianPairPolarReorder : E × E → (E × E) × ℝ) := by
  exact ((LogdetLean.measurable_unitDirection.comp measurable_fst).prodMk
    measurable_snd).prodMk measurable_fst.norm

/-- Exact law of the reordered Gaussian polar pair. -/
theorem map_gaussianPairPolarReorder_gaussianProduct [Nontrivial E] :
    Measure.map (gaussianPairPolarReorder : E × E → (E × E) × ℝ)
        ((stdGaussian E).prod (stdGaussian E)) =
      ((Measure.map LogdetLean.unitDirection (stdGaussian E)).prod
        (stdGaussian E)).prod (Measure.map norm (stdGaussian E)) := by
  let firstPolarSecond : E × E → (E × ℝ) × E :=
    Prod.map gaussianNormDirection id
  have hfirst : Measurable firstPolarSecond :=
    measurable_gaussianNormDirection.prodMap measurable_id
  have hmapFirst :
      Measure.map firstPolarSecond ((stdGaussian E).prod (stdGaussian E)) =
        (Measure.map gaussianNormDirection (stdGaussian E)).prod
          (Measure.map id (stdGaussian E)) := by
    exact (Measure.map_prod_map _ _ measurable_gaussianNormDirection measurable_id).symm
  have hfun :
      (gaussianPairPolarReorder : E × E → (E × E) × ℝ) =
        middleToLast ∘ firstPolarSecond := by
    funext p
    rfl
  calc
    Measure.map (gaussianPairPolarReorder : E × E → (E × E) × ℝ)
        ((stdGaussian E).prod (stdGaussian E)) =
        Measure.map middleToLast
          (Measure.map firstPolarSecond ((stdGaussian E).prod (stdGaussian E))) := by
      rw [hfun, Measure.map_map measurable_middleToLast hfirst]
    _ = Measure.map middleToLast
        ((Measure.map gaussianNormDirection (stdGaussian E)).prod
          (Measure.map id (stdGaussian E))) := by rw [hmapFirst]
    _ = Measure.map middleToLast
        (((Measure.map LogdetLean.unitDirection (stdGaussian E)).prod
          (Measure.map norm (stdGaussian E))).prod (stdGaussian E)) := by
      rw [map_gaussianNormDirection_stdGaussian_eq_prod, Measure.map_id]
    _ = ((Measure.map LogdetLean.unitDirection (stdGaussian E)).prod
        (stdGaussian E)).prod (Measure.map norm (stdGaussian E)) := by
      exact map_middleToLast_prod
        (Measure.map LogdetLean.unitDirection (stdGaussian E))
        (Measure.map norm (stdGaussian E)) (stdGaussian E)

/-- The Gaussian two-frame is independent of the first radial norm. -/
theorem indepFun_gaussianPairFrame_firstNorm_gaussianProduct
    (m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun gaussianPairFrame (fun p : E × E ↦ ‖p.1‖)
      ((stdGaussian E).prod (stdGaussian E)) := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  let dirLaw : Measure E :=
    Measure.map LogdetLean.unitDirection (stdGaussian E)
  let radialLaw : Measure ℝ := Measure.map norm (stdGaussian E)
  let baseLaw : Measure (E × E) := dirLaw.prod (stdGaussian E)
  let targetLaw : Measure ((E × E) × ℝ) := baseLaw.prod radialLaw
  let frameFromBase : E × E → E × E :=
    fun q ↦ (q.1, gaussianAmbientResidualDirection q.1 q.2)
  let Xtarget : (E × E) × ℝ → E × E :=
    fun q ↦ frameFromBase q.1
  let Ytarget : (E × E) × ℝ → ℝ := Prod.snd
  have hframeBase : Measurable frameFromBase := by
    exact measurable_fst.prodMk measurable_uncurry_gaussianAmbientResidualDirection
  have hX : Measurable Xtarget := hframeBase.comp measurable_fst
  have hY : Measurable Ytarget := measurable_snd
  let _ : IsProbabilityMeasure dirLaw := by
    dsimp [dirLaw]
    exact Measure.isProbabilityMeasure_map
      LogdetLean.measurable_unitDirection.aemeasurable
  let _ : IsProbabilityMeasure radialLaw := by
    dsimp [radialLaw]
    exact Measure.isProbabilityMeasure_map measurable_id.norm.aemeasurable
  let _ : IsProbabilityMeasure baseLaw := Measure.prod.instIsProbabilityMeasure _ _
  let _ : IsProbabilityMeasure targetLaw := Measure.prod.instIsProbabilityMeasure _ _
  have htarget : IndepFun Xtarget Ytarget targetLaw := by
    simpa [Xtarget, Ytarget, targetLaw] using
      (indepFun_prod (μ := baseLaw) (ν := radialLaw) hframeBase measurable_id)
  have hmap : Measure.map gaussianPairPolarReorder
      ((stdGaussian E).prod (stdGaussian E)) = targetLaw := by
    simpa [targetLaw, baseLaw, dirLaw, radialLaw] using
      (map_gaussianPairPolarReorder_gaussianProduct (E := E))
  have htransport := indepFun_comp_of_map_eq htarget
    measurable_gaussianPairPolarReorder hX hY hmap
  have hnonzero : ∀ᵐ u ∂stdGaussian E, u ≠ 0 := by
    simpa [ae_iff] using LogdetLean.stdGaussian_zero_singleton (E := E)
  have hnonzeroProd : ∀ᵐ p ∂(stdGaussian E).prod (stdGaussian E), p.1 ≠ 0 := by
    exact (measurePreserving_fst (μ := stdGaussian E)
      (ν := stdGaussian E)).quasiMeasurePreserving.ae hnonzero
  refine htransport.congr ?_ ?_
  · filter_upwards [hnonzeroProd] with p hp
    change (Xtarget ∘ gaussianPairPolarReorder) p = gaussianPairFrame p
    unfold gaussianPairFrame Xtarget frameFromBase gaussianPairPolarReorder
    simp only [Function.comp_apply]
    rw [gaussianAmbientResidualDirection_unitDirection_left p.1 p.2 hp]
  · filter_upwards [] with p
    rfl

/-- Complete two-frame/Ruben separation: the Gaussian two-frame is
independent of the first norm, axial coordinate, and residual energy. -/
theorem indepFun_gaussianPairFrame_gaussianRubenCoordinates
    (m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun gaussianPairFrame gaussianRubenCoordinates
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hframeNorm :=
    indepFun_gaussianPairFrame_firstNorm_gaussianProduct m hdim hm
  have hfullScalar :=
    indepFun_firstAndResidualDirection_axisCoordinates_gaussianProduct m hdim hm
  let bundleFrameNorm : (E × E) → (E × E) × ℝ :=
    fun p ↦ (gaussianPairFrame p, ‖p.1‖)
  have hpairScalar : IndepFun bundleFrameNorm
      (fun p : E × E ↦ gaussianAxisCoordinates p.1 p.2)
      ((stdGaussian E).prod (stdGaussian E)) := by
    have hcomp := hfullScalar.comp
      (φ := fun q : E × E ↦ ((LogdetLean.unitDirection q.1, q.2), ‖q.1‖))
      (ψ := id)
      (((LogdetLean.measurable_unitDirection.comp measurable_fst).prodMk
        measurable_snd).prodMk measurable_fst.norm) measurable_id
    simpa [bundleFrameNorm, gaussianPairFrame, Function.comp_def] using hcomp
  have hresult := IndepFun.left_pair_of_pair_left hframeNorm hpairScalar
    measurable_gaussianPairFrame measurable_fst.norm
    measurable_uncurry_gaussianAxisCoordinates
  change IndepFun gaussianPairFrame
    (fun p : E × E ↦ (‖p.1‖, gaussianAxisCoordinates p.1 p.2))
    ((stdGaussian E).prod (stdGaussian E))
  simpa [gaussianRubenCoordinates] using hresult

end

end LogdetLean.Coherence
