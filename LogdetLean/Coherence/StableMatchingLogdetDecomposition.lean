import LogdetLean.Coherence.StableMatchingRawLaw
import LogdetLean.Coherence.StableMatchingCentralAngle
import LogdetLean.WishartSequentialKernel
import Mathlib.Tactic
/-!
# Exact null log-determinant/frame decomposition for a stable matching

The full iid Gaussian null determinant is decomposed into an orientation
term and the centered internal log angles of the distinguished pairs.  The
orientation term is exactly independent of the complete planted-block Ruben
coordinates; the internal centered sum is negligible under balanced scaling.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real
open scoped BigOperators RealInnerProductSpace Topology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Positivity of a normalized-Gram determinant for an arbitrary finite
index type. -/
theorem det_normalizedGram_pos_of_linearIndependent_finite
    {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → E) (hv : LinearIndependent ℝ v) :
    0 < (normalizedGram v).det := by
  have hgram : 0 < (Matrix.gram ℝ v).det :=
    ((Matrix.posSemidef_gram ℝ v).posDef_iff_det_ne_zero.mpr
      (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv)).det_pos
  have hnorm : 0 < ∏ i, ‖v i‖ ^ 2 := by
    exact Finset.prod_pos fun i _ ↦
      pow_pos (norm_pos_iff.mpr (hv.ne_zero i)) 2
  rw [det_normalizedGram]
  exact div_pos hgram hnorm

/-- A linearly independent pair has nonzero orthogonal residual. -/
theorem gaussianAxisResidualVector_ne_zero_of_pair_linearIndependent
    (x e : E)
    (hli : LinearIndependent ℝ (fun i : Fin 2 ↦ if i = 0 then x else e)) :
    gaussianAxisResidualVector x e ≠ 0 := by
  intro hres
  have hx : x ≠ 0 := by
    simpa using hli.ne_zero (0 : Fin 2)
  have heq : e = gaussianAxisCoordinate x e • LogdetLean.unitDirection x := by
    unfold gaussianAxisResidualVector at hres
    exact sub_eq_zero.mp hres
  have hunit : LogdetLean.unitDirection x = ‖x‖⁻¹ • x :=
    unitDirection_eq_inv_norm_smul x hx
  have heq' : (1 : ℝ) • e =
      (gaussianAxisCoordinate x e * ‖x‖⁻¹) • x := by
    calc
      (1 : ℝ) • e = e := one_smul ℝ e
      _ = gaussianAxisCoordinate x e • LogdetLean.unitDirection x := heq
      _ = (gaussianAxisCoordinate x e * ‖x‖⁻¹) • x := by
        rw [hunit, smul_smul]
  have hind := hli.eq_of_smul_apply_eq_smul_apply
    (1 : ℝ) (gaussianAxisCoordinate x e * ‖x‖⁻¹)
    (1 : Fin 2) (0 : Fin 2) one_ne_zero
  have : (1 : Fin 2) = 0 := by
    apply hind
    simpa using heq'
  norm_num at this

/-- A linearly independent pair has a strict internal sample correlation. -/
theorem abs_signedNormalizedInner_lt_one_of_pair_linearIndependent
    (x e : E)
    (hli : LinearIndependent ℝ (fun i : Fin 2 ↦ if i = 0 then x else e)) :
    |signedNormalizedInner x e| < 1 := by
  have hx : x ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
  have he : e ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
  have hres := gaussianAxisResidualVector_ne_zero_of_pair_linearIndependent
    x e hli
  have hresEnergy : 0 < gaussianAxisResidualEnergy x e := by
    rw [gaussianAxisResidualEnergy_eq_orthogonalProjection x e hx]
    have hproj : (Submodule.orthogonalProjectionOnto (ℝ ∙ x)ᗮ e) ≠ 0 := by
      intro hp
      apply hres
      rw [gaussianAxisResidualVector_eq_orthogonalProjection x e hx]
      simp [hp]
    exact sq_pos_of_pos (norm_pos_iff.mpr hproj)
  have hfrac : 0 < 1 - signedNormalizedInner x e ^ 2 := by
    rw [← residualEnergy_div_normSq_eq_one_sub_signedNormalizedInner_sq
      x e hx he]
    exact div_pos hresEnergy (sq_pos_of_pos (norm_pos_iff.mpr he))
  exact (sq_lt_one_iff_abs_lt_one _).mp (by linarith)

/-- Restrict a linearly independent matching family to one distinguished
two-column block. -/
theorem stableMatching_pair_linearIndependent
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hv : LinearIndependent ℝ v) (e : Fin s) :
    LinearIndependent ℝ (fun i : Fin 2 ↦
      if i = 0 then v (Sum.inl (0, e)) else v (Sum.inl (1, e))) := by
  let f : Fin 2 → Sum (Fin 2 × Fin s) (Fin r) :=
    fun i ↦ Sum.inl (i, e)
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f, Sum.inl.injEq, Prod.mk.injEq] at hij
    exact hij.1
  have hcomp := hv.comp f hf
  have heq : v ∘ f = fun i : Fin 2 ↦
      if i = 0 then v (Sum.inl (0, e)) else v (Sum.inl (1, e)) := by
    funext i
    fin_cases i <;> rfl
  rw [← heq]
  exact hcomp

/-- Null log determinant on the stable-matching base sample. -/
def stableMatchingNullLogdet (s r : ℕ)
    (w : StableMatchingBaseSample E s r) : ℝ :=
  Real.log (normalizedGram (stableMatchingRawColumns s r w)).det

theorem measurable_stableMatchingNullLogdet (s r : ℕ) :
    Measurable (stableMatchingNullLogdet (E := E) s r) := by
  unfold stableMatchingNullLogdet
  exact ((measurable_det_normalizedGram_stableMatchingIndex
    (E := E) s r).log).comp (measurable_stableMatchingRawColumns s r)

/-- Standardized null determinant written on the grouped base sample. -/
def stableMatchingNullZ0 (m s r : ℕ)
    (w : StableMatchingBaseSample E s r) : ℝ :=
  (stableMatchingNullLogdet s r w - nullCenter m (2 * s + r)) /
    Real.sqrt (nullVSeries m (2 * s + r))

theorem measurable_stableMatchingNullZ0 (m s r : ℕ) :
    Measurable (stableMatchingNullZ0 (E := E) m s r) := by
  unfold stableMatchingNullZ0
  exact ((measurable_stableMatchingNullLogdet s r).sub measurable_const).div
    measurable_const

/-- The centered orientation/frame coordinate.  The added `s`-fold edge
mean is exactly the center removed from the internal pair angles. -/
def stableMatchingFrameZ0 (m s r : ℕ)
    (w : StableMatchingBaseSample E s r) : ℝ :=
  (stableMatchingFrameLogdet s r w - nullCenter m (2 * s + r) -
      (s : ℝ) * oneEdgeLogMean (1 / 2)
        (((m - 1 : ℕ) : ℝ) / 2)) /
    Real.sqrt (nullVSeries m (2 * s + r))

theorem measurable_stableMatchingFrameZ0 (m s r : ℕ) :
    Measurable (stableMatchingFrameZ0 (E := E) m s r) := by
  unfold stableMatchingFrameZ0
  exact (((measurable_stableMatchingFrameLogdet s r).sub measurable_const).sub
    measurable_const).div measurable_const

/-- The frame coordinate is exactly independent of all planted-block Ruben
coordinates. -/
theorem indepFun_stableMatchingFrameZ0_rubenData
    (s r m : ℕ) (hdim : Module.finrank ℝ E = m) (hm : 2 ≤ m) :
    IndepFun (stableMatchingFrameZ0 (E := E) m s r)
      (stableMatchingRubenData (E := E) s r)
      (stableMatchingBaseMeasure E s r) := by
  have hg : Measurable (fun x : ℝ ↦
      (x - nullCenter m (2 * s + r) -
          (s : ℝ) * oneEdgeLogMean (1 / 2)
            (((m - 1 : ℕ) : ℝ) / 2)) /
        Real.sqrt (nullVSeries m (2 * s + r))) := by fun_prop
  exact (indepFun_stableMatchingFrameLogdet_rubenData
    (E := E) s r m hdim hm).comp hg measurable_id

/-- Exact pointwise decomposition on every linearly independent base family. -/
theorem stableMatchingNullZ0_eq_frame_add_centralAngle
    (m s r : ℕ) (w : StableMatchingBaseSample E s r)
    (hw : LinearIndependent ℝ (stableMatchingRawColumns s r w)) :
    stableMatchingNullZ0 m s r w =
      stableMatchingFrameZ0 m s r w +
        stableMatchingCentralAngleCorrection m (2 * s + r) s w.1 := by
  let v := stableMatchingRawColumns s r w
  have hv : ∀ i, v i ≠ 0 := fun i ↦ hw.ne_zero i
  have hpair : ∀ e, LinearIndependent ℝ (fun i : Fin 2 ↦
      if i = 0 then v (Sum.inl (0, e)) else v (Sum.inl (1, e))) :=
    fun e ↦ stableMatching_pair_linearIndependent s r v hw e
  have hres : ∀ e, gaussianAxisResidualVector
      (v (Sum.inl (0, e))) (v (Sum.inl (1, e))) ≠ 0 :=
    fun e ↦ gaussianAxisResidualVector_ne_zero_of_pair_linearIndependent
      _ _ (hpair e)
  have hr : ∀ e, |stableMatchingInternalCorrelation s r v e| < 1 := by
    intro e
    exact abs_signedNormalizedInner_lt_one_of_pair_linearIndependent
      _ _ (hpair e)
  have hfullDet : 0 < (normalizedGram v).det :=
    det_normalizedGram_pos_of_linearIndependent_finite v hw
  have hprodPos : 0 < ∏ e,
      (1 - stableMatchingInternalCorrelation s r v e ^ 2) :=
    Finset.prod_pos fun e _ ↦
      sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 (hr e))
  have hfactor := det_normalizedGram_eq_internal_prod_mul_frameDet
    s r v hv hres hr
  have hframeDet : 0 <
      (normalizedGram (stableMatchingFrameFamily s r v)).det := by
    rw [hfactor] at hfullDet
    exact pos_of_mul_pos_right hfullDet hprodPos.le
  have hlog := logdet_normalizedGram_eq_frame_add_internal_sum
    s r v hv hres hr hframeDet
  have hframeEq := stableMatchingFrameColumns_frameData_eq_frameFamily
    (E := E) s r w
  unfold stableMatchingNullZ0 stableMatchingFrameZ0
    stableMatchingCentralAngleCorrection stableMatchingNullLogdet
    stableMatchingFrameLogdet
  rw [show stableMatchingRawColumns s r w = v by rfl, hlog]
  rw [hframeEq]
  have hinter : ∀ e,
      stableMatchingInternalCorrelation s r v e ^ 2 =
        squaredNormalizedInner (w.1 e).1 (w.1 e).2 := by
    intro e
    simpa [v, stableMatchingRawColumns,
      stableMatchingInternalCorrelation] using
      signedNormalizedInner_sq (w.1 e).1 (w.1 e).2
  simp_rw [hinter]
  unfold oneEdgeCenteredPrefix oneEdgeLogLoss
  simp_rw [sub_neg_eq_add]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- Almost-sure form of the exact null decomposition. -/
theorem ae_stableMatchingNullZ0_eq_frame_add_centralAngle
    (s r m : ℕ) (hdim : Module.finrank ℝ E = m)
    (hcols : 2 * s + r ≤ m) :
    stableMatchingNullZ0 (E := E) m s r =ᵐ[stableMatchingBaseMeasure E s r]
      fun w ↦ stableMatchingFrameZ0 m s r w +
        stableMatchingCentralAngleCorrection m (2 * s + r) s w.1 := by
  filter_upwards [ae_linearIndependent_stableMatchingRawColumns
    (E := E) s r m hdim hcols] with w hw
  exact stableMatchingNullZ0_eq_frame_add_centralAngle m s r w hw

end

end LogdetLean.Coherence
