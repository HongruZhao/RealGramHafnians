import LogdetLean.Coherence.GaussianPairFrame
import LogdetLean.Coherence.StableMatchingBlockTransform
import Mathlib.Tactic
/-!
# Deterministic algebra of the Gaussian pair frame

For a nondegenerate pair `(x,e)`, write `u=x/||x||`, let `w` be the unit
direction of the component of `e` orthogonal to `x`, and let

`r = <x,e> / (||x|| ||e||)`.

This file proves that the normalized raw pair is obtained from the
orthonormal frame `(u,w)` by the triangular correlation block with parameter
`r`.  This is the deterministic bridge that isolates the internal sample
correlation from the cross-block geometry.
-/

namespace LogdetLean.Coherence

noncomputable section

open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Signed normalized inner product, totalized at zero. -/
def signedNormalizedInner (x e : E) : ℝ :=
  inner ℝ x e / (‖x‖ * ‖e‖)

theorem signedNormalizedInner_sq (x e : E) :
    signedNormalizedInner x e ^ 2 = squaredNormalizedInner x e := by
  unfold signedNormalizedInner squaredNormalizedInner
  ring

theorem norm_unitDirection_of_ne (x : E) (hx : x ≠ 0) :
    ‖LogdetLean.unitDirection x‖ = 1 := by
  unfold LogdetLean.unitDirection
  rw [if_neg hx, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem unitDirection_eq_inv_norm_smul (x : E) (hx : x ≠ 0) :
    LogdetLean.unitDirection x = ‖x‖⁻¹ • x := by
  simp [LogdetLean.unitDirection, hx]

theorem inner_unitDirection_gaussianAmbientResidualDirection
    (x e : E) (hx : x ≠ 0) :
    inner ℝ (LogdetLean.unitDirection x)
      (gaussianAmbientResidualDirection x e) = 0 := by
  rw [gaussianAmbientResidualDirection_eq_subtype x e hx]
  let q := gaussianAxisResidualDirectionSubtype x e
  have hq : (q : E) ∈ (ℝ ∙ x).orthogonal := q.2
  have hxmem : LogdetLean.unitDirection x ∈ ℝ ∙ x := by
    rw [unitDirection_eq_inv_norm_smul x hx]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  exact Submodule.inner_right_of_mem_orthogonal hxmem hq

theorem norm_gaussianAmbientResidualDirection_of_ne
    (x e : E) (hx : x ≠ 0) (hres : gaussianAxisResidualVector x e ≠ 0) :
    ‖gaussianAmbientResidualDirection x e‖ = 1 := by
  unfold gaussianAmbientResidualDirection
  exact norm_unitDirection_of_ne _ hres

/-- Pythagorean identity for the Gaussian axis decomposition. -/
theorem normSq_eq_axisCoordinate_sq_add_residualEnergy
    (x e : E) :
    ‖e‖ ^ 2 = gaussianAxisCoordinate x e ^ 2 +
      gaussianAxisResidualEnergy x e := by
  unfold gaussianAxisResidualEnergy
  ring

/-- The signed raw correlation is the axial coordinate divided by the second
radius. -/
theorem signedNormalizedInner_eq_axisCoordinate_div_norm
    (x e : E) (hx : x ≠ 0) :
    signedNormalizedInner x e = gaussianAxisCoordinate x e / ‖e‖ := by
  unfold signedNormalizedInner gaussianAxisCoordinate
  field_simp [norm_ne_zero_iff.mpr hx]

/-- Squared residual fraction equals one minus the squared signed
correlation. -/
theorem residualEnergy_div_normSq_eq_one_sub_signedNormalizedInner_sq
    (x e : E) (hx : x ≠ 0) (he : e ≠ 0) :
    gaussianAxisResidualEnergy x e / ‖e‖ ^ 2 =
      1 - signedNormalizedInner x e ^ 2 := by
  rw [signedNormalizedInner_eq_axisCoordinate_div_norm x e hx]
  have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
  rw [div_pow]
  unfold gaussianAxisResidualEnergy
  field_simp [hne]

theorem sqrt_residualEnergy_div_norm_eq_sqrt_one_sub_signedNormalizedInner_sq
    (x e : E) (hx : x ≠ 0) (he : e ≠ 0) :
    Real.sqrt (gaussianAxisResidualEnergy x e) / ‖e‖ =
      Real.sqrt (1 - signedNormalizedInner x e ^ 2) := by
  have hresEnergy : 0 ≤ gaussianAxisResidualEnergy x e := by
    rw [gaussianAxisResidualEnergy_eq_orthogonalProjection x e hx]
    positivity
  calc
    Real.sqrt (gaussianAxisResidualEnergy x e) / ‖e‖ =
        Real.sqrt (gaussianAxisResidualEnergy x e) /
          Real.sqrt (‖e‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg e)]
    _ = Real.sqrt (gaussianAxisResidualEnergy x e / ‖e‖ ^ 2) := by
      rw [Real.sqrt_div hresEnergy]
    _ = Real.sqrt (1 - signedNormalizedInner x e ^ 2) := by
      rw [residualEnergy_div_normSq_eq_one_sub_signedNormalizedInner_sq
        x e hx he]

/-- The normalized raw second vector decomposes in the orthonormal pair
frame. -/
theorem normalizeVector_eq_pairFrame_decomposition
    (x e : E) (hx : x ≠ 0) (he : e ≠ 0)
    (hres : gaussianAxisResidualVector x e ≠ 0) :
    LogdetLean.normalizeVector e =
      signedNormalizedInner x e • LogdetLean.unitDirection x +
        (Real.sqrt (gaussianAxisResidualEnergy x e) / ‖e‖) •
          gaussianAmbientResidualDirection x e := by
  have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hresEnergy : 0 ≤ gaussianAxisResidualEnergy x e := by
    rw [gaussianAxisResidualEnergy_eq_orthogonalProjection x e hx]
    positivity
  have hresNorm : ‖gaussianAxisResidualVector x e‖ =
      Real.sqrt (gaussianAxisResidualEnergy x e) := by
    rw [gaussianAxisResidualVector_eq_orthogonalProjection x e hx,
      gaussianAxisResidualEnergy_eq_orthogonalProjection x e hx,
      Submodule.coe_norm, Real.sqrt_sq_eq_abs, abs_norm]
  have hsplit : e = gaussianAxisCoordinate x e •
        LogdetLean.unitDirection x + gaussianAxisResidualVector x e := by
    unfold gaussianAxisResidualVector
    abel
  have hnormSplit :
      ‖gaussianAxisCoordinate x e • LogdetLean.unitDirection x +
          gaussianAxisResidualVector x e‖ = ‖e‖ := by
    rw [← hsplit]
  unfold LogdetLean.normalizeVector
  calc
    ‖e‖⁻¹ • e =
        (‖e‖⁻¹ * gaussianAxisCoordinate x e) •
            LogdetLean.unitDirection x +
          ‖e‖⁻¹ • gaussianAxisResidualVector x e := by
      conv_lhs => rw [hsplit]
      rw [hnormSplit, smul_add, smul_smul]
    _ = signedNormalizedInner x e • LogdetLean.unitDirection x +
        (Real.sqrt (gaussianAxisResidualEnergy x e) / ‖e‖) •
          gaussianAmbientResidualDirection x e := by
      congr 1
      · rw [signedNormalizedInner_eq_axisCoordinate_div_norm x e hx]
        ring
      · unfold gaussianAmbientResidualDirection LogdetLean.unitDirection
        rw [if_neg hres, hresNorm]
        have hsqrt : Real.sqrt (gaussianAxisResidualEnergy x e) ≠ 0 := by
          rw [← hresNorm]
          exact norm_ne_zero_iff.mpr hres
        rw [smul_smul]
        congr 1
        field_simp [hne, hsqrt]

/-- The preceding decomposition is exactly the triangular pair-mixing map. -/
theorem normalizeVector_eq_correlatedSecondColumn_pairFrame
    (x e : E) (hx : x ≠ 0) (he : e ≠ 0)
    (hres : gaussianAxisResidualVector x e ≠ 0) :
    LogdetLean.normalizeVector e =
      correlatedSecondColumn (signedNormalizedInner x e)
        (LogdetLean.unitDirection x)
        (gaussianAmbientResidualDirection x e) := by
  rw [normalizeVector_eq_pairFrame_decomposition x e hx he hres,
    sqrt_residualEnergy_div_norm_eq_sqrt_one_sub_signedNormalizedInner_sq
      x e hx he]
  rfl

theorem normalizeVector_unitDirection_of_ne (x : E) (hx : x ≠ 0) :
    LogdetLean.normalizeVector (LogdetLean.unitDirection x) =
      LogdetLean.unitDirection x := by
  unfold LogdetLean.normalizeVector
  rw [norm_unitDirection_of_ne x hx]
  simp

theorem normalizeVector_eq_unitDirection_of_ne (x : E) (hx : x ≠ 0) :
    LogdetLean.normalizeVector x = LogdetLean.unitDirection x := by
  unfold LogdetLean.normalizeVector
  exact (unitDirection_eq_inv_norm_smul x hx).symm

theorem normalizedGram_normalizeVector_family
    {I : Type*} [Fintype I]
    (v : I → E) (hv : ∀ i, v i ≠ 0) :
    normalizedGram (fun i ↦ LogdetLean.normalizeVector (v i)) =
      normalizedGram v := by
  unfold normalizedGram
  congr 1
  funext i
  calc
    LogdetLean.normalizeVector (LogdetLean.normalizeVector (v i)) =
        LogdetLean.normalizeVector (LogdetLean.unitDirection (v i)) := by
      rw [normalizeVector_eq_unitDirection_of_ne (v i) (hv i)]
    _ = LogdetLean.unitDirection (v i) :=
      normalizeVector_unitDirection_of_ne (v i) (hv i)
    _ = LogdetLean.normalizeVector (v i) :=
      (normalizeVector_eq_unitDirection_of_ne (v i) (hv i)).symm

/-! ## A finite family of disjoint pair frames -/

/-- Replace every distinguished raw pair by its orthonormal frame and every
singleton by its unit direction. -/
def stableMatchingFrameFamily (s r : ℕ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E) :
    Sum (Fin 2 × Fin s) (Fin r) → E
  | Sum.inl (i, e) =>
      if i = 0 then LogdetLean.unitDirection (v (Sum.inl (0, e)))
      else gaussianAmbientResidualDirection
        (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))
  | Sum.inr j => LogdetLean.unitDirection (v (Sum.inr j))

@[simp] theorem stableMatchingFrameFamily_pair_zero
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E) (e : Fin s) :
    stableMatchingFrameFamily s r v (Sum.inl (0, e)) =
      LogdetLean.unitDirection (v (Sum.inl (0, e))) := by
  simp [stableMatchingFrameFamily]

@[simp] theorem stableMatchingFrameFamily_pair_one
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E) (e : Fin s) :
    stableMatchingFrameFamily s r v (Sum.inl (1, e)) =
      gaussianAmbientResidualDirection
        (v (Sum.inl (0, e))) (v (Sum.inl (1, e))) := by
  simp [stableMatchingFrameFamily]

@[simp] theorem stableMatchingFrameFamily_singleton
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E) (j : Fin r) :
    stableMatchingFrameFamily s r v (Sum.inr j) =
      LogdetLean.unitDirection (v (Sum.inr j)) := by
  simp [stableMatchingFrameFamily]

/-- Internal signed sample correlations of the distinguished raw pairs. -/
def stableMatchingInternalCorrelation (s r : ℕ)
    (v : Sum (Fin 2 × Fin s) (Fin r) → E) (e : Fin s) : ℝ :=
  signedNormalizedInner (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))

/-- Mixing the pair frames by their internal sample correlations reconstructs
the normalized raw columns exactly. -/
theorem mix_stableMatchingFrameFamily_eq_normalizeVector
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hv : ∀ i, v i ≠ 0)
    (hres : ∀ e, gaussianAxisResidualVector
      (v (Sum.inl (0, e))) (v (Sum.inl (1, e))) ≠ 0) :
    mixColumnFamily
        (matchingMixMatrix s r (stableMatchingInternalCorrelation s r v))
        (stableMatchingFrameFamily s r v) =
      fun i ↦ LogdetLean.normalizeVector (v i) := by
  funext i
  rcases i with ⟨i, e⟩ | j
  · fin_cases i
    · change mixColumnFamily
          (matchingMixMatrix s r (stableMatchingInternalCorrelation s r v))
          (stableMatchingFrameFamily s r v) (Sum.inl (0, e)) =
        LogdetLean.normalizeVector (v (Sum.inl (0, e)))
      rw [mixColumnFamily_matchingMixMatrix_pair_zero,
        stableMatchingFrameFamily_pair_zero,
        normalizeVector_eq_unitDirection_of_ne _ (hv (Sum.inl (0, e)))]
    · change mixColumnFamily
          (matchingMixMatrix s r (stableMatchingInternalCorrelation s r v))
          (stableMatchingFrameFamily s r v) (Sum.inl (1, e)) =
        LogdetLean.normalizeVector (v (Sum.inl (1, e)))
      rw [mixColumnFamily_matchingMixMatrix_pair_one,
        stableMatchingFrameFamily_pair_zero,
        stableMatchingFrameFamily_pair_one]
      exact (normalizeVector_eq_correlatedSecondColumn_pairFrame
        (v (Sum.inl (0, e))) (v (Sum.inl (1, e)))
        (hv (Sum.inl (0, e))) (hv (Sum.inl (1, e))) (hres e)).symm
  · rw [mixColumnFamily_matchingMixMatrix_singleton,
      stableMatchingFrameFamily_singleton,
      normalizeVector_eq_unitDirection_of_ne _ (hv (Sum.inr j))]

theorem norm_stableMatchingFrameFamily_eq_one
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hv : ∀ i, v i ≠ 0)
    (hres : ∀ e, gaussianAxisResidualVector
      (v (Sum.inl (0, e))) (v (Sum.inl (1, e))) ≠ 0)
    (i : Sum (Fin 2 × Fin s) (Fin r)) :
    ‖stableMatchingFrameFamily s r v i‖ = 1 := by
  rcases i with ⟨i, e⟩ | j
  · fin_cases i
    · change ‖stableMatchingFrameFamily s r v (Sum.inl (0, e))‖ = 1
      rw [stableMatchingFrameFamily_pair_zero,
        norm_unitDirection_of_ne _ (hv (Sum.inl (0, e)))]
    · change ‖stableMatchingFrameFamily s r v (Sum.inl (1, e))‖ = 1
      rw [stableMatchingFrameFamily_pair_one,
        norm_gaussianAmbientResidualDirection_of_ne
          _ _ (hv (Sum.inl (0, e))) (hres e)]
  · rw [stableMatchingFrameFamily_singleton,
      norm_unitDirection_of_ne _ (hv (Sum.inr j))]

theorem norm_mix_stableMatchingFrameFamily_eq_one
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hv : ∀ i, v i ≠ 0)
    (hres : ∀ e, gaussianAxisResidualVector
      (v (Sum.inl (0, e))) (v (Sum.inl (1, e))) ≠ 0)
    (i : Sum (Fin 2 × Fin s) (Fin r)) :
    ‖mixColumnFamily
      (matchingMixMatrix s r (stableMatchingInternalCorrelation s r v))
      (stableMatchingFrameFamily s r v) i‖ = 1 := by
  rw [mix_stableMatchingFrameFamily_eq_normalizeVector s r v hv hres]
  change ‖LogdetLean.normalizeVector (v i)‖ = 1
  rw [normalizeVector_eq_unitDirection_of_ne (v i) (hv i),
    norm_unitDirection_of_ne (v i) (hv i)]

/-- Exact finite-family determinant factorization: all internal pair angles
factor from the determinant of the frame geometry. -/
theorem det_normalizedGram_eq_internal_prod_mul_frameDet
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hv : ∀ i, v i ≠ 0)
    (hres : ∀ e, gaussianAxisResidualVector
      (v (Sum.inl (0, e))) (v (Sum.inl (1, e))) ≠ 0)
    (hr : ∀ e, |stableMatchingInternalCorrelation s r v e| < 1) :
    (normalizedGram v).det =
      (∏ e, (1 - stableMatchingInternalCorrelation s r v e ^ 2)) *
        (normalizedGram (stableMatchingFrameFamily s r v)).det := by
  let frame := stableMatchingFrameFamily s r v
  let rho := stableMatchingInternalCorrelation s r v
  have hframe : ∀ i, frame i ≠ 0 := by
    intro i
    apply norm_ne_zero_iff.mp
    rw [show ‖frame i‖ = 1 by
      simpa [frame] using norm_stableMatchingFrameFamily_eq_one s r v hv hres i]
    norm_num
  have hmix : ∀ i,
      mixColumnFamily (matchingMixMatrix s r rho) frame i ≠ 0 := by
    intro i
    apply norm_ne_zero_iff.mp
    rw [show ‖mixColumnFamily (matchingMixMatrix s r rho) frame i‖ = 1 by
      simpa [frame, rho] using
        norm_mix_stableMatchingFrameFamily_eq_one s r v hv hres i]
    norm_num
  have hdet := det_normalizedGram_matchingMix s r rho frame
    (fun e ↦ (hr e).le) hframe hmix
  have hleft :
      normalizedGram (mixColumnFamily (matchingMixMatrix s r rho) frame) =
        normalizedGram v := by
    rw [show mixColumnFamily (matchingMixMatrix s r rho) frame =
        fun i ↦ LogdetLean.normalizeVector (v i) by
      simpa [frame, rho] using
        mix_stableMatchingFrameFamily_eq_normalizeVector s r v hv hres]
    exact normalizedGram_normalizeVector_family v hv
  rw [hleft] at hdet
  have hframeNorm : ∀ i, ‖frame i‖ ^ 2 = 1 := by
    intro i
    rw [show ‖frame i‖ = 1 by
      simpa [frame] using norm_stableMatchingFrameFamily_eq_one s r v hv hres i]
    norm_num
  have hmixNorm : ∀ i,
      ‖mixColumnFamily (matchingMixMatrix s r rho) frame i‖ ^ 2 = 1 := by
    intro i
    rw [show ‖mixColumnFamily (matchingMixMatrix s r rho) frame i‖ = 1 by
      simpa [frame, rho] using
        norm_mix_stableMatchingFrameFamily_eq_one s r v hv hres i]
    norm_num
  simp_rw [hframeNorm, hmixNorm] at hdet
  simpa [frame, rho] using hdet

/-- Logarithmic version of the exact frame factorization. -/
theorem logdet_normalizedGram_eq_frame_add_internal_sum
    (s r : ℕ) (v : Sum (Fin 2 × Fin s) (Fin r) → E)
    (hv : ∀ i, v i ≠ 0)
    (hres : ∀ e, gaussianAxisResidualVector
      (v (Sum.inl (0, e))) (v (Sum.inl (1, e))) ≠ 0)
    (hr : ∀ e, |stableMatchingInternalCorrelation s r v e| < 1)
    (hframeDet : 0 <
      (normalizedGram (stableMatchingFrameFamily s r v)).det) :
    Real.log (normalizedGram v).det =
      Real.log (normalizedGram (stableMatchingFrameFamily s r v)).det +
        ∑ e, Real.log
          (1 - stableMatchingInternalCorrelation s r v e ^ 2) := by
  rw [det_normalizedGram_eq_internal_prod_mul_frameDet
    s r v hv hres hr]
  have hgap : ∀ e, 0 < 1 - stableMatchingInternalCorrelation s r v e ^ 2 :=
    fun e ↦ sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 (hr e))
  rw [Real.log_mul
    (Finset.prod_ne_zero_iff.mpr (fun e _ ↦ (hgap e).ne'))
    hframeDet.ne']
  rw [Real.log_prod (fun e _ ↦ (hgap e).ne')]
  ring

end

end LogdetLean.Coherence
