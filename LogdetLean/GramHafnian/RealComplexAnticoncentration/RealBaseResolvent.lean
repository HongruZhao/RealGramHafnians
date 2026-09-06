import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralResolventStep
import LogdetLean.GramHafnian.ShiftedAnticoncentration.BaseInverseMoment
/-!
# Exact beta-one base resolvent

At level one the cofactor energy is exactly the squared norm of one standard
real Gaussian column.  This gives the chi-square negative-half Gamma factor
at dimension `k`, with no matrix good-event error.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The first real past cofactor combination is evaluation at the unique
past column. -/
theorem pastRealCofactorCombination_level_one {k : ℕ}
    (A : OddCofactorIndex 1 (by omega) → Fin k → ℝ) :
    pastRealCofactorCombination (by omega) A = A default := by
  funext a
  unfold pastRealCofactorCombination realOddCofactorColumnCombination
  simp_rw [realOddHafnianCofactorVector_level_one]
  simp [pastRealCofactorMatrix, realLastColumnProductEquiv_apply_nonlast]

/-- The first real cofactor energy is the squared Euclidean norm of the
unique past column. -/
theorem pastRealCofactorV_level_one {k : ℕ}
    (A : OddCofactorIndex 1 (by omega) → Fin k → ℝ) :
    pastRealCofactorV (by omega) A =
      realAuxiliaryNormSq (WithLp.toLp 2 (A default)) := by
  rw [pastRealCofactorV_eq_realCoefficientEnergy,
    pastRealCofactorCombination_level_one]
  unfold realCoefficientEnergy realAuxiliaryNormSq
  rw [EuclideanSpace.real_norm_sq_eq]

/-- Exact inverse-square-root moment at the beta-one base. -/
theorem ennInverseSqrtMoment_pastRealCofactorV_level_one
    {k : ℕ} (hk : 2 ≤ k) :
    ennInverseSqrtMoment
        (Measure.pi fun _ : OddCofactorIndex 1 (by omega) ↦
          standardRealGaussianVectorMeasure k)
        (pastRealCofactorV (k := k) (by omega)) =
      realAuxiliaryGammaHalfFactor k := by
  let I := OddCofactorIndex 1 (by omega)
  let raw : Measure (Fin k → ℝ) := standardRealGaussianVectorMeasure k
  have he : MeasurePreserving (fun A : I → (Fin k → ℝ) ↦ A default)
      (Measure.pi fun _ : I ↦ raw) raw := by
    exact measurePreserving_funUnique raw I
  have hmeas : Measurable
      (fun x : Fin k → ℝ ↦
        ENNReal.ofReal
          (Real.sqrt (realAuxiliaryNormSq (WithLp.toLp 2 x)))⁻¹) := by
    fun_prop
  calc
    ennInverseSqrtMoment (Measure.pi fun _ : I ↦ raw)
        (pastRealCofactorV (k := k) (by omega)) =
        ∫⁻ A : I → (Fin k → ℝ),
          ENNReal.ofReal
            (Real.sqrt
              (realAuxiliaryNormSq (WithLp.toLp 2 (A default))))⁻¹
          ∂Measure.pi fun _ : I ↦ raw := by
      unfold ennInverseSqrtMoment
      apply lintegral_congr
      intro A
      rw [pastRealCofactorV_level_one]
    _ = ∫⁻ x : Fin k → ℝ,
          ENNReal.ofReal
            (Real.sqrt (realAuxiliaryNormSq (WithLp.toLp 2 x)))⁻¹
          ∂raw := by
      exact he.lintegral_comp hmeas
    _ = ∫⁻ g : RealGaussianEuclideanSpace k,
          ENNReal.ofReal (Real.sqrt (realAuxiliaryNormSq g))⁻¹
          ∂(stdGaussian (RealGaussianEuclideanSpace k)) := by
      exact (measurePreserving_toLp_standardRealGaussianVector k).lintegral_comp
        (measurable_realAuxiliaryNormSq.sqrt.inv.ennreal_ofReal)
    _ = realAuxiliaryGammaHalfFactor k :=
      lintegral_inv_sqrt_realAuxiliaryNormSq_stdGaussian_eq_factor hk

/-- Pointwise comparison of the half-resolvent kernel with the inverse
square-root kernel, away from zero energy. -/
theorem ennHalfResolventKernel_le_sqrt_mul_inv_sqrt
    {lambda x : ℝ} (hlambda : 0 < lambda) (hx : 0 < x) :
    ennHalfResolventKernel lambda x ≤
      ENNReal.ofReal (Real.sqrt lambda) *
        ENNReal.ofReal (Real.sqrt x)⁻¹ := by
  unfold ennHalfResolventKernel
  have hsqrt : Real.sqrt x ≤ Real.sqrt (x + lambda) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcoe : ENNReal.ofReal (Real.sqrt x) ≤
      ENNReal.ofReal (Real.sqrt (x + lambda)) :=
    ENNReal.ofReal_le_ofReal hsqrt
  have hinv : ENNReal.ofReal (Real.sqrt (x + lambda))⁻¹ ≤
      ENNReal.ofReal (Real.sqrt x)⁻¹ := by
    calc
      ENNReal.ofReal (Real.sqrt (x + lambda))⁻¹ =
          (ENNReal.ofReal (Real.sqrt (x + lambda)))⁻¹ :=
        ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 (by linarith))
      _ ≤ (ENNReal.ofReal (Real.sqrt x))⁻¹ := ENNReal.inv_le_inv' hcoe
      _ = ENNReal.ofReal (Real.sqrt x)⁻¹ :=
        (ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 hx)).symm
  exact mul_le_mul le_rfl hinv bot_le bot_le

/-- Exact level-one affine envelope: no bad event, and coefficient equal to
the chi-square-`k` negative-half moment. -/
theorem pastRealCofactorHalfResolvent_one_le_exact_sqrt_envelope
    {k : ℕ} (hk : 2 ≤ k) (lambda : ℝ) (hlambda : 0 < lambda) :
    pastRealCofactorHalfResolvent 1 k (by omega) lambda ≤
      realAuxiliaryGammaHalfFactor k *
        ENNReal.ofReal (Real.sqrt lambda) := by
  let I := OddCofactorIndex 1 (by omega)
  let mu : Measure (I → Fin k → ℝ) :=
    Measure.pi fun _ : I ↦ standardRealGaussianVectorMeasure k
  let raw : Measure (Fin k → ℝ) := standardRealGaussianVectorMeasure k
  have he : MeasurePreserving (fun A : I → (Fin k → ℝ) ↦ A default)
      mu raw := by
    exact measurePreserving_funUnique raw I
  have htoLp := measurePreserving_toLp_standardRealGaussianVector k
  have hGne : ∀ᵐ g ∂(stdGaussian (RealGaussianEuclideanSpace k)), g ≠ 0 := by
    let _ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
    let _ : Nontrivial (RealGaussianEuclideanSpace k) := inferInstance
    simpa [ae_iff] using
      LogdetLean.stdGaussian_zero_singleton
        (E := RealGaussianEuclideanSpace k)
  have hxne : ∀ᵐ x ∂raw, WithLp.toLp 2 x ≠ 0 :=
    htoLp.quasiMeasurePreserving.ae hGne
  have hAne : ∀ᵐ A ∂mu, WithLp.toLp 2 (A default) ≠ 0 :=
    he.quasiMeasurePreserving.ae hxne
  have hVpos : ∀ᵐ A ∂mu, 0 < pastRealCofactorV (by omega) A := by
    filter_upwards [hAne] with A hA
    rw [pastRealCofactorV_level_one]
    unfold realAuxiliaryNormSq
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hA)
  have hpoint : ∀ᵐ A ∂mu,
      ennHalfResolventKernel lambda (pastRealCofactorV (by omega) A) ≤
        ENNReal.ofReal (Real.sqrt lambda) *
          ENNReal.ofReal
            (Real.sqrt (pastRealCofactorV (by omega) A))⁻¹ := by
    filter_upwards [hVpos] with A hA
    exact ennHalfResolventKernel_le_sqrt_mul_inv_sqrt hlambda hA
  unfold pastRealCofactorHalfResolvent ennHalfResolvent
  calc
    (∫⁻ A, ennHalfResolventKernel lambda
        (pastRealCofactorV (by omega) A) ∂mu) ≤
      ∫⁻ A, ENNReal.ofReal (Real.sqrt lambda) *
        ENNReal.ofReal (Real.sqrt
          (pastRealCofactorV (by omega) A))⁻¹ ∂mu :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (Real.sqrt lambda) *
        ennInverseSqrtMoment mu (pastRealCofactorV (by omega)) := by
      unfold ennInverseSqrtMoment
      rw [lintegral_const_mul]
      fun_prop
    _ = ENNReal.ofReal (Real.sqrt lambda) *
        realAuxiliaryGammaHalfFactor k := by
      rw [ennInverseSqrtMoment_pastRealCofactorV_level_one hk]
    _ = realAuxiliaryGammaHalfFactor k *
        ENNReal.ofReal (Real.sqrt lambda) := mul_comm _ _

end

end LogdetLean.GramHafnian
