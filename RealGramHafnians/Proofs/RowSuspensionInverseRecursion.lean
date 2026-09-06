import RealGramHafnians.Proofs.RowSuspensionLiteralStep
import LogdetLean.GramHafnian.RealComplexAnticoncentration.ExactAuxiliaryGammaRecurrence
/-!
# The sharp real one-level inverse-moment recursion

This file identifies the physical cofactor-combination law with the literal
odd-cofactor model and applies the row-suspension Fourier majorant.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 5000000

/-- Literal physical cofactor combination, in Euclidean coordinates. -/
def pastRealCofactorCombinationEuclidean
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    RealGaussianEuclideanSpace k :=
  WithLp.toLp 2 (pastRealCofactorCombination hr A)

@[fun_prop] theorem measurable_pastRealCofactorCombinationEuclidean
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastRealCofactorCombinationEuclidean (k := k) hr) := by
  unfold pastRealCofactorCombinationEuclidean
  exact (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp
    (measurable_pastRealCofactorCombination hr)

theorem norm_sq_pastRealCofactorCombinationEuclidean
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    ‖pastRealCofactorCombinationEuclidean hr A‖ ^ 2 =
      pastRealCofactorV hr A := by
  rw [pastRealCofactorV_eq_realCoefficientEnergy]
  unfold pastRealCofactorCombinationEuclidean realCoefficientEnergy
  rw [EuclideanSpace.norm_sq_eq]
  simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

/-- Reindexing the iid columns commutes with the physical cofactor sum. -/
theorem finiteRealGramCofactorCombinationEuclidean_reindex_equiv
    {d : ℕ} {β : Type*} [Fintype β] [LinearOrder β] {k : ℕ}
    (e : Fin d ≃ β) (A : β → (Fin k → ℝ)) :
    finiteRealGramCofactorCombinationEuclidean
        (fun i : Fin d ↦ WithLp.toLp 2 (A (e i))) =
      WithLp.toLp 2
        (fun a ↦ ∑ j : β, A j a * finiteRealGramCofactorVector A j) := by
  apply (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).injective
  unfold finiteRealGramCofactorCombinationEuclidean
  rw [map_sum]
  simp only [map_smul, WithLp.coe_linearEquiv, WithLp.ofLp_toLp,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  funext a
  rw [Finset.sum_apply]
  apply Fintype.sum_equiv e
  intro i
  have hcf := finiteRealGramCofactorVector_reindex_equiv e A i
  change finiteRealGramCofactorVector (fun j p ↦ A (e j) p) i =
    finiteRealGramCofactorVector A (e i) at hcf
  rw [hcf]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem finiteRealGramCofactorCombinationEuclidean_reindex_odd
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    finiteRealGramCofactorCombinationEuclidean
        (fun i : Fin (2 * r - 1) ↦
          WithLp.toLp 2 (A (finOddCofactorEquiv r hr i))) =
      pastRealCofactorCombinationEuclidean hr A := by
  rw [finiteRealGramCofactorCombinationEuclidean_reindex_equiv]
  unfold pastRealCofactorCombinationEuclidean pastRealCofactorCombination
    realOddCofactorColumnCombination
  congr 1
  funext a
  apply Finset.sum_congr rfl
  intro j _hj
  have hcol : pastRealCofactorMatrix hr A j.1 = A j :=
    realLastColumnProductEquiv_apply_nonlast hr (A, 0) j
  rw [hcol,
    realOddHafnianCofactorVector_pastRealCofactorMatrix]

/-- Canonical reindexing and Euclidean realization of the literal columns. -/
def oddColumnsToFinEuclidean
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    Fin (2 * r - 1) → RealGaussianEuclideanSpace k :=
  fun i ↦ WithLp.toLp 2 (A (finOddCofactorEquiv r hr i))

@[fun_prop] theorem measurable_oddColumnsToFinEuclidean
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (oddColumnsToFinEuclidean (k := k) hr) := by
  unfold oddColumnsToFinEuclidean
  fun_prop

theorem measurePreserving_oddColumnsToFinEuclidean
    (r k : ℕ) (hr : 1 ≤ r) :
    MeasurePreserving (oddColumnsToFinEuclidean (k := k) hr)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦
        standardRealGaussianVectorMeasure k)
      (Measure.pi fun _ : Fin (2 * r - 1) ↦
        stdGaussian (RealGaussianEuclideanSpace k)) := by
  let Col := Fin k → ℝ
  let mu : Measure Col := standardRealGaussianVectorMeasure k
  let e := finOddCofactorEquiv r hr
  let g := (MeasurableEquiv.piCongrLeft (fun _ : OddCofactorIndex r hr ↦ Col) e).symm
  have hg : MeasurePreserving g
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ mu)
      (Measure.pi fun _ : Fin (2 * r - 1) ↦ mu) := by
    have h := measurePreserving_piCongrLeft
      (α := fun _ : OddCofactorIndex r hr ↦ Col)
      (fun _ : OddCofactorIndex r hr ↦ mu) e
    simpa [g] using h.symm
  have hlp : MeasurePreserving
      (fun A : Fin (2 * r - 1) → Col ↦
        fun i ↦ WithLp.toLp 2 (A i))
      (Measure.pi fun _ : Fin (2 * r - 1) ↦ mu)
      (Measure.pi fun _ : Fin (2 * r - 1) ↦
        stdGaussian (RealGaussianEuclideanSpace k)) := by
    apply measurePreserving_pi
    intro i
    exact ⟨WithLp.measurable_toLp 2 Col,
      map_pi_eq_stdGaussian⟩
  have h := hlp.comp hg
  convert h using 1
  funext A i
  rfl

def pastRealCofactorCombinationEuclideanLaw
    (r k : ℕ) (hr : 1 ≤ r) :
    Measure (RealGaussianEuclideanSpace k) :=
  Measure.map (pastRealCofactorCombinationEuclidean (k := k) hr)
    (Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k)

instance pastRealCofactorCombinationEuclideanLaw_isProbabilityMeasure
    (r k : ℕ) (hr : 1 ≤ r) :
    IsProbabilityMeasure (pastRealCofactorCombinationEuclideanLaw r k hr) := by
  unfold pastRealCofactorCombinationEuclideanLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_pastRealCofactorCombinationEuclidean hr).aemeasurable

theorem finiteRealGramCofactorCombinationEuclideanLaw_eq_literal
    (r k : ℕ) (hr : 1 ≤ r) :
    finiteRealGramCofactorCombinationEuclideanLaw (2 * r - 1) k =
      pastRealCofactorCombinationEuclideanLaw r k hr := by
  unfold finiteRealGramCofactorCombinationEuclideanLaw
    pastRealCofactorCombinationEuclideanLaw
  have hmp := measurePreserving_oddColumnsToFinEuclidean r k hr
  rw [← hmp.map_eq]
  rw [Measure.map_map]
  · congr 1
    funext A
    exact finiteRealGramCofactorCombinationEuclidean_reindex_odd hr A
  · exact measurable_finiteRealGramCofactorCombinationEuclidean
  · exact measurable_oddColumnsToFinEuclidean hr

/-- Literal negative-half moment of the physical cofactor energy. -/
def sharpRealCofactorInverseSqrtMoment
    (r k : ℕ) (hr : 1 ≤ r) : ENNReal :=
  ennInverseSqrtMoment
    (Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k)
    (pastRealCofactorV hr)

theorem ennInverseSqrtMoment_literalPhysicalLaw_eq
    (r k : ℕ) (hr : 1 ≤ r) :
    ennInverseSqrtMoment
        (pastRealCofactorCombinationEuclideanLaw r k hr)
        (fun x ↦ ‖x‖ ^ 2) =
      sharpRealCofactorInverseSqrtMoment r k hr := by
  unfold pastRealCofactorCombinationEuclideanLaw
    sharpRealCofactorInverseSqrtMoment ennInverseSqrtMoment
  rw [lintegral_map]
  · apply lintegral_congr
    intro A
    rw [show (fun x ↦ ‖x‖ ^ 2)
        (pastRealCofactorCombinationEuclidean hr A) =
        pastRealCofactorV hr A by
      exact norm_sq_pastRealCofactorCombinationEuclidean hr A]
  · fun_prop
  · exact measurable_pastRealCofactorCombinationEuclidean hr

theorem ennInverseSqrtMoment_physicalLaw_eq
    (r k : ℕ) (hr : 1 ≤ r) :
    ennInverseSqrtMoment
        (finiteRealGramCofactorCombinationEuclideanLaw (2 * r - 1) k)
        (fun x ↦ ‖x‖ ^ 2) =
      sharpRealCofactorInverseSqrtMoment r k hr := by
  rw [finiteRealGramCofactorCombinationEuclideanLaw_eq_literal r k hr,
    ennInverseSqrtMoment_literalPhysicalLaw_eq]

theorem ae_norm_sq_pos_pastRealCofactorCombinationEuclideanLaw
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ x ∂(pastRealCofactorCombinationEuclideanLaw r k hr),
      0 < ‖x‖ ^ 2 := by
  unfold pastRealCofactorCombinationEuclideanLaw
  have hset : MeasurableSet
      {x : RealGaussianEuclideanSpace k | 0 < ‖x‖ ^ 2} := by
    change MeasurableSet ((fun x : RealGaussianEuclideanSpace k ↦ ‖x‖ ^ 2) ⁻¹' Set.Ioi 0)
    exact measurableSet_Ioi.preimage (by fun_prop)
  apply (ae_map_iff
    (measurable_pastRealCofactorCombinationEuclidean hr).aemeasurable hset).2
  filter_upwards [ae_pastRealCofactorV_pos_standardRealGaussian hr hk]
    with A hA
  rwa [norm_sq_pastRealCofactorCombinationEuclidean]

theorem ae_norm_sq_pos_finiteRealGramCofactorCombinationEuclideanLaw
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ x ∂(finiteRealGramCofactorCombinationEuclideanLaw (2 * r - 1) k),
      0 < ‖x‖ ^ 2 := by
  rw [finiteRealGramCofactorCombinationEuclideanLaw_eq_literal r k hr]
  exact ae_norm_sq_pos_pastRealCofactorCombinationEuclideanLaw hr hk

theorem ae_rowSuspensionLowerProductVariance_pos
    {r k : ℕ} (hr2 : 2 ≤ r) (hrlow : 1 ≤ r - 1)
    (hk : 2 * (r - 1) - 1 ≤ k) :
    ∀ᵐ p ∂((Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
        standardRealGaussianVectorMeasure k).prod
      (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))),
      0 < rowSuspensionLowerProductVariance hr2 p := by
  let nu := Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
    standardRealGaussianVectorMeasure k
  have hV : ∀ᵐ A ∂nu, 0 < pastRealCofactorV hrlow A :=
    ae_pastRealCofactorV_pos_standardRealGaussian hrlow hk
  have hVprod := (Measure.quasiMeasurePreserving_fst
    (μ := nu) (ν := stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))).ae hV
  have hG : ∀ᵐ g ∂(stdGaussian (RealGaussianEuclideanSpace (2 * r - 1))),
      g ≠ 0 := by
    let _ : Nonempty (Fin (2 * r - 1)) := Fin.pos_iff_nonempty.mp (by omega)
    let _ : Nontrivial (RealGaussianEuclideanSpace (2 * r - 1)) := inferInstance
    simpa [ae_iff] using
      LogdetLean.stdGaussian_zero_singleton
        (E := RealGaussianEuclideanSpace (2 * r - 1))
  have hGprod := (Measure.quasiMeasurePreserving_snd
    (μ := nu) (ν := stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))).ae hG
  filter_upwards [hVprod, hGprod] with p hpV hpG
  unfold rowSuspensionLowerProductVariance realAuxiliaryNormSq
  exact mul_pos hpV (by positivity)

/-- Lossless real row-suspension step.  Both factors are exact negative-half
moments of independent chi-square radii. -/
theorem sharpRealCofactorInverseSqrtMoment_step
    {r k : ℕ} (hr2 : 2 ≤ r) (hk : 2 * r - 1 ≤ k + 1) :
    sharpRealCofactorInverseSqrtMoment r (k + 1) (by omega) ≤
      sharpRealCofactorInverseSqrtMoment (r - 1) k (by omega) *
        realAuxiliaryGammaHalfFactor (k + 1) *
        realAuxiliaryGammaHalfFactor (2 * r - 1) := by
  let nuLower : Measure
      (OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
      standardRealGaussianVectorMeasure k
  let nu := nuLower.prod
    (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1)))
  have hklower : 2 * (r - 1) - 1 ≤ k := by omega
  have hstep := ennInverseSqrt_norm_sq_le_realAuxiliaryGamma_factor
    (d := k + 1) (by omega)
    (finiteRealGramCofactorCombinationEuclideanLaw (2 * r - 1) (k + 1))
    nu
    (rowSuspensionLowerProductVariance (k := k) hr2)
    (measurable_rowSuspensionLowerProductVariance hr2)
    (rowSuspensionLowerProductVariance_nonneg hr2)
    (by
      simpa [nu, nuLower] using
        ae_rowSuspensionLowerProductVariance_pos hr2 (by omega) hklower)
    (physicalCofactorCombination_charFun_re_le_rowSuspension_product
      (k := k) (by omega) hr2)
    (ae_norm_sq_pos_finiteRealGramCofactorCombinationEuclideanLaw
      (k := k + 1) (by omega) hk)
  have hfactor :
      ennInverseSqrtMoment nu
          (rowSuspensionLowerProductVariance (k := k) hr2) =
        sharpRealCofactorInverseSqrtMoment (r - 1) k (by omega) *
          realAuxiliaryGammaHalfFactor (2 * r - 1) := by
    change ennInverseSqrtMoment nu
        (fun p ↦ pastRealCofactorV (k := k) (by omega) p.1 *
          realAuxiliaryNormSq p.2) = _
    have h := ennInverseSqrtMoment_mul_realAuxiliaryNormSq
      nuLower (pastRealCofactorV (k := k) (by omega))
      (measurable_pastRealCofactorV (by omega))
      (pastRealCofactorV_nonneg (by omega)) (by omega : 2 ≤ 2 * r - 1)
    simpa [nu, nuLower, rowSuspensionLowerProductVariance,
      sharpRealCofactorInverseSqrtMoment, realAuxiliaryGammaHalfFactor] using h
  rw [ennInverseSqrtMoment_physicalLaw_eq r (k + 1) (by omega),
    hfactor] at hstep
  simpa [realAuxiliaryGammaHalfFactor, mul_assoc, mul_left_comm, mul_comm]
    using hstep

end

end LogdetLean.GramHafnian
