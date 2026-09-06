import RealGramHafnians.Proofs.SharpRealGaussianMixture
import RealGramHafnians.Proofs.SharpRealSymmetricGaussian
/-!
# Density of the normalized real symmetric Gaussian hafnian

This module derives the density directly from the independent-edge model.
It does not pass to a limit of the finite-row Gram-hafnian densities.  The
last-vertex split writes the hafnian as a Gaussian linear form conditional on
its cofactor vector; Tonelli then identifies the Gaussian scale-mixture
density, and the verified inverse-half-moment estimate supplies continuity
and the quantitative peak bound.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Real ENNReal NNReal Nat Topology

namespace LogdetLean.GramHafnian

noncomputable section

open SymmetricGaussianHafnian

/-- The squared norm of the independent-edge cofactor vector, bundled as a
nonnegative real. -/
def realEdgeCofactorVarianceNNReal {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℝ) : ℝ≥0 :=
  ⟨realEdgeCofactorEnergy x, realEdgeCofactorEnergy_nonneg x⟩

@[fun_prop]
theorem measurable_realEdgeCofactorVarianceNNReal
    {ι : Type*} [Fintype ι] [LinearOrder ι] :
    Measurable (realEdgeCofactorVarianceNNReal : (Edge ι → ℝ) → ℝ≥0) :=
  measurable_realEdgeCofactorEnergy.subtype_mk

/-- The raw density obtained by conditioning the real symmetric Gaussian
hafnian on all edges not incident to its last vertex. -/
def sharpRealSymmetricHafnianDensity (n : ℕ) (x : ℝ) : ℝ :=
  gaussianScaleMixtureDensity
    (realEdgeGaussian (Fin (2 * n - 1)))
    realEdgeCofactorVarianceNNReal x

/-- The conditional variance is positive almost surely for every nontrivial
hafnian order. -/
theorem ae_realEdgeCofactorVarianceNNReal_ne_zero
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ x ∂realEdgeGaussian (Fin (2 * n - 1)),
      (realEdgeCofactorVarianceNNReal x : ℝ≥0) ≠ 0 := by
  have hpos := ae_realEdgeCofactorEnergy_pos_odd (n - 1)
  have hsize : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  rw [hsize] at hpos
  filter_upwards [hpos] with x hx
  intro hzero
  have hcoe := congrArg ((↑) : ℝ≥0 → ℝ) hzero
  change realEdgeCofactorEnergy x = 0 at hcoe
  exact hx.ne' hcoe

/-- The inverse-square-root moment used by the density module is the
independent-edge half inverse moment used by the Fourier recursion. -/
theorem ennInverseSqrtMoment_realEdgeCofactorVariance_eq
    {n : ℕ} (hn : 1 ≤ n) :
    ennInverseSqrtMoment
        (realEdgeGaussian (Fin (2 * n - 1)))
        (fun x ↦ (realEdgeCofactorVarianceNNReal x : ℝ)) =
      realCofactorHalfInverseMoment n := by
  unfold ennInverseSqrtMoment realCofactorHalfInverseMoment
    ennHalfInverseMoment
  apply lintegral_congr_ae
  have hpos := ae_realEdgeCofactorEnergy_pos_odd (n - 1)
  have hsize : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  rw [hsize] at hpos
  filter_upwards [hpos] with x hx
  congr 1
  exact inv_sqrt_eq_rpow_neg_half hx.le

/-- Finiteness of the inverse conditional standard deviation. -/
theorem ennInverseSqrtMoment_realEdgeCofactorVariance_ne_top
    {n : ℕ} (hn : 1 ≤ n) :
    ennInverseSqrtMoment
        (realEdgeGaussian (Fin (2 * n - 1)))
        (fun x ↦ (realEdgeCofactorVarianceNNReal x : ℝ)) ≠ ∞ := by
  rw [ennInverseSqrtMoment_realEdgeCofactorVariance_eq hn]
  exact ne_of_lt <| (realCofactorHalfInverseMoment_le n hn).trans_lt
    ENNReal.ofReal_lt_top

/-- Integrability of the conditional Gaussian peak. -/
theorem integrable_realEdgeCofactorGaussianPeak
    {n : ℕ} (hn : 1 ≤ n) :
    Integrable
      (fun x : Edge (Fin (2 * n - 1)) → ℝ ↦
        gaussianPDFReal 0 (realEdgeCofactorVarianceNNReal x) 0)
      (realEdgeGaussian (Fin (2 * n - 1))) := by
  exact integrable_gaussianScaleMixturePeak_of_inverseSqrtMoment_ne_top
    (realEdgeGaussian (Fin (2 * n - 1)))
    measurable_realEdgeCofactorVarianceNNReal
    (ennInverseSqrtMoment_realEdgeCofactorVariance_ne_top hn)

/-- The raw limiting density is continuous. -/
theorem continuous_sharpRealSymmetricHafnianDensity
    {n : ℕ} (hn : 1 ≤ n) :
    Continuous (sharpRealSymmetricHafnianDensity n) := by
  unfold sharpRealSymmetricHafnianDensity
  exact continuous_gaussianScaleMixtureDensity
    (realEdgeGaussian (Fin (2 * n - 1)))
    measurable_realEdgeCofactorVarianceNNReal
    (ae_realEdgeCofactorVarianceNNReal_ne_zero hn)
    (integrable_realEdgeCofactorGaussianPeak hn)

/-- The raw limiting density is nonnegative and pointwise maximized at zero. -/
theorem sharpRealSymmetricHafnianDensity_nonneg_and_le_zero
    {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    0 ≤ sharpRealSymmetricHafnianDensity n x ∧
      sharpRealSymmetricHafnianDensity n x ≤
        sharpRealSymmetricHafnianDensity n 0 := by
  unfold sharpRealSymmetricHafnianDensity
  constructor
  · exact gaussianScaleMixtureDensity_nonneg
      (realEdgeGaussian (Fin (2 * n - 1)))
      realEdgeCofactorVarianceNNReal x
  · exact gaussianScaleMixtureDensity_le_zero
      (realEdgeGaussian (Fin (2 * n - 1)))
      measurable_realEdgeCofactorVarianceNNReal
      (integrable_realEdgeCofactorGaussianPeak hn) x

/-- The raw limiting density is even. -/
theorem gaussianPDFReal_zero_neg_symmetric (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v (-x) = gaussianPDFReal 0 v x := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [gaussianPDFReal, gaussianPDFReal]
    congr 2
    ring

theorem even_sharpRealSymmetricHafnianDensity
    {n : ℕ} (hn : 1 ≤ n) :
    Function.Even (sharpRealSymmetricHafnianDensity n) := by
  intro x
  unfold sharpRealSymmetricHafnianDensity gaussianScaleMixtureDensity
  apply integral_congr_ae
  filter_upwards [] with w
  exact gaussianPDFReal_zero_neg_symmetric
    (realEdgeCofactorVarianceNNReal w) x

/-- Conditional equality in law between the last-vertex Gaussian linear form
and the corresponding scalar Gaussian scale mixture. -/
theorem map_realEdgeConditionalLinearForm_eq_gaussianScaleMixtureObservable
    (d : ℕ) :
    Measure.map
        (fun p : (Edge (Fin d) → ℝ) × (Fin d → ℝ) ↦
          iidRealLinearForm (realEdgeCofactor p.1) p.2)
        ((realEdgeGaussian (Fin d)).prod
          (standardRealGaussianProduct (Fin d))) =
      Measure.map
        (gaussianScaleMixtureObservable
          (realEdgeCofactorVarianceNNReal :
            (Edge (Fin d) → ℝ) → ℝ≥0))
        ((realEdgeGaussian (Fin d)).prod (gaussianReal 0 1)) := by
  let nu : Measure (Edge (Fin d) → ℝ) := realEdgeGaussian (Fin d)
  let mu : Measure (Fin d → ℝ) := standardRealGaussianProduct (Fin d)
  let y : (Edge (Fin d) → ℝ) → (Fin d → ℝ) := realEdgeCofactor
  let q : (Edge (Fin d) → ℝ) → ℝ≥0 := realEdgeCofactorVarianceNNReal
  have hy : Measurable y := measurable_realEdgeCofactor
  have hq : Measurable q := measurable_realEdgeCofactorVarianceNNReal
  ext s hs
  have hleft : MeasurableSet
      ((fun p : (Edge (Fin d) → ℝ) × (Fin d → ℝ) ↦
        iidRealLinearForm (y p.1) p.2) ⁻¹' s) := by
    apply hs.preimage
    unfold iidRealLinearForm y
    fun_prop
  have hright : MeasurableSet
      (gaussianScaleMixtureObservable q ⁻¹' s) :=
    hs.preimage (measurable_gaussianScaleMixtureObservable hq)
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.map_apply (measurable_gaussianScaleMixtureObservable hq) hs,
    Measure.prod_apply hleft, Measure.prod_apply hright]
  apply lintegral_congr
  intro A
  change mu ((iidRealLinearForm (y A)) ⁻¹' s) =
    (gaussianReal 0 1)
      ((fun z : ℝ ↦ Real.sqrt (q A : ℝ) * z) ⁻¹' s)
  rw [← Measure.map_apply (measurable_iidRealLinearForm (y A)) hs,
    ← Measure.map_apply (by fun_prop) hs]
  have hqA : (q A : ℝ) =
      SymmetricGaussianHafnian.realCoefficientEnergy (y A) := by
    rfl
  rw [hqA]
  have hlaw := iidRealLinearForm_law (y A)
  have hlawSet := congrArg (fun m : Measure ℝ ↦ m s) hlaw
  simpa [nu, mu, y, q] using hlawSet

/-- The literal independent-edge hafnian is the stated scalar Gaussian scale
mixture. -/
theorem map_realEdgeHafnian_eq_gaussianScaleMixtureObservable
    (d : ℕ) :
    Measure.map realEdgeHafnian (realEdgeGaussian (Fin (d + 1))) =
      Measure.map
        (gaussianScaleMixtureObservable
          (realEdgeCofactorVarianceNNReal :
            (Edge (Fin d) → ℝ) → ℝ≥0))
        ((realEdgeGaussian (Fin d)).prod (gaussianReal 0 1)) := by
  change realEdgeHafnianLaw (Fin (d + 1)) = _
  rw [realEdgeHafnianLaw_eq_lastVertexProduct d]
  exact map_realEdgeConditionalLinearForm_eq_gaussianScaleMixtureObservable d

/-- Native `ENNReal` density identity for the literal real symmetric Gaussian
hafnian. -/
theorem map_realSymmetricGaussianHafnian_eq_withDensityENN
    {n : ℕ} (hn : 1 ≤ n) :
    Measure.map realEdgeHafnian (realEdgeGaussian (Fin (2 * n))) =
      volume.withDensity
        (gaussianScaleMixtureDensityENN
          (realEdgeGaussian (Fin (2 * n - 1)))
          (realEdgeCofactorVarianceNNReal :
            (Edge (Fin (2 * n - 1)) → ℝ) → ℝ≥0)) := by
  have hsize : 2 * n = (2 * n - 1) + 1 := by omega
  rw [hsize, map_realEdgeHafnian_eq_gaussianScaleMixtureObservable]
  exact map_gaussianScaleMixtureObservable_eq_withDensity
    (realEdgeGaussian (Fin (2 * n - 1)))
    measurable_realEdgeCofactorVarianceNNReal
    (ae_realEdgeCofactorVarianceNNReal_ne_zero hn)

/-- The native extended density agrees with the real-valued mixture density. -/
theorem gaussianScaleMixtureDensityENN_eq_ofReal_symmetricDensity
    {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    gaussianScaleMixtureDensityENN
        (realEdgeGaussian (Fin (2 * n - 1)))
        (realEdgeCofactorVarianceNNReal :
          (Edge (Fin (2 * n - 1)) → ℝ) → ℝ≥0) x =
      ENNReal.ofReal (sharpRealSymmetricHafnianDensity n x) := by
  have hint := integrable_gaussianScaleMixtureKernel
    (realEdgeGaussian (Fin (2 * n - 1)))
    measurable_realEdgeCofactorVarianceNNReal
    (integrable_realEdgeCofactorGaussianPeak hn) x
  have hnonneg :
      ∀ᵐ A ∂realEdgeGaussian (Fin (2 * n - 1)),
        0 ≤ gaussianPDFReal 0 (realEdgeCofactorVarianceNNReal A) x :=
    Filter.Eventually.of_forall fun A ↦
      gaussianPDFReal_nonneg 0 (realEdgeCofactorVarianceNNReal A) x
  symm
  simpa [sharpRealSymmetricHafnianDensity, gaussianScaleMixtureDensity,
    gaussianScaleMixtureDensityENN, gaussianPDF] using
      ofReal_integral_eq_lintegral_ofReal hint hnonneg

/-- The raw independent-edge hafnian law has the displayed continuous
Gaussian-mixture density. -/
theorem map_realSymmetricGaussianHafnian_eq_withDensity
    {n : ℕ} (hn : 1 ≤ n) :
    Measure.map realEdgeHafnian (realEdgeGaussian (Fin (2 * n))) =
      volume.withDensity
        (fun x ↦ ENNReal.ofReal (sharpRealSymmetricHafnianDensity n x)) := by
  rw [map_realSymmetricGaussianHafnian_eq_withDensityENN hn]
  congr 1
  funext x
  exact gaussianScaleMixtureDensityENN_eq_ofReal_symmetricDensity hn x

/-! ## Root-mean-square normalization -/

/-- The root mean square is strictly positive. -/
theorem sharpRealSymmetricHafnianRMS_pos (n : ℕ) :
    0 < sharpRealSymmetricHafnianRMS n := by
  unfold sharpRealSymmetricHafnianRMS sigma
  apply Real.sqrt_pos.2
  exact_mod_cast oddPairingNat_pos n

/-- The root mean square bundled as a nonnegative real. -/
def sharpRealSymmetricHafnianRMSNNReal (n : ℕ) : ℝ≥0 :=
  ⟨sharpRealSymmetricHafnianRMS n,
    (sharpRealSymmetricHafnianRMS_pos n).le⟩

/-- Conditional variance after dividing the hafnian by its root mean square. -/
def realEdgeNormalizedCofactorVarianceNNReal (n : ℕ)
    (x : Edge (Fin (2 * n - 1)) → ℝ) : ℝ≥0 :=
  realEdgeCofactorVarianceNNReal x /
    (sharpRealSymmetricHafnianRMSNNReal n) ^ 2

@[fun_prop]
theorem measurable_realEdgeNormalizedCofactorVarianceNNReal (n : ℕ) :
    Measurable (realEdgeNormalizedCofactorVarianceNNReal n) := by
  unfold realEdgeNormalizedCofactorVarianceNNReal
  fun_prop

theorem sqrt_realEdgeNormalizedCofactorVarianceNNReal
    {n : ℕ} (x : Edge (Fin (2 * n - 1)) → ℝ) :
    Real.sqrt (realEdgeNormalizedCofactorVarianceNNReal n x : ℝ) =
      Real.sqrt (realEdgeCofactorEnergy x) /
        sharpRealSymmetricHafnianRMS n := by
  unfold realEdgeNormalizedCofactorVarianceNNReal
  rw [NNReal.coe_div, NNReal.coe_pow]
  change Real.sqrt
      (realEdgeCofactorEnergy x /
        sharpRealSymmetricHafnianRMS n ^ 2) = _
  rw [Real.sqrt_div (realEdgeCofactorEnergy_nonneg x),
    Real.sqrt_sq_eq_abs,
    abs_of_pos (sharpRealSymmetricHafnianRMS_pos n)]

theorem ae_realEdgeNormalizedCofactorVarianceNNReal_ne_zero
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ x ∂realEdgeGaussian (Fin (2 * n - 1)),
      realEdgeNormalizedCofactorVarianceNNReal n x ≠ 0 := by
  filter_upwards [ae_realEdgeCofactorVarianceNNReal_ne_zero hn] with x hx
  apply div_ne_zero hx
  apply pow_ne_zero
  intro hzero
  have hcoe := congrArg ((↑) : ℝ≥0 → ℝ) hzero
  change sharpRealSymmetricHafnianRMS n = 0 at hcoe
  exact (sharpRealSymmetricHafnianRMS_pos n).ne' hcoe

/-- The normalized independent-edge hafnian observable. -/
def sharpRealNormalizedSymmetricHafnianObservable (n : ℕ)
    (x : Edge (Fin (2 * n)) → ℝ) : ℝ :=
  realEdgeHafnian x / sharpRealSymmetricHafnianRMS n

@[fun_prop]
theorem measurable_sharpRealNormalizedSymmetricHafnianObservable (n : ℕ) :
    Measurable (sharpRealNormalizedSymmetricHafnianObservable n) := by
  unfold sharpRealNormalizedSymmetricHafnianObservable
  fun_prop

/-- The normalized conditional linear form has the normalized Gaussian
scale-mixture law. -/
theorem map_realEdgeNormalizedConditionalLinearForm_eq_mixture
    {n : ℕ} (hn : 1 ≤ n) :
    Measure.map
        (fun p : (Edge (Fin (2 * n - 1)) → ℝ) ×
            (Fin (2 * n - 1) → ℝ) ↦
          iidRealLinearForm (realEdgeCofactor p.1) p.2 /
            sharpRealSymmetricHafnianRMS n)
        ((realEdgeGaussian (Fin (2 * n - 1))).prod
          (standardRealGaussianProduct (Fin (2 * n - 1)))) =
      Measure.map
        (gaussianScaleMixtureObservable
          (realEdgeNormalizedCofactorVarianceNNReal n))
        ((realEdgeGaussian (Fin (2 * n - 1))).prod
          (gaussianReal 0 1)) := by
  let d := 2 * n - 1
  let nu : Measure (Edge (Fin d) → ℝ) := realEdgeGaussian (Fin d)
  let mu : Measure (Fin d → ℝ) := standardRealGaussianProduct (Fin d)
  let s0 := sharpRealSymmetricHafnianRMS n
  have hs0 : 0 < s0 := sharpRealSymmetricHafnianRMS_pos n
  ext S hS
  have hleft : MeasurableSet
      ((fun p : (Edge (Fin d) → ℝ) × (Fin d → ℝ) ↦
        iidRealLinearForm (realEdgeCofactor p.1) p.2 / s0) ⁻¹' S) := by
    apply hS.preimage
    unfold iidRealLinearForm
    fun_prop
  have hright : MeasurableSet
      (gaussianScaleMixtureObservable
        (realEdgeNormalizedCofactorVarianceNNReal n) ⁻¹' S) :=
    hS.preimage <| measurable_gaussianScaleMixtureObservable
      (measurable_realEdgeNormalizedCofactorVarianceNNReal n)
  rw [Measure.map_apply (by fun_prop) hS,
    Measure.map_apply
      (measurable_gaussianScaleMixtureObservable
        (measurable_realEdgeNormalizedCofactorVarianceNNReal n)) hS,
    Measure.prod_apply hleft, Measure.prod_apply hright]
  apply lintegral_congr
  intro A
  change mu
      ((fun g ↦ iidRealLinearForm (realEdgeCofactor A) g / s0) ⁻¹' S) =
    (gaussianReal 0 1)
      ((fun z ↦ Real.sqrt
        (realEdgeNormalizedCofactorVarianceNNReal n A : ℝ) * z) ⁻¹' S)
  have hlaw := iidRealLinearForm_law (realEdgeCofactor A)
  have hscaled := congrArg
    (Measure.map (fun u : ℝ ↦ u / s0)) hlaw
  rw [Measure.map_map (by fun_prop)
      (measurable_iidRealLinearForm (realEdgeCofactor A)),
    Measure.map_map (by fun_prop) (by fun_prop)] at hscaled
  change Measure.map
      (fun g ↦ iidRealLinearForm (realEdgeCofactor A) g / s0) mu =
    Measure.map
      (fun z ↦ Real.sqrt
        (SymmetricGaussianHafnian.realCoefficientEnergy
          (realEdgeCofactor A)) * z / s0)
      (gaussianReal 0 1) at hscaled
  have hfun :
      (fun z : ℝ ↦
        Real.sqrt
          (SymmetricGaussianHafnian.realCoefficientEnergy
            (realEdgeCofactor A)) * z / s0) =
      (fun z : ℝ ↦ Real.sqrt
        (realEdgeNormalizedCofactorVarianceNNReal n A : ℝ) * z) := by
    funext z
    rw [sqrt_realEdgeNormalizedCofactorVarianceNNReal]
    unfold SymmetricGaussianHafnian.realCoefficientEnergy
      realEdgeCofactorEnergy
    change Real.sqrt (∑ j, realEdgeCofactor A j ^ 2) * z / s0 =
      Real.sqrt (∑ j, realEdgeCofactor A j ^ 2) /
        sharpRealSymmetricHafnianRMS n * z
    dsimp [s0]
    ring
  rw [hfun] at hscaled
  have hscaledSet := congrArg (fun m : Measure ℝ ↦ m S) hscaled
  rw [← Measure.map_apply (by fun_prop) hS,
    ← Measure.map_apply (by fun_prop) hS]
  simpa [d, nu, mu, s0] using hscaledSet

/-- The normalized hafnian is the normalized Gaussian scale mixture. -/
theorem map_normalizedRealSymmetricGaussianHafnian_eq_mixture
    {n : ℕ} (hn : 1 ≤ n) :
    Measure.map (sharpRealNormalizedSymmetricHafnianObservable n)
        (realEdgeGaussian (Fin (2 * n))) =
      Measure.map
        (gaussianScaleMixtureObservable
          (realEdgeNormalizedCofactorVarianceNNReal n))
        ((realEdgeGaussian (Fin (2 * n - 1))).prod
          (gaussianReal 0 1)) := by
  have hraw :
      Measure.map realEdgeHafnian (realEdgeGaussian (Fin (2 * n))) =
        Measure.map
          (gaussianScaleMixtureObservable
            (realEdgeCofactorVarianceNNReal :
              (Edge (Fin (2 * n - 1)) → ℝ) → ℝ≥0))
          ((realEdgeGaussian (Fin (2 * n - 1))).prod
            (gaussianReal 0 1)) := by
    have h :=
      map_realEdgeHafnian_eq_gaussianScaleMixtureObservable (2 * n - 1)
    have hsize : 2 * n - 1 + 1 = 2 * n := by omega
    rw [hsize] at h
    exact h
  have hscaled := congrArg
    (Measure.map
      (fun u : ℝ ↦ u / sharpRealSymmetricHafnianRMS n)) hraw
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop)
      (measurable_gaussianScaleMixtureObservable
        measurable_realEdgeCofactorVarianceNNReal)] at hscaled
  have hleft :
      (fun u : ℝ ↦ u / sharpRealSymmetricHafnianRMS n) ∘
          realEdgeHafnian =
        sharpRealNormalizedSymmetricHafnianObservable n := by
    rfl
  have hright :
      (fun u : ℝ ↦ u / sharpRealSymmetricHafnianRMS n) ∘
          gaussianScaleMixtureObservable
            (realEdgeCofactorVarianceNNReal :
              (Edge (Fin (2 * n - 1)) → ℝ) → ℝ≥0) =
        gaussianScaleMixtureObservable
          (realEdgeNormalizedCofactorVarianceNNReal n) := by
    funext p
    simp only [Function.comp_apply, gaussianScaleMixtureObservable]
    rw [sqrt_realEdgeNormalizedCofactorVarianceNNReal]
    change Real.sqrt (realEdgeCofactorEnergy p.1) * p.2 /
        sharpRealSymmetricHafnianRMS n =
      Real.sqrt (realEdgeCofactorEnergy p.1) /
        sharpRealSymmetricHafnianRMS n * p.2
    ring
  rw [hleft, hright] at hscaled
  exact hscaled

/-- The normalized mixture density. -/
def sharpRealNormalizedSymmetricHafnianDensity (n : ℕ) (x : ℝ) : ℝ :=
  gaussianScaleMixtureDensity
    (realEdgeGaussian (Fin (2 * n - 1)))
    (realEdgeNormalizedCofactorVarianceNNReal n) x

/-- At zero, normalization multiplies every conditional Gaussian peak by the
root mean square. -/
theorem gaussianPDFReal_normalizedCofactor_zero (n : ℕ)
    (x : Edge (Fin (2 * n - 1)) → ℝ) :
    gaussianPDFReal 0 (realEdgeNormalizedCofactorVarianceNNReal n x) 0 =
      sharpRealSymmetricHafnianRMS n *
        gaussianPDFReal 0 (realEdgeCofactorVarianceNNReal x) 0 := by
  rw [gaussianPDFReal_zero_at_zero, gaussianPDFReal_zero_at_zero,
    sqrt_realEdgeNormalizedCofactorVarianceNNReal]
  have hs : sharpRealSymmetricHafnianRMS n ≠ 0 :=
    (sharpRealSymmetricHafnianRMS_pos n).ne'
  change (Real.sqrt (2 * Real.pi))⁻¹ *
      (Real.sqrt (realEdgeCofactorEnergy x) /
        sharpRealSymmetricHafnianRMS n)⁻¹ =
    sharpRealSymmetricHafnianRMS n *
      ((Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.sqrt (realEdgeCofactorEnergy x))⁻¹)
  rw [inv_div]
  ring

/-- The normalized conditional peak is integrable. -/
theorem integrable_realEdgeNormalizedCofactorGaussianPeak
    {n : ℕ} (hn : 1 ≤ n) :
    Integrable
      (fun x : Edge (Fin (2 * n - 1)) → ℝ ↦
        gaussianPDFReal 0
          (realEdgeNormalizedCofactorVarianceNNReal n x) 0)
      (realEdgeGaussian (Fin (2 * n - 1))) := by
  have h := (integrable_realEdgeCofactorGaussianPeak hn).const_mul
    (sharpRealSymmetricHafnianRMS n)
  exact h.congr <| Filter.Eventually.of_forall fun x ↦
    (gaussianPDFReal_normalizedCofactor_zero n x).symm

/-- The normalized real symmetric Gaussian hafnian density is continuous. -/
theorem continuous_sharpRealNormalizedSymmetricHafnianDensity
    {n : ℕ} (hn : 1 ≤ n) :
    Continuous (sharpRealNormalizedSymmetricHafnianDensity n) := by
  unfold sharpRealNormalizedSymmetricHafnianDensity
  exact continuous_gaussianScaleMixtureDensity
    (realEdgeGaussian (Fin (2 * n - 1)))
    (measurable_realEdgeNormalizedCofactorVarianceNNReal n)
    (ae_realEdgeNormalizedCofactorVarianceNNReal_ne_zero hn)
    (integrable_realEdgeNormalizedCofactorGaussianPeak hn)

/-- The normalized density is nonnegative and pointwise maximized at zero. -/
theorem sharpRealNormalizedSymmetricHafnianDensity_nonneg_and_le_zero
    {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    0 ≤ sharpRealNormalizedSymmetricHafnianDensity n x ∧
      sharpRealNormalizedSymmetricHafnianDensity n x ≤
        sharpRealNormalizedSymmetricHafnianDensity n 0 := by
  unfold sharpRealNormalizedSymmetricHafnianDensity
  constructor
  · exact gaussianScaleMixtureDensity_nonneg
      (realEdgeGaussian (Fin (2 * n - 1)))
      (realEdgeNormalizedCofactorVarianceNNReal n) x
  · exact gaussianScaleMixtureDensity_le_zero
      (realEdgeGaussian (Fin (2 * n - 1)))
      (measurable_realEdgeNormalizedCofactorVarianceNNReal n)
      (integrable_realEdgeNormalizedCofactorGaussianPeak hn) x

/-- The normalized density is even. -/
theorem even_sharpRealNormalizedSymmetricHafnianDensity
    {n : ℕ} (hn : 1 ≤ n) :
    Function.Even (sharpRealNormalizedSymmetricHafnianDensity n) := by
  intro x
  unfold sharpRealNormalizedSymmetricHafnianDensity
    gaussianScaleMixtureDensity
  apply integral_congr_ae
  filter_upwards [] with w
  exact gaussianPDFReal_zero_neg_symmetric
    (realEdgeNormalizedCofactorVarianceNNReal n w) x

/-- Native `ENNReal` density identity for the normalized real symmetric
Gaussian hafnian. -/
theorem map_normalizedRealSymmetricGaussianHafnian_eq_withDensityENN
    {n : ℕ} (hn : 1 ≤ n) :
    Measure.map (sharpRealNormalizedSymmetricHafnianObservable n)
        (realEdgeGaussian (Fin (2 * n))) =
      volume.withDensity
        (gaussianScaleMixtureDensityENN
          (realEdgeGaussian (Fin (2 * n - 1)))
          (realEdgeNormalizedCofactorVarianceNNReal n)) := by
  rw [map_normalizedRealSymmetricGaussianHafnian_eq_mixture hn]
  exact map_gaussianScaleMixtureObservable_eq_withDensity
    (realEdgeGaussian (Fin (2 * n - 1)))
    (measurable_realEdgeNormalizedCofactorVarianceNNReal n)
    (ae_realEdgeNormalizedCofactorVarianceNNReal_ne_zero hn)

/-- The native extended density agrees with the real-valued normalized
mixture density. -/
theorem gaussianScaleMixtureDensityENN_eq_ofReal_normalizedSymmetricDensity
    {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    gaussianScaleMixtureDensityENN
        (realEdgeGaussian (Fin (2 * n - 1)))
        (realEdgeNormalizedCofactorVarianceNNReal n) x =
      ENNReal.ofReal
        (sharpRealNormalizedSymmetricHafnianDensity n x) := by
  have hint := integrable_gaussianScaleMixtureKernel
    (realEdgeGaussian (Fin (2 * n - 1)))
    (measurable_realEdgeNormalizedCofactorVarianceNNReal n)
    (integrable_realEdgeNormalizedCofactorGaussianPeak hn) x
  have hnonneg :
      ∀ᵐ A ∂realEdgeGaussian (Fin (2 * n - 1)),
        0 ≤ gaussianPDFReal 0
          (realEdgeNormalizedCofactorVarianceNNReal n A) x :=
    Filter.Eventually.of_forall fun A ↦ gaussianPDFReal_nonneg 0 _ x
  symm
  simpa [sharpRealNormalizedSymmetricHafnianDensity,
    gaussianScaleMixtureDensity, gaussianScaleMixtureDensityENN,
    gaussianPDF] using ofReal_integral_eq_lintegral_ofReal hint hnonneg

/-- The normalized independent-edge hafnian law has the stated continuous
Gaussian-mixture density. -/
theorem map_normalizedRealSymmetricGaussianHafnian_eq_withDensity
    {n : ℕ} (hn : 1 ≤ n) :
    Measure.map (sharpRealNormalizedSymmetricHafnianObservable n)
        (realEdgeGaussian (Fin (2 * n))) =
      volume.withDensity
        (fun x ↦ ENNReal.ofReal
          (sharpRealNormalizedSymmetricHafnianDensity n x)) := by
  rw [map_normalizedRealSymmetricGaussianHafnian_eq_withDensityENN hn]
  congr 1
  funext x
  exact
    gaussianScaleMixtureDensityENN_eq_ofReal_normalizedSymmetricDensity hn x

/-- Integrability of the inverse conditional standard deviation in the raw
cofactor coordinates. -/
theorem integrable_realEdgeCofactorEnergy_inverseSqrt
    {n : ℕ} (hn : 1 ≤ n) :
    Integrable
      (fun x : Edge (Fin (2 * n - 1)) → ℝ ↦
        (Real.sqrt (realEdgeCofactorEnergy x))⁻¹)
      (realEdgeGaussian (Fin (2 * n - 1))) := by
  let g : (Edge (Fin (2 * n - 1)) → ℝ) → ℝ :=
    fun x ↦ (Real.sqrt (realEdgeCofactorEnergy x))⁻¹
  have hgmeas : Measurable g := by
    dsimp [g]
    fun_prop
  have hgnonneg : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g]
    positivity
  refine ⟨hgmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hgnonneg)]
  have hfinite :=
    ennInverseSqrtMoment_realEdgeCofactorVariance_ne_top hn
  unfold ennInverseSqrtMoment at hfinite
  change (∫⁻ x : Edge (Fin (2 * n - 1)) → ℝ,
      ENNReal.ofReal (Real.sqrt (realEdgeCofactorEnergy x))⁻¹
      ∂realEdgeGaussian (Fin (2 * n - 1))) ≠ ∞ at hfinite
  simpa [g] using (lt_top_iff_ne_top.2 hfinite)

/-- The paper's ordinary real expectation `E[V_n^{-1/2}]`.  Keeping this
as a named real integral provides an exact bridge from the robust `ENNReal`
recursion to the notation used in Appendix D. -/
def realEdgeCofactorInverseSqrtExpectation (n : ℕ) : ℝ :=
  ∫ x : Edge (Fin (2 * n - 1)) → ℝ,
    (Real.sqrt (realEdgeCofactorEnergy x))⁻¹
    ∂realEdgeGaussian (Fin (2 * n - 1))

/-- The real expectation is exactly the extended-nonnegative half-inverse
moment used by the recursion. -/
theorem ofReal_realEdgeCofactorInverseSqrtExpectation_eq
    {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (realEdgeCofactorInverseSqrtExpectation n) =
      SymmetricGaussianHafnian.realCofactorHalfInverseMoment n := by
  let nu : Measure (Edge (Fin (2 * n - 1)) → ℝ) :=
    realEdgeGaussian (Fin (2 * n - 1))
  let g : (Edge (Fin (2 * n - 1)) → ℝ) → ℝ :=
    fun x ↦ (Real.sqrt (realEdgeCofactorEnergy x))⁻¹
  have hgint : Integrable g nu := by
    simpa [nu, g] using integrable_realEdgeCofactorEnergy_inverseSqrt hn
  have hgnonneg : ∀ᵐ x ∂nu, 0 ≤ g x :=
    Filter.Eventually.of_forall fun x ↦ by
      dsimp [g]
      positivity
  rw [show realEdgeCofactorInverseSqrtExpectation n =
      ∫ x, g x ∂nu by rfl]
  rw [ofReal_integral_eq_lintegral_ofReal hgint hgnonneg]
  rw [← ennInverseSqrtMoment_realEdgeCofactorVariance_eq hn]
  rfl

/-- Literal conditional-Gaussian expectation formula for the raw density.
This is the pointwise integrand printed in D126, with
`V = realEdgeCofactorEnergy A`. -/
theorem sharpRealSymmetricHafnianDensity_expectationFormula
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    sharpRealSymmetricHafnianDensity n t =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ A : Edge (Fin (2 * n - 1)) → ℝ,
          (Real.sqrt (realEdgeCofactorEnergy A))⁻¹ *
            Real.exp (-(t ^ 2) / (2 * realEdgeCofactorEnergy A))
          ∂realEdgeGaussian (Fin (2 * n - 1)) := by
  unfold sharpRealSymmetricHafnianDensity gaussianScaleMixtureDensity
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_realEdgeCofactorVarianceNNReal_ne_zero hn] with A hA
  have hV : 0 < realEdgeCofactorEnergy A := by
    have hnonneg := realEdgeCofactorEnergy_nonneg A
    have hne : realEdgeCofactorEnergy A ≠ 0 := by
      intro hz
      apply hA
      apply NNReal.eq
      exact hz
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  unfold gaussianPDFReal realEdgeCofactorVarianceNNReal
  rw [show ((↑⟨realEdgeCofactorEnergy A,
      realEdgeCofactorEnergy_nonneg A⟩ : ℝ≥0) : ℝ) =
      realEdgeCofactorEnergy A by rfl]
  rw [show Real.sqrt (2 * Real.pi * realEdgeCofactorEnergy A) =
      Real.sqrt (2 * Real.pi) *
        Real.sqrt (realEdgeCofactorEnergy A) by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]]
  have hs1 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hs2 : Real.sqrt (realEdgeCofactorEnergy A) ≠ 0 := by positivity
  simp only [sub_zero]
  field_simp [hs1, hs2]

/-- The raw mixture density integrates to one.  This supplies the
`Integrable` bridge needed to express measurable-set probabilities using the
ordinary real integral printed in the paper. -/
theorem integrable_sharpRealSymmetricHafnianDensity
    {n : ℕ} (hn : 1 ≤ n) :
    Integrable (sharpRealSymmetricHafnianDensity n) volume := by
  have hmeas : Measurable (sharpRealSymmetricHafnianDensity n) :=
    (continuous_sharpRealSymmetricHafnianDensity hn).measurable
  have hnonneg : ∀ᵐ x ∂volume,
      0 ≤ sharpRealSymmetricHafnianDensity n x :=
    Filter.Eventually.of_forall fun x ↦
      (sharpRealSymmetricHafnianDensity_nonneg_and_le_zero hn x).1
  have hLaw := map_realSymmetricGaussianHafnian_eq_withDensity hn
  have hmass := congrArg (fun mu : Measure ℝ ↦ mu Set.univ) hLaw
  have hlintegral :
      (∫⁻ x, ENNReal.ofReal (sharpRealSymmetricHafnianDensity n x)
        ∂volume) = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ] at hmass
    calc
      (∫⁻ x, ENNReal.ofReal (sharpRealSymmetricHafnianDensity n x)
          ∂volume) =
          Measure.map realEdgeHafnian
            (realEdgeGaussian (Fin (2 * n))) Set.univ := by
              simpa using hmass.symm
      _ = 1 := by
        rw [Measure.map_apply measurable_realEdgeHafnian
          MeasurableSet.univ]
        simp
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnonneg, hlintegral]
  exact ENNReal.one_lt_top

/-- Real-integral form of the verified inverse-half-moment estimate. -/
theorem integral_realEdgeCofactorEnergy_inverseSqrt_le_realGammaProduct
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ x : Edge (Fin (2 * n - 1)) → ℝ,
        (Real.sqrt (realEdgeCofactorEnergy x))⁻¹
        ∂realEdgeGaussian (Fin (2 * n - 1))) ≤
      SymmetricGaussianHafnian.realGammaProduct n := by
  let nu : Measure (Edge (Fin (2 * n - 1)) → ℝ) :=
    realEdgeGaussian (Fin (2 * n - 1))
  let g : (Edge (Fin (2 * n - 1)) → ℝ) → ℝ :=
    fun x ↦ (Real.sqrt (realEdgeCofactorEnergy x))⁻¹
  have hlintegral :
      ENNReal.ofReal (∫ x, g x ∂nu) =
        SymmetricGaussianHafnian.realCofactorHalfInverseMoment n := by
    simpa [nu, g, realEdgeCofactorInverseSqrtExpectation] using
      ofReal_realEdgeCofactorInverseSqrtExpectation_eq hn
  have hENN :
      ENNReal.ofReal (∫ x, g x ∂nu) ≤
        ENNReal.ofReal
          (SymmetricGaussianHafnian.realGammaProduct n) := by
    rw [hlintegral]
    exact SymmetricGaussianHafnian.realCofactorHalfInverseMoment_le n hn
  have hreal :=
    (ENNReal.ofReal_le_ofReal_iff
      (SymmetricGaussianHafnian.realGammaProduct_nonneg n)).mp hENN
  simpa [nu, g] using hreal

/-- The raw Gaussian-mixture density at zero is controlled by the verified
Gamma product. -/
theorem sharpRealSymmetricHafnianDensity_zero_le_gammaProduct
    {n : ℕ} (hn : 1 ≤ n) :
    sharpRealSymmetricHafnianDensity n 0 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        SymmetricGaussianHafnian.realGammaProduct n := by
  unfold sharpRealSymmetricHafnianDensity gaussianScaleMixtureDensity
  simp_rw [gaussianPDFReal_zero_at_zero]
  change (∫ x : Edge (Fin (2 * n - 1)) → ℝ,
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.sqrt (realEdgeCofactorEnergy x))⁻¹
      ∂realEdgeGaussian (Fin (2 * n - 1))) ≤ _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_realEdgeCofactorEnergy_inverseSqrt_le_realGammaProduct hn)
    (by positivity)

/-- The normalized peak is the root-mean-square factor times the raw peak. -/
theorem sharpRealNormalizedSymmetricHafnianDensity_zero_eq
    (n : ℕ) :
    sharpRealNormalizedSymmetricHafnianDensity n 0 =
      sharpRealSymmetricHafnianRMS n *
        sharpRealSymmetricHafnianDensity n 0 := by
  unfold sharpRealNormalizedSymmetricHafnianDensity
    sharpRealSymmetricHafnianDensity gaussianScaleMixtureDensity
  simp_rw [gaussianPDFReal_normalizedCofactor_zero]
  rw [integral_const_mul]

/-- Elementary identity between the Gaussian peak constants. -/
theorem inv_sqrt_two_pi_eq_half_sqrt_two_div_pi :
    (Real.sqrt (2 * Real.pi))⁻¹ =
      Real.sqrt (2 / Real.pi) / 2 := by
  have htwo :
      2 / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : Real.sqrt 2 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hpi : Real.sqrt Real.pi ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    field_simp [h2, hpi]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ =
        (2 / Real.sqrt (2 * Real.pi)) / 2 := by ring
    _ = Real.sqrt (2 / Real.pi) / 2 := by rw [htwo]

/-- The normalized density peak is at most half of the paper's exact
small-ball coefficient. -/
theorem sharpRealNormalizedSymmetricHafnianDensity_zero_le_coefficient_half
    {n : ℕ} (hn : 1 ≤ n) :
    sharpRealNormalizedSymmetricHafnianDensity n 0 ≤
      sharpRealSymmetricSmallBallCoefficient n / 2 := by
  rw [sharpRealNormalizedSymmetricHafnianDensity_zero_eq]
  calc
    sharpRealSymmetricHafnianRMS n *
        sharpRealSymmetricHafnianDensity n 0 ≤
      sharpRealSymmetricHafnianRMS n *
        ((Real.sqrt (2 * Real.pi))⁻¹ *
          SymmetricGaussianHafnian.realGammaProduct n) :=
      mul_le_mul_of_nonneg_left
        (sharpRealSymmetricHafnianDensity_zero_le_gammaProduct hn)
        (sharpRealSymmetricHafnianRMS_pos n).le
    _ = sharpRealSymmetricSmallBallCoefficient n / 2 := by
      rw [inv_sqrt_two_pi_eq_half_sqrt_two_div_pi,
        sharpRealSymmetricSmallBallCoefficient,
        SymmetricGaussianHafnian.realHafnianSmallBallCoefficient_eq_gammaProduct]
      unfold sharpRealSymmetricHafnianRMS
      ring

/-- The table's explicit `n^(3/8)` upper bound for the normalized density
peak. -/
theorem sharpRealNormalizedSymmetricHafnianDensity_zero_le_threeEighth
    {n : ℕ} (hn : 1 ≤ n) :
    sharpRealNormalizedSymmetricHafnianDensity n 0 ≤
      (1 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) := by
  calc
    sharpRealNormalizedSymmetricHafnianDensity n 0 ≤
        sharpRealSymmetricSmallBallCoefficient n / 2 :=
      sharpRealNormalizedSymmetricHafnianDensity_zero_le_coefficient_half hn
    _ ≤ ((2 / Real.sqrt Real.pi) *
          (n : ℝ) ^ (3 / 8 : ℝ)) / 2 :=
      div_le_div_of_nonneg_right
        (sharpRealSymmetricSmallBallCoefficient_threeEighth_twoSided hn).2
        (by norm_num)
    _ = (1 / Real.sqrt Real.pi) *
        (n : ℝ) ^ (3 / 8 : ℝ) := by ring

end

end LogdetLean.GramHafnian
