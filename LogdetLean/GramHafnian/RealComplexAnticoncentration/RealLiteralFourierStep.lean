import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGlobalCofactorCompression
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealFourierGammaFactor
/-!
# Literal real Fourier step

The generic finite real Gram-cofactor characteristic is identified with the
canonically enumerated literal odd-cofactor law.  Consequently the completed
two-column compression theorem applies directly to the random vector whose
squared norm is `pastRealCofactorW`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 2000000

theorem realOddHafnianCofactorVector_eq_finiteRealGramCofactorVector
    {r k : ℕ} (hr : 1 ≤ r) (X : RealColumnMatrix r k)
    (j : OddCofactorIndex r hr) :
    realOddHafnianCofactorVector hr X j =
      finiteRealGramCofactorVector
        (fun i : OddCofactorIndex r hr ↦ X i.1) j := by
  unfold realOddHafnianCofactorVector hafnianPairCofactor
    finiteRealGramCofactorVector
  let e := oddDeleteOrderIsoPairComplement r hr j
  rw [← typeHafnian_reindex_orderIso e
    (fun i l : TypePerfectMatching.PairComplement
      (evenLastIndex r hr) j.1 ↦
      transposeGram (realRowMatrix X) i.1 l.1)]
  rfl

theorem realOddHafnianCofactorVector_pastRealCofactorMatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ))
    (j : OddCofactorIndex r hr) :
    realOddHafnianCofactorVector hr (pastRealCofactorMatrix hr A) j =
      finiteRealGramCofactorVector A j := by
  rw [realOddHafnianCofactorVector_eq_finiteRealGramCofactorVector]
  apply congrArg (fun B ↦ finiteRealGramCofactorVector B j)
  funext i p
  exact congrArg (fun f ↦ f p)
    (realLastColumnProductEquiv_apply_nonlast hr (A, 0) i)

theorem pastRealHafnianCofactorVector_eq_finiteRealGramCofactorVector
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ))
    (j : OddCofactorIndex r hr) :
    pastRealHafnianCofactorVector hr A j =
      finiteRealGramCofactorVector A j := by
  exact realOddHafnianCofactorVector_pastRealCofactorMatrix hr A j

theorem finiteRealGramCofactorCharacteristic_reindex_equiv'
    {alpha beta : Type*} [Fintype alpha] [LinearOrder alpha]
    [Fintype beta] [LinearOrder beta] {k : ℕ}
    (e : alpha ≃ beta) (w : beta → ℝ) :
    finiteRealGramCofactorCharacteristic alpha k (fun i ↦ w (e i)) =
      finiteRealGramCofactorCharacteristic beta k w := by
  let Col := Fin k → ℝ
  let mu : Measure Col := standardRealGaussianVectorMeasure k
  let g := (MeasurableEquiv.piCongrLeft (fun _ : beta ↦ Col) e).symm
  have hg : MeasurePreserving g
      (Measure.pi fun _ : beta ↦ mu)
      (Measure.pi fun _ : alpha ↦ mu) := by
    have h := measurePreserving_piCongrLeft
      (α := fun _ : beta ↦ Col) (fun _ : beta ↦ mu) e
    simpa [g] using h.symm
  unfold finiteRealGramCofactorCharacteristic
  rw [← hg.integral_comp']
  apply integral_congr_ae
  filter_upwards [] with A
  unfold finiteRealGramCofactorPhaseCharacter
  congr 2
  have hgA : g A = fun i ↦ A (e i) := by rfl
  rw [hgA]
  exact congrArg ((↑) : ℝ → ℂ)
    (finiteRealGramCofactorPhase_reindex_equiv e A w)

theorem realOddCofactorRawCharacteristic_eq_finite
    {r k : ℕ} (hr : 1 ≤ r) (w : Fin (2 * r - 1) → ℝ) :
    realOddCofactorRawCharacteristic (k := k) hr w =
      finiteRealGramCofactorCharacteristic (Fin (2 * r - 1)) k w := by
  unfold realOddCofactorRawCharacteristic
  calc
    (∫ A : OddCofactorIndex r hr → (Fin k → ℝ),
        Complex.exp
          (((∑ i : Fin (2 * r - 1),
            w i * pastRealHafnianCofactorVector hr A
              (finOddCofactorEquiv r hr i) : ℝ) : ℂ) * Complex.I)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
          standardRealGaussianVectorMeasure k)) =
      finiteRealGramCofactorCharacteristic (OddCofactorIndex r hr) k
        (fun j ↦ w ((finOddCofactorEquiv r hr).symm j)) := by
          unfold finiteRealGramCofactorCharacteristic
            finiteRealGramCofactorPhaseCharacter finiteRealGramCofactorPhase
          apply integral_congr_ae
          filter_upwards [] with A
          congr 2
          apply congrArg ((↑) : ℝ → ℂ)
          simp_rw [pastRealHafnianCofactorVector_eq_finiteRealGramCofactorVector]
          exact Fintype.sum_equiv (finOddCofactorEquiv r hr)
            (fun i ↦ w i * finiteRealGramCofactorVector A
              (finOddCofactorEquiv r hr i))
            (fun j ↦ w ((finOddCofactorEquiv r hr).symm j) *
              finiteRealGramCofactorVector A j)
            (fun i ↦ by simp)
    _ = finiteRealGramCofactorCharacteristic (Fin (2 * r - 1)) k w := by
      exact finiteRealGramCofactorCharacteristic_reindex_equiv'
        (finOddCofactorEquiv r hr).symm w

/-- Literal radial compression, with the terminal coordinate chosen to be
the one whose singleton law is the lower-level conditional-energy mixture. -/
theorem realOddCofactorRawCharacteristic_radial_compression
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r)
    (w : Fin (2 * r - 1) → ℝ) :
    ‖realOddCofactorRawCharacteristic (k := k) hr w‖ ≤
      ‖realOddCofactorRawCharacteristic (k := k) hr
        (realSingleCoordinate (realFinOddFirstCofactorIndex r hr)
          (Real.sqrt (realCoordinateEnergy w)))‖ := by
  rw [realOddCofactorRawCharacteristic_eq_finite,
    realOddCofactorRawCharacteristic_eq_finite]
  apply finiteRealGramCofactorCharacteristic_radial_compression_dim
  omega

/-- The literal radial estimate written in the exact form consumed by
Gaussian Fourier averaging. -/
theorem pastRealCofactor_charFun_re_le_radial_mixture
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r)
    (xi : RealGaussianEuclideanSpace (2 * r - 1)) :
    (charFun (pastRealCofactorEuclideanLaw r k hr) xi).re ≤
      ∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ),
        Real.exp (-(pastRealCofactorV (by omega) A * ‖xi‖ ^ 2) / 2)
        ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
          standardRealGaussianVectorMeasure k) := by
  let w : Fin (2 * r - 1) → ℝ := fun i ↦ xi i
  have hchar := realOddCofactorRawCharacteristic_eq_charFun
    (k := k) hr xi
  have hrad := realOddCofactorRawCharacteristic_radial_compression
    (k := k) hr hr2 w
  have henergy : realCoordinateEnergy w = ‖xi‖ ^ 2 := by
    exact realCoordinateEnergy_euclideanSpace_coe xi
  calc
    (charFun (pastRealCofactorEuclideanLaw r k hr) xi).re ≤
        ‖charFun (pastRealCofactorEuclideanLaw r k hr) xi‖ :=
      Complex.re_le_norm _
    _ = ‖realOddCofactorRawCharacteristic (k := k) hr w‖ := by
      rw [hchar]
    _ ≤ ‖realOddCofactorRawCharacteristic (k := k) hr
          (realSingleCoordinate (realFinOddFirstCofactorIndex r hr)
            (Real.sqrt (realCoordinateEnergy w)))‖ := hrad
    _ = ∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ),
        Real.exp (-(pastRealCofactorV (by omega) A * ‖xi‖ ^ 2) / 2)
        ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
          standardRealGaussianVectorMeasure k) := by
      rw [realOddCofactorRawCharacteristic_singleton_first hr hr2]
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hnonneg : 0 ≤
          ∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ),
            Real.exp (-(pastRealCofactorV (by omega) A *
              (Real.sqrt (realCoordinateEnergy w)) ^ 2) / 2)
            ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
              standardRealGaussianVectorMeasure k) := by
        exact integral_nonneg fun A ↦ (Real.exp_pos _).le
      rw [abs_of_nonneg hnonneg]
      apply integral_congr_ae
      filter_upwards [] with A
      rw [Real.sq_sqrt (realCoordinateEnergy_nonneg w), henergy]

/-- Pulling the literal cofactor law back to its iid columns identifies its
norm-squared half-resolvent with the resolvent of `pastRealCofactorW`. -/
theorem ennHalfResolvent_pastRealCofactorLaw_norm_sq_eq
    {r k : ℕ} (hr : 1 ≤ r) (lambda : ℝ) :
    ennHalfResolvent (pastRealCofactorEuclideanLaw r k hr)
        (fun x ↦ ‖x‖ ^ 2) lambda =
      ennHalfResolvent
        (Measure.pi fun _ : OddCofactorIndex r hr ↦
          standardRealGaussianVectorMeasure k)
        (pastRealCofactorW hr) lambda := by
  unfold pastRealCofactorEuclideanLaw ennHalfResolvent
  rw [lintegral_map
    ((measurable_ennHalfResolventKernel_comp (by fun_prop) lambda))
    (measurable_pastRealCofactorEuclidean hr)]
  apply lintegral_congr
  intro A
  rw [norm_sq_pastRealCofactorEuclidean]

/-- Exact literal beta-one Fourier step.  The independent Gaussian radius
has dimension `2r-1`, hence chi-square shape `(2r-1)/2`. -/
theorem ennHalfResolvent_pastRealCofactorW_le_product
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ennHalfResolvent
        (Measure.pi fun _ : OddCofactorIndex r hr ↦
          standardRealGaussianVectorMeasure k)
        (pastRealCofactorW hr) lambda ≤
      ennHalfResolvent
        ((Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
            standardRealGaussianVectorMeasure k).prod
          (stdGaussian (RealGaussianEuclideanSpace (2 * r - 1))))
        (fun p ↦ pastRealCofactorV (by omega) p.1 *
          realAuxiliaryNormSq p.2) lambda := by
  rw [← ennHalfResolvent_pastRealCofactorLaw_norm_sq_eq hr]
  exact ennHalfResolvent_norm_sq_le_mul_realAuxiliaryNormSq_of_compression
    (pastRealCofactorEuclideanLaw r k hr)
    (Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
      standardRealGaussianVectorMeasure k)
    (pastRealCofactorV (by omega))
    (measurable_pastRealCofactorV (by omega))
    (pastRealCofactorV_nonneg (by omega))
    (pastRealCofactor_charFun_re_le_radial_mixture hr hr2)
    lambda hlambda

end

end LogdetLean.GramHafnian
