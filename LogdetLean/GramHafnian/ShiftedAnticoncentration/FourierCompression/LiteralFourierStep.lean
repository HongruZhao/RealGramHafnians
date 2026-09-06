import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.LiteralCofactorLaw
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.LocalCofactorCompression
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorAlmostSurePositivity
/-!
# The literal Fourier-compression inverse-moment step

This module transports the finite-coordinate analytic compression theorem to
the literal odd hafnian-cofactor vector and proves the exact `W_r` to
`V_{r-1}` inverse-moment inequality used in the paper recurrence.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ENNReal Real

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 2000000

/-- Reindexing a finite Gram-cofactor characteristic function along an
equivalence of its column labels does not change it. -/
theorem finiteGramCofactorCharacteristic_reindex_equiv'
    {alpha beta : Type*} [Fintype alpha] [LinearOrder alpha]
    [Fintype beta] [LinearOrder beta] {k : ℕ}
    (e : alpha ≃ beta) (w : beta → ℂ) :
    finiteGramCofactorCharacteristic alpha k (fun i ↦ w (e i)) =
      finiteGramCofactorCharacteristic beta k w := by
  let Col := Fin k → ℂ
  let mu : Measure Col := circularGaussianVector k
  let g :=
    (MeasurableEquiv.piCongrLeft (fun _ : beta ↦ Col) e).symm
  have hg : MeasurePreserving g
      (Measure.pi fun _ : beta ↦ mu)
      (Measure.pi fun _ : alpha ↦ mu) := by
    have h := (measurePreserving_piCongrLeft
      (α := fun _ : beta ↦ Col)
      (fun _ : beta ↦ mu) e)
    simpa [g] using h.symm
  unfold finiteGramCofactorCharacteristic
  rw [← hg.integral_comp']
  apply integral_congr_ae
  filter_upwards [] with A
  unfold finiteGramCofactorPhaseCharacter
  congr 2
  have hgA : g A = fun i ↦ A (e i) := by
    rfl
  rw [hgA]
  exact congrArg ((↑) : ℝ → ℂ)
    (finiteGramCofactorPhase_reindex_equiv e A w)

/-- The canonically enumerated literal odd-cofactor characteristic function
is exactly the finite `Fin (2r-1)` Gram-cofactor characteristic function to
which the analytic compression theorem applies. -/
theorem oddCofactorRawCharacteristic_eq_finite
    {r k : ℕ} (hr : 1 ≤ r) (w : Fin (2 * r - 1) → ℂ) :
    oddCofactorRawCharacteristic (k := k) hr w =
      finiteGramCofactorCharacteristic (Fin (2 * r - 1)) k w := by
  unfold oddCofactorRawCharacteristic
  rw [oddHafnianCofactorCharacteristic_eq_finite]
  exact finiteGramCofactorCharacteristic_reindex_equiv'
    (finOddCofactorEquiv r hr).symm w

/-- The canonical first odd-cofactor coordinate in the `Fin (2r-1)`
enumeration. -/
def finOddFirstCofactorIndex (r : ℕ) (hr : 1 ≤ r) :
    Fin (2 * r - 1) :=
  (finOddCofactorEquiv r hr).symm (oddFirstCofactorIndex r hr)

/-- The singleton formula from the literal odd index, transported to the
canonical `Fin` enumeration. -/
theorem oddCofactorRawCharacteristic_singleton_first
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r) (t : ℝ) :
    oddCofactorRawCharacteristic (k := k) hr
        (singleCoordinate (finOddFirstCofactorIndex r hr) (t : ℂ)) =
      (((∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℂ),
          Real.exp (-(pastCofactorV (by omega) A * t ^ 2) / 4)
          ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
            circularGaussianVector k)) : ℝ) : ℂ) := by
  unfold oddCofactorRawCharacteristic
  rw [show (fun j ↦
      singleCoordinate (finOddFirstCofactorIndex r hr) (t : ℂ)
        ((finOddCofactorEquiv r hr).symm j)) =
      singleCoordinate (oddFirstCofactorIndex r hr) (t : ℂ) by
    funext j
    simp [singleCoordinate, finOddFirstCofactorIndex]]
  exact oddHafnianCofactorCharacteristic_singleton_first hr hr2 t

/-- Positivity of the column-combination energy forces positivity of the
cofactor-vector energy. -/
theorem pastCofactorW_pos_of_pastCofactorV_pos
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hV : 0 < pastCofactorV hr A) :
    0 < pastCofactorW hr A := by
  by_contra hW
  have hWzero : pastCofactorW hr A = 0 :=
    le_antisymm (le_of_not_gt hW) (pastCofactorW_nonneg hr A)
  have hterms : ∀ j : OddCofactorIndex r hr,
      Complex.normSq (pastHafnianCofactorVector hr A j) = 0 := by
    have hsum : (∑ j : OddCofactorIndex r hr,
        Complex.normSq (pastHafnianCofactorVector hr A j)) = 0 := by
      rwa [← pastCofactorW_eq_sum_normSq]
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _hi ↦ Complex.normSq_nonneg
        (pastHafnianCofactorVector hr A i))).mp hsum j
      (Finset.mem_univ j)
  have hCzero : pastHafnianCofactorVector hr A = 0 := by
    funext j
    exact Complex.normSq_eq_zero.mp (hterms j)
  have hOddzero :
      oddHafnianCofactorVector hr (pastCofactorMatrix hr A) = 0 := by
    simpa [pastHafnianCofactorVector] using hCzero
  have hVzero : pastCofactorV hr A = 0 := by
    unfold pastCofactorV oddCofactorV oddCofactorColumnCombination
    simp [hOddzero]
  linarith

/-- In the paper range the literal past cofactor norm is strictly positive
almost surely. -/
theorem ae_pastCofactorW_pos
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        circularGaussianVector k),
      0 < pastCofactorW hr A := by
  have hVfull :=
    ae_oddCofactorV_pos_circularGaussianColumnMatrix hr hk
  have hVpast :=
    ae_pastCofactorV_pos_of_ae_oddCofactorV_pos hr hVfull
  filter_upwards [hVpast] with A hA
  exact pastCofactorW_pos_of_pastCofactorV_pos hr A hA

/-- The mapped Euclidean law is almost surely away from the origin. -/
theorem ae_norm_sq_pastConjugateCofactorEuclideanLaw_pos
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ x ∂(pastConjugateCofactorEuclideanLaw r k hr),
      0 < ‖x‖ ^ 2 := by
  unfold pastConjugateCofactorEuclideanLaw
  apply (ae_map_iff
    (measurable_pastConjugateCofactorEuclidean hr).aemeasurable
    (measurableSet_lt measurable_const
      (measurable_id.norm.pow_const 2))).2
  filter_upwards [ae_pastCofactorW_pos hr hk] with A hA
  change 0 < ‖pastConjugateCofactorEuclidean hr A‖ ^ 2
  rwa [norm_sq_pastConjugateCofactorEuclidean]

/-- Its inverse squared-norm moment is literally the inverse moment of
`pastCofactorW`. -/
theorem ennInverseMoment_pastConjugateCofactorEuclideanLaw_norm_sq
    {r k : ℕ} (hr : 1 ≤ r) :
    ennInverseMoment (pastConjugateCofactorEuclideanLaw r k hr)
        (fun x ↦ ‖x‖ ^ 2) =
      ennInverseMoment
        (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)
        (pastCofactorW hr) := by
  unfold ennInverseMoment pastConjugateCofactorEuclideanLaw
  rw [lintegral_map (by fun_prop)
    (measurable_pastConjugateCofactorEuclidean hr)]
  apply lintegral_congr
  intro A
  change ENNReal.ofReal
      (‖pastConjugateCofactorEuclidean hr A‖ ^ 2)⁻¹ =
    ENNReal.ofReal (pastCofactorW hr A)⁻¹
  rw [norm_sq_pastConjugateCofactorEuclidean]

/-- **Literal Fourier step (H1).**  At level `r ≥ 2`, the inverse moment of
the odd cofactor norm is bounded by the lower-level conditional-variance
inverse moment times the exact auxiliary-Gamma factor `(2r-2)⁻¹`.

The rank assumption is used only for the already-proved almost-sure
positivity of the two literal random variables. -/
theorem pastCofactorWInverseMoment_le_fourier
    (k r : ℕ) (hr2 : 2 ≤ r) (hk : 2 * r - 1 ≤ k) :
    pastCofactorWInverseMoment k r ≤
      pastCofactorVInverseMoment k (r - 1) *
        ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹) := by
  let hr : 1 ≤ r := by omega
  let hrlow : 1 ≤ r - 1 := by omega
  let mu := pastConjugateCofactorEuclideanLaw r k hr
  let nu : Measure
      (OddCofactorIndex (r - 1) hrlow → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
      circularGaussianVector k
  let V : (OddCofactorIndex (r - 1) hrlow → (Fin k → ℂ)) → ℝ :=
    pastCofactorV hrlow
  let rawPhi : (Fin (2 * r - 1) → ℂ) → ℂ :=
    finiteGramCofactorCharacteristic (Fin (2 * r - 1)) k
  have hrawPhi : ∀ xi : CircularEuclideanSpace (2 * r - 1),
      rawPhi (fun i ↦ xi i) = charFun mu xi := by
    intro xi
    dsimp only [rawPhi, mu]
    rw [← oddCofactorRawCharacteristic_eq_finite hr]
    exact oddCofactorRawCharacteristic_eq_charFun hr xi
  have hsym :
      SingletonExchangeable rawPhi ∧ CommonPhaseInvariant rawPhi := by
    dsimp only [rawPhi]
    apply finiteGramCofactorCharacteristic_compression_symmetries
      (d := 2 * r - 2)
    · rw [Fintype.card_fin]
      omega
    · omega
    · exact ⟨r - 1, by omega⟩
  have htwo : ∀ z : Fin (2 * r - 1) → ℂ,
      1 < coordinateSupportCard z →
      ∃ zLeft zRight : Fin (2 * r - 1) → ℂ,
        coordinateSupportCard zLeft < coordinateSupportCard z ∧
        coordinateSupportCard zRight < coordinateSupportCard z ∧
        coordinateEnergy zLeft = coordinateEnergy z ∧
        coordinateEnergy zRight = coordinateEnergy z ∧
        ‖rawPhi z‖ ≤ max ‖rawPhi zLeft‖ ‖rawPhi zRight‖ := by
    have hdim : (2 * r - 3) + 2 = 2 * r - 1 := by omega
    dsimp only [rawPhi]
    have h := finiteGramCofactorCharacteristic_global_two_endpoints
      (2 * r - 3) k
    rw [hdim] at h
    exact h
  have hsingleton : ∀ t : ℝ, 0 ≤ t →
      rawPhi (singleCoordinate (finOddFirstCofactorIndex r hr) (t : ℂ)) =
        ((∫ A, Real.exp (-(V A * t ^ 2) / 4) ∂nu) : ℝ) := by
    intro t _ht
    dsimp only [rawPhi]
    rw [← oddCofactorRawCharacteristic_eq_finite hr]
    simpa only [V, nu] using
      (oddCofactorRawCharacteristic_singleton_first
        (k := k) hr hr2 t)
  have hVnonneg : ∀ A, 0 ≤ V A := by
    intro A
    exact pastCofactorV_nonneg hrlow A
  have hVpos : ∀ᵐ A ∂nu, 0 < V A := by
    have hfull := ae_oddCofactorV_pos_circularGaussianColumnMatrix
      hrlow (by omega : 2 * (r - 1) - 1 ≤ k)
    have hpast :=
      ae_pastCofactorV_pos_of_ae_oddCofactorV_pos hrlow hfull
    simpa only [nu, V] using hpast
  have hnormpos : ∀ᵐ x ∂mu, 0 < ‖x‖ ^ 2 := by
    dsimp only [mu]
    exact ae_norm_sq_pastConjugateCofactorEuclideanLaw_pos hr hk
  have hmain :=
    ennInverse_norm_sq_le_auxiliaryGamma_factor_of_two_endpoints
      (Omega := OddCofactorIndex (r - 1) hrlow → (Fin k → ℂ))
      (d := 2 * r - 1) (by omega)
      (finOddFirstCofactorIndex r hr)
      mu nu V (measurable_pastCofactorV hrlow)
      hVnonneg hVpos rawPhi hrawPhi hsym.1 hsym.2 htwo
      hsingleton hnormpos
  have hfactor :
      ((((2 * r - 1 : ℕ) : ℝ) - 1)⁻¹) =
        (((2 : ℝ) * r - 2)⁻¹) := by
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  rw [pastCofactorWInverseMoment_eq hr,
    ← ennInverseMoment_pastConjugateCofactorEuclideanLaw_norm_sq hr,
    pastCofactorVInverseMoment_eq hrlow]
  simpa only [mu, nu, V, hfactor] using hmain

end

end LogdetLean.GramHafnian
