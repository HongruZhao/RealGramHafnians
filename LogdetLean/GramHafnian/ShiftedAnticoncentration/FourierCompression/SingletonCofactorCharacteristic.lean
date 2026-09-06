import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseLiteral
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorAlmostSurePositivity
/-!
# The singleton cofactor characteristic function

This file identifies the canonical singleton Fourier coordinate of the
level-`r` odd cofactor vector with the level-`r-1` Gram hafnian.  Exposing
the last column of that lower-level hafnian then gives the exact conditional
Gaussian kernel `exp (-V_{r-1} t^2 / 4)`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 1600000

/-- Exact phase integral of one transpose-linear form under iid circular
coordinates.  The real scalar convention is the one used by the cofactor
Fourier functional. -/
theorem integral_exp_re_mul_iidCircularTransposeLinearForm
    {k : ℕ} (y : Fin k → ℂ) (t : ℝ) :
    (∫ x : Fin k → ℂ,
        Complex.exp (((((t : ℂ) *
          iidCircularTransposeLinearForm y x).re : ℝ) : ℂ) * Complex.I)
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) =
      Complex.exp (-(((circularCoefficientEnergy y * t ^ 2 : ℝ) : ℂ) / 4)) := by
  let phase : ℂ → ℂ := fun z ↦
    Complex.exp (((((t : ℂ) * z).re : ℝ) : ℂ) * Complex.I)
  have hmap := map_iidCircularTransposeLinearForm_eq_scaled_circular y
  have hmeas := measurable_iidCircularTransposeLinearForm y
  have hphase : phase =
      (fun z : ℂ ↦
        Complex.exp (((inner ℝ z (t : ℂ) : ℝ) : ℂ) * Complex.I)) := by
    funext z
    dsimp [phase]
    congr 2
    norm_cast
    simp [Complex.mul_re]
  have hpush :
      (∫ x : Fin k → ℂ, phase (iidCircularTransposeLinearForm y x)
          ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) =
        ∫ z : ℂ, phase z
          ∂(Measure.map (iidCircularTransposeLinearForm y)
            (Measure.pi fun _ : Fin k ↦ circularGaussian)) := by
    symm
    exact integral_map hmeas.aemeasurable (by fun_prop)
  calc
    (∫ x : Fin k → ℂ,
        Complex.exp (((((t : ℂ) *
          iidCircularTransposeLinearForm y x).re : ℝ) : ℂ) * Complex.I)
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) =
      ∫ z : ℂ, phase z
          ∂(Measure.map (iidCircularTransposeLinearForm y)
            (Measure.pi fun _ : Fin k ↦ circularGaussian)) := by
        simpa [phase] using hpush
    _ = ∫ z : ℂ, phase z
          ∂(Measure.map
            (fun z : ℂ ↦ Real.sqrt (circularCoefficientEnergy y) • z)
            circularGaussian) := by rw [hmap]
    _ = ∫ z : ℂ,
          phase (Real.sqrt (circularCoefficientEnergy y) • z)
          ∂circularGaussian := by
        exact integral_map (by fun_prop) (by fun_prop)
    _ = charFun circularGaussian
          (Real.sqrt (circularCoefficientEnergy y) • (t : ℂ)) := by
        rw [hphase]
        unfold charFun
        apply integral_congr_ae
        filter_upwards [] with z
        congr 2
        rw [real_inner_smul_right]
        simp
        ring
    _ = Complex.exp
          (-(((circularCoefficientEnergy y * t ^ 2 : ℝ) : ℂ) / 4)) := by
        rw [charFun_circularGaussian]
        congr 1
        norm_cast
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
          Real.sq_sqrt (circularCoefficientEnergy_nonneg y),
          Complex.norm_real, Real.norm_eq_abs, sq_abs]
        ring

/-- Exposing the final column of a level-`r` Gram hafnian gives its exact
mixture characteristic function in terms of `V_r`. -/
theorem integral_exp_re_mul_gramHafnian_eq_pastCofactorV_mixture
    {r k : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    (∫ X : ComplexColumnMatrix r k,
        Complex.exp (((((t : ℂ) * gramHafnianObservable r k X).re : ℝ) : ℂ) *
          Complex.I)
        ∂(circularGaussianColumnMatrixMeasure r k)) =
      ∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
        Complex.exp (-(((pastCofactorV hr A * t ^ 2 : ℝ) : ℂ) / 4))
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k) := by
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let mu : Measure (Fin k → ℂ) := circularGaussianVector k
  let e := lastColumnProductEquiv r k hr
  let f : ((OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) → ℂ :=
    fun p ↦ Complex.exp (((((t : ℂ) *
      gramHafnianObservable r k (e p)).re : ℝ) : ℂ) * Complex.I)
  have hf : Integrable f (nu.prod mu) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with p
    rw [Complex.norm_exp]
    simp [f]
  have he := measurePreserving_lastColumnProductEquiv r k hr
  calc
    (∫ X : ComplexColumnMatrix r k,
        Complex.exp (((((t : ℂ) * gramHafnianObservable r k X).re : ℝ) : ℂ) *
          Complex.I)
        ∂(circularGaussianColumnMatrixMeasure r k)) =
      ∫ p, f p ∂(nu.prod mu) := by
        symm
        simpa [f, e, nu, mu] using he.integral_comp'
          (fun X : ComplexColumnMatrix r k ↦
            Complex.exp (((((t : ℂ) * gramHafnianObservable r k X).re : ℝ) : ℂ) *
              Complex.I))
    _ = ∫ A, ∫ x,
          f (A, x) ∂mu ∂nu := by
        exact integral_prod _ hf
    _ = ∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
          Complex.exp (-(((pastCofactorV hr A * t ^ 2 : ℝ) : ℂ) / 4))
          ∂nu := by
        apply integral_congr_ae
        filter_upwards [] with A
        simp_rw [f, e,
          gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm hr]
        change (∫ x : Fin k → ℂ,
            Complex.exp (((((t : ℂ) *
              iidCircularTransposeLinearForm (pastCofactorCombination hr A) x).re : ℝ) : ℂ) *
              Complex.I) ∂mu) = _
        have hgauss :=
          integral_exp_re_mul_iidCircularTransposeLinearForm
            (pastCofactorCombination hr A) t
        simpa [mu, circularGaussianVector,
          pastCofactorV_eq_coefficientEnergy] using hgauss
    _ = ∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
          Complex.exp (-(((pastCofactorV hr A * t ^ 2 : ℝ) : ℂ) / 4))
          ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k) := by
        rfl

/-- Delete the canonical first cofactor coordinate directly on the past
column realization. -/
def canonicalPastCofactorSubmatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    ComplexColumnMatrix (r - 1) k :=
  canonicalCofactorSubmatrix hr (pastCofactorMatrix hr A)

@[fun_prop]
theorem measurable_canonicalPastCofactorSubmatrix
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (canonicalPastCofactorSubmatrix (k := k) hr) := by
  unfold canonicalPastCofactorSubmatrix canonicalCofactorSubmatrix
    pastCofactorMatrix
  fun_prop

/-- The canonical deleted cofactor submatrix of the iid past columns has
exactly the lower-level full iid circular column law. -/
theorem map_canonicalPastCofactorSubmatrix
    (r k : ℕ) (hr : 1 ≤ r) :
    Measure.map (canonicalPastCofactorSubmatrix (k := k) hr)
        (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k) =
      circularGaussianColumnMatrixMeasure (r - 1) k := by
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let mu : Measure (Fin k → ℂ) := circularGaussianVector k
  let e := lastColumnProductEquiv r k hr
  let F := canonicalCofactorSubmatrix (k := k) hr
  let G := canonicalPastCofactorSubmatrix (k := k) hr
  have hfst : MeasurePreserving Prod.fst (nu.prod mu) nu :=
    measurePreserving_fst
  have he := measurePreserving_lastColumnProductEquiv r k hr
  have hcomp : G ∘ Prod.fst = F ∘ e := by
    funext p
    unfold G F canonicalPastCofactorSubmatrix canonicalCofactorSubmatrix
    ext i a
    change pastCofactorMatrix hr p.1 ⟨i.1 + 1, _⟩ a =
      e p ⟨i.1 + 1, _⟩ a
    have hne : (⟨i.1 + 1, by
        have hi := i.2
        omega⟩ : Fin (2 * r)) ≠ evenLastIndex r hr := by
      intro h
      have hv := congrArg Fin.val h
      have hi := i.2
      change i.1 + 1 = 2 * r - 1 at hv
      omega
    let j : OddCofactorIndex r hr :=
      ⟨⟨i.1 + 1, by
        have hi := i.2
        omega⟩, hne⟩
    rw [show (⟨i.1 + 1, by
        have hi := i.2
        omega⟩ : Fin (2 * r)) = j.1 by rfl]
    unfold pastCofactorMatrix
    rw [lastColumnProductEquiv_apply_nonlast hr (p.1, 0) j,
      lastColumnProductEquiv_apply_nonlast hr p j]
  calc
    Measure.map G nu = Measure.map G (Measure.map Prod.fst (nu.prod mu)) := by
      rw [hfst.map_eq]
    _ = Measure.map (G ∘ Prod.fst) (nu.prod mu) := by
      rw [Measure.map_map]
      · exact measurable_canonicalPastCofactorSubmatrix hr
      · exact measurable_fst
    _ = Measure.map (F ∘ e) (nu.prod mu) := by rw [hcomp]
    _ = Measure.map F (Measure.map e (nu.prod mu)) := by
      rw [Measure.map_map]
      · unfold F canonicalCofactorSubmatrix
        fun_prop
      · exact e.measurable
    _ = Measure.map F (circularGaussianColumnMatrixMeasure r k) := by
      rw [he.map_eq]
    _ = circularGaussianColumnMatrixMeasure (r - 1) k := by
      exact map_canonicalCofactorSubmatrix_circularGaussianColumnMatrixMeasure
        r k hr

/-- The canonical singleton Fourier coordinate is exactly the lower-level
conditional-variance mixture required by Fourier compression. -/
theorem oddHafnianCofactorCharacteristic_singleton_first
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r) (t : ℝ) :
    oddHafnianCofactorCharacteristic (k := k) hr
        (singleCoordinate (oddFirstCofactorIndex r hr) (t : ℂ)) =
      (((∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℂ),
          Real.exp (-(pastCofactorV (by omega) A * t ^ 2) / 4)
          ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
            circularGaussianVector k)) : ℝ) : ℂ) := by
  let hrlow : 1 ≤ r - 1 := by omega
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let G := canonicalPastCofactorSubmatrix (k := k) hr
  let phase : ComplexColumnMatrix (r - 1) k → ℂ := fun X ↦
    Complex.exp (((((t : ℂ) * gramHafnianObservable (r - 1) k X).re : ℝ) : ℂ) *
      Complex.I)
  have hmap := map_canonicalPastCofactorSubmatrix r k hr
  calc
    oddHafnianCofactorCharacteristic (k := k) hr
        (singleCoordinate (oddFirstCofactorIndex r hr) (t : ℂ)) =
      ∫ A, phase (G A) ∂nu := by
        unfold oddHafnianCofactorCharacteristic
        apply integral_congr_ae
        filter_upwards [] with A
        simp only [singleCoordinate, Finset.mul_sum]
        rw [Finset.sum_eq_single (oddFirstCofactorIndex r hr)]
        · rw [oddFirstCofactor_eq_gramHafnian_canonicalSubmatrix]
          rfl
        · intro b _hb hne
          simp [hne]
        · simp
    _ = ∫ X, phase X
          ∂(circularGaussianColumnMatrixMeasure (r - 1) k) := by
        have hpush := integral_map
          (measurable_canonicalPastCofactorSubmatrix hr).aemeasurable
          (show AEStronglyMeasurable phase
              (Measure.map G nu) by
            apply Measurable.aestronglyMeasurable
            unfold phase
            exact Complex.continuous_exp.measurable.comp
              ((Complex.continuous_ofReal.measurable.comp
                (Complex.measurable_re.comp
                  (measurable_const.mul
                    (measurable_gramHafnianObservable (r - 1) k)))).mul
                measurable_const))
        rw [show Measure.map G nu =
            circularGaussianColumnMatrixMeasure (r - 1) k by
          simpa [G, nu] using hmap] at hpush
        exact hpush.symm
    _ = ∫ A : OddCofactorIndex (r - 1) hrlow → (Fin k → ℂ),
          Complex.exp (-(((pastCofactorV hrlow A * t ^ 2 : ℝ) : ℂ) / 4))
          ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
            circularGaussianVector k) := by
        unfold phase
        exact integral_exp_re_mul_gramHafnian_eq_pastCofactorV_mixture
          hrlow t
    _ = (((∫ A : OddCofactorIndex (r - 1) hrlow → (Fin k → ℂ),
          Real.exp (-(pastCofactorV hrlow A * t ^ 2) / 4)
          ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
            circularGaussianVector k)) : ℝ) : ℂ) := by
        calc
          (∫ A : OddCofactorIndex (r - 1) hrlow → (Fin k → ℂ),
              Complex.exp
                (-(((pastCofactorV hrlow A * t ^ 2 : ℝ) : ℂ) / 4))
              ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
                circularGaussianVector k)) =
            ∫ A : OddCofactorIndex (r - 1) hrlow → (Fin k → ℂ),
              ((Real.exp (-(pastCofactorV hrlow A * t ^ 2) / 4) : ℝ) : ℂ)
              ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
                circularGaussianVector k) := by
                  apply integral_congr_ae
                  filter_upwards [] with A
                  rw [show -(((pastCofactorV hrlow A * t ^ 2 : ℝ) : ℂ) / 4) =
                      ((-(pastCofactorV hrlow A * t ^ 2) / 4 : ℝ) : ℂ) by
                    push_cast
                    ring]
                  exact (Complex.ofReal_exp _).symm
          _ = _ := integral_ofReal

end

end LogdetLean.GramHafnian
