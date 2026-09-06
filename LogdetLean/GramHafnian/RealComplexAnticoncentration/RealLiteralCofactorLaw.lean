import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLastColumnProduct
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealCoordinateCompression
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.LiteralCofactorLaw
/-!
# The literal real cofactor law and its singleton Fourier coordinate

This file realizes the real odd cofactor vector in Euclidean coordinates,
identifies its pushforward characteristic function, and proves the exact
singleton formula with the lower-level energy `V_{r-1}`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 1600000

/-- The canonically enumerated real cofactor vector. -/
def pastRealCofactorEuclidean
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    RealGaussianEuclideanSpace (2 * r - 1) :=
  WithLp.toLp 2 (fun i ↦
    pastRealHafnianCofactorVector hr A (finOddCofactorEquiv r hr i))

@[fun_prop] theorem measurable_pastRealCofactorEuclidean
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastRealCofactorEuclidean (k := k) hr) := by
  unfold pastRealCofactorEuclidean
  apply (WithLp.measurable_toLp 2 (Fin (2 * r - 1) → ℝ)).comp
  rw [measurable_pi_iff]
  intro i
  exact (measurable_pi_apply (finOddCofactorEquiv r hr i)).comp
    ((measurable_realOddHafnianCofactorVector hr).comp
      ((realLastColumnProductEquiv r k hr).measurable.comp
        (measurable_id.prodMk measurable_const)))

def pastRealCofactorEuclideanLaw
    (r k : ℕ) (hr : 1 ≤ r) :
    Measure (RealGaussianEuclideanSpace (2 * r - 1)) :=
  Measure.map (pastRealCofactorEuclidean (k := k) hr)
    (Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k)

instance pastRealCofactorEuclideanLaw_isProbabilityMeasure
    (r k : ℕ) (hr : 1 ≤ r) :
    IsProbabilityMeasure (pastRealCofactorEuclideanLaw r k hr) := by
  unfold pastRealCofactorEuclideanLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_pastRealCofactorEuclidean hr).aemeasurable

theorem pastRealCofactorW_eq_sum_sq
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    pastRealCofactorW hr A =
      ∑ j : OddCofactorIndex r hr,
        (pastRealHafnianCofactorVector hr A j) ^ 2 := by
  rfl

theorem norm_sq_pastRealCofactorEuclidean
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    ‖pastRealCofactorEuclidean hr A‖ ^ 2 = pastRealCofactorW hr A := by
  rw [EuclideanSpace.norm_sq_eq, pastRealCofactorW_eq_sum_sq]
  unfold pastRealCofactorEuclidean
  simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  exact Fintype.sum_equiv (finOddCofactorEquiv r hr)
    (fun i ↦ (pastRealHafnianCofactorVector hr A
      (finOddCofactorEquiv r hr i)) ^ 2)
    (fun j ↦ (pastRealHafnianCofactorVector hr A j) ^ 2)
    (fun _ ↦ rfl)

/-- Raw real Fourier characteristic functional on canonical `Fin`
coordinates. -/
def realOddCofactorRawCharacteristic
    {r k : ℕ} (hr : 1 ≤ r) :
    (Fin (2 * r - 1) → ℝ) → ℂ :=
  fun w ↦ ∫ A : OddCofactorIndex r hr → (Fin k → ℝ),
    Complex.exp
      (((∑ i : Fin (2 * r - 1),
        w i * pastRealHafnianCofactorVector hr A
          (finOddCofactorEquiv r hr i) : ℝ) : ℂ) * Complex.I)
      ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        standardRealGaussianVectorMeasure k)

theorem realOddCofactorRawCharacteristic_eq_charFun
    {r k : ℕ} (hr : 1 ≤ r)
    (xi : RealGaussianEuclideanSpace (2 * r - 1)) :
    realOddCofactorRawCharacteristic (k := k) hr (fun i ↦ xi i) =
      charFun (pastRealCofactorEuclideanLaw r k hr) xi := by
  unfold realOddCofactorRawCharacteristic pastRealCofactorEuclideanLaw charFun
  rw [integral_map
    (measurable_pastRealCofactorEuclidean hr).aemeasurable
    (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with A
  congr 2

def realFinOddFirstCofactorIndex (r : ℕ) (hr : 1 ≤ r) :
    Fin (2 * r - 1) :=
  (finOddCofactorEquiv r hr).symm (oddFirstCofactorIndex r hr)

def realCanonicalCofactorSubmatrix
    {r k : ℕ} (hr : 1 ≤ r) (X : RealColumnMatrix r k) :
    RealColumnMatrix (r - 1) k :=
  fun i p ↦ X ⟨i.1 + 1, by
    have hi := i.2
    omega⟩ p

@[fun_prop] theorem measurable_realCanonicalCofactorSubmatrix
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (realCanonicalCofactorSubmatrix (k := k) hr) := by
  unfold realCanonicalCofactorSubmatrix
  fun_prop

theorem realOddFirstCofactor_eq_realGramHafnian_canonicalSubmatrix
    {r k : ℕ} (hr : 1 ≤ r) (X : RealColumnMatrix r k) :
    realOddHafnianCofactorVector hr X (oddFirstCofactorIndex r hr) =
      realGramHafnianObservable (r - 1) k
        (realCanonicalCofactorSubmatrix hr X) := by
  unfold realGramHafnianObservable gramHafnian
  rw [← typeHafnian_fin_eq_hafnian]
  unfold realOddHafnianCofactorVector hafnianPairCofactor
  let e := canonicalCofactorSubmatrixOrderIso r hr
  rw [← typeHafnian_reindex_orderIso e
    (fun i j : TypePerfectMatching.PairComplement
      (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 ↦
      transposeGram (realRowMatrix X) i.1 j.1)]
  rfl

theorem map_realCanonicalCofactorSubmatrix_standardRealGaussian
    (r k : ℕ) (hr : 1 ≤ r) :
    Measure.map (realCanonicalCofactorSubmatrix (k := k) hr)
        (standardRealGaussianColumnMatrixMeasure r k) =
      standardRealGaussianColumnMatrixMeasure (r - 1) k := by
  let p : Fin (2 * r) → Prop := fun i ↦
    i ≠ evenLastIndex r hr ∧ i ≠ (oddFirstCofactorIndex r hr).1
  let Col := Fin k → ℝ
  let mu : Measure Col := standardRealGaussianVectorMeasure k
  let split := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (2 * r) ↦ Col) p
  have hsplit : MeasurePreserving split
      (Measure.pi fun _ : Fin (2 * r) ↦ mu)
      ((Measure.pi fun _ : Subtype p ↦ mu).prod
        (Measure.pi fun _ : {i : Fin (2 * r) // ¬p i} ↦ mu)) :=
    measurePreserving_piEquivPiSubtypeProd
      (fun _ : Fin (2 * r) ↦ mu) p
  have hfst : MeasurePreserving Prod.fst
      ((Measure.pi fun _ : Subtype p ↦ mu).prod
        (Measure.pi fun _ : {i : Fin (2 * r) // ¬p i} ↦ mu))
      (Measure.pi fun _ : Subtype p ↦ mu) := measurePreserving_fst
  let e := canonicalCofactorSubmatrixOrderIso r hr
  let reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : TypePerfectMatching.PairComplement
        (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 ↦ Col)
      e.toEquiv).symm
  have hreindex : MeasurePreserving reindex
      (Measure.pi fun _ : Subtype p ↦ mu)
      (Measure.pi fun _ : Fin (2 * (r - 1)) ↦ mu) := by
    have h := (measurePreserving_piCongrLeft
      (α := fun _ : TypePerfectMatching.PairComplement
        (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 ↦ Col)
      (fun _ : TypePerfectMatching.PairComplement
        (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 ↦ mu) e.toEquiv)
    simpa [p, reindex] using h.symm
  have htotal := hreindex.comp (hfst.comp hsplit)
  change Measure.map (realCanonicalCofactorSubmatrix (k := k) hr)
      (Measure.pi fun _ : Fin (2 * r) ↦ mu) =
    Measure.pi fun _ : Fin (2 * (r - 1)) ↦ mu
  rw [← htotal.map_eq]
  congr 1

def realCanonicalPastCofactorSubmatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℝ)) :
    RealColumnMatrix (r - 1) k :=
  realCanonicalCofactorSubmatrix hr (pastRealCofactorMatrix hr A)

@[fun_prop] theorem measurable_realCanonicalPastCofactorSubmatrix
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (realCanonicalPastCofactorSubmatrix (k := k) hr) := by
  unfold realCanonicalPastCofactorSubmatrix realCanonicalCofactorSubmatrix
    pastRealCofactorMatrix
  fun_prop

theorem map_realCanonicalPastCofactorSubmatrix
    (r k : ℕ) (hr : 1 ≤ r) :
    Measure.map (realCanonicalPastCofactorSubmatrix (k := k) hr)
        (Measure.pi fun _ : OddCofactorIndex r hr ↦
          standardRealGaussianVectorMeasure k) =
      standardRealGaussianColumnMatrixMeasure (r - 1) k := by
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let mu : Measure (Fin k → ℝ) := standardRealGaussianVectorMeasure k
  let e := realLastColumnProductEquiv r k hr
  let F := realCanonicalCofactorSubmatrix (k := k) hr
  let G := realCanonicalPastCofactorSubmatrix (k := k) hr
  have hfst : MeasurePreserving Prod.fst (nu.prod mu) nu :=
    measurePreserving_fst
  have he := measurePreserving_realLastColumnProductEquiv r k hr
  have hcomp : G ∘ Prod.fst = F ∘ e := by
    funext q
    unfold G F realCanonicalPastCofactorSubmatrix
      realCanonicalCofactorSubmatrix
    ext i a
    change pastRealCofactorMatrix hr q.1 ⟨i.1 + 1, _⟩ a =
      e q ⟨i.1 + 1, _⟩ a
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
    unfold pastRealCofactorMatrix
    rw [realLastColumnProductEquiv_apply_nonlast hr (q.1, 0) j,
      realLastColumnProductEquiv_apply_nonlast hr q j]
  calc
    Measure.map G nu = Measure.map G (Measure.map Prod.fst (nu.prod mu)) := by
      rw [hfst.map_eq]
    _ = Measure.map (G ∘ Prod.fst) (nu.prod mu) := by
      rw [Measure.map_map]
      · exact measurable_realCanonicalPastCofactorSubmatrix hr
      · exact measurable_fst
    _ = Measure.map (F ∘ e) (nu.prod mu) := by rw [hcomp]
    _ = Measure.map F (Measure.map e (nu.prod mu)) := by
      rw [Measure.map_map]
      · exact measurable_realCanonicalCofactorSubmatrix hr
      · exact e.measurable
    _ = Measure.map F (standardRealGaussianColumnMatrixMeasure r k) := by
      rw [he.map_eq]
    _ = standardRealGaussianColumnMatrixMeasure (r - 1) k :=
      map_realCanonicalCofactorSubmatrix_standardRealGaussian r k hr

/-- Exact characteristic integral of an iid real Gaussian transpose-linear
form. -/
theorem integral_exp_mul_iidRealTransposeLinearForm
    {k : ℕ} (y : Fin k → ℝ) (t : ℝ) :
    (∫ x : Fin k → ℝ,
        Complex.exp ((((t * iidRealTransposeLinearForm y x : ℝ) : ℂ)) *
          Complex.I)
        ∂(standardRealGaussianVectorMeasure k)) =
      Complex.exp (-(((realCoefficientEnergy y * t ^ 2 : ℝ) : ℂ) / 2)) := by
  let e : (Fin k → ℝ) → RealGaussianEuclideanSpace k := WithLp.toLp 2
  have he : Measure.map e (standardRealGaussianVectorMeasure k) =
      stdGaussian (RealGaussianEuclideanSpace k) := by
    exact map_pi_eq_stdGaussian
  calc
    (∫ x : Fin k → ℝ,
        Complex.exp ((((t * iidRealTransposeLinearForm y x : ℝ) : ℂ)) *
          Complex.I)
        ∂(standardRealGaussianVectorMeasure k)) =
      ∫ x : RealGaussianEuclideanSpace k,
        Complex.exp
          (↑(inner ℝ (realTransposeLinearForm y x) t) * Complex.I)
        ∂(stdGaussian (RealGaussianEuclideanSpace k)) := by
          rw [← he, integral_map (by fun_prop) (by fun_prop)]
          apply integral_congr_ae
          filter_upwards [] with x
          congr 2
    _ = charFun ((stdGaussian (RealGaussianEuclideanSpace k)).map
          (realTransposeLinearForm y)) t := by
          rw [charFun_apply, integral_map
            (measurable_realTransposeLinearForm y).aemeasurable (by fun_prop)]
    _ = Complex.exp
          (-(((realCoefficientEnergy y * t ^ 2 : ℝ) : ℂ) / 2)) :=
      by
        simpa only [neg_div] using
          charFun_map_realTransposeLinearForm_stdGaussian y t

/-- Exposing the lower-level last column gives its real Gaussian mixture
characteristic function. -/
theorem integral_exp_mul_realGramHafnian_eq_pastRealCofactorV_mixture
    {r k : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    (∫ X : RealColumnMatrix r k,
        Complex.exp ((((t * realGramHafnianObservable r k X : ℝ) : ℂ)) *
          Complex.I)
        ∂(standardRealGaussianColumnMatrixMeasure r k)) =
      ∫ A : OddCofactorIndex r hr → (Fin k → ℝ),
        Complex.exp (-(((pastRealCofactorV hr A * t ^ 2 : ℝ) : ℂ) / 2))
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
          standardRealGaussianVectorMeasure k) := by
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let mu : Measure (Fin k → ℝ) := standardRealGaussianVectorMeasure k
  let e := realLastColumnProductEquiv r k hr
  let f : ((OddCofactorIndex r hr → (Fin k → ℝ)) × (Fin k → ℝ)) → ℂ :=
    fun p ↦ Complex.exp ((((t *
      realGramHafnianObservable r k (e p) : ℝ) : ℂ)) * Complex.I)
  have hf : Integrable f (nu.prod mu) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with p
    rw [Complex.norm_exp]
    simp [f]
  have he := measurePreserving_realLastColumnProductEquiv r k hr
  calc
    (∫ X : RealColumnMatrix r k,
        Complex.exp ((((t * realGramHafnianObservable r k X : ℝ) : ℂ)) *
          Complex.I)
        ∂(standardRealGaussianColumnMatrixMeasure r k)) =
      ∫ p, f p ∂(nu.prod mu) := by
        symm
        simpa [f, e, nu, mu] using he.integral_comp'
          (fun X : RealColumnMatrix r k ↦
            Complex.exp ((((t * realGramHafnianObservable r k X : ℝ) : ℂ)) *
              Complex.I))
    _ = ∫ A, ∫ x, f (A, x) ∂mu ∂nu := integral_prod _ hf
    _ = ∫ A : OddCofactorIndex r hr → (Fin k → ℝ),
          Complex.exp (-(((pastRealCofactorV hr A * t ^ 2 : ℝ) : ℂ) / 2))
          ∂nu := by
        apply integral_congr_ae
        filter_upwards [] with A
        simp_rw [f, e,
          realGramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm hr]
        change (∫ x : Fin k → ℝ,
            Complex.exp ((((t * iidRealTransposeLinearForm
              (pastRealCofactorCombination hr A) x : ℝ) : ℂ)) * Complex.I)
              ∂mu) = _
        simpa [mu, standardRealGaussianVectorMeasure,
          pastRealCofactorV_eq_realCoefficientEnergy] using
          integral_exp_mul_iidRealTransposeLinearForm
            (pastRealCofactorCombination hr A) t
    _ = _ := rfl

/-- Exact singleton formula for the literal real cofactor characteristic
function. -/
theorem realOddCofactorRawCharacteristic_singleton_first
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r) (t : ℝ) :
    realOddCofactorRawCharacteristic (k := k) hr
        (realSingleCoordinate (realFinOddFirstCofactorIndex r hr) t) =
      (((∫ A : OddCofactorIndex (r - 1) (by omega) → (Fin k → ℝ),
          Real.exp (-(pastRealCofactorV (by omega) A * t ^ 2) / 2)
          ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) (by omega) ↦
            standardRealGaussianVectorMeasure k)) : ℝ) : ℂ) := by
  let hrlow : 1 ≤ r - 1 := by omega
  let nu : Measure (OddCofactorIndex r hr → (Fin k → ℝ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦
      standardRealGaussianVectorMeasure k
  let G := realCanonicalPastCofactorSubmatrix (k := k) hr
  let phase : RealColumnMatrix (r - 1) k → ℂ := fun X ↦
    Complex.exp ((((t * realGramHafnianObservable (r - 1) k X : ℝ) : ℂ)) *
      Complex.I)
  have hmap := map_realCanonicalPastCofactorSubmatrix r k hr
  calc
    realOddCofactorRawCharacteristic (k := k) hr
        (realSingleCoordinate (realFinOddFirstCofactorIndex r hr) t) =
      ∫ A, phase (G A) ∂nu := by
        unfold realOddCofactorRawCharacteristic
        apply integral_congr_ae
        filter_upwards [] with A
        simp only [realSingleCoordinate, Finset.mul_sum]
        rw [Finset.sum_eq_single (realFinOddFirstCofactorIndex r hr)]
        · rw [show finOddCofactorEquiv r hr
              (realFinOddFirstCofactorIndex r hr) =
              oddFirstCofactorIndex r hr by
            simp [realFinOddFirstCofactorIndex]]
          unfold pastRealHafnianCofactorVector
          rw [realOddFirstCofactor_eq_realGramHafnian_canonicalSubmatrix]
          simp only [if_pos rfl]
          unfold phase G realCanonicalPastCofactorSubmatrix
          rfl
        · intro b _hb hne
          simp [hne]
        · simp
    _ = ∫ X, phase X
          ∂(standardRealGaussianColumnMatrixMeasure (r - 1) k) := by
        have hpush := integral_map
          (measurable_realCanonicalPastCofactorSubmatrix hr).aemeasurable
          (show AEStronglyMeasurable phase (Measure.map G nu) by
            fun_prop)
        rw [show Measure.map G nu =
            standardRealGaussianColumnMatrixMeasure (r - 1) k by
          simpa [G, nu] using hmap] at hpush
        exact hpush.symm
    _ = ∫ A : OddCofactorIndex (r - 1) hrlow → (Fin k → ℝ),
          Complex.exp (-(((pastRealCofactorV hrlow A * t ^ 2 : ℝ) : ℂ) / 2))
          ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
            standardRealGaussianVectorMeasure k) := by
        unfold phase
        exact integral_exp_mul_realGramHafnian_eq_pastRealCofactorV_mixture
          hrlow t
    _ = (((∫ A : OddCofactorIndex (r - 1) hrlow → (Fin k → ℝ),
          Real.exp (-(pastRealCofactorV hrlow A * t ^ 2) / 2)
          ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
            standardRealGaussianVectorMeasure k)) : ℝ) : ℂ) := by
        calc
          _ = ∫ A : OddCofactorIndex (r - 1) hrlow → (Fin k → ℝ),
              ((Real.exp (-(pastRealCofactorV hrlow A * t ^ 2) / 2) : ℝ) : ℂ)
              ∂(Measure.pi fun _ : OddCofactorIndex (r - 1) hrlow ↦
                standardRealGaussianVectorMeasure k) := by
            apply integral_congr_ae
            filter_upwards [] with A
            rw [show -(((pastRealCofactorV hrlow A * t ^ 2 : ℝ) : ℂ) / 2) =
                ((-(pastRealCofactorV hrlow A * t ^ 2) / 2 : ℝ) : ℂ) by
              push_cast
              ring]
            exact (Complex.ofReal_exp _).symm
          _ = _ := integral_ofReal

end

end LogdetLean.GramHafnian
