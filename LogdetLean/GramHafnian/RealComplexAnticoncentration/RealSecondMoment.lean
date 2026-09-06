import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralCofactor
import LogdetLean.GramHafnian.RankOneGaussianBilinear
/-!
# Exact second moment of the literal real Gaussian Gram hafnian

This file concerns the genuine beta-one model
`realGramHafnianObservable n k` under independent standard real Gaussian
columns.  It is deliberately separate from `actualGramFirstMomentReal`, whose
underlying columns are circular complex Gaussian.
-/

open scoped BigOperators RealInnerProductSpace Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- Embed a literal real column matrix entrywise into the complex column type. -/
def realColumnMatrixToComplex {n k : ℕ} (X : RealColumnMatrix n k) :
    ComplexColumnMatrix n k :=
  fun i a ↦ (X i a : ℂ)

/-- The complex Gram hafnian of entrywise-real columns is the complex cast of
the literal real Gram hafnian. -/
theorem gramHafnian_realColumnMatrixToComplex {n k : ℕ}
    (X : RealColumnMatrix n k) :
    gramHafnian (rowMatrix (realColumnMatrixToComplex X)) =
      (realGramHafnianObservable n k X : ℂ) := by
  classical
  unfold realGramHafnianObservable gramHafnian hafnian matchingMonomial
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro M _hM
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [transposeGram_apply, transposeGram_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  simp [rowMatrix, realColumnMatrixToComplex, realRowMatrix]

/-- A selected-coordinate monomial is integrable under an iid standard real
Gaussian coordinate field. -/
theorem integrable_realColorProduct_standardGaussian
    {m k : ℕ} (c : Fin m → Fin k) :
    Integrable (fun x : Fin k → ℝ ↦ ∏ i, x (c i))
      (standardRealGaussianVectorMeasure k) := by
  rw [show (fun x : Fin k → ℝ ↦ ∏ i, x (c i)) =
      realCoordinatePowerProduct (colorMultiplicity c) by
    funext x
    exact prod_comp_eq_coordinatePowerProduct c x]
  unfold realCoordinatePowerProduct standardRealGaussianVectorMeasure
  exact Integrable.fintype_prod fun a ↦
    integrable_pow_gaussianReal (colorMultiplicity c a)

/-- The real-coordinate specialization of the circular second monomial is
integrable under a standard real Gaussian column. -/
theorem integrable_coordinateSecondMonomial_realGaussianVector
    {k : ℕ} (a b : Fin k) :
    Integrable (fun x : Fin k → ℝ ↦
      coordinateSecondMonomial (fun j ↦ (x j : ℂ)) a b)
      (standardRealGaussianVectorMeasure k) := by
  let c : Fin 2 → Fin k := ![a, b]
  have hreal : Integrable (fun x : Fin k → ℝ ↦ x a * x b)
      (standardRealGaussianVectorMeasure k) := by
    simpa [c] using integrable_realColorProduct_standardGaussian c
  have hcomplex : Integrable (fun x : Fin k → ℝ ↦ ((x a * x b : ℝ) : ℂ))
      (standardRealGaussianVectorMeasure k) := hreal.ofReal
  simpa [coordinateSecondMonomial] using hcomplex

/-- One standard real Gaussian column contracts two deterministic real
linear forms to their bilinear dot product. -/
theorem integral_realBilinearForms_standardGaussian
    {k : ℕ} (g h : Fin k → ℝ) :
    (∫ x : Fin k → ℝ, bilinearDot g x * bilinearDot h x
        ∂standardRealGaussianVectorMeasure k) = bilinearDot g h := by
  let E := EuclideanSpace ℝ (Fin k)
  let T : (Fin k → ℝ) → E := WithLp.toLp 2
  have hmap : Measure.map T (standardRealGaussianVectorMeasure k) =
      stdGaussian E := by
    simpa only [T, E, standardRealGaussianVectorMeasure] using
      (map_pi_eq_stdGaussian (ι := Fin k))
  calc
    (∫ x : Fin k → ℝ, bilinearDot g x * bilinearDot h x
        ∂standardRealGaussianVectorMeasure k) =
        ∫ x : Fin k → ℝ,
          inner ℝ (WithLp.toLp 2 g) (WithLp.toLp 2 x) *
            inner ℝ (WithLp.toLp 2 h) (WithLp.toLp 2 x)
          ∂standardRealGaussianVectorMeasure k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change bilinearDot g x * bilinearDot h x =
          inner ℝ (WithLp.toLp 2 g) (WithLp.toLp 2 x) *
            inner ℝ (WithLp.toLp 2 h) (WithLp.toLp 2 x)
        rw [inner_toLp_eq_bilinearDot, inner_toLp_eq_bilinearDot]
    _ = ∫ z : E,
          inner ℝ (WithLp.toLp 2 g) z * inner ℝ (WithLp.toLp 2 h) z
          ∂Measure.map T (standardRealGaussianVectorMeasure k) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ z : E,
          inner ℝ (WithLp.toLp 2 g) z * inner ℝ (WithLp.toLp 2 h) z
          ∂stdGaussian E := by rw [hmap]
    _ = inner ℝ (WithLp.toLp 2 g) (WithLp.toLp 2 h) := by
      have hcov := covarianceBilin_apply
        (μ := stdGaussian E) IsGaussian.memLp_two_id
        (WithLp.toLp 2 g) (WithLp.toLp 2 h)
      rw [covarianceBilin_stdGaussian] at hcov
      have hmean : (∫ x : E, id x ∂stdGaussian E) = 0 := by
        simpa only [id_eq] using (integral_id_stdGaussian (E := E))
      rw [hmean] at hcov
      simp only [sub_zero] at hcov
      rw [← hcov, innerSL_apply_apply]
    _ = bilinearDot g h := inner_toLp_eq_bilinearDot g h

/-- The literal real-column version of the two-auxiliary-field integrand. -/
def realSecondAuxiliaryIntegrand {n k : ℕ}
    (w : TwoRealFields k) (X : RealColumnMatrix n k) : ℂ :=
  secondAuxiliaryIntegrand w (realColumnMatrixToComplex X)

/-- Integrating the two auxiliary fields gives the square of the literal real
Gram hafnian. -/
theorem integral_realSecondAuxiliaryIntegrand_fields
    {n k : ℕ} (X : RealColumnMatrix n k) :
    (∫ w, realSecondAuxiliaryIntegrand w X
        ∂twoRealGaussianFieldsMeasure k) =
      (((realGramHafnianObservable n k X) ^ 2 : ℝ) : ℂ) := by
  change (∫ w, secondAuxiliaryIntegrand w (realColumnMatrixToComplex X)
      ∂twoRealGaussianFieldsMeasure k) = _
  rw [integral_secondAuxiliaryIntegrand_fields,
    gramHafnian_realColumnMatrixToComplex]
  simp only [Complex.conj_ofReal, pow_two, Complex.ofReal_mul]

/-- Every term in the finite colouring expansion of the real-column
two-field integrand is jointly integrable. -/
theorem integrable_realSecondExpansionTerm
    {n k : ℕ} (A B : Fin (2 * n) → Fin k) :
    Integrable (Function.uncurry (fun (w : TwoRealFields k)
        (X : RealColumnMatrix n k) ↦
          secondExpansionTerm A B w (realColumnMatrixToComplex X)))
      ((twoRealGaussianFieldsMeasure k).prod
        (standardRealGaussianColumnMatrixMeasure n k)) := by
  have hA := integrable_complexRealColorProduct A
  have hB := integrable_complexRealColorProduct B
  have hfields : Integrable (fun w : TwoRealFields k ↦
      complexRealColorProduct A w.1 * complexRealColorProduct B w.2)
      (twoRealGaussianFieldsMeasure k) := hA.mul_prod hB
  have hcolumns : Integrable (fun X : RealColumnMatrix n k ↦
      ∏ i, coordinateSecondMonomial
        (realColumnMatrixToComplex X i) (A i) (B i))
      (standardRealGaussianColumnMatrixMeasure n k) := by
    unfold standardRealGaussianColumnMatrixMeasure
    exact Integrable.fintype_prod fun i ↦
      integrable_coordinateSecondMonomial_realGaussianVector (A i) (B i)
  exact hfields.mul_prod hcolumns

/-- The complete two-field/real-column polynomial is absolutely integrable,
so the auxiliary fields and literal real columns may be interchanged by
Fubini. -/
theorem integrable_uncurry_realSecondAuxiliaryIntegrand
    {n k : ℕ} :
    Integrable (Function.uncurry
      (realSecondAuxiliaryIntegrand (n := n) (k := k)))
      ((twoRealGaussianFieldsMeasure k).prod
        (standardRealGaussianColumnMatrixMeasure n k)) := by
  apply Integrable.congr
    (integrable_finsetSum _ fun B _ ↦
      integrable_finsetSum _ fun A _ ↦
        integrable_realSecondExpansionTerm A B)
  exact Filter.Eventually.of_forall fun z ↦
    (secondAuxiliaryIntegrand_eq_expansion z.1
      (realColumnMatrixToComplex z.2)).symm

/-- One real Gaussian column, expressed in the complex auxiliary-field
notation, contracts to the real bilinear dot product. -/
theorem integral_columnSecondIntegrand_realGaussianVector
    {k : ℕ} (g h : Fin k → ℝ) :
    (∫ x : Fin k → ℝ,
        columnSecondIntegrand (realVectorToComplex g)
          (realVectorToComplex h) (fun a ↦ (x a : ℂ))
        ∂standardRealGaussianVectorMeasure k) =
      ((bilinearDot g h : ℝ) : ℂ) := by
  calc
    (∫ x : Fin k → ℝ,
        columnSecondIntegrand (realVectorToComplex g)
          (realVectorToComplex h) (fun a ↦ (x a : ℂ))
        ∂standardRealGaussianVectorMeasure k) =
        ∫ x : Fin k → ℝ,
          ((bilinearDot g x * bilinearDot h x : ℝ) : ℂ)
          ∂standardRealGaussianVectorMeasure k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        unfold columnSecondIntegrand complexColumnForm conjugateColumnForm
          realVectorToComplex bilinearDot
        simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul,
          ← Complex.ofReal_sum]
        rw [Complex.ofReal_mul]
    _ = ((bilinearDot g h : ℝ) : ℂ) := by
      rw [integral_complex_ofReal,
        integral_realBilinearForms_standardGaussian]

/-- After the real columns are integrated, their independence leaves the
`2n`-th power of the auxiliary bilinear dot product. -/
theorem integral_realSecondAuxiliaryIntegrand_columns
    {n k : ℕ} (w : TwoRealFields k) :
    (∫ X, realSecondAuxiliaryIntegrand w X
        ∂standardRealGaussianColumnMatrixMeasure n k) =
      ((bilinearDot w.1 w.2 ^ (2 * n) : ℝ) : ℂ) := by
  unfold realSecondAuxiliaryIntegrand secondAuxiliaryIntegrand
    standardRealGaussianColumnMatrixMeasure columnSecondProduct
    realColumnMatrixToComplex
  let f : Fin (2 * n) → (Fin k → ℝ) → ℂ := fun _ x ↦
    columnSecondIntegrand (realVectorToComplex w.1)
      (realVectorToComplex w.2) (realVectorToComplex x)
  change (∫ X : RealColumnMatrix n k, ∏ i, f i (X i)
      ∂Measure.pi fun _ : Fin (2 * n) ↦
        standardRealGaussianVectorMeasure k) = _
  rw [integral_fintype_prod_eq_prod]
  simp_rw [show ∀ i, (∫ x, f i x ∂standardRealGaussianVectorMeasure k) =
      ((bilinearDot w.1 w.2 : ℝ) : ℂ) by
    intro i
    exact integral_columnSecondIntegrand_realGaussianVector w.1 w.2]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.ofReal_pow]

/-- **Exact literal beta-one second moment.**  This theorem integrates the
square of `haf(XᵀX)` under genuinely real iid standard Gaussian columns. -/
theorem integral_sq_realGramHafnianObservable_eq_closedFirstMoment
    (n k : ℕ) (hk : 0 < k) :
    (∫ X, (realGramHafnianObservable n k X) ^ 2
        ∂standardRealGaussianColumnMatrixMeasure n k) =
      closedFirstMoment k n := by
  apply Complex.ofReal_injective
  calc
    ((∫ X, (realGramHafnianObservable n k X) ^ 2
        ∂standardRealGaussianColumnMatrixMeasure n k : ℝ) : ℂ) =
        ∫ X, (((realGramHafnianObservable n k X) ^ 2 : ℝ) : ℂ)
          ∂standardRealGaussianColumnMatrixMeasure n k :=
      integral_complex_ofReal.symm
    _ = ∫ X, ∫ w, realSecondAuxiliaryIntegrand w X
          ∂twoRealGaussianFieldsMeasure k
        ∂standardRealGaussianColumnMatrixMeasure n k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun X ↦
        (integral_realSecondAuxiliaryIntegrand_fields X).symm
    _ = ∫ w, ∫ X, realSecondAuxiliaryIntegrand w X
          ∂standardRealGaussianColumnMatrixMeasure n k
        ∂twoRealGaussianFieldsMeasure k := by
      rw [← integral_integral_swap
        (integrable_uncurry_realSecondAuxiliaryIntegrand (n := n) (k := k))]
    _ = ∫ w : TwoRealFields k,
          ((bilinearDot w.1 w.2 ^ (2 * n) : ℝ) : ℂ)
          ∂twoRealGaussianFieldsMeasure k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        integral_realSecondAuxiliaryIntegrand_columns
    _ = ((∫ w : TwoRealFields k,
          bilinearDot w.1 w.2 ^ (2 * n)
          ∂twoRealGaussianFieldsMeasure k : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = (closedFirstMoment k n : ℂ) := by
      rw [integral_bilinearDot_pow_two_mul_twoRealGaussianFieldsMeasure
        k n hk]

/-- Paper-facing product form of the exact literal beta-one RMS identity. -/
theorem integral_sq_realGramHafnianObservable_eq
    (n k : ℕ) (hk : 0 < k) :
    (∫ X, (realGramHafnianObservable n k X) ^ 2
        ∂standardRealGaussianColumnMatrixMeasure n k) =
      (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ) := by
  rw [integral_sq_realGramHafnianObservable_eq_closedFirstMoment n k hk]
  simp only [closedFirstMoment, dimensionProduct,
    oddPairingNat_eq_doubleFactorial]

/-- Root-mean-square scale for the literal real Gaussian Gram hafnian. -/
def realGramHafnianRMS (n k : ℕ) : ℝ :=
  Real.sqrt (closedFirstMoment k n)

theorem realGramHafnianRMS_nonneg (n k : ℕ) :
    0 ≤ realGramHafnianRMS n k := by
  exact Real.sqrt_nonneg _

theorem realGramHafnianRMS_pos (n k : ℕ) (hk : 0 < k) :
    0 < realGramHafnianRMS n k := by
  unfold realGramHafnianRMS
  exact Real.sqrt_pos.2 (closedFirstMoment_pos k n hk)

theorem realGramHafnianRMS_sq (n k : ℕ) (hk : 0 < k) :
    realGramHafnianRMS n k ^ 2 = closedFirstMoment k n := by
  rw [realGramHafnianRMS, sq]
  exact Real.mul_self_sqrt (le_of_lt (closedFirstMoment_pos k n hk))

/-- The literal integral is exactly the square of the literal real RMS. -/
theorem integral_sq_realGramHafnianObservable_eq_RMS_sq
    (n k : ℕ) (hk : 0 < k) :
    (∫ X, (realGramHafnianObservable n k X) ^ 2
        ∂standardRealGaussianColumnMatrixMeasure n k) =
      realGramHafnianRMS n k ^ 2 := by
  rw [integral_sq_realGramHafnianObservable_eq_closedFirstMoment n k hk,
    realGramHafnianRMS_sq n k hk]

end

end LogdetLean.GramHafnian
