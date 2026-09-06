import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorAlmostSurePositivity
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorInverseMomentAssembly
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralGaussianRealification
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RegularizedCofactorWeights
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RegularizedInverseMomentLimit
/-!
# The literal regularized Wishart limit

This module connects the scalar regularization-removal theorem to the exact
past-column random variables used by the hafnian recurrence.  The only input
left abstract in the final theorem is the family of regularized real-integral
identities supplied by Gaussian integration by parts.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- The literal quadratic form selected by the upper-left inverse block of
the coupled Gram kernel.  This is the expression occurring directly in the
preserved-coordinate Wishart score. -/
def pastCoupledInverseQuadratic {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) : ℝ :=
  quadraticFormReal
    (Matrix.toBlocks₁₁
      (coupledGramKernel (pastComplexColumnMatrix hr A))⁻¹)
    (pastHafnianCofactorVector hr A)

/-- Determinants of finite measurable matrix families are measurable. -/
private theorem measurable_matrix_det_comp
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {F : Ω → Matrix ι ι ℂ} (hF : Measurable F) :
    Measurable (fun ω ↦ (F ω).det) := by
  simp_rw [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ ↦
    measurable_const.mul (Finset.measurable_prod _ fun i _ ↦
      (measurable_pi_apply i).comp
        ((measurable_pi_apply (σ i)).comp hF))

/-- Ordinary nonsingular matrix inversion, totalized at singular matrices,
is measurable in every finite complex matrix space. -/
private theorem measurable_matrix_inv_comp
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {F : Ω → Matrix ι ι ℂ} (hF : Measurable F) :
    Measurable (fun ω ↦ (F ω)⁻¹) := by
  have hentry (i j : ι) : Measurable (fun ω ↦ F ω i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)
  have hdet : Measurable (fun ω ↦ (F ω).det) :=
    measurable_matrix_det_comp hF
  have hadj : Measurable (fun ω ↦ (F ω).adjugate) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.adjugate_apply]
    apply measurable_matrix_det_comp
    refine measurable_pi_lambda _ fun a ↦ measurable_pi_lambda _ fun b ↦ ?_
    by_cases ha : a = j
    · simp [ha]
    · simpa [Matrix.updateRow_apply, ha] using hentry a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul]
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  have hadjEntry : Measurable (fun ω ↦ (F ω).adjugate i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hadj)
  exact hdet.fun_inv.mul hadjEntry

@[fun_prop]
theorem measurable_pastComplexColumnMatrix {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastComplexColumnMatrix (k := k) hr) := by
  refine measurable_pi_lambda _ fun a ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact (measurable_pi_apply a).comp (measurable_pi_apply j)

@[fun_prop]
theorem measurable_pastCoupledInverseQuadratic {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastCoupledInverseQuadratic (k := k) hr) := by
  have hB : Measurable (pastComplexColumnMatrix (k := k) hr) :=
    measurable_pastComplexColumnMatrix hr
  have hK : Measurable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        coupledGramKernel (pastComplexColumnMatrix hr A)) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    cases i <;> cases j <;>
      simp [coupledGramKernel, hermitianGram, transposeGramMatrix,
        Matrix.mul_apply, pastComplexColumnMatrix] <;> fun_prop
  have hKinv : Measurable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (coupledGramKernel (pastComplexColumnMatrix hr A))⁻¹) :=
    measurable_matrix_inv_comp hK
  have hc : Measurable
      (pastHafnianCofactorVector (k := k) hr) :=
    measurable_pastHafnianCofactorVector hr
  unfold pastCoupledInverseQuadratic quadraticFormReal dotProduct Matrix.mulVec
  apply Complex.measurable_re.comp
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have hci : Measurable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        pastHafnianCofactorVector hr A i) :=
    (measurable_pi_apply i).comp hc
  apply (Complex.continuous_conj.measurable.comp hci).mul
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  have hblock : Measurable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (coupledGramKernel (pastComplexColumnMatrix hr A))⁻¹
          (Sum.inl i) (Sum.inl j)) :=
    (measurable_pi_apply (Sum.inl j)).comp
      ((measurable_pi_apply (Sum.inl i)).comp hKinv)
  exact hblock.mul ((measurable_pi_apply j).comp hc)

/-- Full coupled column rank makes the literal score quadratic nonnegative. -/
theorem pastCoupledInverseQuadratic_nonneg_of_fullRank
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hfull : Function.Injective
      (complexConjugateColumnPair (pastComplexColumnMatrix hr A)).mulVec) :
    0 ≤ pastCoupledInverseQuadratic hr A := by
  rw [pastCoupledInverseQuadratic,
    coupledKernel_inverse_toBlocks11 _ hfull]
  exact (coupledSchurComplement_posDef _ hfull).inv.posSemidef.re_dotProduct_nonneg _

/-- On the full-rank locus, the literal upper-left inverse block is exactly
the inverse Schur-complement quadratic. -/
theorem pastCoupledInverseQuadratic_eq_coupledSchur_of_fullRank
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hfull : Function.Injective
      (complexConjugateColumnPair (pastComplexColumnMatrix hr A)).mulVec) :
    pastCoupledInverseQuadratic hr A =
      quadraticFormReal
        (coupledSchurComplement (pastComplexColumnMatrix hr A))⁻¹
        (pastHafnianCofactorVector hr A) := by
  unfold pastCoupledInverseQuadratic
  rw [coupledKernel_inverse_toBlocks11 _ hfull]

/-- The exact deterministic matrix Cauchy--Schwarz comparison in literal
past-column coordinates. -/
theorem pastCofactorW_sq_le_pastCofactorV_mul_pastCoupledInverseQuadratic
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hfull : Function.Injective
      (complexConjugateColumnPair (pastComplexColumnMatrix hr A)).mulVec) :
    pastCofactorW hr A ^ 2 ≤
      pastCofactorV hr A * pastCoupledInverseQuadratic hr A := by
  let B := pastComplexColumnMatrix hr A
  let c := pastHafnianCofactorVector hr A
  have hK : (coupledGramKernel B).PosDef :=
    coupledGramKernel_posDef B hfull
  have hQ : (hermitianGram B).PosDef := by
    convert hK.submatrix (e := Sum.inl) Sum.inl_injective using 1 <;>
      ext i j <;> rfl
  have hmono : quadraticFormReal (hermitianGram B)⁻¹ c ≤
      quadraticFormReal (coupledSchurComplement B)⁻¹ c :=
    quadraticFormReal_mono
      (hermitianGram_inverse_le_coupledSchur_inverse B hfull) c
  calc
    pastCofactorW hr A ^ 2 = vectorNormSq c ^ 2 := by
      rw [vectorNormSq_pastHafnianCofactorVector hr A]
    _ ≤ quadraticFormReal (hermitianGram B) c *
          quadraticFormReal (hermitianGram B)⁻¹ c :=
      matrix_cauchy_schwarz hQ c
    _ ≤ quadraticFormReal (hermitianGram B) c *
          quadraticFormReal (coupledSchurComplement B)⁻¹ c := by
      exact mul_le_mul_of_nonneg_left hmono
        (hQ.posSemidef.re_dotProduct_nonneg c)
    _ = pastCofactorV hr A * pastCoupledInverseQuadratic hr A := by
      rw [quadraticFormReal_hermitianGram_past_eq_pastCofactorV hr A]
      rw [pastCoupledInverseQuadratic,
        coupledKernel_inverse_toBlocks11 B hfull]

/-! ## Almost-sure coupled full rank -/

/-- Canonical reindexing of two copies of an arbitrary finite column type by
the numeric type used by the matrix half-Gaussian full-rank theorem. -/
def literalSplitColumnEquiv (I : Type*) [Fintype I] :
    I ⊕ I ≃ Fin (2 * Fintype.card I) :=
  ((Fintype.equivFin I).sumCongr (Fintype.equivFin I)).trans
    (finSumFinEquiv.trans
      (finCongr (Nat.two_mul (Fintype.card I))).symm)

@[simp]
theorem literalColumnsToHalfGaussianMatrix_apply_splitColumn
    (I : Type*) [Fintype I] (n : ℕ)
    (A : I → (Fin n → ℂ)) (a : Fin n) (j : I ⊕ I) :
    literalColumnsToHalfGaussianMatrixMeasurableEquiv I n A a
        (literalSplitColumnEquiv I j) =
      complexColumnsRealification n A a j := by
  let e₁ : I ⊕ I ≃
      Fin (Fintype.card I) ⊕ Fin (Fintype.card I) :=
    (Fintype.equivFin I).sumCongr (Fintype.equivFin I)
  let e₂ : Fin (Fintype.card I) ⊕ Fin (Fintype.card I) ≃
      Fin (2 * Fintype.card I) :=
    finSumFinEquiv.trans
      (finCongr (Nat.two_mul (Fintype.card I))).symm
  change complexColumnsRealification n A a
      (e₁.symm (e₂.symm ((e₁.trans e₂) j))) = _
  simp

/-- Injectivity of a real matrix survives entrywise complexification. -/
theorem map_complexOfReal_mulVec_injective_of_real
    {k m : Type*} [Fintype k] [Fintype m]
    (R : Matrix k m ℝ) (hR : Function.Injective R.mulVec) :
    Function.Injective (R.map Complex.ofReal).mulVec := by
  intro x y hxy
  have hre : R.mulVec (fun j ↦ (x j).re) =
      R.mulVec (fun j ↦ (y j).re) := by
    funext a
    have ha := congrArg Complex.re (congrFun hxy a)
    simpa [Matrix.mulVec, dotProduct] using ha
  have him : R.mulVec (fun j ↦ (x j).im) =
      R.mulVec (fun j ↦ (y j).im) := by
    funext a
    have ha := congrArg Complex.im (congrFun hxy a)
    simpa [Matrix.mulVec, dotProduct] using ha
  have hre' := hR hre
  have him' := hR him
  funext j
  apply Complex.ext
  · exact congrFun hre' j
  · exact congrFun him' j

/-- Full real rank of `[X,Y]` implies full complex rank of `[A,conj A]`. -/
theorem complexConjugateColumnPair_mulVec_injective_of_realColumnPair
    {k m : Type*} [Fintype k] [Fintype m] [DecidableEq m]
    (X Y : Matrix k m ℝ)
    (hXY : Function.Injective (realColumnPair X Y).mulVec) :
    Function.Injective
      (complexConjugateColumnPair (complexOfRealPair X Y)).mulVec := by
  rw [← realColumnPair_mul_complexPairTransform]
  have hleft : Function.Injective
      ((realColumnPair X Y).map Complex.ofReal).mulVec :=
    map_complexOfReal_mulVec_injective_of_real _ hXY
  have hright : Function.Injective
      (complexPairTransform : Matrix (m ⊕ m) (m ⊕ m) ℂ).mulVec :=
    Matrix.mulVec_injective_of_isUnit complexPairTransform_isUnit
  intro x y hxy
  apply hright
  apply hleft
  simpa only [Matrix.mulVec_mulVec] using hxy

/-- Under the literal iid circular law, `[A,conj A]` has full column rank
almost surely throughout the paper range. -/
theorem ae_injective_complexConjugateColumnPair_pastColumns
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        circularGaussianVector k),
      Function.Injective
        (complexConjugateColumnPair
          (pastComplexColumnMatrix hr A)).mulVec := by
  let I := OddCofactorIndex r hr
  let e := literalSplitColumnEquiv I
  have hcard : 2 * Fintype.card I ≤ k := by
    dsimp only [I]
    rw [card_oddCofactorIndex]
    omega
  have htarget :
      ∀ᵐ R ∂halfGaussianMatrix k (2 * Fintype.card I),
        LinearIndependent ℝ
          (fun j ↦ WithLp.toLp 2 (fun a ↦ R a j) :
            Fin (2 * Fintype.card I) →
              EuclideanSpace ℝ (Fin k)) :=
    ae_linearIndependent_halfGaussianMatrix_columns
      k (2 * Fintype.card I) hcard
  have hmp :=
    measurePreserving_literalPastColumnsToHalfGaussianMatrix (n := k) hr
  have hsource := hmp.quasiMeasurePreserving.ae htarget
  filter_upwards [hsource] with A hnum
  have hsplitLp : LinearIndependent ℝ
      (fun j : I ⊕ I ↦
        WithLp.toLp 2
          (fun a ↦ pastRealifiedMatrix hr A a j) :
        I ⊕ I → EuclideanSpace ℝ (Fin k)) := by
    have hcomp := hnum.comp e e.injective
    have hfun :
        ((fun j ↦ WithLp.toLp 2
            (fun a ↦
              literalColumnsToHalfGaussianMatrixTwoMulMeasurableEquiv
                I k A a j)) ∘ e) =
          (fun j : I ⊕ I ↦ WithLp.toLp 2
            (fun a ↦ pastRealifiedMatrix hr A a j)) := by
      funext j
      rw [WithLp.ext_iff]
      change (fun a ↦
          literalColumnsToHalfGaussianMatrixTwoMulMeasurableEquiv
            I k A a (e j)) =
        (fun a ↦ pastRealifiedMatrix hr A a j)
      funext a
      dsimp only [e, I]
      rw [literalColumnsToHalfGaussianMatrix_apply_splitColumn]
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have hsplitRaw : LinearIndependent ℝ
      (pastRealifiedMatrix hr A).col := by
    have hmap := hsplitLp.map'
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap
      (LinearMap.ker_eq_bot_of_injective
        (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).injective)
    change LinearIndependent ℝ
      (fun j : I ⊕ I ↦ fun a ↦ pastRealifiedMatrix hr A a j)
    simpa [Function.comp_def] using hmap
  have hsplit : Function.Injective (pastRealifiedMatrix hr A).mulVec :=
    Matrix.mulVec_injective_iff.mpr hsplitRaw
  let X : Matrix (Fin k) I ℝ := fun a j ↦ (A j a).re
  let Y : Matrix (Fin k) I ℝ := fun a j ↦ (A j a).im
  have hreal : realColumnPair X Y = pastRealifiedMatrix hr A := by
    rfl
  have hcomplex : complexOfRealPair X Y = pastComplexColumnMatrix hr A := by
    ext a j
    apply Complex.ext <;>
      simp [X, Y, complexOfRealPair, pastComplexColumnMatrix]
  rw [← hcomplex]
  apply complexConjugateColumnPair_mulVec_injective_of_realColumnPair X Y
  rwa [hreal]

/-! ## Literal almost-sure inequalities and the final wrapper -/

/-- Positivity of the literal variance forces the cofactor vector itself to
be nonzero. -/
theorem pastHafnianCofactorVector_ne_zero_of_pastCofactorV_pos
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hV : 0 < pastCofactorV hr A) :
    pastHafnianCofactorVector hr A ≠ 0 := by
  intro hzero
  have hVzero : pastCofactorV hr A = 0 := by
    rw [← quadraticFormReal_hermitianGram_past_eq_pastCofactorV hr A,
      hzero]
    simp [quadraticFormReal, dotProduct, Matrix.mulVec]
  linarith

/-- In the paper range the literal past variance is strictly positive almost
surely. -/
theorem ae_pastCofactorV_pos_paperRange
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        circularGaussianVector k),
      0 < pastCofactorV hr A := by
  have hk' : 2 * r - 1 ≤ k := by omega
  exact ae_pastCofactorV_pos_of_ae_oddCofactorV_pos hr
    (ae_oddCofactorV_pos_circularGaussianColumnMatrix hr hk')

/-- The literal cofactor norm is strictly positive almost surely in the same
range. -/
theorem ae_pastCofactorW_pos_paperRange
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        circularGaussianVector k),
      0 < pastCofactorW hr A := by
  filter_upwards [ae_pastCofactorV_pos_paperRange hr hk] with A hV
  rw [← vectorNormSq_pastHafnianCofactorVector hr A]
  exact vectorNormSq_pos
    (pastHafnianCofactorVector_ne_zero_of_pastCofactorV_pos hr A hV)

/-- The literal coupled inverse quadratic is nonnegative almost surely. -/
theorem ae_pastCoupledInverseQuadratic_nonneg
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        circularGaussianVector k),
      0 ≤ pastCoupledInverseQuadratic hr A := by
  filter_upwards [ae_injective_complexConjugateColumnPair_pastColumns hr hk]
    with A hfull
  exact pastCoupledInverseQuadratic_nonneg_of_fullRank hr A hfull

/-- Matrix Cauchy--Schwarz in the exact almost-sure form consumed by the
regularization-removal theorem. -/
theorem ae_pastCofactorW_sq_le_pastCofactorV_mul_coupledInverseQuadratic
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        circularGaussianVector k),
      pastCofactorW hr A ^ 2 ≤
        pastCofactorV hr A * pastCoupledInverseQuadratic hr A := by
  filter_upwards [ae_injective_complexConjugateColumnPair_pastColumns hr hk]
    with A hfull
  exact
    pastCofactorW_sq_le_pastCofactorV_mul_pastCoupledInverseQuadratic
      hr A hfull

/-- **Literal regularized H2 interface.**  Once the real regularized score
identity has been transported to the iid circular past-column law, no further
matrix or measure-theoretic work remains: this theorem removes the
regularization and produces the exact ENNReal inverse-moment comparison. -/
theorem ennInverseMoment_pastCofactorV_le_of_regularized_coupled_identity
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k)
    (hregularized : ∀ δ : ℝ, 0 < δ →
      Integrable
          (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
            pastCoupledInverseQuadratic hr A /
              (pastCofactorW hr A + δ) ^ 2)
          (Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k) ∧
      Integrable
          (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
            pastCofactorW hr A / (pastCofactorW hr A + δ) ^ 2)
          (Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k) ∧
      (∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
          pastCoupledInverseQuadratic hr A /
            (pastCofactorW hr A + δ) ^ 2
          ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k)) =
        (((k : ℝ) - 4 * r + 1)⁻¹) *
          ∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
            pastCofactorW hr A / (pastCofactorW hr A + δ) ^ 2
            ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
              circularGaussianVector k)) :
    ennInverseMoment
        (Measure.pi fun _ : OddCofactorIndex r hr ↦
          circularGaussianVector k)
        (pastCofactorV hr) ≤
      ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹) *
        ennInverseMoment
          (Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k)
          (pastCofactorW hr) := by
  let μ : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hcden : 0 < (k : ℝ) - 4 * r + 1 := by
    have hkR : (4 : ℝ) * r ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  apply ennInverseMoment_le_of_regularized_integral_identity
    μ (pastCofactorV hr) (pastCofactorW hr)
      (pastCoupledInverseQuadratic hr)
  · exact measurable_pastCofactorV hr
  · exact measurable_pastCofactorW hr
  · exact measurable_pastCoupledInverseQuadratic hr
  · exact ae_pastCofactorV_pos_paperRange hr hk
  · exact ae_pastCofactorW_pos_paperRange hr hk
  · exact ae_pastCoupledInverseQuadratic_nonneg hr hk
  · exact
      ae_pastCofactorW_sq_le_pastCofactorV_mul_coupledInverseQuadratic hr hk
  · exact inv_nonneg.mpr (le_of_lt hcden)
  · simpa [μ] using hregularized

/-- Totalized public form of the literal Wishart step, with the factor placed
on the right exactly as expected by the inverse-moment recurrence assembly. -/
theorem pastCofactorVInverseMoment_le_of_regularized_coupled_identity
    (k r : ℕ) (hr : 1 ≤ r) (hk : 4 * r ≤ k)
    (hregularized : ∀ δ : ℝ, 0 < δ →
      Integrable
          (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
            pastCoupledInverseQuadratic hr A /
              (pastCofactorW hr A + δ) ^ 2)
          (Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k) ∧
      Integrable
          (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
            pastCofactorW hr A / (pastCofactorW hr A + δ) ^ 2)
          (Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k) ∧
      (∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
          pastCoupledInverseQuadratic hr A /
            (pastCofactorW hr A + δ) ^ 2
          ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k)) =
        (((k : ℝ) - 4 * r + 1)⁻¹) *
          ∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
            pastCofactorW hr A / (pastCofactorW hr A + δ) ^ 2
            ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
              circularGaussianVector k)) :
    pastCofactorVInverseMoment k r ≤
      pastCofactorWInverseMoment k r *
        ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹) := by
  rw [pastCofactorVInverseMoment_eq hr,
    pastCofactorWInverseMoment_eq hr]
  simpa [mul_comm] using
    (ennInverseMoment_pastCofactorV_le_of_regularized_coupled_identity
      hr hk hregularized)

end Wishart

end

end LogdetLean.GramHafnian
