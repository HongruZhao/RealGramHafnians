import LogdetLean.GramHafnian.ShiftedAnticoncentration.PastCofactorRandomVariables
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.ScoreTransformPairing
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.SchurCauchy
/-!
# Literal past-cofactor variables as Wishart quadratic forms

This module connects the paper's literal `W_r` and `V_r` random variables
to the matrix quadratic forms used by the conditional-Wishart argument.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Matrix whose columns are the literal iid past columns. -/
def pastComplexColumnMatrix {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    Matrix (Fin k) (OddCofactorIndex r hr) ℂ :=
  fun a j ↦ A j a

@[simp] theorem pastComplexColumnMatrix_apply {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (a : Fin k) (j : OddCofactorIndex r hr) :
    pastComplexColumnMatrix hr A a j = A j a := rfl

/-- Multiplication by the cofactor vector is exactly the literal cofactor
column combination. -/
theorem pastComplexColumnMatrix_mulVec_cofactor {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    (pastComplexColumnMatrix hr A).mulVec
        (pastHafnianCofactorVector hr A) =
      pastCofactorCombination hr A := by
  funext a
  unfold pastComplexColumnMatrix pastHafnianCofactorVector
    pastCofactorCombination oddCofactorColumnCombination Matrix.mulVec
    dotProduct
  simp [pastCofactorMatrix, lastColumnProductEquiv_apply_nonlast]

/-- `W_r` is the squared norm of the cofactor vector in the quadratic-form
normalization used by `matrix_cauchy_schwarz`. -/
theorem vectorNormSq_pastHafnianCofactorVector {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    vectorNormSq (pastHafnianCofactorVector hr A) =
      pastCofactorW hr A := by
  unfold vectorNormSq pastCofactorW oddCofactorW
    pastHafnianCofactorVector
  simp [dotProduct, Complex.normSq_apply]

/-- `V_r` is the cofactor-vector quadratic form of the usual Hermitian Gram
matrix of the past columns. -/
theorem quadraticFormReal_hermitianGram_past_eq_pastCofactorV
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    quadraticFormReal
        (hermitianGram (pastComplexColumnMatrix hr A))
        (pastHafnianCofactorVector hr A) =
      pastCofactorV hr A := by
  unfold hermitianGram
  rw [quadraticFormReal_conjTranspose_mul_self,
    pastComplexColumnMatrix_mulVec_cofactor]
  unfold vectorNormSq pastCofactorV pastCofactorCombination oddCofactorV
  simp [dotProduct, Complex.normSq_apply]

/-- Literal pointwise reciprocal Cauchy--Schwarz bound. -/
theorem pastCofactorV_inv_le_inverseGram_quadratic_div_W_sq
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hQ : (hermitianGram (pastComplexColumnMatrix hr A)).PosDef)
    (hC : pastHafnianCofactorVector hr A ≠ 0) :
    (pastCofactorV hr A)⁻¹ ≤
      quadraticFormReal
          (hermitianGram (pastComplexColumnMatrix hr A))⁻¹
          (pastHafnianCofactorVector hr A) /
        (pastCofactorW hr A) ^ 2 := by
  simpa [quadraticFormReal_hermitianGram_past_eq_pastCofactorV hr A,
    vectorNormSq_pastHafnianCofactorVector hr A] using
    (inverse_quadraticFormReal_le hQ hC)

/-- Complex quadratic forms are monotone in Loewner order. -/
theorem quadraticFormReal_mono
    {m : Type*} [Fintype m] [DecidableEq m]
    {Q T : Matrix m m ℂ} (hQT : Q ≤ T) (c : m → ℂ) :
    quadraticFormReal Q c ≤ quadraticFormReal T c := by
  have hpsd : (T - Q).PosSemidef := Matrix.le_iff.mp hQT
  have hnonneg := hpsd.re_dotProduct_nonneg c
  unfold quadraticFormReal at hnonneg ⊢
  simp only [Matrix.sub_mulVec, dotProduct_sub, map_sub] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Pointwise literal bound after the Schur-complement comparison.  The
right side is the quadratic form whose conditional score is explicit. -/
theorem pastCofactorV_inv_le_coupledSchur_quadratic_div_W_sq
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hfull : Function.Injective
      (complexConjugateColumnPair (pastComplexColumnMatrix hr A)).mulVec)
    (hC : pastHafnianCofactorVector hr A ≠ 0) :
    (pastCofactorV hr A)⁻¹ ≤
      quadraticFormReal
          (coupledSchurComplement (pastComplexColumnMatrix hr A))⁻¹
          (pastHafnianCofactorVector hr A) /
        (pastCofactorW hr A) ^ 2 := by
  let B := pastComplexColumnMatrix hr A
  have hK : (coupledGramKernel B).PosDef :=
    coupledGramKernel_posDef B hfull
  have hQ : (hermitianGram B).PosDef := by
    convert hK.submatrix (e := Sum.inl) Sum.inl_injective using 1 <;>
      ext i j <;> rfl
  calc
    (pastCofactorV hr A)⁻¹ ≤
        quadraticFormReal (hermitianGram B)⁻¹
            (pastHafnianCofactorVector hr A) /
          (pastCofactorW hr A) ^ 2 :=
      pastCofactorV_inv_le_inverseGram_quadratic_div_W_sq hr A hQ hC
    _ ≤ quadraticFormReal (coupledSchurComplement B)⁻¹
            (pastHafnianCofactorVector hr A) /
          (pastCofactorW hr A) ^ 2 := by
      apply div_le_div_of_nonneg_right
      · exact quadraticFormReal_mono
          (hermitianGram_inverse_le_coupledSchur_inverse B hfull) _
      · positivity

end Wishart

end

end LogdetLean.GramHafnian
