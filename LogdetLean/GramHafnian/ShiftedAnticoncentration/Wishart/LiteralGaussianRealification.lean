import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralPastRealification
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.MatrixGaussianBridge
/-!
# The literal circular law under realification

Separating real and imaginary parts sends every standard circular complex
coordinate to two independent `N(0,1/2)` coordinates.  We package the full
finite column-array version as a measure-preserving measurable equivalence.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- One complex coordinate, read as its real and imaginary parts. -/
def complexRealImagMeasurableEquiv : ℂ ≃ᵐ (ℝ × ℝ) :=
  Complex.measurableEquivRealProd

/-- The exact scalar law behind the real Wishart model. -/
theorem map_complexRealImag_circularGaussian :
    Measure.map complexRealImagMeasurableEquiv circularGaussian =
      (gaussianReal 0 halfGaussianVariance).prod
        (gaussianReal 0 halfGaussianVariance) := by
  let s : ℝ → ℝ := fun x ↦ (Real.sqrt 2)⁻¹ * x
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hcoeff : (2 : ℝ)⁻¹ * Real.sqrt 2 = (Real.sqrt 2)⁻¹ := by
    field_simp [hsqrt]
    nlinarith
  have hfun :
      complexRealImagMeasurableEquiv ∘ circularGaussianCoordinate =
        Prod.map s s := by
    funext q
    apply Prod.ext <;>
      simp [complexRealImagMeasurableEquiv, circularGaussianCoordinate, s,
        div_eq_mul_inv, mul_comm, hcoeff]
  rw [circularGaussian,
    Measure.map_map complexRealImagMeasurableEquiv.measurable
      measurable_circularGaussianCoordinate,
    hfun]
  rw [← Measure.map_prod_map
    (gaussianReal 0 1) (gaussianReal 0 1)
    (show Measurable s by fun_prop) (show Measurable s by fun_prop)]
  rw [show Measure.map s (gaussianReal 0 1) =
      gaussianReal 0 halfGaussianVariance by
        simpa [s] using map_invSqrtTwo_gaussianReal_zero_one]

/-- Coordinatewise real/imaginary separation for a single complex column. -/
def complexVectorRealImagMeasurableEquiv (n : ℕ) :
    (Fin n → ℂ) ≃ᵐ ((Fin n → ℝ) × (Fin n → ℝ)) where
  toFun x := ((fun a ↦ (x a).re), fun a ↦ (x a).im)
  invFun p a := (p.1 a : ℂ) + Complex.I * (p.2 a : ℂ)
  left_inv x := by
    funext a
    apply Complex.ext <;> simp
  right_inv p := by
    ext a <;> simp
  measurable_toFun := by
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro a
      exact Complex.measurable_re.comp (measurable_pi_apply a)
    · rw [measurable_pi_iff]
      intro a
      exact Complex.measurable_im.comp (measurable_pi_apply a)
  measurable_invFun := by
    change Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      fun a ↦ (p.1 a : ℂ) + Complex.I * (p.2 a : ℂ))
    rw [measurable_pi_iff]
    intro a
    fun_prop

/-- A circular complex column becomes two independent raw half-Gaussian
real columns. -/
theorem measurePreserving_complexVectorRealImag (n : ℕ) :
    MeasurePreserving (complexVectorRealImagMeasurableEquiv n)
      (circularGaussianVector n)
      ((Measure.pi fun _ : Fin n ↦
          gaussianReal 0 halfGaussianVariance).prod
        (Measure.pi fun _ : Fin n ↦
          gaussianReal 0 halfGaussianVariance)) := by
  let μ : Measure ℝ := gaussianReal 0 halfGaussianVariance
  have hscalar : MeasurePreserving complexRealImagMeasurableEquiv
      circularGaussian (μ.prod μ) :=
    ⟨complexRealImagMeasurableEquiv.measurable,
      by simpa [μ] using map_complexRealImag_circularGaussian⟩
  have hcoordinates : MeasurePreserving
      (fun x : Fin n → ℂ ↦
        fun a ↦ complexRealImagMeasurableEquiv (x a))
      (Measure.pi fun _ : Fin n ↦ circularGaussian)
      (Measure.pi fun _ : Fin n ↦ μ.prod μ) := by
    apply measurePreserving_pi
    intro a
    exact hscalar
  have hsplit : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (Measure.pi fun _ : Fin n ↦ μ.prod μ)
      ((Measure.pi fun _ : Fin n ↦ μ).prod
        (Measure.pi fun _ : Fin n ↦ μ)) := by
    exact measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
      (fun _ ↦ μ) (fun _ ↦ μ)
  have h := hsplit.comp hcoordinates
  have hfun :
      (complexVectorRealImagMeasurableEquiv n :
        (Fin n → ℂ) → ((Fin n → ℝ) × (Fin n → ℝ))) =
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) ∘
          (fun x : Fin n → ℂ ↦
            fun a ↦ complexRealImagMeasurableEquiv (x a)) := by
    funext x
    apply Prod.ext <;> funext a <;> rfl
  rw [hfun]
  simpa [circularGaussianVector, μ] using h

/-- Real/imaginary concatenation for an arbitrary finite family of complex
columns. -/
def complexColumnsRealification {I : Type*} (n : ℕ)
    (A : I → (Fin n → ℂ)) : Matrix (Fin n) (I ⊕ I) ℝ :=
  fun a ↦ Sum.elim (fun j ↦ (A j a).re) (fun j ↦ (A j a).im)

/-- Real/imaginary concatenation is a measurable equivalence, not merely a
map modulo null sets. -/
def complexColumnsRealificationMeasurableEquiv
    (I : Type*) [Fintype I] (n : ℕ) :
    (I → (Fin n → ℂ)) ≃ᵐ Matrix (Fin n) (I ⊕ I) ℝ where
  toFun := complexColumnsRealification n
  invFun R j a :=
    (R a (Sum.inl j) : ℂ) + Complex.I * (R a (Sum.inr j) : ℂ)
  left_inv A := by
    funext j a
    apply Complex.ext <;>
      simp [complexColumnsRealification]
  right_inv R := by
    ext a j
    cases j <;>
      simp [complexColumnsRealification]
  measurable_toFun := by
    change Measurable (fun A : I → (Fin n → ℂ) ↦
      (fun a ↦ Sum.elim (fun j ↦ (A j a).re)
        (fun j ↦ (A j a).im) : Fin n → I ⊕ I → ℝ))
    rw [measurable_pi_iff]
    intro a
    rw [measurable_pi_iff]
    rintro (j | j)
    · exact Complex.measurable_re.comp
        ((measurable_pi_apply a).comp (measurable_pi_apply j))
    · exact Complex.measurable_im.comp
        ((measurable_pi_apply a).comp (measurable_pi_apply j))
  measurable_invFun := by
    change Measurable (fun R : Fin n → (I ⊕ I → ℝ) ↦
      fun j a ↦ (R a (Sum.inl j) : ℂ) +
        Complex.I * (R a (Sum.inr j) : ℂ))
    fun_prop

/-- Identity equivalence from the curried product measurable space to the
explicit matrix measurable-space instance. -/
def curriedMatrixSumMeasurableEquiv
    (n : ℕ) (I : Type*) [Fintype I] :
    (Fin n → I ⊕ I → ℝ) ≃ᵐ Matrix (Fin n) (I ⊕ I) ℝ where
  toFun x := Matrix.of x
  invFun R a i := R a i
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun x : Fin n → I ⊕ I → ℝ ↦ x)
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin n → I ⊕ I → ℝ ↦ x)
    fun_prop

/-- The raw iid `N(0,1/2)` law on a real matrix with a sum-type column
index. -/
def halfGaussianMatrixSum (n : ℕ) (I : Type*) [Fintype I] :
    Measure (Matrix (Fin n) (I ⊕ I) ℝ) :=
  Measure.map (curriedMatrixSumMeasurableEquiv n I)
    (Measure.pi fun _ : Fin n ↦
      Measure.pi fun _ : I ⊕ I ↦
        gaussianReal 0 halfGaussianVariance)

instance (n : ℕ) (I : Type*) [Fintype I] :
    IsProbabilityMeasure (halfGaussianMatrixSum n I) := by
  unfold halfGaussianMatrixSum
  exact Measure.isProbabilityMeasure_map
    (curriedMatrixSumMeasurableEquiv n I).measurable.aemeasurable

instance (n : ℕ) (I : Type*) [Fintype I] :
    SigmaFinite (halfGaussianMatrixSum n I) := by
  infer_instance

/-- The full literal iid circular column family realifies to the raw iid
half-Gaussian matrix law. -/
theorem measurePreserving_complexColumnsRealification
    (I : Type*) [Fintype I] (n : ℕ) :
    MeasurePreserving (complexColumnsRealificationMeasurableEquiv I n)
      (Measure.pi fun _ : I ↦ circularGaussianVector n)
      (halfGaussianMatrixSum n I) := by
  let μ : Measure ℝ := gaussianReal 0 halfGaussianVariance
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  let ρ : Measure (I → (Fin n → ℝ)) := Measure.pi fun _ : I ↦ ν
  let τ : Measure (Fin n → (I → ℝ)) :=
    Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : I ↦ μ

  have hvec : MeasurePreserving (complexVectorRealImagMeasurableEquiv n)
      (circularGaussianVector n) (ν.prod ν) := by
    simpa [ν, μ] using measurePreserving_complexVectorRealImag n
  have hcolumns : MeasurePreserving
      (fun A : I → (Fin n → ℂ) ↦
        fun j ↦ complexVectorRealImagMeasurableEquiv n (A j))
      (Measure.pi fun _ : I ↦ circularGaussianVector n)
      (Measure.pi fun _ : I ↦ ν.prod ν) := by
    apply measurePreserving_pi
    intro j
    exact hvec
  have houterSplit : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow
        (Fin n → ℝ) (Fin n → ℝ) I)
      (Measure.pi fun _ : I ↦ ν.prod ν) (ρ.prod ρ) := by
    simpa [ρ] using
      (measurePreserving_arrowProdEquivProdArrow
        (Fin n → ℝ) (Fin n → ℝ) I
        (fun _ ↦ ν) (fun _ ↦ ν))
  have htranspose : MeasurePreserving
      (LogdetLean.piTransposeMeasurableEquiv I (Fin n) ℝ)
      ρ τ := by
    refine ⟨(LogdetLean.piTransposeMeasurableEquiv I (Fin n) ℝ).measurable, ?_⟩
    simpa [ρ, τ, ν, μ] using
      (LogdetLean.map_pi_pi_piTranspose
        (I := I) (J := Fin n) μ)
  have htransposePair : MeasurePreserving
      (MeasurableEquiv.prodCongr
        (LogdetLean.piTransposeMeasurableEquiv I (Fin n) ℝ)
        (LogdetLean.piTransposeMeasurableEquiv I (Fin n) ℝ))
      (ρ.prod ρ) (τ.prod τ) :=
    htranspose.prod htranspose
  have hrowPair : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow
        (I → ℝ) (I → ℝ) (Fin n)).symm
      (τ.prod τ)
      (Measure.pi fun _ : Fin n ↦
        (Measure.pi fun _ : I ↦ μ).prod
          (Measure.pi fun _ : I ↦ μ)) := by
    simpa [τ] using
      (measurePreserving_arrowProdEquivProdArrow
        (I → ℝ) (I → ℝ) (Fin n)
        (fun _ ↦ Measure.pi fun _ : I ↦ μ)
        (fun _ ↦ Measure.pi fun _ : I ↦ μ)).symm
  have hrowConcatOne : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : I ⊕ I ↦ ℝ)).symm
      ((Measure.pi fun _ : I ↦ μ).prod
        (Measure.pi fun _ : I ↦ μ))
      (Measure.pi fun _ : I ⊕ I ↦ μ) := by
    simpa using measurePreserving_sumPiEquivProdPi_symm
      (fun _ : I ⊕ I ↦ μ)
  have hrowConcat : MeasurePreserving
      (fun B : Fin n → ((I → ℝ) × (I → ℝ)) ↦
        fun a ↦ (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : I ⊕ I ↦ ℝ)).symm (B a))
      (Measure.pi fun _ : Fin n ↦
        (Measure.pi fun _ : I ↦ μ).prod
          (Measure.pi fun _ : I ↦ μ))
      (Measure.pi fun _ : Fin n ↦
        Measure.pi fun _ : I ⊕ I ↦ μ) := by
    apply measurePreserving_pi
    intro a
    exact hrowConcatOne
  have htotalRaw := hrowConcat.comp
    (hrowPair.comp
      (htransposePair.comp (houterSplit.comp hcolumns)))
  have hmatrix : MeasurePreserving
      (curriedMatrixSumMeasurableEquiv n I)
      (Measure.pi fun _ : Fin n ↦
        Measure.pi fun _ : I ⊕ I ↦ μ)
      (halfGaussianMatrixSum n I) := by
    exact ⟨(curriedMatrixSumMeasurableEquiv n I).measurable, rfl⟩
  have htotal := hmatrix.comp htotalRaw
  have hfun :
      (complexColumnsRealificationMeasurableEquiv I n :
        (I → (Fin n → ℂ)) → Matrix (Fin n) (I ⊕ I) ℝ) =
      (curriedMatrixSumMeasurableEquiv n I) ∘
        (fun B : Fin n → ((I → ℝ) × (I → ℝ)) ↦
          fun a ↦ (MeasurableEquiv.sumPiEquivProdPi
            (fun _ : I ⊕ I ↦ ℝ)).symm (B a)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow
          (I → ℝ) (I → ℝ) (Fin n)).symm ∘
        (MeasurableEquiv.prodCongr
          (LogdetLean.piTransposeMeasurableEquiv I (Fin n) ℝ)
          (LogdetLean.piTransposeMeasurableEquiv I (Fin n) ℝ)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow
          (Fin n → ℝ) (Fin n → ℝ) I) ∘
        (fun A : I → (Fin n → ℂ) ↦
          fun j ↦ complexVectorRealImagMeasurableEquiv n (A j)) := by
    funext A
    ext a j
    cases j <;> rfl
  refine ⟨(complexColumnsRealificationMeasurableEquiv I n).measurable, ?_⟩
  rw [hfun]
  simpa [μ] using htotal.map_eq

/-- Literal specialization of the preceding generic measurable equivalence. -/
theorem complexColumnsRealification_eq_pastRealifiedMatrix
    {r n : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin n → ℂ)) :
    complexColumnsRealification n A = pastRealifiedMatrix hr A := by
  rfl

theorem measurePreserving_pastRealifiedMatrix
    {r n : ℕ} (hr : 1 ≤ r) :
    MeasurePreserving
      (complexColumnsRealificationMeasurableEquiv
        (OddCofactorIndex r hr) n)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦
        circularGaussianVector n)
      (halfGaussianMatrixSum n (OddCofactorIndex r hr)) :=
  measurePreserving_complexColumnsRealification
    (OddCofactorIndex r hr) n

/-! ## Reindexing the split columns by a numeric finite type -/

/-- Reindex two `Fin m` real/imaginary blocks as `Fin (2*m)`. -/
def sumColumnsToFinMeasurableEquiv (n m : ℕ) :
    Matrix (Fin n) (Fin m ⊕ Fin m) ℝ ≃ᵐ
      Matrix (Fin n) (Fin (2 * m)) ℝ := by
  let e : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
    finSumFinEquiv.trans (finCongr (Nat.two_mul m)).symm
  exact
    { toFun := fun R a j ↦ R a (e.symm j)
      invFun := fun R a j ↦ R a (e j)
      left_inv := by
        intro R
        ext a j
        simp
      right_inv := by
        intro R
        ext a j
        simp
      measurable_toFun := by
        change Measurable (fun R : Fin n → (Fin m ⊕ Fin m → ℝ) ↦
          fun a j ↦ R a (e.symm j))
        fun_prop
      measurable_invFun := by
        change Measurable (fun R : Fin n → (Fin (2 * m) → ℝ) ↦
          fun a j ↦ R a (e j))
        fun_prop }

/-- Numeric reindexing sends the sum-column half-Gaussian matrix law to the
standard `halfGaussianMatrix` used by the flattened IBP theorem. -/
theorem map_sumColumnsToFin_halfGaussianMatrixSum (n m : ℕ) :
    Measure.map (sumColumnsToFinMeasurableEquiv n m)
        (halfGaussianMatrixSum n (Fin m)) =
      halfGaussianMatrix n (2 * m) := by
  let μ : Measure ℝ := gaussianReal 0 halfGaussianVariance
  let e : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
    finSumFinEquiv.trans (finCongr (Nat.two_mul m)).symm
  let rawSum : Measure (Fin n → (Fin m ⊕ Fin m → ℝ)) :=
    Measure.pi fun _ : Fin n ↦
      Measure.pi fun _ : Fin m ⊕ Fin m ↦ μ
  let rawFin : Measure (Fin n → (Fin (2 * m) → ℝ)) :=
    Measure.pi fun _ : Fin n ↦
      Measure.pi fun _ : Fin (2 * m) ↦ μ
  let rowReindex :
      (Fin n → (Fin m ⊕ Fin m → ℝ)) →
        (Fin n → (Fin (2 * m) → ℝ)) :=
    fun R a ↦ MeasurableEquiv.piCongrLeft
      (fun _ : Fin (2 * m) ↦ ℝ) e (R a)
  have hinner : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (2 * m) ↦ ℝ) e)
      (Measure.pi fun _ : Fin m ⊕ Fin m ↦ μ)
      (Measure.pi fun _ : Fin (2 * m) ↦ μ) := by
    simpa [e] using measurePreserving_piCongrLeft
      (fun _ : Fin (2 * m) ↦ μ)
      (finSumFinEquiv.trans (finCongr (Nat.two_mul m)).symm)
  have hrows : MeasurePreserving rowReindex rawSum rawFin := by
    apply measurePreserving_pi
    intro a
    exact hinner
  have hfun :
      (sumColumnsToFinMeasurableEquiv n m) ∘
          (curriedMatrixSumMeasurableEquiv n (Fin m)) =
        (curriedMatrixMeasurableEquiv n (2 * m)) ∘ rowReindex := by
    funext R
    ext a j
    change R a (e.symm j) =
      (Equiv.piCongrLeft (fun _ : Fin (2 * m) ↦ ℝ) e (R a)) j
    rw [Equiv.piCongrLeft_apply]
    simp only [eq_rec_constant]
  calc
    Measure.map (sumColumnsToFinMeasurableEquiv n m)
        (halfGaussianMatrixSum n (Fin m)) =
        Measure.map
          ((sumColumnsToFinMeasurableEquiv n m) ∘
            (curriedMatrixSumMeasurableEquiv n (Fin m))) rawSum := by
      rw [halfGaussianMatrixSum]
      rw [Measure.map_map
        (sumColumnsToFinMeasurableEquiv n m).measurable
        (curriedMatrixSumMeasurableEquiv n (Fin m)).measurable]
    _ = Measure.map
          ((curriedMatrixMeasurableEquiv n (2 * m)) ∘ rowReindex)
          rawSum := by rw [hfun]
    _ = Measure.map (curriedMatrixMeasurableEquiv n (2 * m))
          (Measure.map rowReindex rawSum) := by
      rw [Measure.map_map
        (curriedMatrixMeasurableEquiv n (2 * m)).measurable
        hrows.measurable]
    _ = Measure.map (curriedMatrixMeasurableEquiv n (2 * m)) rawFin := by
      rw [hrows.map_eq]
    _ = halfGaussianMatrix n (2 * m) := by
      simpa [rawFin, halfGaussianRowProduct, μ] using
        map_curriedMatrix_halfGaussianRowProduct n (2 * m)

theorem measurePreserving_sumColumnsToFin_halfGaussianMatrixSum
    (n m : ℕ) :
    MeasurePreserving (sumColumnsToFinMeasurableEquiv n m)
      (halfGaussianMatrixSum n (Fin m))
      (halfGaussianMatrix n (2 * m)) :=
  ⟨(sumColumnsToFinMeasurableEquiv n m).measurable,
    map_sumColumnsToFin_halfGaussianMatrixSum n m⟩

/-- Reindex an arbitrary finite split-column type by its canonical `Fin`
model. -/
def sumColumnIndexToFinMeasurableEquiv
    (n : ℕ) (I : Type*) [Fintype I] :
    Matrix (Fin n) (I ⊕ I) ℝ ≃ᵐ
      Matrix (Fin n)
        (Fin (Fintype.card I) ⊕ Fin (Fintype.card I)) ℝ := by
  let e : I ⊕ I ≃ Fin (Fintype.card I) ⊕ Fin (Fintype.card I) :=
    (Fintype.equivFin I).sumCongr (Fintype.equivFin I)
  exact
    { toFun := fun R a j ↦ R a (e.symm j)
      invFun := fun R a j ↦ R a (e j)
      left_inv := by
        intro R
        ext a j
        simp
      right_inv := by
        intro R
        ext a j
        simp
      measurable_toFun := by
        change Measurable (fun R : Fin n → (I ⊕ I → ℝ) ↦
          fun a j ↦ R a (e.symm j))
        fun_prop
      measurable_invFun := by
        change Measurable
          (fun R : Fin n →
              (Fin (Fintype.card I) ⊕ Fin (Fintype.card I) → ℝ) ↦
            fun a j ↦ R a (e j))
        fun_prop }

/-- The arbitrary-index iid matrix law is invariant under the canonical
column reindexing. -/
theorem map_sumColumnIndexToFin_halfGaussianMatrixSum
    (n : ℕ) (I : Type*) [Fintype I] :
    Measure.map (sumColumnIndexToFinMeasurableEquiv n I)
        (halfGaussianMatrixSum n I) =
      halfGaussianMatrixSum n (Fin (Fintype.card I)) := by
  let μ : Measure ℝ := gaussianReal 0 halfGaussianVariance
  let e : I ⊕ I ≃ Fin (Fintype.card I) ⊕ Fin (Fintype.card I) :=
    (Fintype.equivFin I).sumCongr (Fintype.equivFin I)
  let rawI : Measure (Fin n → (I ⊕ I → ℝ)) :=
    Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : I ⊕ I ↦ μ
  let rawFin : Measure
      (Fin n →
        (Fin (Fintype.card I) ⊕ Fin (Fintype.card I) → ℝ)) :=
    Measure.pi fun _ : Fin n ↦
      Measure.pi fun _ : Fin (Fintype.card I) ⊕ Fin (Fintype.card I) ↦ μ
  let rowReindex :
      (Fin n → (I ⊕ I → ℝ)) →
        (Fin n →
          (Fin (Fintype.card I) ⊕ Fin (Fintype.card I) → ℝ)) :=
    fun R a ↦ MeasurableEquiv.piCongrLeft
      (fun _ : Fin (Fintype.card I) ⊕ Fin (Fintype.card I) ↦ ℝ)
      e (R a)
  have hinner : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (Fintype.card I) ⊕ Fin (Fintype.card I) ↦ ℝ) e)
      (Measure.pi fun _ : I ⊕ I ↦ μ)
      (Measure.pi fun _ :
        Fin (Fintype.card I) ⊕ Fin (Fintype.card I) ↦ μ) := by
    simpa [e] using measurePreserving_piCongrLeft
      (fun _ : Fin (Fintype.card I) ⊕ Fin (Fintype.card I) ↦ μ)
      ((Fintype.equivFin I).sumCongr (Fintype.equivFin I))
  have hrows : MeasurePreserving rowReindex rawI rawFin := by
    apply measurePreserving_pi
    intro a
    exact hinner
  have hfun :
      (sumColumnIndexToFinMeasurableEquiv n I) ∘
          (curriedMatrixSumMeasurableEquiv n I) =
        (curriedMatrixSumMeasurableEquiv n (Fin (Fintype.card I))) ∘
          rowReindex := by
    funext R
    ext a j
    change R a (e.symm j) =
      (Equiv.piCongrLeft
        (fun _ : Fin (Fintype.card I) ⊕ Fin (Fintype.card I) ↦ ℝ)
        e (R a)) j
    rw [Equiv.piCongrLeft_apply]
    simp only [eq_rec_constant]
  calc
    Measure.map (sumColumnIndexToFinMeasurableEquiv n I)
        (halfGaussianMatrixSum n I) =
        Measure.map
          ((sumColumnIndexToFinMeasurableEquiv n I) ∘
            (curriedMatrixSumMeasurableEquiv n I)) rawI := by
      rw [halfGaussianMatrixSum]
      rw [Measure.map_map
        (sumColumnIndexToFinMeasurableEquiv n I).measurable
        (curriedMatrixSumMeasurableEquiv n I).measurable]
    _ = Measure.map
          ((curriedMatrixSumMeasurableEquiv n (Fin (Fintype.card I))) ∘
            rowReindex) rawI := by rw [hfun]
    _ = Measure.map
          (curriedMatrixSumMeasurableEquiv n (Fin (Fintype.card I)))
          (Measure.map rowReindex rawI) := by
      rw [Measure.map_map
        (curriedMatrixSumMeasurableEquiv n (Fin (Fintype.card I))).measurable
        hrows.measurable]
    _ = Measure.map
          (curriedMatrixSumMeasurableEquiv n (Fin (Fintype.card I)))
          rawFin := by rw [hrows.map_eq]
    _ = halfGaussianMatrixSum n (Fin (Fintype.card I)) := by
      rfl

theorem measurePreserving_sumColumnIndexToFin_halfGaussianMatrixSum
    (n : ℕ) (I : Type*) [Fintype I] :
    MeasurePreserving (sumColumnIndexToFinMeasurableEquiv n I)
      (halfGaussianMatrixSum n I)
      (halfGaussianMatrixSum n (Fin (Fintype.card I))) :=
  ⟨(sumColumnIndexToFinMeasurableEquiv n I).measurable,
    map_sumColumnIndexToFin_halfGaussianMatrixSum n I⟩

/-- Direct measurable equivalence from arbitrary literal circular columns to
the numeric real matrix consumed by the flattened Wishart IBP theorem. -/
def literalColumnsToHalfGaussianMatrixMeasurableEquiv
    (I : Type*) [Fintype I] (n : ℕ) :
    (I → (Fin n → ℂ)) ≃ᵐ
      Matrix (Fin n) (Fin (2 * Fintype.card I)) ℝ :=
  (complexColumnsRealificationMeasurableEquiv I n).trans
    ((sumColumnIndexToFinMeasurableEquiv n I).trans
      (sumColumnsToFinMeasurableEquiv n (Fintype.card I)))

/-- The direct literal-to-numeric equivalence is measure preserving for the
exact laws used on the two sides of H2. -/
theorem measurePreserving_literalColumnsToHalfGaussianMatrix
    (I : Type*) [Fintype I] (n : ℕ) :
    MeasurePreserving
      (literalColumnsToHalfGaussianMatrixMeasurableEquiv I n)
      (Measure.pi fun _ : I ↦ circularGaussianVector n)
      (halfGaussianMatrix n (2 * Fintype.card I)) := by
  exact
    (measurePreserving_sumColumnsToFin_halfGaussianMatrixSum
      n (Fintype.card I)).comp
      ((measurePreserving_sumColumnIndexToFin_halfGaussianMatrixSum n I).comp
        (measurePreserving_complexColumnsRealification I n))

/-- Alias emphasizing the `2*m` syntax used by the analytic score theorem. -/
abbrev literalColumnsToHalfGaussianMatrixTwoMulMeasurableEquiv
    (I : Type*) [Fintype I] (n : ℕ) :
    (I → (Fin n → ℂ)) ≃ᵐ
      Matrix (Fin n) (Fin (2 * Fintype.card I)) ℝ :=
  literalColumnsToHalfGaussianMatrixMeasurableEquiv I n

theorem measurePreserving_literalColumnsToHalfGaussianMatrix_twoMul
    (I : Type*) [Fintype I] (n : ℕ) :
    MeasurePreserving
      (literalColumnsToHalfGaussianMatrixTwoMulMeasurableEquiv I n)
      (Measure.pi fun _ : I ↦ circularGaussianVector n)
      (halfGaussianMatrix n (2 * Fintype.card I)) :=
  measurePreserving_literalColumnsToHalfGaussianMatrix I n

/-- The numeric real matrix is obtained by applying the two canonical column
reindexings to the literal real/imaginary concatenation. -/
theorem literalColumnsToHalfGaussianMatrix_apply
    (I : Type*) [Fintype I] (n : ℕ)
    (A : I → (Fin n → ℂ)) :
    literalColumnsToHalfGaussianMatrixMeasurableEquiv I n A =
      sumColumnsToFinMeasurableEquiv n (Fintype.card I)
        (sumColumnIndexToFinMeasurableEquiv n I
          (complexColumnsRealification n A)) := by
  rfl

theorem measurePreserving_literalPastColumnsToHalfGaussianMatrix
    {r n : ℕ} (hr : 1 ≤ r) :
    MeasurePreserving
      (literalColumnsToHalfGaussianMatrixTwoMulMeasurableEquiv
        (OddCofactorIndex r hr) n)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector n)
      (halfGaussianMatrix n
        (2 * Fintype.card (OddCofactorIndex r hr))) :=
  measurePreserving_literalColumnsToHalfGaussianMatrix_twoMul
    (OddCofactorIndex r hr) n

end Wishart

end

end LogdetLean.GramHafnian
