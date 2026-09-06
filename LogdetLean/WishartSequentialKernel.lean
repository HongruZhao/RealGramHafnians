import LogdetLean.WishartSpectralRotation
import LogdetLean.WishartMellinLaplace
import Mathlib.Tactic
/-!
# Deterministic Bartlett kernel for an unnormalized Gram determinant

The sequential statistic in `WishartBetaGammaFactors` retains the normalized
Gram increment and the fresh squared column norm.  Their product telescopes
to the unnormalized Gram determinant.  This file proves that deterministic
identity, which is the last algebraic bridge before applying the finite
Mellin--Laplace product formula.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace

/-- The product of all squared column norms in a nested tuple. -/
def nestedNormSqProduct {E : Type*} [Norm E] :
    (n : ℕ) → NestedTuple E n → ℝ :=
  nestedStageProduct (fun _ x ↦ ‖x‖ ^ 2)

theorem nestedNormSqProduct_eq_finProduct
    {E : Type*} [Norm E] :
    ∀ (n : ℕ) (z : NestedTuple E n),
      nestedNormSqProduct n z =
        ∏ i, ‖nestedTupleToFin n z i‖ ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [nestedNormSqProduct, nestedStageProduct]
  | succ n ih =>
      rintro ⟨past, x⟩
      rw [Fin.prod_univ_castSucc]
      simp only [nestedNormSqProduct, nestedStageProduct,
        nestedTupleToFin, Fin.snoc_castSucc, Fin.snoc_last]
      simpa only [nestedNormSqProduct] using congrArg (fun q ↦ q * ‖x‖ ^ 2) (ih past)

/-- Multiplying each retained `(normalized increment, squared norm)` pair
separates into the normalized determinant product and the column-norm
product. -/
theorem nestedStageProduct_pairMul_sequentialFactorWithNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∀ (n : ℕ) (z : NestedTuple E n),
      nestedStageProduct (fun (_ : ℕ) (y : ℝ × ℝ) ↦ y.1 * y.2) n
          (sequentialStatistic
            (nestedNormalizedGramFactorWithNorm (E := E)) n z) =
        nestedRealProduct n
            (sequentialStatistic
              (nestedNormalizedGramFactor (E := E)) n z) *
          nestedNormSqProduct n z := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [nestedStageProduct, nestedRealProduct, nestedNormSqProduct]
  | succ n ih =>
      rintro ⟨past, x⟩
      change
        nestedStageProduct (fun (_ : ℕ) (y : ℝ × ℝ) ↦ y.1 * y.2) n
              (sequentialStatistic
                (nestedNormalizedGramFactorWithNorm (E := E)) n past) *
            (nestedNormalizedGramFactor n past x * ‖x‖ ^ 2) =
          (nestedRealProduct n
              (sequentialStatistic
                (nestedNormalizedGramFactor (E := E)) n past) *
            nestedNormalizedGramFactor n past x) *
              (nestedNormSqProduct n past * ‖x‖ ^ 2)
      rw [ih past]
      ring

/-- On the full-rank event, the sequential products of normalized Bartlett
increments and fresh squared norms equal the ordinary Gram determinant. -/
theorem nestedStageProduct_pairMul_sequentialFactorWithNorm_eq_det
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (z : NestedTuple E n)
    (hz : LinearIndependent ℝ (nestedTupleToFin n z)) :
    nestedStageProduct (fun (_ : ℕ) (y : ℝ × ℝ) ↦ y.1 * y.2) n
        (sequentialStatistic
          (nestedNormalizedGramFactorWithNorm (E := E)) n z) =
      (Matrix.gram ℝ (nestedTupleToFin n z)).det := by
  rw [nestedStageProduct_pairMul_sequentialFactorWithNorm]
  rw [nestedRealProduct_sequentialGramFactor_eq_det n z hz]
  rw [nestedNormSqProduct_eq_finProduct]
  unfold nestedNormalizedGramDet
  rw [det_normalizedGram]
  have hprod : (∏ i, ‖nestedTupleToFin n z i‖ ^ 2) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (hz.ne_zero i))
  field_simp [hprod]

/-! ## Positivity and the real Mellin--Laplace kernel -/

theorem det_normalizedGram_pos_of_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v) :
    0 < (normalizedGram v).det := by
  have hgram : 0 < (Matrix.gram ℝ v).det :=
    ((Matrix.posSemidef_gram ℝ v).posDef_iff_det_ne_zero.mpr
      (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv)).det_pos
  have hnorm : 0 < ∏ i, ‖v i‖ ^ 2 := by
    exact Finset.prod_pos fun i _ ↦
      pow_pos (norm_pos_iff.mpr (hv.ne_zero i)) 2
  rw [det_normalizedGram]
  exact div_pos hgram hnorm

theorem nestedNormalizedGramFactor_pos_of_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (past : NestedTuple E n) (x : E)
    (hfull : LinearIndependent ℝ
      (Fin.snoc (nestedTupleToFin n past) x)) :
    0 < nestedNormalizedGramFactor n past x := by
  have hpast : LinearIndependent ℝ (nestedTupleToFin n past) :=
    (linearIndependent_finSnoc.mp hfull).1
  unfold nestedNormalizedGramFactor nestedNormalizedGramDet
  exact div_pos
    (det_normalizedGram_pos_of_linearIndependent _ hfull)
    (det_normalizedGram_pos_of_linearIndependent _ hpast)

/-- Every retained Beta--Gamma pair has strictly positive coordinates. -/
def NestedPairPositive : (n : ℕ) → NestedTuple (ℝ × ℝ) n → Prop
  | 0, _ => True
  | n + 1, y => NestedPairPositive n y.1 ∧ 0 < y.2.1 ∧ 0 < y.2.2

theorem nestedPairPositive_sequentialFactorWithNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∀ (n : ℕ) (z : NestedTuple E n),
      LinearIndependent ℝ (nestedTupleToFin n z) →
      NestedPairPositive n
        (sequentialStatistic
          (nestedNormalizedGramFactorWithNorm (E := E)) n z) := by
  intro n
  induction n with
  | zero =>
      intro z hz
      trivial
  | succ n ih =>
      rintro ⟨past, x⟩ hfull
      have hpast : LinearIndependent ℝ (nestedTupleToFin n past) :=
        (linearIndependent_finSnoc.mp hfull).1
      refine ⟨ih past hpast,
        nestedNormalizedGramFactor_pos_of_linearIndependent past x hfull, ?_⟩
      exact pow_pos (norm_pos_iff.mpr (by
        simpa [nestedTupleToFin] using hfull.ne_zero (Fin.last n))) 2

/-- Weighted sum of the second (squared-norm) coordinates. -/
def nestedWeightedSecondSum (c : ℕ → ℝ) :
    (n : ℕ) → NestedTuple (ℝ × ℝ) n → ℝ
  | 0, _ => 0
  | n + 1, y => nestedWeightedSecondSum c n y.1 + c n * y.2.2

theorem nestedWeightedSecondSum_sequentialFactorWithNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℕ → ℝ) :
    ∀ (n : ℕ) (z : NestedTuple E n),
      nestedWeightedSecondSum c n
        (sequentialStatistic
            (nestedNormalizedGramFactorWithNorm (E := E)) n z) =
        ∑ i : Fin n, c i.1 * ‖nestedTupleToFin n z i‖ ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [nestedWeightedSecondSum]
  | succ n ih =>
      rintro ⟨past, x⟩
      change
        nestedWeightedSecondSum c n
            (sequentialStatistic
              (nestedNormalizedGramFactorWithNorm (E := E)) n past) +
              c n * ‖x‖ ^ 2 =
          ∑ i : Fin (n + 1), c i.1 *
            ‖nestedTupleToFin (n + 1) (past, x) i‖ ^ 2
      rw [Fin.sum_univ_castSucc]
      simp only [nestedTupleToFin, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.val_castSucc, Fin.val_last]
      rw [ih past]

theorem nestedStageProduct_pairMul_pos
    (n : ℕ) (y : NestedTuple (ℝ × ℝ) n)
    (hy : NestedPairPositive n y) :
    0 < nestedStageProduct
      (fun (_ : ℕ) (q : ℝ × ℝ) ↦ q.1 * q.2) n y := by
  induction n with
  | zero => simp [nestedStageProduct]
  | succ n ih =>
      exact mul_pos (ih y.1 hy.1) (mul_pos hy.2.1 hy.2.2)

/-- Algebraic conversion of the finite Beta--Gamma stage product into one
Mellin power and one exponential tilt. -/
theorem nestedWishartBetaGammaStageProduct_eq
    (t : ℝ) (c : ℕ → ℝ) :
    ∀ (n : ℕ) (y : NestedTuple (ℝ × ℝ) n),
      NestedPairPositive n y →
      nestedStageProduct (wishartBetaGammaStage t c) n y =
        (nestedStageProduct
          (fun (_ : ℕ) (q : ℝ × ℝ) ↦ q.1 * q.2) n y) ^ t *
          Real.exp (-(nestedWeightedSecondSum c n y)) := by
  intro n
  induction n with
  | zero =>
      intro y hy
      simp [nestedStageProduct, nestedWeightedSecondSum]
  | succ n ih =>
      intro y hy
      have hprev := nestedStageProduct_pairMul_pos n y.1 hy.1
      have hpair : 0 < y.2.1 * y.2.2 := mul_pos hy.2.1 hy.2.2
      rw [nestedStageProduct, ih y.1 hy.1]
      unfold wishartBetaGammaStage
      change
        nestedStageProduct
              (fun (_ : ℕ) (q : ℝ × ℝ) ↦ q.1 * q.2) n y.1 ^ t *
            Real.exp (-(nestedWeightedSecondSum c n y.1)) *
              (y.2.1 ^ t *
                (y.2.2 ^ t * Real.exp (-(c n) * y.2.2))) =
          (nestedStageProduct
              (fun (_ : ℕ) (q : ℝ × ℝ) ↦ q.1 * q.2) n y.1 *
                (y.2.1 * y.2.2)) ^ t *
            Real.exp (-(nestedWeightedSecondSum c n y.1 + c n * y.2.2))
      rw [Real.mul_rpow hprev.le hpair.le]
      rw [Real.mul_rpow hy.2.1.le hy.2.2.le]
      have hexp :
          Real.exp (-(nestedWeightedSecondSum c n y.1)) *
              Real.exp (-(c n) * y.2.2) =
            Real.exp (-(nestedWeightedSecondSum c n y.1 + c n * y.2.2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      ring

/-- For the actual sequential Gaussian columns, the previous algebra and
the determinant telescope give the exact unnormalized Gram kernel. -/
theorem nestedWishartBetaGammaStageProduct_sequential_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ℝ) (c : ℕ → ℝ) (n : ℕ) (z : NestedTuple E n)
    (hz : LinearIndependent ℝ (nestedTupleToFin n z)) :
    nestedStageProduct (wishartBetaGammaStage t c) n
        (sequentialStatistic
          (nestedNormalizedGramFactorWithNorm (E := E)) n z) =
      (Matrix.gram ℝ (nestedTupleToFin n z)).det ^ t *
        Real.exp (-(nestedWeightedSecondSum c n
          (sequentialStatistic
            (nestedNormalizedGramFactorWithNorm (E := E)) n z))) := by
  rw [nestedWishartBetaGammaStageProduct_eq t c n _
    (nestedPairPositive_sequentialFactorWithNorm n z hz)]
  rw [nestedStageProduct_pairMul_sequentialFactorWithNorm_eq_det n z hz]

/-- Column-side real Mellin--Laplace kernel. -/
def nestedGaussianWishartKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ℝ) (c : ℕ → ℝ) (n : ℕ) (z : NestedTuple E n) : ℝ :=
  (Matrix.gram ℝ (nestedTupleToFin n z)).det ^ t *
    Real.exp (-∑ i : Fin n, c i.1 * ‖nestedTupleToFin n z i‖ ^ 2)

theorem nestedWishartBetaGammaStageProduct_sequential_eq_kernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ℝ) (c : ℕ → ℝ) (n : ℕ) (z : NestedTuple E n)
    (hz : LinearIndependent ℝ (nestedTupleToFin n z)) :
    nestedStageProduct (wishartBetaGammaStage t c) n
        (sequentialStatistic
          (nestedNormalizedGramFactorWithNorm (E := E)) n z) =
      nestedGaussianWishartKernel t c n z := by
  rw [nestedWishartBetaGammaStageProduct_sequential_eq t c n z hz]
  rw [nestedWeightedSecondSum_sequentialFactorWithNorm]
  rfl

/-- Exact real matrix-Gamma transform for independent standard Gaussian
columns, proved through the sequential Beta--Gamma law. -/
theorem integral_nestedGaussianWishartKernel_eq_diagonal
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    {t : ℝ} (c : ℕ → ℝ)
    (ht : ∀ n < p, 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : ∀ n < p, 0 < (1 / 2 : ℝ) + c n) :
    ∫ z, nestedGaussianWishartKernel
          (E := EuclideanSpace ℝ (Fin m)) t c p z
        ∂nestedProductMeasure
          (stdGaussian (EuclideanSpace ℝ (Fin m))) p =
      ∏ n ∈ Finset.range p,
        wishartDiagonalStageTransform m n t (c n) := by
  let E := EuclideanSpace ℝ (Fin m)
  let mu := nestedProductMeasure (stdGaussian E) p
  let seq := sequentialStatistic
    (nestedNormalizedGramFactorWithNorm (E := E)) p
  let f := nestedStageProduct (wishartBetaGammaStage t c) p
  have hli : ∀ᵐ z ∂mu,
      LinearIndependent ℝ (nestedTupleToFin p z) := by
    exact ae_linearIndependent_nested_stdGaussian p (by simpa [E] using hp)
  have hae :
      (fun z : NestedTuple E p ↦
        nestedGaussianWishartKernel t c p z) =ᵐ[mu]
          (fun z ↦ f (seq z)) := by
    filter_upwards [hli] with z hz
    exact (nestedWishartBetaGammaStageProduct_sequential_eq_kernel
      t c p z hz).symm
  have hseq : Measurable seq :=
    measurable_sequentialStatistic
      (nestedNormalizedGramFactorWithNorm (E := E))
      measurable_uncurry_nestedNormalizedGramFactorWithNorm p
  have hf : Measurable f :=
    measurable_nestedStageProduct (wishartBetaGammaStage t c)
      (measurable_wishartBetaGammaStage t c) p
  have hseqlaw : Measure.map seq mu =
      nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p := by
    exact map_sequentialNormalizedGramFactorWithNorm_eq_betaGammaProduct
      m p (by simp [E]) hp
  calc
    ∫ z, nestedGaussianWishartKernel t c p z ∂mu =
        ∫ z, f (seq z) ∂mu := integral_congr_ae hae
    _ = ∫ y, f y ∂Measure.map seq mu := by
      exact (MeasureTheory.integral_map hseq.aemeasurable
        hf.aestronglyMeasurable).symm
    _ = ∫ y, f y
        ∂nestedProductMeasureFamily
          (gaussianGramBetaGammaFactorMeasure m) p := by rw [hseqlaw]
    _ = ∏ n ∈ Finset.range p,
        wishartDiagonalStageTransform m n t (c n) :=
      integral_nestedWishartBetaGammaTransform_eq_diagonal
        hm hp c ht hrate

/-! ## Exact real MGF of the actual leading statistic -/

/-- Spectral exponential-tilt coefficient, extended by zero beyond the
finite eigenvalue range. -/
def wishartSpectralTiltCoefficient {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (t : ℝ) (n : ℕ) : ℝ :=
  if hn : n < p then
    t * (1 + R.deviationEigenvalues ⟨n, hn⟩) / (m : ℝ)
  else 0

@[simp]
theorem wishartSpectralTiltCoefficient_fin {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (t : ℝ) (i : Fin p) :
    wishartSpectralTiltCoefficient m R t i.1 =
      t * (1 + R.deviationEigenvalues i) / (m : ℝ) := by
  simp [wishartSpectralTiltCoefficient, i.2]

theorem exp_mul_wishartDiagonalLeadingStatistic_eq_kernel
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) (t : ℝ)
    (z : NestedTuple (EuclideanSpace ℝ (Fin m)) p)
    (hz : LinearIndependent ℝ (nestedTupleToFin p z)) :
    Real.exp (t * wishartDiagonalLeadingStatistic m R
        (nestedTupleToFin p z)) =
      Real.exp (-t * GeneralRDecomposition.W0LogDetMean m p +
          t * (p : ℝ)) *
        nestedGaussianWishartKernel t
          (wishartSpectralTiltCoefficient m R t) p z := by
  have hdet : 0 < (Matrix.gram ℝ (nestedTupleToFin p z)).det :=
    ((Matrix.posSemidef_gram ℝ (nestedTupleToFin p z)).posDef_iff_det_ne_zero.mpr
      (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hz)).det_pos
  unfold wishartDiagonalLeadingStatistic nestedGaussianWishartKernel
  rw [Real.rpow_def_of_pos hdet]
  rw [← Real.exp_add]
  rw [← Real.exp_add]
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [wishartSpectralTiltCoefficient_fin]
  have hsum :
      (∑ i : Fin p,
          (t * (1 + R.deviationEigenvalues i) / (m : ℝ)) *
            ‖nestedTupleToFin p z i‖ ^ 2) =
        (t / (m : ℝ)) *
          ∑ i : Fin p, (1 + R.deviationEigenvalues i) *
            ‖nestedTupleToFin p z i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  field_simp [hmR]
  ring

/-- Exact real MGF of the paper's actual row-based `M_R`, on the natural
real domain where all shifted Gamma shapes and tilted rates remain positive. -/
theorem integral_exp_mul_M_R_eq_diagonal
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) {t : ℝ}
    (ht : ∀ n < p, 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : ∀ n < p,
      0 < (1 / 2 : ℝ) + wishartSpectralTiltCoefficient m R t n) :
    ∫ z, Real.exp (t * GeneralRDecomposition.M_R m R z)
        ∂standardGaussianDataMeasure m p =
      Real.exp (-t * GeneralRDecomposition.W0LogDetMean m p +
          t * (p : ℝ)) *
        ∏ n ∈ Finset.range p,
          wishartDiagonalStageTransform m n t
            (wishartSpectralTiltCoefficient m R t n) := by
  let E := EuclideanSpace ℝ (Fin m)
  let mu := standardGaussianDataMeasure m p
  let nu := nestedProductMeasure (stdGaussian E) p
  let X := GeneralRDecomposition.M_R m R
  let Y := wishartDiagonalLeadingStatistic m R ∘ nestedTupleToFin (n := p)
  let g : ℝ → ℝ := fun x ↦ Real.exp (t * x)
  let c := wishartSpectralTiltCoefficient m R t
  have hMlaw : Measure.map X mu = Measure.map Y nu := by
    exact map_M_R_eq_map_nestedWishartDiagonalLeadingStatistic R
  have hX : Measurable X := GeneralRDecomposition.measurable_M_R m R
  have hY : Measurable Y :=
    (measurable_wishartDiagonalLeadingStatistic m R).comp
      (measurable_nestedTupleToFin p)
  have hg : Measurable g := by
    unfold g
    fun_prop
  have hli : ∀ᵐ z ∂nu, LinearIndependent ℝ (nestedTupleToFin p z) := by
    exact ae_linearIndependent_nested_stdGaussian p (by simpa [E] using hp)
  have hae : (fun z : NestedTuple E p ↦ g (Y z)) =ᵐ[nu]
      (fun z ↦
        Real.exp (-t * GeneralRDecomposition.W0LogDetMean m p +
            t * (p : ℝ)) *
          nestedGaussianWishartKernel t c p z) := by
    filter_upwards [hli] with z hz
    exact exp_mul_wishartDiagonalLeadingStatistic_eq_kernel hm R t z hz
  calc
    ∫ z, g (X z) ∂mu = ∫ x, g x ∂Measure.map X mu := by
      exact (MeasureTheory.integral_map hX.aemeasurable
        hg.aestronglyMeasurable).symm
    _ = ∫ x, g x ∂Measure.map Y nu := by rw [hMlaw]
    _ = ∫ z, g (Y z) ∂nu := by
      exact MeasureTheory.integral_map hY.aemeasurable
        hg.aestronglyMeasurable
    _ = ∫ z,
        Real.exp (-t * GeneralRDecomposition.W0LogDetMean m p +
            t * (p : ℝ)) *
          nestedGaussianWishartKernel t c p z ∂nu :=
      integral_congr_ae hae
    _ = Real.exp (-t * GeneralRDecomposition.W0LogDetMean m p +
          t * (p : ℝ)) *
        ∫ z, nestedGaussianWishartKernel t c p z ∂nu := by
      rw [integral_const_mul]
    _ = Real.exp (-t * GeneralRDecomposition.W0LogDetMean m p +
          t * (p : ℝ)) *
        ∏ n ∈ Finset.range p,
          wishartDiagonalStageTransform m n t (c n) := by
      rw [integral_nestedGaussianWishartKernel_eq_diagonal hm hp c ht hrate]

end

end LogdetLean
