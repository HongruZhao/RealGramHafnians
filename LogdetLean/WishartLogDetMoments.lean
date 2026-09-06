import LogdetLean.WishartSequentialKernel
import LogdetLean.WishartColumnRotation
import LogdetLean.BetaCumulantSeries
import LogdetLean.GammaMellin
import Mathlib.Tactic
/-!
# Exact second moments of a Gaussian Gram determinant

This file derives the classical Bartlett log-determinant moments from the
joint Beta--Gamma factor law proved in `WishartBetaGammaFactors`.  The proof
is finite: at each Gram--Schmidt stage the normalized determinant increment
is independent of the fresh column energy, and different stages form a
product law.

The source result is Bartlett's decomposition; see Muirhead (1982),
Theorem 3.2.14.  No matrix-Wishart moment formula is imported as an axiom.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal RealInnerProductSpace

set_option linter.style.haveILetI false

/-- Logarithm of one normalized Bartlett coordinate. -/
def wishartPairLogBeta (q : ℝ × ℝ) : ℝ := Real.log q.1

/-- Logarithm of one fresh column energy. -/
def wishartPairLogGamma (q : ℝ × ℝ) : ℝ := Real.log q.2

/-- Logarithm of one unnormalized determinant increment. -/
def wishartPairLogDet (q : ℝ × ℝ) : ℝ :=
  wishartPairLogBeta q + wishartPairLogGamma q

/-- Sum of the logarithmic unnormalized increments in a right-nested tuple. -/
def nestedWishartLogDet : (n : ℕ) → NestedTuple (ℝ × ℝ) n → ℝ
  | 0, _ => 0
  | n + 1, y => nestedWishartLogDet n y.1 + wishartPairLogDet y.2

/-- Log energy in coordinate `i` of a nested pair tuple. -/
def nestedWishartLogEnergy (n : ℕ) (i : Fin n)
    (y : NestedTuple (ℝ × ℝ) n) : ℝ :=
  wishartPairLogGamma (nestedTupleToFin n y i)

/-- Log determinant of the ordinary Gram matrix of a nested column tuple. -/
def nestedGaussianLogDet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (z : NestedTuple E n) : ℝ :=
  Real.log (Matrix.gram ℝ (nestedTupleToFin n z)).det

/-- Log squared norm of coordinate `i` in a nested column tuple. -/
def nestedGaussianLogEnergy
    {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (i : Fin n) (z : NestedTuple E n) : ℝ :=
  Real.log (‖nestedTupleToFin n z i‖ ^ 2)

/-- The same Gram log determinant on an ordinary finite column family. -/
def gaussianColumnLogDet {m p : ℕ}
    (v : Fin p → EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.log (Matrix.gram ℝ v).det

/-- The log squared norm of one ordinary Gaussian column. -/
def gaussianColumnLogEnergy {m p : ℕ} (i : Fin p)
    (v : Fin p → EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.log (‖v i‖ ^ 2)

theorem measurable_nestedWishartLogDet : ∀ n : ℕ,
    Measurable (nestedWishartLogDet n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact (ih.comp measurable_fst).add
        (((measurable_fst.log).add measurable_snd.log).comp measurable_snd)

theorem measurable_nestedWishartLogEnergy (n : ℕ) (i : Fin n) :
    Measurable (nestedWishartLogEnergy n i) := by
  unfold nestedWishartLogEnergy wishartPairLogGamma
  exact (measurable_snd.log).comp (measurable_nestedTupleToFin_apply n i)

theorem measurable_nestedGaussianLogDet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) : Measurable (nestedGaussianLogDet (E := E) n) := by
  have hdet : Measurable
      (fun v : Fin n → E ↦ (Matrix.gram ℝ v).det) := by
    have hgram : Continuous (fun v : Fin n → E ↦ Matrix.gram ℝ v) := by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      simpa [Matrix.gram] using (continuous_apply i).inner (continuous_apply j)
    exact hgram.matrix_det.measurable
  exact (hdet.comp (measurable_nestedTupleToFin n)).log

theorem measurable_nestedGaussianLogEnergy
    {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (i : Fin n) :
    Measurable (nestedGaussianLogEnergy (E := E) n i) := by
  unfold nestedGaussianLogEnergy
  exact (((measurable_nestedTupleToFin_apply (α := E) n i).norm).pow_const 2).log

theorem measurable_gaussianColumnLogDet (m p : ℕ) :
    Measurable (gaussianColumnLogDet (m := m) (p := p)) := by
  have hgram : Continuous (fun v :
      Fin p → EuclideanSpace ℝ (Fin m) ↦ Matrix.gram ℝ v) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simpa [Matrix.gram] using (continuous_apply i).inner (continuous_apply j)
  exact hgram.matrix_det.measurable.log

theorem measurable_gaussianColumnLogEnergy {m p : ℕ} (i : Fin p) :
    Measurable (gaussianColumnLogEnergy (m := m) i) := by
  unfold gaussianColumnLogEnergy
  exact (((measurable_pi_apply i).norm).pow_const 2).log

@[simp]
theorem gaussianColumnLogDet_nestedTupleToFin
    {m p : ℕ} (z : NestedTuple (EuclideanSpace ℝ (Fin m)) p) :
    gaussianColumnLogDet (nestedTupleToFin p z) = nestedGaussianLogDet p z :=
  rfl

@[simp]
theorem gaussianColumnLogEnergy_nestedTupleToFin
    {m p : ℕ} (i : Fin p)
    (z : NestedTuple (EuclideanSpace ℝ (Fin m)) p) :
    gaussianColumnLogEnergy i (nestedTupleToFin p z) =
      nestedGaussianLogEnergy p i z := rfl

theorem gaussianColumnLogDet_dataColumns_eq_log_det_W0
    {m p : ℕ} (z : GaussianData m p) :
    gaussianColumnLogDet (dataColumns z) =
      Real.log (GeneralRDecomposition.W0 z).det := by
  unfold gaussianColumnLogDet GeneralRDecomposition.W0
  rw [scatterMatrix_eq_gram_dataColumns]

theorem gaussianColumnLogEnergy_dataColumns_eq
    {m p : ℕ} (i : Fin p) (z : GaussianData m p) :
    gaussianColumnLogEnergy i (dataColumns z) =
      Real.log (‖dataColumn z i‖ ^ 2) := rfl

/-! The next two identities are the deterministic logarithmic form of the
Bartlett telescope. -/

theorem nestedWishartLogDet_eq_log_stageProduct :
    ∀ (n : ℕ) (y : NestedTuple (ℝ × ℝ) n),
      NestedPairPositive n y →
      nestedWishartLogDet n y =
        Real.log (nestedStageProduct
          (fun (_ : ℕ) (q : ℝ × ℝ) ↦ q.1 * q.2) n y) := by
  intro n
  induction n with
  | zero =>
      intro y hy
      simp [nestedWishartLogDet, nestedStageProduct]
  | succ n ih =>
      intro y hy
      have hprev := nestedStageProduct_pairMul_pos n y.1 hy.1
      rw [nestedWishartLogDet, nestedStageProduct, ih y.1 hy.1,
        Real.log_mul hprev.ne' (mul_pos hy.2.1 hy.2.2).ne',
        Real.log_mul hy.2.1.ne' hy.2.2.ne']
      rfl

theorem nestedWishartLogDet_sequential_eq_nestedGaussianLogDet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (z : NestedTuple E n)
    (hz : LinearIndependent ℝ (nestedTupleToFin n z)) :
    nestedWishartLogDet n
        (sequentialStatistic
          (nestedNormalizedGramFactorWithNorm (E := E)) n z) =
      nestedGaussianLogDet n z := by
  rw [nestedWishartLogDet_eq_log_stageProduct n _
    (nestedPairPositive_sequentialFactorWithNorm n z hz)]
  rw [nestedStageProduct_pairMul_sequentialFactorWithNorm_eq_det n z hz]
  rfl

theorem nestedWishartLogEnergy_sequential_eq_nestedGaussianLogEnergy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∀ (n : ℕ) (i : Fin n) (z : NestedTuple E n),
      nestedWishartLogEnergy n i
          (sequentialStatistic
            (nestedNormalizedGramFactorWithNorm (E := E)) n z) =
        nestedGaussianLogEnergy n i z := by
  intro n
  induction n with
  | zero => exact fun i ↦ Fin.elim0 i
  | succ n ih =>
      intro i z
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [nestedWishartLogEnergy, nestedGaussianLogEnergy,
          sequentialStatistic, nestedTupleToFin,
          nestedNormalizedGramFactorWithNorm, wishartPairLogGamma]
      · simpa [nestedWishartLogEnergy, nestedGaussianLogEnergy,
          sequentialStatistic, nestedTupleToFin] using ih j z.1

theorem isProbabilityMeasure_gaussianGramSchmidtFactorMeasure
    {m n : ℕ} (hnm : n < m) :
    IsProbabilityMeasure (gaussianGramSchmidtFactorMeasure m n) := by
  cases n with
  | zero =>
      unfold gaussianGramSchmidtFactorMeasure
      infer_instance
  | succ n =>
      have hshape1 : 0 < (((m - (n + 1) : ℕ) : ℝ) / 2) := by
        have : 0 < m - (n + 1) := by omega
        positivity
      have hshape2 : 0 < (((n + 1 : ℕ) : ℝ) / 2) := by positivity
      letI : IsProbabilityMeasure
          (betaMeasure (((m - (n + 1) : ℕ) : ℝ) / 2)
            (((n + 1 : ℕ) : ℝ) / 2)) :=
        isProbabilityMeasureBeta hshape1 hshape2
      rw [gaussianGramSchmidtFactorMeasure_succ]
      infer_instance

theorem isProbabilityMeasure_gaussianGramBetaGammaFactorMeasure
    {m n : ℕ} (hm : 0 < m) (hnm : n < m) :
    IsProbabilityMeasure (gaussianGramBetaGammaFactorMeasure m n) := by
  letI : IsProbabilityMeasure (gaussianGramSchmidtFactorMeasure m n) :=
    isProbabilityMeasure_gaussianGramSchmidtFactorMeasure hnm
  letI : IsProbabilityMeasure
      (gammaMeasure ((m : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  unfold gaussianGramBetaGammaFactorMeasure
  infer_instance

theorem isProbabilityMeasure_nestedGaussianGramBetaGamma
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m) :
    IsProbabilityMeasure
      (nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p) := by
  induction p with
  | zero =>
      rw [nestedProductMeasureFamily]
      infer_instance
  | succ p ih =>
      letI : IsProbabilityMeasure
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p) := ih (by omega)
      letI : IsProbabilityMeasure
          (gaussianGramBetaGammaFactorMeasure m p) :=
        isProbabilityMeasure_gaussianGramBetaGammaFactorMeasure hm (by omega)
      rw [nestedProductMeasureFamily]
      infer_instance

private lemma memLp_log_of_integrable_pow_two
    {mu : Measure ℝ} [IsFiniteMeasure mu]
    (h : Integrable (fun x : ℝ ↦ Real.log x ^ 2) mu) :
    MemLp Real.log 2 mu := by
  apply (integrable_norm_rpow_iff (by fun_prop) (by norm_num) (by simp)).mp
  have hn := h.norm
  simpa [Real.norm_eq_abs, sq_abs] using hn

theorem memLp_log_gammaMeasure_two {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    MemLp Real.log 2 (gammaMeasure a r) := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  exact memLp_log_of_integrable_pow_two
    (integrable_pow_log_gammaMeasure ha hr 2)

theorem memLp_log_gaussianGramSchmidtFactorMeasure_two
    {m n : ℕ} (hnm : n < m) :
    MemLp Real.log 2 (gaussianGramSchmidtFactorMeasure m n) := by
  cases n with
  | zero =>
      rw [gaussianGramSchmidtFactorMeasure]
      refine MemLp.of_bound (by fun_prop) 0 ?_
      simp
  | succ n =>
      rw [gaussianGramSchmidtFactorMeasure_succ]
      have hshape1 : 0 < (((m - (n + 1) : ℕ) : ℝ) / 2) := by
        have : 0 < m - (n + 1) := by omega
        positivity
      have hshape2 : 0 < (((n + 1 : ℕ) : ℝ) / 2) := by positivity
      letI : IsProbabilityMeasure
          (betaMeasure (((m - (n + 1) : ℕ) : ℝ) / 2)
            (((n + 1 : ℕ) : ℝ) / 2)) :=
        isProbabilityMeasureBeta hshape1 hshape2
      exact memLp_log_of_integrable_pow_two
        (integrable_pow_log_betaMeasure hshape1 hshape2 2)

theorem memLp_wishartPairLogBeta_two {m n : ℕ}
    (hm : 0 < m) (hnm : n < m) :
    MemLp wishartPairLogBeta 2
      (gaussianGramBetaGammaFactorMeasure m n) := by
  letI : IsProbabilityMeasure
      (gammaMeasure ((m : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  unfold wishartPairLogBeta gaussianGramBetaGammaFactorMeasure
  exact (memLp_log_gaussianGramSchmidtFactorMeasure_two hnm).comp_fst
    (gammaMeasure ((m : ℝ) / 2) (1 / 2))

theorem memLp_wishartPairLogGamma_two {m n : ℕ}
    (hm : 0 < m) (hnm : n < m) :
    MemLp wishartPairLogGamma 2
      (gaussianGramBetaGammaFactorMeasure m n) := by
  letI : IsProbabilityMeasure (gaussianGramSchmidtFactorMeasure m n) :=
    isProbabilityMeasure_gaussianGramSchmidtFactorMeasure hnm
  letI : SFinite (gammaMeasure ((m : ℝ) / 2) (1 / 2)) := by
    unfold gammaMeasure
    infer_instance
  unfold wishartPairLogGamma gaussianGramBetaGammaFactorMeasure
  exact (memLp_log_gammaMeasure_two (show 0 < (m : ℝ) / 2 by positivity)
    (by norm_num)).comp_snd (gaussianGramSchmidtFactorMeasure m n)

theorem memLp_wishartPairLogDet_two {m n : ℕ}
    (hm : 0 < m) (hnm : n < m) :
    MemLp wishartPairLogDet 2
      (gaussianGramBetaGammaFactorMeasure m n) := by
  exact (memLp_wishartPairLogBeta_two hm hnm).add
    (memLp_wishartPairLogGamma_two hm hnm)

theorem memLp_nestedWishartLogDet_two {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) :
    MemLp (nestedWishartLogDet p) 2
      (nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p) := by
  induction p with
  | zero =>
      letI : IsProbabilityMeasure
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) 0) :=
        isProbabilityMeasure_nestedGaussianGramBetaGamma hm (by omega)
      refine MemLp.of_bound (by fun_prop) 0 ?_
      simp [nestedWishartLogDet]
  | succ p ih =>
      letI : IsProbabilityMeasure
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p) :=
        isProbabilityMeasure_nestedGaussianGramBetaGamma hm (by omega)
      letI : IsProbabilityMeasure
          (gaussianGramBetaGammaFactorMeasure m p) :=
        isProbabilityMeasure_gaussianGramBetaGammaFactorMeasure hm (by omega)
      rw [nestedProductMeasureFamily]
      exact (ih (by omega)).comp_fst
          (gaussianGramBetaGammaFactorMeasure m p) |>.add
        ((memLp_wishartPairLogDet_two hm (by omega)).comp_snd
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p))

theorem memLp_nestedWishartLogEnergy_two {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) (i : Fin p) :
    MemLp (nestedWishartLogEnergy p i) 2
      (nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p) := by
  -- Coordinate projection of the finite product law; proved by induction on
  -- the right-nested tuple.
  induction p with
  | zero => exact Fin.elim0 i
  | succ p ih =>
      letI : IsProbabilityMeasure
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p) :=
        isProbabilityMeasure_nestedGaussianGramBetaGamma hm (by omega)
      letI : IsProbabilityMeasure
          (gaussianGramBetaGammaFactorMeasure m p) :=
        isProbabilityMeasure_gaussianGramBetaGammaFactorMeasure hm (by omega)
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [nestedProductMeasureFamily]
        rw [show nestedWishartLogEnergy (p + 1) (Fin.last p) =
            fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              wishartPairLogGamma y.2 by
          funext y
          simp [nestedWishartLogEnergy, nestedTupleToFin]]
        exact
          (memLp_wishartPairLogGamma_two (m := m) (n := p) hm
            (by omega)).comp_snd
            (nestedProductMeasureFamily
              (gaussianGramBetaGammaFactorMeasure m) p)
      · rw [nestedProductMeasureFamily]
        rw [show nestedWishartLogEnergy (p + 1) j.castSucc =
            fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              nestedWishartLogEnergy p j y.1 by
          funext y
          simp [nestedWishartLogEnergy, nestedTupleToFin]]
        exact
          (ih (by omega) j).comp_fst
            (gaussianGramBetaGammaFactorMeasure m p)

/-! ## Exact second moments for one Bartlett stage -/

/-- The logarithm of a gamma variable has variance `trigammaSeries a`.
This is the variance-form restatement of the exact centered integral proved
in `GammaMellin`. -/
theorem variance_log_gammaMeasure_eq_trigammaSeries {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    Var[Real.log; gammaMeasure a r] = trigammaSeries a := by
  rw [variance_eq_integral (measurable_id'.log).aemeasurable]
  exact integral_centered_sq_log_gammaMeasure_eq ha hr

/-- The deterministic variance contribution of the normalized factor at
Gram--Schmidt stage `n`.  Stage zero is the constant factor one. -/
def wishartBetaStageVariance (m n : ℕ) : ℝ :=
  if n = 0 then 0 else
    trigammaSeries (((m - n : ℕ) : ℝ) / 2) -
      trigammaSeries ((m : ℝ) / 2)

/-- Exact log-variance of the normalized factor at one Bartlett stage. -/
theorem variance_log_gaussianGramSchmidtFactorMeasure_eq
    {m n : ℕ} (hnm : n < m) :
    Var[Real.log; gaussianGramSchmidtFactorMeasure m n] =
      wishartBetaStageVariance m n := by
  cases n with
  | zero =>
      simp [gaussianGramSchmidtFactorMeasure, wishartBetaStageVariance]
  | succ n =>
      have hshape1 : 0 < (((m - (n + 1) : ℕ) : ℝ) / 2) := by
        have : 0 < m - (n + 1) := by omega
        positivity
      have hshape2 : 0 < (((n + 1 : ℕ) : ℝ) / 2) := by positivity
      rw [gaussianGramSchmidtFactorMeasure_succ,
        variance_eq_integral (measurable_id'.log).aemeasurable,
        integral_centered_sq_log_betaMeasure_eq_trigammaSeries_sub
          hshape1 hshape2]
      simp only [wishartBetaStageVariance, Nat.succ_ne_zero, ↓reduceIte]
      have hsub : m - (n + 1) + (n + 1) = m :=
        Nat.sub_add_cancel (by omega)
      have hsubR : ((m - (n + 1) : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) =
          (m : ℝ) := by
        exact_mod_cast hsub
      congr 2
      norm_num
      norm_num at hsubR ⊢
      linarith

/-- The unnormalized determinant increment has the sum of the exact
log-Beta and log-Gamma variances. -/
theorem variance_wishartPairLogDet_eq {m n : ℕ}
    (hm : 0 < m) (hnm : n < m) :
    Var[wishartPairLogDet; gaussianGramBetaGammaFactorMeasure m n] =
      wishartBetaStageVariance m n +
        trigammaSeries ((m : ℝ) / 2) := by
  letI : IsProbabilityMeasure (gaussianGramSchmidtFactorMeasure m n) :=
    isProbabilityMeasure_gaussianGramSchmidtFactorMeasure hnm
  letI : IsProbabilityMeasure
      (gammaMeasure ((m : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  unfold gaussianGramBetaGammaFactorMeasure wishartPairLogDet
    wishartPairLogBeta wishartPairLogGamma
  rw [variance_add_prod
    (memLp_log_gaussianGramSchmidtFactorMeasure_two hnm)
    (memLp_log_gammaMeasure_two (by positivity) (by norm_num)),
    variance_log_gaussianGramSchmidtFactorMeasure_eq hnm,
    variance_log_gammaMeasure_eq_trigammaSeries (by positivity) (by norm_num)]

/-- At one stage, the log determinant increment and the fresh log energy
have covariance equal to the common log-Gamma variance. -/
theorem covariance_wishartPairLogDet_logGamma_eq {m n : ℕ}
    (hm : 0 < m) (hnm : n < m) :
    cov[wishartPairLogDet, wishartPairLogGamma;
      gaussianGramBetaGammaFactorMeasure m n] =
      trigammaSeries ((m : ℝ) / 2) := by
  letI : IsProbabilityMeasure (gaussianGramSchmidtFactorMeasure m n) :=
    isProbabilityMeasure_gaussianGramSchmidtFactorMeasure hnm
  letI : IsProbabilityMeasure
      (gammaMeasure ((m : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have hb := memLp_log_gaussianGramSchmidtFactorMeasure_two hnm
  have hg := memLp_log_gammaMeasure_two
    (show 0 < (m : ℝ) / 2 by positivity) (show 0 < (1 / 2 : ℝ) by norm_num)
  unfold gaussianGramBetaGammaFactorMeasure wishartPairLogDet
    wishartPairLogBeta wishartPairLogGamma
  change cov[(fun q : ℝ × ℝ ↦ Real.log q.1) +
      (fun q : ℝ × ℝ ↦ Real.log q.2),
      (fun q : ℝ × ℝ ↦ Real.log q.2);
      (gaussianGramSchmidtFactorMeasure m n).prod
        (gammaMeasure ((m : ℝ) / 2) (1 / 2))] = _
  rw [covariance_add_left (hb.comp_fst _) (hg.comp_snd _) (hg.comp_snd _),
    covariance_fst_snd_prod hb hg,
    covariance_self (μ := (gaussianGramSchmidtFactorMeasure m n).prod
      (gammaMeasure ((m : ℝ) / 2) (1 / 2)))
      ((hg.comp_snd
        (gaussianGramSchmidtFactorMeasure m n)).aemeasurable),
    measurePreserving_snd.variance_fun_comp hg.aemeasurable,
    variance_log_gammaMeasure_eq_trigammaSeries (by positivity) (by norm_num)]
  simp

/-! ## Finite product assembly -/

/-- Sum of the normalized-factor variances in the first `p` Bartlett
stages.  This intermediate form makes the finite-product induction literal. -/
def wishartBetaVarianceSum (m p : ℕ) : ℝ :=
  ∑ n ∈ Finset.range p, wishartBetaStageVariance m n

/-- Exact variance of the nested log determinant under the joint finite
Beta--Gamma product law. -/
theorem variance_nestedWishartLogDet_eq_stageSum {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) :
    Var[nestedWishartLogDet p;
      nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p] =
      wishartBetaVarianceSum m p +
        (p : ℝ) * trigammaSeries ((m : ℝ) / 2) := by
  induction p with
  | zero =>
      letI : IsProbabilityMeasure
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) 0) :=
        isProbabilityMeasure_nestedGaussianGramBetaGamma hm (by omega)
      simp [nestedProductMeasureFamily, nestedWishartLogDet,
        wishartBetaVarianceSum]
  | succ p ih =>
      letI : IsProbabilityMeasure
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p) :=
        isProbabilityMeasure_nestedGaussianGramBetaGamma hm (by omega)
      letI : IsProbabilityMeasure
          (gaussianGramBetaGammaFactorMeasure m p) :=
        isProbabilityMeasure_gaussianGramBetaGammaFactorMeasure hm (by omega)
      rw [nestedProductMeasureFamily]
      change Var[fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
          nestedWishartLogDet p y.1 + wishartPairLogDet y.2;
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p).prod
              (gaussianGramBetaGammaFactorMeasure m p)] = _
      rw [variance_add_prod
        (memLp_nestedWishartLogDet_two hm (by omega))
        (memLp_wishartPairLogDet_two hm (by omega)),
        ih (by omega), variance_wishartPairLogDet_eq hm (by omega)]
      simp only [wishartBetaVarianceSum, Finset.sum_range_succ,
        Nat.cast_add, Nat.cast_one]
      ring

/-- Adding one admissible column adds exactly the next normalized Bartlett
variance to the finite trigamma sum `nullVSeries`. -/
theorem nullVSeries_succ_eq_add_wishartBetaStageVariance
    {m p : ℕ} (hp : p < m) :
    nullVSeries m (p + 1) =
      nullVSeries m p + wishartBetaStageVariance m p := by
  cases p with
  | zero =>
      simp [nullVSeries, wishartBetaStageVariance]
  | succ p =>
      unfold nullVSeries
      rw [Finset.sum_Icc_succ_top (show 2 ≤ p + 1 + 1 by omega)]
      simp only [wishartBetaStageVariance, Nat.succ_ne_zero, ↓reduceIte]
      congr 2
      unfold betaShapeA
      rw [Nat.cast_sub (show p + 1 ≤ m by omega)]
      push_cast
      apply congrArg trigammaSeries
      ring

/-- The stage-by-stage Bartlett variance sum is the paper's exact finite
quantity `V_{m,p}=nullVSeries m p`. -/
theorem wishartBetaVarianceSum_eq_nullVSeries {m p : ℕ} (hp : p ≤ m) :
    wishartBetaVarianceSum m p = nullVSeries m p := by
  induction p with
  | zero => simp [wishartBetaVarianceSum, nullVSeries]
  | succ p ih =>
      rw [wishartBetaVarianceSum, Finset.sum_range_succ,
        ← wishartBetaVarianceSum, ih (by omega),
        nullVSeries_succ_eq_add_wishartBetaStageVariance (by omega)]

/-- Exact nested Bartlett-product variance in the paper's notation. -/
theorem variance_nestedWishartLogDet_eq_nullVSeries {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) :
    Var[nestedWishartLogDet p;
      nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p] =
      nullVSeries m p +
        (p : ℝ) * trigammaSeries ((m : ℝ) / 2) := by
  rw [variance_nestedWishartLogDet_eq_stageSum hm hp,
    wishartBetaVarianceSum_eq_nullVSeries hp]

/-! ## Transfer to independent Gaussian columns -/

theorem measurePreserving_sequentialNormalizedGramFactorWithNorm
    {m p : ℕ} (hp : p ≤ m) :
    MeasurePreserving
      (sequentialStatistic
        (nestedNormalizedGramFactorWithNorm
          (E := EuclideanSpace ℝ (Fin m))) p)
      (nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin m))) p)
      (nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p) := by
  constructor
  · exact measurable_sequentialStatistic
      (nestedNormalizedGramFactorWithNorm
        (E := EuclideanSpace ℝ (Fin m)))
      measurable_uncurry_nestedNormalizedGramFactorWithNorm p
  · exact map_sequentialNormalizedGramFactorWithNorm_eq_betaGammaProduct
      m p (by simp) hp

theorem ae_nestedGaussianLogDet_eq_nestedWishartLogDet_sequential
    {m p : ℕ} (hp : p ≤ m) :
    nestedGaussianLogDet p =ᵐ[
      nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin m))) p]
      nestedWishartLogDet p ∘
        sequentialStatistic
          (nestedNormalizedGramFactorWithNorm
            (E := EuclideanSpace ℝ (Fin m))) p := by
  filter_upwards [ae_linearIndependent_nested_stdGaussian p
    (by simpa using hp)] with z hz
  exact (nestedWishartLogDet_sequential_eq_nestedGaussianLogDet p z hz).symm

theorem nestedGaussianLogEnergy_eq_nestedWishartLogEnergy_sequential
    {m p : ℕ} (i : Fin p) :
    nestedGaussianLogEnergy p i =
      nestedWishartLogEnergy p i ∘
        sequentialStatistic
          (nestedNormalizedGramFactorWithNorm
            (E := EuclideanSpace ℝ (Fin m))) p := by
  funext z
  exact (nestedWishartLogEnergy_sequential_eq_nestedGaussianLogEnergy
    p i z).symm

theorem memLp_nestedGaussianLogDet_two {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) :
    MemLp (nestedGaussianLogDet p) 2
      (nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin m))) p) := by
  have hcomp := (memLp_nestedWishartLogDet_two hm hp).comp_measurePreserving
    (measurePreserving_sequentialNormalizedGramFactorWithNorm hp)
  exact hcomp.ae_eq
    (ae_nestedGaussianLogDet_eq_nestedWishartLogDet_sequential hp).symm

theorem memLp_nestedGaussianLogEnergy_two {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) (i : Fin p) :
    MemLp (nestedGaussianLogEnergy p i) 2
      (nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin m))) p) := by
  rw [nestedGaussianLogEnergy_eq_nestedWishartLogEnergy_sequential i]
  exact (memLp_nestedWishartLogEnergy_two hm hp i).comp_measurePreserving
    (measurePreserving_sequentialNormalizedGramFactorWithNorm hp)

private theorem covariance_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hEX : ∫ x, X x ∂μ = ∫ x, X' x ∂μ := integral_congr_ae hX
  have hEY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  unfold covariance
  apply integral_congr_ae
  filter_upwards [hX, hY] with x hx hy
  rw [hx, hy, hEX, hEY]

/-- Exact variance of the actual Gram log determinant for independent
right-nested Gaussian columns. -/
theorem variance_nestedGaussianLogDet_eq_nullVSeries {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) :
    Var[nestedGaussianLogDet p;
      nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin m))) p] =
      nullVSeries m p +
        (p : ℝ) * trigammaSeries ((m : ℝ) / 2) := by
  let seq := sequentialStatistic
    (nestedNormalizedGramFactorWithNorm
      (E := EuclideanSpace ℝ (Fin m))) p
  have hmp := measurePreserving_sequentialNormalizedGramFactorWithNorm hp
  calc
    Var[nestedGaussianLogDet p;
        nestedProductMeasure
          (stdGaussian (EuclideanSpace ℝ (Fin m))) p] =
        Var[nestedWishartLogDet p ∘ seq;
          nestedProductMeasure
            (stdGaussian (EuclideanSpace ℝ (Fin m))) p] :=
      variance_congr
        (ae_nestedGaussianLogDet_eq_nestedWishartLogDet_sequential hp)
    _ = Var[nestedWishartLogDet p;
        nestedProductMeasureFamily
          (gaussianGramBetaGammaFactorMeasure m) p] :=
      hmp.variance_fun_comp (measurable_nestedWishartLogDet p).aemeasurable
    _ = _ := variance_nestedWishartLogDet_eq_nullVSeries hm hp

private theorem covariance_comp_fst_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    cov[fun z : α × β ↦ f z.1, fun z ↦ g z.1; μ.prod ν] =
      cov[f, g; μ] := by
  exact measurePreserving_fst.hasLaw.covariance_fun_comp
    hf.aemeasurable hg.aemeasurable

private theorem covariance_comp_snd_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f g : β → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    cov[fun z : α × β ↦ f z.2, fun z ↦ g z.2; μ.prod ν] =
      cov[f, g; ν] := by
  exact measurePreserving_snd.hasLaw.covariance_fun_comp
    hf.aemeasurable hg.aemeasurable

/-- Every nested log determinant has covariance equal to the common
log-Gamma variance with each one of its column log energies. -/
theorem covariance_nestedWishartLogDet_logEnergy_eq {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) (i : Fin p) :
    cov[nestedWishartLogDet p, nestedWishartLogEnergy p i;
      nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p] =
      trigammaSeries ((m : ℝ) / 2) := by
  induction p with
  | zero => exact Fin.elim0 i
  | succ p ih =>
      letI : IsProbabilityMeasure
          (nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p) :=
        isProbabilityMeasure_nestedGaussianGramBetaGamma hm (by omega)
      letI : IsProbabilityMeasure
          (gaussianGramBetaGammaFactorMeasure m p) :=
        isProbabilityMeasure_gaussianGramBetaGammaFactorMeasure hm (by omega)
      have hprev := memLp_nestedWishartLogDet_two hm (show p ≤ m by omega)
      have hstage := memLp_wishartPairLogDet_two hm (show p < m by omega)
      have hgamma := memLp_wishartPairLogGamma_two hm (show p < m by omega)
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [nestedProductMeasureFamily]
        rw [show nestedWishartLogDet (p + 1) =
            fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              nestedWishartLogDet p y.1 + wishartPairLogDet y.2 by
          rfl]
        rw [show nestedWishartLogEnergy (p + 1) (Fin.last p) =
            fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              wishartPairLogGamma y.2 by
          funext y
          simp [nestedWishartLogEnergy, nestedTupleToFin]]
        change cov[(fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              nestedWishartLogDet p y.1) +
            (fun y ↦ wishartPairLogDet y.2),
            (fun y ↦ wishartPairLogGamma y.2);
            (nestedProductMeasureFamily
              (gaussianGramBetaGammaFactorMeasure m) p).prod
                (gaussianGramBetaGammaFactorMeasure m p)] = _
        rw [covariance_add_left (hprev.comp_fst _)
          (hstage.comp_snd _) (hgamma.comp_snd _),
          covariance_fst_snd_prod hprev hgamma,
          covariance_comp_snd_prod hstage hgamma,
          covariance_wishartPairLogDet_logGamma_eq hm (by omega), zero_add]
      · rw [nestedProductMeasureFamily]
        have henergy := memLp_nestedWishartLogEnergy_two hm
          (show p ≤ m by omega) j
        rw [show nestedWishartLogDet (p + 1) =
            fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              nestedWishartLogDet p y.1 + wishartPairLogDet y.2 by
          rfl]
        rw [show nestedWishartLogEnergy (p + 1) j.castSucc =
            fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              nestedWishartLogEnergy p j y.1 by
          funext y
          simp [nestedWishartLogEnergy, nestedTupleToFin]]
        change cov[(fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              nestedWishartLogDet p y.1) +
            (fun y ↦ wishartPairLogDet y.2),
            (fun y ↦ nestedWishartLogEnergy p j y.1);
            (nestedProductMeasureFamily
              (gaussianGramBetaGammaFactorMeasure m) p).prod
                (gaussianGramBetaGammaFactorMeasure m p)] = _
        rw [covariance_add_left (hprev.comp_fst _)
          (hstage.comp_snd _) (henergy.comp_fst _),
          covariance_comp_fst_prod hprev henergy,
          ih (by omega) j]
        have hcross : cov[(fun y : NestedTuple (ℝ × ℝ) p × (ℝ × ℝ) ↦
              wishartPairLogDet y.2),
            (fun y ↦ nestedWishartLogEnergy p j y.1);
            (nestedProductMeasureFamily
              (gaussianGramBetaGammaFactorMeasure m) p).prod
                (gaussianGramBetaGammaFactorMeasure m p)] = 0 := by
          rw [covariance_comm]
          exact covariance_fst_snd_prod henergy hstage
        rw [hcross, add_zero]

/-- Exact covariance between the actual Gaussian Gram log determinant and
each actual column log energy. -/
theorem covariance_nestedGaussianLogDet_logEnergy_eq {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) (i : Fin p) :
    cov[nestedGaussianLogDet p, nestedGaussianLogEnergy p i;
      nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin m))) p] =
      trigammaSeries ((m : ℝ) / 2) := by
  let seq := sequentialStatistic
    (nestedNormalizedGramFactorWithNorm
      (E := EuclideanSpace ℝ (Fin m))) p
  have hmp := measurePreserving_sequentialNormalizedGramFactorWithNorm hp
  have hdet := ae_nestedGaussianLogDet_eq_nestedWishartLogDet_sequential hp
  have henergy : nestedGaussianLogEnergy p i =ᵐ[
      nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin m))) p]
      nestedWishartLogEnergy p i ∘ seq := by
    exact Filter.Eventually.of_forall fun z ↦
      congrFun (nestedGaussianLogEnergy_eq_nestedWishartLogEnergy_sequential i) z
  calc
    cov[nestedGaussianLogDet p, nestedGaussianLogEnergy p i;
        nestedProductMeasure
          (stdGaussian (EuclideanSpace ℝ (Fin m))) p] =
        cov[nestedWishartLogDet p ∘ seq,
          nestedWishartLogEnergy p i ∘ seq;
          nestedProductMeasure
            (stdGaussian (EuclideanSpace ℝ (Fin m))) p] :=
      covariance_congr_ae hdet henergy
    _ = cov[nestedWishartLogDet p, nestedWishartLogEnergy p i;
        nestedProductMeasureFamily
          (gaussianGramBetaGammaFactorMeasure m) p] :=
      hmp.hasLaw.covariance_comp
        (measurable_nestedWishartLogDet p).aemeasurable
        (measurable_nestedWishartLogEnergy p i).aemeasurable
    _ = _ := covariance_nestedWishartLogDet_logEnergy_eq hm hp i

/-! ## Transfer back to the row-based Gaussian data model -/

theorem measurePreserving_dataColumns_standardGaussianDataMeasure
    (m p : ℕ) :
    MeasurePreserving dataColumns
      (standardGaussianDataMeasure m p)
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  exact ⟨measurable_dataColumns,
    map_dataColumns_standardGaussianDataMeasure m p⟩

theorem memLp_gaussianColumnLogDet_two {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) :
    MemLp (gaussianColumnLogDet (m := m) (p := p)) 2
      (Measure.pi fun _ : Fin p ↦
        stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  let mu := nestedProductMeasure
    (stdGaussian (EuclideanSpace ℝ (Fin m))) p
  let f := gaussianColumnLogDet (m := m) (p := p)
  have hcomp : MemLp (f ∘ nestedTupleToFin p) 2 mu := by
    simpa [f, mu, Function.comp_def] using
      memLp_nestedGaussianLogDet_two hm hp
  have hfmap : MemLp f 2 (Measure.map (nestedTupleToFin p) mu) :=
    (memLp_map_measure_iff
      (measurable_gaussianColumnLogDet m p).aestronglyMeasurable
      (measurable_nestedTupleToFin p).aemeasurable).2 hcomp
  rw [map_nestedTupleToFin_nestedProductMeasure] at hfmap
  exact hfmap

/-- The actual row-based `log det W₀` is square integrable.  This discharges
the `hW` input used by the general-correlation variance assembly. -/
theorem memLp_log_det_W0_two {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) :
    MemLp (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det) 2
      (standardGaussianDataMeasure m p) := by
  have hcomp := (memLp_gaussianColumnLogDet_two hm hp).comp_measurePreserving
    (measurePreserving_dataColumns_standardGaussianDataMeasure m p)
  exact hcomp.ae_eq (Filter.Eventually.of_forall fun z ↦
    gaussianColumnLogDet_dataColumns_eq_log_det_W0 z)

/-- Exact variance of the row-based standard Gaussian scatter determinant.
This discharges `hvarW`. -/
theorem variance_log_det_W0_eq_nullVSeries {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) :
    Var[fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det;
      standardGaussianDataMeasure m p] =
      nullVSeries m p +
        (p : ℝ) * trigammaSeries ((m : ℝ) / 2) := by
  let f := gaussianColumnLogDet (m := m) (p := p)
  let muPi := Measure.pi fun _ : Fin p ↦
    stdGaussian (EuclideanSpace ℝ (Fin m))
  let muNested := nestedProductMeasure
    (stdGaussian (EuclideanSpace ℝ (Fin m))) p
  have hdata := measurePreserving_dataColumns_standardGaussianDataMeasure m p
  have hnested := measurePreserving_nestedTupleToFin
    (stdGaussian (EuclideanSpace ℝ (Fin m))) p
  have hactual : (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det) =ᵐ[
        standardGaussianDataMeasure m p] f ∘ dataColumns :=
    Filter.Eventually.of_forall fun z ↦
      (gaussianColumnLogDet_dataColumns_eq_log_det_W0 z).symm
  calc
    Var[fun z : GaussianData m p ↦
          Real.log (GeneralRDecomposition.W0 z).det;
        standardGaussianDataMeasure m p] =
        Var[f ∘ dataColumns; standardGaussianDataMeasure m p] :=
      variance_congr hactual
    _ = Var[f; muPi] :=
      hdata.variance_fun_comp
        (measurable_gaussianColumnLogDet m p).aemeasurable
    _ = Var[f ∘ nestedTupleToFin p; muNested] :=
      (hnested.variance_fun_comp
        (measurable_gaussianColumnLogDet m p).aemeasurable).symm
    _ = Var[nestedGaussianLogDet p; muNested] := by rfl
    _ = _ := variance_nestedGaussianLogDet_eq_nullVSeries hm hp

/-- Covariance of the actual row-based Gram log determinant with the log
energy of one of its original independent columns. -/
theorem covariance_log_det_W0_log_dataColumn_eq {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) (i : Fin p) :
    cov[fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det,
      fun z ↦ Real.log (‖dataColumn z i‖ ^ 2);
      standardGaussianDataMeasure m p] =
      trigammaSeries ((m : ℝ) / 2) := by
  let f := gaussianColumnLogDet (m := m) (p := p)
  let g := gaussianColumnLogEnergy (m := m) i
  let muPi := Measure.pi fun _ : Fin p ↦
    stdGaussian (EuclideanSpace ℝ (Fin m))
  let muNested := nestedProductMeasure
    (stdGaussian (EuclideanSpace ℝ (Fin m))) p
  have hdata := measurePreserving_dataColumns_standardGaussianDataMeasure m p
  have hnested := measurePreserving_nestedTupleToFin
    (stdGaussian (EuclideanSpace ℝ (Fin m))) p
  have hdet : (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det) =ᵐ[
        standardGaussianDataMeasure m p] f ∘ dataColumns :=
    Filter.Eventually.of_forall fun z ↦
      (gaussianColumnLogDet_dataColumns_eq_log_det_W0 z).symm
  have henergy : (fun z : GaussianData m p ↦
      Real.log (‖dataColumn z i‖ ^ 2)) =ᵐ[
        standardGaussianDataMeasure m p] g ∘ dataColumns :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  calc
    cov[fun z : GaussianData m p ↦
          Real.log (GeneralRDecomposition.W0 z).det,
        fun z ↦ Real.log (‖dataColumn z i‖ ^ 2);
        standardGaussianDataMeasure m p] =
        cov[f ∘ dataColumns, g ∘ dataColumns;
          standardGaussianDataMeasure m p] :=
      covariance_congr_ae hdet henergy
    _ = cov[f, g; muPi] :=
      hdata.hasLaw.covariance_comp
        (measurable_gaussianColumnLogDet m p).aemeasurable
        (measurable_gaussianColumnLogEnergy i).aemeasurable
    _ = cov[f ∘ nestedTupleToFin p, g ∘ nestedTupleToFin p; muNested] :=
      (hnested.hasLaw.covariance_comp
        (measurable_gaussianColumnLogDet m p).aemeasurable
        (measurable_gaussianColumnLogEnergy i).aemeasurable).symm
    _ = cov[nestedGaussianLogDet p, nestedGaussianLogEnergy p i;
        muNested] := by rfl
    _ = _ := covariance_nestedGaussianLogDet_logEnergy_eq hm hp i

/-! ## A prescribed rotation for a correlated radius -/

/-- Row `i` of the symmetric covariance square root, viewed as a unit vector
in the observation Euclidean space. -/
def covarianceSqrtRowVector {p : ℕ} (R : CorrelationMatrix p) (i : Fin p) :
    CorrelationMatrix.Observation p :=
  WithLp.toLp 2 (fun j ↦ R.covarianceSqrt i j)

theorem norm_covarianceSqrtRowVector {p : ℕ}
    (R : CorrelationMatrix p) (i : Fin p) :
    ‖covarianceSqrtRowVector R i‖ = 1 := by
  have hmul := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A i i)
    R.covarianceSqrt_mul_self
  have hsum : ∑ j : Fin p,
      R.covarianceSqrt i j * R.covarianceSqrt j i = 1 := by
    simpa [Matrix.mul_apply, R.apply_self] using hmul
  have hsq : ‖covarianceSqrtRowVector R i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin p, (R.covarianceSqrt i j) ^ 2) = 1
    calc
      (∑ j : Fin p, (R.covarianceSqrt i j) ^ 2) =
          ∑ j : Fin p,
            R.covarianceSqrt i j * R.covarianceSqrt j i := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [R.covarianceSqrt_apply_symm j i]
        ring
      _ = 1 := hsum
  nlinarith [norm_nonneg (covarianceSqrtRowVector R i)]

theorem inner_covarianceSqrtRowVector_eq_correlateObservation_apply
    {p : ℕ} (R : CorrelationMatrix p) (i : Fin p)
    (x : CorrelationMatrix.Observation p) :
    inner ℝ (covarianceSqrtRowVector R i) x =
      R.correlateObservation x i := by
  unfold covarianceSqrtRowVector CorrelationMatrix.correlateObservation
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The prescribed unit covariance-square-root row extends to a full
orthonormal basis, with its index retained. -/
theorem exists_orthonormalBasis_covarianceSqrtRowVector {p : ℕ}
    (R : CorrelationMatrix p) (i : Fin p) :
    ∃ b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p),
      b i = covarianceSqrtRowVector R i := by
  let a := covarianceSqrtRowVector R i
  let v : Fin p → CorrelationMatrix.Observation p := fun _ ↦ a
  let s : Set (Fin p) := {i}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro j
    exact norm_covarianceSqrtRowVector R i
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp)
  refine ⟨b, ?_⟩
  simpa [s, v, a] using hb i (by simp [s])

/-- Under the prescribed basis rotation, coordinate `i` is exactly the
correlated Gaussian column `G_i`. -/
theorem dataColumn_rotateRowsByBasis_eq_G {m p : ℕ}
    (R : CorrelationMatrix p) (i : Fin p)
    (b : OrthonormalBasis (Fin p) ℝ (CorrelationMatrix.Observation p))
    (hb : b i = covarianceSqrtRowVector R i)
    (z : GaussianData m p) :
    dataColumn (rotateRowsByBasis b z) i =
      GeneralRDecomposition.G R z i := by
  rw [dataColumn_rotateRowsByBasis]
  ext k
  change inner ℝ (b i) (z k) = R.correlateObservation (z k) i
  rw [hb, inner_covarianceSqrtRowVector_eq_correlateObservation_apply]

theorem measurable_log_det_W0 (m p : ℕ) :
    Measurable (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det) := by
  rw [show (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det) =
      gaussianColumnLogDet ∘ dataColumns by
    funext z
    exact (gaussianColumnLogDet_dataColumns_eq_log_det_W0 z).symm]
  exact (measurable_gaussianColumnLogDet m p).comp measurable_dataColumns

/-- The determinant/radius covariance is independent of which unit linear
combination of the independent Gaussian columns defines the radius.  Applied
to the covariance-square-root row, this is exactly the missing `hcovW`
identity for an arbitrary correlation matrix. -/
theorem covariance_log_det_W0_log_Q_eq {m p : ℕ}
    (hm : 0 < m) (hp : p ≤ m) (R : CorrelationMatrix p) (i : Fin p) :
    cov[fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det,
      fun z ↦ Real.log (GeneralRDecomposition.Q R z i);
      standardGaussianDataMeasure m p] =
      trigammaSeries ((m : ℝ) / 2) := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_covarianceSqrtRowVector R i
  let rot := rotateRowsByBasis (m := m) b
  let L : GaussianData m p → ℝ := fun z ↦
    Real.log (GeneralRDecomposition.W0 z).det
  let qR : GaussianData m p → ℝ := fun z ↦
    Real.log (GeneralRDecomposition.Q R z i)
  let q0 : GaussianData m p → ℝ := fun z ↦
    Real.log (‖dataColumn z i‖ ^ 2)
  have hrot : MeasurePreserving rot
      (standardGaussianDataMeasure m p)
      (standardGaussianDataMeasure m p) := by
    exact ⟨measurable_rotateRowsByBasis b,
      map_rotateRowsByBasis_standardGaussianDataMeasure b⟩
  have hLmeas : Measurable L := measurable_log_det_W0 m p
  have hq0meas : Measurable q0 := by
    unfold q0
    exact (measurable_gaussianColumnLogEnergy i).comp measurable_dataColumns
  have hL : L =ᵐ[standardGaussianDataMeasure m p] L ∘ rot :=
    Filter.Eventually.of_forall fun z ↦ by
      unfold L rot GeneralRDecomposition.W0
      exact congrArg Real.log
        (det_scatterMatrix_rotateRowsByBasis b z).symm
  have hq : qR =ᵐ[standardGaussianDataMeasure m p] q0 ∘ rot :=
    Filter.Eventually.of_forall fun z ↦ by
      unfold qR q0 rot GeneralRDecomposition.Q
      change Real.log (‖GeneralRDecomposition.G R z i‖ ^ 2) =
        Real.log (‖dataColumn (rotateRowsByBasis b z) i‖ ^ 2)
      rw [dataColumn_rotateRowsByBasis_eq_G R i b hb]
  calc
    cov[fun z : GaussianData m p ↦
          Real.log (GeneralRDecomposition.W0 z).det,
        fun z ↦ Real.log (GeneralRDecomposition.Q R z i);
        standardGaussianDataMeasure m p] =
        cov[L ∘ rot, q0 ∘ rot;
          standardGaussianDataMeasure m p] := by
      change cov[L, qR; standardGaussianDataMeasure m p] = _
      exact covariance_congr_ae hL hq
    _ = cov[L, q0; standardGaussianDataMeasure m p] :=
      hrot.hasLaw.covariance_comp hLmeas.aemeasurable hq0meas.aemeasurable
    _ = _ := by
      exact covariance_log_det_W0_log_dataColumn_eq hm hp i

end

end LogdetLean
