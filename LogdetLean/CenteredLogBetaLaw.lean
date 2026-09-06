import LogdetLean.SampleCorrelationBeta
import LogdetLean.FullTarget
/-!
# Logarithmic law of the centered Gaussian correlation determinant

This module completes the measure-theoretic passage from the exact
Beta-product determinant law to the additive law `logBetaSumLaw`.  It proves
explicitly that every Beta factor, their finite product, and hence the
centered Gaussian correlation determinant are positive almost surely.  Thus
the use of the real logarithm loses no probability mass, and `Real.log_mul`
is applied only away from zero.

## Exact published provenance

The mathematical determinant factorization is Alain Rouault,
“Asymptotic behavior of random determinants in the Laguerre, Gram and Jacobi
ensembles,” *ALEA* **3** (2007), Proposition 2.1(2) and equations (2.4)--(2.7),
printed pp. 185--187; stable journal PDF
<https://alea.impa.br/articles/v3/03-09.pdf>.  The detailed conditional-law
proof followed by the earlier bridge modules is Rouault's arXiv version
`math/0509021`, Section 2.1, equations (4)--(10) and Proposition 2.1,
pp. 4--6.  Rouault credits the classical decomposition to Bartlett and
Cochran.

Rouault states the multiplicative Beta-product law.  The pushforward under
`Real.log`, the explicit almost-sure positivity checks, and the recursive
identification with this project's `logBetaSumLaw` are formalization choices
proved here, rather than verbatim statements attributed to Rouault.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set

noncomputable section

set_option linter.style.haveILetI false

/-- A beta measure is concentrated on strictly positive reals.  This support
statement does not require positive shape parameters: it follows directly
from the support indicator in mathlib's density definition. -/
theorem ae_pos_betaMeasure (alpha betaShape : ℝ) :
    ∀ᵐ x ∂betaMeasure alpha betaShape, 0 < x := by
  rw [betaMeasure]
  refine (ae_withDensity_iff (μ := volume)
    (measurable_betaPDFReal alpha betaShape).ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hpdf
  by_contra hx
  apply hpdf
  have hzero : betaPDFReal alpha betaShape x = 0 := by
    rw [betaPDFReal, if_neg]
    exact fun hsupport ↦ hx hsupport.1
  rw [hzero, ENNReal.ofReal_zero]

/-- Every sequential Gaussian Gram--Schmidt factor is positive almost surely.
The zeroth factor is one and every later factor is beta distributed. -/
theorem ae_pos_gaussianGramSchmidtFactorMeasure (m n : ℕ) :
    ∀ᵐ x ∂gaussianGramSchmidtFactorMeasure m n, 0 < x := by
  cases n with
  | zero => simp [gaussianGramSchmidtFactorMeasure]
  | succ n =>
      simpa only [gaussianGramSchmidtFactorMeasure_succ] using
        ae_pos_betaMeasure
          (((m - (n + 1) : ℕ) : ℝ) / 2) (((n + 1 : ℕ) : ℝ) / 2)

/-- The product of all sequential factors is positive almost surely. -/
theorem ae_pos_nestedRealProduct_gaussianFactors (m : ℕ) :
    ∀ p, ∀ᵐ z ∂nestedProductMeasureFamily
        (gaussianGramSchmidtFactorMeasure m) p,
      0 < nestedRealProduct p z := by
  intro p
  induction p with
  | zero => simp [nestedProductMeasureFamily, nestedRealProduct]
  | succ p ih =>
      have hmeas : Measurable
          (fun z : NestedTuple ℝ p × ℝ ↦ nestedRealProduct p z.1 * z.2) :=
        ((measurable_nestedRealProduct p).comp measurable_fst).mul measurable_snd
      have hset : MeasurableSet
          {z : NestedTuple ℝ p × ℝ | 0 < nestedRealProduct p z.1 * z.2} :=
        measurableSet_lt measurable_const hmeas
      rw [nestedProductMeasureFamily]
      change ∀ᵐ z : NestedTuple ℝ p × ℝ ∂
          (nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p).prod
              (gaussianGramSchmidtFactorMeasure m p),
        0 < nestedRealProduct p z.1 * z.2
      rw [Measure.ae_prod_iff_ae_ae hset]
      filter_upwards [ih] with past hpast
      filter_upwards [ae_pos_gaussianGramSchmidtFactorMeasure m p] with x hx
      simpa only [nestedRealProduct] using mul_pos hpast hx

/-- Mapping multiplication of two nonzero real variables by `log` produces
the additive convolution of their mapped logarithmic laws. -/
theorem map_log_mul_prod_eq_conv_map_log
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (nu : Measure ℝ) [SFinite mu] [SFinite nu]
    (f : alpha → ℝ) (hf : Measurable f)
    (hmu : ∀ᵐ x ∂mu, f x ≠ 0) (hnu : ∀ᵐ y ∂nu, y ≠ 0) :
    Measure.map (fun z : alpha × ℝ ↦ Real.log (f z.1 * z.2)) (mu.prod nu) =
      Measure.map (Real.log ∘ f) mu ∗ Measure.map Real.log nu := by
  have hset : MeasurableSet
      {z : alpha × ℝ |
        Real.log (f z.1 * z.2) = Real.log (f z.1) + Real.log z.2} := by
    exact measurableSet_eq_fun
      (measurable_log.comp ((hf.comp measurable_fst).mul measurable_snd))
      ((measurable_log.comp (hf.comp measurable_fst)).add
        (measurable_log.comp measurable_snd))
  have hlog :
      (fun z : alpha × ℝ ↦ Real.log (f z.1 * z.2)) =ᵐ[mu.prod nu]
        (fun z ↦ Real.log (f z.1) + Real.log z.2) := by
    change ∀ᵐ z : alpha × ℝ ∂mu.prod nu,
      Real.log (f z.1 * z.2) = Real.log (f z.1) + Real.log z.2
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [hmu] with x hx
    filter_upwards [hnu] with y hy
    exact Real.log_mul hx hy
  rw [Measure.map_congr hlog, Measure.conv]
  rw [Measure.map_prod_map mu nu (measurable_log.comp hf) measurable_log]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Stage `n+1` of Rouault's sequential factor measure is exactly the factor
indexed by `j=n+2` in the paper's notation. -/
theorem gaussianGramSchmidtFactorMeasure_succ_eq_betaShapes
    {m n : ℕ} (h : n + 2 ≤ m) :
    gaussianGramSchmidtFactorMeasure m (n + 1) =
      betaMeasure (betaShapeA m (n + 2)) (betaShapeB (n + 2)) := by
  rw [gaussianGramSchmidtFactorMeasure_succ]
  congr 2
  · rw [Nat.cast_sub (by omega : n + 1 ≤ m)]
    push_cast
    ring
  · push_cast
    ring

/-- Logarithmic pushforward of a nontrivial sequential factor. -/
theorem map_log_gaussianGramSchmidtFactorMeasure_eq_logBetaLaw
    {m n : ℕ} (h : n + 2 ≤ m) :
    Measure.map Real.log (gaussianGramSchmidtFactorMeasure m (n + 1)) =
      logBetaLaw m (n + 2) := by
  rw [gaussianGramSchmidtFactorMeasure_succ_eq_betaShapes h]
  rfl

/-- The logarithm of the independent sequential factor product has exactly
the recursively convolved law `logBetaSumLaw`. -/
theorem map_log_nestedRealProduct_gaussianFactors_eq_logBetaSumLaw
    {m p : ℕ} (hpm : p ≤ m) :
    Measure.map (Real.log ∘ nestedRealProduct p)
        (nestedProductMeasureFamily (gaussianGramSchmidtFactorMeasure m) p) =
      logBetaSumLaw m p := by
  induction p with
  | zero =>
      simp [nestedProductMeasureFamily, nestedRealProduct, logBetaSumLaw]
  | succ p ih =>
      have hprev_nonzero :
          ∀ᵐ z ∂nestedProductMeasureFamily
              (gaussianGramSchmidtFactorMeasure m) p,
            nestedRealProduct p z ≠ 0 :=
        (ae_pos_nestedRealProduct_gaussianFactors m p).mono
          (fun _ hz ↦ hz.ne')
      have hfresh_nonzero :
          ∀ᵐ x ∂gaussianGramSchmidtFactorMeasure m p, x ≠ 0 :=
        (ae_pos_gaussianGramSchmidtFactorMeasure m p).mono
          (fun _ hx ↦ hx.ne')
      change Measure.map
          (fun z : NestedTuple ℝ p × ℝ ↦
            Real.log (nestedRealProduct p z.1 * z.2))
          ((nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p).prod
              (gaussianGramSchmidtFactorMeasure m p)) = _
      rw [map_log_mul_prod_eq_conv_map_log _ _ (nestedRealProduct p)
        (measurable_nestedRealProduct p) hprev_nonzero hfresh_nonzero]
      rw [ih (by omega)]
      by_cases hp2 : 2 ≤ p + 1
      · cases p with
        | zero => omega
        | succ n =>
            rw [map_log_gaussianGramSchmidtFactorMeasure_eq_logBetaLaw hpm]
            rw [logBetaSumLaw.eq_2 m (n + 1),
              if_pos (by omega : 2 ≤ n + 2)]
      · have hp0 : p = 0 := by omega
        subst p
        simp [gaussianGramSchmidtFactorMeasure, logBetaSumLaw]

/-- The exact law of the logarithm of the centered Gaussian sample-correlation
determinant with `m+1` observations and `p≤m` variables. -/
theorem map_log_centeredSampleCorrelationDet_succ_eq_logBetaSumLaw
    (m p : ℕ) (hpm : p ≤ m) :
    Measure.map (Real.log ∘ centeredSampleCorrelationDet (m + 1) p)
        (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) =
      logBetaSumLaw m p := by
  have hdet := map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors
    m p hpm
  calc
    Measure.map (Real.log ∘ centeredSampleCorrelationDet (m + 1) p)
        (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) =
        Measure.map Real.log
          (Measure.map (centeredSampleCorrelationDet (m + 1) p)
            (nestedProductMeasure
              (stdGaussian (ObservationSpace (m + 1))) p)) :=
      (Measure.map_map measurable_log
        (measurable_centeredSampleCorrelationDet
          (Nat.zero_lt_succ m))).symm
    _ = Measure.map Real.log
          (Measure.map (nestedRealProduct p)
            (nestedProductMeasureFamily
              (gaussianGramSchmidtFactorMeasure m) p)) := by rw [hdet]
    _ = Measure.map (Real.log ∘ nestedRealProduct p)
          (nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p) :=
      Measure.map_map measurable_log (measurable_nestedRealProduct p)
    _ = logBetaSumLaw m p :=
      map_log_nestedRealProduct_gaussianFactors_eq_logBetaSumLaw hpm

/-- The centered Gaussian sample-correlation determinant is positive almost
surely whenever `p≤m`. -/
theorem ae_pos_centeredSampleCorrelationDet_succ
    (m p : ℕ) (hpm : p ≤ m) :
    ∀ᵐ z ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p,
      0 < centeredSampleCorrelationDet (m + 1) p z := by
  have hmap :
      Measure.map (centeredSampleCorrelationDet (m + 1) p)
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) p) =
        Measure.map (nestedRealProduct p)
          (nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p) :=
    map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors m p hpm
  have htarget :
      ∀ᵐ x ∂Measure.map (nestedRealProduct p)
          (nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p), 0 < x :=
    (ae_map_iff (measurable_nestedRealProduct p).aemeasurable
      ((measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))))).2
        (ae_pos_nestedRealProduct_gaussianFactors m p)
  have hmapped :
      ∀ᵐ x ∂Measure.map (centeredSampleCorrelationDet (m + 1) p)
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) p), 0 < x := by
    rw [hmap]
    exact htarget
  exact (ae_map_iff
    (measurable_centeredSampleCorrelationDet
      (Nat.zero_lt_succ m)).aemeasurable
    ((measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))))).1 hmapped

/-- `HasLaw` form of the exact centered log-determinant law. -/
theorem hasLaw_log_centeredSampleCorrelationDet_succ
    (m p : ℕ) (hpm : p ≤ m) :
    HasLaw (Real.log ∘ centeredSampleCorrelationDet (m + 1) p)
      (logBetaSumLaw m p)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) p) := by
  refine ⟨(measurable_log.comp
    (measurable_centeredSampleCorrelationDet
      (Nat.zero_lt_succ m))).aemeasurable, ?_⟩
  exact map_log_centeredSampleCorrelationDet_succ_eq_logBetaSumLaw m p hpm

end

end LogdetLean
