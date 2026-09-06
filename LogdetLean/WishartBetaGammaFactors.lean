import LogdetLean.FixedPastBeta
import LogdetLean.ScalarGammaBetaBridge
import Mathlib.Tactic
/-!
# Joint Beta--Gamma factors for a Gaussian Gram matrix

This file strengthens the normalized Bartlett factorization already proved in
`FixedPastBeta`.  At stage `n`, we retain both

* the normalized Gram--Schmidt factor, and
* the squared norm of the fresh Gaussian column.

For a linearly independent fixed past, these two quantities have the product
law

`Beta((m-n)/2,n/2) ⊗ Gamma(m/2,1/2)`

(with the Beta coordinate equal to one at `n=0`).  Thus the normalized factor
and the column energy are independent.  The proof is the classical
Beta--Gamma change of variables applied to the two orthogonal Gaussian
projection energies.  This is the scalar Bartlett ingredient used in the
Wishart matrix-gamma transform; compare Muirhead (1982), Theorem 3.2.14, and
Zhao, arXiv:2608.00565v1, Lemma 5.4 and Appendix A.  Every statement below is
derived from the density/Jacobian theorem in `ScalarGammaBetaBridge` and the
Gaussian projection laws in `FixedSubspaceGaussian`.
-/

namespace LogdetLean

noncomputable section

open Filter MeasureTheory ProbabilityTheory Matrix Module Set
open scoped ENNReal RealInnerProductSpace

private theorem ae_mem_Ioo_betaMeasure (a b : ℝ) :
    ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  rw [betaMeasure]
  refine (ae_withDensity_iff (measurable_betaPDFReal a b).ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hpdf
  by_contra hx
  apply hpdf
  rw [betaPDFReal, if_neg, ENNReal.ofReal_zero]
  simpa only [mem_Ioo] using hx

private theorem ae_pos_gammaMeasure (a r : ℝ) :
    ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [gammaMeasure]
  refine (ae_withDensity_iff (measurable_gammaPDFReal a r).ennreal_ofReal).2 ?_
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with x hx0
  intro hpdf
  by_contra hx
  apply hpdf
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
  rw [gammaPDFReal, if_neg (not_le.mpr hxneg), ENNReal.ofReal_zero]

/-- The forward Beta--Gamma change of variables.  The existing density-level
theorem is stated for the inverse map; this corollary records explicitly that
`(X/(X+Y),X+Y)` has the independent Beta--Gamma product law. -/
theorem map_betaGammaCoord_prod_gamma_eq_prod_beta_gamma
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Measure.map betaGammaCoord
        ((gammaMeasure a r).prod (gammaMeasure b r)) =
      (betaMeasure a b).prod (gammaMeasure (a + b) r) := by
  let _ : IsProbabilityMeasure (betaMeasure a b) :=
    isProbabilityMeasureBeta ha hb
  let _ : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hcoord : Measurable betaGammaCoord := by
    change Measurable (fun q : ℝ × ℝ ↦
      (q.1 / (q.1 + q.2), q.1 + q.2))
    fun_prop
  have hinv : Measurable betaGammaCoord.symm := by
    change Measurable (fun p : ℝ × ℝ ↦
      (p.1 * p.2, (1 - p.1) * p.2))
    fun_prop
  rw [← map_betaGammaCoord_symm_prod_beta_gamma ha hb hr]
  rw [Measure.map_map hcoord hinv]
  calc
    Measure.map (betaGammaCoord ∘ betaGammaCoord.symm)
        ((betaMeasure a b).prod (gammaMeasure (a + b) r)) =
        Measure.map id
          ((betaMeasure a b).prod (gammaMeasure (a + b) r)) := by
      apply Measure.map_congr
      have hset : MeasurableSet
          {p : ℝ × ℝ | p ∈ betaGammaCoord.target} :=
        betaGammaCoord.open_target.measurableSet
      have hmem : ∀ᵐ p ∂((betaMeasure a b).prod (gammaMeasure (a + b) r)),
          p ∈ betaGammaCoord.target := by
        rw [Measure.ae_prod_iff_ae_ae hset]
        filter_upwards [ae_mem_Ioo_betaMeasure a b] with u hu
        filter_upwards [ae_pos_gammaMeasure (a + b) r] with s hs
        exact ⟨hu, hs⟩
      filter_upwards [hmem] with p hp
      exact betaGammaCoord.right_inv hp
    _ = (betaMeasure a b).prod (gammaMeasure (a + b) r) :=
      Measure.map_id

/-- The stage statistic retaining both the normalized determinant increment
and the fresh column energy. -/
def nestedNormalizedGramFactorWithNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (past : NestedTuple E n) (x : E) : ℝ × ℝ :=
  (nestedNormalizedGramFactor n past x, ‖x‖ ^ 2)

theorem measurable_uncurry_nestedNormalizedGramFactorWithNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) :
    Measurable
      (Function.uncurry (nestedNormalizedGramFactorWithNorm (E := E) n)) := by
  exact (measurable_uncurry_nestedNormalizedGramFactor n).prodMk (by fun_prop)

/-- Product measure of the normalized Bartlett factor and a full-column
chi-square energy. -/
def gaussianGramBetaGammaFactorMeasure (m n : ℕ) : Measure (ℝ × ℝ) :=
  (gaussianGramSchmidtFactorMeasure m n).prod
    (gammaMeasure ((m : ℝ) / 2) (1 / 2))

instance gaussianGramBetaGammaFactorMeasure_sFinite (m n : ℕ) :
    SFinite (gaussianGramBetaGammaFactorMeasure m n) := by
  unfold gaussianGramBetaGammaFactorMeasure gammaMeasure
  infer_instance

/-- Exact fixed-past joint law.  In particular the normalized Gram increment
is independent of the fresh column norm. -/
theorem map_nestedNormalizedGramFactorWithNorm_stdGaussian_fixedPast
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m n : ℕ) (hdim : finrank ℝ E = m)
    (past : NestedTuple E n)
    (hpast : LinearIndependent ℝ (nestedTupleToFin n past))
    (hnm : n < m) :
    Measure.map (nestedNormalizedGramFactorWithNorm n past)
        (stdGaussian E) = gaussianGramBetaGammaFactorMeasure m n := by
  let v : Fin n → E := nestedTupleToFin n past
  have hnrank : n < finrank ℝ E := by omega
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (Nat.zero_lt_of_lt hnrank)
  have hfull : ∀ᵐ x ∂stdGaussian E,
      LinearIndependent ℝ (Fin.snoc v x) :=
    ae_linearIndependent_snoc_stdGaussian hpast hnrank
  cases n with
  | zero =>
      have hfactor :
          (nestedNormalizedGramFactorWithNorm (E := E) 0 past) =ᵐ[stdGaussian E]
            (fun x ↦ ((1 : ℝ), ‖x‖ ^ 2)) := by
        filter_upwards [hfull] with x hx
        apply Prod.ext
        · rw [nestedNormalizedGramFactorWithNorm,
            nestedNormalizedGramFactor_eq_orthogonalProjection past x hx,
            gramSchmidtPastSpan_snoc_eq_span_range v x]
          have hx0 : x ≠ 0 := by
            intro hzero
            apply hx.ne_zero (Fin.last 0)
            subst x
            simpa using
              (@Fin.snoc_last 0 (fun _ : Fin 1 ↦ E) (0 : E) v)
          simp [v]
          rw [Submodule.starProjection_top]
          exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0))
        · rfl
      have hnorm : Measure.map (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E) =
          gammaMeasure ((m : ℝ) / 2) (1 / 2) := by
        have h := (hasLaw_normSq_stdGaussian E).map_eq
        rw [stdGaussianNormSqMeasure_eq_gamma E] at h
        simpa [hdim] using h
      calc
        Measure.map (nestedNormalizedGramFactorWithNorm 0 past)
            (stdGaussian E) =
            Measure.map (fun x : E ↦ ((1 : ℝ), ‖x‖ ^ 2))
              (stdGaussian E) := Measure.map_congr hfactor
        _ = Measure.map (fun s : ℝ ↦ ((1 : ℝ), s))
              (Measure.map (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E)) := by
            exact (Measure.map_map (by fun_prop) (by fun_prop)).symm
        _ = Measure.map (fun s : ℝ ↦ ((1 : ℝ), s))
              (gammaMeasure ((m : ℝ) / 2) (1 / 2)) := by rw [hnorm]
        _ = (Measure.dirac 1).prod
              (gammaMeasure ((m : ℝ) / 2) (1 / 2)) := by
            let _ : IsProbabilityMeasure
                (gammaMeasure ((m : ℝ) / 2) (1 / 2)) :=
              isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
            exact (Measure.dirac_prod (1 : ℝ)).symm
        _ = gaussianGramBetaGammaFactorMeasure m 0 := rfl
  | succ k =>
      let S : Submodule ℝ E := Submodule.span ℝ (Set.range v)
      have hfinS : finrank ℝ S = k + 1 := by
        simpa [S, v] using finrank_span_eq_card hpast
      have hfinPerp : finrank ℝ (Sᗮ) = m - (k + 1) := by
        have hadd := S.finrank_add_finrank_orthogonal
        rw [hfinS, hdim] at hadd
        omega
      let _ : Nontrivial S :=
        Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ S)
      let _ : Nontrivial (Sᗮ) :=
        Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ (Sᗮ))
      let _ : Nontrivial ((Sᗮ)ᗮ) := by
        rw [S.orthogonal_orthogonal]
        infer_instance
      have hjoint := hasLaw_normSq_orthogonalProjections_prod_gamma (K := Sᗮ)
      have hfinDouble : finrank ℝ ((Sᗮ)ᗮ) = k + 1 := by
        rw [S.orthogonal_orthogonal, hfinS]
      rw [hfinPerp, hfinDouble] at hjoint
      have hsub : 0 < m - (k + 1) := by omega
      have hres : 0 < (((m - (k + 1) : ℕ) : ℝ) / 2) := by
        positivity
      have hmap := map_betaGammaCoord_prod_gamma_eq_prod_beta_gamma
        (a := (((m - (k + 1) : ℕ) : ℝ) / 2))
        (b := (((k + 1 : ℕ) : ℝ) / 2))
        (r := (1 / 2 : ℝ))
        hres (by positivity) (by norm_num)
      have hratioNorm : HasLaw
          (fun x : E ↦
            (‖(Sᗮ).orthogonalProjectionOnto x‖ ^ 2 / ‖x‖ ^ 2,
              ‖x‖ ^ 2))
          ((betaMeasure (((m - (k + 1) : ℕ) : ℝ) / 2)
              (((k + 1 : ℕ) : ℝ) / 2)).prod
            (gammaMeasure ((m : ℝ) / 2) (1 / 2)))
          (stdGaussian E) := by
        have hbase : HasLaw betaGammaCoord
            ((betaMeasure (((m - (k + 1) : ℕ) : ℝ) / 2)
                (((k + 1 : ℕ) : ℝ) / 2)).prod
              (gammaMeasure
                ((((m - (k + 1) : ℕ) : ℝ) / 2) +
                  (((k + 1 : ℕ) : ℝ) / 2)) (1 / 2)))
            ((gammaMeasure (((m - (k + 1) : ℕ) : ℝ) / 2) (1 / 2)).prod
              (gammaMeasure (((k + 1 : ℕ) : ℝ) / 2) (1 / 2))) :=
          { aemeasurable :=
              (show Measurable betaGammaCoord by
                change Measurable (fun q : ℝ × ℝ ↦
                  (q.1 / (q.1 + q.2), q.1 + q.2)); fun_prop).aemeasurable
            map_eq := hmap }
        have hcomp := hbase.fun_comp hjoint
        have hfun :
            betaGammaCoord ∘
                (fun x : E ↦
                  (‖(Sᗮ).orthogonalProjectionOnto x‖ ^ 2,
                    ‖((Sᗮ)ᗮ).orthogonalProjectionOnto x‖ ^ 2)) =
              (fun x : E ↦
                (‖(Sᗮ).orthogonalProjectionOnto x‖ ^ 2 / ‖x‖ ^ 2,
                  ‖x‖ ^ 2)) := by
          funext x
          rw [Function.comp_apply, betaGammaCoord_apply,
            normSq_eq_projection_add_orthogonalComplement (Sᗮ) x]
        change HasLaw
          (betaGammaCoord ∘
            (fun x : E ↦
              (‖(Sᗮ).orthogonalProjectionOnto x‖ ^ 2,
                ‖((Sᗮ)ᗮ).orthogonalProjectionOnto x‖ ^ 2))) _ _ at hcomp
        rw [hfun] at hcomp
        have hshape :
            (((m - (k + 1) : ℕ) : ℝ) / 2) +
                (((k + 1 : ℕ) : ℝ) / 2) = (m : ℝ) / 2 := by
          rw [Nat.cast_sub (by omega : k + 1 ≤ m)]
          push_cast
          ring
        rw [hshape] at hcomp
        exact hcomp
      have heq :
          (nestedNormalizedGramFactorWithNorm (E := E) (k + 1) past) =ᵐ[
            stdGaussian E]
          (fun x : E ↦
            (‖(Sᗮ).orthogonalProjectionOnto x‖ ^ 2 / ‖x‖ ^ 2,
              ‖x‖ ^ 2)) := by
        filter_upwards [hfull] with x hx
        apply Prod.ext
        · rw [nestedNormalizedGramFactorWithNorm,
            nestedNormalizedGramFactor_eq_orthogonalProjection past x hx,
            gramSchmidtPastSpan_snoc_eq_span_range v x]
        · rfl
      calc
        Measure.map (nestedNormalizedGramFactorWithNorm (k + 1) past)
            (stdGaussian E) =
            Measure.map
              (fun x : E ↦
                (‖(Sᗮ).orthogonalProjectionOnto x‖ ^ 2 / ‖x‖ ^ 2,
                  ‖x‖ ^ 2))
              (stdGaussian E) := Measure.map_congr heq
        _ = (betaMeasure (((m - (k + 1) : ℕ) : ℝ) / 2)
              (((k + 1 : ℕ) : ℝ) / 2)).prod
            (gammaMeasure ((m : ℝ) / 2) (1 / 2)) := hratioNorm.map_eq
        _ = gaussianGramBetaGammaFactorMeasure m (k + 1) := rfl

/-- The whole sequence of normalized determinant factors and column energies
has the independent product law. -/
theorem map_sequentialNormalizedGramFactorWithNorm_eq_betaGammaProduct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m p : ℕ) (hdim : finrank ℝ E = m) (hp : p ≤ m) :
    Measure.map
        (sequentialStatistic
          (nestedNormalizedGramFactorWithNorm (E := E)) p)
        (nestedProductMeasure (stdGaussian E) p) =
      nestedProductMeasureFamily
        (gaussianGramBetaGammaFactorMeasure m) p := by
  apply map_sequentialStatistic_eq_nestedProduct_of_lt
    (stdGaussian E) (gaussianGramBetaGammaFactorMeasure m)
    (nestedNormalizedGramFactorWithNorm (E := E))
    measurable_uncurry_nestedNormalizedGramFactorWithNorm p
  intro n hnp
  have hnm : n < m := lt_of_lt_of_le hnp hp
  have hnrank : n ≤ finrank ℝ E := by omega
  filter_upwards [ae_linearIndependent_nested_stdGaussian n hnrank] with past hpast
  exact map_nestedNormalizedGramFactorWithNorm_stdGaussian_fixedPast
    m n hdim past hpast hnm

end

end LogdetLean
