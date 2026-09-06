import LogdetLean.Coherence.CanonicalEdgeDecoratedOrthogonalInvariant
import LogdetLean.Coherence.OneEdgeLogPrefixBounds
import LogdetLean.Coherence.ThresholdReplacement
import LogdetLean.Coherence.PrefixTailDeterminantDecomposition
import LogdetLean.Coherence.ProvedLogdetBerryEsseenEnvelope
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
/-!
# Canonical one-edge mark replacement

This module turns the exact canonical-prefix/decorated-tail independence and
the finite one-edge beta integrals into the two mark-replacement estimates
used by the marked Poisson--void argument.

The first part is model independent.  It records an unweighted and a
prefix-event-weighted threshold-replacement inequality for an independent
additive perturbation.  The second part identifies the two-column Gaussian
prefix with the centered log of one beta correlation factor.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set Module
open scoped ProbabilityTheory

/-! ## Integrating threshold replacement under independence -/

/-- A prefix weight and additive prefix shift can be integrated against an
independent real tail.  The hypotheses `hw0` and `hw1` are tailored to a
Bernoulli event indicator; they also make every integrability obligation
automatic. -/
theorem integral_weighted_abs_lowerThresholdIndicator_add_sub_le_of_indep
    {Omega U : Type*} [MeasurableSpace Omega] [MeasurableSpace U]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Ustat : Omega → U) (X : Omega → ℝ)
    (r w : U → ℝ) (z c d : ℝ)
    (hU : Measurable Ustat) (hX : Measurable X)
    (hr : Measurable r) (hw : Measurable w)
    (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∀ u, w u ≤ 1)
    (hrInt : Integrable (fun omega ↦ |r (Ustat omega)|) P)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hindep : IndepFun Ustat X P)
    (hinterval : ∀ (a h : ℝ), 0 ≤ h →
      (Measure.map X P).real (Ioc a (a + h)) ≤ c * h + d) :
    (∫ omega, w (Ustat omega) *
        |lowerThresholdIndicator z (X omega + r (Ustat omega)) -
          lowerThresholdIndicator z (X omega)| ∂P) ≤
      c * (∫ omega, w (Ustat omega) * |r (Ustat omega)| ∂P) +
        d * (∫ omega, w (Ustat omega) ∂P) := by
  let muU : Measure U := Measure.map Ustat P
  let muX : Measure ℝ := Measure.map X P
  let D : U × ℝ → ℝ := fun ux ↦
    w ux.1 * |lowerThresholdIndicator z (ux.2 + r ux.1) -
      lowerThresholdIndicator z ux.2|
  let G : U → ℝ := fun u ↦ w u * (c * |r u| + d)
  letI : IsProbabilityMeasure muU :=
    Measure.isProbabilityMeasure_map hU.aemeasurable
  letI : IsProbabilityMeasure muX :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hDmeas : Measurable D := by
    dsimp [D]
    exact (hw.comp measurable_fst).mul <|
      (((measurable_lowerThresholdIndicator z).comp
        (measurable_snd.add (hr.comp measurable_fst))).sub
          ((measurable_lowerThresholdIndicator z).comp measurable_snd)).abs
  have hDle : ∀ ux, |D ux| ≤ 1 := by
    rintro ⟨u, y⟩
    dsimp [D]
    rw [abs_mul, abs_of_nonneg (hw0 u), abs_abs]
    have hdiff :
        |lowerThresholdIndicator z (y + r u) -
          lowerThresholdIndicator z y| ≤ 1 := by
      unfold lowerThresholdIndicator
      split_ifs <;> norm_num
    calc
      w u * |lowerThresholdIndicator z (y + r u) -
          lowerThresholdIndicator z y| ≤ 1 * 1 :=
        mul_le_mul (hw1 u) hdiff (abs_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hDintProd : Integrable D (muU.prod muX) := by
    exact Integrable.of_bound hDmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hDle)
  have hGmeas : Measurable G := by
    dsimp [G]
    exact hw.mul (measurable_const.mul hr.abs |>.add measurable_const)
  have hGint : Integrable G muU := by
    have hrInt : Integrable (fun u ↦ |r u|) muU := by
      change Integrable (fun u ↦ |r u|) (Measure.map Ustat P)
      rw [integrable_map_measure hr.abs.aestronglyMeasurable hU.aemeasurable]
      simpa [Function.comp_def] using hrInt
    have hbase : Integrable (fun u ↦ c * |r u| + d) muU :=
      (hrInt.const_mul c).add (integrable_const d)
    exact hbase.mono' hGmeas.aestronglyMeasurable <| by
      filter_upwards with u
      have hnonneg : 0 ≤ c * |r u| + d :=
        add_nonneg (mul_nonneg hc (abs_nonneg _)) hd
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 u),
        abs_of_nonneg hnonneg]
      exact mul_le_of_le_one_left hnonneg (hw1 u)
  have hinner : ∀ u,
      (∫ y, D (u, y) ∂muX) ≤ G u := by
    intro u
    have hrep := integral_abs_lowerThresholdIndicator_add_sub_le
      muX hc hd (by simpa [muX] using hinterval) z (r u)
    have hwge := hw0 u
    dsimp [D, G]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hrep hwge
  have hpair : Measurable (fun omega ↦ (Ustat omega, X omega)) :=
    hU.prodMk hX
  have hDintMap : Integrable D
      (Measure.map (fun omega ↦ (Ustat omega, X omega)) P) := by
    rw [hindep.map_prod_eq_prod_map_map hU.aemeasurable hX.aemeasurable]
    exact hDintProd
  have hprodLe : (∫ ux, D ux ∂(muU.prod muX)) ≤ ∫ u, G u ∂muU := by
    rw [MeasureTheory.integral_prod _ hDintProd]
    apply integral_mono_ae hDintProd.integral_prod_left hGint
    filter_upwards with u
    exact hinner u
  calc
    (∫ omega, w (Ustat omega) *
        |lowerThresholdIndicator z (X omega + r (Ustat omega)) -
          lowerThresholdIndicator z (X omega)| ∂P) =
        ∫ ux, D ux
          ∂Measure.map (fun omega ↦ (Ustat omega, X omega)) P := by
      rw [integral_map hpair.aemeasurable hDintMap.aestronglyMeasurable]
    _ = ∫ ux, D ux ∂(muU.prod muX) := by
      rw [hindep.map_prod_eq_prod_map_map hU.aemeasurable hX.aemeasurable]
    _ ≤ ∫ u, G u ∂muU := hprodLe
    _ = ∫ omega, G (Ustat omega) ∂P := by
      change (∫ u, G u ∂Measure.map Ustat P) = _
      rw [integral_map hU.aemeasurable hGint.aestronglyMeasurable]
    _ = c * (∫ omega, w (Ustat omega) * |r (Ustat omega)| ∂P) +
        d * (∫ omega, w (Ustat omega) ∂P) := by
      dsimp [G]
      have hwComp : Integrable (fun omega ↦ w (Ustat omega)) P :=
        Integrable.of_bound (hw.comp hU).aestronglyMeasurable 1 <|
          Filter.Eventually.of_forall fun omega ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
            exact hw1 _
      have hwrComp : Integrable
          (fun omega ↦ w (Ustat omega) * |r (Ustat omega)|) P := by
        exact hrInt.mono'
          ((hw.comp hU).mul ((hr.abs).comp hU)).aestronglyMeasurable <| by
            filter_upwards with omega
            rw [Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (hw0 _), abs_abs]
            exact mul_le_of_le_one_left (abs_nonneg _) (hw1 _)
      rw [show (fun omega ↦
          w (Ustat omega) * (c * |r (Ustat omega)| + d)) =
          fun omega ↦
            c * (w (Ustat omega) * |r (Ustat omega)|) +
              d * w (Ustat omega) by
        funext omega
        ring]
      rw [integral_add (hwrComp.const_mul c) (hwComp.const_mul d),
        integral_const_mul, integral_const_mul]

/-! ## Concentration of an independent deleted tail -/

/-- If `T = R + X`, the prefix `R` is independent of the deleted tail `X`,
and the full statistic `T` is within Kolmogorov distance `B` of the standard
normal, then `X` inherits a linear interval-concentration bound.  The proof
uses the event `|R| < 2 E|R|`, which has probability at least one half by
Markov's inequality, and independence.  Thus no high-probability truncation
parameter and no circular comparison of the two CDFs is needed. -/
theorem map_measureReal_Ioc_le_of_independent_sum_L1
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (R X T : Omega → ℝ)
    (hR : Measurable R) (hX : Measurable X) (hT : Measurable T)
    (hRInt : Integrable (fun omega ↦ |R omega|) P)
    (hindep : IndepFun R X P)
    (hsum : T =ᵐ[P] fun omega ↦ R omega + X omega)
    {B a h : ℝ} (hh : 0 ≤ h)
    (hK : kolmogorovDistance (Measure.map T P) (gaussianReal 0 1) ≤ B) :
    (Measure.map X P).real (Ioc a (a + h)) ≤
      2 * (h + 4 * (∫ omega, |R omega| ∂P)) /
          Real.sqrt (2 * Real.pi) + 4 * B := by
  let e : ℝ := ∫ omega, |R omega| ∂P
  have he0 : 0 ≤ e := integral_nonneg fun _ ↦ abs_nonneg _
  have hB0 : 0 ≤ B :=
    (kolmogorovDistance_nonneg _ _).trans hK
  let S : Omega → ℝ := fun omega ↦ R omega + X omega
  have hS : Measurable S := hR.add hX
  have hmapST : Measure.map S P = Measure.map T P := by
    exact Measure.map_congr hsum.symm
  let muX : Measure ℝ := Measure.map X P
  let muS : Measure ℝ := Measure.map S P
  letI : IsProbabilityMeasure muX :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure muS :=
    Measure.isProbabilityMeasure_map hS.aemeasurable
  by_cases he : e = 0
  · have hRzeroAbs : (fun omega ↦ |R omega|) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
        hRInt).mp he
    have hRzero : R =ᵐ[P] 0 := by
      filter_upwards [hRzeroAbs] with omega homega
      simpa using (abs_eq_zero.mp homega)
    have hSX : S =ᵐ[P] X := by
      filter_upwards [hRzero] with omega homega
      simp [S, homega]
    have hmapSX : muS = muX := by
      exact Measure.map_congr hSX
    have hKX : kolmogorovDistance muX (gaussianReal 0 1) ≤ B := by
      rw [← hmapSX]
      change kolmogorovDistance (Measure.map S P) (gaussianReal 0 1) ≤ B
      rw [hmapST]
      exact hK
    have hinterval := measureReal_Ioc_le_length_add_two_kolmogorov
      muX hh (a := a)
    change muX.real (Ioc a (a + h)) ≤ _
    calc
      muX.real (Ioc a (a + h)) ≤
          h / Real.sqrt (2 * Real.pi) +
            2 * kolmogorovDistance muX (gaussianReal 0 1) := hinterval
      _ ≤ h / Real.sqrt (2 * Real.pi) + 2 * B := by
        gcongr
      _ ≤ 2 * (h + 4 * e) / Real.sqrt (2 * Real.pi) + 4 * B := by
        rw [he]
        have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
        have hfrac : 0 ≤ h / Real.sqrt (2 * Real.pi) :=
          div_nonneg hh hsqrt.le
        have hrearrange :
            2 * (h + 4 * 0) / Real.sqrt (2 * Real.pi) + 4 * B =
              2 * (h / Real.sqrt (2 * Real.pi)) + 4 * B := by ring
        rw [hrearrange]
        nlinarith
  · have hepos : 0 < e := lt_of_le_of_ne he0 (Ne.symm he)
    let K : Set ℝ := {y | |y| < 2 * e}
    let C : Set Omega := R ⁻¹' K
    let A : Set Omega := X ⁻¹' Ioc a (a + h)
    let J : Set ℝ := Ioc (a - 2 * e) (a + h + 2 * e)
    have hKset : MeasurableSet K := by
      exact measurableSet_Iio.preimage measurable_id.abs
    have hC : MeasurableSet C := hKset.preimage hR
    have hA : MeasurableSet A := measurableSet_Ioc.preimage hX
    have hJ : MeasurableSet J := measurableSet_Ioc
    have hCcompl : Cᶜ = {omega | 2 * e ≤ |R omega|} := by
      ext omega
      simp [C, K]
    have hmarkov :
        2 * e * P.real {omega | 2 * e ≤ |R omega|} ≤ e := by
      simpa [e] using mul_meas_ge_le_integral_of_nonneg
        (μ := P) (f := fun omega ↦ |R omega|)
        (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
        hRInt (2 * e)
    have hbadHalf : P.real {omega | 2 * e ≤ |R omega|} ≤ 1 / 2 := by
      have := hmarkov
      nlinarith
    have hChalf : 1 / 2 ≤ P.real C := by
      have hcompl := probReal_compl_eq_one_sub hC (μ := P)
      rw [hCcompl] at hcompl
      linarith
    have hindepReal : P.real (C ∩ A) = P.real C * P.real A := by
      have hmeasure := hindep.measure_inter_preimage_eq_mul
        K (Ioc a (a + h)) hKset measurableSet_Ioc
      change P (C ∩ A) = P C * P A at hmeasure
      rw [measureReal_def, measureReal_def, measureReal_def]
      rw [hmeasure, ENNReal.toReal_mul]
      all_goals finiteness
    have hsubset : C ∩ A ⊆ S ⁻¹' J := by
      intro omega homega
      rcases homega with ⟨hco, hao⟩
      change a - 2 * e < S omega ∧ S omega ≤ a + h + 2 * e
      change |R omega| < 2 * e at hco
      have hcoRaw := abs_lt.mp hco
      have hco' : -2 * e < R omega ∧ R omega < 2 * e := by
        constructor <;> linarith [hcoRaw.1, hcoRaw.2]
      change a < X omega ∧ X omega ≤ a + h at hao
      dsimp [S]
      constructor <;> linarith [hco'.1, hco'.2]
    have hmono : P.real (C ∩ A) ≤ P.real (S ⁻¹' J) :=
      measureReal_mono hsubset
    have hmapApply : P.real (S ⁻¹' J) = muS.real J := by
      dsimp [muS]
      rw [map_measureReal_apply hS hJ]
    have hAmap : P.real A = muX.real (Ioc a (a + h)) := by
      dsimp [muX]
      rw [map_measureReal_apply hX measurableSet_Ioc]
    have hmassHalf :
        (1 / 2 : ℝ) * muX.real (Ioc a (a + h)) ≤ muS.real J := by
      have hmass0 : 0 ≤ muX.real (Ioc a (a + h)) := measureReal_nonneg
      calc
        (1 / 2 : ℝ) * muX.real (Ioc a (a + h)) ≤
            P.real C * P.real A := by
          rw [hAmap]
          exact mul_le_mul_of_nonneg_right hChalf hmass0
        _ = P.real (C ∩ A) := hindepReal.symm
        _ ≤ P.real (S ⁻¹' J) := hmono
        _ = muS.real J := hmapApply
    have hlen : J = Ioc (a - 2 * e) ((a - 2 * e) + (h + 4 * e)) := by
      ext y
      simp only [J, mem_Ioc]
      constructor <;> rintro ⟨hleft, hright⟩ <;>
        constructor <;> linarith
    have hhe : 0 ≤ h + 4 * e := by positivity
    have hinterval := measureReal_Ioc_le_length_add_two_kolmogorov
      muS hhe (a := a - 2 * e)
    have hKS : kolmogorovDistance muS (gaussianReal 0 1) ≤ B := by
      change kolmogorovDistance (Measure.map S P) (gaussianReal 0 1) ≤ B
      rw [hmapST]
      exact hK
    have hupper : muS.real J ≤
        (h + 4 * e) / Real.sqrt (2 * Real.pi) + 2 * B := by
      rw [hlen]
      exact hinterval.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left hKS (by norm_num)) _)
    change muX.real (Ioc a (a + h)) ≤ _
    have := hmassHalf.trans hupper
    have hrearrange :
        2 * (h + 4 * e) / Real.sqrt (2 * Real.pi) + 4 * B =
          2 * ((h + 4 * e) / Real.sqrt (2 * Real.pi) + 2 * B) := by
      ring
    rw [hrearrange]
    nlinarith

/-! ## The actual two-column Gaussian prefix -/

/-- For two nonzero vectors, the normalized-Gram determinant is one minus
their squared normalized inner product. -/
theorem nestedNormalizedGramDet_two_eq_one_sub_squaredNormalizedInner
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : NestedTuple E 2)
    (hzero : nestedTupleToFin 2 w 0 ≠ 0)
    (hone : nestedTupleToFin 2 w 1 ≠ 0) :
    nestedNormalizedGramDet 2 w =
      1 - squaredNormalizedInner
        (nestedTupleToFin 2 w 0) (nestedTupleToFin 2 w 1) := by
  let v : Fin 2 → E := nestedTupleToFin 2 w
  have hdiag0 : normalizedGram v 0 0 = 1 :=
    normalizedGram_apply_self v 0 hzero
  have hdiag1 : normalizedGram v 1 1 = 1 :=
    normalizedGram_apply_self v 1 hone
  have hn0 : ‖v 0‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  have hn1 : ‖v 1‖ ≠ 0 := norm_ne_zero_iff.mpr hone
  have hoff01 : normalizedGram v 0 1 =
      inner ℝ (v 0) (v 1) / (‖v 0‖ * ‖v 1‖) := by
    unfold normalizedGram normalizeVector
    simp only [Matrix.gram_apply, real_inner_smul_left,
      real_inner_smul_right, RCLike.ofReal_real_eq_id, id_eq]
    field_simp
  have hoff10 : normalizedGram v 1 0 =
      inner ℝ (v 0) (v 1) / (‖v 0‖ * ‖v 1‖) := by
    unfold normalizedGram normalizeVector
    simp only [Matrix.gram_apply, real_inner_smul_left,
      real_inner_smul_right, RCLike.ofReal_real_eq_id, id_eq]
    rw [real_inner_comm]
    field_simp
  unfold nestedNormalizedGramDet squaredNormalizedInner
  change (normalizedGram v).det = _
  rw [Matrix.det_fin_two, hdiag0, hdiag1, hoff01, hoff10]
  field_simp [hn0, hn1]
  ring

/-- Forget the initial lifted unit coordinate in a right-nested two-tuple. -/
def nestedTupleTwoToPair {E : Type} (w : NestedTuple E 2) : E × E :=
  (nestedTupleToFin 2 w 0, nestedTupleToFin 2 w 1)

theorem measurable_nestedTupleTwoToPair
    {E : Type} [MeasurableSpace E] :
    Measurable (nestedTupleTwoToPair (E := E)) := by
  exact ((measurable_pi_apply 0).comp (measurable_nestedTupleToFin 2)).prodMk
    ((measurable_pi_apply 1).comp (measurable_nestedTupleToFin 2))

/-- The two genuine coordinates of an iid right-nested two-tuple have the
ordinary product law. -/
theorem map_nestedTupleTwoToPair_nestedProductMeasure
    {E : Type} [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] :
    Measure.map nestedTupleTwoToPair (nestedProductMeasure mu 2) =
      mu.prod mu := by
  letI : IsProbabilityMeasure (nestedProductMeasure mu 1) :=
    nestedProductMeasure_isProbability mu 1
  change Measure.map
      (Prod.map (fun w : NestedTuple E 1 ↦ w.2) id)
      ((nestedProductMeasure mu 1).prod mu) = mu.prod mu
  rw [← Measure.map_prod_map _ _ measurable_snd measurable_id]
  change (Measure.map Prod.snd ((Measure.dirac (ULift.up Unit.unit)).prod mu)).prod
      (Measure.map id mu) = mu.prod mu
  rw [Measure.map_snd_prod, Measure.map_id]
  simp

/-- Integrating a measurable function of the two actual coordinates of a
right-nested two-tuple is the same as integrating under the product law. -/
theorem integral_nestedTuple_two_eq_integral_prod
    {E : Type} [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu]
    (g : E × E → ℝ) (hg : StronglyMeasurable g) :
    (∫ w : NestedTuple E 2,
        g (nestedTupleTwoToPair w)
        ∂nestedProductMeasure mu 2) =
      ∫ z : E × E, g z ∂(mu.prod mu) := by
  rw [← map_nestedTupleTwoToPair_nestedProductMeasure mu]
  exact (integral_map measurable_nestedTupleTwoToPair.aemeasurable
    hg.aestronglyMeasurable).symm

/-- Squared Pearson correlation carried by a raw two-column prefix. -/
def canonicalPrefixSquaredPearson (m : ℕ)
    (pref : NestedTuple (ObservationSpace (m + 1)) 2) : ℝ :=
  squaredCenteredPearson (m + 1) (nestedTupleTwoToPair pref)

theorem measurable_canonicalPrefixSquaredPearson (m : ℕ) :
    Measurable (canonicalPrefixSquaredPearson m) :=
  (measurable_squaredCenteredPearson (m + 1)).comp
    measurable_nestedTupleTwoToPair

/-- On the almost-sure nonsingular set, the two-column centered sample
correlation determinant is `1-r^2`. -/
theorem ae_log_centeredSampleCorrelationDet_two_eq_neg_oneEdgeLogLoss
    {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ pref ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) 2,
      Real.log (centeredSampleCorrelationDet (m + 1) 2 pref) =
        -oneEdgeLogLoss (canonicalPrefixSquaredPearson m pref) := by
  have hLI := ae_linearIndependent_centerNested (m := m) (p := 2) hm
  filter_upwards [hLI] with pref hpref
  have hzero : nestedTupleToFin 2
      (centerNested (m + 1) 2 pref) 0 ≠ 0 := hpref.ne_zero 0
  have hone : nestedTupleToFin 2
      (centerNested (m + 1) 2 pref) 1 ≠ 0 := hpref.ne_zero 1
  rw [centeredSampleCorrelationDet_eq_nestedCenteredNormalizedGramDet
    (Nat.zero_lt_succ m)]
  unfold nestedCenteredNormalizedGramDet
  rw [nestedNormalizedGramDet_two_eq_one_sub_squaredNormalizedInner
    (centerNested (m + 1) 2 pref) hzero hone]
  have hcorr : squaredNormalizedInner
      (nestedTupleToFin 2 (centerNested (m + 1) 2 pref) 0)
      (nestedTupleToFin 2 (centerNested (m + 1) 2 pref) 1) =
      canonicalPrefixSquaredPearson m pref := by
    rcases pref with ⟨⟨u0, u⟩, v⟩
    rfl
  rw [hcorr]
  unfold oneEdgeLogLoss
  ring

/-- The beta centering used in `oneEdgeCenteredPrefix` is exactly the
negative of the `p=2` null log-determinant center. -/
theorem oneEdgeLogMean_half_sub_half_eq_neg_nullCenter_two
    {m : ℕ} (hm : 2 ≤ m) :
    oneEdgeLogMean (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) =
      -nullCenter m 2 := by
  let mu := stdGaussian (ObservationSpace (m + 1))
  let lossPair : ObservationSpace (m + 1) ×
      ObservationSpace (m + 1) → ℝ := fun z ↦
    oneEdgeLogLoss (squaredCenteredPearson (m + 1) z)
  have hloss : StronglyMeasurable oneEdgeLogLoss := by
    unfold oneEdgeLogLoss
    exact ((Real.measurable_log.comp
      (measurable_const.sub measurable_id)).neg).stronglyMeasurable
  have hlossPair : StronglyMeasurable lossPair := by
    exact hloss.comp_measurable
      (measurable_squaredCenteredPearson (m + 1))
  have htransport :
      (∫ pref : NestedTuple (ObservationSpace (m + 1)) 2,
          oneEdgeLogLoss (canonicalPrefixSquaredPearson m pref)
          ∂nestedProductMeasure mu 2) =
        oneEdgeLogMean (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
    calc
      (∫ pref : NestedTuple (ObservationSpace (m + 1)) 2,
          oneEdgeLogLoss (canonicalPrefixSquaredPearson m pref)
          ∂nestedProductMeasure mu 2) =
          ∫ z, lossPair z ∂(mu.prod mu) := by
        exact integral_nestedTuple_two_eq_integral_prod mu lossPair hlossPair
      _ = ∫ y, oneEdgeLogLoss y
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
        exact integral_comp_squaredCenteredPearson_rawGaussian_eq_beta
          m hm oneEdgeLogLoss hloss
      _ = oneEdgeLogMean (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := rfl
  have hdetMean :=
    integral_log_centeredSampleCorrelationDet_eq_nullCenterDigammaSeries
      m 2 hm
  have hcenter := nullCenter_eq_nullCenterDigammaSeries (m := m) (p := 2) hm
  have hae := ae_log_centeredSampleCorrelationDet_two_eq_neg_oneEdgeLogLoss hm
  have hint := integral_congr_ae hae
  change (∫ pref : NestedTuple (ObservationSpace (m + 1)) 2,
      Real.log (centeredSampleCorrelationDet (m + 1) 2 pref)
      ∂nestedProductMeasure mu 2) = _ at hint
  rw [integral_neg, htransport] at hint
  rw [← hcenter] at hdetMean
  linarith

/-- Marginal law of a retained prefix of an iid nested tuple. -/
theorem map_nestedTuplePrefix_nestedProductMeasure_eq
    {E : Type} [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] (q r : ℕ) :
    Measure.map (nestedTuplePrefix (E := E) q r)
        (nestedProductMeasure mu (q + r)) =
      nestedProductMeasure mu q := by
  let split := nestedTupleSplit (α := E) q r
  have hsplit : Measurable split := measurable_nestedTupleSplit q r
  have hpref : Measurable (nestedTuplePrefix (E := E) q r) :=
    measurable_nestedTuplePrefix q r
  calc
    Measure.map (nestedTuplePrefix (E := E) q r)
        (nestedProductMeasure mu (q + r)) =
      Measure.map Prod.fst
        (Measure.map split (nestedProductMeasure mu (q + r))) := by
      rw [Measure.map_map measurable_fst hsplit]
      rfl
    _ = Measure.map Prod.fst
        ((nestedProductMeasure mu q).prod
          (nestedProductMeasure mu r)) := by
      rw [map_nestedTupleSplit_nestedProductMeasure mu q r]
    _ = nestedProductMeasure mu q := by
      rw [Measure.map_fst_prod]
      simp

/-- Centering commutes with retaining the first `q` columns. -/
theorem nestedTuplePrefix_centerNested
    (N q : ℕ) : ∀ r
    (data : NestedTuple (ObservationSpace N) (q + r)),
    nestedTuplePrefix q r (centerNested N (q + r) data) =
      centerNested N q (nestedTuplePrefix q r data) := by
  intro r
  induction r with
  | zero => intro data; rfl
  | succ r ih =>
      intro data
      exact ih data.1

/-- The centered canonical log-correlation prefix at the full `p` scale. -/
def canonicalOneEdgePrefixRemainderOnPrefix
    (m p : ℕ) (pref : NestedTuple (ObservationSpace (m + 1)) 2) : ℝ :=
  oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
    (Real.sqrt (nullVSeries m p)) (canonicalPrefixSquaredPearson m pref)

theorem measurable_canonicalOneEdgePrefixRemainderOnPrefix (m p : ℕ) :
    Measurable (canonicalOneEdgePrefixRemainderOnPrefix m p) :=
  (measurable_oneEdgeCenteredPrefix
    (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m p))).comp
        (measurable_canonicalPrefixSquaredPearson m)

/-- The same prefix remainder read from complete `2+r` column data. -/
def canonicalOneEdgePrefixRemainder
    (m r : ℕ)
    (data : NestedTuple (ObservationSpace (m + 1)) (2 + r)) : ℝ :=
  canonicalOneEdgePrefixRemainderOnPrefix m (2 + r)
    (nestedTuplePrefix 2 r data)

theorem measurable_canonicalOneEdgePrefixRemainder (m r : ℕ) :
    Measurable (canonicalOneEdgePrefixRemainder m r) :=
  (measurable_canonicalOneEdgePrefixRemainderOnPrefix m (2 + r)).comp
    (measurable_nestedTuplePrefix 2 r)

/-- The canonical prefix remainder is exactly the prefix term appearing in
the additive log-determinant decomposition, almost surely. -/
theorem ae_canonicalOneEdgePrefixRemainder_eq_standardizedCenteredPrefix
    {m r : ℕ} (hqr : 2 + r ≤ m) :
    ∀ᵐ data ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r),
      canonicalOneEdgePrefixRemainder m r data =
        standardizedCenteredPrefixLogDetAtFullScale m 2 (2 + r)
          (nestedTuplePrefix 2 r
            (centerNested (m + 1) (2 + r) data)) := by
  have hm : 2 ≤ m := le_trans (by omega : 2 ≤ 2 + r) hqr
  have hprefAE :=
    ae_log_centeredSampleCorrelationDet_two_eq_neg_oneEdgeLogLoss hm
  have hmap := map_nestedTuplePrefix_nestedProductMeasure_eq
    (stdGaussian (ObservationSpace (m + 1))) 2 r
  rw [← hmap] at hprefAE
  have hprefMeas : Measurable
      (nestedTuplePrefix (E := ObservationSpace (m + 1)) 2 r) :=
    measurable_nestedTuplePrefix (α := ObservationSpace (m + 1)) 2 r
  have hpulled := ae_of_ae_map hprefMeas.aemeasurable hprefAE
  filter_upwards [hpulled] with data hlog
  unfold canonicalOneEdgePrefixRemainder
    canonicalOneEdgePrefixRemainderOnPrefix
    standardizedCenteredPrefixLogDetAtFullScale
  rw [nullVariance_eq_nullVSeries hqr]
  rw [nestedTuplePrefix_centerNested]
  have hdet : Real.log (nestedNormalizedGramDet 2
      (centerNested (m + 1) 2 (nestedTuplePrefix 2 r data))) =
      -oneEdgeLogLoss
        (canonicalPrefixSquaredPearson m (nestedTuplePrefix 2 r data)) := by
    simpa [centeredSampleCorrelationDet_eq_nestedCenteredNormalizedGramDet
      (Nat.zero_lt_succ m), nestedCenteredNormalizedGramDet] using hlog
  unfold oneEdgeCenteredPrefix
  rw [hdet, oneEdgeLogMean_half_sub_half_eq_neg_nullCenter_two hm]
  ring

/-- Exact additive decomposition using the concrete canonical one-edge
prefix remainder. -/
theorem ae_Z0mpStatistic_eq_canonicalOneEdgePrefix_add_tail
    {m r : ℕ} (hqr : 2 + r ≤ m) :
    ∀ᵐ data ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r),
      Z0mpStatistic m (2 + r) data =
        canonicalOneEdgePrefixRemainder m r data +
          standardizedGaussianRetainedTailStatistic m 2 r data := by
  filter_upwards
      [ae_Z0mpStatistic_eq_prefix_add_standardizedGaussianRetainedTail hqr,
        ae_canonicalOneEdgePrefixRemainder_eq_standardizedCenteredPrefix hqr]
      with data hdecomp hprefix
  rw [hdecomp, hprefix]

/-- Squaring an off-diagonal normalized-Gram entry gives the squared
normalized inner product, including at zero vectors under totalized inverse. -/
theorem normalizedGram_entry_sq_eq_squaredNormalizedInner
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (v : Fin n → E) (i j : Fin n) :
    (normalizedGram v i j) ^ 2 = squaredNormalizedInner (v i) (v j) := by
  unfold normalizedGram normalizeVector squaredNormalizedInner
  simp only [Matrix.gram_apply, real_inner_smul_left,
    real_inner_smul_right, RCLike.ofReal_real_eq_id, id_eq]
  rw [div_eq_mul_inv]
  ring

/-- The canonical two-column score is exactly `m` times the squared Pearson
correlation carried by that prefix. -/
theorem scaledSquaredCorrelationScore_canonicalEdgeInTwo_eq
    (m : ℕ) (pref : NestedTuple (ObservationSpace (m + 1)) 2) :
    scaledSquaredCorrelationScore m 2 pref canonicalEdgeInTwo =
      (m : ℝ) * canonicalPrefixSquaredPearson m pref := by
  unfold scaledSquaredCorrelationScore centeredCorrelationMatrix
    canonicalPrefixSquaredPearson squaredCenteredPearson centerGaussianPair
  rw [normalizedGram_entry_sq_eq_squaredNormalizedInner]
  rcases pref with ⟨⟨u0, u⟩, v⟩
  rfl

/-- The canonical edge indicator is the beta-tail indicator at the divided
threshold `classicalCoherenceThreshold / m`. -/
theorem canonicalEdgeExceedanceIndicatorOnPrefix_eq_Ioi_indicator
    {m r : ℕ} (hm : 0 < m) (x : ℝ)
    (pref : NestedTuple (ObservationSpace (m + 1)) 2) :
    (canonicalEdgeExceedanceIndicatorOnPrefix m r x pref : ℝ) =
      (Ioi (classicalCoherenceThreshold m (2 + r) x / (m : ℝ))).indicator
        (fun _ : ℝ ↦ (1 : ℝ))
        (canonicalPrefixSquaredPearson m pref) := by
  unfold canonicalEdgeExceedanceIndicatorOnPrefix
  rw [scaledSquaredCorrelationScore_canonicalEdgeInTwo_eq]
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  by_cases hcross : classicalCoherenceThreshold m (2 + r) x <
      (m : ℝ) * canonicalPrefixSquaredPearson m pref
  · have htail : classicalCoherenceThreshold m (2 + r) x / (m : ℝ) <
        canonicalPrefixSquaredPearson m pref :=
      (div_lt_iff₀ hmR).2 (by simpa [mul_comm] using hcross)
    simp [hcross, Set.indicator, htail]
  · have htail : ¬classicalCoherenceThreshold m (2 + r) x / (m : ℝ) <
        canonicalPrefixSquaredPearson m pref := by
      intro h
      exact hcross ((div_lt_iff₀ hmR).1 h |>.trans_eq (mul_comm _ _))
    simp [hcross, Set.indicator, htail]

/-- Full-sample form of the canonical beta-tail indicator identity. -/
theorem canonicalEdgeExceedanceIndicator_eq_Ioi_indicator
    {m r : ℕ} (hm : 0 < m) (x : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) (2 + r)) :
    (canonicalEdgeExceedanceIndicator m r x data : ℝ) =
      (Ioi (classicalCoherenceThreshold m (2 + r) x / (m : ℝ))).indicator
        (fun _ : ℝ ↦ (1 : ℝ))
        (canonicalPrefixSquaredPearson m (nestedTuplePrefix 2 r data)) := by
  unfold canonicalEdgeExceedanceIndicator
  exact canonicalEdgeExceedanceIndicatorOnPrefix_eq_Ioi_indicator hm x _

/-- Measurability of the concrete standardized deleted-tail statistic. -/
theorem measurable_standardizedGaussianRetainedTailStatistic
    (m q r : ℕ) :
    Measurable (standardizedGaussianRetainedTailStatistic m q r) := by
  unfold standardizedGaussianRetainedTailStatistic
  exact (measurable_standardizedRetainedTailLogStatistic m q r).comp
    (measurable_centeredRetainedPrefixTailFactors (m + 1) q r)

/-- The mark obtained by deleting the canonical first edge from the
log-determinant statistic. -/
def canonicalOneEdgeLeaveMark (m r : ℕ) (z : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) (2 + r)) : ℝ :=
  lowerThresholdIndicator z
    (standardizedGaussianRetainedTailStatistic m 2 r data)

theorem measurable_canonicalOneEdgeLeaveMark (m r : ℕ) (z : ℝ) :
    Measurable (canonicalOneEdgeLeaveMark m r z) :=
  (measurable_lowerThresholdIndicator z).comp
    (measurable_standardizedGaussianRetainedTailStatistic m 2 r)

theorem abs_canonicalOneEdgeLeaveMark_le_one
    (m r : ℕ) (z : ℝ)
    (data : NestedTuple (ObservationSpace (m + 1)) (2 + r)) :
    |canonicalOneEdgeLeaveMark m r z data| ≤ 1 := by
  unfold canonicalOneEdgeLeaveMark lowerThresholdIndicator
  split_ifs <;> norm_num

/-- The real-valued canonical exceedance indicator is independent of the
deleted-tail mark jointly with the remote exceedance count. -/
theorem canonicalEdgeExceedanceIndicator_indep_leaveMark_remoteCount
    {m r : ℕ} (x z : ℝ) (hqr : 2 + r ≤ m) :
    IndepFun
      (fun data : NestedTuple (ObservationSpace (m + 1)) (2 + r) ↦
        (canonicalEdgeExceedanceIndicator m r x data : ℝ))
      (fun data ↦
        (canonicalOneEdgeLeaveMark m r z data,
          remoteCoherenceExceedanceCountOnFull m r x data))
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) := by
  have h :=
    canonicalEdgeExceedanceIndicator_indep_canonicalDecoratedTail_admissible
      m r x hqr
  have hcast : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
    measurable_of_countable (fun n : ℕ ↦ (n : ℝ))
  have hdecorate : Measurable (fun y : ℝ × ℕ ↦
      (lowerThresholdIndicator z y.1, y.2)) :=
    ((measurable_lowerThresholdIndicator z).comp measurable_fst).prodMk
      measurable_snd
  have hcomp := h.comp hcast hdecorate
  simpa [canonicalDecoratedTail, canonicalOneEdgeLeaveMark,
    Function.comp_def] using hcomp

/-! ## Integrability and finite prefix moments -/

/-- The centered one-edge logarithmic prefix is genuinely integrable under
its beta law.  This is kept separate from the numerical integral bound:
Bochner integrals are totalized, so a finite displayed integral alone would
not certify integrability. -/
theorem integrable_oneEdgeCenteredPrefix_betaMeasure
    {alpha betaShape scale : ℝ}
    (ha : 0 < alpha) (hb : 1 < betaShape) :
    Integrable (oneEdgeCenteredPrefix alpha betaShape scale)
      (betaMeasure alpha betaShape) := by
  letI : IsProbabilityMeasure (betaMeasure alpha betaShape) :=
    isProbabilityMeasureBeta ha (lt_trans zero_lt_one hb)
  unfold oneEdgeCenteredPrefix
  exact ((integrable_const (oneEdgeLogMean alpha betaShape)).sub
    (integrable_oneEdgeLogLoss_betaMeasure ha hb)).div_const scale

/-- Integrability transported to two raw Gaussian sample columns. -/
theorem integrable_oneEdgeCenteredPrefix_rawPearson_nullVSeries
    {m p : ℕ} (hadm : Admissible m p) (hm6 : 6 ≤ m) :
    Integrable
      (fun z : ObservationSpace (m + 1) × ObservationSpace (m + 1) ↦
        oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m p))
          (squaredCenteredPearson (m + 1) z))
      ((stdGaussian (ObservationSpace (m + 1))).prod
        (stdGaussian (ObservationSpace (m + 1)))) := by
  let g : ℝ → ℝ := oneEdgeCenteredPrefix
    (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m p))
  have hsub : (5 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 5 ≤ m - 1 by omega)
  have hb : (1 : ℝ) < ((m - 1 : ℕ) : ℝ) / 2 := by linarith
  have hbeta : Integrable g
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) := by
    exact integrable_oneEdgeCenteredPrefix_betaMeasure
      (by norm_num) hb
  have hmap : Measure.map (squaredCenteredPearson (m + 1))
      ((stdGaussian (ObservationSpace (m + 1))).prod
        (stdGaussian (ObservationSpace (m + 1)))) =
      betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) :=
    map_squaredCenteredPearson_rawGaussianProduct_eq_beta m (by omega)
  have htransport : Integrable g
      (Measure.map (squaredCenteredPearson (m + 1))
        ((stdGaussian (ObservationSpace (m + 1))).prod
          (stdGaussian (ObservationSpace (m + 1))))) := by
    exact hmap.symm ▸ hbeta
  have hcomp := htransport.comp_measurable
    (measurable_squaredCenteredPearson (m + 1))
  simpa [g, Function.comp_def] using hcomp

/-- Integrability of the canonical remainder on the two-column prefix. -/
theorem integrable_canonicalOneEdgePrefixRemainderOnPrefix
    {m r : ℕ} (hadm : Admissible m (2 + r)) (hm6 : 6 ≤ m) :
    Integrable (canonicalOneEdgePrefixRemainderOnPrefix m (2 + r))
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) 2) := by
  let mu := stdGaussian (ObservationSpace (m + 1))
  let g : ObservationSpace (m + 1) × ObservationSpace (m + 1) → ℝ :=
    fun z ↦ oneEdgeCenteredPrefix
      (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m (2 + r)))
      (squaredCenteredPearson (m + 1) z)
  have hraw : Integrable g (mu.prod mu) := by
    simpa [g, mu] using
      (integrable_oneEdgeCenteredPrefix_rawPearson_nullVSeries hadm hm6)
  have htransport : Integrable g
      (Measure.map nestedTupleTwoToPair (nestedProductMeasure mu 2)) := by
    rw [map_nestedTupleTwoToPair_nestedProductMeasure mu]
    exact hraw
  have hcomp := htransport.comp_measurable measurable_nestedTupleTwoToPair
  change Integrable
    (fun pref : NestedTuple (ObservationSpace (m + 1)) 2 ↦
      oneEdgeCenteredPrefix (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
        (Real.sqrt (nullVSeries m (2 + r)))
        (squaredCenteredPearson (m + 1) (nestedTupleTwoToPair pref)))
    (nestedProductMeasure mu 2)
  simpa [g, Function.comp_def] using hcomp

/-- Integrability of the absolute canonical remainder on all `2+r` columns. -/
theorem integrable_abs_canonicalOneEdgePrefixRemainder
    {m r : ℕ} (hadm : Admissible m (2 + r)) (hm6 : 6 ≤ m) :
    Integrable (fun data ↦ |canonicalOneEdgePrefixRemainder m r data|)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) := by
  let mu := stdGaussian (ObservationSpace (m + 1))
  let f : NestedTuple (ObservationSpace (m + 1)) 2 → ℝ :=
    fun pref ↦ |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r) pref|
  have hpref : Integrable f (nestedProductMeasure mu 2) := by
    simpa [f, mu] using
      (integrable_canonicalOneEdgePrefixRemainderOnPrefix hadm hm6).abs
  have htransport : Integrable f
      (Measure.map (nestedTuplePrefix
          (E := ObservationSpace (m + 1)) 2 r)
        (nestedProductMeasure mu (2 + r))) := by
    have hmap := map_nestedTuplePrefix_nestedProductMeasure_eq mu 2 r
    exact hmap.symm ▸ hpref
  have hcomp := htransport.comp_measurable
    (measurable_nestedTuplePrefix 2 r)
  simpa [f, mu, canonicalOneEdgePrefixRemainder, Function.comp_def]
    using hcomp

/-- Concrete unconditional `L¹` estimate for the canonical remainder. -/
theorem integral_abs_canonicalOneEdgePrefixRemainder_le
    {m r : ℕ} (hadm : Admissible m (2 + r)) (hm6 : 6 ≤ m) :
    (∫ data,
      |canonicalOneEdgePrefixRemainder m r data|
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) ≤
      4 / ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r))) := by
  let mu := stdGaussian (ObservationSpace (m + 1))
  let f : ObservationSpace (m + 1) × ObservationSpace (m + 1) → ℝ :=
    fun z ↦ |oneEdgeCenteredPrefix
      (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m (2 + r)))
      (squaredCenteredPearson (m + 1) z)|
  have hprefixMap : Measure.map
      (nestedTuplePrefix (E := ObservationSpace (m + 1)) 2 r)
      (nestedProductMeasure mu (2 + r)) =
        nestedProductMeasure mu 2 :=
    map_nestedTuplePrefix_nestedProductMeasure_eq mu 2 r
  have hprefIntegral :
      (∫ pref : NestedTuple (ObservationSpace (m + 1)) 2,
        |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r) pref|
          ∂nestedProductMeasure mu 2) =
        ∫ z, f z ∂(mu.prod mu) := by
    simpa [f, canonicalOneEdgePrefixRemainderOnPrefix,
      canonicalPrefixSquaredPearson] using
      (integral_nestedTuple_two_eq_integral_prod mu f
        (((measurable_oneEdgeCenteredPrefix
          (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m (2 + r)))).comp
            (measurable_squaredCenteredPearson (m + 1))).abs.stronglyMeasurable))
  have hprefMeas : Measurable
      (fun pref : NestedTuple (ObservationSpace (m + 1)) 2 ↦
        |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r) pref|) :=
    (measurable_canonicalOneEdgePrefixRemainderOnPrefix m (2 + r)).abs
  have hprefStrong : StronglyMeasurable
      (fun pref : NestedTuple (ObservationSpace (m + 1)) 2 ↦
        |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r) pref|) :=
    hprefMeas.stronglyMeasurable
  calc
    (∫ data,
      |canonicalOneEdgePrefixRemainder m r data|
      ∂nestedProductMeasure mu (2 + r)) =
        ∫ pref,
          |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r) pref|
          ∂Measure.map (nestedTuplePrefix 2 r)
            (nestedProductMeasure mu (2 + r)) := by
      exact (integral_map_of_stronglyMeasurable
        (measurable_nestedTuplePrefix 2 r)
        hprefStrong).symm
    _ = ∫ pref,
          |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r) pref|
          ∂nestedProductMeasure mu 2 := by
      rw [hprefixMap]
      rfl
    _ = ∫ z, f z ∂(mu.prod mu) := hprefIntegral
    _ ≤ 4 / ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r))) := by
      simpa [f, mu] using
        (integral_abs_oneEdgeCenteredPrefix_rawPearson_nullVSeries_le
          hadm hm6)

/-- Concrete event-weighted `L¹` estimate.  The event probability remains as
a multiplicative beta tail; in particular, no division by a small edge
probability occurs. -/
theorem
    integral_canonicalEdgeIndicator_mul_abs_prefixRemainder_le_log_rate
    {m r : ℕ} (hadm : Admissible m (2 + r)) (hm6 : 6 ≤ m)
    (x ell : ℝ)
    (ht0 : 0 < classicalCoherenceThreshold m (2 + r) x / (m : ℝ))
    (htHalf : classicalCoherenceThreshold m (2 + r) x / (m : ℝ) ≤ 1 / 2)
    (hell : 1 ≤ ell)
    (htRate : classicalCoherenceThreshold m (2 + r) x / (m : ℝ) ≤
      5 * ell / (m : ℝ)) :
    (∫ data,
      (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
        |canonicalOneEdgePrefixRemainder m r data|
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
          (Ioi (classicalCoherenceThreshold m (2 + r) x / (m : ℝ))) *
        (16 * ell /
          ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r)))) := by
  let mu := stdGaussian (ObservationSpace (m + 1))
  let t := classicalCoherenceThreshold m (2 + r) x / (m : ℝ)
  let F : NestedTuple (ObservationSpace (m + 1)) 2 → ℝ := fun pref ↦
    (canonicalEdgeExceedanceIndicatorOnPrefix m r x pref : ℝ) *
      |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r) pref|
  let g : ObservationSpace (m + 1) × ObservationSpace (m + 1) → ℝ :=
    fun y ↦ (Ioi t).indicator
      (fun s ↦ |oneEdgeCenteredPrefix
        (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
        (Real.sqrt (nullVSeries m (2 + r))) s|)
      (squaredCenteredPearson (m + 1) y)
  have hm : 0 < m := by omega
  have hcast : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
    measurable_of_countable (fun n : ℕ ↦ (n : ℝ))
  have hFmeas : Measurable F := by
    exact (hcast.comp
      (measurable_canonicalEdgeExceedanceIndicatorOnPrefix m r x)).mul
        (measurable_canonicalOneEdgePrefixRemainderOnPrefix m (2 + r)).abs
  have hpoint : ∀ pref, F pref = g (nestedTupleTwoToPair pref) := by
    intro pref
    dsimp [F, g]
    rw [canonicalEdgeExceedanceIndicatorOnPrefix_eq_Ioi_indicator hm x]
    change (Ioi t).indicator (fun _ : ℝ ↦ (1 : ℝ))
        (canonicalPrefixSquaredPearson m pref) *
          |oneEdgeCenteredPrefix
            (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
            (Real.sqrt (nullVSeries m (2 + r)))
            (canonicalPrefixSquaredPearson m pref)| =
      (Ioi t).indicator
        (fun s ↦ |oneEdgeCenteredPrefix
          (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
          (Real.sqrt (nullVSeries m (2 + r))) s|)
        (canonicalPrefixSquaredPearson m pref)
    by_cases hmem : canonicalPrefixSquaredPearson m pref ∈ Ioi t <;>
      simp [Set.indicator, hmem]
  have hg : StronglyMeasurable g := by
    exact (((measurable_oneEdgeCenteredPrefix
      (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)
      (Real.sqrt (nullVSeries m (2 + r)))).abs.stronglyMeasurable).indicator
        measurableSet_Ioi).comp_measurable
          (measurable_squaredCenteredPearson (m + 1))
  have hprefixMap : Measure.map
      (nestedTuplePrefix (E := ObservationSpace (m + 1)) 2 r)
      (nestedProductMeasure mu (2 + r)) =
        nestedProductMeasure mu 2 :=
    map_nestedTuplePrefix_nestedProductMeasure_eq mu 2 r
  calc
    (∫ data,
      (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
        |canonicalOneEdgePrefixRemainder m r data|
      ∂nestedProductMeasure mu (2 + r)) =
        ∫ pref, F pref
          ∂Measure.map (nestedTuplePrefix 2 r)
            (nestedProductMeasure mu (2 + r)) := by
      change (∫ data, F (nestedTuplePrefix 2 r data)
        ∂nestedProductMeasure mu (2 + r)) =
          ∫ pref, F pref
            ∂Measure.map (nestedTuplePrefix 2 r)
              (nestedProductMeasure mu (2 + r))
      exact (integral_map_of_stronglyMeasurable
        (measurable_nestedTuplePrefix 2 r) hFmeas.stronglyMeasurable).symm
    _ = ∫ pref, F pref ∂nestedProductMeasure mu 2 := by
      rw [hprefixMap]
      rfl
    _ = ∫ pref, g (nestedTupleTwoToPair pref)
          ∂nestedProductMeasure mu 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ y, g y ∂(mu.prod mu) :=
      integral_nestedTuple_two_eq_integral_prod mu g hg
    _ ≤ (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
          (Ioi t) *
        (16 * ell /
          ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r)))) := by
      simpa [g, t, mu] using
        (integral_indicator_abs_oneEdgeCenteredPrefix_rawPearson_nullVSeries_le_log_rate
          hadm hm6 ht0 htHalf hell htRate)

/-- Exact mean of the real-valued canonical exceedance indicator. -/
theorem integral_canonicalEdgeExceedanceIndicator_eq_betaTail
    {m r : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    (∫ data,
      (canonicalEdgeExceedanceIndicator m r x data : ℝ)
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) =
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
        (Ioi (classicalCoherenceThreshold m (2 + r) x / (m : ℝ))) := by
  let mu := stdGaussian (ObservationSpace (m + 1))
  let t := classicalCoherenceThreshold m (2 + r) x / (m : ℝ)
  let F : NestedTuple (ObservationSpace (m + 1)) 2 → ℝ := fun pref ↦
    (canonicalEdgeExceedanceIndicatorOnPrefix m r x pref : ℝ)
  let g : ℝ → ℝ := (Ioi t).indicator (fun _ : ℝ ↦ (1 : ℝ))
  have hm0 : 0 < m := by omega
  have hcast : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
    measurable_of_countable (fun n : ℕ ↦ (n : ℝ))
  have hFmeas : Measurable F := hcast.comp
    (measurable_canonicalEdgeExceedanceIndicatorOnPrefix m r x)
  have hg : StronglyMeasurable g :=
    measurable_const.stronglyMeasurable.indicator measurableSet_Ioi
  have hpair : StronglyMeasurable
      (fun y : ObservationSpace (m + 1) × ObservationSpace (m + 1) ↦
        g (squaredCenteredPearson (m + 1) y)) :=
    hg.comp_measurable (measurable_squaredCenteredPearson (m + 1))
  have hpoint : ∀ pref,
      F pref = g (canonicalPrefixSquaredPearson m pref) := by
    intro pref
    exact canonicalEdgeExceedanceIndicatorOnPrefix_eq_Ioi_indicator hm0 x pref
  have hprefixMap : Measure.map
      (nestedTuplePrefix (E := ObservationSpace (m + 1)) 2 r)
      (nestedProductMeasure mu (2 + r)) =
        nestedProductMeasure mu 2 :=
    map_nestedTuplePrefix_nestedProductMeasure_eq mu 2 r
  calc
    (∫ data,
      (canonicalEdgeExceedanceIndicator m r x data : ℝ)
      ∂nestedProductMeasure mu (2 + r)) =
        ∫ pref, F pref
          ∂Measure.map (nestedTuplePrefix 2 r)
            (nestedProductMeasure mu (2 + r)) := by
      change (∫ data, F (nestedTuplePrefix 2 r data)
        ∂nestedProductMeasure mu (2 + r)) =
          ∫ pref, F pref
            ∂Measure.map (nestedTuplePrefix 2 r)
              (nestedProductMeasure mu (2 + r))
      exact (integral_map_of_stronglyMeasurable
        (measurable_nestedTuplePrefix 2 r) hFmeas.stronglyMeasurable).symm
    _ = ∫ pref, F pref ∂nestedProductMeasure mu 2 := by
      rw [hprefixMap]
      rfl
    _ = ∫ pref, g (canonicalPrefixSquaredPearson m pref)
          ∂nestedProductMeasure mu 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ y,
          g (squaredCenteredPearson (m + 1) y) ∂(mu.prod mu) := by
      simpa [canonicalPrefixSquaredPearson] using
        (integral_nestedTuple_two_eq_integral_prod mu
          (fun y ↦ g (squaredCenteredPearson (m + 1) y)) hpair)
    _ = ∫ s, g s
          ∂betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2) := by
      simpa [mu] using
        (integral_comp_squaredCenteredPearson_rawGaussian_eq_beta
          m hm g hg)
    _ = (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
          (Ioi t) := by
      simpa [g] using
        (integral_indicator_one (μ :=
          betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)) measurableSet_Ioi)

/-! ## Deleted-tail independence and anti-concentration -/

/-- The actual first two columns are independent of the standardized retained
tail statistic. -/
theorem nestedTuplePrefix_indep_standardizedGaussianRetainedTailStatistic
    {m r : ℕ} (hqr : 2 + r ≤ m) :
    IndepFun
      (nestedTuplePrefix
        (E := ObservationSpace (m + 1)) 2 r)
      (standardizedGaussianRetainedTailStatistic m 2 r)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) := by
  have h := nestedTuplePrefix_indep_canonicalDecoratedTail m r 0 hqr
  have hcomp := h.comp measurable_id measurable_fst
  simpa [canonicalDecoratedTail, Function.comp_def] using hcomp

/-- Consequently the scalar canonical prefix remainder is independent of the
standardized retained tail. -/
theorem canonicalOneEdgePrefixRemainder_indep_retainedTail
    {m r : ℕ} (hqr : 2 + r ≤ m) :
    IndepFun
      (canonicalOneEdgePrefixRemainder m r)
      (standardizedGaussianRetainedTailStatistic m 2 r)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) := by
  have h := prefixStatistic_indep_canonicalDecoratedTail
    m r 0 hqr
      (canonicalOneEdgePrefixRemainderOnPrefix m (2 + r))
      (measurable_canonicalOneEdgePrefixRemainderOnPrefix m (2 + r))
  have hcomp := h.comp measurable_id measurable_fst
  change IndepFun
    (fun data ↦ canonicalOneEdgePrefixRemainderOnPrefix m (2 + r)
      (nestedTuplePrefix 2 r data))
    (standardizedGaussianRetainedTailStatistic m 2 r)
    (nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) (2 + r))
  simpa [canonicalDecoratedTail, Function.comp_def] using hcomp

/-- Exact inherited interval-concentration bound for the deleted tail, still
showing the true first absolute moment of the deleted prefix. -/
theorem map_retainedTail_measureReal_Ioc_le_with_exact_prefix_moment
    {m r : ℕ} (hadm : Admissible m (2 + r)) (hm6 : 6 ≤ m)
    {a h : ℝ} (hh : 0 ≤ h) :
    (Measure.map (standardizedGaussianRetainedTailStatistic m 2 r)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r))).real
        (Ioc a (a + h)) ≤
      2 * (h + 4 *
        (∫ data, |canonicalOneEdgePrefixRemainder m r data|
          ∂nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) (2 + r))) /
          Real.sqrt (2 * Real.pi) +
        4 * provedNullLogdetKolmogorovEnvelope m (2 + r) := by
  exact map_measureReal_Ioc_le_of_independent_sum_L1
    (nestedProductMeasure
      (stdGaussian (ObservationSpace (m + 1))) (2 + r))
    (canonicalOneEdgePrefixRemainder m r)
    (standardizedGaussianRetainedTailStatistic m 2 r)
    (Z0mpStatistic m (2 + r))
    (measurable_canonicalOneEdgePrefixRemainder m r)
    (measurable_standardizedGaussianRetainedTailStatistic m 2 r)
    (measurable_Z0mpStatistic m (2 + r))
    (integrable_abs_canonicalOneEdgePrefixRemainder hadm hm6)
    (canonicalOneEdgePrefixRemainder_indep_retainedTail hadm.2)
    (ae_Z0mpStatistic_eq_canonicalOneEdgePrefix_add_tail hadm.2)
    hh (kolmogorovDistance_actualZ0mp_le_provedEnvelope hadm)

/-- Explicit inherited anti-concentration after inserting the finite
`4/(m√V)` prefix moment. -/
theorem map_retainedTail_measureReal_Ioc_le
    {m r : ℕ} (hadm : Admissible m (2 + r)) (hm6 : 6 ≤ m)
    {a h : ℝ} (hh : 0 ≤ h) :
    (Measure.map (standardizedGaussianRetainedTailStatistic m 2 r)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r))).real
        (Ioc a (a + h)) ≤
      2 * (h + 16 /
        ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r)))) /
          Real.sqrt (2 * Real.pi) +
        4 * provedNullLogdetKolmogorovEnvelope m (2 + r) := by
  have hbase :=
    map_retainedTail_measureReal_Ioc_le_with_exact_prefix_moment
      hadm hm6 (a := a) (h := h) hh
  have hL1 := integral_abs_canonicalOneEdgePrefixRemainder_le hadm hm6
  let den := (m : ℝ) * Real.sqrt (nullVSeries m (2 + r))
  have hfour : 4 *
      (∫ data, |canonicalOneEdgePrefixRemainder m r data|
        ∂nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) (2 + r)) ≤
      16 / den := by
    calc
      4 * (∫ data, |canonicalOneEdgePrefixRemainder m r data|
        ∂nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) (2 + r)) ≤
          4 * (4 / den) := mul_le_mul_of_nonneg_left
            (by simpa [den] using hL1) (by norm_num)
      _ = 16 / den := by ring
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  calc
    (Measure.map (standardizedGaussianRetainedTailStatistic m 2 r)
      (nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r))).real
        (Ioc a (a + h)) ≤
      2 * (h + 4 *
        (∫ data, |canonicalOneEdgePrefixRemainder m r data|
          ∂nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) (2 + r))) /
          Real.sqrt (2 * Real.pi) +
        4 * provedNullLogdetKolmogorovEnvelope m (2 + r) := hbase
    _ ≤ 2 * (h + 16 / den) / Real.sqrt (2 * Real.pi) +
        4 * provedNullLogdetKolmogorovEnvelope m (2 + r) := by
      gcongr
    _ = 2 * (h + 16 /
        ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r)))) /
          Real.sqrt (2 * Real.pi) +
        4 * provedNullLogdetKolmogorovEnvelope m (2 + r) := by
      rfl

/-! ## Concrete threshold-mark replacement -/

/-- Unconditional canonical one-edge mark replacement.  The explicit error
is `4 B + 40/(m√V√(2π))`, where `B` is the proved finite scalar
Kolmogorov envelope. -/
theorem integral_abs_Z0mp_lowerMark_sub_canonicalLeaveMark_le
    {m r : ℕ} (hadm : Admissible m (2 + r)) (hm6 : 6 ≤ m)
    (z : ℝ) :
    (∫ data,
      |lowerThresholdIndicator z (Z0mpStatistic m (2 + r) data) -
        canonicalOneEdgeLeaveMark m r z data|
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) ≤
      4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
        40 / ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r)) *
          Real.sqrt (2 * Real.pi)) := by
  let P := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) (2 + r)
  let den := (m : ℝ) * Real.sqrt (nullVSeries m (2 + r))
  let s := Real.sqrt (2 * Real.pi)
  let c := 2 / s
  let d := 32 / (den * s) +
    4 * provedNullLogdetKolmogorovEnvelope m (2 + r)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hm0 : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden : 0 < den := mul_pos hm0 (sqrt_nullVSeries_pos hadm)
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 ≤ c := div_nonneg (by norm_num) hs.le
  have hB : 0 ≤ provedNullLogdetKolmogorovEnvelope m (2 + r) :=
    provedNullLogdetKolmogorovEnvelope_nonneg m (2 + r)
  have hd : 0 ≤ d := by
    dsimp [d]
    exact add_nonneg (div_nonneg (by norm_num) (mul_nonneg hden.le hs.le))
      (mul_nonneg (by norm_num) hB)
  have hinterval : ∀ (a h : ℝ), 0 ≤ h →
      (Measure.map (standardizedGaussianRetainedTailStatistic m 2 r) P).real
        (Ioc a (a + h)) ≤ c * h + d := by
    intro a h hh
    have hi := map_retainedTail_measureReal_Ioc_le
      hadm hm6 (a := a) (h := h) hh
    calc
      (Measure.map (standardizedGaussianRetainedTailStatistic m 2 r) P).real
          (Ioc a (a + h)) ≤
        2 * (h + 16 / den) / s +
          4 * provedNullLogdetKolmogorovEnvelope m (2 + r) := by
        simpa [P, den, s] using hi
      _ = c * h + d := by
        dsimp [c, d]
        ring
  have hrInt : Integrable
      (fun data ↦
        |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r)
          (nestedTuplePrefix 2 r data)|) P := by
    simpa [P, canonicalOneEdgePrefixRemainder] using
      (integrable_abs_canonicalOneEdgePrefixRemainder hadm hm6)
  have hrep :=
    integral_weighted_abs_lowerThresholdIndicator_add_sub_le_of_indep
      P
      (nestedTuplePrefix
        (E := ObservationSpace (m + 1)) 2 r)
      (standardizedGaussianRetainedTailStatistic m 2 r)
      (canonicalOneEdgePrefixRemainderOnPrefix m (2 + r))
      (fun _ ↦ (1 : ℝ)) z c d
      (measurable_nestedTuplePrefix 2 r)
      (measurable_standardizedGaussianRetainedTailStatistic m 2 r)
      (measurable_canonicalOneEdgePrefixRemainderOnPrefix m (2 + r))
      measurable_const
      (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
      hrInt hc hd
      (nestedTuplePrefix_indep_standardizedGaussianRetainedTailStatistic
        hadm.2)
      hinterval
  have hrep' :
      (∫ data,
        |lowerThresholdIndicator z
          (standardizedGaussianRetainedTailStatistic m 2 r data +
            canonicalOneEdgePrefixRemainder m r data) -
          lowerThresholdIndicator z
            (standardizedGaussianRetainedTailStatistic m 2 r data)| ∂P) ≤
        c * (∫ data, |canonicalOneEdgePrefixRemainder m r data| ∂P) + d := by
    simpa [canonicalOneEdgePrefixRemainder] using hrep
  have hmarkEq :
      (∫ data,
        |lowerThresholdIndicator z (Z0mpStatistic m (2 + r) data) -
          canonicalOneEdgeLeaveMark m r z data| ∂P) =
      ∫ data,
        |lowerThresholdIndicator z
          (standardizedGaussianRetainedTailStatistic m 2 r data +
            canonicalOneEdgePrefixRemainder m r data) -
          lowerThresholdIndicator z
            (standardizedGaussianRetainedTailStatistic m 2 r data)| ∂P := by
    apply integral_congr_ae
    filter_upwards
      [ae_Z0mpStatistic_eq_canonicalOneEdgePrefix_add_tail hadm.2]
      with data hdecomp
    rw [hdecomp]
    simp [canonicalOneEdgeLeaveMark, add_comm]
  have hL1 := integral_abs_canonicalOneEdgePrefixRemainder_le hadm hm6
  calc
    (∫ data,
      |lowerThresholdIndicator z (Z0mpStatistic m (2 + r) data) -
        canonicalOneEdgeLeaveMark m r z data|
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) =
      (∫ data,
        |lowerThresholdIndicator z (Z0mpStatistic m (2 + r) data) -
          canonicalOneEdgeLeaveMark m r z data| ∂P) := by rfl
    _ = ∫ data,
        |lowerThresholdIndicator z
          (standardizedGaussianRetainedTailStatistic m 2 r data +
            canonicalOneEdgePrefixRemainder m r data) -
          lowerThresholdIndicator z
            (standardizedGaussianRetainedTailStatistic m 2 r data)| ∂P := hmarkEq
    _ ≤ c * (∫ data, |canonicalOneEdgePrefixRemainder m r data| ∂P) + d :=
      hrep'
    _ ≤ c * (4 / den) + d := by
      have hL1' :
          (∫ data, |canonicalOneEdgePrefixRemainder m r data| ∂P) ≤
            4 / den := by
        simpa [P, den, Nat.add_comm] using hL1
      have hmul := mul_le_mul_of_nonneg_left hL1' hc
      calc
        c * (∫ data, |canonicalOneEdgePrefixRemainder m r data| ∂P) + d =
            d + c * (∫ data,
              |canonicalOneEdgePrefixRemainder m r data| ∂P) := by ring
        _ ≤ d + c * (4 / den) := add_le_add_right hmul d
        _ = c * (4 / den) + d := by ring
    _ = 4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
        40 / (den * s) := by
      dsimp [c, d]
      ring
    _ = 4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
        40 / ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r)) *
          Real.sqrt (2 * Real.pi)) := by
      rfl

/-- Canonical edge-event-weighted mark replacement.  The edge probability
factors out, leaving the finite conditional-scale error
`4 B + 64 ell/(m√V√(2π))`. -/
theorem
    integral_canonicalEdgeIndicator_mul_abs_Z0mp_lowerMark_sub_leaveMark_le
    {m r : ℕ} (hadm : Admissible m (2 + r)) (hm6 : 6 ≤ m)
    (x z ell : ℝ)
    (ht0 : 0 < classicalCoherenceThreshold m (2 + r) x / (m : ℝ))
    (htHalf : classicalCoherenceThreshold m (2 + r) x / (m : ℝ) ≤ 1 / 2)
    (hell : 1 ≤ ell)
    (htRate : classicalCoherenceThreshold m (2 + r) x / (m : ℝ) ≤
      5 * ell / (m : ℝ)) :
    (∫ data,
      (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
        |lowerThresholdIndicator z (Z0mpStatistic m (2 + r) data) -
          canonicalOneEdgeLeaveMark m r z data|
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) ≤
      (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
          (Ioi (classicalCoherenceThreshold m (2 + r) x / (m : ℝ))) *
        (4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          64 * ell /
            ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r)) *
              Real.sqrt (2 * Real.pi))) := by
  let P := nestedProductMeasure
    (stdGaussian (ObservationSpace (m + 1))) (2 + r)
  let den := (m : ℝ) * Real.sqrt (nullVSeries m (2 + r))
  let s := Real.sqrt (2 * Real.pi)
  let t := classicalCoherenceThreshold m (2 + r) x / (m : ℝ)
  let q := (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real (Ioi t)
  let c := 2 / s
  let d := 32 / (den * s) +
    4 * provedNullLogdetKolmogorovEnvelope m (2 + r)
  let w : NestedTuple (ObservationSpace (m + 1)) 2 → ℝ := fun pref ↦
    (canonicalEdgeExceedanceIndicatorOnPrefix m r x pref : ℝ)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hm0 : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden : 0 < den := mul_pos hm0 (sqrt_nullVSeries_pos hadm)
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 ≤ c := div_nonneg (by norm_num) hs.le
  have hB : 0 ≤ provedNullLogdetKolmogorovEnvelope m (2 + r) :=
    provedNullLogdetKolmogorovEnvelope_nonneg m (2 + r)
  have hd : 0 ≤ d := by
    dsimp [d]
    exact add_nonneg (div_nonneg (by norm_num) (mul_nonneg hden.le hs.le))
      (mul_nonneg (by norm_num) hB)
  have hcast : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
    measurable_of_countable (fun n : ℕ ↦ (n : ℝ))
  have hw : Measurable w := hcast.comp
    (measurable_canonicalEdgeExceedanceIndicatorOnPrefix m r x)
  have hw0 : ∀ pref, 0 ≤ w pref := by
    intro pref
    dsimp [w]
    unfold canonicalEdgeExceedanceIndicatorOnPrefix
    split_ifs <;> norm_num
  have hw1 : ∀ pref, w pref ≤ 1 := by
    intro pref
    dsimp [w]
    unfold canonicalEdgeExceedanceIndicatorOnPrefix
    split_ifs <;> norm_num
  have hinterval : ∀ (a h : ℝ), 0 ≤ h →
      (Measure.map (standardizedGaussianRetainedTailStatistic m 2 r) P).real
        (Ioc a (a + h)) ≤ c * h + d := by
    intro a h hh
    have hi := map_retainedTail_measureReal_Ioc_le
      hadm hm6 (a := a) (h := h) hh
    calc
      (Measure.map (standardizedGaussianRetainedTailStatistic m 2 r) P).real
          (Ioc a (a + h)) ≤
        2 * (h + 16 / den) / s +
          4 * provedNullLogdetKolmogorovEnvelope m (2 + r) := by
        simpa [P, den, s] using hi
      _ = c * h + d := by
        dsimp [c, d]
        ring
  have hrInt : Integrable
      (fun data ↦
        |canonicalOneEdgePrefixRemainderOnPrefix m (2 + r)
          (nestedTuplePrefix 2 r data)|) P := by
    simpa [P, canonicalOneEdgePrefixRemainder] using
      (integrable_abs_canonicalOneEdgePrefixRemainder hadm hm6)
  have hrep :=
    integral_weighted_abs_lowerThresholdIndicator_add_sub_le_of_indep
      P
      (nestedTuplePrefix
        (E := ObservationSpace (m + 1)) 2 r)
      (standardizedGaussianRetainedTailStatistic m 2 r)
      (canonicalOneEdgePrefixRemainderOnPrefix m (2 + r))
      w z c d
      (measurable_nestedTuplePrefix 2 r)
      (measurable_standardizedGaussianRetainedTailStatistic m 2 r)
      (measurable_canonicalOneEdgePrefixRemainderOnPrefix m (2 + r))
      hw hw0 hw1 hrInt hc hd
      (nestedTuplePrefix_indep_standardizedGaussianRetainedTailStatistic
        hadm.2)
      hinterval
  have hrep' :
      (∫ data,
        (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
          |lowerThresholdIndicator z
            (standardizedGaussianRetainedTailStatistic m 2 r data +
              canonicalOneEdgePrefixRemainder m r data) -
            lowerThresholdIndicator z
              (standardizedGaussianRetainedTailStatistic m 2 r data)| ∂P) ≤
        c * (∫ data,
          (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
            |canonicalOneEdgePrefixRemainder m r data| ∂P) +
        d * (∫ data,
          (canonicalEdgeExceedanceIndicator m r x data : ℝ) ∂P) := by
    simpa [w, canonicalEdgeExceedanceIndicator,
      canonicalOneEdgePrefixRemainder] using hrep
  have hmarkEq :
      (∫ data,
        (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
          |lowerThresholdIndicator z (Z0mpStatistic m (2 + r) data) -
            canonicalOneEdgeLeaveMark m r z data| ∂P) =
      ∫ data,
        (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
          |lowerThresholdIndicator z
            (standardizedGaussianRetainedTailStatistic m 2 r data +
              canonicalOneEdgePrefixRemainder m r data) -
            lowerThresholdIndicator z
              (standardizedGaussianRetainedTailStatistic m 2 r data)| ∂P := by
    apply integral_congr_ae
    filter_upwards
      [ae_Z0mpStatistic_eq_canonicalOneEdgePrefix_add_tail hadm.2]
      with data hdecomp
    rw [hdecomp]
    simp [canonicalOneEdgeLeaveMark, add_comm]
  have hweightedRaw :=
    integral_canonicalEdgeIndicator_mul_abs_prefixRemainder_le_log_rate
      hadm hm6 x ell ht0 htHalf hell htRate
  have hweighted :
      (∫ data,
        (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
          |canonicalOneEdgePrefixRemainder m r data| ∂P) ≤
        q * (16 * ell / den) := by
    simpa [P, q, t, den] using hweightedRaw
  have hmeanRaw := integral_canonicalEdgeExceedanceIndicator_eq_betaTail
    (m := m) (r := r) (by omega) x
  have hmean :
      (∫ data,
        (canonicalEdgeExceedanceIndicator m r x data : ℝ) ∂P) = q := by
    simpa [P, q, t] using hmeanRaw
  have hq0 : 0 ≤ q := by dsimp [q]; exact measureReal_nonneg
  have hsmall : 32 / (den * s) ≤ 32 * ell / (den * s) := by
    apply (div_le_div_iff_of_pos_right (mul_pos hden hs)).2
    nlinarith
  have hinside :
      4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          32 * ell / (den * s) + 32 / (den * s) ≤
        4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          64 * ell / (den * s) := by
    calc
      4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          32 * ell / (den * s) + 32 / (den * s) ≤
        4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          32 * ell / (den * s) + 32 * ell / (den * s) :=
        add_le_add_right hsmall
          (4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
            32 * ell / (den * s))
      _ = 4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          64 * ell / (den * s) := by ring
  calc
    (∫ data,
      (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
        |lowerThresholdIndicator z (Z0mpStatistic m (2 + r) data) -
          canonicalOneEdgeLeaveMark m r z data|
      ∂nestedProductMeasure
        (stdGaussian (ObservationSpace (m + 1))) (2 + r)) =
      (∫ data,
        (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
          |lowerThresholdIndicator z (Z0mpStatistic m (2 + r) data) -
            canonicalOneEdgeLeaveMark m r z data| ∂P) := by rfl
    _ = ∫ data,
        (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
          |lowerThresholdIndicator z
            (standardizedGaussianRetainedTailStatistic m 2 r data +
              canonicalOneEdgePrefixRemainder m r data) -
            lowerThresholdIndicator z
              (standardizedGaussianRetainedTailStatistic m 2 r data)| ∂P :=
      hmarkEq
    _ ≤ c * (∫ data,
          (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
            |canonicalOneEdgePrefixRemainder m r data| ∂P) +
        d * (∫ data,
          (canonicalEdgeExceedanceIndicator m r x data : ℝ) ∂P) := hrep'
    _ ≤ c * (q * (16 * ell / den)) + d * q := by
      rw [hmean]
      have hmul := mul_le_mul_of_nonneg_left hweighted hc
      calc
        c * (∫ data,
            (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
              |canonicalOneEdgePrefixRemainder m r data| ∂P) + d * q =
          d * q + c * (∫ data,
            (canonicalEdgeExceedanceIndicator m r x data : ℝ) *
              |canonicalOneEdgePrefixRemainder m r data| ∂P) := by ring
        _ ≤ d * q + c * (q * (16 * ell / den)) :=
          add_le_add_right hmul (d * q)
        _ = c * (q * (16 * ell / den)) + d * q := by ring
    _ = q *
        (4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          32 * ell / (den * s) + 32 / (den * s)) := by
      dsimp [c, d]
      ring
    _ ≤ q *
        (4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          64 * ell / (den * s)) :=
      mul_le_mul_of_nonneg_left hinside hq0
    _ = (betaMeasure (1 / 2) (((m - 1 : ℕ) : ℝ) / 2)).real
          (Ioi (classicalCoherenceThreshold m (2 + r) x / (m : ℝ))) *
        (4 * provedNullLogdetKolmogorovEnvelope m (2 + r) +
          64 * ell /
            ((m : ℝ) * Real.sqrt (nullVSeries m (2 + r)) *
              Real.sqrt (2 * Real.pi))) := by
      rfl

end

end LogdetLean.Coherence
