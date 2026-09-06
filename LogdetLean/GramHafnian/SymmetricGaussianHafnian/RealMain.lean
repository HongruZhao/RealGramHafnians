import LogdetLean.GramHafnian.SymmetricGaussianHafnian.RealLiteralCompression
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.HalfInverseMoment
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.Constants
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.RealSmallBallLowerCore
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-!
# Unconditional real Gaussian hafnian anticoncentration

The observable is the literal perfect-matching hafnian of a symmetric real
matrix with independent `N(0,1)` upper off-diagonal entries.  The final
shifted-interval theorem has no analytic hypothesis or scientific axiom.
-/

open MeasureTheory ProbabilityTheory Set Complex
open scoped BigOperators ENNReal Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 1200000

/-! ## Euclidean realization and radial recurrence -/

def realEdgeCofactorEuclidean {d : ℕ}
    (x : Edge (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j ↦ realEdgeCofactor x j)

@[fun_prop] theorem measurable_realEdgeCofactorEuclidean (d : ℕ) :
    Measurable (realEdgeCofactorEuclidean (d := d)) := by
  unfold realEdgeCofactorEuclidean
  apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
  exact measurable_realEdgeCofactor

def realEdgeCofactorLaw (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (realEdgeGaussian (Fin d)).map realEdgeCofactorEuclidean

instance realEdgeCofactorLaw_probability (d : ℕ) :
    IsProbabilityMeasure (realEdgeCofactorLaw d) := by
  unfold realEdgeCofactorLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_realEdgeCofactorEuclidean d).aemeasurable

theorem norm_sq_realEdgeCofactorEuclidean {d : ℕ}
    (x : Edge (Fin d) → ℝ) :
    ‖realEdgeCofactorEuclidean x‖ ^ 2 = realEdgeCofactorEnergy x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [realEdgeCofactorEuclidean, realEdgeCofactorEnergy]

theorem realEdgeCofactorCharacteristic_eq_charFun {d : ℕ}
    (xi : EuclideanSpace ℝ (Fin d)) :
    realEdgeCofactorCharacteristic (Fin d) (fun j ↦ xi j) =
      charFun (realEdgeCofactorLaw d) xi := by
  unfold realEdgeCofactorCharacteristic realEdgeCofactorLaw charFun
  rw [integral_map (measurable_realEdgeCofactorEuclidean d).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold realEdgeCofactorPhaseCharacter realEdgeCofactorPhase
  congr 2

theorem ennHalfInverseMoment_realEdgeCofactorLaw (d : ℕ) :
    ennHalfInverseMoment (realEdgeCofactorLaw d) (fun x ↦ ‖x‖ ^ 2) =
      ennHalfInverseMoment (realEdgeGaussian (Fin d)) realEdgeCofactorEnergy := by
  unfold ennHalfInverseMoment realEdgeCofactorLaw
  rw [lintegral_map (by fun_prop) (measurable_realEdgeCofactorEuclidean d)]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal ((‖realEdgeCofactorEuclidean x‖ ^ 2) ^ (-(1 / 2 : ℝ))) = _
  rw [norm_sq_realEdgeCofactorEuclidean]

theorem norm_sq_pos_ae_realEdgeCofactorLaw {d : ℕ}
    (hpos : ∀ᵐ x ∂realEdgeGaussian (Fin d), 0 < realEdgeCofactorEnergy x) :
    ∀ᵐ x ∂realEdgeCofactorLaw d, 0 < ‖x‖ ^ 2 := by
  rw [realEdgeCofactorLaw,
    ae_map_iff (measurable_realEdgeCofactorEuclidean d).aemeasurable
      (measurableSet_lt measurable_const (by fun_prop))]
  simpa only [norm_sq_realEdgeCofactorEuclidean] using hpos

/-- Full characteristic-function bound at paper cofactor level `r`. -/
theorem realEdgeCofactorCharacteristic_re_le_previous_mixture
    (r : ℕ) (hr : 2 ≤ r) (xi : EuclideanSpace ℝ (Fin (2 * r - 1))) :
    (realEdgeCofactorCharacteristic (Fin (2 * r - 1)) (fun j ↦ xi j)).re ≤
      ∫ A : Edge (Fin (2 * r - 3)) → ℝ,
        Real.exp (-(realEdgeCofactorEnergy A * ‖xi‖ ^ 2) / 2)
        ∂realEdgeGaussian (Fin (2 * r - 3)) := by
  have hc := realEdgeCofactorCharacteristic_norm_le_singleton r hr
    (⟨2 * r - 2, by omega⟩ : Fin (2 * r - 1)) (fun j ↦ xi j)
  have henergy : realCoordinateEnergy (fun j ↦ xi j) = ‖xi‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [realCoordinateEnergy]
  have hsize : (2 * r - 3) + 2 = 2 * r - 1 := by omega
  have hsingle' (t : ℝ) :
      realEdgeCofactorCharacteristic (Fin (2 * r - 1))
          (realSingleCoordinate (⟨2 * r - 2, by omega⟩ : Fin (2 * r - 1)) t) =
        ∫ A : Edge (Fin (2 * r - 3)) → ℝ,
          Complex.exp (-(((realEdgeCofactorEnergy A * t ^ 2 : ℝ) : ℂ) / 2))
          ∂realEdgeGaussian (Fin (2 * r - 3)) := by
    let e : Fin ((2 * r - 3) + 2) ≃ Fin (2 * r - 1) :=
      (Fin.castOrderIso hsize).toEquiv
    let lastSource : Fin ((2 * r - 3) + 2) := Fin.last ((2 * r - 3) + 1)
    let lastTarget : Fin (2 * r - 1) := ⟨2 * r - 2, by omega⟩
    have heLast : e lastSource = lastTarget := by
      apply Fin.ext
      change 2 * r - 3 + 1 = 2 * r - 2
      omega
    have hw :
        (fun j ↦ realSingleCoordinate lastTarget t (e j)) =
          realSingleCoordinate lastSource t := by
      funext j
      by_cases hj : j = lastSource
      · subst j
        simp [realSingleCoordinate, heLast]
      · have hej : e j ≠ lastTarget := by
          intro h
          apply hj
          exact e.injective (h.trans heLast.symm)
        simp [realSingleCoordinate, hj, hej]
    have hre := realEdgeCofactorCharacteristic_reindex e
      (realSingleCoordinate lastTarget t)
    rw [hw] at hre
    calc
      _ = realEdgeCofactorCharacteristic (Fin ((2 * r - 3) + 2))
          (realSingleCoordinate lastSource t) := hre.symm
      _ = _ := realEdgeCofactorCharacteristic_singleton_last (2 * r - 3) t
  rw [hsingle', henergy] at hc
  have hsqrt : Real.sqrt (‖xi‖ ^ 2) ^ 2 = ‖xi‖ ^ 2 :=
    Real.sq_sqrt (sq_nonneg _)
  calc
    _ ≤ ‖realEdgeCofactorCharacteristic (Fin (2 * r - 1)) (fun j ↦ xi j)‖ :=
      Complex.re_le_norm _
    _ ≤ ‖∫ A : Edge (Fin (2 * r - 3)) → ℝ,
        Complex.exp (-(((realEdgeCofactorEnergy A * Real.sqrt (‖xi‖ ^ 2) ^ 2 : ℝ) : ℂ) / 2))
        ∂realEdgeGaussian (Fin (2 * r - 3))‖ := hc
    _ ≤ ∫ A : Edge (Fin (2 * r - 3)) → ℝ,
        ‖Complex.exp (-(((realEdgeCofactorEnergy A * Real.sqrt (‖xi‖ ^ 2) ^ 2 : ℝ) : ℂ) / 2))‖
        ∂realEdgeGaussian (Fin (2 * r - 3)) := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with A
      rw [Complex.norm_exp, hsqrt]
      congr 1
      norm_cast
      ring

/-! ## Almost-sure positivity -/

theorem realLinearForm_zero_measure_of_energy_pos {d : ℕ}
    (y : Fin d → ℝ) (hy : 0 < realCoefficientEnergy y) :
    (standardRealGaussianProduct (Fin d))
      {g | iidRealLinearForm y g = 0} = 0 := by
  have hs : Real.sqrt (realCoefficientEnergy y) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hy
  let _ : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hsingle : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton 0
  calc
    _ = ((standardRealGaussianProduct (Fin d)).map (iidRealLinearForm y)) {0} :=
      (Measure.map_apply (measurable_iidRealLinearForm y) hsingle).symm
    _ = ((gaussianReal 0 1).map
        (fun z : ℝ ↦ Real.sqrt (realCoefficientEnergy y) * z)) {0} := by
      rw [iidRealLinearForm_law]
    _ = (gaussianReal 0 1)
        ((fun z : ℝ ↦ Real.sqrt (realCoefficientEnergy y) * z) ⁻¹' {0}) :=
      Measure.map_apply (by fun_prop) hsingle
    _ = (gaussianReal 0 1) ({0} : Set ℝ) := by
      congr 1
      ext z
      simp [hs]
    _ = 0 := measure_singleton 0

theorem ae_realEdgeHafnian_ne_zero_of_energy_pos (d : ℕ)
    (hpos : ∀ᵐ x ∂realEdgeGaussian (Fin d), 0 < realEdgeCofactorEnergy x) :
    ∀ᵐ x ∂realEdgeGaussian (Fin (d + 1)), realEdgeHafnian x ≠ 0 := by
  let S : Set ((Edge (Fin d) → ℝ) × (Fin d → ℝ)) :=
    {p | iidRealLinearForm (realEdgeCofactor p.1) p.2 = 0}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hprod : ((realEdgeGaussian (Fin d)).prod
      (standardRealGaussianProduct (Fin d))) S = 0 := by
    rw [Measure.prod_apply hS]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hpos] with A hA
    simpa [S, realEdgeCofactorEnergy, realCoefficientEnergy] using
      realLinearForm_zero_measure_of_energy_pos (realEdgeCofactor A) hA
  rw [ae_iff]
  simp only [not_ne_iff]
  let T : Set (Edge (Fin (d + 1)) → ℝ) := {x | realEdgeHafnian x = 0}
  have hT : MeasurableSet T := by
    dsimp [T]
    exact measurableSet_eq_fun measurable_realEdgeHafnian measurable_const
  have hpre : T = realLastVertexSplit d ⁻¹' S := by
    ext x
    change (realEdgeHafnian x = 0) ↔
      (iidRealLinearForm (realEdgeCofactor (realLastVertexSplit d x).1)
        (realLastVertexSplit d x).2 = 0)
    rw [realEdgeHafnian_eq_lastVertexLinearForm]
  rw [show {x : Edge (Fin (d + 1)) → ℝ | realEdgeHafnian x = 0} = T by rfl,
    hpre, (measurePreserving_realLastVertexSplit d).measure_preimage hS.nullMeasurableSet]
  exact hprod

theorem ae_realEdgeEnergy_succ_pos_of_hafnian_ne_zero (d : ℕ)
    (hH : ∀ᵐ x ∂realEdgeGaussian (Fin d), realEdgeHafnian x ≠ 0) :
    ∀ᵐ x ∂realEdgeGaussian (Fin (d + 1)), 0 < realEdgeCofactorEnergy x := by
  have hpull :=
    (measurePreserving_realRestrictEdges (initialVertexEmbedding d)).quasiMeasurePreserving.ae hH
  filter_upwards [hpull] with x hx
  have hc : realEdgeCofactor x (Fin.last d) ≠ 0 := by
    rwa [realEdgeCofactor_last_eq_restrictedHafnian]
  have hs : 0 < (realEdgeCofactor x (Fin.last d)) ^ 2 := sq_pos_of_ne_zero hc
  apply lt_of_lt_of_le hs
  unfold realEdgeCofactorEnergy
  exact Finset.single_le_sum
    (fun j _ ↦ sq_nonneg (realEdgeCofactor x j)) (Finset.mem_univ _)

theorem ae_realEdgeHafnian_nonzero_even (n : ℕ) :
    ∀ᵐ x ∂realEdgeGaussian (Fin (2 * n)), realEdgeHafnian x ≠ 0 := by
  induction n with
  | zero =>
      apply Filter.Eventually.of_forall
      intro x
      simp [realEdgeHafnian, typeHafnian_eq_one_of_isEmpty]
  | succ n ih =>
      have hp := ae_realEdgeEnergy_succ_pos_of_hafnian_ne_zero (2 * n) ih
      have hn := ae_realEdgeHafnian_ne_zero_of_energy_pos (2 * n + 1) hp
      have hdim : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [hdim]
      exact hn

theorem ae_realEdgeCofactorEnergy_pos_odd (n : ℕ) :
    ∀ᵐ x ∂realEdgeGaussian (Fin (2 * n + 1)),
      0 < realEdgeCofactorEnergy x :=
  ae_realEdgeEnergy_succ_pos_of_hafnian_ne_zero (2 * n)
    (ae_realEdgeHafnian_nonzero_even n)

/-! ## Exact half-inverse-moment product -/

def realCofactorHalfInverseMoment (n : ℕ) : ℝ≥0∞ :=
  ennHalfInverseMoment (realEdgeGaussian (Fin (2 * n - 1))) realEdgeCofactorEnergy

@[simp] theorem realCofactorHalfInverseMoment_one :
    realCofactorHalfInverseMoment 1 = 1 := by
  have hc (x : Edge (Fin 1) → ℝ) (j : Fin 1) : realEdgeCofactor x j = 1 := by
    unfold realEdgeCofactor matrixCofactor
    let _ : IsEmpty {i : Fin 1 // i ≠ j} := ⟨fun i ↦ by
      have hij : i.1 = j := Subsingleton.elim _ _
      exact i.2 hij⟩
    exact typeHafnian_eq_one_of_isEmpty _
  have he (x : Edge (Fin 1) → ℝ) : realEdgeCofactorEnergy x = 1 := by
    unfold realEdgeCofactorEnergy
    simp_rw [hc x]
    simp
  unfold realCofactorHalfInverseMoment ennHalfInverseMoment
  simp_rw [he]
  simp

theorem realCofactorHalfInverseMoment_step (r : ℕ) (hr : 2 ≤ r) :
    realCofactorHalfInverseMoment r ≤
      realCofactorHalfInverseMoment (r - 1) *
        ENNReal.ofReal (gammaNegativeFactor 1 r (1 / 2)) := by
  unfold realCofactorHalfInverseMoment
  have hdim : 2 * (r - 1) - 1 = 2 * r - 3 := by omega
  rw [hdim]
  rw [← ennHalfInverseMoment_realEdgeCofactorLaw]
  apply ennHalfInverse_normSq_le_realGammaFactor r hr
    (realEdgeCofactorLaw (2 * r - 1))
    (realEdgeGaussian (Fin (2 * r - 3))) realEdgeCofactorEnergy
    measurable_realEdgeCofactorEnergy realEdgeCofactorEnergy_nonneg
  · have h := ae_realEdgeCofactorEnergy_pos_odd (r - 2)
    have hsize : 2 * (r - 2) + 1 = 2 * r - 3 := by omega
    rw [hsize] at h
    exact h
  · intro xi
    rw [← realEdgeCofactorCharacteristic_eq_charFun]
    exact realEdgeCofactorCharacteristic_re_le_previous_mixture r hr xi
  · have h := ae_realEdgeCofactorEnergy_pos_odd (r - 1)
    have hsize : 2 * (r - 1) + 1 = 2 * r - 1 := by omega
    rw [hsize] at h
    exact norm_sq_pos_ae_realEdgeCofactorLaw h

def realGammaProduct (n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n, gammaNegativeFactor 1 r (1 / 2)

theorem realCofactorHalfInverseMoment_le (n : ℕ) (hn : 1 ≤ n) :
    realCofactorHalfInverseMoment n ≤ ENNReal.ofReal (realGammaProduct n) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    realCofactorHalfInverseMoment j ≤ ENNReal.ofReal (realGammaProduct j)
  have hind : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · simp [P, realGammaProduct]
    · intro r hr ih
      dsimp [P] at ih ⊢
      calc
        realCofactorHalfInverseMoment (r + 1) ≤
            realCofactorHalfInverseMoment r *
              ENNReal.ofReal (gammaNegativeFactor 1 (r + 1) (1 / 2)) := by
          simpa using realCofactorHalfInverseMoment_step (r + 1) (by omega)
        _ ≤ ENNReal.ofReal (realGammaProduct r) *
            ENNReal.ofReal (gammaNegativeFactor 1 (r + 1) (1 / 2)) :=
          mul_le_mul ih le_rfl bot_le bot_le
        _ = ENNReal.ofReal (realGammaProduct (r + 1)) := by
          rw [← ENNReal.ofReal_mul]
          · unfold realGammaProduct
            rw [Finset.prod_Icc_succ_top (by omega)]
          · exact (Finset.prod_nonneg fun j hj ↦
              (gammaNegativeFactor_pos (by norm_num)
                (Finset.mem_Icc.mp hj).1 (by norm_num)).le)
  exact hind

/-! ## Shifted real intervals -/

private theorem two_div_sqrt_two_pi :
    2 / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hpi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  field_simp [h2, hpi]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem gaussianReal_standard_scaled_shiftedInterval_le
    (s z rho : ℝ) (hs : 0 < s) (hrho : 0 ≤ rho) :
    (gaussianReal 0 1) {x : ℝ | |s * x - z| ≤ rho} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * rho / s) := by
  let S : Set ℝ := {x | |s * x - z| ≤ rho}
  have hS : S = Icc ((z - rho) / s) ((z + rho) / s) := by
    ext x
    simp only [S, mem_setOf_eq, mem_Icc]
    constructor
    · intro hx
      have h := abs_le.mp hx
      constructor
      · apply (div_le_iff₀ hs).2
        linarith
      · apply (le_div_iff₀ hs).2
        linarith
    · intro hx
      apply abs_le.mpr
      constructor
      · have h := (div_le_iff₀ hs).1 hx.1
        linarith
      · have h := (le_div_iff₀ hs).1 hx.2
        linarith
  have hpdf (x : ℝ) :
      gaussianPDF 0 1 x ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) := by
    unfold gaussianPDF gaussianPDFReal
    apply ENNReal.ofReal_le_ofReal
    norm_num at ⊢
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
    have hexp' : Real.exp (-x ^ 2 / 2) ≤ 1 := by simpa using hexp
    simpa using mul_le_mul_of_nonneg_left hexp'
      (show 0 ≤ (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ by positivity)
  rw [show {x : ℝ | |s * x - z| ≤ rho} = S by rfl,
    gaussianReal_apply 0 (by norm_num), hS]
  calc
    (∫⁻ x in Icc ((z - rho) / s) ((z + rho) / s), gaussianPDF 0 1 x) ≤
        ∫⁻ _x in Icc ((z - rho) / s) ((z + rho) / s),
          ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) := by
      apply lintegral_mono
      exact hpdf
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) *
        volume (Icc ((z - rho) / s) ((z + rho) / s)) :=
      setLIntegral_const _ _
    _ = ENNReal.ofReal (Real.sqrt (2 / Real.pi) * rho / s) := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        (Real.sqrt (2 * Real.pi))⁻¹ *
            ((z + rho) / s - (z - rho) / s) =
            (2 / Real.sqrt (2 * Real.pi)) * rho / s := by
          field_simp [hs.ne']
          ring
        _ = _ := by rw [two_div_sqrt_two_pi]

theorem iidRealLinearForm_shiftedInterval_le
    {d : ℕ} (y : Fin d → ℝ)
    (hy : 0 < realCoefficientEnergy y) (z rho : ℝ) (hrho : 0 ≤ rho) :
    (standardRealGaussianProduct (Fin d))
        {g | |iidRealLinearForm y g - z| ≤ rho} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * rho *
        (realCoefficientEnergy y) ^ (-(1 / 2 : ℝ))) := by
  let T : Set ℝ := {u | |u - z| ≤ rho}
  have hT : MeasurableSet T := by
    dsimp [T]
    exact measurableSet_le (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
      measurable_const
  let s := Real.sqrt (realCoefficientEnergy y)
  have hs : 0 < s := Real.sqrt_pos.2 hy
  have hrpow :
      (realCoefficientEnergy y) ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    dsimp [s]
    rw [Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]
  calc
    _ = ((standardRealGaussianProduct (Fin d)).map (iidRealLinearForm y)) T :=
      (Measure.map_apply (measurable_iidRealLinearForm y) hT).symm
    _ = ((gaussianReal 0 1).map (fun u : ℝ ↦ s * u)) T := by
      rw [iidRealLinearForm_law]
    _ = (gaussianReal 0 1) {u : ℝ | |s * u - z| ≤ rho} := by
      rw [Measure.map_apply (by fun_prop) hT]
      rfl
    _ ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * rho / s) :=
      gaussianReal_standard_scaled_shiftedInterval_le s z rho hs hrho
    _ = _ := by
      congr 1
      rw [hrpow]
      field_simp [hs.ne']

theorem prod_realGaussian_shiftedInterval_le_halfInverseMoment
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (nu : Measure Ω) [IsProbabilityMeasure nu]
    (y : Ω → Fin d → ℝ) (hy : Measurable y)
    (henergy : ∀ᵐ w ∂nu, 0 < realCoefficientEnergy (y w))
    (z rho : ℝ) (hrho : 0 ≤ rho) :
    (nu.prod (standardRealGaussianProduct (Fin d)))
        {p | |iidRealLinearForm (y p.1) p.2 - z| ≤ rho} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * rho) *
        ennHalfInverseMoment nu (fun w ↦ realCoefficientEnergy (y w)) := by
  let mu := standardRealGaussianProduct (Fin d)
  let S : Set (Ω × (Fin d → ℝ)) :=
    {p | |iidRealLinearForm (y p.1) p.2 - z| ≤ rho}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le
      (continuous_abs.measurable.comp ((by
        unfold iidRealLinearForm
        fun_prop : Measurable (fun p : Ω × (Fin d → ℝ) ↦
          iidRealLinearForm (y p.1) p.2)).sub_const z)) measurable_const
  rw [show nu.prod (standardRealGaussianProduct (Fin d)) = nu.prod mu by rfl,
    show {p : Ω × (Fin d → ℝ) |
      |iidRealLinearForm (y p.1) p.2 - z| ≤ rho} = S by rfl,
    Measure.prod_apply hS]
  calc
    (∫⁻ w, mu (Prod.mk w ⁻¹' S) ∂nu) ≤
        ∫⁻ w, ENNReal.ofReal (Real.sqrt (2 / Real.pi) * rho) *
          ENNReal.ofReal ((realCoefficientEnergy (y w)) ^ (-(1 / 2 : ℝ))) ∂nu := by
      apply lintegral_mono_ae
      filter_upwards [henergy] with w hw
      have hfixed := iidRealLinearForm_shiftedInterval_le (y w) hw z rho hrho
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) hrho)] at hfixed
      simpa [mu, S] using hfixed
    _ = _ := by
      rw [lintegral_const_mul]
      · rfl
      · unfold realCoefficientEnergy
        fun_prop

theorem realEdgeHafnian_shiftedInterval_le_halfInverseMoment
    (d : ℕ)
    (hpos : ∀ᵐ x ∂realEdgeGaussian (Fin d), 0 < realEdgeCofactorEnergy x)
    (z rho : ℝ) (hrho : 0 ≤ rho) :
    (realEdgeGaussian (Fin (d + 1)))
        {x | |realEdgeHafnian x - z| ≤ rho} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * rho) *
        ennHalfInverseMoment (realEdgeGaussian (Fin d)) realEdgeCofactorEnergy := by
  let S : Set ((Edge (Fin d) → ℝ) × (Fin d → ℝ)) :=
    {p | |iidRealLinearForm (realEdgeCofactor p.1) p.2 - z| ≤ rho}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le
      (continuous_abs.measurable.comp ((by
        unfold iidRealLinearForm
        fun_prop : Measurable (fun p : (Edge (Fin d) → ℝ) × (Fin d → ℝ) ↦
          iidRealLinearForm (realEdgeCofactor p.1) p.2)).sub_const z)) measurable_const
  let T : Set (Edge (Fin (d + 1)) → ℝ) :=
    {x | |realEdgeHafnian x - z| ≤ rho}
  have hT : MeasurableSet T := by
    dsimp [T]
    exact measurableSet_le ((measurable_realEdgeHafnian.sub_const z).abs) measurable_const
  have hpre : T = realLastVertexSplit d ⁻¹' S := by
    ext x
    change (|realEdgeHafnian x - z| ≤ rho) ↔
      (|iidRealLinearForm (realEdgeCofactor (realLastVertexSplit d x).1)
        (realLastVertexSplit d x).2 - z| ≤ rho)
    rw [realEdgeHafnian_eq_lastVertexLinearForm]
  rw [show {x : Edge (Fin (d + 1)) → ℝ | |realEdgeHafnian x - z| ≤ rho} = T by rfl,
    hpre, (measurePreserving_realLastVertexSplit d).measure_preimage hS.nullMeasurableSet]
  change ((realEdgeGaussian (Fin d)).prod (standardRealGaussianProduct (Fin d)))
      {p | |iidRealLinearForm (realEdgeCofactor p.1) p.2 - z| ≤ rho} ≤
    ENNReal.ofReal (Real.sqrt (2 / Real.pi) * rho) *
      ennHalfInverseMoment (realEdgeGaussian (Fin d))
        (fun w ↦ ∑ j, (realEdgeCofactor w j) ^ 2)
  simpa [realEdgeCofactorEnergy, realCoefficientEnergy] using
    prod_realGaussian_shiftedInterval_le_halfInverseMoment
      (realEdgeGaussian (Fin d)) realEdgeCofactor measurable_realEdgeCofactor
      hpos z rho hrho

theorem gammaNegativeFactor_real_half (r : ℕ) :
    gammaNegativeFactor 1 r (1 / 2) =
      Real.Gamma ((r : ℝ) - 1) /
        (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2)) := by
  have hpow : ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  unfold gammaNegativeFactor gammaShape
  rw [hpow]
  have hnum : 1 * (2 * (r : ℝ) - 1) / 2 - 1 / 2 = (r : ℝ) - 1 := by ring
  have hden : 1 * (2 * (r : ℝ) - 1) / 2 = (r : ℝ) - 1 / 2 := by ring
  rw [hnum, hden]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem realGammaProduct_eq_paperProduct (n : ℕ) :
    realGammaProduct n =
      ∏ r ∈ Finset.Icc 2 n,
        Real.Gamma ((r : ℝ) - 1) /
          (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2)) := by
  unfold realGammaProduct
  apply Finset.prod_congr rfl
  intro r _
  exact gammaNegativeFactor_real_half r

theorem realGammaProduct_nonneg (n : ℕ) : 0 ≤ realGammaProduct n := by
  unfold realGammaProduct
  exact Finset.prod_nonneg fun r hr ↦
    (gammaNegativeFactor_pos (by norm_num) (Finset.mem_Icc.mp hr).1 (by norm_num)).le

theorem realHafnianSmallBallCoefficient_eq_gammaProduct (n : ℕ) :
    realHafnianSmallBallCoefficient n =
      Real.sqrt (2 / Real.pi) * sigma n * realGammaProduct n := by
  unfold realHafnianSmallBallCoefficient
  rw [realGammaProduct_eq_paperProduct]

/-- Literal finite, uniform-in-shift real Gaussian hafnian theorem. -/
theorem symmetricRealHafnian_shifted_smallBall
    (n : ℕ) (hn : 1 ≤ n) (z : ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    (realEdgeGaussian (Fin (2 * n)))
        {x | |realEdgeHafnian x - z| ≤ ε * sigma n} ≤
      min 1 (ENNReal.ofReal (realHafnianSmallBallCoefficient n * ε)) := by
  have hpos := ae_realEdgeCofactorEnergy_pos_odd (n - 1)
  have hsize : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  rw [hsize] at hpos
  have hraw := realEdgeHafnian_shiftedInterval_le_halfInverseMoment
    (2 * n - 1) hpos z (ε * sigma n) (mul_nonneg hε (sigma_nonneg n))
  rw [show 2 * n - 1 + 1 = 2 * n by omega] at hraw
  apply le_min
  · exact prob_le_one
  · calc
      _ ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (ε * sigma n)) *
          ennHalfInverseMoment (realEdgeGaussian (Fin (2 * n - 1)))
            realEdgeCofactorEnergy := hraw
      _ ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (ε * sigma n)) *
          ENNReal.ofReal (realGammaProduct n) :=
        mul_le_mul le_rfl (realCofactorHalfInverseMoment_le n hn) bot_le bot_le
      _ = ENNReal.ofReal (realHafnianSmallBallCoefficient n * ε) := by
        rw [← ENNReal.ofReal_mul
          (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hε (sigma_nonneg n))),
          realHafnianSmallBallCoefficient_eq_gammaProduct]
        congr 1
        ring

theorem symmetricRealHafnian_shifted_smallBall_uncapped
    (n : ℕ) (hn : 1 ≤ n) (z : ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    (realEdgeGaussian (Fin (2 * n)))
        {x | |realEdgeHafnian x - z| ≤ ε * sigma n} ≤
      ENNReal.ofReal (realHafnianSmallBallCoefficient n * ε) :=
  (symmetricRealHafnian_shifted_smallBall n hn z ε hε).trans (min_le_right _ _)

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
