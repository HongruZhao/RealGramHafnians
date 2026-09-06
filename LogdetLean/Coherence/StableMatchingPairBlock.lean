import LogdetLean.KibbleCovarianceBounds
import LogdetLean.GeneralRPairLaplace
import LogdetLean.Coherence.NoncentralPearsonRuben
import Mathlib.Tactic
/-!
# A strict Gaussian pair block and its log-radius difference

This file isolates the scalar `2 × 2` block calculation used in the stable
matching alternative.  For two standard Gaussian columns with correlation
`c`, it proves an all-dimension `L²` bound for the difference of their log
squared radii.  The proof uses the already verified unconditional Kibble
covariance remainder bounds; no asymptotic or scalar-series certificate is
assumed.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The elementary determinant representation of one minus a squared
normalized inner product. -/
theorem one_sub_squaredNormalizedInner_eq_twoColumnGramDet_div
    (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    1 - squaredNormalizedInner u v =
      twoColumnGramDet u v / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  unfold squaredNormalizedInner twoColumnGramDet
  field_simp [hnu, hnv]

/-- Mixing the second column by a population correlation multiplies the
unnormalized two-column Gram determinant by exactly `1-rho²`. -/
theorem twoColumnGramDet_correlatedSecondColumn_eq
    (rho : ℝ) (x e : E) (hrho : |rho| ≤ 1) (hx : x ≠ 0) :
    twoColumnGramDet x (correlatedSecondColumn rho x e) =
      (1 - rho ^ 2) * twoColumnGramDet x e := by
  have hcorr := twoColumnGramDet_correlatedSecondColumn rho x e hx
  have hnull := twoColumnGramDet_correlatedSecondColumn 0 x e hx
  have hsqrt : (Real.sqrt (1 - rho ^ 2)) ^ 2 = 1 - rho ^ 2 := by
    rw [Real.sq_sqrt]
    exact sub_nonneg.mpr ((sq_le_one_iff_abs_le_one rho).2 hrho)
  have hzero : correlatedSecondColumn 0 x e = e := by
    simp [correlatedSecondColumn]
  rw [hzero] at hnull
  norm_num at hnull
  rw [hsqrt] at hcorr
  rw [hcorr, hnull]
  ring

/-- Exact normalized two-column determinant ratio.  This is the scalar
identity behind the full block-triangular coupling used by the matching
alternative. -/
theorem one_sub_squaredNormalizedInner_correlatedSecondColumn
    (rho : ℝ) (x e : E) (hrho : |rho| < 1)
    (hx : x ≠ 0) (he : e ≠ 0)
    (hy : correlatedSecondColumn rho x e ≠ 0) :
    1 - squaredNormalizedInner x (correlatedSecondColumn rho x e) =
      (1 - rho ^ 2) * (1 - squaredNormalizedInner x e) *
        ‖e‖ ^ 2 / ‖correlatedSecondColumn rho x e‖ ^ 2 := by
  rw [one_sub_squaredNormalizedInner_eq_twoColumnGramDet_div x
      (correlatedSecondColumn rho x e) hx hy,
    one_sub_squaredNormalizedInner_eq_twoColumnGramDet_div x e hx he,
    twoColumnGramDet_correlatedSecondColumn_eq rho x e hrho.le hx]
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
  have hny : ‖correlatedSecondColumn rho x e‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hy
  field_simp [hnx, hne, hny]

/-- Exact logarithmic correction for one planted block.  It separates the
deterministic population shift from a difference of two Gaussian log radii. -/
theorem log_one_sub_squaredNormalizedInner_correlatedSecondColumn_sub
    (rho : ℝ) (x e : E) (hrho : |rho| < 1)
    (hx : x ≠ 0) (he : e ≠ 0)
    (hy : correlatedSecondColumn rho x e ≠ 0)
    (hnull : 0 < 1 - squaredNormalizedInner x e) :
    Real.log
          (1 - squaredNormalizedInner x (correlatedSecondColumn rho x e)) -
        Real.log (1 - squaredNormalizedInner x e) =
      Real.log (1 - rho ^ 2) + Real.log (‖e‖ ^ 2) -
        Real.log (‖correlatedSecondColumn rho x e‖ ^ 2) := by
  have hgap : 0 < 1 - rho ^ 2 := by
    exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one rho).2 hrho)
  have hne : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  have hny : ‖correlatedSecondColumn rho x e‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  rw [one_sub_squaredNormalizedInner_correlatedSecondColumn
      rho x e hrho hx he hy]
  rw [Real.log_div (mul_ne_zero (mul_ne_zero hgap.ne' hnull.ne') hne) hny,
    Real.log_mul (mul_ne_zero hgap.ne' hnull.ne') hne,
    Real.log_mul hgap.ne' hnull.ne']
  ring

/-- The strict `2 × 2` correlation matrix with off-diagonal entry `rho`. -/
def strictPairCorrelation (rho : ℝ) (hrho : |rho| < 1) :
    CorrelationMatrix 2 where
  val := CorrelationMatrix.pairCorrelationMatrix rho
  posDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [CorrelationMatrix.pairCorrelationMatrix, Matrix.IsHermitian]
    · intro x hx
      have hrhoSq : rho ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one rho).2 hrho
      have hgap : 0 < 1 - rho ^ 2 := sub_pos.mpr hrhoSq
      have hxcoord : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        funext i
        fin_cases i <;> simp [h.1, h.2]
      simp only [starRingEnd_apply, star_id_of_comm]
      simp [dotProduct, Matrix.mulVec,
        CorrelationMatrix.pairCorrelationMatrix]
      rcases hxcoord with hx0 | hx1
      · by_cases h1 : x 1 = 0
        · simpa [h1] using hx0
        · nlinarith [sq_nonneg (x 0 + rho * x 1),
            mul_pos hgap (sq_pos_of_ne_zero h1)]
      · nlinarith [sq_nonneg (x 0 + rho * x 1),
          mul_pos hgap (sq_pos_of_ne_zero hx1)]
  diag_one := by
    intro i
    fin_cases i <;> simp [CorrelationMatrix.pairCorrelationMatrix]

@[simp] theorem strictPairCorrelation_apply_zero_zero
    (rho : ℝ) (hrho : |rho| < 1) :
    (strictPairCorrelation rho hrho).val 0 0 = 1 := by
  rfl

@[simp] theorem strictPairCorrelation_apply_one_one
    (rho : ℝ) (hrho : |rho| < 1) :
    (strictPairCorrelation rho hrho).val 1 1 = 1 := by
  rfl

@[simp] theorem strictPairCorrelation_apply_zero_one
    (rho : ℝ) (hrho : |rho| < 1) :
    (strictPairCorrelation rho hrho).val 0 1 = rho := by
  rfl

@[simp] theorem strictPairCorrelation_apply_one_zero
    (rho : ℝ) (hrho : |rho| < 1) :
    (strictPairCorrelation rho hrho).val 1 0 = rho := by
  rfl

/-- Difference of the two log squared radii in the canonical strict pair. -/
def pairLogRadiusDifference (m : ℕ) (rho : ℝ) (hrho : |rho| < 1) :
    GaussianData m 2 → ℝ := fun z ↦
  Real.log (GeneralRDecomposition.Q (strictPairCorrelation rho hrho) z 1) -
    Real.log (GeneralRDecomposition.Q (strictPairCorrelation rho hrho) z 0)

/-- A dimension-uniform variance bound for the log-radius difference of a
strict Gaussian pair.  The leading term vanishes as `rho² ↑ 1`; the
`8 / m²` term is the already verified nonlinear Kibble remainder. -/
theorem variance_pairLogRadiusDifference_le
    {m : ℕ} (hm : 0 < m) (rho : ℝ) (hrho : |rho| < 1) :
    Var[pairLogRadiusDifference m rho hrho;
        standardGaussianDataMeasure m 2] ≤
      4 * (1 - rho ^ 2) / (m : ℝ) + 8 / (m : ℝ) ^ 2 := by
  let R : CorrelationMatrix 2 := strictPairCorrelation rho hrho
  let X : GaussianData m 2 → ℝ := fun z ↦
    Real.log (GeneralRDecomposition.Q R z 1)
  let Y : GaussianData m 2 → ℝ := fun z ↦
    Real.log (GeneralRDecomposition.Q R z 0)
  have hX : MemLp X 2 (standardGaussianDataMeasure m 2) := by
    simpa [X] using GeneralRDecomposition.memLp_log_Q_two hm R (1 : Fin 2)
  have hY : MemLp Y 2 (standardGaussianDataMeasure m 2) := by
    simpa [Y] using GeneralRDecomposition.memLp_log_Q_two hm R (0 : Fin 2)
  have hvarX : Var[X; standardGaussianDataMeasure m 2] =
      trigammaSeries ((m : ℝ) / 2) := by
    simpa [X] using GeneralRDecomposition.variance_log_Q_eq_trigamma hm R (1 : Fin 2)
  have hvarY : Var[Y; standardGaussianDataMeasure m 2] =
      trigammaSeries ((m : ℝ) / 2) := by
    simpa [Y] using GeneralRDecomposition.variance_log_Q_eq_trigamma hm R (0 : Fin 2)
  have hcovLower : 2 * rho ^ 2 / (m : ℝ) ≤
      cov[X, Y; standardGaussianDataMeasure m 2] := by
    have h := (actual_logRadiusCovariance_remainder_bounds hm R
      (1 : Fin 2) (0 : Fin 2)).1
    simpa [X, Y, R] using h
  have ha : 0 < (m : ℝ) / 2 := by positivity
  have htrig := trigammaSeries_le_one_div_add_one_div_sq ha
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have htrigUpper : trigammaSeries ((m : ℝ) / 2) ≤
      2 / (m : ℝ) + 4 / (m : ℝ) ^ 2 := by
    calc
      trigammaSeries ((m : ℝ) / 2) ≤
          1 / ((m : ℝ) / 2) + 1 / ((m : ℝ) / 2) ^ 2 := htrig
      _ = 2 / (m : ℝ) + 4 / (m : ℝ) ^ 2 := by
        field_simp [hm0]
        ring
  have hvar := variance_sub hX hY
  change Var[X - Y; standardGaussianDataMeasure m 2] ≤ _
  rw [hvar, hvarX, hvarY]
  calc
    trigammaSeries ((m : ℝ) / 2) -
          2 * cov[X, Y; standardGaussianDataMeasure m 2] +
          trigammaSeries ((m : ℝ) / 2) ≤
        2 * (2 / (m : ℝ) + 4 / (m : ℝ) ^ 2) -
          2 * (2 * rho ^ 2 / (m : ℝ)) := by linarith
    _ = 4 * (1 - rho ^ 2) / (m : ℝ) + 8 / (m : ℝ) ^ 2 := by ring

/-- A nonzero signal correlation produces a strict radius correlation
`sqrt (1-rho²)`. -/
theorem abs_sqrt_one_sub_sq_lt_one
    (rho : ℝ) (hrho : |rho| < 1) (hrho0 : rho ≠ 0) :
    |Real.sqrt (1 - rho ^ 2)| < 1 := by
  have hsq_le : rho ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one rho).2 hrho.le
  have hs : 0 ≤ Real.sqrt (1 - rho ^ 2) := Real.sqrt_nonneg _
  have hsSq : (Real.sqrt (1 - rho ^ 2)) ^ 2 = 1 - rho ^ 2 := by
    rw [Real.sq_sqrt]
    exact sub_nonneg.mpr hsq_le
  rw [abs_of_nonneg hs]
  nlinarith [sq_pos_of_ne_zero hrho0]

/-- Signal-parameter form of the preceding bound.  If the radius correlation
is `sqrt (1-rho²)`, the difference variance is at most
`4 rho² / m + 8 / m²`. -/
theorem variance_pairLogRadiusDifference_sqrt_one_sub_sq_le
    {m : ℕ} (hm : 0 < m) (rho : ℝ) (hrho : |rho| < 1)
    (hrho0 : rho ≠ 0) :
    Var[pairLogRadiusDifference m (Real.sqrt (1 - rho ^ 2))
          (abs_sqrt_one_sub_sq_lt_one rho hrho hrho0);
        standardGaussianDataMeasure m 2] ≤
      4 * rho ^ 2 / (m : ℝ) + 8 / (m : ℝ) ^ 2 := by
  let hroot : |Real.sqrt (1 - rho ^ 2)| < 1 :=
    abs_sqrt_one_sub_sq_lt_one rho hrho hrho0
  have h := variance_pairLogRadiusDifference_le hm
    (Real.sqrt (1 - rho ^ 2)) hroot
  have hsSq : (Real.sqrt (1 - rho ^ 2)) ^ 2 = 1 - rho ^ 2 := by
    rw [Real.sq_sqrt]
    exact sub_nonneg.mpr ((sq_le_one_iff_abs_le_one rho).2 hrho.le)
  simpa [hroot, hsSq] using h

/-- The centered random part of the logarithmic correction associated with a
nonzero planted correlation `rho`. -/
def signalPairLogRadiusCorrection (m : ℕ) (rho : ℝ)
    (hrho : |rho| < 1) (hrho0 : rho ≠ 0) : GaussianData m 2 → ℝ :=
  pairLogRadiusDifference m (Real.sqrt (1 - rho ^ 2))
    (abs_sqrt_one_sub_sq_lt_one rho hrho hrho0)

theorem measurable_signalPairLogRadiusCorrection
    (m : ℕ) (rho : ℝ) (hrho : |rho| < 1) (hrho0 : rho ≠ 0) :
    Measurable (signalPairLogRadiusCorrection m rho hrho hrho0) := by
  unfold signalPairLogRadiusCorrection pairLogRadiusDifference
  exact ((GeneralRDecomposition.measurable_Q _ _).log).sub
    ((GeneralRDecomposition.measurable_Q _ _).log)

theorem memLp_signalPairLogRadiusCorrection_two
    {m : ℕ} (hm : 0 < m) (rho : ℝ)
    (hrho : |rho| < 1) (hrho0 : rho ≠ 0) :
    MemLp (signalPairLogRadiusCorrection m rho hrho hrho0) 2
      (standardGaussianDataMeasure m 2) := by
  unfold signalPairLogRadiusCorrection pairLogRadiusDifference
  exact (GeneralRDecomposition.memLp_log_Q_two hm _ _).sub
    (GeneralRDecomposition.memLp_log_Q_two hm _ _)

/-- The random radius correction is exactly centered. -/
theorem integral_signalPairLogRadiusCorrection_eq_zero
    {m : ℕ} (hm : 0 < m) (rho : ℝ)
    (hrho : |rho| < 1) (hrho0 : rho ≠ 0) :
    ∫ z, signalPairLogRadiusCorrection m rho hrho hrho0 z
        ∂standardGaussianDataMeasure m 2 = 0 := by
  let c : ℝ := Real.sqrt (1 - rho ^ 2)
  let hc : |c| < 1 := abs_sqrt_one_sub_sq_lt_one rho hrho hrho0
  let R : CorrelationMatrix 2 := strictPairCorrelation c hc
  have h1 := GeneralRDecomposition.integral_log_Q_eq_chiSquareLogMean
    hm R (1 : Fin 2)
  have h0 := GeneralRDecomposition.integral_log_Q_eq_chiSquareLogMean
    hm R (0 : Fin 2)
  have hi1 := GeneralRDecomposition.integrable_log_Q hm R (1 : Fin 2)
  have hi0 := GeneralRDecomposition.integrable_log_Q hm R (0 : Fin 2)
  simp only [signalPairLogRadiusCorrection, pairLogRadiusDifference]
  rw [integral_sub hi1 hi0, h1, h0, sub_self]

/-- The centered signal correction inherits the all-dimension variance bound. -/
theorem variance_signalPairLogRadiusCorrection_le
    {m : ℕ} (hm : 0 < m) (rho : ℝ)
    (hrho : |rho| < 1) (hrho0 : rho ≠ 0) :
    Var[signalPairLogRadiusCorrection m rho hrho hrho0;
        standardGaussianDataMeasure m 2] ≤
      4 * rho ^ 2 / (m : ℝ) + 8 / (m : ℝ) ^ 2 := by
  exact variance_pairLogRadiusDifference_sqrt_one_sub_sq_le
    hm rho hrho hrho0

end

end LogdetLean.Coherence
