import LogdetLean.Coherence.StandardGaussianMills
import LogdetLean.Coherence.NoncentralPearsonRateAlgebra
import Mathlib.Tactic
/-!
# The Gaussian denominator in the noncentral-Pearson relative approximation

The two-sided comparison is normalized by
`Q (q - lambda) + Q (q + lambda)`.  This file proves, without any
probabilistic assumption, that the exponentially small discarded-radius
term is negligible relative to that denominator throughout the full
coherence-scale window.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real MeasureTheory ProbabilityTheory Set
open scoped Topology Real

/-- The two-sided Gaussian tail which normalizes the noncentral Pearson
moderate-deviation approximation. -/
def pearsonMDGaussianTailDenominator (q lambda : ℝ) : ℝ :=
  standardGaussianUpperTail (q - lambda) +
    standardGaussianUpperTail (q + lambda)

theorem pearsonMDGaussianTailDenominator_pos (q lambda : ℝ) :
    0 < pearsonMDGaussianTailDenominator q lambda := by
  unfold pearsonMDGaussianTailDenominator
  exact add_pos (standardGaussianUpperTail_pos _) (standardGaussianUpperTail_pos _)

/-- The denominator dominates the tail at its largest possible argument.
This elementary reduction is what makes one lower Mills bound sufficient
for both signs of the noncentrality parameter. -/
theorem upperTail_q_add_abs_le_pearsonMDGaussianTailDenominator
    (q lambda : ℝ) :
    standardGaussianUpperTail (q + |lambda|) ≤
      pearsonMDGaussianTailDenominator q lambda := by
  have hlambda : lambda ≤ |lambda| := le_abs_self lambda
  have hcdf := monotone_cdf (gaussianReal 0 1)
    (add_le_add_left hlambda q)
  have htail : standardGaussianUpperTail (q + |lambda|) ≤
      standardGaussianUpperTail (q + lambda) := by
    unfold standardGaussianUpperTail
    have hcdf' : cdf (gaussianReal 0 1) (q + lambda) ≤
        cdf (gaussianReal 0 1) (q + |lambda|) := by
      simpa [add_comm] using hcdf
    linarith
  unfold pearsonMDGaussianTailDenominator
  exact htail.trans (le_add_of_nonneg_left
    (standardGaussianUpperTail_nonneg (q - lambda)))

/-- A finite lower envelope for the two-sided Gaussian denominator on the
coherence scale.  Constants are explicit but intentionally non-optimal. -/
theorem pearsonMDGaussianTailDenominator_lower_envelope
    {C q lambda : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hscale : q + |lambda| ≤
      C * Real.sqrt (Real.log (p : ℝ))) :
    (1 / (1 + C * Real.sqrt (Real.log (p : ℝ)))) *
        (Real.exp (-2) * (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(C ^ 2 * Real.log (p : ℝ)) / 2)) ≤
      pearsonMDGaussianTailDenominator q lambda := by
  let t : ℝ := q + |lambda|
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have hright0 : 0 ≤ C * Real.sqrt (Real.log (p : ℝ)) := by positivity
  have ht2 : t ^ 2 ≤ C ^ 2 * Real.log (p : ℝ) := by
    have hsquare := sq_le_sq₀ ht0 hright0 |>.2 hscale
    simpa [mul_pow, Real.sq_sqrt hlog0] using hsquare
  have hdenpos : 0 < 1 + t := by linarith
  have hbigdenpos :
      0 < 1 + C * Real.sqrt (Real.log (p : ℝ)) := by positivity
  have hinv :
      1 / (1 + C * Real.sqrt (Real.log (p : ℝ))) ≤ 1 / (1 + t) := by
    exact one_div_le_one_div_of_le hdenpos (by linarith)
  have hexp :
      Real.exp (-(C ^ 2 * Real.log (p : ℝ)) / 2) ≤
        Real.exp (-t ^ 2 / 2) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hpdf :
      (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(C ^ 2 * Real.log (p : ℝ)) / 2) ≤
        gaussianPDFReal 0 1 t := by
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hprod :
      (1 / (1 + C * Real.sqrt (Real.log (p : ℝ)))) *
          (Real.exp (-2) * (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(C ^ 2 * Real.log (p : ℝ)) / 2)) ≤
        (1 / (1 + t)) *
          (Real.exp (-2) * gaussianPDFReal 0 1 t) := by
    have hrightfactor0 : 0 ≤ Real.exp (-2) * gaussianPDFReal 0 1 t := by
      exact mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _)
    have hpdf' :
        Real.exp (-2) *
            ((Real.sqrt (2 * Real.pi))⁻¹ *
              Real.exp (-(C ^ 2 * Real.log (p : ℝ)) / 2)) ≤
          Real.exp (-2) * gaussianPDFReal 0 1 t :=
      mul_le_mul_of_nonneg_left hpdf (Real.exp_pos _).le
    calc
      (1 / (1 + C * Real.sqrt (Real.log (p : ℝ)))) *
          (Real.exp (-2) * (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(C ^ 2 * Real.log (p : ℝ)) / 2))
          ≤ (1 / (1 + C * Real.sqrt (Real.log (p : ℝ)))) *
              (Real.exp (-2) * gaussianPDFReal 0 1 t) := by
            exact mul_le_mul_of_nonneg_left (by
              simpa [mul_assoc] using hpdf') (by positivity)
      _ ≤ (1 / (1 + t)) *
              (Real.exp (-2) * gaussianPDFReal 0 1 t) := by
            exact mul_le_mul_of_nonneg_right hinv hrightfactor0
  calc
    _ ≤ (1 / (1 + t)) *
          (Real.exp (-2) * gaussianPDFReal 0 1 t) := hprod
    _ ≤ standardGaussianUpperTail t :=
      exp_neg_two_mul_pdf_div_one_add_le_upperTail ht0
    _ ≤ pearsonMDGaussianTailDenominator q lambda := by
      simpa [t] using
        upperTail_q_add_abs_le_pearsonMDGaussianTailDenominator q lambda

/-- Explicit quotient envelope for the discarded-radius probability.
The right-hand side is a constant times the deterministic discarded-chi
rate, apart from the harmless factor `1 + C sqrt(log p)`. -/
theorem pearsonMDDiscardedExp_div_gaussianTailDenominator_le
    {C L q lambda : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hscale : q + |lambda| ≤
      C * Real.sqrt (Real.log (p : ℝ))) :
    8 * Real.exp (-2 * (L * Real.log (p : ℝ))) /
        pearsonMDGaussianTailDenominator q lambda ≤
      8 * Real.exp 2 * Real.sqrt (2 * Real.pi) *
        (1 + C * Real.sqrt (Real.log (p : ℝ))) *
        (p : ℝ) ^ (C ^ 2 / 2 - 2 * L) := by
  have hlower := pearsonMDGaussianTailDenominator_lower_envelope
    hp hC hq hscale
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hbigdenpos :
      0 < 1 + C * Real.sqrt (Real.log (p : ℝ)) := by positivity
  have hsqrtpos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsmallpos :
      0 < (1 / (1 + C * Real.sqrt (Real.log (p : ℝ)))) *
        (Real.exp (-2) * (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(C ^ 2 * Real.log (p : ℝ)) / 2)) := by positivity
  have hnum0 :
      0 ≤ 8 * Real.exp (-2 * (L * Real.log (p : ℝ))) := by positivity
  calc
    8 * Real.exp (-2 * (L * Real.log (p : ℝ))) /
          pearsonMDGaussianTailDenominator q lambda
        ≤ 8 * Real.exp (-2 * (L * Real.log (p : ℝ))) /
          ((1 / (1 + C * Real.sqrt (Real.log (p : ℝ)))) *
            (Real.exp (-2) * (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.exp (-(C ^ 2 * Real.log (p : ℝ)) / 2))) := by
          exact div_le_div_of_nonneg_left hnum0 hsmallpos hlower
    _ = 8 * Real.exp 2 * Real.sqrt (2 * Real.pi) *
          (1 + C * Real.sqrt (Real.log (p : ℝ))) *
          (p : ℝ) ^ (C ^ 2 / 2 - 2 * L) := by
      rw [Real.rpow_def_of_pos hpR]
      field_simp [hbigdenpos.ne', hsqrtpos.ne']
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- The exact denominator-normalized discarded-radius term tends to zero
under the sharp moderate-deviation exponent gap. -/
theorem tendsto_pearsonMDDiscardedExp_div_gaussianTailDenominator_zero
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hgap : C ^ 2 / 2 < L)
    {qseq lambdaSeq : ℕ → ℝ}
    (hq : ∀ᶠ p in atTop, 0 ≤ qseq p)
    (hscale : ∀ᶠ p in atTop,
      qseq p + |lambdaSeq p| ≤
        C * Real.sqrt (Real.log (p : ℝ))) :
    Tendsto (fun p : ℕ ↦
      8 * Real.exp (-2 * (L * Real.log (p : ℝ))) /
        pearsonMDGaussianTailDenominator (qseq p) (lambdaSeq p))
      atTop (nhds 0) := by
  have hgap2 : C ^ 2 / 2 < 2 * L := by nlinarith
  have hrate := tendsto_pearsonMDDiscardedChiRate_zero hgap2
  let K : ℝ := 8 * Real.exp 2 * Real.sqrt (2 * Real.pi) * (1 + C)
  have hKrate : Tendsto (fun p : ℕ ↦
      K * pearsonMDDiscardedChiRate C (2 * L) p)
      atTop (nhds 0) := by
    simpa using hrate.const_mul K
  apply squeeze_zero'
  · filter_upwards with p
    exact div_nonneg (by positivity)
      (pearsonMDGaussianTailDenominator_pos _ _).le
  · filter_upwards [eventually_ge_atTop 3, hq, hscale]
      with p hp hqp hscalep
    have hp1 : 1 ≤ p := by omega
    have hlog1 : 1 ≤ Real.log (p : ℝ) := by
      have he : Real.exp 1 < (3 : ℝ) := by
        exact Real.exp_one_lt_d9.trans (by norm_num)
      have h3p : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (p : ℝ))).2
        (he.le.trans h3p)
    have hsqrt1 : 1 ≤ Real.sqrt (Real.log (p : ℝ)) := by
      exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by simpa using hlog1)
    have hfinite :=
      pearsonMDDiscardedExp_div_gaussianTailDenominator_le
        (L := L) hp1 hC hqp hscalep
    calc
      8 * Real.exp (-2 * (L * Real.log (p : ℝ))) /
          pearsonMDGaussianTailDenominator (qseq p) (lambdaSeq p)
          ≤ 8 * Real.exp 2 * Real.sqrt (2 * Real.pi) *
              (1 + C * Real.sqrt (Real.log (p : ℝ))) *
              (p : ℝ) ^ (C ^ 2 / 2 - 2 * L) := hfinite
      _ ≤ K * pearsonMDDiscardedChiRate C (2 * L) p := by
        unfold K pearsonMDDiscardedChiRate
        have hpow0 : 0 ≤ (p : ℝ) ^ (C ^ 2 / 2 - 2 * L) :=
          Real.rpow_nonneg (Nat.cast_nonneg p) _
        have hsqrt0 : 0 ≤ Real.sqrt (Real.log (p : ℝ)) :=
          Real.sqrt_nonneg _
        have hfactor :
            1 + C * Real.sqrt (Real.log (p : ℝ)) ≤
              (1 + C) * Real.sqrt (Real.log (p : ℝ)) := by
          nlinarith
        have hconst0 :
            0 ≤ 8 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
        calc
          8 * Real.exp 2 * Real.sqrt (2 * Real.pi) *
                (1 + C * Real.sqrt (Real.log (p : ℝ))) *
                (p : ℝ) ^ (C ^ 2 / 2 - 2 * L)
              ≤ 8 * Real.exp 2 * Real.sqrt (2 * Real.pi) *
                ((1 + C) * Real.sqrt (Real.log (p : ℝ))) *
                (p : ℝ) ^ (C ^ 2 / 2 - 2 * L) := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hfactor hconst0) hpow0
          _ = 8 * Real.exp 2 * Real.sqrt (2 * Real.pi) *
                (1 + C) *
                (Real.sqrt (Real.log (p : ℝ)) *
                  (p : ℝ) ^ (C ^ 2 / 2 - 2 * L)) := by ring
  · exact hKrate

end

end LogdetLean.Coherence
