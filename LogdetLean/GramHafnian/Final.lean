import LogdetLean.GramHafnian.ExactGramMoments
import LogdetLean.GramHafnian.AsymptoticCentralBaseline
import LogdetLean.GramHafnian.LogBoundaryConverse
import LogdetLean.GramHafnian.BesselI0Identity
/-!
# Paper-facing Gaussian Gram--hafnian results

This module collects the literal Gaussian first and fourth moments, their
normalized ratio, the exact finite correction, the strongest unified
nonasymptotic bounds, and the proved asymptotic regimes.

The crossover function `besselMajorant` is the entire series defined in
`FiniteBesselMajorant`.  The project separately defines the literal standard
series `modifiedBesselI0Series` and proves
`besselMajorant y = exp y * modifiedBesselI0Series y`.  Mathlib does not
currently expose a modified-Bessel `I₀` special-function object, so this is a
proved identity between explicit project series rather than an appeal to a
Mathlib `I₀` API.
-/

open scoped Topology
open Filter Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- Literal Gaussian Gram--hafnian `M₁ = E |haf(XᵀX)|²`. -/
theorem literalGaussianGramHafnian_M1
    (k n : ℕ) (hk : 0 < k) :
    actualGramFirstMomentReal k n = closedFirstMoment k n :=
  actualGramFirstMomentReal_eq_closedFirstMoment k n hk

/-- Literal Gaussian Gram--hafnian `M₂ = E |haf(XᵀX)|⁴`. -/
theorem literalGaussianGramHafnian_M2
    (k n : ℕ) (hk : 0 < k) :
    actualGramFourthMomentReal k n = closedFourthMoment k n :=
  actualGramFourthMomentReal_eq_closedFourthMoment k n hk

/-- Exact bridge from the literal Gaussian observable to the deterministic
finite ratio used by every bound and asymptotic theorem below. -/
theorem literalGaussianGramHafnian_normalizedRatio
    (k n : ℕ) (hk : 0 < k) :
    actualGramSecondMomentRatio k n = gramSecondMomentRatio k n :=
  actualGramSecondMomentRatio_eq_gramSecondMomentRatio k n hk

/-- Exact special-function presentation using the project's literal standard
modified-Bessel `I₀` series.  This is not a reference to a Mathlib `I₀` API. -/
theorem gramHafnian_besselMajorant_eq_exp_mul_modifiedBesselI0Series
    (y : ℝ) :
    besselMajorant y =
      Real.exp y * modifiedBesselI0Series y :=
  besselMajorant_eq_exp_mul_modifiedBesselI0Series y

/-- Exact terminating `₃F₂` representation of the finite correction. -/
theorem gramHafnian_finiteCorrection_eq_threeFtwo
    (k n : ℕ) (hk : 0 < k) :
    finiteCorrection k n =
      terminatingThreeFtwo n (-(n : ℝ)) (-(n : ℝ)) (1 / 2 : ℝ)
        1 ((k : ℝ) / 2) 1 :=
  finiteCorrection_eq_terminatingThreeFtwo k n hk

/-- One paper-facing finite bracket combining the Bessel-series,
exponential, and maximum-summand lower bounds with the maximum-summand upper
bound. -/
theorem gramHafnian_unified_finite_ratio_bounds
    (k n jStar : ℕ) (hk : 0 < k) (hjStar : jStar ≤ n)
    (hmax : ∀ j, j ≤ n → finiteTerm k n j ≤ finiteTerm k n jStar) :
    max
        (max
          (centralBaseline n / besselMajorant ((n : ℝ) ^ 2 / k))
          (centralBaseline n *
            Real.exp (-((2 : ℝ) * (n : ℝ) ^ 2 / k))))
        (centralBaseline n /
          ((n + 1 : ℝ) * finiteTerm k n jStar)) ≤
        gramSecondMomentRatio k n ∧
      gramSecondMomentRatio k n ≤
        centralBaseline n / finiteTerm k n jStar := by
  have hmaxBracket :=
    max_summand_ratio_bracket k n jStar hk hjStar hmax
  constructor
  · refine max_le (max_le ?_ ?_) hmaxBracket.1
    · exact baseline_div_besselMajorant_le_gramSecondMomentRatio k n hk
    · exact baseline_mul_exp_neg_le_gramSecondMomentRatio k n hk
  · exact hmaxBracket.2

/-- Literal-Gaussian form of the unified finite bracket. -/
theorem literalGaussianGramHafnian_unified_finite_ratio_bounds
    (k n jStar : ℕ) (hk : 0 < k) (hjStar : jStar ≤ n)
    (hmax : ∀ j, j ≤ n → finiteTerm k n j ≤ finiteTerm k n jStar) :
    max
        (max
          (centralBaseline n / besselMajorant ((n : ℝ) ^ 2 / k))
          (centralBaseline n *
            Real.exp (-((2 : ℝ) * (n : ℝ) ^ 2 / k))))
        (centralBaseline n /
          ((n + 1 : ℝ) * finiteTerm k n jStar)) ≤
        actualGramSecondMomentRatio k n ∧
      actualGramSecondMomentRatio k n ≤
        centralBaseline n / finiteTerm k n jStar := by
  rw [actualGramSecondMomentRatio_eq_gramSecondMomentRatio k n hk]
  exact gramHafnian_unified_finite_ratio_bounds k n jStar hk hjStar hmax

/-- A one-summand geometric certificate forcing an explicit exponentially
small upper bound for the deterministic ratio. -/
theorem gramHafnian_ratio_le_two_pow_neg_of_geometric_certificate
    (k n j : ℕ) (hk : 0 < k) (hj : j ≤ n)
    (hscale :
      (2 : ℝ) * (j : ℝ) * ((k + 2 * j : ℕ) : ℝ) ≤
        ((n + 1 - j : ℕ) : ℝ) ^ 2) :
    gramSecondMomentRatio k n ≤ 1 / (2 : ℝ) ^ j :=
  gramSecondMomentRatio_le_two_pow_neg_of_geometric_certificate
    k n j hk hj hscale

/-- Literal-Gaussian form of the geometric one-summand certificate. -/
theorem literalGaussianGramHafnian_ratio_le_two_pow_neg_of_geometric_certificate
    (k n j : ℕ) (hk : 0 < k) (hj : j ≤ n)
    (hscale :
      (2 : ℝ) * (j : ℝ) * ((k + 2 * j : ℕ) : ℝ) ≤
        ((n + 1 - j : ℕ) : ℝ) ^ 2) :
    actualGramSecondMomentRatio k n ≤ 1 / (2 : ℝ) ^ j := by
  rw [actualGramSecondMomentRatio_eq_gramSecondMomentRatio k n hk]
  exact gramHafnian_ratio_le_two_pow_neg_of_geometric_certificate
    k n j hk hj hscale

/-- Sharp quadratic-window limit of the exact finite correction.  The limit
is the explicitly defined series `besselMajorant (1/c)`. -/
theorem gramHafnian_finiteCorrection_quadratic_crossover
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦ finiteCorrection (kseq n) n)
      atTop (nhds (besselMajorant (1 / c))) :=
  tendsto_finiteCorrection_quadratic_crossover kseq c hc hkTop haspect

/-- Conventional absolute normalization of the sharp quadratic crossover. -/
theorem gramHafnian_ratio_quadratic_crossover
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦
      gramSecondMomentRatio (kseq n) n * Real.sqrt (Real.pi * n))
      atTop (nhds (1 / besselMajorant (1 / c))) :=
  tendsto_gramSecondMomentRatio_mul_sqrt_pi_mul_quadratic_crossover
    kseq c hc hkTop haspect

/-- Literal-Gaussian form of the sharp quadratic crossover. -/
theorem literalGaussianGramHafnian_ratio_quadratic_crossover
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦
      actualGramSecondMomentRatio (kseq n) n * Real.sqrt (Real.pi * n))
      atTop (nhds (1 / besselMajorant (1 / c))) := by
  apply (gramHafnian_ratio_quadratic_crossover
    kseq c hc hkTop haspect).congr'
  filter_upwards [hkTop.eventually (eventually_ge_atTop 1)] with n hn
  rw [actualGramSecondMomentRatio_eq_gramSecondMomentRatio
    (kseq n) n hn]

/-- Sharp correction-factor crossover in the project's literal
`exp(y) * I₀(y)` series presentation. -/
theorem gramHafnian_finiteCorrection_quadratic_crossover_I0Series
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦ finiteCorrection (kseq n) n)
      atTop (nhds
        (Real.exp (1 / c) * modifiedBesselI0Series (1 / c))) := by
  simpa only [besselMajorant_eq_exp_mul_modifiedBesselI0Series] using
    gramHafnian_finiteCorrection_quadratic_crossover
      kseq c hc hkTop haspect

/-- Sharp normalized-ratio crossover in the project's literal
`exp(y) * I₀(y)` series presentation. -/
theorem gramHafnian_ratio_quadratic_crossover_I0Series
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦
      gramSecondMomentRatio (kseq n) n * Real.sqrt (Real.pi * n))
      atTop (nhds
        (1 /
          (Real.exp (1 / c) * modifiedBesselI0Series (1 / c)))) := by
  simpa only [besselMajorant_eq_exp_mul_modifiedBesselI0Series] using
    gramHafnian_ratio_quadratic_crossover kseq c hc hkTop haspect

/-- Literal-Gaussian sharp crossover in the project's literal
`exp(y) * I₀(y)` series presentation. -/
theorem literalGaussianGramHafnian_ratio_quadratic_crossover_I0Series
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦
      actualGramSecondMomentRatio (kseq n) n * Real.sqrt (Real.pi * n))
      atTop (nhds
        (1 /
          (Real.exp (1 / c) * modifiedBesselI0Series (1 / c)))) := by
  simpa only [besselMajorant_eq_exp_mul_modifiedBesselI0Series] using
    literalGaussianGramHafnian_ratio_quadratic_crossover
      kseq c hc hkTop haspect

/-- In the superquadratic regime the exact normalized ratio is asymptotic to
the central-binomial baseline. -/
theorem gramHafnian_ratio_superquadratic_baseline
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hratio : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      gramSecondMomentRatio (kseq n) n / centralBaseline n)
      atTop (nhds 1) :=
  tendsto_gramSecondMomentRatio_div_baseline_one kseq hk hratio

/-- Literal-Gaussian form of the superquadratic baseline equivalence. -/
theorem literalGaussianGramHafnian_ratio_superquadratic_baseline
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hratio : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (kseq n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      actualGramSecondMomentRatio (kseq n) n / centralBaseline n)
      atTop (nhds 1) := by
  apply (gramHafnian_ratio_superquadratic_baseline kseq hk hratio).congr'
  filter_upwards [hk] with n hn
  rw [actualGramSecondMomentRatio_eq_gramSecondMomentRatio
    (kseq n) n hn]

/-- Proved sufficient half of the logarithmic weak-anticoncentration
boundary. -/
theorem gramHafnian_hasWeakAntiConcentration_of_log_scale
    (kseq : ℕ → ℕ) (d : ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ 2 / (kseq n : ℝ) ≤
        (d : ℝ) * Real.log n) :
    HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio (kseq n) n) :=
  hasWeakAntiConcentration_of_eventually_log_scale kseq d hk hscale

/-- Literal-Gaussian form of the proved sufficient logarithmic condition. -/
theorem literalGaussianGramHafnian_hasWeakAntiConcentration_of_log_scale
    (kseq : ℕ → ℕ) (d : ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ 2 / (kseq n : ℝ) ≤
        (d : ℝ) * Real.log n) :
    HasWeakAntiConcentration
      (fun n ↦ actualGramSecondMomentRatio (kseq n) n) := by
  rcases gramHafnian_hasWeakAntiConcentration_of_log_scale
      kseq d hk hscale with ⟨C, hC, exponent, hbound⟩
  refine ⟨C, hC, exponent, ?_⟩
  filter_upwards [hbound, hk] with n hn hkn
  rw [actualGramSecondMomentRatio_eq_gramSecondMomentRatio
    (kseq n) n hkn]
  exact hn

/-- Converse order regime at the logarithmic scale: if
`k_n * log n / n² → 0`, then no inverse-polynomial lower bound can hold. -/
theorem gramHafnian_not_hasWeakAntiConcentration_of_log_dimension_ratio_zero
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hratio : Tendsto (fun n : ℕ ↦
      (kseq n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0)) :
    ¬ HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio (kseq n) n) :=
  not_hasWeakAntiConcentration_of_log_dimension_ratio_zero kseq hk hratio

/-- Literal-Gaussian form of the logarithmic subcritical failure theorem. -/
theorem literalGaussianGramHafnian_not_hasWeakAntiConcentration_of_log_dimension_ratio_zero
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hratio : Tendsto (fun n : ℕ ↦
      (kseq n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0)) :
    ¬ HasWeakAntiConcentration
      (fun n ↦ actualGramSecondMomentRatio (kseq n) n) := by
  intro hactual
  apply gramHafnian_not_hasWeakAntiConcentration_of_log_dimension_ratio_zero
    kseq hk hratio
  rcases hactual with ⟨C, hC, exponent, hbound⟩
  refine ⟨C, hC, exponent, ?_⟩
  filter_upwards [hbound, hk] with n hn hkn
  rw [← actualGramSecondMomentRatio_eq_gramSecondMomentRatio
    (kseq n) n hkn]
  exact hn

/-- Exact rank-one failure of inverse-polynomial weak anticoncentration. -/
theorem gramHafnian_not_hasWeakAntiConcentration_rank_one :
    ¬ HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio 1 n) :=
  not_hasWeakAntiConcentration_rank_one

/-- Literal-Gaussian rank-one failure of weak anticoncentration. -/
theorem literalGaussianGramHafnian_not_hasWeakAntiConcentration_rank_one :
    ¬ HasWeakAntiConcentration
      (fun n ↦ actualGramSecondMomentRatio 1 n) := by
  intro hactual
  apply gramHafnian_not_hasWeakAntiConcentration_rank_one
  rcases hactual with ⟨C, hC, exponent, hbound⟩
  refine ⟨C, hC, exponent, ?_⟩
  filter_upwards [hbound] with n hn
  rw [← actualGramSecondMomentRatio_eq_gramSecondMomentRatio 1 n (by omega)]
  exact hn

end

end LogdetLean.GramHafnian
