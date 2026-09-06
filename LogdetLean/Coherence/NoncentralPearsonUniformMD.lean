import LogdetLean.Coherence.NoncentralPearsonFiniteMD
import LogdetLean.Coherence.NoncentralPearsonRateAlgebra
import LogdetLean.Coherence.NoncentralPearsonTailDenominator
import Mathlib.Tactic
/-!
# Uniform noncentral Pearson moderate deviations

This file turns the finite-sample two-sided Pearson comparison into its
sequential triangular-array form.  The probability in the numerator is the
exact probability under two independent standard Gaussian columns; the
correlated second column is then formed with population correlation `rho`.

Sequential uniformity is the usual exact formulation of a uniform
moderate-deviation result: every admissible choice of dimensions, thresholds,
and local correlations has relative error tending to zero.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Topology

/-- The two-sided Gaussian reference tail under noncentrality `lambda`. -/
def noncentralGaussianTwoSidedTail (q lambda : ℝ) : ℝ :=
  standardGaussianUpperTail (q - lambda) +
    standardGaussianUpperTail (q + lambda)

theorem noncentralGaussianTwoSidedTail_pos (q lambda : ℝ) :
    0 < noncentralGaussianTwoSidedTail q lambda := by
  unfold noncentralGaussianTwoSidedTail
  exact add_pos (standardGaussianUpperTail_pos _)
    (standardGaussianUpperTail_pos _)

/-- Monotonicity of the symmetric exponential envelope used in the finite
Gaussian-tail perturbation bound. -/
theorem exp_sub_exp_neg_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp a - Real.exp (-a) ≤ Real.exp b - Real.exp (-b) := by
  have hup : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have hlow : Real.exp (-b) ≤ Real.exp (-a) :=
    Real.exp_le_exp.mpr (neg_le_neg hab)
  linarith

theorem exp_sub_exp_neg_nonneg {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ Real.exp a - Real.exp (-a) := by
  exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))

/-- The deterministic exponent appearing in the genuine finite comparison.
Unlike the older rate-only profile, this uses the exact global hazard
constant `exp 2` from `StandardGaussianMills`. -/
def pearsonMDFiniteTailExponent
    (L q lambda : ℝ) (m p : ℕ) : ℝ :=
  let delta := pearsonMDArgumentPerturbation L q lambda m p
  Real.exp 2 * delta * (1 + q + |lambda| + delta)

/-- Relative Gaussian-envelope part of the finite Pearson comparison. -/
def pearsonMDFiniteGaussianEnvelope
    (L q lambda : ℝ) (m p : ℕ) : ℝ :=
  Real.exp (pearsonMDFiniteTailExponent L q lambda m p) -
    Real.exp (-pearsonMDFiniteTailExponent L q lambda m p)

/-- The exact finite Gaussian perturbation envelope vanishes throughout the
full coherence moderate-deviation window. -/
theorem tendsto_pearsonMDFiniteGaussianEnvelope_zero
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    {mseq : ℕ → ℕ} {qseq lambdaSeq : ℕ → ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hq : ∀ᶠ p in atTop, 0 ≤ qseq p)
    (hscale : ∀ᶠ p in atTop,
      qseq p + |lambdaSeq p| ≤
        C * Real.sqrt (Real.log (p : ℝ))) :
    Tendsto (fun p : ℕ ↦
      pearsonMDFiniteGaussianEnvelope
        L (qseq p) (lambdaSeq p) (mseq p) p)
      atTop (nhds 0) := by
  have hdelta := tendsto_pearsonMDArgumentPerturbation_zero
    (L := L) hC hadm hq hscale
  have hcross := tendsto_pearsonMDArgumentPerturbation_mul_scale_zero
    (L := L) hC hL hadm hq hscale
  have hsum := (hdelta.add hcross).add (hdelta.pow 2)
  have hexponent : Tendsto (fun p : ℕ ↦
      pearsonMDFiniteTailExponent
        L (qseq p) (lambdaSeq p) (mseq p) p)
      atTop (nhds 0) := by
    have hscaled := hsum.const_mul (Real.exp 2)
    have hscaled' : Tendsto (fun p : ℕ ↦
        Real.exp 2 *
          (pearsonMDArgumentPerturbation
              L (qseq p) (lambdaSeq p) (mseq p) p +
            pearsonMDArgumentPerturbation
                L (qseq p) (lambdaSeq p) (mseq p) p *
              (qseq p + |lambdaSeq p|) +
            pearsonMDArgumentPerturbation
                L (qseq p) (lambdaSeq p) (mseq p) p ^ 2))
        atTop (nhds 0) := by
      simpa using hscaled
    apply hscaled'.congr'
    filter_upwards with p
    unfold pearsonMDFiniteTailExponent
    dsimp only
    ring
  have hpos : Tendsto (fun p : ℕ ↦
      Real.exp (pearsonMDFiniteTailExponent
        L (qseq p) (lambdaSeq p) (mseq p) p))
      atTop (nhds 1) := by
    simpa [Function.comp_def] using
      (Real.continuous_exp.tendsto 0).comp hexponent
  have hneg : Tendsto (fun p : ℕ ↦
      Real.exp (-pearsonMDFiniteTailExponent
        L (qseq p) (lambdaSeq p) (mseq p) p))
      atTop (nhds 1) := by
    have hnegExponent : Tendsto (fun p : ℕ ↦
        -pearsonMDFiniteTailExponent
          L (qseq p) (lambdaSeq p) (mseq p) p)
        atTop (nhds 0) := by
      simpa using hexponent.neg
    simpa [Function.comp_def] using
      (Real.continuous_exp.tendsto 0).comp hnegExponent
  simpa [pearsonMDFiniteGaussianEnvelope] using hpos.sub hneg

/-- Both one-sided Gaussian perturbation exponents in the finite Pearson
bound are controlled by the common deterministic exponent. -/
theorem gaussianTailPerturbationExponent_le_pearsonMDFiniteTailExponent
    {L q lambda : ℝ} {m p : ℕ} (hq : 0 ≤ q)
    {x : ℝ} (hx : |x| ≤ q + |lambda|) :
    gaussianTailPerturbationExponent x
        (pearsonMDArgumentPerturbation L q lambda m p) ≤
      pearsonMDFiniteTailExponent L q lambda m p := by
  let delta := pearsonMDArgumentPerturbation L q lambda m p
  have hdelta : 0 ≤ delta := by
    unfold delta pearsonMDArgumentPerturbation pearsonMDChiRadius
    positivity
  unfold gaussianTailPerturbationExponent pearsonMDFiniteTailExponent
  dsimp only
  have hfac : 1 + |x| + pearsonMDArgumentPerturbation L q lambda m p ≤
      1 + q + |lambda| +
        pearsonMDArgumentPerturbation L q lambda m p := by linarith
  exact mul_le_mul_of_nonneg_left hfac
    (mul_nonneg (Real.exp_pos 2).le hdelta)

theorem abs_sub_le_common_envelope
    {L q lambda : ℝ} {m p : ℕ} (hq : 0 ≤ q) :
    Real.exp (gaussianTailPerturbationExponent (q - lambda)
          (pearsonMDArgumentPerturbation L q lambda m p)) -
        Real.exp (-gaussianTailPerturbationExponent (q - lambda)
          (pearsonMDArgumentPerturbation L q lambda m p)) ≤
      pearsonMDFiniteGaussianEnvelope L q lambda m p := by
  have hx : |q - lambda| ≤ q + |lambda| := by
    calc
      |q - lambda| ≤ |q| + |lambda| := abs_sub q lambda
      _ = q + |lambda| := by rw [abs_of_nonneg hq]
  have hE := gaussianTailPerturbationExponent_le_pearsonMDFiniteTailExponent
    (L := L) (m := m) (p := p) hq hx
  have hE0 : 0 ≤ gaussianTailPerturbationExponent (q - lambda)
      (pearsonMDArgumentPerturbation L q lambda m p) := by
    have hdelta : 0 ≤ pearsonMDArgumentPerturbation L q lambda m p := by
      unfold pearsonMDArgumentPerturbation pearsonMDChiRadius
      positivity
    unfold gaussianTailPerturbationExponent
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos 2).le hdelta)
      (by linarith [abs_nonneg (q - lambda)])
  simpa [pearsonMDFiniteGaussianEnvelope] using
    exp_sub_exp_neg_mono hE0 hE

theorem abs_add_le_common_envelope
    {L q lambda : ℝ} {m p : ℕ} (hq : 0 ≤ q) :
    Real.exp (gaussianTailPerturbationExponent (q + lambda)
          (pearsonMDArgumentPerturbation L q lambda m p)) -
        Real.exp (-gaussianTailPerturbationExponent (q + lambda)
          (pearsonMDArgumentPerturbation L q lambda m p)) ≤
      pearsonMDFiniteGaussianEnvelope L q lambda m p := by
  have hx : |q + lambda| ≤ q + |lambda| := by
    calc
      |q + lambda| ≤ |q| + |lambda| := abs_add_le q lambda
      _ = q + |lambda| := by rw [abs_of_nonneg hq]
  have hE := gaussianTailPerturbationExponent_le_pearsonMDFiniteTailExponent
    (L := L) (m := m) (p := p) hq hx
  have hE0 : 0 ≤ gaussianTailPerturbationExponent (q + lambda)
      (pearsonMDArgumentPerturbation L q lambda m p) := by
    have hdelta : 0 ≤ pearsonMDArgumentPerturbation L q lambda m p := by
      unfold pearsonMDArgumentPerturbation pearsonMDChiRadius
      positivity
    unfold gaussianTailPerturbationExponent
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos 2).le hdelta)
      (by linarith [abs_nonneg (q + lambda)])
  simpa [pearsonMDFiniteGaussianEnvelope] using
    exp_sub_exp_neg_mono hE0 hE

/-- An elementary endpoint lemma used below: an eventual finite relative
error bound, together with a vanishing deterministic envelope, forces the
ratio to tend to one. -/
theorem tendsto_ratio_one_of_abs_sub_le
    {P D eps : ℕ → ℝ}
    (hD : ∀ᶠ n in atTop, 0 < D n)
    (hbound : ∀ᶠ n in atTop, |P n - D n| ≤ D n * eps n)
    (heps : Tendsto eps atTop (nhds 0)) :
    Tendsto (fun n ↦ P n / D n) atTop (nhds 1) := by
  have herr : Tendsto (fun n ↦ P n / D n - 1) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using
      (squeeze_zero'
        (f := fun n ↦ |P n / D n - 1|) (g := eps)
        (by filter_upwards with n; exact abs_nonneg _)
        (by
          filter_upwards [hD, hbound] with n hDn hn
          calc
            |P n / D n - 1| = |P n - D n| / D n := by
              rw [div_sub_one hDn.ne', abs_div, abs_of_pos hDn]
            _ ≤ (D n * eps n) / D n :=
              div_le_div_of_nonneg_right hn hDn.le
            _ = eps n := by field_simp [hDn.ne'])
        heps)
  have hadd := herr.add_const 1
  simpa only [sub_add_cancel, zero_add] using hadd

/-- **Uniform noncentral Pearson moderate deviations.**

For every triangular array with `2 ≤ p ≤ m`, every nonnegative threshold,
and every Gaussian population correlation with
`q + |sqrt(m) rho / sqrt(1-rho²)| ≤ C sqrt(log p)`, the exact two-sided
studentized sample-correlation tail is asymptotic, in relative error, to the
corresponding two-sided shifted Gaussian tail.  Quantifying over arbitrary
admissible sequences is the sequential characterization of uniformity.
-/
theorem tendsto_gaussianPearsonTwoSidedTail_div_gaussianTail_one
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hgap : C ^ 2 / 2 < L)
    {mseq : ℕ → ℕ} {rhoSeq qseq : ℕ → ℝ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hrho : ∀ᶠ p in atTop, |rhoSeq p| < 1)
    (hq : ∀ᶠ p in atTop, 0 ≤ qseq p)
    (hscale : ∀ᶠ p in atTop,
      qseq p + |pearsonRubenNoncentrality (mseq p) (rhoSeq p)| ≤
        C * Real.sqrt (Real.log (p : ℝ))) :
    Tendsto (fun p : ℕ ↦
      gaussianPearsonTwoSidedTail
          (E := EuclideanSpace ℝ (Fin (mseq p)))
          (mseq p) (rhoSeq p) (qseq p) /
        pearsonMDGaussianTailDenominator
          (qseq p) (pearsonRubenNoncentrality (mseq p) (rhoSeq p)))
      atTop (nhds 1) := by
  let lambdaSeq : ℕ → ℝ := fun p ↦
    pearsonRubenNoncentrality (mseq p) (rhoSeq p)
  let envelope : ℕ → ℝ := fun p ↦
    pearsonMDFiniteGaussianEnvelope
      L (qseq p) (lambdaSeq p) (mseq p) p
  let badRatio : ℕ → ℝ := fun p ↦
    8 * Real.exp (-2 * (L * Real.log (p : ℝ))) /
      pearsonMDGaussianTailDenominator (qseq p) (lambdaSeq p)
  let P : ℕ → ℝ := fun p ↦
    gaussianPearsonTwoSidedTail
      (E := EuclideanSpace ℝ (Fin (mseq p)))
      (mseq p) (rhoSeq p) (qseq p)
  let D : ℕ → ℝ := fun p ↦
    pearsonMDGaussianTailDenominator (qseq p) (lambdaSeq p)
  have hEnv : Tendsto envelope atTop (nhds 0) := by
    dsimp [envelope, lambdaSeq]
    exact tendsto_pearsonMDFiniteGaussianEnvelope_zero
      hC hL hadm hq hscale
  have hBad : Tendsto badRatio atTop (nhds 0) := by
    dsimp [badRatio, lambdaSeq]
    exact tendsto_pearsonMDDiscardedExp_div_gaussianTailDenominator_zero
      hC hL hgap hq hscale
  have hEps : Tendsto (fun p ↦ envelope p + badRatio p)
      atTop (nhds 0) := by
    simpa using hEnv.add hBad
  have hD : ∀ᶠ p in atTop, 0 < D p := by
    filter_upwards with p
    exact pearsonMDGaussianTailDenominator_pos _ _
  have hquarter := eventually_pearsonMDChiRadius_le_quarter
    (L := L) hadm
  have hfinite : ∀ᶠ p in atTop,
      |P p - D p| ≤ D p * (envelope p + badRatio p) := by
    filter_upwards [hadm, hrho, hq, hscale, hquarter]
      with p hp hrhop hqp _hscalep hquarterp
    have hp1 : 1 ≤ p := (by omega : 1 ≤ 2).trans hp.1
    have hlog0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp1)
    have ht0 : 0 ≤ L * Real.log (p : ℝ) := mul_nonneg hL hlog0
    have hchi :
        pearsonChiRadius (mseq p) (L * Real.log (p : ℝ)) =
          pearsonMDChiRadius L (mseq p) p := by
      unfold pearsonChiRadius pearsonMDChiRadius
      rfl
    let lambda : ℝ := lambdaSeq p
    let delta : ℝ := pearsonMDArgumentPerturbation
      L (qseq p) lambda (mseq p) p
    have hm : 2 ≤ mseq p := hp.1.trans hp.2
    have hraw := gaussianPearsonTwoSidedTail_finite_comparison
      (E := EuclideanSpace ℝ (Fin (mseq p)))
      (m := mseq p) (by simp) hm (rhoSeq p) hrhop ht0
      (by simpa [hchi] using hquarterp) (qseq p)
    have hdelta :
        2 * pearsonChiRadius (mseq p) (L * Real.log (p : ℝ)) *
            (|qseq p| + |lambda|) = delta := by
      simp only [hchi, abs_of_nonneg hqp]
      dsimp [delta]
      unfold pearsonMDArgumentPerturbation
      ring
    have hminus := abs_sub_le_common_envelope
      (L := L) (m := mseq p) (p := p) (lambda := lambda) hqp
    have hplus := abs_add_le_common_envelope
      (L := L) (m := mseq p) (p := p) (lambda := lambda) hqp
    have hQminus : 0 ≤ standardGaussianUpperTail (qseq p - lambda) :=
      standardGaussianUpperTail_nonneg _
    have hQplus : 0 ≤ standardGaussianUpperTail (qseq p + lambda) :=
      standardGaussianUpperTail_nonneg _
    have hweighted :
        standardGaussianUpperTail (qseq p - lambda) *
            (Real.exp (gaussianTailPerturbationExponent
                (qseq p - lambda) delta) -
              Real.exp (-gaussianTailPerturbationExponent
                (qseq p - lambda) delta)) +
          standardGaussianUpperTail (qseq p + lambda) *
            (Real.exp (gaussianTailPerturbationExponent
                (qseq p + lambda) delta) -
              Real.exp (-gaussianTailPerturbationExponent
                (qseq p + lambda) delta)) ≤
        (standardGaussianUpperTail (qseq p - lambda) +
            standardGaussianUpperTail (qseq p + lambda)) *
          pearsonMDFiniteGaussianEnvelope
            L (qseq p) lambda (mseq p) p := by
      calc
        _ ≤ standardGaussianUpperTail (qseq p - lambda) *
                pearsonMDFiniteGaussianEnvelope
                  L (qseq p) lambda (mseq p) p +
              standardGaussianUpperTail (qseq p + lambda) *
                pearsonMDFiniteGaussianEnvelope
                  L (qseq p) lambda (mseq p) p :=
            add_le_add
              (mul_le_mul_of_nonneg_left (by simpa [delta] using hminus) hQminus)
              (mul_le_mul_of_nonneg_left (by simpa [delta] using hplus) hQplus)
        _ = _ := by ring
    have habs : |P p - D p| ≤
        D p * envelope p + 8 * Real.exp (-2 *
          (L * Real.log (p : ℝ))) := by
      dsimp only at hraw
      rw [hdelta] at hraw
      have hraw' : |P p - D p| ≤
          (standardGaussianUpperTail (qseq p - lambda) *
              (Real.exp (gaussianTailPerturbationExponent
                  (qseq p - lambda) delta) -
                Real.exp (-gaussianTailPerturbationExponent
                  (qseq p - lambda) delta)) +
            standardGaussianUpperTail (qseq p + lambda) *
              (Real.exp (gaussianTailPerturbationExponent
                  (qseq p + lambda) delta) -
                Real.exp (-gaussianTailPerturbationExponent
                  (qseq p + lambda) delta))) +
            8 * Real.exp (-2 * (L * Real.log (p : ℝ))) := by
        simpa [P, D, lambda, lambdaSeq,
          pearsonMDGaussianTailDenominator] using hraw
      have htarget :
          (standardGaussianUpperTail (qseq p - lambda) *
              (Real.exp (gaussianTailPerturbationExponent
                  (qseq p - lambda) delta) -
                Real.exp (-gaussianTailPerturbationExponent
                  (qseq p - lambda) delta)) +
            standardGaussianUpperTail (qseq p + lambda) *
              (Real.exp (gaussianTailPerturbationExponent
                  (qseq p + lambda) delta) -
                Real.exp (-gaussianTailPerturbationExponent
                  (qseq p + lambda) delta))) +
            8 * Real.exp (-2 * (L * Real.log (p : ℝ))) ≤
          D p * envelope p +
            8 * Real.exp (-2 * (L * Real.log (p : ℝ))) := by
        have hw := add_le_add_right hweighted
          (8 * Real.exp (-2 * (L * Real.log (p : ℝ))))
        simpa [D, envelope, lambda, lambdaSeq,
          pearsonMDGaussianTailDenominator] using hw
      exact hraw'.trans htarget
    have hDpos : 0 < D p := pearsonMDGaussianTailDenominator_pos _ _
    dsimp [badRatio]
    calc
      |P p - D p| ≤
          D p * envelope p +
            8 * Real.exp (-2 * (L * Real.log (p : ℝ))) := habs
      _ = D p * (envelope p +
          8 * Real.exp (-2 * (L * Real.log (p : ℝ))) / D p) := by
        field_simp [hDpos.ne']
  have hratio := tendsto_ratio_one_of_abs_sub_le hD hfinite hEps
  simpa [P, D, lambdaSeq] using hratio

end

end LogdetLean.Coherence
