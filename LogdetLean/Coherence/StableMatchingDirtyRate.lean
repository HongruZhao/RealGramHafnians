import LogdetLean.Coherence.OverlapAsymptotic
import Mathlib.Tactic
/-!
# Vanishing cross-edge mass for a sparse block matching

There are at most order `s_p p` nonplanted edges touching the special block
vertices.  Since every such edge has the central `p^{-2}` marginal tail, their
total mass vanishes when `s_p=o(p)`; no multiedge independence is required.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real
open scoped Topology

theorem tendsto_two_mul_matching_mul_ambient_mul_betaTail_zero
    {mseq sseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hsparse : Tendsto (fun p : ℕ ↦ (sseq p : ℝ) / (p : ℝ))
      atTop (nhds 0)) (x : ℝ) :
    Tendsto (fun p : ℕ ↦
      2 * (sseq p : ℝ) * (p : ℝ) *
        betaCorrelationTailProbability (mseq p) p x)
      atTop (nhds 0) := by
  have htail := tendsto_sq_mul_betaCorrelationTailProbability hadm x
  have hprod := (hsparse.const_mul 2).mul htail
  have hprod' : Tendsto (fun p : ℕ ↦
      2 * ((sseq p : ℝ) / (p : ℝ)) *
        ((p : ℝ) ^ 2 * betaCorrelationTailProbability (mseq p) p x))
      atTop (nhds 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop.eventually
    (eventually_ne_atTop (0 : ℝ)))] with p hp
  field_simp [hp]

/-- Any nonnegative dirty-edge count whose expectation is bounded by the
preceding first-moment envelope converges to zero in probability at the void
level.  This is the Markov step used in the matrix theorem. -/
theorem tendsto_dirtyVoidProbability_one_of_expectation_bound
    {mseq sseq : ℕ → ℕ}
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hsparse : Tendsto (fun p : ℕ ↦ (sseq p : ℝ) / (p : ℝ))
      atTop (nhds 0)) (x : ℝ)
    {dirtyNonvoid : ℕ → ℝ}
    (hnonneg : ∀ᶠ p in atTop, 0 ≤ dirtyNonvoid p)
    (hupper : ∀ᶠ p in atTop,
      dirtyNonvoid p ≤ 2 * (sseq p : ℝ) * (p : ℝ) *
        betaCorrelationTailProbability (mseq p) p x) :
    Tendsto (fun p ↦ 1 - dirtyNonvoid p) atTop (nhds 1) := by
  have henv :=
    tendsto_two_mul_matching_mul_ambient_mul_betaTail_zero hadm hsparse x
  have hzero : Tendsto dirtyNonvoid atTop (nhds 0) :=
    squeeze_zero' hnonneg hupper henv
  simpa using (tendsto_const_nhds : Tendsto (fun _p : ℕ ↦ (1 : ℝ))
    atTop (nhds 1)).sub hzero

end

end LogdetLean.Coherence
