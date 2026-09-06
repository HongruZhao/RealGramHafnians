import LogdetLean.Coherence.FactorialBonferroni
/-!
# From mixed factorial moments to a void probability

The model-specific work enters only through mixed factorial-moment limits.
Finite Bonferroni bounds and the exponential series then give the void-event
limit.
-/

namespace LogdetLean.Coherence

open Filter
open scoped BigOperators Topology

noncomputable section

/-- A two-stage squeeze lemma: first send `n → ∞` for each fixed truncation
order, then send the truncation order to infinity. -/
theorem tendsto_of_two_stage_squeeze
    (s : ℕ → ℝ) (lower upper : ℕ → ℕ → ℝ)
    (lowerLimit upperLimit : ℕ → ℝ) (L : ℝ)
    (hlower : ∀ K, Tendsto (lower K) atTop (nhds (lowerLimit K)))
    (hupper : ∀ K, Tendsto (upper K) atTop (nhds (upperLimit K)))
    (hbounds : ∀ n K, lower K n ≤ s n ∧ s n ≤ upper K n)
    (hlowerLimit : Tendsto lowerLimit atTop (nhds L))
    (hupperLimit : Tendsto upperLimit atTop (nhds L)) :
    Tendsto s atTop (nhds L) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hKevent : ∀ᶠ K in atTop, a < lowerLimit K :=
      hlowerLimit.eventually_const_lt ha
    obtain ⟨K, hK⟩ := hKevent.exists
    have hnevent : ∀ᶠ n in atTop, a < lower K n :=
      (hlower K).eventually_const_lt hK
    filter_upwards [hnevent] with n hn
    exact hn.trans_le (hbounds n K).1
  · intro b hb
    have hKevent : ∀ᶠ K in atTop, upperLimit K < b :=
      hupperLimit.eventually_lt_const hb
    obtain ⟨K, hK⟩ := hKevent.exists
    have hnevent : ∀ᶠ n in atTop, upper K n < b :=
      (hupper K).eventually_lt_const hK
    filter_upwards [hnevent] with n hn
    exact (hbounds n K).2.trans_lt hn

/-- Finite exponential-series partial sum. -/
def exponentialPartialSum (lambda : ℝ) (J : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (J + 1),
    (-lambda) ^ k / (k.factorial : ℝ)

/-- Exponential partial sums converge to `exp (-lambda)`. -/
theorem exponentialPartialSum_tendsto (lambda : ℝ) :
    Tendsto (exponentialPartialSum lambda) atTop
      (nhds (Real.exp (-lambda))) := by
  unfold exponentialPartialSum
  rw [Filter.tendsto_add_atTop_iff_nat
    (f := fun n ↦ ∑ k ∈ Finset.range n,
      (-lambda) ^ k / (k.factorial : ℝ)) 1]
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp (-lambda : ℝ)).tendsto_sum_nat

/-- Alternating partial sum made from a triangular array `a n k`. -/
def mixedFactorialPartialSum (a : ℕ → ℕ → ℝ)
    (n J : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (J + 1),
    (-1 : ℝ) ^ k / k.factorial * a n k

/-- Pointwise mixed factorial-moment limits imply convergence of each fixed
finite alternating sum. -/
theorem mixedFactorialPartialSum_tendsto
    (a : ℕ → ℕ → ℝ) (A lambda : ℝ)
    (hmom : ∀ k, Tendsto (fun n ↦ a n k) atTop
      (nhds (A * lambda ^ k))) (J : ℕ) :
    Tendsto (fun n ↦ mixedFactorialPartialSum a n J) atTop
      (nhds (A * exponentialPartialSum lambda J)) := by
  have hsum :
      Tendsto (fun n ↦ mixedFactorialPartialSum a n J) atTop
        (nhds (∑ k ∈ Finset.range (J + 1),
          ((-1 : ℝ) ^ k / k.factorial) * (A * lambda ^ k))) := by
    unfold mixedFactorialPartialSum
    exact tendsto_finsetSum (Finset.range (J + 1))
      (fun k hk ↦ ((hmom k).const_mul ((-1 : ℝ) ^ k / k.factorial)))
  have hlimit :
      (∑ k ∈ Finset.range (J + 1),
          ((-1 : ℝ) ^ k / k.factorial) * (A * lambda ^ k)) =
        A * exponentialPartialSum lambda J := by
    rw [exponentialPartialSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [neg_pow]
    ring
  rw [← hlimit]
  exact hsum

/-- Odd and even subsequences have the same exponential-series limit. -/
theorem exponentialPartialSum_parity_tendsto (lambda : ℝ) :
    Tendsto (fun K ↦ exponentialPartialSum lambda (2 * K + 1)) atTop
        (nhds (Real.exp (-lambda))) ∧
      Tendsto (fun K ↦ exponentialPartialSum lambda (2 * K)) atTop
        (nhds (Real.exp (-lambda))) := by
  have hoddIndex : Tendsto (fun K : ℕ ↦ 2 * K + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact (eventually_ge_atTop b).mono (fun K hK ↦ by omega)
  have hevenIndex : Tendsto (fun K : ℕ ↦ 2 * K) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact (eventually_ge_atTop b).mono (fun K hK ↦ by omega)
  exact ⟨(exponentialPartialSum_tendsto lambda).comp hoddIndex,
    (exponentialPartialSum_tendsto lambda).comp hevenIndex⟩

/-- Abstract mixed-factorial-moment-to-void theorem. -/
theorem tendsto_void_of_mixed_factorial_limits
    (a : ℕ → ℕ → ℝ) (s : ℕ → ℝ) (A lambda : ℝ)
    (hmom : ∀ k, Tendsto (fun n ↦ a n k) atTop
      (nhds (A * lambda ^ k)))
    (hbonf : ∀ n K,
      mixedFactorialPartialSum a n (2 * K + 1) ≤ s n ∧
        s n ≤ mixedFactorialPartialSum a n (2 * K)) :
    Tendsto s atTop (nhds (A * Real.exp (-lambda))) := by
  apply tendsto_of_two_stage_squeeze s
    (fun K n ↦ mixedFactorialPartialSum a n (2 * K + 1))
    (fun K n ↦ mixedFactorialPartialSum a n (2 * K))
    (fun K ↦ A * exponentialPartialSum lambda (2 * K + 1))
    (fun K ↦ A * exponentialPartialSum lambda (2 * K))
    (A * Real.exp (-lambda))
  · intro K
    exact mixedFactorialPartialSum_tendsto a A lambda hmom (2 * K + 1)
  · intro K
    exact mixedFactorialPartialSum_tendsto a A lambda hmom (2 * K)
  · exact hbonf
  · exact (exponentialPartialSum_parity_tendsto lambda).1.const_mul A
  · exact (exponentialPartialSum_parity_tendsto lambda).2.const_mul A

/-- Product-limit specialization used by the coherence theorem. -/
theorem joint_product_limit_of_mixed_factorial_limits
    (a : ℕ → ℕ → ℝ) (jointProbability : ℕ → ℝ)
    (A lambda : ℝ)
    (hmom : ∀ k, Tendsto (fun n ↦ a n k) atTop
      (nhds (A * lambda ^ k)))
    (hbonf : ∀ n K,
      mixedFactorialPartialSum a n (2 * K + 1) ≤ jointProbability n ∧
        jointProbability n ≤ mixedFactorialPartialSum a n (2 * K)) :
    Tendsto jointProbability atTop
      (nhds (A * Real.exp (-lambda))) :=
  tendsto_void_of_mixed_factorial_limits a jointProbability
    A lambda hmom hbonf

end

end LogdetLean.Coherence
