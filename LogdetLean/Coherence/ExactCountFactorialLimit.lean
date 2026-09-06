import LogdetLean.Coherence.FactorialVoidLimit
/-!
# From factorial moments to fixed exact-count limits

This file is a scalar transfer layer.  It proves shifted Bonferroni bounds and
uses the already verified void-limit mechanism to recover the mass of a fixed
integer count from all fixed falling-factorial moments.

The finite-mass specialization may be read with
`mass n w = P(B_n and W_n = w)`.  Thus `A` may be a limiting CDF weight.
Nothing here constructs `W_n`, proves a point-process limit, or supplies any
model-specific factorial-moment asymptotic.
-/

namespace LogdetLean.Coherence

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Real-valued indicator of the exact count `W = r`. -/
def exactCountIndicator (W r : ℕ) : ℝ :=
  if W = r then 1 else 0

/-- The shifted alternating sum associated with the exact-count event
`W = r`.  Its terms use the factorial moments of orders `r, r+1, ...`. -/
def shiftedAlternatingFactorialSum (W r J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    (-1 : ℝ) ^ j / j.factorial *
      ((W.descFactorial (r + j) : ℝ) / (r.factorial : ℝ))

/-- Splitting a descending factorial after its first `r` factors. -/
theorem descFactorial_add_div_factorial
    (W r j : ℕ) :
    (W.descFactorial (r + j) : ℝ) / (r.factorial : ℝ) =
      (W.choose r : ℝ) * ((W - r).descFactorial j : ℝ) := by
  have hsplit := Nat.descFactorial_mul_descFactorial
    (n := W) (k := r) (m := r + j) (by omega)
  have hnat :
      W.descFactorial (r + j) =
        r.factorial * W.choose r * (W - r).descFactorial j := by
    rw [← hsplit]
    simp only [Nat.add_sub_cancel_left,
      Nat.descFactorial_eq_factorial_mul_choose]
    ac_rfl
  have hreal :
      (W.descFactorial (r + j) : ℝ) =
        (r.factorial : ℝ) * (W.choose r : ℝ) *
          ((W - r).descFactorial j : ℝ) := by
    exact_mod_cast hnat
  rw [hreal]
  field_simp

/-- The shifted sum is a nonnegative binomial prefactor times the ordinary
void-event alternating sum for the residual count `W-r`. -/
theorem shiftedAlternatingFactorialSum_eq_choose_mul
    (W r J : ℕ) :
    shiftedAlternatingFactorialSum W r J =
      (W.choose r : ℝ) * alternatingFactorialSum (W - r) J := by
  unfold shiftedAlternatingFactorialSum alternatingFactorialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [descFactorial_add_div_factorial]
  ring

/-- Multiplying the residual void indicator by `choose W r` gives exactly
the indicator of `W = r`. -/
theorem choose_mul_residualVoidIndicator (W r : ℕ) :
    (W.choose r : ℝ) * (if W - r = 0 then 1 else 0) =
      exactCountIndicator W r := by
  by_cases hlt : W < r
  · have hne : W ≠ r := by omega
    simp [exactCountIndicator, Nat.choose_eq_zero_of_lt hlt, hne]
  · have hrle : r ≤ W := by omega
    by_cases heq : W = r
    · subst W
      simp [exactCountIndicator]
    · have hrlt : r < W := lt_of_le_of_ne hrle (Ne.symm heq)
      have hsub : W - r ≠ 0 := by omega
      simp [exactCountIndicator, heq, hsub]

/-- Shifted Bonferroni: odd truncations lie below the exact-count indicator
and even truncations lie above it. -/
theorem shiftedAlternatingFactorialSum_bonferroni
    (W r K : ℕ) :
    shiftedAlternatingFactorialSum W r (2 * K + 1) ≤
        exactCountIndicator W r ∧
      exactCountIndicator W r ≤
        shiftedAlternatingFactorialSum W r (2 * K) := by
  have hvoid := alternatingFactorialSum_bonferroni (W - r) K
  rw [shiftedAlternatingFactorialSum_eq_choose_mul,
    shiftedAlternatingFactorialSum_eq_choose_mul,
    ← choose_mul_residualVoidIndicator W r]
  exact ⟨mul_le_mul_of_nonneg_left hvoid.1 (by positivity),
    mul_le_mul_of_nonneg_left hvoid.2 (by positivity)⟩

/-- A nonnegative weight preserves the shifted Bonferroni bounds.  Taking the
weight to be a CDF-event indicator is the pointwise joint-count case. -/
theorem weighted_shiftedAlternatingFactorialSum_bonferroni
    (weight : ℝ) (hweight : 0 ≤ weight) (W r K : ℕ) :
    weight * shiftedAlternatingFactorialSum W r (2 * K + 1) ≤
        weight * exactCountIndicator W r ∧
      weight * exactCountIndicator W r ≤
        weight * shiftedAlternatingFactorialSum W r (2 * K) := by
  exact ⟨mul_le_mul_of_nonneg_left
      (shiftedAlternatingFactorialSum_bonferroni W r K).1 hweight,
    mul_le_mul_of_nonneg_left
      (shiftedAlternatingFactorialSum_bonferroni W r K).2 hweight⟩

/-- Shifted alternating partial sum made from an abstract triangular array of
factorial moments. -/
def shiftedMixedFactorialPartialSum
    (a : ℕ → ℕ → ℝ) (r n J : ℕ) : ℝ :=
  mixedFactorialPartialSum
    (fun n j ↦ a n (r + j) / (r.factorial : ℝ)) n J

/-- The Poisson mass at the fixed count `r`, written in the normalization
produced by factorial moments. -/
def poissonExactMass (lambda : ℝ) (r : ℕ) : ℝ :=
  lambda ^ r / (r.factorial : ℝ) * Real.exp (-lambda)

/-- **Abstract weighted exact-count transfer.**  If every fixed factorial
moment has the product limit `A * lambda^k`, and the desired scalar exact-count
quantity is squeezed by the shifted Bonferroni sums, then it converges to
`A` times the Poisson mass at `r`.

The theorem is deliberately scalar.  For a joint CDF/count statement, `A` is
the limiting CDF value and `a n k` is the CDF-indicator-weighted factorial
moment. -/
theorem tendsto_weightedExactCount_of_mixed_factorial_limits
    (a : ℕ → ℕ → ℝ) (exactMass : ℕ → ℝ) (A lambda : ℝ) (r : ℕ)
    (hmom : ∀ k, Tendsto (fun n ↦ a n k) atTop
      (nhds (A * lambda ^ k)))
    (hbonf : ∀ n K,
      shiftedMixedFactorialPartialSum a r n (2 * K + 1) ≤ exactMass n ∧
        exactMass n ≤ shiftedMixedFactorialPartialSum a r n (2 * K)) :
    Tendsto exactMass atTop (nhds (A * poissonExactMass lambda r)) := by
  let b : ℕ → ℕ → ℝ :=
    fun n j ↦ a n (r + j) / (r.factorial : ℝ)
  have hb (j : ℕ) :
      Tendsto (fun n ↦ b n j) atTop
        (nhds ((A * lambda ^ r / (r.factorial : ℝ)) * lambda ^ j)) := by
    have h := (hmom (r + j)).div_const (r.factorial : ℝ)
    convert h using 1
    rw [pow_add]
    ring_nf
  have hlimit := tendsto_void_of_mixed_factorial_limits b exactMass
    (A * lambda ^ r / (r.factorial : ℝ)) lambda hb
    (fun n K ↦ by simpa [shiftedMixedFactorialPartialSum, b] using hbonf n K)
  convert hlimit using 1
  simp only [poissonExactMass]
  ring_nf

/-! ## Finite integer-count laws

The next specialization removes the abstract Bonferroni hypothesis for a
finite-support count law.  The coefficients need only be nonnegative; they
may be ordinary count probabilities or joint masses
`P(B_n and W_n = w)`. -/

/-- Falling-factorial moment of a finite nonnegative count-mass array. -/
def finiteCountWeightedFactorialMoment
    (cap : ℕ → ℕ) (mass : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ W ∈ Finset.range (cap n + 1),
    mass n W * (W.descFactorial k : ℝ)

/-- Exact-count mass extracted from the same finite array.  Writing this as a
sum makes the Bonferroni transfer independent of any support convention for
`mass` outside `0, ..., cap n`. -/
def finiteCountWeightedExactMass
    (cap : ℕ → ℕ) (mass : ℕ → ℕ → ℝ) (n r : ℕ) : ℝ :=
  ∑ W ∈ Finset.range (cap n + 1),
    mass n W * exactCountIndicator W r

/-- Once the fixed count lies below the finite support cap, the extracted
exact mass is literally the coefficient at that count. -/
theorem finiteCountWeightedExactMass_eq_of_le
    (cap : ℕ → ℕ) (mass : ℕ → ℕ → ℝ) (n r : ℕ)
    (hr : r ≤ cap n) :
    finiteCountWeightedExactMass cap mass n r = mass n r := by
  unfold finiteCountWeightedExactMass
  rw [Finset.sum_eq_single r]
  · simp [exactCountIndicator]
  · intro W hW hne
    simp [exactCountIndicator, hne]
  · simp only [Finset.mem_range]
    omega

/-- Expanding a shifted mixed factorial sum and interchanging its two finite
sums gives the mass-weighted pointwise shifted sum. -/
theorem shiftedMixedFactorialPartialSum_finiteCount_eq
    (cap : ℕ → ℕ) (mass : ℕ → ℕ → ℝ) (r n J : ℕ) :
    shiftedMixedFactorialPartialSum
        (finiteCountWeightedFactorialMoment cap mass) r n J =
      ∑ W ∈ Finset.range (cap n + 1),
        mass n W * shiftedAlternatingFactorialSum W r J := by
  simp only [shiftedMixedFactorialPartialSum, mixedFactorialPartialSum,
    finiteCountWeightedFactorialMoment, shiftedAlternatingFactorialSum,
    Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W hW
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Nonnegativity of the finite masses supplies the shifted Bonferroni bounds
for the exact-count mass automatically. -/
theorem finiteCountWeightedExactMass_bonferroni
    (cap : ℕ → ℕ) (mass : ℕ → ℕ → ℝ)
    (hmass : ∀ n W, 0 ≤ mass n W) (r n K : ℕ) :
    shiftedMixedFactorialPartialSum
        (finiteCountWeightedFactorialMoment cap mass) r n (2 * K + 1) ≤
        finiteCountWeightedExactMass cap mass n r ∧
      finiteCountWeightedExactMass cap mass n r ≤
        shiftedMixedFactorialPartialSum
          (finiteCountWeightedFactorialMoment cap mass) r n (2 * K) := by
  rw [shiftedMixedFactorialPartialSum_finiteCount_eq,
    shiftedMixedFactorialPartialSum_finiteCount_eq]
  unfold finiteCountWeightedExactMass
  constructor
  · apply Finset.sum_le_sum
    intro W hW
    exact mul_le_mul_of_nonneg_left
      (shiftedAlternatingFactorialSum_bonferroni W r K).1 (hmass n W)
  · apply Finset.sum_le_sum
    intro W hW
    exact mul_le_mul_of_nonneg_left
      (shiftedAlternatingFactorialSum_bonferroni W r K).2 (hmass n W)

/-- **Finite count-law exact Poisson mass theorem.**  Convergence of every
fixed falling-factorial moment of a finite nonnegative integer-count mass
array to `A * lambda^k` implies convergence of its mass at every fixed count
`r` to `A` times the Poisson mass.

For an unweighted probability law, take `A = 1`.  For a joint CDF/count law,
take `mass n w = P(B_n and W_n = w)` and `A` equal to the limiting CDF. -/
theorem tendsto_finiteCountWeightedExactMass_of_factorialMoments
    (cap : ℕ → ℕ) (mass : ℕ → ℕ → ℝ)
    (A lambda : ℝ) (r : ℕ)
    (hmass : ∀ n W, 0 ≤ mass n W)
    (hmom : ∀ k,
      Tendsto
        (fun n ↦ finiteCountWeightedFactorialMoment cap mass n k)
        atTop (nhds (A * lambda ^ k))) :
    Tendsto
      (fun n ↦ finiteCountWeightedExactMass cap mass n r)
      atTop (nhds (A * poissonExactMass lambda r)) := by
  apply tendsto_weightedExactCount_of_mixed_factorial_limits
    (finiteCountWeightedFactorialMoment cap mass)
    (fun n ↦ finiteCountWeightedExactMass cap mass n r)
    A lambda r hmom
  intro n K
  exact finiteCountWeightedExactMass_bonferroni cap mass hmass r n K

/-- Coefficient form of the finite count-law theorem.  The eventual support
condition is automatic in the usual setting where the count cap tends to
infinity (and also when it is a fixed cap at least `r`). -/
theorem tendsto_finiteCountCoefficient_of_factorialMoments
    (cap : ℕ → ℕ) (mass : ℕ → ℕ → ℝ)
    (A lambda : ℝ) (r : ℕ)
    (hmass : ∀ n W, 0 ≤ mass n W)
    (hcap : ∀ᶠ n in atTop, r ≤ cap n)
    (hmom : ∀ k,
      Tendsto
        (fun n ↦ finiteCountWeightedFactorialMoment cap mass n k)
        atTop (nhds (A * lambda ^ k))) :
    Tendsto (fun n ↦ mass n r) atTop
      (nhds (A * poissonExactMass lambda r)) := by
  apply (tendsto_finiteCountWeightedExactMass_of_factorialMoments
    cap mass A lambda r hmass hmom).congr'
  filter_upwards [hcap] with n hn
  exact finiteCountWeightedExactMass_eq_of_le cap mass n r hn

/-- Unweighted probability-mass specialization (`A = 1`). -/
theorem tendsto_finiteCountCoefficient_poisson_of_factorialMoments
    (cap : ℕ → ℕ) (mass : ℕ → ℕ → ℝ)
    (lambda : ℝ) (r : ℕ)
    (hmass : ∀ n W, 0 ≤ mass n W)
    (hcap : ∀ᶠ n in atTop, r ≤ cap n)
    (hmom : ∀ k,
      Tendsto
        (fun n ↦ finiteCountWeightedFactorialMoment cap mass n k)
        atTop (nhds (lambda ^ k))) :
    Tendsto (fun n ↦ mass n r) atTop
      (nhds (poissonExactMass lambda r)) := by
  have hmom' : ∀ k,
      Tendsto
        (fun n ↦ finiteCountWeightedFactorialMoment cap mass n k)
        atTop (nhds ((1 : ℝ) * lambda ^ k)) := by
    intro k
    simpa using hmom k
  simpa using tendsto_finiteCountCoefficient_of_factorialMoments
    cap mass 1 lambda r hmass hcap hmom'

end

end LogdetLean.Coherence
