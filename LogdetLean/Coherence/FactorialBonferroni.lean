import Mathlib
/-!
# The finite Bonferroni step

Exact alternating-binomial and falling-factorial bounds.  No probability or
asymptotic assumption occurs in this module.
-/

namespace LogdetLean.Coherence

open scoped BigOperators

noncomputable section

/-- Alternating binomial partial sum through order `J`. -/
def alternatingChooseSum (W J : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (J + 1), (-1 : ℤ) ^ k * (W.choose k : ℤ)

/-- Exact partial-sum identity
`∑_{k=0}^J (-1)^k C(n+1,k) = (-1)^J C(n,J)`. -/
theorem alternatingChooseSum_succ (n J : ℕ) :
    alternatingChooseSum (n + 1) J =
      (-1 : ℤ) ^ J * (n.choose J : ℤ) := by
  exact Int.alternating_sum_range_choose_eq_choose

/-- For `W = 0`, every alternating partial sum equals one. -/
@[simp] theorem alternatingChooseSum_zero (J : ℕ) :
    alternatingChooseSum 0 J = 1 := by
  unfold alternatingChooseSum
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp [Nat.choose_zero_succ]
  · simp

/-- Integer-valued indicator of the void event. -/
def voidIndicator (W : ℕ) : ℤ := if W = 0 then 1 else 0

/-- Odd truncations lie below the void indicator and even truncations above
it. -/
theorem alternatingChooseSum_bonferroni (W K : ℕ) :
    alternatingChooseSum W (2 * K + 1) ≤ voidIndicator W ∧
      voidIndicator W ≤ alternatingChooseSum W (2 * K) := by
  cases W with
  | zero => simp [voidIndicator]
  | succ n =>
      rw [alternatingChooseSum_succ, alternatingChooseSum_succ]
      simp [voidIndicator, pow_succ]

/-- A falling factorial divided by `k!` is the corresponding binomial
coefficient, viewed in `ℝ`. -/
theorem descFactorial_div_factorial (W k : ℕ) :
    (W.descFactorial k : ℝ) / (k.factorial : ℝ) = W.choose k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- Alternating partial sum in the factorial-moment normalization. -/
def alternatingFactorialSum (W J : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (J + 1),
    (-1 : ℝ) ^ k / k.factorial * W.descFactorial k

/-- The factorial-moment and binomial partial sums agree. -/
theorem alternatingFactorialSum_eq (W J : ℕ) :
    alternatingFactorialSum W J = (alternatingChooseSum W J : ℝ) := by
  unfold alternatingFactorialSum alternatingChooseSum
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (-1 : ℝ) ^ k / k.factorial * W.descFactorial k =
        (-1 : ℝ) ^ k *
          ((W.descFactorial k : ℝ) / k.factorial) := by ring
    _ = (-1 : ℝ) ^ k * W.choose k := by
      rw [descFactorial_div_factorial]

/-- Real-valued Bonferroni inequality in factorial-moment normalization. -/
theorem alternatingFactorialSum_bonferroni (W K : ℕ) :
    alternatingFactorialSum W (2 * K + 1) ≤
        (if W = 0 then 1 else 0) ∧
      (if W = 0 then 1 else 0) ≤
        alternatingFactorialSum W (2 * K) := by
  have h := alternatingChooseSum_bonferroni W K
  have hv : (voidIndicator W : ℝ) = (if W = 0 then 1 else 0) := by
    simp [voidIndicator]
  rw [alternatingFactorialSum_eq, alternatingFactorialSum_eq]
  constructor
  · calc
      (alternatingChooseSum W (2 * K + 1) : ℝ) ≤
          (voidIndicator W : ℝ) := by exact_mod_cast h.1
      _ = (if W = 0 then 1 else 0) := hv
  · calc
      (if W = 0 then 1 else 0) = (voidIndicator W : ℝ) := hv.symm
      _ ≤ (alternatingChooseSum W (2 * K) : ℝ) := by
        exact_mod_cast h.2

end

end LogdetLean.Coherence
