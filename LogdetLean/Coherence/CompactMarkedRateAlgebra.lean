import LogdetLean.Coherence.JointBerryEsseenFinalTarget
/-!
# Finite algebra for the local marked-Poisson error

After the marked Stein estimate, the complete-graph local term is

`min(1,1/lambda) * 4 * choose(p,2) * p * q^2`,

where `lambda = choose(p,2) * q`.  If the intensity is bounded above by a
compact-window constant `K`, this term is at most `16 K / p`.  The theorem
below makes that cancellation explicit and avoids a spurious `K^2` bound.
-/

namespace LogdetLean.Coherence

noncomputable section

/-- Exact finite local-error reduction from the one-edge probability to an
`O(K/p)` bound. -/
theorem min_inv_intensity_mul_completeGraphLocal_le
    {p : ℕ} (hp : 2 ≤ p) {q lambda K : ℝ}
    (_hq : 0 ≤ q) (hlambda : 0 < lambda)
    (hlambdaEq : lambda = ((p.choose 2 : ℕ) : ℝ) * q)
    (hlambdaK : lambda ≤ K) :
    min 1 (1 / lambda) *
        (4 * ((p.choose 2 : ℕ) : ℝ) * (p : ℝ) * q ^ 2) ≤
      16 * K / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hchoose : ((p.choose 2 : ℕ) : ℝ) =
      (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hchoosePos : 0 < ((p.choose 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos hp
  have hmin : min 1 (1 / lambda) ≤ 1 / lambda := min_le_right _ _
  have hlocal0 : 0 ≤
      4 * ((p.choose 2 : ℕ) : ℝ) * (p : ℝ) * q ^ 2 := by positivity
  have hfirst :
      min 1 (1 / lambda) *
          (4 * ((p.choose 2 : ℕ) : ℝ) * (p : ℝ) * q ^ 2) ≤
        (1 / lambda) *
          (4 * ((p.choose 2 : ℕ) : ℝ) * (p : ℝ) * q ^ 2) :=
    mul_le_mul_of_nonneg_right hmin hlocal0
  have hqEq : q = lambda / ((p.choose 2 : ℕ) : ℝ) := by
    apply (eq_div_iff hchoosePos.ne').2
    nlinarith [hlambdaEq]
  have hsimplify :
      (1 / lambda) *
          (4 * ((p.choose 2 : ℕ) : ℝ) * (p : ℝ) * q ^ 2) =
        8 * lambda / ((p : ℝ) - 1) := by
    rw [hqEq, hchoose]
    field_simp [hlambda.ne', hp0.ne', show (p : ℝ) - 1 ≠ 0 by linarith]
    ring
  have hK0 : 0 ≤ K := hlambda.le.trans hlambdaK
  have hsecond : 8 * lambda / ((p : ℝ) - 1) ≤
      8 * K / ((p : ℝ) - 1) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlambdaK (by norm_num)) (by linarith)
  have hthird : 8 * K / ((p : ℝ) - 1) ≤ 16 * K / (p : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : 0 < (p : ℝ) - 1) hp0).2
    nlinarith
  exact hfirst.trans (hsimplify.le.trans (hsecond.trans hthird))

end

end LogdetLean.Coherence
