import LogdetLean.Coherence.BetaIntensityFiniteBound
/-!
# Compact-window hypotheses for the one-edge logarithmic estimate

The finite Beta-prefix bound is stated under transparent scalar conditions:
the squared-correlation threshold lies in `(0,1/2]`, is at most
`5 log(p)/m`, and `log(p) >= 1`.  The compact-rate conditions already used
for the finite intensity imply all of them uniformly over `m >= p`.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter Real

/-- The compact Beta-rate conditions imply exactly the finite hypotheses
needed by the one-edge `L¹` logarithmic-prefix theorem. -/
theorem compactBetaRateConditions_oneEdge_bounds
    {M : ℝ} {m p : ℕ} {x : ℝ}
    (hcond : CompactBetaRateConditions M p)
    (hpm : p ≤ m) (hx : |x| ≤ M) :
    6 ≤ m ∧
      0 < classicalCoherenceThreshold m p x / (m : ℝ) ∧
      classicalCoherenceThreshold m p x / (m : ℝ) ≤ 1 / 2 ∧
      1 ≤ Real.log (p : ℝ) ∧
      classicalCoherenceThreshold m p x / (m : ℝ) ≤
        5 * Real.log (p : ℝ) / (m : ℝ) := by
  rcases hcond with ⟨hM, hL, hell, hsum, hsq⟩
  let L : ℝ := Real.log (p : ℝ)
  let ell : ℝ := Real.log L
  let A : ℝ := classicalCoherenceThreshold m p x
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hpPos : (0 : ℝ) < (p : ℝ) := by
    have hpN : 0 < p := by
      by_contra hp
      have : p = 0 := by omega
      subst p
      norm_num [L] at hL
    exact_mod_cast hpN
  have hmPos : (0 : ℝ) < (m : ℝ) :=
    hpPos.trans_le (Nat.cast_le.mpr hpm)
  have hp100R : (100 : ℝ) ≤ (p : ℝ) := by
    have hLsq : 1 ≤ L ^ 2 := by nlinarith
    have : 100 * L ^ 2 ≤ (p : ℝ) := by simpa [L] using hsq
    nlinarith
  have hp100 : 100 ≤ p := by exact_mod_cast hp100R
  have hm6 : 6 ≤ m := by omega
  have hxlo : -M ≤ x := (abs_le.mp hx).1
  have hxhi : x ≤ M := (abs_le.mp hx).2
  have hAlower : 2 * L ≤ A := by
    dsimp [A, L, ell]
    unfold classicalCoherenceThreshold
    linarith
  have hAupper : A ≤ 5 * L := by
    dsimp [A, L, ell]
    unfold classicalCoherenceThreshold
    linarith
  have hApos : 0 < A :=
    (mul_pos (by norm_num) hLpos).trans_le hAlower
  have hten : 10 * L ≤ (m : ℝ) := by
    have hsqLower : 10 * L ≤ 100 * L ^ 2 := by nlinarith
    exact hsqLower.trans ((show 100 * L ^ 2 ≤ (p : ℝ) by
      simpa [L] using hsq).trans (Nat.cast_le.mpr hpm))
  have hhalf : A / (m : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hmPos).2
    nlinarith
  have hrate : A / (m : ℝ) ≤ 5 * L / (m : ℝ) :=
    (div_le_div_iff_of_pos_right hmPos).2 hAupper
  exact ⟨hm6, div_pos hApos hmPos, hhalf, by simpa [L] using hL,
    by simpa [A, L] using hrate⟩

/-- Eventual compact-window form, uniform over every `m >= p`. -/
theorem eventually_uniform_compactOneEdgeConditions
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ P : ℕ, ∀ p ≥ P, ∀ m ≥ p, ∀ x : ℝ, |x| ≤ M →
      6 ≤ m ∧
        0 < classicalCoherenceThreshold m p x / (m : ℝ) ∧
        classicalCoherenceThreshold m p x / (m : ℝ) ≤ 1 / 2 ∧
        1 ≤ Real.log (p : ℝ) ∧
        classicalCoherenceThreshold m p x / (m : ℝ) ≤
          5 * Real.log (p : ℝ) / (m : ℝ) := by
  obtain ⟨P, hP⟩ := eventually_atTop.1
    (eventually_compactBetaRateConditions hM)
  refine ⟨P, ?_⟩
  intro p hp m hpm x hx
  exact compactBetaRateConditions_oneEdge_bounds (hP p hp) hpm hx

end

end LogdetLean.Coherence
