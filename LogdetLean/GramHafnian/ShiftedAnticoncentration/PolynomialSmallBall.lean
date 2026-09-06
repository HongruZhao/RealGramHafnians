import LogdetLean.GramHafnian.ShiftedAnticoncentration.FinalTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-!
# Polynomial small balls in the logarithmic dimension regime

This module derives the manuscript's asymptotic polynomial-small-ball
corollary from the verified simplified finite theorem.  The conclusion is
pointwise in the complex centre; this is the public formulation used
throughout the formalization and is equivalent to the displayed supremum
bound in the manuscript.
-/

open Filter

namespace LogdetLean.GramHafnian

noncomputable section

/-- Under `k ≥ 8n`, the exponent in the simplified finite coefficient is at
most `1 + 6 n²/k`. -/
theorem simplifiedAnticoncentrationExponent_le
    {n k : ℕ} (hn : 1 ≤ n) (hk : 8 * n ≤ k) :
    1 / ((k : ℝ) - 1) +
        (3 * (n : ℝ) ^ 2 - 3) /
          ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
      1 + 6 * ((n : ℝ) ^ 2 / (k : ℝ)) := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hkR : 8 * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkposNat : 0 < k := by omega
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkposNat
  have hkm1 : 0 < (k : ℝ) - 1 := by nlinarith
  have hhead : 1 / ((k : ℝ) - 1) ≤ 1 := by
    exact (div_le_iff₀ hkm1).2 (by nlinarith)
  have hnum0 : 0 ≤ 3 * (n : ℝ) ^ 2 := by positivity
  have hnum : 3 * (n : ℝ) ^ 2 - 3 ≤ 3 * (n : ℝ) ^ 2 := by linarith
  have hkhalf : 0 < (k : ℝ) / 2 := by positivity
  have hden : (k : ℝ) / 2 ≤ (k : ℝ) - 4 * (n : ℝ) + 1 := by
    nlinarith
  have htail :
      (3 * (n : ℝ) ^ 2 - 3) /
          ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
        6 * ((n : ℝ) ^ 2 / (k : ℝ)) := by
    calc
      (3 * (n : ℝ) ^ 2 - 3) /
            ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
          (3 * (n : ℝ) ^ 2) / ((k : ℝ) / 2) :=
        div_le_div₀ hnum0 hnum hkhalf hden
      _ = 6 * ((n : ℝ) ^ 2 / (k : ℝ)) := by
        field_simp [hkpos.ne']
        ring
  linarith

/-- A finite, directly usable polynomial form of the simplified small-ball
bound.  The final hypothesis is the harmless large-`n` absorption of the
constant `2e`; the asymptotic theorem below discharges it automatically from
the strict exponent margin. -/
theorem gaussianGramHafnianShiftedAnticoncentration_polynomial_finite
    {n k : ℕ} {A D beta : ℝ}
    (hn : 1 ≤ n) (hk : 8 * n ≤ k)
    (hscale : (n : ℝ) ^ 2 / (k : ℝ) ≤ D * Real.log (n : ℝ))
    (hconstant :
      2 * Real.exp 1 ≤
        (n : ℝ) ^ (2 * beta - A - 6 * D - (1 / 2 : ℝ))) :
    ∀ z : ℂ,
      gramHafnianShiftedSmallBallProbability k n z
          ((n : ℝ) ^ (-beta)) ≤
        (n : ℝ) ^ (-A) := by
  intro z
  have hnpos : 0 < (n : ℝ) := by positivity
  have hk4 : 4 * n ≤ k := by omega
  have heps : 0 ≤ (n : ℝ) ^ (-beta) :=
    Real.rpow_nonneg hnpos.le _
  have hexponent := simplifiedAnticoncentrationExponent_le hn hk
  have hscale6 :
      6 * ((n : ℝ) ^ 2 / (k : ℝ)) ≤
        6 * D * Real.log (n : ℝ) := by
    nlinarith
  have hexponent' :
      1 / ((k : ℝ) - 1) +
          (3 * (n : ℝ) ^ 2 - 3) /
            ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
        1 + 6 * D * Real.log (n : ℝ) := by
    linarith
  have hepssq :
      ((n : ℝ) ^ (-beta)) ^ 2 = (n : ℝ) ^ (-2 * beta) := by
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul hnpos.le]
    congr 1
    ring
  have hexplog :
      Real.exp (6 * D * Real.log (n : ℝ)) =
        (n : ℝ) ^ (6 * D) := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hpowcombine :
      (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (6 * D) *
          (n : ℝ) ^ (-2 * beta) =
        (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) := by
    calc
      (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (6 * D) *
            (n : ℝ) ^ (-2 * beta) =
          (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D) *
            (n : ℝ) ^ (-2 * beta) := by
              rw [← Real.rpow_add hnpos (1 / 2 : ℝ) (6 * D)]
      _ = (n : ℝ) ^ (((1 / 2 : ℝ) + 6 * D) + (-2 * beta)) := by
              exact (Real.rpow_add hnpos
                ((1 / 2 : ℝ) + 6 * D) (-2 * beta)).symm
      _ = (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) := by
              congr 1
              ring
  have hsimplify :
      (2 * Real.sqrt (n : ℝ) *
          Real.exp (1 + 6 * D * Real.log (n : ℝ))) *
          ((n : ℝ) ^ (-beta)) ^ 2 =
        (2 * Real.exp 1) *
          (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) := by
    rw [Real.sqrt_eq_rpow, Real.exp_add, hexplog, hepssq]
    calc
      2 * (n : ℝ) ^ (1 / 2 : ℝ) *
            (Real.exp 1 * (n : ℝ) ^ (6 * D)) *
            (n : ℝ) ^ (-2 * beta) =
          (2 * Real.exp 1) *
            ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (6 * D) *
              (n : ℝ) ^ (-2 * beta)) := by ring
      _ = (2 * Real.exp 1) *
            (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) := by
              rw [hpowcombine]
  have hmarginNonneg :
      0 ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) :=
    Real.rpow_nonneg hnpos.le _
  have habsorb := mul_le_mul_of_nonneg_right hconstant hmarginNonneg
  have habsorb' :
      (2 * Real.exp 1) *
          (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) ≤
        (n : ℝ) ^ (-A) := by
    calc
      (2 * Real.exp 1) *
            (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) ≤
          (n : ℝ) ^ (2 * beta - A - 6 * D - (1 / 2 : ℝ)) *
            (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) := habsorb
      _ = (n : ℝ) ^
          ((2 * beta - A - 6 * D - (1 / 2 : ℝ)) +
            ((1 / 2 : ℝ) + 6 * D - 2 * beta)) := by
              rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (-A) := by
              congr 1
              ring
  calc
    gramHafnianShiftedSmallBallProbability k n z
          ((n : ℝ) ^ (-beta)) ≤
        (2 * Real.sqrt (n : ℝ) *
          Real.exp
            (1 / ((k : ℝ) - 1) +
              (3 * (n : ℝ) ^ 2 - 3) /
                ((k : ℝ) - 4 * (n : ℝ) + 1))) *
          ((n : ℝ) ^ (-beta)) ^ 2 :=
      gaussianGramHafnianShiftedAnticoncentration_simplified
        n k hn hk4 z ((n : ℝ) ^ (-beta)) heps
    _ ≤ (2 * Real.sqrt (n : ℝ) *
          Real.exp (1 + 6 * D * Real.log (n : ℝ))) *
          ((n : ℝ) ^ (-beta)) ^ 2 := by
      gcongr
    _ = (2 * Real.exp 1) *
          (n : ℝ) ^ ((1 / 2 : ℝ) + 6 * D - 2 * beta) := hsimplify
    _ ≤ (n : ℝ) ^ (-A) := habsorb'

/-- The logarithmic scale assumption forces the finite admissibility
`k(n) ≥ 8n` eventually.  Eventual positivity is stated explicitly because
Lean's totalized division would otherwise make `n² / 0 = 0`. -/
theorem eventually_eight_mul_le_of_log_scale
    (kseq : ℕ → ℕ) {D : ℝ} (hD : 0 < D)
    (hkpos : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, 8 * n ≤ kseq n := by
  have hlogdiv : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hscaled : Tendsto
      (fun n : ℕ ↦ (8 * D) *
        (Real.log (n : ℝ) / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using hlogdiv.const_mul (8 * D)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (8 * D) * (Real.log (n : ℝ) / (n : ℝ)) < 1 :=
    hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hkpos, hscale, hsmall, eventually_ge_atTop 2]
    with n hkn hs hsm hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hkposR : 0 < (kseq n : ℝ) := by exact_mod_cast hkn
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hDlogpos : 0 < D * Real.log (n : ℝ) := mul_pos hD hlogpos
  have hlogbound : 8 * D * Real.log (n : ℝ) < (n : ℝ) := by
    have hdiv :
        (8 * D * Real.log (n : ℝ)) / (n : ℝ) < 1 := by
      simpa [div_eq_mul_inv, mul_assoc] using hsm
    exact (div_lt_one hnpos).mp hdiv
  have hscaleMul :
      (n : ℝ) ^ 2 ≤ D * Real.log (n : ℝ) * (kseq n : ℝ) :=
    (div_le_iff₀ hkposR).mp hs
  have hkR : 8 * (n : ℝ) ≤ (kseq n : ℝ) := by
    by_contra hnot
    have hklt : (kseq n : ℝ) < 8 * (n : ℝ) := lt_of_not_ge hnot
    have hprod1 :
        D * Real.log (n : ℝ) * (kseq n : ℝ) <
          D * Real.log (n : ℝ) * (8 * (n : ℝ)) :=
      mul_lt_mul_of_pos_left hklt hDlogpos
    have hprod2 :
        D * Real.log (n : ℝ) * (8 * (n : ℝ)) < (n : ℝ) ^ 2 := by
      calc
        D * Real.log (n : ℝ) * (8 * (n : ℝ)) =
            (8 * D * Real.log (n : ℝ)) * (n : ℝ) := by ring
        _ < (n : ℝ) * (n : ℝ) :=
          mul_lt_mul_of_pos_right hlogbound hnpos
        _ = (n : ℝ) ^ 2 := by ring
    exact (not_lt_of_ge hscaleMul) (hprod1.trans hprod2)
  exact_mod_cast hkR

/-- **Polynomial small balls.**

This is the pointwise-in-the-centre form of the manuscript corollary.  For
every fixed exponent strictly above
`(A + 6D + 1/2) / 2`, the logarithmic dimension regime gives failure
probability at most `n⁻ᴬ` at radius `n⁻ᵝ`, eventually in `n`.

The eventual positivity hypothesis only records that `k(n)` is a genuine
positive matrix dimension; it is implicit in the manuscript's ratio
`n²/k(n)` and necessary in Lean because division is totalized at zero. -/
theorem gaussianGramHafnianShiftedAnticoncentration_polynomial
    (kseq : ℕ → ℕ) {A D beta : ℝ}
    (_hA : 0 < A) (hD : 0 < D)
    (hbeta : (A + 6 * D + (1 / 2 : ℝ)) / 2 < beta)
    (hkpos : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ,
      gramHafnianShiftedSmallBallProbability (kseq n) n z
          ((n : ℝ) ^ (-beta)) ≤
        (n : ℝ) ^ (-A) := by
  have hmargin : 0 < 2 * beta - A - 6 * D - (1 / 2 : ℝ) := by
    linarith
  have hconstant : ∀ᶠ n : ℕ in atTop,
      2 * Real.exp 1 ≤
        (n : ℝ) ^ (2 * beta - A - 6 * D - (1 / 2 : ℝ)) :=
    ((tendsto_rpow_atTop hmargin).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 * Real.exp 1))
  have hk8 := eventually_eight_mul_le_of_log_scale kseq hD hkpos hscale
  filter_upwards [hscale, hk8, hconstant, eventually_ge_atTop 1]
    with n hs hk hc hn
  exact gaussianGramHafnianShiftedAnticoncentration_polynomial_finite
    hn hk hs hc

/-- Existential form of polynomial small balls, matching the first sentence
of the manuscript corollary. -/
theorem gaussianGramHafnianShiftedAnticoncentration_polynomial_exists
    (kseq : ℕ → ℕ) {A D : ℝ}
    (hA : 0 < A) (hD : 0 < D)
    (hkpos : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    ∃ beta : ℝ, 0 < beta ∧
      ∀ᶠ n : ℕ in atTop, ∀ z : ℂ,
        gramHafnianShiftedSmallBallProbability (kseq n) n z
            ((n : ℝ) ^ (-beta)) ≤
          (n : ℝ) ^ (-A) := by
  let beta : ℝ := (A + 6 * D + (1 / 2 : ℝ)) / 2 + 1
  have hbeta : (A + 6 * D + (1 / 2 : ℝ)) / 2 < beta := by
    simp [beta]
  have hbetapos : 0 < beta := by
    dsimp [beta]
    positivity
  exact ⟨beta, hbetapos,
    gaussianGramHafnianShiftedAnticoncentration_polynomial
      kseq hA hD hbeta hkpos hscale⟩

end

end LogdetLean.GramHafnian
