import LogdetLean.GramHafnian.AsymptoticCritical
import Mathlib.Analysis.SpecialFunctions.Stirling
/-!
# Absolute normalization of the central-binomial baseline

The exact Gram--hafnian crossover is naturally stated relative to
`centralBaseline n = choose(2n,n)/4^n`.  Stirling's theorem identifies its
absolute scale as `1 / sqrt (π n)`.
-/

open scoped Topology
open Filter Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- Exact reduction of the central-binomial baseline to the Stirling
sequence. -/
theorem centralBaseline_mul_sqrt_eq_stirlingSeq_ratio
    (n : ℕ) (hn : 0 < n) :
    centralBaseline n * Real.sqrt n =
      Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2nR : (0 : ℝ) < 2 * n := by positivity
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2nfac : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  have hsqn : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  have hsqrt2n : Real.sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
  have hsqrt4n : Real.sqrt (2 * ((2 * n : ℕ) : ℝ)) ≠ 0 := by positivity
  have hnpow : (((n : ℝ) / Real.exp 1) ^ n) ≠ 0 := by positivity
  have h2npow : ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) ≠ 0 := by
    positivity
  have hfour : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial
    (show n ≤ 2 * n by omega)
  have hchoose :
      ((Nat.choose (2 * n) n : ℕ) : ℝ) * (n.factorial : ℝ) *
          (n.factorial : ℝ) = ((2 * n).factorial : ℝ) := by
    have hsub : 2 * n - n = n := by omega
    exact_mod_cast (hsub ▸ hchooseNat)
  rw [centralBaseline, Stirling.stirlingSeq, Stirling.stirlingSeq]
  push_cast
  rw [show (2 : ℝ) * (2 * (n : ℝ)) = 4 * n by ring]
  have hsqrt4 : Real.sqrt (4 * (n : ℝ)) = 2 * Real.sqrt n := by
    calc
      Real.sqrt (4 * (n : ℝ)) = Real.sqrt 4 * Real.sqrt n := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt n := by norm_num
  rw [hsqrt4]
  have hpow :
      (((2 : ℝ) * n) / Real.exp 1) ^ (2 * n) =
        (4 : ℝ) ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 := by
    rw [show ((2 : ℝ) * n) / Real.exp 1 =
      2 * ((n : ℝ) / Real.exp 1) by ring, mul_pow,
      show 2 * n = n + n by omega, pow_add]
    have htwoPow : (2 : ℝ) ^ n * 2 ^ n = 4 ^ n := by
      rw [← mul_pow]
      norm_num
    rw [htwoPow]
    ring
  rw [hpow]
  field_simp [hnfac, h2nfac, hsqn, hsqrt2n, hsqrt4n, hnpow,
    h2npow, hfour]
  rw [sq_sqrt (show 0 ≤ (2 : ℝ) * n by positivity)]
  rw [sq_sqrt hnR.le, pow_two]
  calc
    ((Nat.choose (2 * n) n : ℕ) : ℝ) * (n : ℝ) * 2 *
          ((n.factorial : ℝ) * (n.factorial : ℝ)) =
        (((Nat.choose (2 * n) n : ℕ) : ℝ) *
          (n.factorial : ℝ) * (n.factorial : ℝ)) * (2 * (n : ℝ)) := by ring
    _ = ((2 * n).factorial : ℝ) * (2 * (n : ℝ)) := by rw [hchoose]

/-- Classical central-binomial normalization, derived inside Lean from
Mathlib's proved Stirling formula. -/
theorem tendsto_centralBaseline_mul_sqrt :
    Tendsto (fun n : ℕ ↦ centralBaseline n * Real.sqrt n)
      atTop (nhds (1 / Real.sqrt Real.pi)) := by
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hs2 : Tendsto (fun n : ℕ ↦ Stirling.stirlingSeq (2 * n))
      atTop (nhds (Real.sqrt Real.pi)) := by
    have ht := hs.comp
      (tendsto_id.const_mul_atTop' (by norm_num : 0 < (2 : ℕ)))
    apply ht.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      simp [Function.comp_apply]
  have hratio := hs2.div (hs.pow 2)
    (by positivity : Real.sqrt Real.pi ^ 2 ≠ 0)
  have hratio' : Tendsto
      (fun n : ℕ ↦ Stirling.stirlingSeq (2 * n) /
        Stirling.stirlingSeq n ^ 2)
      atTop (nhds (1 / Real.sqrt Real.pi)) := by
    have ht : Tendsto
        (fun n : ℕ ↦ Stirling.stirlingSeq (2 * n) /
          Stirling.stirlingSeq n ^ 2)
        atTop (nhds (Real.sqrt Real.pi / Real.sqrt Real.pi ^ 2)) := by
      apply hratio.congr'
      exact Filter.Eventually.of_forall fun _ ↦ rfl
    have hpi : Real.sqrt Real.pi ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    have heq : Real.sqrt Real.pi / Real.sqrt Real.pi ^ 2 =
        1 / Real.sqrt Real.pi := by
      field_simp [hpi]
    rwa [heq] at ht
  apply hratio'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (centralBaseline_mul_sqrt_eq_stirlingSeq_ratio n (by omega)).symm

/-- Absolute version of the sharp quadratic crossover:

`m₂(k_n,n) * sqrt n → 1 / (sqrt π * besselMajorant(1/c))`.
-/
theorem tendsto_gramSecondMomentRatio_mul_sqrt_quadratic_crossover
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦
      gramSecondMomentRatio (kseq n) n * Real.sqrt n)
      atTop (nhds (1 /
        (Real.sqrt Real.pi * besselMajorant (1 / c)))) := by
  have hm := tendsto_gramSecondMomentRatio_quadratic_crossover
    kseq c hc hkTop haspect
  have hp := hm.mul tendsto_centralBaseline_mul_sqrt
  have htarget :
      (1 / besselMajorant (1 / c)) * (1 / Real.sqrt Real.pi) =
        1 / (Real.sqrt Real.pi * besselMajorant (1 / c)) := by
    ring
  rw [htarget] at hp
  apply hp.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    have hbase : centralBaseline n ≠ 0 := ne_of_gt (centralBaseline_pos n)
    field_simp [hbase]

/-- Equivalent conventional statement with the factor `sqrt(π n)`:

`m₂(k_n,n) * sqrt(π n) → 1 / besselMajorant(1/c)`.
-/
theorem tendsto_gramSecondMomentRatio_mul_sqrt_pi_mul_quadratic_crossover
    (kseq : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hkTop : Tendsto kseq atTop atTop)
    (haspect : Tendsto
      (fun n : ℕ ↦ (kseq n : ℝ) / (n : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n : ℕ ↦
      gramSecondMomentRatio (kseq n) n * Real.sqrt (Real.pi * n))
      atTop (nhds (1 / besselMajorant (1 / c))) := by
  have h :=
    (tendsto_gramSecondMomentRatio_mul_sqrt_quadratic_crossover
      kseq c hc hkTop haspect).mul_const (Real.sqrt Real.pi)
  have htarget :
      (1 / (Real.sqrt Real.pi * besselMajorant (1 / c))) *
          Real.sqrt Real.pi = 1 / besselMajorant (1 / c) := by
    field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos),
      ne_of_gt (besselMajorant_pos (one_div_nonneg.mpr hc.le))]
  rw [htarget] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    change gramSecondMomentRatio (kseq n) n * Real.sqrt n *
        Real.sqrt Real.pi =
      gramSecondMomentRatio (kseq n) n * Real.sqrt (Real.pi * (n : ℝ))
    rw [Real.sqrt_mul (Real.pi_pos.le)]
    ring

end

end LogdetLean.GramHafnian
