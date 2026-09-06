import LogdetLean.GramHafnian.SymmetricGaussianHafnian.CoefficientPowerBounds
/-!
# Sharp lower power bounds for the finite coefficients

This module proves matching polynomial lower bounds for the exact real and
complex shifted-hafnian coefficients.  It also audits the purely algebraic
beta-four specialization without asserting a quaternionic shifted-small-ball
theorem.
-/

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

open Filter
open scoped BigOperators Real Topology

/-! ## A discrete Kershaw--Wallis half-step bound -/

/-- The normalized Gamma ratio whose upper bound by one is the half-step
Kershaw--Wallis inequality needed below. -/
def kershawRatio (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) + 1 / 4) * Real.Gamma ((n : ℝ) + 1 / 2) /
    Real.Gamma ((n : ℝ) + 1)

private theorem kershawRatio_nonneg (n : ℕ) : 0 ≤ kershawRatio n := by
  unfold kershawRatio
  positivity

/-- At integer arguments the Kershaw ratio increases.  After squaring and
using the Gamma recurrence, the comparison reduces to `0 ≤ 1/16`. -/
private theorem kershawRatio_le_succ (n : ℕ) (hn : 1 ≤ n) :
    kershawRatio n ≤ kershawRatio (n + 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hGhalf : 0 < Real.Gamma ((n : ℝ) + 1 / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hGone : 0 < Real.Gamma ((n : ℝ) + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hroot0 : 0 ≤ (n : ℝ) + 1 / 4 := by positivity
  have hroot1 : 0 ≤ (n : ℝ) + 1 + 1 / 4 := by positivity
  have hGhalfNext :
      Real.Gamma (((n + 1 : ℕ) : ℝ) + 1 / 2) =
        ((n : ℝ) + 1 / 2) * Real.Gamma ((n : ℝ) + 1 / 2) := by
    have hcast : (((n + 1 : ℕ) : ℝ) + 1 / 2) =
        ((n : ℝ) + 1 / 2) + 1 := by
      push_cast
      ring
    rw [hcast, Real.Gamma_add_one (by linarith : (n : ℝ) + 1 / 2 ≠ 0)]
  have hGoneNext :
      Real.Gamma (((n + 1 : ℕ) : ℝ) + 1) =
        ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 1 + 1 := by
      push_cast
      ring
    rw [hcast, Real.Gamma_add_one (by linarith : (n : ℝ) + 1 ≠ 0)]
  rw [← sq_le_sq₀ (kershawRatio_nonneg n) (kershawRatio_nonneg (n + 1))]
  unfold kershawRatio
  rw [hGhalfNext, hGoneNext]
  simp only [div_pow, mul_pow]
  rw [Real.sq_sqrt hroot0]
  have hcastroot : (((n + 1 : ℕ) : ℝ) + 1 / 4) =
      (n : ℝ) + 1 + 1 / 4 := by
    push_cast
    ring
  rw [hcastroot, Real.sq_sqrt hroot1]
  field_simp [hGhalf.ne', hGone.ne']
  nlinarith

private theorem kershawRatio_eq_normalized (n : ℕ) (hn : 1 ≤ n) :
    kershawRatio n =
      Real.sqrt (((n : ℝ) + 1 / 4) / (n : ℝ)) *
        (LogdetLean.Coherence.gammaHalfRatioScale (n : ℝ))⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnum : 0 ≤ (n : ℝ) + 1 / 4 := by positivity
  rw [Real.sqrt_div hnum]
  unfold kershawRatio LogdetLean.Coherence.gammaHalfRatioScale
  rw [Real.Gamma_add_one hnR.ne']
  field_simp [ne_of_gt (Real.sqrt_pos.2 hnR),
    (Real.Gamma_pos_of_pos hnR).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < (n : ℝ) + 1 / 2)).ne']
  rw [Real.sq_sqrt hnR.le]

private theorem tendsto_kershawRatio_succ :
    Tendsto (fun n : ℕ ↦ kershawRatio (n + 1)) atTop (nhds 1) := by
  have hdouble : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
    refine tendsto_atTop_atTop.2 ?_
    intro b
    exact ⟨b, fun a ha ↦ by omega⟩
  have hscale0 :=
    LogdetLean.Coherence.tendsto_gammaHalfRatioScale_nat_half.comp hdouble
  have hscale : Tendsto
      (fun n : ℕ ↦ LogdetLean.Coherence.gammaHalfRatioScale ((n : ℝ) + 1))
      atTop (nhds 1) := by
    convert hscale0.comp (tendsto_add_atTop_nat 1) using 1
    funext n
    congr 1
    push_cast
    ring
  have hinv : Tendsto
      (fun n : ℕ ↦
        (LogdetLean.Coherence.gammaHalfRatioScale ((n : ℝ) + 1))⁻¹)
      atTop (nhds 1) := by
    simpa using hscale.inv₀ one_ne_zero
  have hquot : Tendsto
      (fun n : ℕ ↦ ((((n + 1 : ℕ) : ℝ) + 1 / 4) /
        ((n + 1 : ℕ) : ℝ))) atTop (nhds 1) := by
    have hzero : Tendsto (fun n : ℕ ↦ (1 / 4 : ℝ) /
        ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 / 4 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
    have hfun : (fun n : ℕ ↦ ((((n + 1 : ℕ) : ℝ) + 1 / 4) /
        ((n + 1 : ℕ) : ℝ))) =
        (fun n : ℕ ↦ (1 : ℝ) + (1 / 4 : ℝ) /
          ((n + 1 : ℕ) : ℝ)) := by
      funext n
      have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hfun]
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hone.add hzero
  have hsqrt : Tendsto
      (fun n : ℕ ↦ Real.sqrt (((((n + 1 : ℕ) : ℝ) + 1 / 4) /
        ((n + 1 : ℕ) : ℝ)))) atTop (nhds 1) := by
    simpa using hquot.sqrt
  have hprod : Tendsto
      (fun n : ℕ ↦ Real.sqrt (((((n + 1 : ℕ) : ℝ) + 1 / 4) /
        ((n + 1 : ℕ) : ℝ))) *
        (LogdetLean.Coherence.gammaHalfRatioScale ((n : ℝ) + 1))⁻¹)
      atTop (nhds 1) := by
    simpa using hsqrt.mul hinv
  convert hprod using 1
  funext n
  simpa only [Nat.cast_add, Nat.cast_one] using
    kershawRatio_eq_normalized (n + 1) (by omega)

/-- The discrete Kershaw--Wallis inequality, derived internally from the
Gamma recurrence, monotonicity, and the already proved half-step limit. -/
theorem kershawRatio_le_one (n : ℕ) (hn : 1 ≤ n) :
    kershawRatio n ≤ 1 := by
  let f : ℕ → ℝ := fun m ↦ kershawRatio (m + 1)
  have hmono : Monotone f := monotone_nat_of_le_succ fun m ↦
    kershawRatio_le_succ (m + 1) (by omega)
  have hlim : Tendsto f atTop (nhds 1) := by
    simpa [f] using tendsto_kershawRatio_succ
  simpa only [f, Nat.sub_add_cancel hn] using
    hmono.ge_of_tendsto hlim (n - 1)

/-- Integer half-step Gamma-ratio lower bound in the form used by the
coefficient recurrence. -/
theorem sqrt_add_quarter_le_Gamma_ratio (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((n : ℝ) + 1 / 4) ≤
      Real.Gamma ((n : ℝ) + 1) /
        Real.Gamma ((n : ℝ) + 1 / 2) := by
  have hden : 0 < Real.Gamma ((n : ℝ) + 1) := by positivity
  have hhalf : 0 < Real.Gamma ((n : ℝ) + 1 / 2) := by positivity
  have h := kershawRatio_le_one n hn
  unfold kershawRatio at h
  apply (le_div_iff₀ hhalf).2
  have hmul := (div_le_iff₀ hden).mp h
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-! ## Complex coefficient -/

private theorem coefficient_succ_eq_mul_ratio (n : ℕ) (hn : 1 ≤ n) :
    coefficient (n + 1) = coefficient n *
      (((n : ℝ) + 1 / 2) / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [coefficient_eq_gamma (n + 1) (by omega), coefficient_eq_gamma n hn]
  have hhalf : (n : ℝ) + 1 / 2 ≠ 0 := by linarith
  rw [show (((n + 1 : ℕ) : ℝ) + 1 / 2) =
      ((n : ℝ) + 1 / 2) + 1 by push_cast; ring,
    Real.Gamma_add_one hhalf,
    show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
    Real.Gamma_add_one hnR.ne']
  field_simp [(Real.sqrt_ne_zero'.mpr Real.pi_pos),
    (Real.Gamma_pos_of_pos hnR).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < (n : ℝ) + 1 / 2)).ne']

private theorem sqrt_succ_le_sqrt_mul_complex_ratio
    (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
      Real.sqrt (n : ℝ) * (((n : ℝ) + 1 / 2) / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hleft : 0 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hright : 0 ≤
      Real.sqrt (n : ℝ) * (((n : ℝ) + 1 / 2) / (n : ℝ)) := by
    positivity
  rw [← sq_le_sq₀ hleft hright]
  rw [Real.sq_sqrt (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)), mul_pow,
    Real.sq_sqrt hnR.le]
  field_simp [hnR.ne']
  push_cast
  nlinarith

/-- Matching lower power bound for the exact complex coefficient. -/
theorem coefficient_ge_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) ≤ coefficient n := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    Real.sqrt (j : ℝ) ≤ coefficient j
  have hind : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · norm_num [P, coefficient, oddPairingNat, inverseBound_one]
    · intro j hj ih
      dsimp only [P] at ih ⊢
      rw [coefficient_succ_eq_mul_ratio j hj]
      have hratio : 0 ≤ (((j : ℝ) + 1 / 2) / (j : ℝ)) := by
        positivity
      calc
        Real.sqrt ((j + 1 : ℕ) : ℝ) ≤
            Real.sqrt (j : ℝ) * (((j : ℝ) + 1 / 2) / (j : ℝ)) :=
          sqrt_succ_le_sqrt_mul_complex_ratio j hj
        _ ≤ coefficient j * (((j : ℝ) + 1 / 2) / (j : ℝ)) :=
          mul_le_mul_of_nonneg_right ih hratio
  exact hind

/-! ## Real coefficient -/

private theorem sigma_succ_eq (n : ℕ) :
    sigma (n + 1) = Real.sqrt ((2 * n + 1 : ℕ) : ℝ) * sigma n := by
  unfold sigma
  rw [oddPairingNat_succ, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg (oddPairingNat n))]
  ring

private theorem realCoefficient_succ_eq_mul_ratio (n : ℕ) (hn : 1 ≤ n) :
    realHafnianSmallBallCoefficient (n + 1) =
      realHafnianSmallBallCoefficient n *
        (Real.sqrt ((n : ℝ) + 1 / 2) * Real.Gamma (n : ℝ) /
          Real.Gamma ((n : ℝ) + 1 / 2)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hG : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnR
  have hGh : 0 < Real.Gamma ((n : ℝ) + 1 / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hsqrtFactor :
      Real.sqrt ((2 * n + 1 : ℕ) : ℝ) =
        Real.sqrt 2 * Real.sqrt ((n : ℝ) + 1 / 2) := by
    rw [show ((2 * n + 1 : ℕ) : ℝ) =
      2 * ((n : ℝ) + 1 / 2) by push_cast; ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold realHafnianSmallBallCoefficient
  rw [sigma_succ_eq,
    Finset.prod_Icc_succ_top (by omega), hsqrtFactor]
  have harg1 : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by
    push_cast
    ring
  have harg2 : (((n + 1 : ℕ) : ℝ) - 1 / 2) =
      (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  rw [harg1, harg2]
  field_simp [hsqrt2, hG.ne', hGh.ne']

/-- The exact real one-step ratio dominates its algebraic Kershaw envelope. -/
private theorem realCoefficient_ratio_ge_algebraic (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (((1 : ℝ) + 1 / (2 * (n : ℝ))) *
        ((1 : ℝ) + 1 / (4 * (n : ℝ)))) ≤
      Real.sqrt ((n : ℝ) + 1 / 2) * Real.Gamma (n : ℝ) /
        Real.Gamma ((n : ℝ) + 1 / 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hG : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnR
  have hGh : 0 < Real.Gamma ((n : ℝ) + 1 / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hk := sqrt_add_quarter_le_Gamma_ratio n hn
  rw [Real.Gamma_add_one hnR.ne'] at hk
  have hk' : Real.sqrt ((n : ℝ) + 1 / 4) / (n : ℝ) ≤
      Real.Gamma (n : ℝ) / Real.Gamma ((n : ℝ) + 1 / 2) := by
    apply (div_le_iff₀ hnR).2
    calc
      Real.sqrt ((n : ℝ) + 1 / 4) ≤
          (n : ℝ) * Real.Gamma (n : ℝ) /
            Real.Gamma ((n : ℝ) + 1 / 2) := hk
      _ = (Real.Gamma (n : ℝ) /
          Real.Gamma ((n : ℝ) + 1 / 2)) * (n : ℝ) := by ring
  have hsqrt : Real.sqrt (((1 : ℝ) + 1 / (2 * (n : ℝ))) *
        ((1 : ℝ) + 1 / (4 * (n : ℝ)))) =
      Real.sqrt ((n : ℝ) + 1 / 2) *
        (Real.sqrt ((n : ℝ) + 1 / 4) / (n : ℝ)) := by
    have hrad : 0 ≤ (((1 : ℝ) + 1 / (2 * (n : ℝ))) *
        ((1 : ℝ) + 1 / (4 * (n : ℝ)))) := by positivity
    have hrhs : 0 ≤ Real.sqrt ((n : ℝ) + 1 / 2) *
        (Real.sqrt ((n : ℝ) + 1 / 4) / (n : ℝ)) := by positivity
    rw [← sq_eq_sq₀ (Real.sqrt_nonneg _) hrhs,
      Real.sq_sqrt hrad, mul_pow, div_pow,
      Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1 / 2),
      Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1 / 4)]
    field_simp [hnR.ne']
  rw [hsqrt]
  calc
    Real.sqrt ((n : ℝ) + 1 / 2) *
        (Real.sqrt ((n : ℝ) + 1 / 4) / (n : ℝ)) ≤
      Real.sqrt ((n : ℝ) + 1 / 2) *
        (Real.Gamma (n : ℝ) / Real.Gamma ((n : ℝ) + 1 / 2)) :=
      mul_le_mul_of_nonneg_left hk' (Real.sqrt_nonneg _)
    _ = Real.sqrt ((n : ℝ) + 1 / 2) * Real.Gamma (n : ℝ) /
        Real.Gamma ((n : ℝ) + 1 / 2) := by ring

/-- The elementary polynomial comparison that turns the Kershaw envelope
into the exponent `3/8`. -/
private theorem real_rpow_ratio_le_algebraic (n : ℕ) (hn : 1 ≤ n) :
    ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (3 / 8 : ℝ)) ≤
      Real.sqrt (((1 : ℝ) + 1 / (2 * (n : ℝ))) *
        ((1 : ℝ) + 1 / (4 * (n : ℝ)))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (n : ℝ)
  let A : ℝ := (1 + u / 2) * (1 + u / 4)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoly : (1 + u) ^ 3 ≤ A ^ 4 := by
    have hu2 : 0 ≤ u ^ 2 := by positivity
    have hu3 : 0 ≤ u ^ 3 := by positivity
    have hu4 : 0 ≤ u ^ 4 := by positivity
    have hu5 : 0 ≤ u ^ 5 := by positivity
    have hu6 : 0 ≤ u ^ 6 := by positivity
    have hu7 : 0 ≤ u ^ 7 := by positivity
    have hu8 : 0 ≤ u ^ 8 := by positivity
    dsimp [A]
    nlinarith [hu2, hu3, hu4, hu5, hu6, hu7, hu8]
  have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1 + u) ^ 3)
    hpoly (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hleft : ((1 + u) ^ 3) ^ (1 / 8 : ℝ) =
      (1 + u) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1 + u)]
    norm_num
  have hright : (A ^ 4) ^ (1 / 8 : ℝ) = Real.sqrt A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA, Real.sqrt_eq_rpow]
    norm_num
  have hmain : (1 + u) ^ (3 / 8 : ℝ) ≤ Real.sqrt A := by
    rw [← hleft, ← hright]
    exact hrpow
  have hratio : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) = 1 + u := by
    dsimp [u]
    push_cast
    field_simp [hnR.ne']
  have hAeq : A = (((1 : ℝ) + 1 / (2 * (n : ℝ))) *
        ((1 : ℝ) + 1 / (4 * (n : ℝ)))) := by
    dsimp [A, u]
    ring
  rw [hratio, ← hAeq]
  exact hmain

private theorem realCoefficient_nonneg (n : ℕ) :
    0 ≤ realHafnianSmallBallCoefficient n := by
  unfold realHafnianSmallBallCoefficient
  refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sigma_nonneg n)) ?_
  exact Finset.prod_nonneg fun r hr ↦ by
    have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    exact div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
      (mul_nonneg (Real.sqrt_nonneg _)
        (Real.Gamma_pos_of_pos (by linarith)).le)

/-- Matching lower power bound for the exact real coefficient.  Equality at
`n=1` makes the constant `sqrt (2/pi)` sharp over all positive dimensions. -/
theorem realCoefficient_ge_sqrt_two_div_pi_mul_rpow
    (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 / Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) ≤
      realHafnianSmallBallCoefficient n := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    Real.sqrt (2 / Real.pi) * (j : ℝ) ^ (3 / 8 : ℝ) ≤
      realHafnianSmallBallCoefficient j
  have hind : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · dsimp only [P]
      norm_num [realHafnianSmallBallCoefficient, sigma, oddPairingNat]
    · intro j hj ih
      dsimp only [P] at ih ⊢
      rw [realCoefficient_succ_eq_mul_ratio j hj]
      let q : ℝ := Real.sqrt ((j : ℝ) + 1 / 2) * Real.Gamma (j : ℝ) /
        Real.Gamma ((j : ℝ) + 1 / 2)
      let r : ℝ := ((((j + 1 : ℕ) : ℝ) / (j : ℝ)) ^ (3 / 8 : ℝ))
      have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
      have hrnonneg : 0 ≤ r := Real.rpow_nonneg (by positivity) _
      have hrq : r ≤ q := by
        dsimp only [r, q]
        exact (real_rpow_ratio_le_algebraic j hj).trans
          (realCoefficient_ratio_ge_algebraic j hj)
      have hpower : (((j + 1 : ℕ) : ℝ) ^ (3 / 8 : ℝ)) =
          (j : ℝ) ^ (3 / 8 : ℝ) * r := by
        have hfactor : (((j + 1 : ℕ) : ℝ) : ℝ) =
            (j : ℝ) * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) := by
          push_cast
          field_simp [hjR.ne']
        rw [hfactor, Real.mul_rpow hjR.le (by positivity)]
      rw [hpower]
      calc
        Real.sqrt (2 / Real.pi) * ((j : ℝ) ^ (3 / 8 : ℝ) * r) =
            (Real.sqrt (2 / Real.pi) * (j : ℝ) ^ (3 / 8 : ℝ)) * r := by ring
        _ ≤ realHafnianSmallBallCoefficient j * r :=
          mul_le_mul_of_nonneg_right ih hrnonneg
        _ ≤ realHafnianSmallBallCoefficient j * q :=
          mul_le_mul_of_nonneg_left hrq (realCoefficient_nonneg j)
  exact hind

/-- Sharpness of the real lower constant at the first positive dimension. -/
theorem realCoefficient_one :
    realHafnianSmallBallCoefficient 1 = Real.sqrt (2 / Real.pi) := by
  norm_num [realHafnianSmallBallCoefficient, sigma, oddPairingNat]

/-! ## Algebraic beta-four extension

This definition is only the Gamma-product obtained by substituting
`beta=4`, `a=2` into the coefficient formula.  It is **not** a shifted
quaternionic anticoncentration theorem. -/

def algebraicBetaFourCoefficient (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * n) * (oddPairingNat n : ℝ) ^ 2 /
      Real.Gamma 3) *
    ∏ r ∈ Finset.Icc 2 n,
      Real.Gamma (4 * ((r : ℝ) - 1)) /
        Real.Gamma (4 * ((r : ℝ) - 1 / 2))

/-- Exact rational recurrence of the formal beta-four Gamma product. -/
theorem algebraicBetaFourCoefficient_succ (n : ℕ) (hn : 1 ≤ n) :
    algebraicBetaFourCoefficient (n + 1) =
      algebraicBetaFourCoefficient n *
        ((4 * (n : ℝ) + 2) ^ 2 /
          ((4 * (n : ℝ)) * (4 * (n : ℝ) + 1))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let x : ℝ := 4 * (n : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hG1 : Real.Gamma (x + 1) = x * Real.Gamma x := by
    rw [Real.Gamma_add_one hx.ne']
  have hG2 : Real.Gamma (x + 2) =
      (x + 1) * (x * Real.Gamma x) := by
    rw [show x + 2 = (x + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith : x + 1 ≠ 0), hG1]
  have hnum : 4 * ((((n + 1 : ℕ) : ℝ)) - 1) = x := by
    dsimp [x]
    push_cast
    ring
  have hden : 4 * ((((n + 1 : ℕ) : ℝ)) - 1 / 2) = x + 2 := by
    dsimp [x]
    push_cast
    ring
  unfold algebraicBetaFourCoefficient
  rw [Finset.prod_Icc_succ_top (by omega), hnum, hden, hG2,
    oddPairingNat_succ, Nat.cast_mul]
  have hpow : (2 : ℝ) ^ (2 * (n + 1)) =
      (2 : ℝ) ^ (2 * n) * 4 := by
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    norm_num
  rw [hpow]
  have hGamma3 : Real.Gamma 3 ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  field_simp [hG.ne', hGamma3, hx.ne', (by linarith : x + 1 ≠ 0)]
  dsimp [x]
  push_cast
  ring

private theorem betaFour_rpow_ratio_le_rational (n : ℕ) (hn : 1 ≤ n) :
    ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (3 / 4 : ℝ)) ≤
      (4 * (n : ℝ) + 2) ^ 2 /
        ((4 * (n : ℝ)) * (4 * (n : ℝ) + 1)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (n : ℝ)
  let B : ℝ := 1 + u / 2
  let D : ℝ := 1 + u / 4
  let q : ℝ := B ^ 2 / D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcross : (1 + u) ^ 3 * D ^ 4 ≤ B ^ 8 := by
    have hu2 : 0 ≤ u ^ 2 := by positivity
    have hu3 : 0 ≤ u ^ 3 := by positivity
    have hu4 : 0 ≤ u ^ 4 := by positivity
    have hu5 : 0 ≤ u ^ 5 := by positivity
    have hu6 : 0 ≤ u ^ 6 := by positivity
    have hu7 : 0 ≤ u ^ 7 := by positivity
    have hu8 : 0 ≤ u ^ 8 := by positivity
    dsimp [B, D]
    nlinarith [hu2, hu3, hu4, hu5, hu6, hu7, hu8]
  have hqpow : (1 + u) ^ 3 ≤ q ^ 4 := by
    dsimp [q]
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hD 4)).2
    calc
      (1 + u) ^ 3 * D ^ 4 ≤ B ^ 8 := hcross
      _ = (B ^ 2) ^ 4 := by ring
  have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1 + u) ^ 3)
    hqpow (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hleft : ((1 + u) ^ 3) ^ (1 / 4 : ℝ) =
      (1 + u) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1 + u)]
    norm_num
  have hright : (q ^ 4) ^ (1 / 4 : ℝ) = q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
    norm_num
  have hmain : (1 + u) ^ (3 / 4 : ℝ) ≤ q := by
    rw [← hleft, ← hright]
    exact hrpow
  have hratio : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) = 1 + u := by
    dsimp [u]
    push_cast
    field_simp [hnR.ne']
  have hqeq : q = (4 * (n : ℝ) + 2) ^ 2 /
        ((4 * (n : ℝ)) * (4 * (n : ℝ) + 1)) := by
    dsimp [q, B, D, u]
    field_simp [hnR.ne']
    ring
  rw [hratio, ← hqeq]
  exact hmain

private theorem algebraicBetaFourCoefficient_nonneg (n : ℕ) :
    0 ≤ algebraicBetaFourCoefficient n := by
  unfold algebraicBetaFourCoefficient
  refine mul_nonneg ?_ ?_
  · positivity
  · exact Finset.prod_nonneg fun r hr ↦ by
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      exact div_nonneg (Real.Gamma_pos_of_pos (by nlinarith)).le
        (Real.Gamma_pos_of_pos (by nlinarith)).le

/-- Sharp lower power bound for the formal beta-four Gamma product.  This is
an algebraic coefficient statement only. -/
theorem algebraicBetaFourCoefficient_ge_two_mul_rpow
    (n : ℕ) (hn : 1 ≤ n) :
    2 * (n : ℝ) ^ (3 / 4 : ℝ) ≤ algebraicBetaFourCoefficient n := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    2 * (j : ℝ) ^ (3 / 4 : ℝ) ≤ algebraicBetaFourCoefficient j
  have hind : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · dsimp only [P]
      norm_num [algebraicBetaFourCoefficient, oddPairingNat]
    · intro j hj ih
      dsimp only [P] at ih ⊢
      rw [algebraicBetaFourCoefficient_succ j hj]
      let q : ℝ := (4 * (j : ℝ) + 2) ^ 2 /
        ((4 * (j : ℝ)) * (4 * (j : ℝ) + 1))
      let r : ℝ := ((((j + 1 : ℕ) : ℝ) / (j : ℝ)) ^ (3 / 4 : ℝ))
      have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
      have hrnonneg : 0 ≤ r := Real.rpow_nonneg (by positivity) _
      have hrq : r ≤ q := by
        dsimp only [r, q]
        exact betaFour_rpow_ratio_le_rational j hj
      have hpower : (((j + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) =
          (j : ℝ) ^ (3 / 4 : ℝ) * r := by
        have hfactor : (((j + 1 : ℕ) : ℝ) : ℝ) =
            (j : ℝ) * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) := by
          push_cast
          field_simp [hjR.ne']
        rw [hfactor, Real.mul_rpow hjR.le (by positivity)]
      rw [hpower]
      calc
        2 * ((j : ℝ) ^ (3 / 4 : ℝ) * r) =
            (2 * (j : ℝ) ^ (3 / 4 : ℝ)) * r := by ring
        _ ≤ algebraicBetaFourCoefficient j * r :=
          mul_le_mul_of_nonneg_right ih hrnonneg
        _ ≤ algebraicBetaFourCoefficient j * q :=
          mul_le_mul_of_nonneg_left hrq (algebraicBetaFourCoefficient_nonneg j)
  exact hind

theorem algebraicBetaFourCoefficient_one :
    algebraicBetaFourCoefficient 1 = 2 := by
  norm_num [algebraicBetaFourCoefficient, oddPairingNat]

/-! ## Bundled field-uniform endpoint -/

private theorem sqrt_two_div_pi_le_one : Real.sqrt (2 / Real.pi) ≤ 1 := by
  have hfrac : 0 ≤ 2 / Real.pi := by positivity
  have hfrac_le : 2 / Real.pi ≤ 1 := by
    apply (div_le_one Real.pi_pos).2
    linarith [Real.pi_gt_three]
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hfrac_le

theorem coefficient_ge_common_constant_mul_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 / Real.pi) * Real.sqrt (n : ℝ) ≤ coefficient n := by
  calc
    Real.sqrt (2 / Real.pi) * Real.sqrt (n : ℝ) ≤
        1 * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right sqrt_two_div_pi_le_one (Real.sqrt_nonneg _)
    _ = Real.sqrt (n : ℝ) := one_mul _
    _ ≤ coefficient n := coefficient_ge_sqrt n hn

/-- The exact common lower envelope for the two shifted fields, together with
the algebraic beta-four extension.  The beta-four conjunct does not assert a
quaternionic shifted small-ball theorem. -/
theorem sharpCommonCoefficientLowerEnvelope :
    (∀ n : ℕ, 1 ≤ n →
      Real.sqrt (2 / Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) ≤
        realHafnianSmallBallCoefficient n) ∧
    (∀ n : ℕ, 1 ≤ n →
      Real.sqrt (2 / Real.pi) * Real.sqrt (n : ℝ) ≤ coefficient n) ∧
    realHafnianSmallBallCoefficient 1 = Real.sqrt (2 / Real.pi) ∧
    (∀ n : ℕ, 1 ≤ n →
      2 * (n : ℝ) ^ (3 / 4 : ℝ) ≤ algebraicBetaFourCoefficient n) ∧
    algebraicBetaFourCoefficient 1 = 2 := by
  exact ⟨realCoefficient_ge_sqrt_two_div_pi_mul_rpow,
    coefficient_ge_common_constant_mul_sqrt, realCoefficient_one,
    algebraicBetaFourCoefficient_ge_two_mul_rpow,
    algebraicBetaFourCoefficient_one⟩

#print axioms kershawRatio_le_one
#print axioms sqrt_add_quarter_le_Gamma_ratio
#print axioms coefficient_ge_sqrt
#print axioms realCoefficient_ge_sqrt_two_div_pi_mul_rpow
#print axioms realCoefficient_one
#print axioms algebraicBetaFourCoefficient_succ
#print axioms algebraicBetaFourCoefficient_ge_two_mul_rpow
#print axioms algebraicBetaFourCoefficient_one
#print axioms sharpCommonCoefficientLowerEnvelope


end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
