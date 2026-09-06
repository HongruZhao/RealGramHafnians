import LogdetLean.GramHafnian.SymmetricGaussianHafnian.Constants
import LogdetLean.GramHafnian.CurrentPRL.CoefficientEndpoints
import LogdetLean.Coherence.BetaHalfNormalization
/-!
# Sharp polynomial bounds for the symmetric-hafnian coefficients

This module records fully proved numerical consequences of the exact
coefficient definitions.  In particular, it supplies the paper's field-uniform
constant `2 / sqrt pi`, the real and complex power envelopes, and asymptotic
saturation in the complex case.
-/

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

open Filter
open scoped Real Topology

theorem coefficient_eq_gamma (n : ℕ) (hn : 1 ≤ n) :
    coefficient n =
      2 * Real.Gamma ((n : ℝ) + 1 / 2) /
        (Real.sqrt Real.pi * Real.Gamma (n : ℝ)) := by
  rw [coefficient_centralBinomial n hn,
    ← CurrentPRL.limitingAnticoncentrationConstant_eq_centralBinomial n hn]
  rfl

/-- The complex coefficient has the sharp Wallis constant. -/
theorem coefficient_le_two_div_sqrt_pi_mul_sqrt
    (n : ℕ) (hn : 1 ≤ n) :
    coefficient n ≤ (2 / Real.sqrt Real.pi) * Real.sqrt (n : ℝ) := by
  rw [coefficient_eq_gamma n hn]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgamma :
      Real.Gamma ((n : ℝ) + 1 / 2) ≤
        Real.sqrt (n : ℝ) * Real.Gamma (n : ℝ) :=
    LogdetLean.Coherence.Gamma_add_half_le_sqrt_mul_Gamma hnR
  have hden : 0 < Real.sqrt Real.pi * Real.Gamma (n : ℝ) := by positivity
  calc
    2 * Real.Gamma ((n : ℝ) + 1 / 2) /
          (Real.sqrt Real.pi * Real.Gamma (n : ℝ)) ≤
        (2 * (Real.sqrt (n : ℝ) * Real.Gamma (n : ℝ))) /
          (Real.sqrt Real.pi * Real.Gamma (n : ℝ)) := by
            exact (div_le_div_iff_of_pos_right hden).2 (by nlinarith)
    _ = (2 / Real.sqrt Real.pi) * Real.sqrt (n : ℝ) := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos),
        (Real.Gamma_pos_of_pos hnR).ne']

/-- The complex coefficient asymptotically saturates its sharp universal
envelope, so the constant `2 / sqrt pi` cannot be decreased in a bound valid
for every positive dimension. -/
theorem coefficient_ratio_tendsto_one :
    Tendsto
      (fun n : ℕ ↦ coefficient n /
        (2 * Real.sqrt (n : ℝ) / Real.sqrt Real.pi))
      atTop (nhds 1) := by
  apply
    CurrentPRL.limitingAnticoncentrationConstant_ratio_tendsto_one.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [coefficient_eq_gamma n hn]
  rfl

/-- Equivalent unnormalized form of the sharp complex asymptotic. -/
theorem coefficient_div_sqrt_tendsto_two_div_sqrt_pi :
    Tendsto
      (fun n : ℕ ↦ coefficient n / Real.sqrt (n : ℝ))
      atTop (nhds (2 / Real.sqrt Real.pi)) := by
  have hconst : Tendsto
      (fun _ : ℕ ↦ (2 / Real.sqrt Real.pi : ℝ))
      atTop (nhds (2 / Real.sqrt Real.pi)) := tendsto_const_nhds
  have hmul := hconst.mul coefficient_ratio_tendsto_one
  have heq : ∀ᶠ n : ℕ in atTop,
      (2 / Real.sqrt Real.pi) *
          (coefficient n /
            (2 * Real.sqrt (n : ℝ) / Real.sqrt Real.pi)) =
        coefficient n / Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
    have hsqrtpi : Real.sqrt Real.pi ≠ 0 :=
      Real.sqrt_ne_zero'.mpr Real.pi_pos
    field_simp [hsqrtn, hsqrtpi]
  simpa only [mul_one] using hmul.congr' heq

/-- Exactness of the field-uniform constant: any coefficient envelope of the
form `coefficient n ≤ C * sqrt n` in every positive dimension must have
`2 / sqrt pi ≤ C`. -/
theorem two_div_sqrt_pi_le_of_coefficient_bound
    (C : ℝ)
    (hC : ∀ n : ℕ, 1 ≤ n →
      coefficient n ≤ C * Real.sqrt (n : ℝ)) :
    2 / Real.sqrt Real.pi ≤ C := by
  apply le_of_tendsto coefficient_div_sqrt_tendsto_two_div_sqrt_pi
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_le_iff₀ (Real.sqrt_pos.2 hnR)).2 (hC n hn)

/-- Watson's normalized half-step ratio, at positive integer arguments. -/
def watsonRatio (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) - (1 / 4 : ℝ)) * Real.Gamma (n : ℝ) /
    Real.Gamma ((n : ℝ) + 1 / 2)

private theorem watsonRatio_nonneg (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ watsonRatio n := by
  unfold watsonRatio
  positivity

/-- The elementary square comparison behind Watson's lower Gamma-ratio
bound. -/
private theorem watsonRatio_le_succ (n : ℕ) (hn : 1 ≤ n) :
    watsonRatio n ≤ watsonRatio (n + 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm : 0 ≤ (n : ℝ) - (1 / 4 : ℝ) := by linarith
  have hnp : 0 ≤ (n : ℝ) + (3 / 4 : ℝ) := by linarith
  have hG : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnR
  have hGh : 0 < Real.Gamma ((n : ℝ) + 1 / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hhalfne : (n : ℝ) + 1 / 2 ≠ 0 := by linarith
  have hGnext :
      Real.Gamma ((n + 1 : ℕ) : ℝ) = (n : ℝ) * Real.Gamma (n : ℝ) := by
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
      Real.Gamma_add_one hnR.ne']
  have hGhnext :
      Real.Gamma (((n + 1 : ℕ) : ℝ) + 1 / 2) =
        ((n : ℝ) + 1 / 2) * Real.Gamma ((n : ℝ) + 1 / 2) := by
    have hcast : (((n + 1 : ℕ) : ℝ) + 1 / 2) =
        ((n : ℝ) + 1 / 2) + 1 := by
      push_cast
      ring
    rw [hcast,
      Real.Gamma_add_one hhalfne]
  rw [← sq_le_sq₀ (watsonRatio_nonneg n hn)
    (watsonRatio_nonneg (n + 1) (by omega))]
  unfold watsonRatio
  rw [hGnext, hGhnext]
  have hsnext : (((n + 1 : ℕ) : ℝ) - 1 / 4) =
      (n : ℝ) + 3 / 4 := by
    push_cast
    ring
  rw [hsnext]
  simp only [div_pow, mul_pow]
  rw [Real.sq_sqrt hnm, Real.sq_sqrt hnp]
  field_simp [hG.ne', hGh.ne']
  nlinarith

private theorem watsonRatio_eq_normalized (n : ℕ) (hn : 1 ≤ n) :
    watsonRatio n =
      Real.sqrt (((n : ℝ) - 1 / 4) / (n : ℝ)) *
        LogdetLean.Coherence.gammaHalfRatioScale (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsub : 0 ≤ (n : ℝ) - 1 / 4 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Real.sqrt_div hsub]
  unfold watsonRatio LogdetLean.Coherence.gammaHalfRatioScale
  field_simp [ne_of_gt (Real.sqrt_pos.2 hnR),
    (Real.Gamma_pos_of_pos hnR).ne']

private theorem tendsto_watsonRatio_succ :
    Tendsto (fun n : ℕ ↦ watsonRatio (n + 1)) atTop (nhds 1) := by
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
  have hquot : Tendsto
      (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) - 1 / 4) /
        ((n + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    have hzero : Tendsto (fun n : ℕ ↦ (1 / 4 : ℝ) /
        ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 / 4 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
    have hfun : (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) - 1 / 4) /
        ((n + 1 : ℕ) : ℝ)) =
        (fun n : ℕ ↦ (1 : ℝ) - (1 / 4 : ℝ) /
          ((n + 1 : ℕ) : ℝ)) := by
      funext n
      have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hfun]
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hone.sub hzero
  have hsqrt : Tendsto
      (fun n : ℕ ↦ Real.sqrt ((((n + 1 : ℕ) : ℝ) - 1 / 4) /
        ((n + 1 : ℕ) : ℝ))) atTop (nhds 1) := by
    simpa using hquot.sqrt
  have hprod : Tendsto
      (fun n : ℕ ↦ Real.sqrt ((((n + 1 : ℕ) : ℝ) - 1 / 4) /
        ((n + 1 : ℕ) : ℝ)) *
        LogdetLean.Coherence.gammaHalfRatioScale ((n : ℝ) + 1))
      atTop (nhds 1) := by
    simpa using hsqrt.mul hscale
  convert hprod using 1
  funext n
  simpa only [Nat.cast_add, Nat.cast_one] using
    watsonRatio_eq_normalized (n + 1) (by omega)

private theorem watsonRatio_le_one (n : ℕ) (hn : 1 ≤ n) :
    watsonRatio n ≤ 1 := by
  let f : ℕ → ℝ := fun m ↦ watsonRatio (m + 1)
  have hmono : Monotone f := monotone_nat_of_le_succ fun m ↦
    watsonRatio_le_succ (m + 1) (by omega)
  have hlim : Tendsto f atTop (nhds 1) := by
    simpa [f] using tendsto_watsonRatio_succ
  simpa only [f, Nat.sub_add_cancel hn] using
    hmono.ge_of_tendsto hlim (n - 1)

/-- A quarter/three-quarter log-convexity consequence (Wendel's upper
half-step envelope). -/
private theorem gamma_add_three_quarter_le (x : ℝ) (hx : 0 < x) :
    Real.Gamma (x + 3 / 4) ≤ Real.Gamma x * x ^ (3 / 4 : ℝ) := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    hx (by linarith : 0 < x + 1)
    (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num : (1 / 4 : ℝ) + 3 / 4 = 1)
  have hGpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hG : 0 ≤ Real.Gamma x := hGpos.le
  rw [show (1 / 4 : ℝ) * x + 3 / 4 * (x + 1) = x + 3 / 4 by ring,
    Real.Gamma_add_one hx.ne', Real.mul_rpow hx.le hG] at h
  calc
    Real.Gamma (x + 3 / 4) ≤
        Real.Gamma x ^ (1 / 4 : ℝ) *
          (x ^ (3 / 4 : ℝ) * Real.Gamma x ^ (3 / 4 : ℝ)) := h
    _ = x ^ (3 / 4 : ℝ) *
        (Real.Gamma x ^ (1 / 4 : ℝ) * Real.Gamma x ^ (3 / 4 : ℝ)) := by ring
    _ = x ^ (3 / 4 : ℝ) * Real.Gamma x ^ ((1 / 4 : ℝ) + 3 / 4) := by
      rw [← Real.rpow_add hGpos]
    _ = Real.Gamma x * x ^ (3 / 4 : ℝ) := by norm_num; ring

private theorem real_gamma_factor_sq_le (r : ℕ) (hr : 2 ≤ r) :
    (Real.Gamma ((r : ℝ) - 1) /
      (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2))) ^ 2 ≤
      (2 * ((r : ℝ) - 5 / 4))⁻¹ := by
  have hrm1 : 1 ≤ r - 1 := by omega
  have hwatson := watsonRatio_le_one (r - 1) hrm1
  have hpos : 0 < ((r : ℝ) - 5 / 4) := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hnum : 0 < Real.Gamma ((r : ℝ) - 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hden : 0 < Real.Gamma ((r : ℝ) - 1 / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  unfold watsonRatio at hwatson
  rw [hcast] at hwatson
  have hrootarg : (r : ℝ) - 1 - 1 / 4 = (r : ℝ) - 5 / 4 := by ring
  have hgarg : (r : ℝ) - 1 + 1 / 2 = (r : ℝ) - 1 / 2 := by ring
  rw [hrootarg, hgarg] at hwatson
  have hsquare := (sq_le_sq₀ (by positivity : 0 ≤
      Real.sqrt ((r : ℝ) - 5 / 4) * Real.Gamma ((r : ℝ) - 1) /
        Real.Gamma ((r : ℝ) - 1 / 2))
    (by positivity : 0 ≤ (1 : ℝ))).2 hwatson
  rw [div_pow, mul_pow, Real.sq_sqrt hpos.le] at hsquare
  have hsqrt2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  rw [div_pow, mul_pow, hsqrt2]
  have hbase : ((r : ℝ) - 5 / 4) * Real.Gamma ((r : ℝ) - 1) ^ 2 ≤
      Real.Gamma ((r : ℝ) - 1 / 2) ^ 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hden)] at hsquare
    simpa using hsquare
  rw [div_le_iff₀ (by positivity :
    0 < 2 * Real.Gamma ((r : ℝ) - 1 / 2) ^ 2)]
  calc
    Real.Gamma ((r : ℝ) - 1) ^ 2 ≤
        Real.Gamma ((r : ℝ) - 1 / 2) ^ 2 /
          ((r : ℝ) - 5 / 4) :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hbase)
    _ = (2 * ((r : ℝ) - 5 / 4))⁻¹ *
          (2 * Real.Gamma ((r : ℝ) - 1 / 2) ^ 2) := by
      field_simp [hpos.ne']

/-- Product of the rational envelopes supplied by `real_gamma_factor_sq_le`. -/
private def realFactorEnvelopeProduct (n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n, (2 * ((r : ℝ) - 5 / 4))⁻¹

/-- Exact Gamma telescope for the rational real-field envelopes. -/
private theorem realFactorEnvelopeProduct_eq_gamma
    (n : ℕ) (hn : 1 ≤ n) :
    realFactorEnvelopeProduct n =
      Real.Gamma (3 / 4) /
        ((2 : ℝ) ^ (n - 1) * Real.Gamma ((n : ℝ) - 1 / 4)) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    realFactorEnvelopeProduct j =
      Real.Gamma (3 / 4) /
        ((2 : ℝ) ^ (j - 1) * Real.Gamma ((j : ℝ) - 1 / 4))
  apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
  · dsimp [P]
    have hG : Real.Gamma (3 / 4) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by norm_num)).ne'
    norm_num [realFactorEnvelopeProduct]
    exact (div_self hG).symm
  · intro j hj ih
    change realFactorEnvelopeProduct j =
      Real.Gamma (3 / 4) /
        ((2 : ℝ) ^ (j - 1) * Real.Gamma ((j : ℝ) - 1 / 4)) at ih
    change realFactorEnvelopeProduct (j + 1) =
      Real.Gamma (3 / 4) /
        ((2 : ℝ) ^ (j + 1 - 1) *
          Real.Gamma (((j + 1 : ℕ) : ℝ) - 1 / 4))
    have hx : 0 < (j : ℝ) - 1 / 4 := by
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have hrec :
        Real.Gamma (((j + 1 : ℕ) : ℝ) - 1 / 4) =
          ((j : ℝ) - 1 / 4) * Real.Gamma ((j : ℝ) - 1 / 4) := by
      have harg : (((j + 1 : ℕ) : ℝ) - 1 / 4) =
          ((j : ℝ) - 1 / 4) + 1 := by
        push_cast
        ring
      rw [harg, Real.Gamma_add_one hx.ne']
    unfold realFactorEnvelopeProduct at ih ⊢
    rw [Finset.prod_Icc_succ_top (by omega), ih, hrec]
    have htwo : (2 : ℝ) ^ (j - 1) ≠ 0 := by positivity
    have hG : Real.Gamma ((j : ℝ) - 1 / 4) ≠ 0 :=
      (Real.Gamma_pos_of_pos hx).ne'
    rw [show j + 1 - 1 = j by omega,
      show j = (j - 1) + 1 by omega, pow_succ]
    push_cast
    field_simp [htwo, hG, hx.ne']
    ring

private theorem realHafnianSmallBallCoefficient_sq_le_envelope (n : ℕ) :
    realHafnianSmallBallCoefficient n ^ 2 ≤
      (2 / Real.pi) * (oddPairingNat n : ℝ) *
        realFactorEnvelopeProduct n := by
  have hprod :
      (∏ r ∈ Finset.Icc 2 n,
        Real.Gamma ((r : ℝ) - 1) /
          (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2))) ^ 2 ≤
        realFactorEnvelopeProduct n := by
    calc
      (∏ r ∈ Finset.Icc 2 n,
        Real.Gamma ((r : ℝ) - 1) /
          (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2))) ^ 2 =
          ∏ r ∈ Finset.Icc 2 n,
            (Real.Gamma ((r : ℝ) - 1) /
              (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2))) ^ 2 :=
        (Finset.prod_pow _ _ _).symm
      _ ≤ realFactorEnvelopeProduct n := by
        unfold realFactorEnvelopeProduct
        refine Finset.prod_le_prod ?_ ?_
        · intro r hr
          positivity
        · intro r hr
          exact real_gamma_factor_sq_le r (Finset.mem_Icc.mp hr).1
  unfold realHafnianSmallBallCoefficient
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi),
    sigma_sq]
  calc
    (2 / Real.pi) * (oddPairingNat n : ℝ) *
        (∏ r ∈ Finset.Icc 2 n,
          Real.Gamma ((r : ℝ) - 1) /
            (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2))) ^ 2 ≤
        (2 / Real.pi) * (oddPairingNat n : ℝ) *
          realFactorEnvelopeProduct n :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := rfl

private theorem oddPairingNat_cast_eq_gamma (n : ℕ) :
    (oddPairingNat n : ℝ) =
      (2 : ℝ) ^ n * Real.Gamma ((n : ℝ) + 1 / 2) /
        Real.sqrt Real.pi := by
  have h := Real.Gamma_nat_add_half n
  rw [← oddPairingNat_eq_doubleFactorial] at h
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  rw [h]
  field_simp [htwo, hsqrt]

private theorem realHafnianSmallBallCoefficient_sq_le_gamma_envelope
    (n : ℕ) (hn : 1 ≤ n) :
    realHafnianSmallBallCoefficient n ^ 2 ≤
      (4 / (Real.pi * Real.sqrt Real.pi)) *
        (Real.Gamma ((n : ℝ) + 1 / 2) * Real.Gamma (3 / 4) /
          Real.Gamma ((n : ℝ) - 1 / 4)) := by
  calc
    realHafnianSmallBallCoefficient n ^ 2 ≤
        (2 / Real.pi) * (oddPairingNat n : ℝ) *
          realFactorEnvelopeProduct n :=
      realHafnianSmallBallCoefficient_sq_le_envelope n
    _ = (4 / (Real.pi * Real.sqrt Real.pi)) *
        (Real.Gamma ((n : ℝ) + 1 / 2) * Real.Gamma (3 / 4) /
          Real.Gamma ((n : ℝ) - 1 / 4)) := by
      rw [oddPairingNat_cast_eq_gamma,
        realFactorEnvelopeProduct_eq_gamma n hn]
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hsqrt : Real.sqrt Real.pi ≠ 0 :=
        Real.sqrt_ne_zero'.mpr Real.pi_pos
      have hG : Real.Gamma ((n : ℝ) - 1 / 4) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith)).ne'
      have hpow : (2 : ℝ) ^ n * 2 = (2 : ℝ) ^ (n - 1) * 4 := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [show 1 + m - 1 = m by omega,
          show 1 + m = m + 1 by omega, pow_succ]
        ring
      field_simp [hpi, hsqrt, hG]
      rw [show ((n : ℝ) * 4 - 1) / 4 = (n : ℝ) - 1 / 4 by ring]
      calc
        2 * (2 : ℝ) ^ n / Real.Gamma ((n : ℝ) - 1 / 4) =
            ((2 : ℝ) ^ n * 2) / Real.Gamma ((n : ℝ) - 1 / 4) := by ring
        _ = _ := by rw [hpow]; ring

private theorem Gamma_three_quarter_le_sqrt_pi :
    Real.Gamma (3 / 4) ≤ Real.sqrt Real.pi := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [show (1 / 2 : ℝ) * (1 / 2) + 1 / 2 * 1 = 3 / 4 by ring,
    Real.Gamma_one_half_eq, Real.Gamma_one, Real.one_rpow, mul_one,
    ← Real.sqrt_eq_rpow] at h
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hsqrtpi : 1 ≤ Real.sqrt Real.pi := by
    rw [← sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1)
      (Real.sqrt_nonneg Real.pi), one_pow, Real.sq_sqrt Real.pi_pos.le]
    exact hpi
  have hsqrtsqrt : Real.sqrt (Real.sqrt Real.pi) ≤ Real.sqrt Real.pi := by
    have hsq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
      Real.sq_sqrt Real.pi_pos.le
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt Real.pi_pos.le]
    nlinarith [hsq]
  exact h.trans hsqrtsqrt

private theorem realHafnianSmallBallCoefficient_sq_le_power
    (n : ℕ) (hn : 1 ≤ n) :
    realHafnianSmallBallCoefficient n ^ 2 ≤
      (4 / Real.pi) * (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let x : ℝ := (n : ℝ) - 1 / 4
  have hx : 0 < x := by dsimp [x]; linarith
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hwendel : Real.Gamma ((n : ℝ) + 1 / 2) ≤
      Real.Gamma x * x ^ (3 / 4 : ℝ) := by
    have h := gamma_add_three_quarter_le x hx
    convert h using 1
    dsimp [x]
    ring
  have hratio : Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma x ≤
      x ^ (3 / 4 : ℝ) := by
    exact (div_le_iff₀ hGx).2 (by simpa [mul_comm] using hwendel)
  have hxle : x ≤ (n : ℝ) := by dsimp [x]; linarith
  have hrpow : x ^ (3 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hx.le hxle (by norm_num)
  have hgammaProduct :
      Real.Gamma ((n : ℝ) + 1 / 2) * Real.Gamma (3 / 4) /
          Real.Gamma x ≤
        (n : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    calc
      Real.Gamma ((n : ℝ) + 1 / 2) * Real.Gamma (3 / 4) /
          Real.Gamma x =
          (Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma x) *
            Real.Gamma (3 / 4) := by ring
      _ ≤ x ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4) :=
        mul_le_mul hratio le_rfl (Real.Gamma_pos_of_pos (by norm_num)).le
          (Real.rpow_nonneg hx.le _)
      _ ≤ (n : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt Real.pi :=
        mul_le_mul hrpow Gamma_three_quarter_le_sqrt_pi
          (Real.Gamma_pos_of_pos (by norm_num)).le
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  calc
    realHafnianSmallBallCoefficient n ^ 2 ≤
        (4 / (Real.pi * Real.sqrt Real.pi)) *
          (Real.Gamma ((n : ℝ) + 1 / 2) * Real.Gamma (3 / 4) /
            Real.Gamma ((n : ℝ) - 1 / 4)) :=
      realHafnianSmallBallCoefficient_sq_le_gamma_envelope n hn
    _ ≤ (4 / (Real.pi * Real.sqrt Real.pi)) *
        ((n : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt Real.pi) := by
      exact mul_le_mul_of_nonneg_left (by simpa [x] using hgammaProduct)
        (by positivity)
    _ = (4 / Real.pi) * (n : ℝ) ^ (3 / 4 : ℝ) := by
      field_simp [Real.pi_ne_zero,
        (Real.sqrt_ne_zero'.mpr Real.pi_pos)]

/-- The real shifted coefficient has the universal polynomial envelope with
the same sharp field-uniform constant as the complex coefficient. -/
theorem realHafnianSmallBallCoefficient_le_two_div_sqrt_pi_mul_rpow
    (n : ℕ) (hn : 1 ≤ n) :
    realHafnianSmallBallCoefficient n ≤
      (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcoef : 0 ≤ realHafnianSmallBallCoefficient n := by
    unfold realHafnianSmallBallCoefficient
    refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sigma_nonneg n)) ?_
    exact Finset.prod_nonneg fun r hr ↦ by
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      have hnum : 0 < Real.Gamma ((r : ℝ) - 1) :=
        Real.Gamma_pos_of_pos (by linarith)
      have hden : 0 < Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2) := by
        exact mul_pos (Real.sqrt_pos.2 (by norm_num))
          (Real.Gamma_pos_of_pos (by linarith))
      exact (div_nonneg hnum.le hden.le)
  have hrhs : 0 ≤
      (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) := by
    positivity
  rw [← sq_le_sq₀ hcoef hrhs]
  calc
    realHafnianSmallBallCoefficient n ^ 2 ≤
        (4 / Real.pi) * (n : ℝ) ^ (3 / 4 : ℝ) :=
      realHafnianSmallBallCoefficient_sq_le_power n hn
    _ = ((2 / Real.sqrt Real.pi) *
        (n : ℝ) ^ (3 / 8 : ℝ)) ^ 2 := by
      have hpow : ((n : ℝ) ^ (3 / 8 : ℝ)) ^ 2 =
          (n : ℝ) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hnR.le]
        norm_num
      rw [mul_pow, div_pow, Real.sq_sqrt Real.pi_pos.le, hpow]
      norm_num

/-- Paper-facing bundled endpoint: both finite field envelopes and exactness
of their common universal constant. -/
theorem sharpFieldUniformCoefficientEnvelope :
    (∀ n : ℕ, 1 ≤ n →
      coefficient n ≤
        (2 / Real.sqrt Real.pi) * Real.sqrt (n : ℝ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      realHafnianSmallBallCoefficient n ≤
        (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ)) ∧
    (∀ C : ℝ,
      (∀ n : ℕ, 1 ≤ n →
        coefficient n ≤ C * Real.sqrt (n : ℝ)) →
      2 / Real.sqrt Real.pi ≤ C) := by
  exact ⟨coefficient_le_two_div_sqrt_pi_mul_sqrt,
    realHafnianSmallBallCoefficient_le_two_div_sqrt_pi_mul_rpow,
    two_div_sqrt_pi_le_of_coefficient_bound⟩

#print axioms coefficient_le_two_div_sqrt_pi_mul_sqrt
#print axioms coefficient_ratio_tendsto_one
#print axioms coefficient_div_sqrt_tendsto_two_div_sqrt_pi
#print axioms two_div_sqrt_pi_le_of_coefficient_bound
#print axioms realHafnianSmallBallCoefficient_le_two_div_sqrt_pi_mul_rpow
#print axioms sharpFieldUniformCoefficientEnvelope
#print axioms watsonRatio_le_one
#print axioms gamma_add_three_quarter_le
#print axioms real_gamma_factor_sq_le

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
