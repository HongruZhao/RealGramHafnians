import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGammaCoefficient
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralGramTailPolynomial
/-!
# Polynomial bounds for the literal beta-one coefficient

This file bounds the elementary dimension-loss product at the paper scale
and assembles the exact finite theorem into its eventual polynomial form.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- The elementary numerator inequality used in every `P_ent` factor. -/
theorem sqrt_one_add_le_exp_half {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ Real.exp (x / 2) := by
  calc
    Real.sqrt (1 + x) ≤ 1 + x / 2 :=
      Real.sqrt_one_add_le (by linarith)
    _ ≤ Real.exp (x / 2) := by
      simpa [add_comm] using Real.add_one_le_exp (x / 2)

/-- For `0 ≤ delta ≤ 1/2`, the inverse square-root denominator loses
at most `exp delta`. -/
theorem inv_sqrt_one_sub_le_exp
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2) :
    (Real.sqrt (1 - delta))⁻¹ ≤ Real.exp delta := by
  have hbase : 0 < 1 - delta := by linarith
  apply (inv_le_iff_one_le_mul₀ (Real.sqrt_pos.2 hbase)).2
  rw [← sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ Real.exp delta * Real.sqrt (1 - delta))]
  have hlin : 1 ≤ (1 + 2 * delta) * (1 - delta) := by
    nlinarith
  have hexp : 1 + 2 * delta ≤ Real.exp (2 * delta) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * delta)
  calc
    (1 : ℝ) ^ 2 ≤ (1 + 2 * delta) * (1 - delta) := by simpa using hlin
    _ ≤ Real.exp (2 * delta) * (1 - delta) :=
      mul_le_mul_of_nonneg_right hexp hbase.le
    _ = (Real.exp delta * Real.sqrt (1 - delta)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hbase.le, pow_two, ← Real.exp_add]
      ring_nf

/-- One raw `P_ent` factor in the exact normalization equals its displayed
dimensionless paper form. -/
theorem realElementaryPEnt_factor_eq_displayed
    {k r : ℕ} (hk : 0 < k) (hr : 1 ≤ r)
    {delta : ℝ} (hdeltalt : delta < 1) :
    Real.sqrt ((k : ℝ) + 2 * (r : ℝ) - 2) *
        (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ =
      Real.sqrt (1 + (2 * (r : ℝ) - 2) / (k : ℝ)) *
        (Real.sqrt (1 - delta))⁻¹ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hshift : 0 ≤ 2 * (r : ℝ) - 2 := by
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hratio : 0 ≤ 1 + (2 * (r : ℝ) - 2) / (k : ℝ) := by
    positivity
  have hfactor :
      (k : ℝ) + 2 * (r : ℝ) - 2 =
        (k : ℝ) * (1 + (2 * (r : ℝ) - 2) / (k : ℝ)) := by
    field_simp
    ring
  rw [hfactor, Real.sqrt_mul hkR.le, Real.sqrt_mul hkR.le]
  have hsqrtk : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.2 hkR).ne'
  field_simp [hsqrtk]

/-- Every elementary dimension-loss factor is bounded by the exponential
of its numerator increment plus `delta`. -/
theorem realElementaryPEnt_factor_le_exp
    {k r : ℕ} (hk : 0 < k) (hr : 1 ≤ r)
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2) :
    Real.sqrt ((k : ℝ) + 2 * (r : ℝ) - 2) *
        (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ ≤
      Real.exp (((r : ℝ) - 1) / (k : ℝ) + delta) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx : 0 ≤ (2 * (r : ℝ) - 2) / (k : ℝ) := by
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    exact div_nonneg (by linarith) hkR.le
  rw [realElementaryPEnt_factor_eq_displayed hk hr (by linarith)]
  calc
    Real.sqrt (1 + (2 * (r : ℝ) - 2) / (k : ℝ)) *
          (Real.sqrt (1 - delta))⁻¹ ≤
        Real.exp (((2 * (r : ℝ) - 2) / (k : ℝ)) / 2) *
          Real.exp delta :=
      mul_le_mul (sqrt_one_add_le_exp_half hx)
        (inv_sqrt_one_sub_le_exp hdelta0 hdeltahalf)
        (by positivity) (by positivity)
    _ = Real.exp (((r : ℝ) - 1) / (k : ℝ) + delta) := by
      rw [← Real.exp_add]
      congr 1
      field_simp

/-- Exact finite exponential envelope for the elementary product. -/
theorem realElementaryPEnt_le_exp_exact
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k)
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2) :
    realElementaryPEnt n k delta ≤
      Real.exp
        ((n : ℝ) * ((n : ℝ) - 1) / (2 * (k : ℝ)) +
          ((n : ℝ) - 1) * delta) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    realElementaryPEnt j k delta ≤
      Real.exp
        ((j : ℝ) * ((j : ℝ) - 1) / (2 * (k : ℝ)) +
          ((j : ℝ) - 1) * delta)
  have hP : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · dsimp [P]
      simp [realElementaryPEnt]
    · intro j hj ih
      dsimp [P] at ih ⊢
      rw [realElementaryPEnt_succ j k hj delta]
      have hfactor := realElementaryPEnt_factor_le_exp
        (k := k) (r := j + 1) hk (by omega) hdelta0 hdeltahalf
      have hleft :
          (k : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) - 2 =
            (k : ℝ) + 2 * (j : ℝ) := by
        push_cast
        ring
      have hright :
          (((j + 1 : ℕ) : ℝ) - 1) / (k : ℝ) + delta =
            (j : ℝ) / (k : ℝ) + delta := by
        push_cast
        ring
      rw [hleft, hright] at hfactor
      calc
        realElementaryPEnt j k delta *
            (Real.sqrt ((k : ℝ) + 2 * (j : ℝ)) *
              (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹) ≤
            Real.exp
                ((j : ℝ) * ((j : ℝ) - 1) / (2 * (k : ℝ)) +
                  ((j : ℝ) - 1) * delta) *
              Real.exp ((j : ℝ) / (k : ℝ) + delta) := by
          apply mul_le_mul ih
          · exact hfactor
          · positivity
          · positivity
        _ = Real.exp
            (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) /
                (2 * (k : ℝ)) +
              (((j + 1 : ℕ) : ℝ) - 1) * delta) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          field_simp
          ring
  exact hP

/-- Paper-displayed (slightly weakened) finite `P_ent` bound. -/
theorem realElementaryPEnt_le_exp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k)
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2) :
    realElementaryPEnt n k delta ≤
      Real.exp
        ((n : ℝ) * ((n : ℝ) - 1) / (2 * (k : ℝ)) +
          (n : ℝ) * delta) := by
  refine (realElementaryPEnt_le_exp_exact hn hk hdelta0 hdeltahalf).trans ?_
  rw [Real.exp_le_exp]
  nlinarith

/-- The logarithmic threshold is eventually at most `1/2`. -/
theorem eventually_real_logarithmic_threshold_le_half
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop,
      L * Real.log (n : ℝ) / (n : ℝ) ≤ 1 / 2 := by
  have hratio : Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hdeltaT : Tendsto (fun n : ℕ ↦
      L * Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ L) atTop (nhds L) :=
      tendsto_const_nhds
    have h := hconst.mul hratio
    convert h using 1
    · funext n
      ring
    · simp
  exact (hdeltaT.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).mono
    fun _ h ↦ h.le

/-- The paper cross-growth condition eventually implies the convenient
coarse inequality `n² ≤ k_n`. -/
theorem eventually_nat_sq_le_of_real_cross_growth
    (kseq : ℕ → ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hcross : ∀ᶠ n : ℕ in atTop,
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (kseq n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, n ^ 2 ≤ kseq n := by
  obtain ⟨N, hN⟩ := exists_nat_gt (L ^ 2)
  filter_upwards [eventually_ge_atTop (max 2 N), hcross] with n hn hc
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 N) hn
  have hNn : N ≤ n := le_trans (le_max_right 2 N) hn
  let x : ℝ := n
  have hx2 : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast hn2
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx2
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx2
  have hLsq : L ^ 2 ≤ x := by
    dsimp [x]
    exact (le_of_lt hN).trans (by exact_mod_cast hNn)
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hlogle : Real.log x ≤ x := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hDpos : 0 < L ^ 2 * Real.log x := by positivity
  have hDle : L ^ 2 * Real.log x ≤ x ^ 2 := by
    calc
      L ^ 2 * Real.log x ≤ x * x :=
        mul_le_mul hLsq hlogle (Real.log_nonneg hx1.le) (by positivity)
      _ = x ^ 2 := by ring
  have hcoef : (1 : ℝ) ≤ 32 * (A + 5) := by nlinarith
  have hx4nonneg : 0 ≤ x ^ 4 := by positivity
  have hsmall : x ^ 2 * (L ^ 2 * Real.log x) ≤
      32 * (A + 5) * x ^ 4 := by
    calc
      x ^ 2 * (L ^ 2 * Real.log x) ≤ x ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_left hDle (by positivity)
      _ = x ^ 4 := by ring
      _ ≤ 32 * (A + 5) * x ^ 4 :=
        by simpa using mul_le_mul_of_nonneg_right hcoef hx4nonneg
  have hkreal : x ^ 2 ≤ (kseq n : ℝ) := by
    apply le_trans (b :=
      (32 * (A + 5) * x ^ 4) / (L ^ 2 * Real.log x))
    · exact (le_div_iff₀ hDpos).2 hsmall
    · apply (div_le_iff₀ hDpos).2
      calc
        32 * (A + 5) * x ^ 4 ≤
            L ^ 2 * Real.log x * (kseq n : ℝ) := by
          simpa [x] using hc
        _ = (kseq n : ℝ) * (L ^ 2 * Real.log x) := by ring
  dsimp [x] at hkreal
  exact_mod_cast hkreal

/-- Under a unit bound on the harmless `n²/k` correction, the complete
paper coefficient has a simple `2 e n n^L` envelope. -/
theorem realElementaryPaperCoefficient_le_coarse
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    {A L delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdeltahalf : delta ≤ 1 / 2)
    (hdimloss :
      (n : ℝ) * ((n : ℝ) - 1) / (2 * (k : ℝ)) ≤ 1)
    (hdeltaScale : (n : ℝ) * delta = L * Real.log (n : ℝ)) :
    realElementaryBk k * realElementaryKn n *
        realElementaryPEnt n k delta ≤
      2 * Real.exp 1 * (n : ℝ) * (n : ℝ) ^ L := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hK : realElementaryKn n ≤ (n : ℝ) := by
    calc
      realElementaryKn n ≤
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) :=
        realElementaryKn_le_sqrt_odd hn
      _ ≤ (n : ℝ) := by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hcast : (((2 * n - 1 : ℕ) : ℝ)) =
              2 * (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
            push_cast
            ring
          rw [hcast]
          nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hP : realElementaryPEnt n k delta ≤
      Real.exp 1 * (n : ℝ) ^ L := by
    calc
      realElementaryPEnt n k delta ≤
          Real.exp
            ((n : ℝ) * ((n : ℝ) - 1) / (2 * (k : ℝ)) +
              (n : ℝ) * delta) :=
        realElementaryPEnt_le_exp hn (by omega) hdelta0 hdeltahalf
      _ ≤ Real.exp (1 + L * Real.log (n : ℝ)) := by
        rw [Real.exp_le_exp, hdeltaScale]
        linarith
      _ = Real.exp 1 * (n : ℝ) ^ L := by
        rw [Real.exp_add, Real.rpow_def_of_pos hnpos]
        congr 2
        ring
  calc
    realElementaryBk k * realElementaryKn n *
        realElementaryPEnt n k delta ≤
      2 * (n : ℝ) * (Real.exp 1 * (n : ℝ) ^ L) := by
        exact mul_le_mul
          (mul_le_mul (realElementaryBk_le_two hk) hK
            realElementaryKn_pos.le (by norm_num))
          hP (realElementaryPEnt_pos (by omega) (by linarith)).le
          (by positivity)
    _ = 2 * Real.exp 1 * (n : ℝ) * (n : ℝ) ^ L := by ring

/-- A fixed numerical threshold absorbs the harmless constant in the
coefficient envelope. -/
theorem four_exp_mul_rpow_succ_le_half_rpow
    {x A : ℝ} (hx : 8 * Real.exp 1 ≤ x) :
    4 * Real.exp 1 * x ^ (-(A + 1)) ≤
      (1 / 2 : ℝ) * x ^ (-A) := by
  have hxpos : 0 < x := (mul_pos (by norm_num) (Real.exp_pos 1)).trans_le hx
  rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hxpos]
  have hexponent : Real.log x * (-(A + 1)) =
      Real.log x * (-A) - Real.log x := by ring
  rw [hexponent, Real.exp_sub, Real.exp_log hxpos]
  rw [show 4 * Real.exp 1 *
      (Real.exp (Real.log x * -A) / x) =
      (4 * Real.exp 1 * Real.exp (Real.log x * -A)) / x by ring]
  apply (div_le_iff₀ hxpos).2
  have hE : 0 < Real.exp (Real.log x * -A) := Real.exp_pos _
  nlinarith

/-- Under the paper cross-growth condition, the normalized linear term at
radius `n^{-(A+L+2)}` uses at most half of the target `n^{-A}` budget. -/
theorem eventually_two_mul_realElementaryPaperCoefficient_mul_radius_le_half_polynomial
    (kseq : ℕ → ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hcross : ∀ᶠ n : ℕ in atTop,
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (kseq n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ENNReal) *
          ENNReal.ofReal
            (realElementaryBk (kseq n) * realElementaryKn n *
              realElementaryPEnt n (kseq n)
                (L * Real.log (n : ℝ) / (n : ℝ))) *
          ENNReal.ofReal ((n : ℝ) ^ (-(A + L + 2))) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-A)) := by
  have hparams := eventually_real_literal_anticoncentration_parameters
    kseq hA hL hcross
  have hhalf := eventually_real_logarithmic_threshold_le_half hL
  have hsq := eventually_nat_sq_le_of_real_cross_growth
    kseq hA hL hcross
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * Real.exp 1)
  filter_upwards [eventually_ge_atTop (max 1 N), hparams, hhalf, hsq]
      with n hn hpar hδhalf hnsq
  let delta : ℝ := L * Real.log (n : ℝ) / (n : ℝ)
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hNn : N ≤ n := le_trans (le_max_right 1 N) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hk : 2 ≤ kseq n := hpar.2.1
  have hkR : (0 : ℝ) < (kseq n : ℝ) := by positivity
  have hdelta0 : 0 ≤ delta := hpar.2.2.1
  have hdeltalt : delta < 1 := hpar.2.2.2
  have hdimloss :
      (n : ℝ) * ((n : ℝ) - 1) /
          (2 * (kseq n : ℝ)) ≤ 1 := by
    have hsqR : (n : ℝ) ^ 2 ≤ (kseq n : ℝ) := by
      exact_mod_cast hnsq
    have hnum : (n : ℝ) * ((n : ℝ) - 1) ≤
        (n : ℝ) ^ 2 := by nlinarith
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * (kseq n : ℝ))).2
    nlinarith
  have hdeltaScale : (n : ℝ) * delta =
      L * Real.log (n : ℝ) := by
    dsimp [delta]
    field_simp
  have hcoef := realElementaryPaperCoefficient_le_coarse
    (n := n) (k := kseq n) hn1 hk (A := A) (L := L)
    (delta := delta) hdelta0 (by simpa [delta] using hδhalf)
    hdimloss hdeltaScale
  have hrpow :
      (n : ℝ) * (n : ℝ) ^ L *
          (n : ℝ) ^ (-(A + L + 2)) =
        (n : ℝ) ^ (-(A + 1)) := by
    calc
      (n : ℝ) * (n : ℝ) ^ L *
          (n : ℝ) ^ (-(A + L + 2)) =
        (n : ℝ) ^ (1 + L) *
          (n : ℝ) ^ (-(A + L + 2)) := by
            rw [Real.rpow_add hnpos, Real.rpow_one]
      _ = (n : ℝ) ^ ((1 + L) + (-(A + L + 2))) :=
        (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ) ^ (-(A + 1)) := by
        congr 1
        ring
  have hnconst : 8 * Real.exp 1 ≤ (n : ℝ) :=
    (le_of_lt hN).trans (by exact_mod_cast hNn)
  have hbudget :
      2 *
          (realElementaryBk (kseq n) * realElementaryKn n *
            realElementaryPEnt n (kseq n) delta) *
          (n : ℝ) ^ (-(A + L + 2)) ≤
        (1 / 2 : ℝ) * (n : ℝ) ^ (-A) := by
    calc
      2 *
          (realElementaryBk (kseq n) * realElementaryKn n *
            realElementaryPEnt n (kseq n) delta) *
          (n : ℝ) ^ (-(A + L + 2)) ≤
        2 * (2 * Real.exp 1 * (n : ℝ) * (n : ℝ) ^ L) *
          (n : ℝ) ^ (-(A + L + 2)) := by
            gcongr
      _ = 4 * Real.exp 1 * (n : ℝ) ^ (-(A + 1)) := by
        rw [← hrpow]
        ring
      _ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (-A) :=
        four_exp_mul_rpow_succ_le_half_rpow hnconst
  have hprod0 : 0 ≤
      realElementaryBk (kseq n) * realElementaryKn n *
        realElementaryPEnt n (kseq n) delta :=
    mul_nonneg
      (mul_nonneg (realElementaryBk_pos hk).le realElementaryKn_pos.le)
      (realElementaryPEnt_pos (by omega) hdeltalt).le
  have heps0 : 0 ≤ (n : ℝ) ^ (-(A + L + 2)) := by positivity
  change (2 : ENNReal) *
      ENNReal.ofReal
        (realElementaryBk (kseq n) * realElementaryKn n *
          realElementaryPEnt n (kseq n) delta) *
      ENNReal.ofReal ((n : ℝ) ^ (-(A + L + 2))) ≤ _
  calc
    (2 : ENNReal) *
        ENNReal.ofReal
          (realElementaryBk (kseq n) * realElementaryKn n *
            realElementaryPEnt n (kseq n) delta) *
        ENNReal.ofReal ((n : ℝ) ^ (-(A + L + 2))) =
      ENNReal.ofReal
        (2 *
          (realElementaryBk (kseq n) * realElementaryKn n *
            realElementaryPEnt n (kseq n) delta) *
          (n : ℝ) ^ (-(A + L + 2))) := by
            symm
            rw [ENNReal.ofReal_mul
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hprod0)]
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-A)) :=
      ENNReal.ofReal_le_ofReal hbudget

end

end LogdetLean.GramHafnian
