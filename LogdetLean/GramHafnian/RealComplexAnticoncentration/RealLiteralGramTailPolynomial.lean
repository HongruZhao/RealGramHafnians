import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralGramTailUniform
/-!
# Polynomial specialization of the literal real Gram error

Set `delta_n = L log n / n`.  The cross-multiplied growth condition

`32 (A+5) n^4 ≤ L^2 log(n) k`

implies that the accumulated bad-event probability is at most `n^{-A}`.
The cross-multiplied formulation avoids every issue caused by totalized
division at small `n`.  A final theorem packages the statement eventually
for an arbitrary natural-valued dimension sequence.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace LogdetLean.GramHafnian

noncomputable section

private theorem real_logarithmic_growth_implies_decay
    {x A L K : ℝ} (hx : 0 < x) (hlog : 0 < Real.log x)
    (hL : 0 < L) (hA : 0 ≤ A)
    (hcross :
      32 * (A + 5) * x ^ 4 ≤ L ^ 2 * Real.log x * K) :
    (A + 5) * Real.log x ≤
      K * ((L * Real.log x / x) / (2 * x)) ^ 2 / 8 := by
  have hden : 0 < L ^ 2 * Real.log x := by positivity
  have hquot :
      32 * (A + 5) * x ^ 4 / (L ^ 2 * Real.log x) ≤ K := by
    apply (div_le_iff₀ hden).2
    calc
      32 * (A + 5) * x ^ 4 ≤ L ^ 2 * Real.log x * K := hcross
      _ = K * (L ^ 2 * Real.log x) := by ring
  let s : ℝ := ((L * Real.log x / x) / (2 * x)) ^ 2 / 8
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have heq :
      (32 * (A + 5) * x ^ 4 / (L ^ 2 * Real.log x)) * s =
        (A + 5) * Real.log x := by
    dsimp [s]
    field_simp
    ring
  have hdecay5 : (A + 5) * Real.log x ≤ K * s := by
    calc
      (A + 5) * Real.log x =
          (32 * (A + 5) * x ^ 4 /
            (L ^ 2 * Real.log x)) * s := heq.symm
      _ ≤ K * s := mul_le_mul_of_nonneg_right hquot hs
  calc
    (A + 5) * Real.log x ≤ K * s := hdecay5
    _ = K * ((L * Real.log x / x) / (2 * x)) ^ 2 / 8 := by
      dsimp [s]
      ring

private theorem real_coarse_gram_error_le_exp_neg_log
    {x A E : ℝ} (hx : 8 ≤ x)
    (hE : (A + 4) * Real.log x ≤ E) :
    x * (2 * (2 * x) ^ 2 * Real.exp (-E)) ≤
      Real.exp (-A * Real.log x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx3 : 0 ≤ x ^ 3 := by positivity
  have hpoly : 8 * x ^ 3 ≤ x ^ 4 := by
    calc
      8 * x ^ 3 ≤ x * x ^ 3 := mul_le_mul_of_nonneg_right hx hx3
      _ = x ^ 4 := by ring
  have hx4 : x ^ 4 = Real.exp (4 * Real.log x) := by
    calc
      x ^ 4 = Real.exp (Real.log x) ^ 4 := by
        rw [Real.exp_log hxpos]
      _ = Real.exp (4 * Real.log x) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hexp : Real.exp (-E) ≤
      Real.exp (-((A + 4) * Real.log x)) := by
    rw [Real.exp_le_exp]
    linarith
  calc
    x * (2 * (2 * x) ^ 2 * Real.exp (-E)) =
        (8 * x ^ 3) * Real.exp (-E) := by ring
    _ ≤ x ^ 4 * Real.exp (-((A + 4) * Real.log x)) :=
      mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
    _ = Real.exp (-A * Real.log x) := by
      rw [hx4, ← Real.exp_add]
      congr 1
      ring

private theorem two_mul_rpow_succ_le_half_rpow
    {x A : ℝ} (hx : 4 ≤ x) :
    2 * x ^ (-(A + 1)) ≤ (1 / 2 : ℝ) * x ^ (-A) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hxpos]
  have hexponent : Real.log x * (-(A + 1)) =
      Real.log x * (-A) - Real.log x := by ring
  rw [hexponent, Real.exp_sub, Real.exp_log hxpos]
  rw [show 2 * (Real.exp (Real.log x * -A) / x) =
      (2 * Real.exp (Real.log x * -A)) / x by ring]
  apply (div_le_iff₀ hxpos).2
  nlinarith [Real.exp_pos (Real.log x * -A)]

/-- Explicit finite polynomial consequence.  The only threshold hypothesis
left explicit is `delta_n ≤ 1`; the eventual theorem below discharges it
for every fixed `L > 0`. -/
theorem pastRealCofactorGramBadProbabilitySum_le_polynomial_with_slack_of_cross_growth
    {n k : ℕ} {A L : ℝ}
    (hn : 8 ≤ n) (hA : 0 ≤ A) (hL : 0 < L)
    (hdelta1 : L * Real.log (n : ℝ) / (n : ℝ) ≤ 1)
    (hcross :
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (k : ℝ)) :
    pastRealCofactorGramBadProbabilitySum n k
        (L * Real.log (n : ℝ) / (n : ℝ)) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-(A + 1))) := by
  let x : ℝ := n
  let delta : ℝ := L * Real.log x / x
  have hx8 : 8 ≤ x := by
    dsimp [x]
    exact_mod_cast hn
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx8
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx8
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hden : 0 < L ^ 2 * Real.log x := by positivity
  have hquot :
      32 * (A + 5) * x ^ 4 / (L ^ 2 * Real.log x) ≤ (k : ℝ) := by
    apply (div_le_iff₀ hden).2
    calc
      32 * (A + 5) * x ^ 4 ≤
          L ^ 2 * Real.log x * (k : ℝ) := by simpa [x] using hcross
      _ = (k : ℝ) * (L ^ 2 * Real.log x) := by ring
  have hLowerPos :
      0 < 32 * (A + 5) * x ^ 4 / (L ^ 2 * Real.log x) := by
    positivity
  have hkreal : (0 : ℝ) < (k : ℝ) := hLowerPos.trans_le hquot
  have hk : 0 < k := by exact_mod_cast hkreal
  have hsum := pastRealCofactorGramBadProbabilitySum_le_uniformError
    (n := n) hk hdelta0 (by simpa [delta, x] using hdelta1)
  have hdecay : (A + 5) * Real.log x ≤
      (k : ℝ) * (delta / (2 * x)) ^ 2 / 8 := by
    have h := real_logarithmic_growth_implies_decay
      hxpos hlog hL hA (K := (k : ℝ)) (by simpa [x] using hcross)
    simpa [delta] using h
  have hreal : pastRealCofactorGramUniformErrorReal n k delta ≤
      Real.exp (-(A + 1) * Real.log x) := by
    unfold pastRealCofactorGramUniformErrorReal
      pastRealCofactorGramUniformLevelEnvelopeReal
    change x * (2 * (2 * x) ^ 2 *
      Real.exp (-((k : ℝ) * (delta / (2 * x)) ^ 2 / 8))) ≤ _
    have hdecay' : (A + 1 + 4) * Real.log x ≤
        (k : ℝ) * (delta / (2 * x)) ^ 2 / 8 := by
      convert hdecay using 1 <;> ring
    have h := real_coarse_gram_error_le_exp_neg_log
      (A := A + 1) hx8 hdecay'
    simpa using h
  have hrpow : x ^ (-(A + 1)) =
      Real.exp (-(A + 1) * Real.log x) := by
    rw [Real.rpow_def_of_pos hxpos]
    congr 1
    ring
  calc
    pastRealCofactorGramBadProbabilitySum n k
        (L * Real.log (n : ℝ) / (n : ℝ)) =
        pastRealCofactorGramBadProbabilitySum n k delta := by rfl
    _ ≤ ENNReal.ofReal
        (pastRealCofactorGramUniformErrorReal n k delta) := hsum
    _ ≤ ENNReal.ofReal (Real.exp (-(A + 1) * Real.log x)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((n : ℝ) ^ (-(A + 1))) := by rw [hrpow]

/-- Weaker finite projection of the slack theorem, retained as a convenient
`n^{-A}` interface. -/
theorem pastRealCofactorGramBadProbabilitySum_le_polynomial_of_cross_growth
    {n k : ℕ} {A L : ℝ}
    (hn : 8 ≤ n) (hA : 0 ≤ A) (hL : 0 < L)
    (hdelta1 : L * Real.log (n : ℝ) / (n : ℝ) ≤ 1)
    (hcross :
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (k : ℝ)) :
    pastRealCofactorGramBadProbabilitySum n k
        (L * Real.log (n : ℝ) / (n : ℝ)) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-A)) := by
  calc
    pastRealCofactorGramBadProbabilitySum n k
        (L * Real.log (n : ℝ) / (n : ℝ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-(A + 1))) :=
      pastRealCofactorGramBadProbabilitySum_le_polynomial_with_slack_of_cross_growth
        hn hA hL hdelta1 hcross
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-A)) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ n by omega)) (by linarith)

/-- Eventual polynomial bad-event bound under the paper-scale dimension
condition `k_n ≳ n^4 / log n`.  No upper bound on the fixed constant `L`
is needed: `L log n / n < 1` follows internally from `log n / n → 0`. -/
theorem eventually_pastRealCofactorGramBadProbabilitySum_le_polynomial_with_slack
    (kseq : ℕ → ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hcross : ∀ᶠ n : ℕ in atTop,
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (kseq n : ℝ)) :
    ∀ᶠ n in atTop,
      pastRealCofactorGramBadProbabilitySum n (kseq n)
          (L * Real.log (n : ℝ) / (n : ℝ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-(A + 1))) := by
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
  have hdelta1 : ∀ᶠ n : ℕ in atTop,
      L * Real.log (n : ℝ) / (n : ℝ) ≤ 1 :=
    (hdeltaT.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono
      fun _ hn ↦ hn.le
  filter_upwards [eventually_ge_atTop 8, hdelta1, hcross] with n hn hdelta hc
  exact pastRealCofactorGramBadProbabilitySum_le_polynomial_with_slack_of_cross_growth
    hn hA hL hdelta hc

/-- Weaker eventual `n^{-A}` projection, retained for callers that do not
need the preserved power of slack. -/
theorem eventually_pastRealCofactorGramBadProbabilitySum_le_polynomial
    (kseq : ℕ → ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hcross : ∀ᶠ n : ℕ in atTop,
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (kseq n : ℝ)) :
    ∀ᶠ n in atTop,
      pastRealCofactorGramBadProbabilitySum n (kseq n)
          (L * Real.log (n : ℝ) / (n : ℝ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-A)) := by
  have hstrong :=
    eventually_pastRealCofactorGramBadProbabilitySum_le_polynomial_with_slack
      kseq hA hL hcross
  filter_upwards [eventually_ge_atTop 1, hstrong] with n hn hbound
  calc
    pastRealCofactorGramBadProbabilitySum n (kseq n)
        (L * Real.log (n : ℝ) / (n : ℝ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-(A + 1))) := hbound
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-A)) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hn) (by linarith)

/-- The preserved slack absorbs the outer factor `2` occurring in the final
small-ball assembly, under the same paper-scale dimension condition. -/
theorem eventually_two_mul_pastRealCofactorGramBadProbabilitySum_le_half_polynomial
    (kseq : ℕ → ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hcross : ∀ᶠ n : ℕ in atTop,
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (kseq n : ℝ)) :
    ∀ᶠ n in atTop,
      (2 : ENNReal) *
          pastRealCofactorGramBadProbabilitySum n (kseq n)
            (L * Real.log (n : ℝ) / (n : ℝ)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-A)) := by
  have hstrong :=
    eventually_pastRealCofactorGramBadProbabilitySum_le_polynomial_with_slack
      kseq hA hL hcross
  filter_upwards [eventually_ge_atTop 4, hstrong] with n hn hbound
  calc
    (2 : ENNReal) *
        pastRealCofactorGramBadProbabilitySum n (kseq n)
          (L * Real.log (n : ℝ) / (n : ℝ)) ≤
        2 * ENNReal.ofReal ((n : ℝ) ^ (-(A + 1))) := by
      gcongr
    _ = ENNReal.ofReal (2 * (n : ℝ) ^ (-(A + 1))) := by
      simpa using (ENNReal.ofReal_mul
        (p := (2 : ℝ)) (q := (n : ℝ) ^ (-(A + 1)))
        (by norm_num : (0 : ℝ) ≤ 2)).symm
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-A)) := by
      apply ENNReal.ofReal_le_ofReal
      exact two_mul_rpow_succ_le_half_rpow (by exact_mod_cast hn)

/-- Convenient weaker projection of
`eventually_two_mul_pastRealCofactorGramBadProbabilitySum_le_half_polynomial`.
It has exactly the outer-factor interface used by the final small-ball
assembly, without spending any of the `A + 5` exponent slack. -/
theorem eventually_two_mul_pastRealCofactorGramBadProbabilitySum_le_polynomial
    (kseq : ℕ → ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hcross : ∀ᶠ n : ℕ in atTop,
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (kseq n : ℝ)) :
    ∀ᶠ n in atTop,
      (2 : ENNReal) *
          pastRealCofactorGramBadProbabilitySum n (kseq n)
            (L * Real.log (n : ℝ) / (n : ℝ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-A)) := by
  have hhalf :=
    eventually_two_mul_pastRealCofactorGramBadProbabilitySum_le_half_polynomial
      kseq hA hL hcross
  filter_upwards [hhalf] with n hn
  calc
    (2 : ENNReal) *
        pastRealCofactorGramBadProbabilitySum n (kseq n)
          (L * Real.log (n : ℝ) / (n : ℝ)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * (n : ℝ) ^ (-A)) := hn
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-A)) := by
      apply ENNReal.ofReal_le_ofReal
      have hp : 0 ≤ (n : ℝ) ^ (-A) := by positivity
      nlinarith

/-- The paper-scale cross condition eventually makes the ambient real
dimension at least the largest literal cofactor width `2n - 1`. -/
theorem eventually_two_mul_sub_one_le_of_real_cross_growth
    (kseq : ℕ → ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hcross : ∀ᶠ n : ℕ in atTop,
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (kseq n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, 2 * n - 1 ≤ kseq n := by
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
  have hwidth0 : 0 ≤ 2 * x - 1 := by linarith
  have hwidth : 2 * x - 1 ≤ 2 * x := by linarith
  have hsmall :
      (2 * x - 1) * (L ^ 2 * Real.log x) ≤
        32 * (A + 5) * x ^ 4 := by
    calc
      (2 * x - 1) * (L ^ 2 * Real.log x) ≤
          (2 * x) * (x * x) := by gcongr
      _ = 2 * x ^ 3 := by ring
      _ ≤ 160 * x ^ 4 := by
        have hx3 : 0 ≤ x ^ 3 := by positivity
        have hcoef : 2 ≤ 160 * x := by nlinarith
        calc
          2 * x ^ 3 ≤ (160 * x) * x ^ 3 :=
            mul_le_mul_of_nonneg_right hcoef hx3
          _ = 160 * x ^ 4 := by ring
      _ ≤ 32 * (A + 5) * x ^ 4 := by
        have hcoef : (160 : ℝ) ≤ 32 * (A + 5) := by nlinarith
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hden : 0 < L ^ 2 * Real.log x := by positivity
  have hlower : 2 * x - 1 ≤ (kseq n : ℝ) := by
    apply le_trans (b :=
      (32 * (A + 5) * x ^ 4) / (L ^ 2 * Real.log x))
    · exact (le_div_iff₀ hden).2 hsmall
    · apply (div_le_iff₀ hden).2
      calc
        32 * (A + 5) * x ^ 4 ≤
            L ^ 2 * Real.log x * (kseq n : ℝ) := by simpa [x] using hc
        _ = (kseq n : ℝ) * (L ^ 2 * Real.log x) := by ring
  have hlower' : 2 * x ≤ (kseq n : ℝ) + 1 := by linarith
  have hnat : 2 * n ≤ kseq n + 1 := by
    dsimp [x] at hlower'
    exact_mod_cast hlower'
  omega

/-- The logarithmic threshold is eventually a genuine number in `[0,1)`.
This lemma is independent of the dimension sequence. -/
theorem eventually_real_logarithmic_threshold_mem_Ico
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop,
      L * Real.log (n : ℝ) / (n : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
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
  have hlt : ∀ᶠ n : ℕ in atTop,
      L * Real.log (n : ℝ) / (n : ℝ) < 1 :=
    hdeltaT.eventually_lt_const (by norm_num)
  filter_upwards [eventually_ge_atTop 2, hlt] with n hn hnlt
  constructor
  · have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    exact (div_pos (mul_pos hL hlog) hnpos).le
  · exact hnlt

/-- All elementary size and threshold side conditions needed by the literal
real recursion hold eventually under the same cross condition as the final
polynomial estimate. -/
theorem eventually_real_literal_anticoncentration_parameters
    (kseq : ℕ → ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hcross : ∀ᶠ n : ℕ in atTop,
      32 * (A + 5) * (n : ℝ) ^ 4 ≤
        L ^ 2 * Real.log (n : ℝ) * (kseq n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      2 * n - 1 ≤ kseq n ∧
      2 ≤ kseq n ∧
      0 ≤ L * Real.log (n : ℝ) / (n : ℝ) ∧
      L * Real.log (n : ℝ) / (n : ℝ) < 1 := by
  have hwidth := eventually_two_mul_sub_one_le_of_real_cross_growth
    kseq hA hL hcross
  have hdelta := eventually_real_logarithmic_threshold_mem_Ico hL
  filter_upwards [eventually_ge_atTop 2, hwidth, hdelta] with n hn hnwidth hnδ
  have htwo : 2 ≤ 2 * n - 1 := by omega
  exact ⟨hnwidth, htwo.trans hnwidth, hnδ.1, hnδ.2⟩

end

end LogdetLean.GramHafnian
