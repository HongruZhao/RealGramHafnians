import LogdetLean.PolygammaSeries
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Tactic
/-!
# The coefficient series in Kibble's log-radius covariance formula

For `a > 0`, the Kibble bivariate-gamma calculation gives the formal
coefficient series

`sum_{k >= 1} (k-1)! / (k (a)_k) * rho^(2k)`.

We index by `n = k-1`, so Lean's ordinary sum over `Nat` represents the
paper's sum over positive integers without an exceptional zeroth term.  This
file proves, for the range `a >= 1` needed by sample correlation matrices,
absolute convergence all the way to `rho = ±1`, positivity, evenness, the
exact first coefficient, and a sharp reduction of the nonlinear tail to its
endpoint value.  The separate probabilistic Frullani/Laplace bridge identifies
this deterministic series with the covariance of two Gaussian log radii.
-/

namespace LogdetLean

noncomputable section

/-- `(a)_k`, the rising Pochhammer symbol, evaluated in `Real`. -/
def risingPochhammerReal (a : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval a

/-- The coefficient with paper index `k=n+1`:
`n! / ((n+1) (a)_(n+1))`. -/
def kibbleCoeff (a : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) /
    (((n + 1 : ℕ) : ℝ) * risingPochhammerReal a (n + 1))

/-- The Kibble covariance series.  Its `n`-th Lean term is the paper's
`k=n+1` term. -/
def kibbleCovarianceSeries (a rho : ℝ) : ℝ :=
  ∑' n : ℕ, kibbleCoeff a n * rho ^ (2 * (n + 1))

/-- The series tail after removing the `k=1` term. -/
def kibbleCovarianceTail (a rho : ℝ) : ℝ :=
  ∑' n : ℕ, kibbleCoeff a (n + 1) * rho ^ (2 * (n + 2))

/-- A telescoping potential for the nonlinear coefficient tail. -/
def kibbleTailPotential (a : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) /
    (a * risingPochhammerReal a (n + 1))

@[simp] theorem risingPochhammerReal_zero (a : ℝ) :
    risingPochhammerReal a 0 = 1 := by
  simp [risingPochhammerReal]

theorem risingPochhammerReal_succ (a : ℝ) (n : ℕ) :
    risingPochhammerReal a (n + 1) =
      risingPochhammerReal a n * (a + n) := by
  simp [risingPochhammerReal, ascPochhammer_succ_eval]

theorem risingPochhammerReal_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < risingPochhammerReal a n := by
  exact ascPochhammer_pos n a ha

theorem factorial_cast_le_risingPochhammerReal {a : ℝ} (ha : 1 ≤ a) :
    ∀ n : ℕ, (n.factorial : ℝ) ≤ risingPochhammerReal a n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [risingPochhammerReal_succ]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have hn : (0 : ℝ) ≤ n.factorial := by positivity
      have hp : 0 ≤ risingPochhammerReal a n :=
        (risingPochhammerReal_pos (lt_of_lt_of_le zero_lt_one ha) n).le
      have hfac : (n.factorial : ℝ) * (n + 1) ≤
          risingPochhammerReal a n * (n + 1) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      have hstep : risingPochhammerReal a n * (n + 1) ≤
          risingPochhammerReal a n * (a + n) := by
        apply mul_le_mul_of_nonneg_left _ hp
        linarith
      simpa [mul_comm] using hfac.trans hstep

theorem kibbleCoeff_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < kibbleCoeff a n := by
  unfold kibbleCoeff
  have hp := risingPochhammerReal_pos ha (n + 1)
  positivity

theorem kibbleCoeff_nonneg {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 ≤ kibbleCoeff a n := (kibbleCoeff_pos ha n).le

theorem kibbleTailPotential_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < kibbleTailPotential a n := by
  unfold kibbleTailPotential
  have hp := risingPochhammerReal_pos ha (n + 1)
  positivity

@[simp] theorem kibbleTailPotential_zero {a : ℝ} (ha : a ≠ 0) :
    kibbleTailPotential a 0 = 1 / a ^ 2 := by
  simp [kibbleTailPotential, risingPochhammerReal]
  field_simp [ha]

/-- The potential difference has a particularly simple exact form. -/
theorem kibbleTailPotential_sub_succ {a : ℝ} (ha : 0 < a) (n : ℕ) :
    kibbleTailPotential a n - kibbleTailPotential a (n + 1) =
      (n.factorial : ℝ) / risingPochhammerReal a (n + 2) := by
  have hp : risingPochhammerReal a (n + 1) ≠ 0 :=
    (risingPochhammerReal_pos ha (n + 1)).ne'
  have han : a + ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold kibbleTailPotential
  rw [risingPochhammerReal_succ a (n + 1)]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp [ha.ne', hp, han]
  ring

/-- Every nonlinear coefficient is dominated by one telescoping potential
difference. -/
theorem kibbleCoeff_succ_le_potential_sub_succ {a : ℝ}
    (ha : 0 < a) (n : ℕ) :
    kibbleCoeff a (n + 1) ≤
      kibbleTailPotential a n - kibbleTailPotential a (n + 1) := by
  rw [kibbleTailPotential_sub_succ ha]
  have hp : 0 < risingPochhammerReal a (n + 2) :=
    risingPochhammerReal_pos ha (n + 2)
  have hn2 : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
  unfold kibbleCoeff
  change ((n + 1).factorial : ℝ) /
      (((n + 2 : ℕ) : ℝ) * risingPochhammerReal a (n + 2)) ≤
    (n.factorial : ℝ) / risingPochhammerReal a (n + 2)
  rw [div_le_div_iff₀ (mul_pos hn2 hp) hp]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  nlinarith [show (0 : ℝ) < n.factorial by positivity]

@[simp] theorem kibbleCoeff_zero (a : ℝ) :
    kibbleCoeff a 0 = 1 / a := by
  simp [kibbleCoeff, risingPochhammerReal]

/-- For `a >= 1`, the endpoint coefficients are bounded by the shifted
`p=2` series. -/
theorem kibbleCoeff_le_inv_sq {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    kibbleCoeff a n ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hfac0 : 0 < (n.factorial : ℝ) := by positivity
  have hn1 : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hp0 : 0 < risingPochhammerReal a (n + 1) :=
    risingPochhammerReal_pos ha0 (n + 1)
  have hpoch : ((n + 1).factorial : ℝ) ≤
      risingPochhammerReal a (n + 1) :=
    factorial_cast_le_risingPochhammerReal ha (n + 1)
  have hfac : ((n + 1).factorial : ℝ) =
      (n.factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    simp [Nat.factorial_succ, mul_comm]
  rw [hfac] at hpoch
  unfold kibbleCoeff
  rw [div_le_iff₀ (mul_pos hn1 hp0), div_eq_mul_inv]
  field_simp
  nlinarith

/-- The coefficient sequence is summable at the singular endpoints whenever
`a >= 1`. -/
theorem summable_kibbleCoeff {a : ℝ} (ha : 1 ≤ a) :
    Summable (kibbleCoeff a) := by
  have hbase : Summable (fun n : ℕ ↦
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num))
  exact hbase.of_nonneg_of_le
    (fun n ↦ kibbleCoeff_nonneg (lt_of_lt_of_le zero_lt_one ha) n)
    (kibbleCoeff_le_inv_sq ha)

/-- Absolute convergence on the full closed correlation interval. -/
theorem summable_kibbleCovarianceSeries_terms {a rho : ℝ}
    (ha : 1 ≤ a) (hrho : |rho| ≤ 1) :
    Summable (fun n : ℕ ↦ kibbleCoeff a n * rho ^ (2 * (n + 1))) := by
  apply Summable.of_norm_bounded (summable_kibbleCoeff ha)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (kibbleCoeff_nonneg (lt_of_lt_of_le zero_lt_one ha) n)]
  have hp : |rho| ^ (2 * (n + 1)) ≤ 1 := pow_le_one₀ (abs_nonneg rho) hrho
  nlinarith [kibbleCoeff_nonneg (lt_of_lt_of_le zero_lt_one ha) n]

theorem summable_kibbleCovarianceTail_terms {a rho : ℝ}
    (ha : 1 ≤ a) (hrho : |rho| ≤ 1) :
    Summable (fun n : ℕ ↦
      kibbleCoeff a (n + 1) * rho ^ (2 * (n + 2))) := by
  have h := summable_kibbleCovarianceSeries_terms ha hrho
  simpa [Function.comp_def] using
    h.comp_injective (i := Nat.succ) Nat.succ_injective

/-- Splitting the paper's `k=1` term from the convergent series. -/
theorem kibbleCovarianceSeries_eq_first_add_tail {a rho : ℝ}
    (ha : 1 ≤ a) (hrho : |rho| ≤ 1) :
    kibbleCovarianceSeries a rho = rho ^ 2 / a +
      kibbleCovarianceTail a rho := by
  let f : ℕ → ℝ := fun n ↦
    kibbleCoeff a n * rho ^ (2 * (n + 1))
  have hsum : Summable f := summable_kibbleCovarianceSeries_terms ha hrho
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ha)
  have hfinite : ∑ n ∈ Finset.range 1, f n = rho ^ 2 / a := by
    simp [f, kibbleCoeff_zero, div_eq_mul_inv, mul_comm]
  have htail : (∑' n : ℕ, f (n + 1)) = kibbleCovarianceTail a rho := by
    apply tsum_congr
    intro n
    simp only [f]
  rw [hfinite, htail] at hsplit
  exact hsplit.symm

theorem kibbleCovarianceTail_nonneg {a rho : ℝ}
    (ha : 0 < a) : 0 ≤ kibbleCovarianceTail a rho := by
  unfold kibbleCovarianceTail
  exact tsum_nonneg fun n ↦ mul_nonneg (kibbleCoeff_nonneg ha (n + 1)) (by
    rw [pow_mul]
    positivity)

/-- The nonlinear part at `rho` is at most `rho^4` times the nonlinear
part at the endpoint.  This is valid on the closed interval, not merely for
`|rho|<1`. -/
theorem kibbleCovarianceTail_le_pow_four_mul_endpoint {a rho : ℝ}
    (ha : 1 ≤ a) (hrho : |rho| ≤ 1) :
    kibbleCovarianceTail a rho ≤ rho ^ 4 * kibbleCovarianceTail a 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hsumrho := summable_kibbleCovarianceTail_terms ha hrho
  have hsumone := summable_kibbleCovarianceTail_terms ha (by simp : |(1 : ℝ)| ≤ 1)
  unfold kibbleCovarianceTail
  calc
    ∑' n : ℕ, kibbleCoeff a (n + 1) * rho ^ (2 * (n + 2)) ≤
        ∑' n : ℕ, rho ^ 4 * (kibbleCoeff a (n + 1) * 1 ^ (2 * (n + 2))) := by
      apply hsumrho.tsum_le_tsum
      · intro n
        have hr2 : 0 ≤ rho ^ 2 := sq_nonneg rho
        have hr2le : rho ^ 2 ≤ 1 := by
          simpa [pow_two] using abs_le_one_iff_mul_self_le_one.mp hrho
        have hpow : rho ^ (2 * (n + 2)) ≤ rho ^ 4 := by
          rw [show 2 * (n + 2) = 4 + 2 * n by omega, pow_add,
            show rho ^ (2 * n) = (rho ^ 2) ^ n by rw [pow_mul]]
          exact mul_le_of_le_one_right (by positivity)
            (pow_le_one₀ hr2 hr2le)
        have hc0 := kibbleCoeff_nonneg ha0 (n + 1)
        simpa [mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left hpow hc0
      · simpa using hsumone.mul_left (rho ^ 4)
    _ = rho ^ 4 * ∑' n : ℕ,
        kibbleCoeff a (n + 1) * 1 ^ (2 * (n + 2)) := by
      rw [tsum_mul_left]

/-- The endpoint tail is the endpoint covariance minus its first
coefficient. -/
theorem kibbleCovarianceTail_one_eq {a : ℝ} (ha : 1 ≤ a) :
    kibbleCovarianceTail a 1 = kibbleCovarianceSeries a 1 - 1 / a := by
  have hsplit := kibbleCovarianceSeries_eq_first_add_tail ha
    (by simp : |(1 : ℝ)| ≤ 1)
  norm_num at hsplit ⊢
  linarith

/-- The entire endpoint nonlinear tail is at most `1/a^2`.  This direct
telescoping proof avoids any use of the probabilistic endpoint identity. -/
theorem kibbleCovarianceTail_one_le_inv_sq {a : ℝ} (ha : 1 ≤ a) :
    kibbleCovarianceTail a 1 ≤ 1 / a ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  unfold kibbleCovarianceTail
  simp only [one_pow, mul_one]
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact kibbleCoeff_nonneg ha0 (n + 1)
  · intro N
    calc
      ∑ n ∈ Finset.range N, kibbleCoeff a (n + 1) ≤
          ∑ n ∈ Finset.range N,
            (kibbleTailPotential a n - kibbleTailPotential a (n + 1)) := by
        exact Finset.sum_le_sum fun n _hn ↦
          kibbleCoeff_succ_le_potential_sub_succ ha0 n
      _ = kibbleTailPotential a 0 - kibbleTailPotential a N := by
        exact Finset.sum_range_sub' (kibbleTailPotential a) N
      _ ≤ kibbleTailPotential a 0 := by
        exact sub_le_self _ (kibbleTailPotential_pos ha0 N).le
      _ = 1 / a ^ 2 := kibbleTailPotential_zero ha0.ne'

/-- Closed-interval nonlinear bound proved solely from the coefficients. -/
theorem kibbleCovarianceTail_le_pow_four_div_sq {a rho : ℝ}
    (ha : 1 ≤ a) (hrho : |rho| ≤ 1) :
    kibbleCovarianceTail a rho ≤ rho ^ 4 / a ^ 2 := by
  calc
    kibbleCovarianceTail a rho ≤
        rho ^ 4 * kibbleCovarianceTail a 1 :=
      kibbleCovarianceTail_le_pow_four_mul_endpoint ha hrho
    _ ≤ rho ^ 4 * (1 / a ^ 2) := by
      exact mul_le_mul_of_nonneg_left (kibbleCovarianceTail_one_le_inv_sq ha)
        (by positivity)
    _ = rho ^ 4 / a ^ 2 := by ring

/-- A bridge-free sharp tail comparison.  Once the probabilistic endpoint
identity says `series(a,1)=trigammaSeries(a)`, this immediately gives the
paper's `rho^4/a^2` remainder. -/
theorem kibbleCovarianceSeries_sub_first_le_endpoint {a rho : ℝ}
    (ha : 1 ≤ a) (hrho : |rho| ≤ 1) :
    kibbleCovarianceSeries a rho - rho ^ 2 / a ≤
      rho ^ 4 * (kibbleCovarianceSeries a 1 - 1 / a) := by
  rw [kibbleCovarianceSeries_eq_first_add_tail ha hrho]
  simp only [add_sub_cancel_left]
  rw [← kibbleCovarianceTail_one_eq ha]
  exact kibbleCovarianceTail_le_pow_four_mul_endpoint ha hrho

/-- Conditional on the exact endpoint identity, the complete Kibble
remainder inequality follows with its sharp paper constant.  The endpoint
identity itself belongs to the probability bridge: at `rho=1` the two radii
coincide, so the covariance is the trigamma variance. -/
theorem kibbleCovarianceSeries_remainder_bounds_of_endpoint
    {a rho : ℝ} (ha : 1 ≤ a) (hrho : |rho| ≤ 1)
    (hendpoint : kibbleCovarianceSeries a 1 = trigammaSeries a) :
    0 ≤ kibbleCovarianceSeries a rho - rho ^ 2 / a ∧
      kibbleCovarianceSeries a rho - rho ^ 2 / a ≤ rho ^ 4 / a ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  constructor
  · rw [kibbleCovarianceSeries_eq_first_add_tail ha hrho]
    simpa using kibbleCovarianceTail_nonneg (rho := rho) ha0
  · calc
      kibbleCovarianceSeries a rho - rho ^ 2 / a ≤
          rho ^ 4 * (kibbleCovarianceSeries a 1 - 1 / a) :=
        kibbleCovarianceSeries_sub_first_le_endpoint ha hrho
      _ = rho ^ 4 * (trigammaSeries a - 1 / a) := by rw [hendpoint]
      _ ≤ rho ^ 4 * (1 / a ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [trigammaSeries_le_one_div_add_one_div_sq ha0]
      _ = rho ^ 4 / a ^ 2 := by ring

/-- The complete first-term/remainder bound, now with no probabilistic
hypothesis. -/
theorem kibbleCovarianceSeries_remainder_bounds {a rho : ℝ}
    (ha : 1 ≤ a) (hrho : |rho| ≤ 1) :
    0 ≤ kibbleCovarianceSeries a rho - rho ^ 2 / a ∧
      kibbleCovarianceSeries a rho - rho ^ 2 / a ≤ rho ^ 4 / a ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  rw [kibbleCovarianceSeries_eq_first_add_tail ha hrho]
  simp only [add_sub_cancel_left]
  exact ⟨kibbleCovarianceTail_nonneg (rho := rho) ha0,
    kibbleCovarianceTail_le_pow_four_div_sq ha hrho⟩

/-- The paper's covariance-series notation `c_m(rho)`, with
`a=m/2`. -/
def logRadiusCovarianceSeries (m : ℕ) (rho : ℝ) : ℝ :=
  kibbleCovarianceSeries ((m : ℝ) / 2) rho

/-- Literal Lean rendering of
`c_m(rho)=sum_{k>=1} (k-1)!/[k(m/2)_k] rho^(2k)`, with `n=k-1`. -/
theorem logRadiusCovarianceSeries_eq_paper_sum (m : ℕ) (rho : ℝ) :
    logRadiusCovarianceSeries m rho =
      ∑' n : ℕ,
        (n.factorial : ℝ) /
          (((n + 1 : ℕ) : ℝ) *
            risingPochhammerReal ((m : ℝ) / 2) (n + 1)) *
          rho ^ (2 * (n + 1)) := rfl

theorem half_nat_one_le {m : ℕ} (hm : 2 ≤ m) :
    (1 : ℝ) ≤ (m : ℝ) / 2 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- The exact paper remainder bound in the original `m` normalization.  The
only input not proved by coefficient algebra is the endpoint identity, which
the Gaussian log-radius probability bridge supplies. -/
theorem logRadiusCovarianceSeries_remainder_bounds_of_endpoint
    {m : ℕ} {rho : ℝ} (hm : 2 ≤ m) (hrho : |rho| ≤ 1)
    (hendpoint : logRadiusCovarianceSeries m 1 =
      trigammaSeries ((m : ℝ) / 2)) :
    0 ≤ logRadiusCovarianceSeries m rho - 2 * rho ^ 2 / (m : ℝ) ∧
      logRadiusCovarianceSeries m rho - 2 * rho ^ 2 / (m : ℝ) ≤
        4 * rho ^ 4 / (m : ℝ) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h := kibbleCovarianceSeries_remainder_bounds_of_endpoint
    (half_nat_one_le hm) hrho hendpoint
  unfold logRadiusCovarianceSeries at h ⊢
  have hfirst : rho ^ 2 / ((m : ℝ) / 2) = 2 * rho ^ 2 / (m : ℝ) := by
    field_simp
  have hfourth : rho ^ 4 / ((m : ℝ) / 2) ^ 2 =
      4 * rho ^ 4 / (m : ℝ) ^ 2 := by
    field_simp
    ring
  simpa [hfirst, hfourth] using h

/-- The exact paper remainder bound in the original `m` normalization,
proved without the endpoint covariance bridge. -/
theorem logRadiusCovarianceSeries_remainder_bounds
    {m : ℕ} {rho : ℝ} (hm : 2 ≤ m) (hrho : |rho| ≤ 1) :
    0 ≤ logRadiusCovarianceSeries m rho - 2 * rho ^ 2 / (m : ℝ) ∧
      logRadiusCovarianceSeries m rho - 2 * rho ^ 2 / (m : ℝ) ≤
        4 * rho ^ 4 / (m : ℝ) ^ 2 := by
  have h := kibbleCovarianceSeries_remainder_bounds
    (half_nat_one_le hm) hrho
  unfold logRadiusCovarianceSeries at h ⊢
  have hfirst : rho ^ 2 / ((m : ℝ) / 2) = 2 * rho ^ 2 / (m : ℝ) := by
    field_simp
  have hfourth : rho ^ 4 / ((m : ℝ) / 2) ^ 2 =
      4 * rho ^ 4 / (m : ℝ) ^ 2 := by
    field_simp
    ring
  simpa [hfirst, hfourth] using h

/-- The endpoint series is even; in particular the `+1` and `-1` endpoint
values coincide. -/
theorem kibbleCovarianceSeries_neg (a rho : ℝ) :
    kibbleCovarianceSeries a (-rho) = kibbleCovarianceSeries a rho := by
  unfold kibbleCovarianceSeries
  congr 1
  funext n
  rw [neg_pow]
  simp

@[simp] theorem kibbleCovarianceSeries_neg_one (a : ℝ) :
    kibbleCovarianceSeries a (-1) = kibbleCovarianceSeries a 1 := by
  simpa using kibbleCovarianceSeries_neg a 1

theorem logRadiusCovarianceSeries_neg (m : ℕ) (rho : ℝ) :
    logRadiusCovarianceSeries m (-rho) = logRadiusCovarianceSeries m rho :=
  kibbleCovarianceSeries_neg _ _

@[simp] theorem logRadiusCovarianceSeries_neg_one (m : ℕ) :
    logRadiusCovarianceSeries m (-1) = logRadiusCovarianceSeries m 1 := by
  exact kibbleCovarianceSeries_neg_one _

end

end LogdetLean
