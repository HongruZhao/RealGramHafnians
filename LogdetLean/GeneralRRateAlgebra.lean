import Mathlib.Tactic
import LogdetLean.CorrelationSpectralAlgebra
import LogdetLean.Paper2608Computations
/-!
# Deterministic rate algebra for the general-correlation bound

This module proves the dimension-free algebra used when the full
general-correlation Berry--Esseen bound is simplified.  It is shared by the
qualitative old-paper CLT and the quantitative new paper.

The main theorem is equation `Q-simple-proof` of the sharp manuscript.  Its
inputs are precisely the two lower bounds on the variance proxy; no
probabilistic or spectral assertion is hidden in the statement.
-/

namespace LogdetLean

noncomputable section

open Filter

/-- The squared-remainder rate before substituting matrix-specific values. -/
def generalRemainderRateQ (m p a sSq : ℝ) : ℝ :=
  4 * (p + a) / (m ^ 2 * sSq)

/-- The cubic spectral contribution before matrix-specific substitution. -/
def generalRCubicRateRho (m c s : ℝ) : ℝ :=
  c / (m ^ 2 * s ^ 3)

/-- The null component of `Q` is controlled by the lower bound
`s^2 >= p(p-1)/m^2`. -/
theorem generalRemainderRateQ_null_part_le
    {m p sSq : ℝ} (hm : 0 < m) (hp : 1 < p) (hs : 0 < sSq)
    (hnull : p * (p - 1) / m ^ 2 ≤ sSq) :
    4 * p / (m ^ 2 * sSq) ≤ 4 / (p - 1) := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hden : 0 < m ^ 2 * sSq := mul_pos hm2 hs
  have hcross : p * (p - 1) ≤ m ^ 2 * sSq :=
    by simpa [mul_comm] using (div_le_iff₀ hm2).mp hnull
  apply (div_le_div_iff₀ hden hp1).2
  nlinarith

/-- The correlation component of `Q` is controlled by the lower bound
`s^2 >= 2a/m`. -/
theorem generalRemainderRateQ_correlation_part_le
    {m a sSq : ℝ} (hm : 0 < m) (hs : 0 < sSq)
    (hcorr : 2 * a / m ≤ sSq) :
    4 * a / (m ^ 2 * sSq) ≤ 2 / m := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hden : 0 < m ^ 2 * sSq := mul_pos hm2 hs
  have hcross : 2 * a ≤ sSq * m := (div_le_iff₀ hm).mp hcorr
  apply (div_le_div_iff₀ hden hm).2
  nlinarith

/-- Exact simplification used in the final general-correlation theorem:

`Q <= 4/(p-1) + 2/m`.
-/
theorem generalRemainderRateQ_le_simple
    {m p a sSq : ℝ} (hm : 0 < m) (hp : 1 < p) (hs : 0 < sSq)
    (hnull : p * (p - 1) / m ^ 2 ≤ sSq)
    (hcorr : 2 * a / m ≤ sSq) :
    generalRemainderRateQ m p a sSq ≤ 4 / (p - 1) + 2 / m := by
  unfold generalRemainderRateQ
  rw [mul_add, add_div]
  exact add_le_add
    (generalRemainderRateQ_null_part_le hm hp hs hnull)
    (generalRemainderRateQ_correlation_part_le hm hs hcorr)

/-- Abstract form of the universal cubic-rate estimate.  The hypothesis
`c <= a sqrt(a)` is the finite-dimensional Schatten inequality, while
`2a/m <= s^2` is the correlation part of the variance proxy. -/
theorem generalRCubicRateRho_le_simple
    {m a c s : ℝ} (hm : 0 < m) (ha : 0 ≤ a)
    (hs : 0 < s) (hcubic : c ≤ a * Real.sqrt a)
    (hscale : 2 * a / m ≤ s ^ 2) :
    generalRCubicRateRho m c s ≤
      1 / (2 * Real.sqrt 2 * Real.sqrt m) := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsqrta : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hsquareScale : 2 * a ≤ m * s ^ 2 := by
    have := (div_le_iff₀ hm).mp hscale
    nlinarith
  have hrootSq : (Real.sqrt 2 * Real.sqrt a) ^ 2 ≤
      (Real.sqrt m * s) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt ha, Real.sq_sqrt hm.le]
    nlinarith
  have hroot : Real.sqrt 2 * Real.sqrt a ≤ Real.sqrt m * s := by
    exact (sq_le_sq₀ (mul_nonneg hsqrt2.le hsqrta)
      (mul_nonneg hsqrtm.le hs.le)).mp hrootSq
  have hcube := pow_le_pow_left₀
    (mul_nonneg hsqrt2.le hsqrta) hroot 3
  have hcube' :
      2 * Real.sqrt 2 * (a * Real.sqrt a) ≤
        m * Real.sqrt m * s ^ 3 := by
    rw [mul_pow, mul_pow, show (Real.sqrt 2) ^ 3 =
        2 * Real.sqrt 2 by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring,
      show (Real.sqrt a) ^ 3 = a * Real.sqrt a by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add,
          Real.sq_sqrt ha]
        ring,
      show (Real.sqrt m) ^ 3 = m * Real.sqrt m by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add,
          Real.sq_sqrt hm.le]
        ring] at hcube
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcube
  have hcrossCubic :
      c * (2 * Real.sqrt 2 * Real.sqrt m) ≤ m ^ 2 * s ^ 3 := by
    calc
      c * (2 * Real.sqrt 2 * Real.sqrt m) ≤
          (a * Real.sqrt a) * (2 * Real.sqrt 2 * Real.sqrt m) := by
        exact mul_le_mul_of_nonneg_right hcubic
          (by positivity)
      _ = Real.sqrt m *
          (2 * Real.sqrt 2 * (a * Real.sqrt a)) := by ring
      _ ≤ Real.sqrt m * (m * Real.sqrt m * s ^ 3) := by
        exact mul_le_mul_of_nonneg_left hcube' hsqrtm.le
      _ = m ^ 2 * s ^ 3 := by
        rw [show Real.sqrt m * (m * Real.sqrt m * s ^ 3) =
          m * (Real.sqrt m) ^ 2 * s ^ 3 by ring,
          Real.sq_sqrt hm.le]
        ring
  unfold generalRCubicRateRho
  have hdenLeft : 0 < m ^ 2 * s ^ 3 := mul_pos (sq_pos_of_pos hm) (pow_pos hs 3)
  have hdenRight : 0 < 2 * Real.sqrt 2 * Real.sqrt m := by positivity
  exact (div_le_div_iff₀ hdenLeft hdenRight).2 (by simpa using hcrossCubic)

/-- Spectral-family specialization: the abstract cubic hypothesis is supplied
by the already-proved finite Schatten inequality. -/
theorem generalRCubicRateRho_eigenvalues_le_simple
    {ι : Type*} {index : Finset ι} {m s : ℝ} (lambda : ι → ℝ)
    (hm : 0 < m) (hs : 0 < s)
    (hscale : 2 * (∑ i ∈ index, lambda i ^ 2) / m ≤ s ^ 2) :
    generalRCubicRateRho m (∑ i ∈ index, |lambda i| ^ 3) s ≤
      1 / (2 * Real.sqrt 2 * Real.sqrt m) := by
  have ha : 0 ≤ ∑ i ∈ index, lambda i ^ 2 := by positivity
  apply generalRCubicRateRho_le_simple hm ha hs
  · simpa [mul_comm] using
      (sum_abs_cube_le_sqrt_sum_sq_mul_sum_sq
        (s := index) (x := lambda))
  · exact hscale

/-- In the natural-number regime `2 <= p <= m`, the simple upper bound tends
to zero whenever `p` tends to infinity.  This finite comparison is the
bookkeeping input for the eventual qualitative CLT. -/
theorem four_div_pred_add_two_div_dimension_le
    {m p : ℕ} (hp : 2 ≤ p) (hpm : p ≤ m) :
    4 / ((p : ℝ) - 1) + 2 / (m : ℝ) ≤ 6 / ((p : ℝ) - 1) := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hmNat : 0 < m := lt_of_lt_of_le (show 0 < p by omega) hpm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hpred : 0 < (p : ℝ) - 1 := sub_pos.mpr hpR
  have hpmR : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpm
  have htwo : 2 / (m : ℝ) ≤ 2 / ((p : ℝ) - 1) := by
    apply (div_le_div_iff₀ hmR hpred).2
    nlinarith
  calc
    4 / ((p : ℝ) - 1) + 2 / (m : ℝ) ≤
        4 / ((p : ℝ) - 1) + 2 / ((p : ℝ) - 1) :=
      add_le_add_right htwo _
    _ = 6 / ((p : ℝ) - 1) := by ring

/-- The universal dimension-only upper envelope tends to zero.  This theorem
is kept separate from any matrix sequence so the old qualitative CLT and the
new quantitative theorem can use the same final limit calculation. -/
theorem tendsto_six_div_nat_pred_zero :
    Tendsto (fun p : ℕ ↦ (6 : ℝ) / ((p : ℝ) - 1)) atTop (nhds 0) := by
  have hden : Tendsto (fun p : ℕ ↦ (p : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ)
        tendsto_natCast_atTop_atTop)
  exact tendsto_const_nhds.div_atTop hden

/-- Consequently the simple remainder envelope
`4/(p-1)+2/m(p)` vanishes along every eventually admissible dimension array.
This is pure deterministic bookkeeping; it does not assert the probabilistic
remainder estimate itself. -/
theorem tendsto_generalRemainder_simple_envelope_zero
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, 2 ≤ p ∧ p ≤ m p) :
    Tendsto
      (fun p : ℕ ↦ 4 / ((p : ℝ) - 1) + 2 / (m p : ℝ))
      atTop (nhds 0) := by
  have hnonneg : ∀ᶠ (p : ℕ) in atTop,
      0 ≤ 4 / ((p : ℝ) - 1) + 2 / (m p : ℝ) := by
    filter_upwards [hadm] with p hp
    have hpden : 0 ≤ (p : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ p by omega))
    exact add_nonneg (div_nonneg (by norm_num) hpden)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hupper : ∀ᶠ (p : ℕ) in atTop,
      4 / ((p : ℝ) - 1) + 2 / (m p : ℝ) ≤
        6 / ((p : ℝ) - 1) := by
    filter_upwards [hadm] with p hp
    exact four_div_pred_add_two_div_dimension_le hp.1 hp.2
  exact squeeze_zero' hnonneg hupper tendsto_six_div_nat_pred_zero

/-- The dimension sequence `m(p)` itself tends to infinity whenever it is
eventually at least `p`. -/
theorem tendsto_dimension_array_atTop
    (m : ℕ → ℕ) (hle : ∀ᶠ p in atTop, p ≤ m p) :
    Tendsto m atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b, hle] with p hbp hpm
  exact hbp.trans hpm

/-- The universal cubic spectral envelope is `o(1)` along every admissible
dimension array.  This is the limit calculation used after the future
matrix-transform theorem supplies the finite `rho_R` estimate. -/
theorem tendsto_generalRCubic_simple_envelope_zero
    (m : ℕ → ℕ) (hle : ∀ᶠ p in atTop, p ≤ m p) :
    Tendsto
      (fun p : ℕ ↦
        1 / (2 * Real.sqrt 2 * Real.sqrt (m p : ℝ)))
      atTop (nhds 0) := by
  have hmNat : Tendsto m atTop atTop := tendsto_dimension_array_atTop m hle
  have hmReal : Tendsto (fun p : ℕ ↦ (m p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmNat
  have hsqrt : Tendsto (fun p : ℕ ↦ Real.sqrt (m p : ℝ))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hmReal
  have hden : Tendsto
      (fun p : ℕ ↦ 2 * Real.sqrt 2 * Real.sqrt (m p : ℝ))
      atTop atTop := by
    exact hsqrt.const_mul_atTop (by positivity : 0 < 2 * Real.sqrt 2)
  exact tendsto_const_nhds.div_atTop hden

end

end LogdetLean
