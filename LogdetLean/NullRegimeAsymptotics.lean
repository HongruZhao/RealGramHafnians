import LogdetLean.NullUniformEdgeworthTarget
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
/-!
# Regime asymptotics for the null log-determinant

This file evaluates the exact finite polygamma sums `nullVSeries` and
`nullASeries` in the seven regimes used in the paper.  The development starts
with cancellation-preserving finite comparison formulas.  In particular, the
dilute case is never deduced from a coarse harmonic estimate.

Write `d=m-p`.  The elementary comparison sums are

* `S1 = sum_{k=d+1}^{m-1} (k⁻¹-m⁻¹)`, and
* `S2 = sum_{k=d+1}^{m-1} (k⁻²-m⁻²)`.

The exact series satisfy `V = 2*S1 + error` and `A = 4*S2 + error`, with
fully explicit finite error bounds below.  The fixed-gap limit instead uses
the exact absolutely convergent hard-edge tail `hardEdgeAConstant d`.

The asymptotic evaluations are self-derived from the positive polygamma
series, elementary sum--integral/Taylor comparisons, and standard limit
algebra in mathlib.  See `docs/provenance/null_regime_asymptotics.md`.
-/

namespace LogdetLean

open Filter Real Set
open scoped BigOperators Topology

noncomputable section

/-- Residual gap `d=m-p`. -/
def nullGap (m p : ℕ) : ℕ := m - p

/-- Cancellation-preserving reciprocal-power sum over the beta shapes. -/
def nullGapPowerDifference (r m p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico (m - p + 1) m,
    (1 / (k : ℝ) ^ r - 1 / (m : ℝ) ^ r)

/-- Elementary leading variance sum `2 S1`. -/
def nullVLeading (m p : ℕ) : ℝ := 2 * nullGapPowerDifference 1 m p

/-- Elementary leading third-cumulant sum `4 S2`. -/
def nullALeading (m p : ℕ) : ℝ := 4 * nullGapPowerDifference 2 m p

/-- Exact hard-edge tail.  Gap `d=0` is the square constant. -/
def hardEdgeAConstant (d : ℕ) : ℝ :=
  ∑' n : ℕ, negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2)

/-- The real zeta value at three, represented by its defining positive
series.  The `n=0` term is zero in Lean's totalized division. -/
def realZetaThree : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ 3

/-- Closed expression for the square hard-edge third-cumulant constant. -/
def squareAConstant : ℝ := 4 * Real.pi ^ 2 / 3 + 7 * realZetaThree

private theorem cast_shape_index {m j : ℕ} (hjm : j ≤ m) :
    (((m - j + 1 : ℕ) : ℝ) / 2) = betaShapeA m j := by
  unfold betaShapeA
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hjm]

/-- Reindex the exact variance by the residual degrees of freedom. -/
theorem nullVSeries_eq_gap_sum {m p : ℕ} (h : Admissible m p) :
    nullVSeries m p =
      ∑ k ∈ Finset.Ico (m - p + 1) m,
        (trigammaSeries ((k : ℝ) / 2) -
          trigammaSeries ((m : ℝ) / 2)) := by
  unfold nullVSeries betaShapeTotal
  have hpm : p ≤ m := h.2
  apply Finset.sum_bij (fun j _hj ↦ m - j + 1)
  · intro j hj
    have hjb := Finset.mem_Icc.mp hj
    exact Finset.mem_Ico.mpr (by omega)
  · intro j₁ hj₁ j₂ hj₂ heq
    have h₁ := (Finset.mem_Icc.mp hj₁).2
    have h₂ := (Finset.mem_Icc.mp hj₂).2
    omega
  · intro k hk
    have hkb := Finset.mem_Ico.mp hk
    refine ⟨m - k + 1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr (by omega)
    · omega
  · intro j hj
    have hjm : j ≤ m := le_trans (Finset.mem_Icc.mp hj).2 h.2
    rw [← cast_shape_index hjm]

/-- Reindex the exact positive third-cumulant magnitude by the gap. -/
theorem nullASeries_eq_gap_sum {m p : ℕ} (h : Admissible m p) :
    nullASeries m p =
      ∑ k ∈ Finset.Ico (m - p + 1) m,
        (negPsiTwoSeries ((k : ℝ) / 2) -
          negPsiTwoSeries ((m : ℝ) / 2)) := by
  unfold nullASeries betaShapeTotal
  have hpm : p ≤ m := h.2
  apply Finset.sum_bij (fun j _hj ↦ m - j + 1)
  · intro j hj
    have hjb := Finset.mem_Icc.mp hj
    exact Finset.mem_Ico.mpr (by omega)
  · intro j₁ hj₁ j₂ hj₂ heq
    have h₁ := (Finset.mem_Icc.mp hj₁).2
    have h₂ := (Finset.mem_Icc.mp hj₂).2
    omega
  · intro k hk
    have hkb := Finset.mem_Ico.mp hk
    refine ⟨m - k + 1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr (by omega)
    · omega
  · intro j hj
    have hjm : j ≤ m := le_trans (Finset.mem_Icc.mp hj).2 h.2
    rw [← cast_shape_index hjm]

private theorem trigamma_half_residual_bounds {k : ℕ} (hk : 0 < k) :
    0 ≤ trigammaSeries ((k : ℝ) / 2) - 2 / (k : ℝ) ∧
      trigammaSeries ((k : ℝ) / 2) - 2 / (k : ℝ) ≤
        4 / (k : ℝ) ^ 2 := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hx : 0 < (k : ℝ) / 2 := by positivity
  have hb := trigammaSeries_bounds hx
  have hlin : 1 / ((k : ℝ) / 2) = 2 / (k : ℝ) := by
    field_simp [hkR.ne']
  have hsq : 1 / ((k : ℝ) / 2) ^ 2 = 4 / (k : ℝ) ^ 2 := by
    field_simp [hkR.ne'] <;> norm_num
  constructor
  · rw [← hlin]
    exact sub_nonneg.mpr hb.1
  · rw [← hlin, ← hsq]
    linarith [hb.2]

private theorem negPsiTwo_half_residual_bounds {k : ℕ} (hk : 0 < k) :
    0 ≤ negPsiTwoSeries ((k : ℝ) / 2) - 4 / (k : ℝ) ^ 2 ∧
      negPsiTwoSeries ((k : ℝ) / 2) - 4 / (k : ℝ) ^ 2 ≤
        16 / (k : ℝ) ^ 3 := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hx : 0 < (k : ℝ) / 2 := by positivity
  have hb := negPsiTwoSeries_bounds hx
  have hsq : 1 / ((k : ℝ) / 2) ^ 2 = 4 / (k : ℝ) ^ 2 := by
    field_simp [hkR.ne'] <;> norm_num
  have hcub : 2 / ((k : ℝ) / 2) ^ 3 = 16 / (k : ℝ) ^ 3 := by
    field_simp [hkR.ne'] <;> norm_num
  constructor
  · rw [← hsq]
    exact sub_nonneg.mpr hb.1
  · rw [← hsq, ← hcub]
    linarith [hb.2]

private theorem abs_sub_le_of_interval {x y a b : ℝ}
    (hx0 : 0 ≤ x) (hxa : x ≤ a) (hy0 : 0 ≤ y) (hyb : y ≤ b) :
    |x - y| ≤ a + b := by
  rw [abs_le]
  constructor <;> linarith

/-- Finite cancellation-preserving variance comparison. -/
theorem abs_nullVSeries_sub_nullVLeading_le {m p : ℕ}
    (h : Admissible m p) :
    |nullVSeries m p - nullVLeading m p| ≤
      ∑ k ∈ Finset.Ico (m - p + 1) m,
        (4 / (k : ℝ) ^ 2 + 4 / (m : ℝ) ^ 2) := by
  rw [nullVSeries_eq_gap_sum h]
  unfold nullVLeading nullGapPowerDifference
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hkb := Finset.mem_Ico.mp hk
  have hkpos : 0 < k := by omega
  have hmpos : 0 < m := by omega
  have hkB := trigamma_half_residual_bounds hkpos
  have hmB := trigamma_half_residual_bounds hmpos
  have hid :
      (trigammaSeries ((k : ℝ) / 2) - trigammaSeries ((m : ℝ) / 2)) -
          2 * (1 / (k : ℝ) ^ 1 - 1 / (m : ℝ) ^ 1) =
        (trigammaSeries ((k : ℝ) / 2) - 2 / (k : ℝ)) -
          (trigammaSeries ((m : ℝ) / 2) - 2 / (m : ℝ)) := by
    simp only [pow_one]
    ring
  rw [hid]
  exact abs_sub_le_of_interval hkB.1 hkB.2 hmB.1 hmB.2

/-- Finite cancellation-preserving third-cumulant comparison. -/
theorem abs_nullASeries_sub_nullALeading_le {m p : ℕ}
    (h : Admissible m p) :
    |nullASeries m p - nullALeading m p| ≤
      ∑ k ∈ Finset.Ico (m - p + 1) m,
        (16 / (k : ℝ) ^ 3 + 16 / (m : ℝ) ^ 3) := by
  rw [nullASeries_eq_gap_sum h]
  unfold nullALeading nullGapPowerDifference
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hkb := Finset.mem_Ico.mp hk
  have hkpos : 0 < k := by omega
  have hmpos : 0 < m := by omega
  have hkB := negPsiTwo_half_residual_bounds hkpos
  have hmB := negPsiTwo_half_residual_bounds hmpos
  have hid :
      (negPsiTwoSeries ((k : ℝ) / 2) - negPsiTwoSeries ((m : ℝ) / 2)) -
          4 * (1 / (k : ℝ) ^ 2 - 1 / (m : ℝ) ^ 2) =
        (negPsiTwoSeries ((k : ℝ) / 2) - 4 / (k : ℝ) ^ 2) -
          (negPsiTwoSeries ((m : ℝ) / 2) - 4 / (m : ℝ) ^ 2) := by ring
  rw [hid]
  exact abs_sub_le_of_interval hkB.1 hkB.2 hmB.1 hmB.2

/-- Endpoint form of the variance comparison.  Unlike the coarser
`1/(m-p)` tail bound below, this retains the factor `p-1` and is therefore
strong enough when `p/m -> 0`. -/
theorem abs_nullVSeries_sub_nullVLeading_endpoint_le {m p : ℕ}
    (h : Admissible m p) :
    |nullVSeries m p - nullVLeading m p| ≤
      4 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 2) +
        4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hbase := abs_nullVSeries_sub_nullVLeading_le h
  have hsum :
      (∑ k ∈ Finset.Ico (m - p + 1) m,
        (4 / (k : ℝ) ^ 2 + 4 / (m : ℝ) ^ 2)) ≤
      ∑ _k ∈ Finset.Ico (m - p + 1) m,
        (4 / (((m - p + 1 : ℕ) : ℝ) ^ 2) + 4 / (m : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro k hk
    have hmk : m - p + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hpos : 0 < (((m - p + 1 : ℕ) : ℝ)) := by positivity
    have hkposNat : 0 < k := by omega
    have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr hkposNat
    have hcast : (((m - p + 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hinv : 4 / (k : ℝ) ^ 2 ≤
        4 / (((m - p + 1 : ℕ) : ℝ) ^ 2) := by gcongr
    linarith
  have hcard : m - (m - p + 1) = p - 1 := by omega
  calc
    |nullVSeries m p - nullVLeading m p| ≤
        (∑ k ∈ Finset.Ico (m - p + 1) m,
          (4 / (k : ℝ) ^ 2 + 4 / (m : ℝ) ^ 2)) := hbase
    _ ≤ ∑ _k ∈ Finset.Ico (m - p + 1) m,
          (4 / (((m - p + 1 : ℕ) : ℝ) ^ 2) + 4 / (m : ℝ) ^ 2) := hsum
    _ = 4 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 2) +
          4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
      rw [Finset.sum_const, Nat.card_Ico, hcard]
      simp only [nsmul_eq_mul]
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      ring

/-- Endpoint form of the third-cumulant comparison.  It retains the factor
`p-1`, which makes the error `o(p^2/m^3)` throughout the dilute regime. -/
theorem abs_nullASeries_sub_nullALeading_endpoint_le {m p : ℕ}
    (h : Admissible m p) :
    |nullASeries m p - nullALeading m p| ≤
      16 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 3) +
        16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hbase := abs_nullASeries_sub_nullALeading_le h
  have hsum :
      (∑ k ∈ Finset.Ico (m - p + 1) m,
        (16 / (k : ℝ) ^ 3 + 16 / (m : ℝ) ^ 3)) ≤
      ∑ _k ∈ Finset.Ico (m - p + 1) m,
        (16 / (((m - p + 1 : ℕ) : ℝ) ^ 3) + 16 / (m : ℝ) ^ 3) := by
    apply Finset.sum_le_sum
    intro k hk
    have hmk : m - p + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hpos : 0 < (((m - p + 1 : ℕ) : ℝ)) := by positivity
    have hkposNat : 0 < k := by omega
    have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr hkposNat
    have hcast : (((m - p + 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hinv : 16 / (k : ℝ) ^ 3 ≤
        16 / (((m - p + 1 : ℕ) : ℝ) ^ 3) := by gcongr
    linarith
  have hcard : m - (m - p + 1) = p - 1 := by omega
  calc
    |nullASeries m p - nullALeading m p| ≤
        (∑ k ∈ Finset.Ico (m - p + 1) m,
          (16 / (k : ℝ) ^ 3 + 16 / (m : ℝ) ^ 3)) := hbase
    _ ≤ ∑ _k ∈ Finset.Ico (m - p + 1) m,
          (16 / (((m - p + 1 : ℕ) : ℝ) ^ 3) + 16 / (m : ℝ) ^ 3) := hsum
    _ = 16 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 3) +
          16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 := by
      rw [Finset.sum_const, Nat.card_Ico, hcard]
      simp only [nsmul_eq_mul]
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      ring

/-- Absolute summability certificate for the defining hard-edge tail. -/
theorem summable_hardEdgeA_terms (d : ℕ) :
    Summable (fun n : ℕ ↦
      negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2)) := by
  have hs2 : Summable (fun n : ℕ ↦ 20 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    exact ((summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))).mul_left 20
  apply hs2.of_nonneg_of_le
  · intro n
    exact negPsiTwoSeries_nonneg (by positivity)
  · intro n
    have hdn : (n + 1 : ℕ) ≤ d + n + 1 := by omega
    have hnR : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    have hdR : (((n + 1 : ℕ) : ℝ)) ≤ (((d + n + 1 : ℕ) : ℝ)) := by exact_mod_cast hdn
    have hb := negPsiTwoSeries_le_one_div_sq_add_two_div_cube
      (show 0 < (((d + n + 1 : ℕ) : ℝ)) / 2 by positivity)
    have hsq : 4 / (((d + n + 1 : ℕ) : ℝ)) ^ 2 ≤
        4 / (((n + 1 : ℕ) : ℝ)) ^ 2 := by
      gcongr
    have hcub : 16 / (((d + n + 1 : ℕ) : ℝ)) ^ 3 ≤
        16 / (((n + 1 : ℕ) : ℝ)) ^ 2 := by
      let N : ℝ := (((n + 1 : ℕ) : ℝ))
      let D : ℝ := (((d + n + 1 : ℕ) : ℝ))
      have hN : 0 < N := by dsimp [N]; positivity
      have hD : 0 < D := by dsimp [D]; positivity
      have hND : N ≤ D := by simpa [N, D] using hdR
      have hDone : 1 ≤ D := by
        dsimp [D]
        exact_mod_cast (show 1 ≤ d + n + 1 by omega)
      have hden : N ^ 2 ≤ D ^ 3 := by
        have hsq : N ^ 2 ≤ D ^ 2 := by gcongr
        have hc : D ^ 2 ≤ D ^ 3 := by
          rw [pow_succ]
          exact le_mul_of_one_le_right (sq_nonneg D) hDone
        exact hsq.trans hc
      apply (div_le_div_iff₀ (pow_pos hD 3) (pow_pos hN 2)).2
      nlinarith
    have hb' : negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2) ≤
        4 / (((d + n + 1 : ℕ) : ℝ)) ^ 2 +
          16 / (((d + n + 1 : ℕ) : ℝ)) ^ 3 := by
      have hD : 0 < (((d + n + 1 : ℕ) : ℝ)) := by positivity
      have hsq' : 1 / ((((d + n + 1 : ℕ) : ℝ)) / 2) ^ 2 =
          4 / (((d + n + 1 : ℕ) : ℝ)) ^ 2 := by
        field_simp [hD.ne'] <;> norm_num
      have hcub' : 2 / ((((d + n + 1 : ℕ) : ℝ)) / 2) ^ 3 =
          16 / (((d + n + 1 : ℕ) : ℝ)) ^ 3 := by
        field_simp [hD.ne'] <;> norm_num
      rw [hsq', hcub'] at hb
      exact hb
    calc
      negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2) ≤
          4 / (((d + n + 1 : ℕ) : ℝ)) ^ 2 +
            16 / (((d + n + 1 : ℕ) : ℝ)) ^ 3 := hb'
      _ ≤ 4 / (((n + 1 : ℕ) : ℝ)) ^ 2 +
            16 / (((n + 1 : ℕ) : ℝ)) ^ 2 := add_le_add hsq hcub
      _ = 20 * (1 / (((n + 1 : ℕ) : ℝ)) ^ 2) := by ring

/-- The hard-edge constant is positive. -/
theorem hardEdgeAConstant_pos (d : ℕ) : 0 < hardEdgeAConstant d := by
  unfold hardEdgeAConstant
  exact (summable_hardEdgeA_terms d).tsum_pos
    (fun n ↦ (negPsiTwoSeries_nonneg (by positivity))) 0
    (negPsiTwoSeries_pos (by positivity))

/-- Removing the first hard-edge term gives the next gap constant. -/
theorem hardEdgeAConstant_eq_term_add_succ (d : ℕ) :
    hardEdgeAConstant d =
      negPsiTwoSeries (((d + 1 : ℕ) : ℝ) / 2) + hardEdgeAConstant (d + 1) := by
  unfold hardEdgeAConstant
  rw [(summable_hardEdgeA_terms d).tsum_eq_zero_add]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  congr 1
  apply tsum_congr
  intro n
  congr 2 <;> ring

/-- The fixed-gap hard-edge constants strictly decrease with the gap. -/
theorem hardEdgeAConstant_strictAnti : StrictAnti hardEdgeAConstant := by
  exact strictAnti_nat_of_succ_lt fun d ↦ by
    conv_rhs => rw [hardEdgeAConstant_eq_term_add_succ]
    have hx : 0 < (((d + 1 : ℕ) : ℝ) / 2) := by positivity
    exact lt_add_of_pos_left _ (negPsiTwoSeries_pos hx)

/-- Antitone form used by the constrained-supremum argument. -/
theorem hardEdgeAConstant_antitone : Antitone hardEdgeAConstant :=
  hardEdgeAConstant_strictAnti.antitone

private theorem tendsto_nat_sub_const_atTop (c : ℕ) :
    Tendsto (fun n : ℕ ↦ n - c) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b + c)] with n hn
  omega

private theorem tendsto_nat_add_sub_one_atTop (d : ℕ) :
    Tendsto (fun n : ℕ ↦ n + d - 1) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b + 1)] with n hn
  omega

/-- Exact fixed-gap formula as a partial hard-edge sum minus the common
shape correction. -/
theorem nullASeries_fixedGap_eq (d p : ℕ) (hp : 2 ≤ p) :
    nullASeries (p + d) p =
      (∑ n ∈ Finset.range (p - 1),
        negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2)) -
      ((p : ℝ) - 1) * negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2) := by
  have hadm : Admissible (p + d) p := ⟨hp, by omega⟩
  rw [nullASeries_eq_gap_sum hadm, Finset.sum_sub_distrib]
  have hgap : p + d - p + 1 = d + 1 := by omega
  rw [hgap, Finset.sum_Ico_eq_sum_range]
  have hlen : p + d - (d + 1) = p - 1 := by omega
  rw [hlen]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    congr 2
    exact_mod_cast (show d + 1 + n = d + n + 1 by omega)
  · rw [Finset.sum_const, Nat.card_Ico]
    simp only [nsmul_eq_mul]
    rw [hlen, Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num

private theorem fixedGap_common_correction_nonneg (d p : ℕ) (hp : 1 ≤ p) :
    0 ≤ ((p : ℝ) - 1) *
      negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact mul_nonneg (sub_nonneg.mpr hp1)
    (negPsiTwoSeries_nonneg (by positivity))

private theorem fixedGap_common_correction_le (d p : ℕ) (hp : 2 ≤ p) :
    ((p : ℝ) - 1) * negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2) ≤
      20 / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by positivity
  have hpdR : (p : ℝ) ≤ ((p + d : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right p d
  have hb := negPsiTwoSeries_le_one_div_sq_add_two_div_cube
    (show 0 < (((p + d : ℕ) : ℝ)) / 2 by positivity)
  have hpd1 : 1 ≤ ((p + d : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ p + d by omega)
  have hb' : negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2) ≤
      20 / (((p + d : ℕ) : ℝ)) ^ 2 := by
    have hsq : 1 / ((((p + d : ℕ) : ℝ)) / 2) ^ 2 =
        4 / (((p + d : ℕ) : ℝ)) ^ 2 := by
      have hpos : 0 < ((p + d : ℕ) : ℝ) := by positivity
      field_simp [hpos.ne'] <;> norm_num
    have hcub : 2 / ((((p + d : ℕ) : ℝ)) / 2) ^ 3 =
        16 / (((p + d : ℕ) : ℝ)) ^ 3 := by
      have hpos : 0 < ((p + d : ℕ) : ℝ) := by positivity
      field_simp [hpos.ne'] <;> norm_num
    rw [hsq, hcub] at hb
    have hcube : 16 / (((p + d : ℕ) : ℝ)) ^ 3 ≤
        16 / (((p + d : ℕ) : ℝ)) ^ 2 := by
      have hpos : 0 < ((p + d : ℕ) : ℝ) := by positivity
      apply (div_le_div_iff₀ (pow_pos hpos 3) (pow_pos hpos 2)).2
      have hpow : (((p + d : ℕ) : ℝ)) ^ 2 ≤
          (((p + d : ℕ) : ℝ)) ^ 3 := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (sq_nonneg _) hpd1
      nlinarith
    calc
      negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2) ≤
          4 / (((p + d : ℕ) : ℝ)) ^ 2 +
            16 / (((p + d : ℕ) : ℝ)) ^ 3 := hb
      _ ≤ 4 / (((p + d : ℕ) : ℝ)) ^ 2 +
            16 / (((p + d : ℕ) : ℝ)) ^ 2 := add_le_add le_rfl hcube
      _ = 20 / (((p + d : ℕ) : ℝ)) ^ 2 := by ring
  have htoP : 20 / (((p + d : ℕ) : ℝ)) ^ 2 ≤ 20 / (p : ℝ) ^ 2 := by
    gcongr
  have hfactor : (p : ℝ) - 1 ≤ (p : ℝ) := by linarith
  have hnonneg : 0 ≤ negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2) :=
    negPsiTwoSeries_nonneg (by positivity)
  calc
    ((p : ℝ) - 1) * negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2) ≤
        (p : ℝ) * negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hfactor hnonneg
    _ ≤ (p : ℝ) * (20 / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (hb'.trans htoP) hpR.le
    _ = 20 / (p : ℝ) := by field_simp [hpR.ne']

private theorem tendsto_fixedGap_common_correction_zero (d : ℕ) :
    Tendsto (fun p : ℕ ↦ ((p : ℝ) - 1) *
      negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2)) atTop (nhds 0) := by
  have hbound : Tendsto (fun p : ℕ ↦ 20 / (p : ℝ)) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop).const_div_atTop 20
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with p hp
    exact fixedGap_common_correction_nonneg d p hp
  · filter_upwards [eventually_ge_atTop 2] with p hp
    exact fixedGap_common_correction_le d p hp
  · exact hbound

/-- Exact third-cumulant limit at every fixed gap. -/
theorem tendsto_fixedGap_nullASeries (d : ℕ) :
    Tendsto (fun p : ℕ ↦ nullASeries (p + d) p) atTop
      (nhds (hardEdgeAConstant d)) := by
  have hpartial : Tendsto
      (fun p : ℕ ↦ ∑ n ∈ Finset.range (p - 1),
        negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2))
      atTop (nhds (hardEdgeAConstant d)) :=
    (summable_hardEdgeA_terms d).hasSum.tendsto_sum_nat.comp
      (tendsto_nat_sub_const_atTop 1)
  have hsub := hpartial.sub (tendsto_fixedGap_common_correction_zero d)
  have hsub' : Tendsto
      (fun p : ℕ ↦ (∑ n ∈ Finset.range (p - 1),
        negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2)) -
        ((p : ℝ) - 1) * negPsiTwoSeries (((p + d : ℕ) : ℝ) / 2))
      atTop (nhds (hardEdgeAConstant d)) := by simpa using hsub
  apply hsub'.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  exact (nullASeries_fixedGap_eq d p hp).symm

/-- Two-sequence fixed-gap wrapper. -/
theorem tendsto_fixedGap_nullASeries_of_eventually_eq
    (m p : ℕ → ℕ) (d : ℕ)
    (hp : Tendsto p atTop atTop)
    (hgap : ∀ᶠ n in atTop, m n = p n + d) :
    Tendsto (fun n ↦ nullASeries (m n) (p n)) atTop
      (nhds (hardEdgeAConstant d)) := by
  have hbase := (tendsto_fixedGap_nullASeries d).comp hp
  apply hbase.congr'
  exact hgap.mono fun n hn ↦ by simp only [Function.comp_apply]; rw [hn]

private theorem sum_inv_Ico_fixedGap_eq_harmonic_sub
    (d p : ℕ) (hp : 1 ≤ p) :
    (∑ k ∈ Finset.Ico (d + 1) (p + d), (1 / (k : ℝ))) =
      (harmonic (p + d - 1) : ℝ) - (harmonic d : ℝ) := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hsub : Finset.Icc 1 d ⊆ Finset.Icc 1 (p + d - 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  rw [← Finset.sum_sdiff_eq_sub hsub]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  · intro k hk
    simp only [one_div]

/-- Exact harmonic-number formula for the elementary leading variance sum.
This is the finite master identity used in all growing-gap regimes. -/
theorem nullVLeading_eq_harmonic_sub {m p : ℕ} (h : Admissible m p) :
    nullVLeading m p =
      2 * ((harmonic (m - 1) : ℝ) - (harmonic (m - p) : ℝ) -
        ((p : ℝ) - 1) / (m : ℝ)) := by
  have hp : 2 ≤ p := h.1
  unfold nullVLeading nullGapPowerDifference
  rw [Finset.sum_sub_distrib]
  simp only [pow_one]
  have hsum := sum_inv_Ico_fixedGap_eq_harmonic_sub (m - p) p (by omega)
  have hadd : p + (m - p) = m := Nat.add_sub_of_le h.2
  rw [hadd] at hsum
  rw [hsum, Finset.sum_const, Nat.card_Ico]
  simp only [nsmul_eq_mul]
  have hcard : m - (m - p + 1) = p - 1 := by omega
  rw [hcard, Nat.cast_sub (by omega : 1 ≤ p)]
  ring

/-- Exact elementary variance formula at fixed gap. -/
theorem nullVLeading_fixedGap_eq (d p : ℕ) (hp : 2 ≤ p) :
    nullVLeading (p + d) p =
      2 * ((harmonic (p + d - 1) : ℝ) - (harmonic d : ℝ) -
        ((p : ℝ) - 1) / ((p + d : ℕ) : ℝ)) := by
  unfold nullVLeading nullGapPowerDifference
  have hgap : p + d - p + 1 = d + 1 := by omega
  rw [hgap, Finset.sum_sub_distrib]
  simp only [pow_one]
  rw [sum_inv_Ico_fixedGap_eq_harmonic_sub d p (by omega)]
  have hlen : p + d - (d + 1) = p - 1 := by omega
  rw [Finset.sum_const, Nat.card_Ico, hlen]
  simp only [nsmul_eq_mul, pow_one]
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  ring

private theorem tendsto_log_fixed_add_sub_one_sub_log_zero (d : ℕ) :
    Tendsto (fun p : ℕ ↦
      Real.log ((p + d - 1 : ℕ) : ℝ) - Real.log (p : ℝ))
      atTop (nhds 0) := by
  have hreal := (Real.tendsto_log_comp_add_sub_log ((d : ℝ) - 1)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop)
  apply hreal.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hcast : (((p + d - 1 : ℕ) : ℝ)) = (p : ℝ) + (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p + d), Nat.cast_add]
    norm_num
  simp only [Function.comp_apply]
  rw [hcast]
  congr 2 <;> ring

private theorem tendsto_log_fixed_add_sub_one_div_log_one (d : ℕ) :
    Tendsto (fun p : ℕ ↦
      Real.log ((p + d - 1 : ℕ) : ℝ) / Real.log (p : ℝ))
      atTop (nhds 1) := by
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun p : ℕ ↦ 1 / Real.log (p : ℝ)) atTop (nhds 0) :=
    hlog.const_div_atTop 1
  have hsmall := (tendsto_log_fixed_add_sub_one_sub_log_zero d).mul hinv
  have hadd : Tendsto (fun p : ℕ ↦ 1 +
      (Real.log ((p + d - 1 : ℕ) : ℝ) - Real.log (p : ℝ)) *
        (1 / Real.log (p : ℝ))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  apply hadd.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  field_simp [hlogpos.ne']
  ring

private theorem tendsto_harmonic_fixed_add_sub_one_div_log_one (d : ℕ) :
    Tendsto (fun p : ℕ ↦
      (harmonic (p + d - 1) : ℝ) / Real.log (p : ℝ))
      atTop (nhds 1) := by
  have hindex := tendsto_nat_add_sub_one_atTop d
  have hEuler := Real.tendsto_harmonic_sub_log.comp hindex
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun p : ℕ ↦ 1 / Real.log (p : ℝ)) atTop (nhds 0) :=
    hlog.const_div_atTop 1
  have herror := hEuler.mul hinv
  have hsum : Tendsto (fun p : ℕ ↦
      Real.log ((p + d - 1 : ℕ) : ℝ) / Real.log (p : ℝ) +
        ((harmonic (p + d - 1) : ℝ) -
          Real.log ((p + d - 1 : ℕ) : ℝ)) *
          (1 / Real.log (p : ℝ))) atTop (nhds 1) := by
    simpa only [Function.comp_apply, add_zero, mul_zero] using
      (tendsto_log_fixed_add_sub_one_div_log_one d).add herror
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  field_simp [hlogpos.ne']
  ring

private theorem tendsto_fixedGap_fraction_one (d : ℕ) :
    Tendsto (fun p : ℕ ↦ ((p : ℝ) - 1) / ((p + d : ℕ) : ℝ))
      atTop (nhds 1) := by
  have hpTop : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun p : ℕ ↦ 1 / (p : ℝ)) atTop (nhds 0) :=
    hpTop.const_div_atTop 1
  have hnum : Tendsto (fun p : ℕ ↦ 1 - 1 / (p : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hden : Tendsto (fun p : ℕ ↦ 1 + (d : ℝ) / (p : ℝ)) atTop (nhds 1) := by
    have hd := hinv.const_mul (d : ℝ)
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add hd
  have hquot : Tendsto (fun p : ℕ ↦
      (1 - 1 / (p : ℝ)) / (1 + (d : ℝ) / (p : ℝ)))
      atTop (nhds 1) := by
    convert hnum.div hden (by norm_num) using 1
    · funext p
      rfl
    · norm_num
  apply hquot.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hpR : 0 < (p : ℝ) := by positivity
  have hpd : ((p + d : ℕ) : ℝ) = (p : ℝ) + (d : ℝ) := by norm_num
  rw [hpd]
  field_simp [hpR.ne']

/-- The exact variance has the fixed-gap equivalent `2 log p`. -/
theorem tendsto_fixedGap_nullVLeading_div_log (d : ℕ) :
    Tendsto (fun p : ℕ ↦ nullVLeading (p + d) p / Real.log (p : ℝ))
      atTop (nhds 2) := by
  have hH := tendsto_harmonic_fixed_add_sub_one_div_log_one d
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun p : ℕ ↦ 1 / Real.log (p : ℝ)) atTop (nhds 0) :=
    hlog.const_div_atTop 1
  have hconst : Tendsto (fun p : ℕ ↦ (harmonic d : ℝ) / Real.log (p : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul (harmonic d : ℝ)
  have hfrac := (tendsto_fixedGap_fraction_one d).mul hinv
  have hcore := (hH.sub hconst).sub hfrac
  have htwo : Tendsto (fun p : ℕ ↦ 2 *
      ((harmonic (p + d - 1) : ℝ) / Real.log (p : ℝ) -
        (harmonic d : ℝ) / Real.log (p : ℝ) -
        (((p : ℝ) - 1) / ((p + d : ℕ) : ℝ)) *
          (1 / Real.log (p : ℝ)))) atTop (nhds 2) := by
    simpa using hcore.const_mul 2
  apply htwo.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  rw [nullVLeading_fixedGap_eq d p hp]
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  field_simp [hlogpos.ne']

private theorem fixedGap_variance_comparison_bound (d p : ℕ) (hp : 2 ≤ p) :
    |nullVSeries (p + d) p - nullVLeading (p + d) p| ≤
      4 * (Real.pi ^ 2 / 6) + 4 := by
  have hadm : Admissible (p + d) p := ⟨hp, by omega⟩
  have hbase := abs_nullVSeries_sub_nullVLeading_le hadm
  have hgap : p + d - p + 1 = d + 1 := by omega
  rw [hgap] at hbase
  have hsplit :
      (∑ k ∈ Finset.Ico (d + 1) (p + d),
        (4 / (k : ℝ) ^ 2 + 4 / ((p + d : ℕ) : ℝ) ^ 2)) =
      (∑ k ∈ Finset.Ico (d + 1) (p + d), 4 / (k : ℝ) ^ 2) +
      (∑ _k ∈ Finset.Ico (d + 1) (p + d),
        4 / ((p + d : ℕ) : ℝ) ^ 2) := by rw [Finset.sum_add_distrib]
  rw [hsplit] at hbase
  have hzeta : (∑ k ∈ Finset.Ico (d + 1) (p + d), 4 / (k : ℝ) ^ 2) ≤
      4 * (Real.pi ^ 2 / 6) := by
    have hs := hasSum_zeta_two.mul_left 4
    have hle := hs.summable.sum_le_tsum (Finset.Ico (d + 1) (p + d))
      (fun k hk ↦ by positivity)
    rw [hs.tsum_eq] at hle
    calc
      (∑ k ∈ Finset.Ico (d + 1) (p + d), 4 / (k : ℝ) ^ 2) =
          ∑ k ∈ Finset.Ico (d + 1) (p + d),
            4 * (1 / (k : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 4 * (Real.pi ^ 2 / 6) := hle
  have hconst :
      (∑ _k ∈ Finset.Ico (d + 1) (p + d),
        4 / ((p + d : ℕ) : ℝ) ^ 2) ≤ 4 := by
    rw [Finset.sum_const, Nat.card_Ico]
    simp only [nsmul_eq_mul]
    have hlen : p + d - (d + 1) = p - 1 := by omega
    rw [hlen]
    have hpR : 0 < (p : ℝ) := by positivity
    have hpdR : (p : ℝ) ≤ ((p + d : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right p d
    have hnum : (((p - 1 : ℕ) : ℝ)) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
    have hden : (p : ℝ) ≤ ((p + d : ℕ) : ℝ) ^ 2 := by
      have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
      nlinarith [sq_nonneg (((p + d : ℕ) : ℝ) - (p : ℝ))]
    have hratio : (((p - 1 : ℕ) : ℝ)) / ((p + d : ℕ) : ℝ) ^ 2 ≤ 1 := by
      apply (div_le_one (pow_pos (by positivity) 2)).2
      exact hnum.trans hden
    calc
      (((p - 1 : ℕ) : ℝ)) * (4 / ((p + d : ℕ) : ℝ) ^ 2) =
          4 * ((((p - 1 : ℕ) : ℝ)) / ((p + d : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = 4 := by ring
  exact hbase.trans (by linarith)

/-- The exact variance has the fixed-gap equivalent `2 log p`. -/
theorem tendsto_fixedGap_nullVSeries_div_log (d : ℕ) :
    Tendsto (fun p : ℕ ↦ nullVSeries (p + d) p / Real.log (p : ℝ))
      atTop (nhds 2) := by
  let B : ℝ := 4 * (Real.pi ^ 2 / 6) + 4
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun p : ℕ ↦ B / Real.log (p : ℝ)) atTop (nhds 0) :=
    hlog.const_div_atTop B
  have herr : Tendsto (fun p : ℕ ↦
      (nullVSeries (p + d) p - nullVLeading (p + d) p) /
        Real.log (p : ℝ)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun p ↦ abs_nonneg _
    · filter_upwards [eventually_ge_atTop 2] with p hp
      have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
      simp only [Function.comp_apply, abs_div, abs_of_pos hlogpos]
      exact div_le_div_of_nonneg_right
        (fixedGap_variance_comparison_bound d p hp) hlogpos.le
    · exact hB
  have hadd : Tendsto (fun p : ℕ ↦
      nullVLeading (p + d) p / Real.log (p : ℝ) +
        (nullVSeries (p + d) p - nullVLeading (p + d) p) /
          Real.log (p : ℝ)) atTop (nhds 2) := by
    simpa using (tendsto_fixedGap_nullVLeading_div_log d).add herr
  apply hadd.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  field_simp [hlogpos.ne']
  ring

/-- Fixed-gap standardized third-cumulant equivalent. -/
theorem tendsto_fixedGap_nullLambda_logPow (d : ℕ) :
    Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) ^ (3 / 2 : ℝ) * nullLambdaSeries (p + d) p)
      atTop (nhds (hardEdgeAConstant d / (2 : ℝ) ^ (3 / 2 : ℝ))) := by
  have hA := tendsto_fixedGap_nullASeries d
  have hV := tendsto_fixedGap_nullVSeries_div_log d
  have hVr : Tendsto (fun p : ℕ ↦
      (nullVSeries (p + d) p / Real.log (p : ℝ)) ^ (3 / 2 : ℝ))
      atTop (nhds ((2 : ℝ) ^ (3 / 2 : ℝ))) :=
    hV.rpow_const (Or.inl (by norm_num : (2 : ℝ) ≠ 0))
  have hdenne : (2 : ℝ) ^ (3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hquot := hA.div hVr hdenne
  apply hquot.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hadm : Admissible (p + d) p := ⟨hp, by omega⟩
  have hVpos := nullVSeries_pos hadm
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  simp only [Pi.div_apply]
  rw [nullLambdaSeries_eq, Real.div_rpow hVpos.le hlogpos.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hVpos _),
    ne_of_gt (Real.rpow_pos_of_pos hlogpos _)]

/-- Two-sequence fixed-gap variance wrapper. -/
theorem tendsto_fixedGap_nullVSeries_div_log_of_eventually_eq
    (m p : ℕ → ℕ) (d : ℕ)
    (hp : Tendsto p atTop atTop)
    (hgap : ∀ᶠ n in atTop, m n = p n + d) :
    Tendsto (fun n ↦ nullVSeries (m n) (p n) / Real.log (p n : ℝ))
      atTop (nhds 2) := by
  have hbase := (tendsto_fixedGap_nullVSeries_div_log d).comp hp
  apply hbase.congr'
  exact hgap.mono fun n hn ↦ by simp only [Function.comp_apply]; rw [hn]

/-- Two-sequence fixed-gap standardized-cumulant wrapper. -/
theorem tendsto_fixedGap_nullLambda_logPow_of_eventually_eq
    (m p : ℕ → ℕ) (d : ℕ)
    (hp : Tendsto p atTop atTop)
    (hgap : ∀ᶠ n in atTop, m n = p n + d) :
    Tendsto (fun n ↦ Real.log (p n : ℝ) ^ (3 / 2 : ℝ) *
      nullLambdaSeries (m n) (p n)) atTop
      (nhds (hardEdgeAConstant d / (2 : ℝ) ^ (3 / 2 : ℝ))) := by
  have hbase := (tendsto_fixedGap_nullLambda_logPow d).comp hp
  apply hbase.congr'
  exact hgap.mono fun n hn ↦ by simp only [Function.comp_apply]; rw [hn]

/-- Square specialization of the fixed-gap variance theorem. -/
theorem tendsto_square_nullVSeries_div_log :
    Tendsto (fun p : ℕ ↦ nullVSeries p p / Real.log (p : ℝ))
      atTop (nhds 2) := by simpa using tendsto_fixedGap_nullVSeries_div_log 0

/-- Square specialization of the exact third-cumulant limit. -/
theorem tendsto_square_nullASeries :
    Tendsto (fun p : ℕ ↦ nullASeries p p) atTop
      (nhds (hardEdgeAConstant 0)) := by simpa using tendsto_fixedGap_nullASeries 0

/-- Square specialization of the standardized third-cumulant equivalent. -/
theorem tendsto_square_nullLambda_logPow :
    Tendsto (fun p : ℕ ↦
      Real.log (p : ℝ) ^ (3 / 2 : ℝ) * nullLambdaSeries p p)
      atTop (nhds (hardEdgeAConstant 0 / (2 : ℝ) ^ (3 / 2 : ℝ))) := by
  simpa using tendsto_fixedGap_nullLambda_logPow 0

/-! ## Elementary power-sum bounds for a growing gap -/

private theorem forward_inv_gap_le_inv_sq {k : ℕ} (hk : 1 ≤ k) :
    1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 / (k : ℝ) ^ 2 := by
  have hkR : 0 < (k : ℝ) := by positivity
  have hk1R : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  push_cast at hk1R ⊢
  field_simp [hkR.ne', hk1R.ne']
  nlinarith

private theorem inv_sq_le_backward_inv_gap {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 2 ≤ 1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := by
  have hkm : 0 < k - 1 := by omega
  have hkR : 0 < (k : ℝ) := by positivity
  have hkmR : 0 < ((k - 1 : ℕ) : ℝ) := by positivity
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [hcast]
  have hkR2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkmR' : 0 < (k : ℝ) - 1 := by linarith
  have heq : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) =
      1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
    field_simp [hkR.ne', hkmR'.ne']
    ring
  rw [heq]
  apply one_div_le_one_div_of_le (mul_pos hkR hkmR')
  nlinarith

private theorem sum_forward_inv_gap (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b,
      (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) =
      1 / (a : ℝ) - 1 / (b : ℝ) := by
  let f : ℕ → ℝ := fun k ↦ 1 / (k : ℝ)
  have htel := Finset.sum_Ico_sub f hab
  calc
    (∑ k ∈ Finset.Ico a b,
        (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) =
        ∑ k ∈ Finset.Ico a b, -(f (k + 1) - f k) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f]
      ring
    _ = -∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) :=
      Finset.sum_neg_distrib (fun k ↦ f (k + 1) - f k)
    _ = -(f b - f a) := by rw [htel]
    _ = 1 / (a : ℝ) - 1 / (b : ℝ) := by dsimp [f]; ring

private theorem sum_backward_inv_gap (d m : ℕ) (hd : 1 ≤ d) (hdm : d + 1 ≤ m) :
    (∑ k ∈ Finset.Ico (d + 1) m,
      (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ))) =
      1 / (d : ℝ) - 1 / ((m - 1 : ℕ) : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : m - (d + 1) = (m - 1) - d := by omega
  rw [hlen]
  have htel := sum_forward_inv_gap d (m - 1) (by omega)
  rw [Finset.sum_Ico_eq_sum_range] at htel
  calc
    (∑ x ∈ Finset.range (m - 1 - d),
        (1 / (↑(d + 1 + x - 1) : ℝ) - 1 / (↑(d + 1 + x) : ℝ))) =
        ∑ x ∈ Finset.range (m - 1 - d),
          (1 / (↑(d + x) : ℝ) - 1 / (↑(d + x + 1) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have h₁ : d + 1 + n - 1 = d + n := by omega
      have h₂ : d + 1 + n = d + n + 1 := by omega
      rw [h₁, h₂]
    _ = 1 / (d : ℝ) - 1 / ((m - 1 : ℕ) : ℝ) := htel

private theorem sum_inv_sq_bounds {d m : ℕ} (hd : 1 ≤ d) (hdm : d + 1 ≤ m) :
    1 / ((d + 1 : ℕ) : ℝ) - 1 / (m : ℝ) ≤
      (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2) ∧
    (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2) ≤
      1 / (d : ℝ) - 1 / ((m - 1 : ℕ) : ℝ) := by
  constructor
  · rw [← sum_forward_inv_gap (d + 1) m (by omega)]
    apply Finset.sum_le_sum
    intro k hk
    have hkb := Finset.mem_Ico.mp hk
    exact forward_inv_gap_le_inv_sq (k := k) (by omega)
  · rw [← sum_backward_inv_gap d m hd hdm]
    apply Finset.sum_le_sum
    intro k hk
    have hkb := Finset.mem_Ico.mp hk
    exact inv_sq_le_backward_inv_gap (k := k) (by omega)

/-- Two-sided elementary bounds for the cancellation-preserving `S2`. -/
theorem nullGapPowerDifference_two_bounds {m p : ℕ}
    (h : Admissible m p) (hd : 1 ≤ m - p) :
    1 / (((m - p + 1 : ℕ) : ℝ)) - 1 / (m : ℝ) -
        ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
      nullGapPowerDifference 2 m p ∧
    nullGapPowerDifference 2 m p ≤
      1 / (((m - p : ℕ) : ℝ)) - 1 / (((m - 1 : ℕ) : ℝ)) -
        ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
  have hmpos : 0 < m := by omega
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hdm : m - p + 1 ≤ m := by omega
  have hs := sum_inv_sq_bounds hd hdm
  unfold nullGapPowerDifference
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico]
  simp only [nsmul_eq_mul]
  have hcard : m - (m - p + 1) = p - 1 := by omega
  rw [hcard, Nat.cast_sub (by omega : 1 ≤ p)]
  constructor
  · convert sub_le_sub_right hs.1 (((p : ℝ) - 1) / (m : ℝ) ^ 2) using 1 <;> ring
  · convert sub_le_sub_right hs.2 (((p : ℝ) - 1) / (m : ℝ) ^ 2) using 1 <;> ring

private theorem inv_cube_le_gap_inv_mul_inv_sq
    {d k : ℕ} (hd : 1 ≤ d) (hdk : d ≤ k) :
    1 / (k : ℝ) ^ 3 ≤ (1 / (d : ℝ)) * (1 / (k : ℝ) ^ 2) := by
  have hdR : 0 < (d : ℝ) := by positivity
  have hk1 : 1 ≤ k := hd.trans hdk
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hdkR : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hdk
  field_simp [hdR.ne', hkR.ne']
  nlinarith

private theorem sum_inv_cube_gap_le {d m : ℕ} (hd : 1 ≤ d) (hdm : d + 1 ≤ m) :
    (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 3) ≤
      1 / (d : ℝ) ^ 2 := by
  have hpoint :
      (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 3) ≤
        ∑ k ∈ Finset.Ico (d + 1) m,
          (1 / (d : ℝ)) * (1 / (k : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkb := Finset.mem_Ico.mp hk
    exact inv_cube_le_gap_inv_mul_inv_sq hd (by omega)
  rw [← Finset.mul_sum] at hpoint
  have hs := (sum_inv_sq_bounds hd hdm).2
  have hsum_nonneg : 0 ≤
      (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2) := by positivity
  have hsimple :
      (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2) ≤
        1 / (d : ℝ) := by
    have hm1pos : 0 < m - 1 := by omega
    have hinvnonneg : 0 ≤ 1 / (((m - 1 : ℕ) : ℝ)) := by positivity
    linarith
  calc
    (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 3) ≤
        (1 / (d : ℝ)) *
          (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2) := hpoint
    _ ≤ (1 / (d : ℝ)) * (1 / (d : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsimple (by positivity)
    _ = 1 / (d : ℝ) ^ 2 := by ring

/-- Explicit growing-gap error for the variance comparison `V=2S1+error`. -/
theorem abs_nullVSeries_sub_nullVLeading_growingGap_le {m p : ℕ}
    (h : Admissible m p) (hd : 1 ≤ m - p) :
    |nullVSeries m p - nullVLeading m p| ≤
      4 / ((m - p : ℕ) : ℝ) +
        4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
  have hbase := abs_nullVSeries_sub_nullVLeading_le h
  let d : ℕ := m - p
  have hdm : d + 1 ≤ m := by
    dsimp [d]
    have hp := h.1
    have hpm := h.2
    omega
  have hs := (sum_inv_sq_bounds (d := d) (m := m) hd hdm).2
  have hsimp : (∑ k ∈ Finset.Ico (d + 1) m, 4 / (k : ℝ) ^ 2) ≤
      4 / (d : ℝ) := by
    have hm1pos : 0 < m - 1 := by omega
    have hnonneg : 0 ≤ 1 / (((m - 1 : ℕ) : ℝ)) := by positivity
    calc
      (∑ k ∈ Finset.Ico (d + 1) m, 4 / (k : ℝ) ^ 2) =
          4 * ∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 4 * (1 / (d : ℝ) - 1 / (((m - 1 : ℕ) : ℝ))) := by gcongr
      _ ≤ 4 * (1 / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ hnonneg) (by norm_num)
      _ = 4 / (d : ℝ) := by ring
  have hsplit :
      (∑ k ∈ Finset.Ico (d + 1) m,
        (4 / (k : ℝ) ^ 2 + 4 / (m : ℝ) ^ 2)) =
      (∑ k ∈ Finset.Ico (d + 1) m, 4 / (k : ℝ) ^ 2) +
      ((p : ℝ) - 1) * (4 / (m : ℝ) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico]
    simp only [nsmul_eq_mul]
    have hcard : m - (d + 1) = p - 1 := by
      dsimp [d]
      have hp := h.1
      have hpm := h.2
      omega
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  change |nullVSeries m p - nullVLeading m p| ≤
    4 / (d : ℝ) + 4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2
  rw [hsplit] at hbase
  calc
    |nullVSeries m p - nullVLeading m p| ≤
        (∑ k ∈ Finset.Ico (d + 1) m, 4 / (k : ℝ) ^ 2) +
          ((p : ℝ) - 1) * (4 / (m : ℝ) ^ 2) := hbase
    _ ≤ 4 / (d : ℝ) + ((p : ℝ) - 1) * (4 / (m : ℝ) ^ 2) :=
      add_le_add hsimp le_rfl
    _ = 4 / (d : ℝ) + 4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by ring

/-- Explicit growing-gap error for the third-cumulant comparison `A=4S2+error`. -/
theorem abs_nullASeries_sub_nullALeading_growingGap_le {m p : ℕ}
    (h : Admissible m p) (hd : 1 ≤ m - p) :
    |nullASeries m p - nullALeading m p| ≤
      16 / ((m - p : ℕ) : ℝ) ^ 2 +
        16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 := by
  have hbase := abs_nullASeries_sub_nullALeading_le h
  let d : ℕ := m - p
  have hdm : d + 1 ≤ m := by
    dsimp [d]
    have hp := h.1
    have hpm := h.2
    omega
  have hcub := sum_inv_cube_gap_le (d := d) (m := m) hd hdm
  have hcub16 : (∑ k ∈ Finset.Ico (d + 1) m, 16 / (k : ℝ) ^ 3) ≤
      16 / (d : ℝ) ^ 2 := by
    calc
      (∑ k ∈ Finset.Ico (d + 1) m, 16 / (k : ℝ) ^ 3) =
          16 * ∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) ^ 3 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 16 * (1 / (d : ℝ) ^ 2) := by gcongr
      _ = 16 / (d : ℝ) ^ 2 := by ring
  have hsplit :
      (∑ k ∈ Finset.Ico (d + 1) m,
        (16 / (k : ℝ) ^ 3 + 16 / (m : ℝ) ^ 3)) =
      (∑ k ∈ Finset.Ico (d + 1) m, 16 / (k : ℝ) ^ 3) +
      ((p : ℝ) - 1) * (16 / (m : ℝ) ^ 3) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico]
    simp only [nsmul_eq_mul]
    have hcard : m - (d + 1) = p - 1 := by
      dsimp [d]
      have hp := h.1
      have hpm := h.2
      omega
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  change |nullASeries m p - nullALeading m p| ≤
    16 / (d : ℝ) ^ 2 + 16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3
  rw [hsplit] at hbase
  calc
    |nullASeries m p - nullALeading m p| ≤
        (∑ k ∈ Finset.Ico (d + 1) m, 16 / (k : ℝ) ^ 3) +
          ((p : ℝ) - 1) * (16 / (m : ℝ) ^ 3) := hbase
    _ ≤ 16 / (d : ℝ) ^ 2 + ((p : ℝ) - 1) * (16 / (m : ℝ) ^ 3) :=
      add_le_add hcub16 le_rfl
    _ = 16 / (d : ℝ) ^ 2 + 16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 := by ring

end

end LogdetLean
