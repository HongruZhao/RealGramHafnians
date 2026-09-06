import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Tactic
open scoped ENNReal Topology

noncomputable section

def nbCoeff (a : ℝ) (n : ℕ) : ℝ := Ring.choose (a + n - 1) n

lemma nbCoeff_nonneg {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 ≤ nbCoeff a n := by
  have hp : 0 < (ascPochhammer ℝ n).eval a :=
    ascPochhammer_pos n a ha
  rw [nbCoeff, Ring.choose_eq_smul,
    Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  simp only [smul_eq_mul]
  have harg : a + (n : ℝ) - 1 - (n : ℝ) + 1 = a := by ring
  rw [harg]
  positivity

lemma nbCoeff_zero (a : ℝ) : nbCoeff a 0 = 1 := by
  simp [nbCoeff]

lemma nbCoeff_one (a : ℝ) : nbCoeff a 1 = a := by
  simp [nbCoeff]

lemma hasSum_nbCoeff_mul_pow {a x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ ↦ nbCoeff a n * x ^ n) (1 / (1 - x) ^ a) := by
  have h := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a
  have hx' : x ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hx
  have hs := h.hasSum_sub hx'
  have heq : (fun n : ℕ ↦
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ Ring.choose (a + n - 1) n) n) (fun _ ↦ x - 0)) =
      (fun n : ℕ ↦ nbCoeff a n * x ^ n) := by
    funext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [sub_zero, smul_eq_mul, nbCoeff]
  rw [heq] at hs
  exact hs

def nbTail (a z : ℝ) : ℝ :=
  ∑' n : ℕ, nbCoeff a (n + 2) * z ^ (n + 2)

lemma summable_nbCoeff_mul_pow {a x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ ↦ nbCoeff a n * x ^ n) :=
  (hasSum_nbCoeff_mul_pow hx).summable

lemma nbTail_nonneg {a z : ℝ} (ha : 0 < a) (hz : 0 ≤ z) :
    0 ≤ nbTail a z := by
  exact tsum_nonneg fun n ↦ mul_nonneg (nbCoeff_nonneg ha _) (pow_nonneg hz _)

lemma nbTail_eq {a x : ℝ} (hx : |x| < 1) :
    nbTail a x = 1 / (1 - x) ^ a - 1 - a * x := by
  let f : ℕ → ℝ := fun n ↦ nbCoeff a n * x ^ n
  have hsum : Summable f := summable_nbCoeff_mul_pow hx
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hfull : ∑' n, f n = 1 / (1 - x) ^ a :=
    (hasSum_nbCoeff_mul_pow hx).tsum_eq
  have htail : (∑' n, f (n + 2)) = nbTail a x := by rfl
  rw [show ∑ i ∈ Finset.range 2, f i = 1 + a * x by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp [f, nbCoeff]] at hsplit
  rw [htail, hfull] at hsplit
  linarith

lemma nbTail_le_sq_mul {a b z : ℝ} (ha : 0 < a)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    nbTail a (z * b) ≤ z ^ 2 * nbTail a b := by
  have hbabs : |b| < 1 := by simpa [abs_of_nonneg hb0]
  have hzbabs : |z * b| < 1 := by
    rw [abs_mul, abs_of_nonneg hz0, abs_of_nonneg hb0]
    exact (mul_le_of_le_one_left hb0 hz1).trans_lt hb1
  have hsum_b : Summable (fun n : ℕ ↦ nbCoeff a (n + 2) * b ^ (n + 2)) := by
    exact (summable_nbCoeff_mul_pow hbabs).comp_injective (fun _ _ h ↦ by omega)
  have hsum_zb : Summable (fun n : ℕ ↦ nbCoeff a (n + 2) * (z * b) ^ (n + 2)) := by
    exact (summable_nbCoeff_mul_pow hzbabs).comp_injective (fun _ _ h ↦ by omega)
  unfold nbTail
  calc
    ∑' n : ℕ, nbCoeff a (n + 2) * (z * b) ^ (n + 2) ≤
        ∑' n : ℕ, z ^ 2 * (nbCoeff a (n + 2) * b ^ (n + 2)) := by
      apply hsum_zb.tsum_le_tsum
      intro n
      rw [mul_pow]
      have hzpow : z ^ (n + 2) ≤ z ^ 2 := by
        rw [show n + 2 = 2 + n by omega, pow_add]
        exact mul_le_of_le_one_right (pow_nonneg hz0 2)
          (pow_le_one₀ hz0 hz1)
      calc
        nbCoeff a (n + 2) * (z ^ (n + 2) * b ^ (n + 2)) =
            z ^ (n + 2) * (nbCoeff a (n + 2) * b ^ (n + 2)) := by ring
        _ ≤ z ^ 2 * (nbCoeff a (n + 2) * b ^ (n + 2)) :=
          mul_le_mul_of_nonneg_right hzpow
            (mul_nonneg (nbCoeff_nonneg ha (n + 2)) (pow_nonneg hb0 (n + 2)))
      exact (hsum_b.mul_left (z ^ 2))
    _ = z ^ 2 * ∑' n : ℕ, nbCoeff a (n + 2) * b ^ (n + 2) := by
      rw [tsum_mul_left]
