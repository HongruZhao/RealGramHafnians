import LogdetLean.GeneralRPairLaplace
import LogdetLean.NegativeBinomialTail
import Mathlib.Tactic
open Real

noncomputable section

namespace LogdetLean

lemma inv_sqrt_pow_eq_one_div_rpow_half' (x : ℝ) (m : ℕ) (hx : 0 < x) :
    (Real.sqrt x)⁻¹ ^ m = 1 / x ^ ((m : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_neg hx.le]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx.le]
  simp only [one_div]
  rw [← Real.rpow_neg hx.le]
  congr 1
  ring

def laplaceA (s t : ℝ) : ℝ := (1 + 2 * s) * (1 + 2 * t)
def laplaceB (s t : ℝ) : ℝ := 4 * s * t / laplaceA s t

lemma laplaceA_pos {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 < laplaceA s t := by
  unfold laplaceA
  exact mul_pos (by linarith) (by linarith)

lemma laplaceB_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ laplaceB s t := by
  unfold laplaceB
  exact div_nonneg (by positivity) (laplaceA_pos hs ht).le

lemma laplaceB_lt_one {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    laplaceB s t < 1 := by
  have hA := laplaceA_pos hs ht
  unfold laplaceB
  rw [div_lt_one hA]
  unfold laplaceA at *
  nlinarith

lemma laplace_discriminant_factor (s t z : ℝ)
    (hA : laplaceA s t ≠ 0) :
    (1 + 2 * s) * (1 + 2 * t) - 4 * z * s * t =
      laplaceA s t * (1 - z * laplaceB s t) := by
  unfold laplaceB
  field_simp [hA]
  unfold laplaceA
  ring

lemma jointLaplace_eq_nbExpansion {m : ℕ} {s t z : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (_hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) - 4 * z * s * t))⁻¹ ^ m =
      (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
        (1 / (1 - z * laplaceB s t) ^ ((m : ℝ) / 2)) := by
  have hA := laplaceA_pos hs ht
  have hb0 := laplaceB_nonneg hs ht
  have hb1 := laplaceB_lt_one hs ht
  have hzb : z * laplaceB s t < 1 :=
    (mul_le_of_le_one_left hb0 hz1).trans_lt hb1
  have hfac : 0 < laplaceA s t * (1 - z * laplaceB s t) :=
    mul_pos hA (sub_pos.mpr hzb)
  rw [laplace_discriminant_factor s t z hA.ne']
  rw [inv_sqrt_pow_eq_one_div_rpow_half' _ _ hfac]
  rw [Real.mul_rpow hA.le (sub_nonneg.mpr hzb.le)]
  field_simp

lemma jointLaplace_tail_eq {m : ℕ} (_hm : 0 < m) {s t z : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) - 4 * z * s * t))⁻¹ ^ m -
        (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
          (1 + ((m : ℝ) / 2) * z * laplaceB s t) =
      (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
        nbTail ((m : ℝ) / 2) (z * laplaceB s t) := by
  rw [jointLaplace_eq_nbExpansion hs ht hz0 hz1]
  have hb0 := laplaceB_nonneg hs ht
  have hb1 := laplaceB_lt_one hs ht
  have hzbabs : |z * laplaceB s t| < 1 := by
    rw [abs_of_nonneg (mul_nonneg hz0 hb0)]
    exact (mul_le_of_le_one_left hb0 hz1).trans_lt hb1
  rw [nbTail_eq hzbabs]
  ring

lemma jointLaplace_tail_le_fourth {m : ℕ} (hm : 0 < m) {s t z : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) - 4 * z * s * t))⁻¹ ^ m -
        (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
          (1 + ((m : ℝ) / 2) * z * laplaceB s t) ≤
      z ^ 2 *
        ((Real.sqrt ((1 + 2 * s) * (1 + 2 * t) - 4 * s * t))⁻¹ ^ m -
          (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
            (1 + ((m : ℝ) / 2) * laplaceB s t)) := by
  rw [jointLaplace_tail_eq hm hs ht hz0 hz1]
  have htail1 := jointLaplace_tail_eq (m := m) hm
    (s := s) (t := t) (z := (1 : ℝ)) hs ht (by norm_num) (by norm_num)
  have htail1' :
      (Real.sqrt ((1 + 2 * s) * (1 + 2 * t) - 4 * s * t))⁻¹ ^ m -
          (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
            (1 + ((m : ℝ) / 2) * laplaceB s t) =
        (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
          nbTail ((m : ℝ) / 2) (laplaceB s t) := by
    simpa only [one_mul, mul_one] using htail1
  rw [htail1']
  have hfactor : 0 ≤ 1 / (laplaceA s t) ^ ((m : ℝ) / 2) :=
    div_nonneg zero_le_one (Real.rpow_nonneg (laplaceA_pos hs ht).le _)
  calc
    (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
        nbTail ((m : ℝ) / 2) (z * laplaceB s t) ≤
      (1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
        (z ^ 2 * nbTail ((m : ℝ) / 2) (laplaceB s t)) := by
      exact mul_le_mul_of_nonneg_left
        (nbTail_le_sq_mul (by positivity)
          (laplaceB_nonneg hs ht) (laplaceB_lt_one hs ht) hz0 hz1)
        hfactor
    _ = z ^ 2 * ((1 / (laplaceA s t) ^ ((m : ℝ) / 2)) *
        nbTail ((m : ℝ) / 2) (laplaceB s t)) := by ring

end LogdetLean
