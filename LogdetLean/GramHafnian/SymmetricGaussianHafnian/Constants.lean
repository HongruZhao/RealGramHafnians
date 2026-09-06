import LogdetLean.GramHafnian.ShiftedAnticoncentration.ConstantAlgebra
import LogdetLean.GramHafnian.ShiftedAnticoncentration.SimplifiedConstantBound
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Normalization
import LogdetLean.GramHafnian.ShiftedAnticoncentration.ConditionalSmallBall
/-!
# Constants and extended inverse-moment induction for symmetric hafnians

This module contains proved numerical/measure-theoretic implications, not
an assertion that the literal symmetric cofactor law satisfies the recurrence.
That model-specific obligation is kept separate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

def inverseBound (n : ℕ) : ℝ := (evenRecurrenceProduct n)⁻¹

def coefficient (n : ℕ) : ℝ := (oddPairingNat n : ℝ) * inverseBound n

def sigma (n : ℕ) : ℝ := Real.sqrt (oddPairingNat n : ℝ)

/-- Paper coefficient `b_{n,1}` for the real shifted-interval theorem. -/
def realHafnianSmallBallCoefficient (n : ℕ) : ℝ :=
  Real.sqrt (2 / Real.pi) * sigma n *
    ∏ r ∈ Finset.Icc 2 n,
      Real.Gamma ((r : ℝ) - 1) /
        (Real.sqrt 2 * Real.Gamma ((r : ℝ) - 1 / 2))

theorem inverseBound_closed (n : ℕ) (hn : 1 ≤ n) :
    inverseBound n = ((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ))⁻¹ := by
  rw [inverseBound, evenRecurrenceProduct_eq n hn]

theorem inverseBound_pos (n : ℕ) (hn : 1 ≤ n) : 0 < inverseBound n := by
  rw [inverseBound_closed n hn]
  positivity

@[simp] theorem inverseBound_one : inverseBound 1 = 1 := by
  norm_num [inverseBound, evenRecurrenceProduct]

theorem inverseBound_succ (n : ℕ) (hn : 1 ≤ n) :
    inverseBound (n + 1) = inverseBound n * ((2 : ℝ) * (n + 1) - 2)⁻¹ := by
  unfold inverseBound evenRecurrenceProduct
  rw [Finset.prod_Icc_succ_top (by omega), mul_inv]
  norm_cast

theorem coefficient_closed (n : ℕ) (hn : 1 ≤ n) :
    coefficient n = (oddPairingNat n : ℝ) /
      ((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ)) := by
  rw [coefficient, inverseBound_closed n hn, div_eq_mul_inv]

theorem coefficient_centralBinomial (n : ℕ) (hn : 1 ≤ n) :
    coefficient n = (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n := by
  exact oddPairing_mul_evenRecurrenceProduct_inv n hn

theorem coefficient_le_two_sqrt (n : ℕ) (hn : 1 ≤ n) :
    coefficient n ≤ 2 * Real.sqrt (n : ℝ) := by
  rw [coefficient_centralBinomial n hn]
  exact centralBinomial_prefactor_le_two_sqrt n

theorem sigma_sq (n : ℕ) : sigma n ^ 2 = (oddPairingNat n : ℝ) := by
  exact Real.sq_sqrt (Nat.cast_nonneg _)

theorem sigma_nonneg (n : ℕ) : 0 ≤ sigma n := Real.sqrt_nonneg _

/-- Extended moments are bounded before any conversion to ordinary integrals.
The recurrence is an explicit hypothesis; this theorem alone is not the
literal symmetric Gaussian anticoncentration theorem. -/
theorem inverseBound_of_recurrence
    (u : ℕ → ℝ≥0∞) (n : ℕ) (hn : 1 ≤ n)
    (hbase : u 1 ≤ 1)
    (hstep : ∀ r, 2 ≤ r → r ≤ n →
      u r ≤ u (r - 1) * ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹)) :
    u n ≤ ENNReal.ofReal (inverseBound n) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ =>
    j ≤ n → u j ≤ ENNReal.ofReal (inverseBound j)
  have hind : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · intro _
      simpa [P] using hbase
    · intro j hj ih hsucc
      have hrec := hstep (j + 1) (by omega) hsucc
      have hih := ih (by omega)
      calc
        u (j + 1) ≤ u j * ENNReal.ofReal (((2 : ℝ) * (j + 1) - 2)⁻¹) := by
          simpa using hrec
        _ ≤ ENNReal.ofReal (inverseBound j) *
            ENNReal.ofReal (((2 : ℝ) * (j + 1) - 2)⁻¹) :=
          mul_le_mul hih le_rfl bot_le bot_le
        _ = ENNReal.ofReal (inverseBound j * ((2 : ℝ) * (j + 1) - 2)⁻¹) := by
          rw [ENNReal.ofReal_mul (inverseBound_pos j hj).le]
        _ = ENNReal.ofReal (inverseBound (j + 1)) := by
          rw [inverseBound_succ j hj]
  exact hind le_rfl

theorem finite_of_recurrence
    (u : ℕ → ℝ≥0∞) (n : ℕ) (hn : 1 ≤ n)
    (hbase : u 1 ≤ 1)
    (hstep : ∀ r, 2 ≤ r → r ≤ n →
      u r ≤ u (r - 1) * ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹)) :
    u n < ⊤ := by
  exact lt_of_le_of_lt (inverseBound_of_recurrence u n hn hbase hstep)
    ENNReal.ofReal_lt_top

/-- A normalized disk bound for any genuine independent complex Gaussian
mixture whose cofactor inverse moment has been bounded. The explicit `hInv`
must be discharged for a literal hafnian model before claiming the paper's
unconditional endpoint. -/
theorem shiftedDisk_le_of_inverseBound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (y : Ω → Fin d → ℂ) (hy : Measurable y)
    (hpos : ∀ᵐ w ∂ν, 0 < conditionalCircularEnergy y w)
    (n : ℕ) (_hn : 1 ≤ n)
    (hInv : ennInverseMoment ν (conditionalCircularEnergy y) ≤
      ENNReal.ofReal (inverseBound n))
    (z : ℂ) (ε : ℝ) (hε : 0 ≤ ε) :
    (ν.prod (Measure.pi fun _ : Fin d => circularGaussian))
      {p : Ω × (Fin d → ℂ) |
        ‖conditionalCircularLinearForm y p - z‖ ≤ ε * sigma n} ≤
      min 1 (ENNReal.ofReal (coefficient n * ε ^ 2)) := by
  apply le_min
  · exact prob_le_one
  · have h := prod_pi_circularGaussian_shiftedSmallBall_le_inverseMoment
      ν y hy hpos z (ε * sigma n) (mul_nonneg hε (sigma_nonneg n))
    calc
      _ ≤ ENNReal.ofReal ((ε * sigma n) ^ 2) *
          ennInverseMoment ν (conditionalCircularEnergy y) := h
      _ ≤ ENNReal.ofReal ((ε * sigma n) ^ 2) * ENNReal.ofReal (inverseBound n) :=
        mul_le_mul le_rfl hInv bot_le bot_le
      _ = ENNReal.ofReal (coefficient n * ε ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_pow, sigma_sq]
        congr 1
        unfold coefficient
        ring

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
