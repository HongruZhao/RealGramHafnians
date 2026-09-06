import LogdetLean.GramHafnian.ShiftedAnticoncentration.Definitions
/-!
# The deterministic inverse-moment recurrence

This file isolates the purely ordered-field part of the probabilistic
induction.  Later files provide the two probabilistic one-step estimates;
the theorem here assembles them without introducing any probabilistic axiom.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- One step of the inverse-energy induction at level `r`. -/
def inverseVarianceStep (k r : ℕ) : ℝ :=
  ((((2 : ℝ) * r - 2) * ((k : ℝ) - 4 * r + 1)))⁻¹

/-- The unnormalized inverse-variance bound obtained by iterating all levels
from `1` through `n`. -/
def inverseVarianceBound (k n : ℕ) : ℝ :=
  (((k : ℝ) - 1)⁻¹) *
    ∏ r ∈ Finset.Icc 2 n, inverseVarianceStep k r

lemma inverseVarianceStep_nonneg
    {k r n : ℕ} (hkr : 4 * n ≤ k) (h2r : 2 ≤ r) (hrn : r ≤ n) :
    0 ≤ inverseVarianceStep k r := by
  unfold inverseVarianceStep
  have hfirst : 0 < (2 : ℝ) * r - 2 := by
    have hr : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h2r
    linarith
  have hsecond : 0 < (k : ℝ) - 4 * r + 1 := by
    have hnat : 4 * r ≤ k := by omega
    have hreal : (4 : ℝ) * (r : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hnat
    linarith
  positivity

/-- Any nonnegative sequence satisfying the paper's base estimate and
one-step inverse-moment estimates is bounded by the explicit finite product.
This is the exact induction used for `E[V_n⁻¹]`. -/
theorem inverseVarianceBound_of_recurrence
    (u : ℕ → ℝ) (n k : ℕ) (hn : 1 ≤ n)
    (hu : ∀ r, r ≤ n → 0 ≤ u r)
    (hbase : u 1 ≤ ((k : ℝ) - 1)⁻¹)
    (hstep : ∀ r, 2 ≤ r → r ≤ n →
      u r ≤ inverseVarianceStep k r * u (r - 1))
    (hstep_nonneg : ∀ r, 2 ≤ r → r ≤ n →
      0 ≤ inverseVarianceStep k r) :
    u n ≤ inverseVarianceBound k n := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop :=
    fun j _ => j ≤ n → u j ≤ inverseVarianceBound k j
  have hind : P n hn := by
    apply Nat.le_induction (m := 1) (P := P)
      (n := n) (hmn := hn)
    · intro _
      simpa [P, inverseVarianceBound] using hbase
    · intro j hj ih hjn
      have hrec := hstep (j + 1) (by omega) hjn
      have hih : u j ≤ inverseVarianceBound k j := ih (by omega)
      have hmul :
          inverseVarianceStep k (j + 1) * u j ≤
            inverseVarianceStep k (j + 1) * inverseVarianceBound k j := by
        exact mul_le_mul_of_nonneg_left hih
          (hstep_nonneg (j + 1) (by omega) hjn)
      calc
        u (j + 1) ≤ inverseVarianceStep k (j + 1) * u j := by
          simpa using hrec
        _ ≤ inverseVarianceStep k (j + 1) * inverseVarianceBound k j := hmul
        _ = inverseVarianceBound k (j + 1) := by
          rw [inverseVarianceBound, inverseVarianceBound,
            Finset.prod_Icc_succ_top (by omega)]
          ring
  exact hind le_rfl

/-- Specialization in the admissible parameter range `k ≥ 4n`; positivity of
all recurrence factors is then automatic. -/
theorem inverseVarianceBound_of_paper_recurrence
    (u : ℕ → ℝ) (n k : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (hu : ∀ r, r ≤ n → 0 ≤ u r)
    (hbase : u 1 ≤ ((k : ℝ) - 1)⁻¹)
    (hstep : ∀ r, 2 ≤ r → r ≤ n →
      u r ≤ inverseVarianceStep k r * u (r - 1)) :
    u n ≤ inverseVarianceBound k n := by
  apply inverseVarianceBound_of_recurrence u n k hn hu hbase hstep
  intro r h2r hrn
  exact inverseVarianceStep_nonneg hkn h2r hrn

end

end LogdetLean.GramHafnian
