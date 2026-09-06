import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGaussianGramTailSharp
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralResolventIteration
/-!
# Elementary tail bounds for the literal real cofactor recursion

This module specializes the generic transpose-Gram entry estimate to the
literal odd cofactor index and then sums it over the hafnian levels.  Symmetry
reduces the union to the diagonal and strict upper triangle, giving the exact
elementary prefactor `2 m²`; no independence between Gram entries is used.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The elementary envelope for the bad transpose-Gram event at level `r`.
It is stated using the literal cardinality `2*r-1`. -/
def pastRealCofactorGramBadEnvelope (r k : ℕ) (delta : ℝ) : ENNReal :=
  ENNReal.ofReal
    (2 * ((2 * r - 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (-((k : ℝ) *
        (delta / ((2 * r - 1 : ℕ) : ℝ)) ^ 2 / 8)))

/-- Direct literal specialization of the elementary Gaussian Gram-entry
union bound. -/
theorem pastRealCofactorGramBadProbability_le_envelope
    {r k : ℕ} (hr : 1 ≤ r) (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    pastRealCofactorGramBadProbability r k hr delta ≤
      pastRealCofactorGramBadEnvelope r k delta := by
  letI : Nonempty (OddCofactorIndex r hr) :=
    Fintype.card_pos_iff.mp (by
      rw [card_oddCofactorIndex]
      omega)
  have h := standardRealGaussianColumnFamily_not_good_le_ennreal_sharp
    (ι := OddCofactorIndex r hr) hk hdelta0 hdelta1
  unfold pastRealCofactorGramBadProbability
    pastRealCofactorGramBadEnvelope
  rw [card_oddCofactorIndex] at h
  convert h using 1
  rfl

/-- Proof-independent form used in the finite level sum. -/
theorem pastRealCofactorGramBadProbabilityNat_le_envelope
    {r k : ℕ} (hr : 1 ≤ r) (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    pastRealCofactorGramBadProbabilityNat r k delta ≤
      pastRealCofactorGramBadEnvelope r k delta := by
  rw [pastRealCofactorGramBadProbabilityNat_eq hr delta]
  exact pastRealCofactorGramBadProbability_le_envelope
    hr hk hdelta0 hdelta1

/-- The exact finite sum of the elementary level envelopes bounds the entire
bad-event cost in the literal real recursion. -/
theorem pastRealCofactorGramBadProbabilitySum_le_sum_envelopes
    {n k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    pastRealCofactorGramBadProbabilitySum n k delta ≤
      ∑ r ∈ Finset.Icc 2 n,
        pastRealCofactorGramBadEnvelope r k delta := by
  unfold pastRealCofactorGramBadProbabilitySum
  apply Finset.sum_le_sum
  intro r hr
  exact pastRealCofactorGramBadProbabilityNat_le_envelope
    (le_trans (by norm_num : 1 ≤ 2) (Finset.mem_Icc.mp hr).1)
    hk hdelta0 hdelta1

end

end LogdetLean.GramHafnian
