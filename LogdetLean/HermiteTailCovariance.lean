import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
/-!
# The algebraic fourth-chaos consequence of Mehler's identity

The source is Zhao, *On the Log Determinant of Sample Correlation Matrices
under Gaussianity*, arXiv:2608.00565v1, Lemma 5.2, printed p. 11, together
with the proof in the manuscript subsection “Direct computation of the
second chaos projection” and Appendix “The Hermite covariance identity.”
The one-dimensional identity credited there is Nourdin--Peccati (2012),
Proposition 2.2.1, p. 26; the Ornstein--Uhlenbeck/Mehler formulation is their
Definition 2.8.1 and Theorem 2.8.2, pp. 45--47.

This module proves the infinite-series inequality used after Mehler's
identity.  A `FourthChaosEnergy` records the nonnegative squared L2 norms of
the even chaos components of degrees `4,6,8,...`.  It does **not** claim that
a given random variable has such a profile; that analytic Hermite-expansion
bridge remains a separate theorem obligation.
-/

namespace LogdetLean

noncomputable section

open scoped BigOperators

/-- Squared L2 energies of chaos degrees `4,6,8,...`; index `q` corresponds
to total Hermite degree `2*(q+2)`. -/
structure FourthChaosEnergy where
  energy : ℕ → ℝ
  energy_nonneg : ∀ q, 0 ≤ energy q
  summable_energy : Summable energy

namespace FourthChaosEnergy

/-- Total variance represented by the orthogonal tail. -/
def total (P : FourthChaosEnergy) : ℝ := ∑' q, P.energy q

/-- Mehler covariance series at correlation `rho`. -/
def covarianceSeries (P : FourthChaosEnergy) (rho : ℝ) : ℝ :=
  ∑' q, rho ^ (2 * (q + 2)) * P.energy q

private theorem square_le_one {rho : ℝ} (hrho : |rho| ≤ 1) :
    rho ^ 2 ≤ 1 := by
  rw [abs_le] at hrho
  nlinarith [sq_nonneg (rho - 1), sq_nonneg (rho + 1)]

private theorem mehlerWeight_nonneg (rho : ℝ) (q : ℕ) :
    0 ≤ rho ^ (2 * (q + 2)) := by
  exact (even_two.mul_right (q + 2)).pow_nonneg rho

private theorem mehlerWeight_le_one {rho : ℝ} (hrho : |rho| ≤ 1)
    (q : ℕ) :
    rho ^ (2 * (q + 2)) ≤ 1 := by
  rw [show 2 * (q + 2) = 2 * (q + 2) by rfl, pow_mul]
  exact pow_le_one₀ (sq_nonneg rho) (square_le_one hrho)

private theorem mehlerWeight_le_fourth {rho : ℝ} (hrho : |rho| ≤ 1)
    (q : ℕ) :
    rho ^ (2 * (q + 2)) ≤ rho ^ 4 := by
  rw [show 2 * (q + 2) = 4 + 2 * q by omega, pow_add, pow_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (n := q) (sq_nonneg rho) (square_le_one hrho))
    ((show Even 4 by norm_num).pow_nonneg rho)

theorem summable_covarianceSeries_terms (P : FourthChaosEnergy) {rho : ℝ}
    (hrho : |rho| ≤ 1) :
    Summable (fun q ↦ rho ^ (2 * (q + 2)) * P.energy q) := by
  exact P.summable_energy.of_nonneg_of_le
    (fun q ↦ mul_nonneg (mehlerWeight_nonneg rho q) (P.energy_nonneg q))
    (fun q ↦ mul_le_of_le_one_left (P.energy_nonneg q)
      (mehlerWeight_le_one hrho q))

theorem total_nonneg (P : FourthChaosEnergy) : 0 ≤ P.total := by
  exact tsum_nonneg P.energy_nonneg

/-- The exact algebraic conclusion used in Zhao's residual-covariance proof:
the Mehler series is nonnegative and at most `rho^4` times its total energy. -/
theorem covarianceSeries_nonneg_and_le_fourth (P : FourthChaosEnergy)
    {rho : ℝ} (hrho : |rho| ≤ 1) :
    0 ≤ P.covarianceSeries rho ∧
      P.covarianceSeries rho ≤ rho ^ 4 * P.total := by
  have hsummable := P.summable_covarianceSeries_terms hrho
  constructor
  · unfold covarianceSeries
    exact tsum_nonneg fun q ↦
      mul_nonneg (mehlerWeight_nonneg rho q) (P.energy_nonneg q)
  · unfold covarianceSeries total
    calc
      ∑' q, rho ^ (2 * (q + 2)) * P.energy q ≤
          ∑' q, rho ^ 4 * P.energy q :=
        hsummable.tsum_le_tsum
          (fun q ↦ mul_le_mul_of_nonneg_right
            (mehlerWeight_le_fourth hrho q) (P.energy_nonneg q))
          (P.summable_energy.mul_left (rho ^ 4))
      _ = rho ^ 4 * ∑' q, P.energy q := by rw [tsum_mul_left]

/-- A transfer form convenient for a future actual Hermite expansion: if a
pair covariance and a variance have been identified with one common energy
profile, the desired fourth-power bound follows immediately. -/
theorem covariance_nonneg_and_le_of_representation
    (P : FourthChaosEnergy) {rho covariance variance : ℝ}
    (hrho : |rho| ≤ 1)
    (hcovariance : covariance = P.covarianceSeries rho)
    (hvariance : variance = P.total) :
    0 ≤ covariance ∧ covariance ≤ rho ^ 4 * variance := by
  rw [hcovariance, hvariance]
  exact P.covarianceSeries_nonneg_and_le_fourth hrho

end FourthChaosEnergy

end

end LogdetLean
