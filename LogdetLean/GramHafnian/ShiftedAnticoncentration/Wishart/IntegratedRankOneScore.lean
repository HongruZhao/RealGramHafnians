import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.HermitianRankOneDecomposition
/-!
# Assembly of fixed-direction score identities into a variable rank-one score

The cofactor vector depends on the preserved transpose Gram, so its Hermitian
rank-one matrix is not a fixed score direction.  The fixed coordinate
decomposition permits applying the Gaussian score theorem finitely many
times and summing the resulting integral identities.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {m Ω : Type*} [Fintype m] [DecidableEq m]
  [MeasurableSpace Ω]

def rankOneRealCoordinateWeight
    (u : Ω → ℝ) (c : Ω → m → ℂ) (i j : m) (ω : Ω) : ℝ :=
  u ω * ((c ω i * star (c ω j)).re / 2)

def rankOneImagCoordinateWeight
    (u : Ω → ℝ) (c : Ω → m → ℂ) (i j : m) (ω : Ω) : ℝ :=
  u ω * ((c ω i * star (c ω j)).im / 2)

theorem integrable_double_fintype_sum
    (f : m → m → Ω → ℝ)
    (hf : ∀ i j, Integrable (f i j) μ) :
    Integrable (fun ω ↦ ∑ i, ∑ j, f i j ω) μ := by
  apply integrable_finset_sum Finset.univ
  intro i _
  apply integrable_finset_sum Finset.univ
  intro j _
  exact hf i j

theorem integral_double_fintype_sum
    (f : m → m → Ω → ℝ)
    (hf : ∀ i j, Integrable (f i j) μ) :
    (∫ ω, ∑ i, ∑ j, f i j ω ∂μ) =
      ∑ i, ∑ j, ∫ ω, f i j ω ∂μ := by
  rw [integral_finset_sum Finset.univ (fun i _ ↦
    integrable_finset_sum Finset.univ (fun j _ ↦ hf i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ ↦ hf i j)]

/-- Coordinatewise left-score integrability assembles to integrability of
the variable rank-one left score. -/
theorem integrable_variable_rankOne_score_left_of_coordinates
    (μ : Measure Ω)
    (G : Ω → Matrix (m ⊕ m) (m ⊕ m) ℝ)
    (u : Ω → ℝ) (c : Ω → m → ℂ) (a : ℝ)
    (hLRe : ∀ i j, Integrable (fun ω ↦
      rankOneRealCoordinateWeight u c i j ω *
        (a * Matrix.trace
          (G ω * scoreDeltaM (hermitianRealCoordinateDirection i j)))) μ)
    (hLIm : ∀ i j, Integrable (fun ω ↦
      rankOneImagCoordinateWeight u c i j ω *
        (a * Matrix.trace
          (G ω * scoreDeltaM (hermitianImagCoordinateDirection i j)))) μ) :
    Integrable (fun ω ↦ u ω *
      (a * Matrix.trace
        (G ω * scoreDeltaM (hermitianRankOne (c ω))))) μ := by
  apply ((integrable_double_fintype_sum _ hLRe).add
    (integrable_double_fintype_sum _ hLIm)).congr
  filter_upwards [] with ω
  simp only [Pi.add_apply]
  rw [trace_mul_scoreDeltaM_hermitianRankOne_eq_sum]
  unfold rankOneRealCoordinateWeight rankOneImagCoordinateWeight
  rw [mul_add a, mul_add (u ω)]
  congr 1 <;>
    simp_rw [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Coordinatewise right-score integrability assembles to integrability of
the variable rank-one right score. -/
theorem integrable_variable_rankOne_score_right_of_coordinates
    (μ : Measure Ω)
    (u : Ω → ℝ) (c : Ω → m → ℂ)
    (hRRe : ∀ i j, Integrable (fun ω ↦
      rankOneRealCoordinateWeight u c i j ω *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j))) μ)
    (hRIm : ∀ i j, Integrable (fun ω ↦
      rankOneImagCoordinateWeight u c i j ω *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j))) μ) :
    Integrable (fun ω ↦ u ω *
      Matrix.trace (scoreDeltaM (hermitianRankOne (c ω)))) μ := by
  apply ((integrable_double_fintype_sum _ hRRe).add
    (integrable_double_fintype_sum _ hRIm)).congr
  filter_upwards [] with ω
  simp only [Pi.add_apply]
  rw [trace_scoreDeltaM_hermitianRankOne_eq_sum]
  unfold rankOneRealCoordinateWeight rankOneImagCoordinateWeight
  rw [mul_add (u ω)]
  congr 1 <;>
    simp_rw [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Finite assembly theorem.  Its hypotheses are precisely the fixed real
and imaginary coordinate score identities plus the integrability needed for
finite linearity of the Bochner integral. -/
theorem integral_variable_rankOne_score_eq_of_coordinate_scores
    (μ : Measure Ω)
    (G : Ω → Matrix (m ⊕ m) (m ⊕ m) ℝ)
    (u : Ω → ℝ) (c : Ω → m → ℂ) (a : ℝ)
    (hLRe : ∀ i j, Integrable (fun ω ↦
      rankOneRealCoordinateWeight u c i j ω *
        (a * Matrix.trace
          (G ω * scoreDeltaM (hermitianRealCoordinateDirection i j)))) μ)
    (hLIm : ∀ i j, Integrable (fun ω ↦
      rankOneImagCoordinateWeight u c i j ω *
        (a * Matrix.trace
          (G ω * scoreDeltaM (hermitianImagCoordinateDirection i j)))) μ)
    (hRRe : ∀ i j, Integrable (fun ω ↦
      rankOneRealCoordinateWeight u c i j ω *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j))) μ)
    (hRIm : ∀ i j, Integrable (fun ω ↦
      rankOneImagCoordinateWeight u c i j ω *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j))) μ)
    (hscoreRe : ∀ i j,
      (∫ ω, rankOneRealCoordinateWeight u c i j ω *
          (a * Matrix.trace
            (G ω * scoreDeltaM (hermitianRealCoordinateDirection i j))) ∂μ) =
        ∫ ω, rankOneRealCoordinateWeight u c i j ω *
          Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)) ∂μ)
    (hscoreIm : ∀ i j,
      (∫ ω, rankOneImagCoordinateWeight u c i j ω *
          (a * Matrix.trace
            (G ω * scoreDeltaM (hermitianImagCoordinateDirection i j))) ∂μ) =
        ∫ ω, rankOneImagCoordinateWeight u c i j ω *
          Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)) ∂μ) :
    (∫ ω, u ω *
        (a * Matrix.trace
          (G ω * scoreDeltaM (hermitianRankOne (c ω)))) ∂μ) =
      ∫ ω, u ω *
        Matrix.trace (scoreDeltaM (hermitianRankOne (c ω))) ∂μ := by
  have hleftPoint (ω : Ω) :
      u ω * (a * Matrix.trace
        (G ω * scoreDeltaM (hermitianRankOne (c ω)))) =
      (∑ i, ∑ j,
        rankOneRealCoordinateWeight u c i j ω *
          (a * Matrix.trace
            (G ω * scoreDeltaM (hermitianRealCoordinateDirection i j)))) +
      (∑ i, ∑ j,
        rankOneImagCoordinateWeight u c i j ω *
          (a * Matrix.trace
            (G ω * scoreDeltaM (hermitianImagCoordinateDirection i j)))) := by
    rw [trace_mul_scoreDeltaM_hermitianRankOne_eq_sum]
    unfold rankOneRealCoordinateWeight rankOneImagCoordinateWeight
    rw [mul_add a, mul_add (u ω)]
    congr 1 <;>
      simp_rw [Finset.mul_sum] <;>
      apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have hrightPoint (ω : Ω) :
      u ω * Matrix.trace (scoreDeltaM (hermitianRankOne (c ω))) =
      (∑ i, ∑ j,
        rankOneRealCoordinateWeight u c i j ω *
          Matrix.trace
            (scoreDeltaM (hermitianRealCoordinateDirection i j))) +
      (∑ i, ∑ j,
        rankOneImagCoordinateWeight u c i j ω *
          Matrix.trace
            (scoreDeltaM (hermitianImagCoordinateDirection i j))) := by
    rw [trace_scoreDeltaM_hermitianRankOne_eq_sum]
    unfold rankOneRealCoordinateWeight rankOneImagCoordinateWeight
    rw [mul_add (u ω)]
    congr 1 <;>
      simp_rw [Finset.mul_sum] <;>
      apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hleftPoint),
    integral_congr_ae (Filter.Eventually.of_forall hrightPoint)]
  rw [integral_add
      (integrable_double_fintype_sum _ hLRe)
      (integrable_double_fintype_sum _ hLIm),
    integral_add
      (integrable_double_fintype_sum _ hRRe)
      (integrable_double_fintype_sum _ hRIm),
    integral_double_fintype_sum _ hLRe,
    integral_double_fintype_sum _ hLIm,
    integral_double_fintype_sum _ hRRe,
    integral_double_fintype_sum _ hRIm]
  congr 1 <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _
  · exact hscoreRe i j
  · exact hscoreIm i j

end Wishart

end

end LogdetLean.GramHafnian
