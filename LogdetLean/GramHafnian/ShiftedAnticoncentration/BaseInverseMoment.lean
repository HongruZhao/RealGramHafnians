import LogdetLean.GramHafnian.ShiftedAnticoncentration.LastColumnProduct
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianNormGamma
/-!
# The first cofactor-energy inverse moment

At level one the odd cofactor vector has one coordinate, equal to the empty
hafnian `1`.  Thus its column combination is a single iid circular Gaussian
column, and the inverse energy is exactly `1/(k-1)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

instance uniqueOddCofactorIndexOne :
    Unique (OddCofactorIndex 1 (by omega)) where
  default := ⟨0, by
    intro h
    have hv := congrArg Fin.val h
    simp [evenLastIndex] at hv⟩
  uniq j := by
    apply Subtype.ext
    apply Fin.ext
    have hjlt : j.1 < evenLastIndex 1 (by omega) :=
      lt_evenLastIndex (by omega) j.1 j.2
    change j.1.1 < 1 at hjlt
    change j.1.1 = 0
    omega

/-- The first past cofactor combination is evaluation at the unique past
column. -/
theorem pastCofactorCombination_level_one {k : ℕ}
    (A : OddCofactorIndex 1 (by omega) -> (Fin k -> ℂ)) :
    pastCofactorCombination (by omega) A = A default := by
  funext a
  unfold pastCofactorCombination oddCofactorColumnCombination
  simp_rw [oddHafnianCofactorVector_level_one]
  simp [pastCofactorMatrix, lastColumnProductEquiv_apply_nonlast]

/-- Coordinate identification of the first cofactor energy with the squared
Euclidean norm of the unique past column. -/
theorem pastCofactorV_level_one {k : ℕ}
    (A : OddCofactorIndex 1 (by omega) -> (Fin k -> ℂ)) :
    pastCofactorV (by omega) A =
      circularVectorNormSq (WithLp.toLp 2 (A default)) := by
  rw [pastCofactorV_eq_coefficientEnergy,
    pastCofactorCombination_level_one]
  unfold circularCoefficientEnergy circularVectorNormSq
  rw [EuclideanSpace.norm_sq_eq]

/-- Exact extended-nonnegative inverse moment at the base of the hafnian
cofactor recurrence. -/
theorem ennInverseMoment_pastCofactorV_level_one
    {k : ℕ} (hk : 2 ≤ k) :
    ennInverseMoment
        (Measure.pi fun _ : OddCofactorIndex 1 (by omega) =>
          circularGaussianVector k)
        (pastCofactorV (k := k) (by omega)) =
      ENNReal.ofReal (((k : ℝ) - 1)⁻¹) := by
  let I := OddCofactorIndex 1 (by omega)
  let raw : Measure (Fin k -> ℂ) := circularGaussianVector k
  have he : MeasurePreserving (fun A : I -> (Fin k -> ℂ) => A default)
      (Measure.pi fun _ : I => raw) raw := by
    exact measurePreserving_funUnique raw I
  have hmeas : Measurable
      (fun x : Fin k -> ℂ =>
        ENNReal.ofReal
          (circularVectorNormSq (WithLp.toLp 2 x))⁻¹) := by
    fun_prop
  calc
    ennInverseMoment (Measure.pi fun _ : I => raw)
        (pastCofactorV (k := k) (by omega)) =
        ∫⁻ A : I -> (Fin k -> ℂ),
          ENNReal.ofReal
            (circularVectorNormSq (WithLp.toLp 2 (A default)))⁻¹
          ∂Measure.pi fun _ : I => raw := by
      unfold ennInverseMoment
      apply lintegral_congr
      intro A
      rw [pastCofactorV_level_one]
    _ = ∫⁻ x : Fin k -> ℂ,
          ENNReal.ofReal
            (circularVectorNormSq (WithLp.toLp 2 x))⁻¹ ∂raw := by
      exact he.lintegral_comp hmeas
    _ = ∫⁻ x : CircularEuclideanSpace k,
          ENNReal.ofReal (circularVectorNormSq x)⁻¹
          ∂raw.map (WithLp.toLp 2) := by
      rw [lintegral_map (by fun_prop) (by fun_prop)]
    _ = ENNReal.ofReal (((k : ℝ) - 1)⁻¹) := by
      simpa [raw, circularGaussianVector] using
        lintegral_ofReal_inv_circularVectorNormSq_iid_circular hk

end

end LogdetLean.GramHafnian
