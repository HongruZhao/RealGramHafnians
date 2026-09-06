import LogdetLean.Coherence.StableMatchingBlockTransform
import LogdetLean.Coherence.StableMatchingLogdetDecomposition
import Mathlib.Tactic
/-!
# Exact alternative log-determinant coupling for a block matching

The alternative columns are obtained from iid Gaussian base columns by the
explicit block-triangular matching transform.  This file records the actual
matrix statistic and its exact finite-sample decomposition.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A strict correlated second column cannot vanish when its two base
columns are linearly independent. -/
theorem correlatedSecondColumn_ne_zero_of_pair_linearIndependent
    (rho : ℝ) (x e : E) (hrho : |rho| < 1)
    (hli : LinearIndependent ℝ (fun i : Fin 2 ↦ if i = 0 then x else e)) :
    correlatedSecondColumn rho x e ≠ 0 := by
  have hgap : 0 < 1 - rho ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one rho).2 hrho)
  have hsqrt : 0 < Real.sqrt (1 - rho ^ 2) := Real.sqrt_pos.2 hgap
  intro hy
  have heq : Real.sqrt (1 - rho ^ 2) • e = (-rho) • x := by
    unfold correlatedSecondColumn at hy
    have := eq_neg_of_add_eq_zero_right hy
    simpa using this
  have hind := hli.eq_of_smul_apply_eq_smul_apply
    (Real.sqrt (1 - rho ^ 2)) (-rho)
    (1 : Fin 2) (0 : Fin 2) hsqrt.ne'
  have : (1 : Fin 2) = 0 := by
    apply hind
    simpa using heq
  norm_num at this

/-- Correlated residual columns on the common iid Gaussian base space. -/
def stableMatchingAlternativeColumns
    (s r : ℕ) (rho : Fin s → ℝ)
    (w : StableMatchingBaseSample E s r) :
    Sum (Fin 2 × Fin s) (Fin r) → E :=
  mixColumnFamily (matchingMixMatrix s r rho)
    (stableMatchingRawColumns (E := E) s r w)

theorem measurable_stableMatchingAlternativeColumns
    (s r : ℕ) (rho : Fin s → ℝ) :
    Measurable (stableMatchingAlternativeColumns (E := E) s r rho) := by
  unfold stableMatchingAlternativeColumns mixColumnFamily
  refine measurable_pi_lambda _ fun j ↦ ?_
  apply Finset.measurable_sum
  intro i _hi
  exact measurable_const.smul
    ((measurable_pi_apply i).comp (measurable_stableMatchingRawColumns s r))

/-- Actual log determinant under the matching alternative. -/
def stableMatchingAlternativeLogdet
    (s r : ℕ) (rho : Fin s → ℝ)
    (w : StableMatchingBaseSample E s r) : ℝ :=
  Real.log (normalizedGram
    (stableMatchingAlternativeColumns s r rho w)).det

theorem measurable_stableMatchingAlternativeLogdet
    (s r : ℕ) (rho : Fin s → ℝ) :
    Measurable (stableMatchingAlternativeLogdet (E := E) s r rho) := by
  unfold stableMatchingAlternativeLogdet
  exact ((measurable_det_normalizedGram_stableMatchingIndex
    (E := E) s r).log).comp
      (measurable_stableMatchingAlternativeColumns s r rho)

/-- Sum of the random radius corrections appearing in the exact determinant
identity. -/
def stableMatchingDirectRadiusCorrection
    (s : ℕ) (rho : Fin s → ℝ) (v : Fin s → E × E) : ℝ :=
  ∑ e, (Real.log (‖(v e).2‖ ^ 2) -
    Real.log (‖correlatedSecondColumn (rho e) (v e).1 (v e).2‖ ^ 2))

theorem measurable_stableMatchingDirectRadiusCorrection
    (s : ℕ) (rho : Fin s → ℝ) :
    Measurable (stableMatchingDirectRadiusCorrection (E := E) s rho) := by
  unfold stableMatchingDirectRadiusCorrection
  apply Finset.measurable_sum
  intro e _he
  unfold correlatedSecondColumn
  fun_prop

/-- Every transformed column is nonzero on the full-rank base event. -/
theorem stableMatchingAlternativeColumns_ne_zero
    (s r : ℕ) (rho : Fin s → ℝ) (hrho : ∀ e, |rho e| < 1)
    (w : StableMatchingBaseSample E s r)
    (hw : LinearIndependent ℝ (stableMatchingRawColumns (E := E) s r w)) :
    ∀ i, stableMatchingAlternativeColumns s r rho w i ≠ 0 := by
  intro i
  rcases i with ⟨i, e⟩ | j
  · fin_cases i
    · simpa [stableMatchingAlternativeColumns] using
        hw.ne_zero (Sum.inl (0, e))
    · simpa [stableMatchingAlternativeColumns] using
        correlatedSecondColumn_ne_zero_of_pair_linearIndependent
        (rho e) _ _ (hrho e)
        (stableMatching_pair_linearIndependent s r
          (stableMatchingRawColumns s r w) hw e)
  · rw [stableMatchingAlternativeColumns,
      mixColumnFamily_matchingMixMatrix_singleton]
    exact hw.ne_zero (Sum.inr j)

/-- Exact finite-sample determinant decomposition on the full-rank event. -/
theorem stableMatchingAlternativeLogdet_sub_null
    (s r : ℕ) (rho : Fin s → ℝ) (hrho : ∀ e, |rho e| < 1)
    (w : StableMatchingBaseSample E s r)
    (hw : LinearIndependent ℝ (stableMatchingRawColumns (E := E) s r w)) :
    stableMatchingAlternativeLogdet s r rho w -
        stableMatchingNullLogdet s r w =
      (∑ e, Real.log (1 - rho e ^ 2)) +
        stableMatchingDirectRadiusCorrection s rho w.1 := by
  let v := stableMatchingRawColumns (E := E) s r w
  have hv : ∀ i, v i ≠ 0 := fun i ↦ hw.ne_zero i
  have hTv : ∀ i,
      mixColumnFamily (matchingMixMatrix s r rho) v i ≠ 0 := by
    simpa [v, stableMatchingAlternativeColumns] using
      stableMatchingAlternativeColumns_ne_zero
        (E := E) s r rho hrho w hw
  have hdet : 0 < (normalizedGram v).det :=
    det_normalizedGram_pos_of_linearIndependent_finite v hw
  simpa [stableMatchingAlternativeLogdet, stableMatchingNullLogdet,
    stableMatchingAlternativeColumns, stableMatchingDirectRadiusCorrection,
    v, stableMatchingRawColumns] using
      logdet_normalizedGram_matchingMix_sub
        (E := E) s r rho v hrho hv hTv hdet

/-- Sign convention used by the testing theorem: large positive values are
evidence against the identity correlation matrix. -/
def stableMatchingAlternativeZ
    (m s r : ℕ) (rho : Fin s → ℝ)
    (w : StableMatchingBaseSample E s r) : ℝ :=
  -(stableMatchingAlternativeLogdet s r rho w -
      nullCenter m (2 * s + r)) /
    Real.sqrt (nullVSeries m (2 * s + r))

theorem measurable_stableMatchingAlternativeZ
    (m s r : ℕ) (rho : Fin s → ℝ) :
    Measurable (stableMatchingAlternativeZ (E := E) m s r rho) := by
  unfold stableMatchingAlternativeZ
  exact ((measurable_stableMatchingAlternativeLogdet s r rho).sub
    measurable_const).neg.div measurable_const

/-- Exact decomposition of the testing statistic into a reflected null
coordinate, the deterministic population shift, and the random radial
correction. -/
theorem stableMatchingAlternativeZ_eq
    (m s r : ℕ) (rho : Fin s → ℝ) (hrho : ∀ e, |rho e| < 1)
    (w : StableMatchingBaseSample E s r)
    (hw : LinearIndependent ℝ (stableMatchingRawColumns (E := E) s r w)) :
    stableMatchingAlternativeZ m s r rho w =
      -stableMatchingNullZ0 m s r w -
        (∑ e, Real.log (1 - rho e ^ 2)) /
          Real.sqrt (nullVSeries m (2 * s + r)) -
        stableMatchingDirectRadiusCorrection s rho w.1 /
          Real.sqrt (nullVSeries m (2 * s + r)) := by
  have h := stableMatchingAlternativeLogdet_sub_null
    (E := E) s r rho hrho w hw
  unfold stableMatchingAlternativeZ stableMatchingNullZ0
  rw [show stableMatchingAlternativeLogdet s r rho w =
      stableMatchingNullLogdet s r w +
        ((∑ e, Real.log (1 - rho e ^ 2)) +
          stableMatchingDirectRadiusCorrection s rho w.1) by linarith]
  ring

end

end LogdetLean.Coherence
