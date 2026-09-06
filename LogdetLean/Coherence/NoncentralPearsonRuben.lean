import LogdetLean.Coherence.RubenCoordinates
import Mathlib.Tactic
/-!
# Exact Ruben identity for noncentral Gaussian Pearson correlation

`RubenCoordinates` proves the exact independent chi--normal--Gamma product
law.  This file supplies the deterministic bridge from those coordinates to
the studentized sample-correlation statistic under a nonzero population
correlation.  No moderate-deviation approximation is assumed.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The canonical second Gaussian column with population correlation `rho`. -/
def correlatedSecondColumn (rho : ℝ) (x e : E) : E :=
  rho • x + Real.sqrt (1 - rho ^ 2) • e

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_correlatedSecondColumn (rho : ℝ) (x e : E) :
    inner ℝ x (correlatedSecondColumn rho x e) =
      rho * ‖x‖ ^ 2 + Real.sqrt (1 - rho ^ 2) * inner ℝ x e := by
  unfold correlatedSecondColumn
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normSq_correlatedSecondColumn_expansion (rho : ℝ) (x e : E) :
    ‖correlatedSecondColumn rho x e‖ ^ 2 =
      rho ^ 2 * ‖x‖ ^ 2 +
        2 * rho * Real.sqrt (1 - rho ^ 2) * inner ℝ x e +
        (Real.sqrt (1 - rho ^ 2)) ^ 2 * ‖e‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  unfold correlatedSecondColumn
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm e x]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_eq_norm_mul_gaussianAxisCoordinate
    (x e : E) (hx : x ≠ 0) :
    inner ℝ x e = ‖x‖ * gaussianAxisCoordinate x e := by
  unfold gaussianAxisCoordinate
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hnorm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normSq_correlatedSecondColumn_ruben
    (rho : ℝ) (x e : E) (hx : x ≠ 0) :
    ‖correlatedSecondColumn rho x e‖ ^ 2 =
      (rho * ‖x‖ + Real.sqrt (1 - rho ^ 2) *
          gaussianAxisCoordinate x e) ^ 2 +
        (Real.sqrt (1 - rho ^ 2)) ^ 2 *
          gaussianAxisResidualEnergy x e := by
  rw [normSq_correlatedSecondColumn_expansion,
    inner_eq_norm_mul_gaussianAxisCoordinate x e hx]
  unfold gaussianAxisResidualEnergy
  ring

/-- The determinant of the two-column Gram matrix. -/
def twoColumnGramDet (u v : E) : ℝ :=
  ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem twoColumnGramDet_correlatedSecondColumn
    (rho : ℝ) (x e : E) (hx : x ≠ 0) :
    twoColumnGramDet x (correlatedSecondColumn rho x e) =
      ‖x‖ ^ 2 * (Real.sqrt (1 - rho ^ 2)) ^ 2 *
        gaussianAxisResidualEnergy x e := by
  unfold twoColumnGramDet
  rw [normSq_correlatedSecondColumn_ruben rho x e hx,
    inner_correlatedSecondColumn,
    inner_eq_norm_mul_gaussianAxisCoordinate x e hx]
  ring

/-- Square of the usual Pearson `t` statistic when the residual vector
dimension is `m` (equivalently, the original sample size is `m+1`). -/
def squaredPearsonT (m : ℕ) (u v : E) : ℝ :=
  ((m - 1 : ℕ) : ℝ) * inner ℝ u v ^ 2 / twoColumnGramDet u v

/-- Population odds parameter in Ruben's representation. -/
def populationCorrelationOdds (rho : ℝ) : ℝ :=
  rho / Real.sqrt (1 - rho ^ 2)

/-- The exact chi-mixed noncentral representation, written in the three
coordinates whose product law is proved in `RubenCoordinates`. -/
def squaredRubenT (m : ℕ) (rho : ℝ) (x e : E) : ℝ :=
  ((m - 1 : ℕ) : ℝ) *
    (gaussianAxisCoordinate x e + populationCorrelationOdds rho * ‖x‖) ^ 2 /
      gaussianAxisResidualEnergy x e

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Exact pointwise squared Ruben identity.  It is valid without excluding a
zero residual energy because Lean's division is totalized; only the first
column and the population gap must be nonzero. -/
theorem squaredPearsonT_correlatedSecondColumn_eq_squaredRubenT
    (m : ℕ) (rho : ℝ) (x e : E)
    (hrho : |rho| < 1) (hx : x ≠ 0) :
    squaredPearsonT m x (correlatedSecondColumn rho x e) =
      squaredRubenT m rho x e := by
  have hrhoSq : rho ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one rho).2 hrho
  have hgap : 0 < 1 - rho ^ 2 := sub_pos.mpr hrhoSq
  have hsqrt : 0 < Real.sqrt (1 - rho ^ 2) := Real.sqrt_pos.2 hgap
  have hsqrt0 : Real.sqrt (1 - rho ^ 2) ≠ 0 := hsqrt.ne'
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hinner :
      inner ℝ x (correlatedSecondColumn rho x e) =
        ‖x‖ * Real.sqrt (1 - rho ^ 2) *
          (gaussianAxisCoordinate x e +
            populationCorrelationOdds rho * ‖x‖) := by
    rw [inner_correlatedSecondColumn,
      inner_eq_norm_mul_gaussianAxisCoordinate x e hx]
    unfold populationCorrelationOdds
    field_simp [hsqrt0]
    ring
  rw [squaredPearsonT, squaredRubenT, hinner,
    twoColumnGramDet_correlatedSecondColumn rho x e hx]
  by_cases hB : gaussianAxisResidualEnergy x e = 0
  · simp [hB]
  · field_simp [hnorm, hsqrt0, hB]

/-! ## Exact law-level Ruben reduction -/

/-- The squared Pearson `t` statistic evaluated on the canonical correlated
Gaussian pair generated by `(x,e)`. -/
def correlatedSquaredPearsonT (m : ℕ) (rho : ℝ) (z : E × E) : ℝ :=
  squaredPearsonT m z.1 (correlatedSecondColumn rho z.1 z.2)

/-- The deterministic squared Ruben statistic on the independent coordinate
triple `(A,Z,B²)`. -/
def squaredRubenCoordinateStatistic (m : ℕ) (rho : ℝ)
    (w : ℝ × (ℝ × ℝ)) : ℝ :=
  ((m - 1 : ℕ) : ℝ) *
    (w.2.1 + populationCorrelationOdds rho * w.1) ^ 2 / w.2.2

theorem measurable_correlatedSquaredPearsonT (m : ℕ) (rho : ℝ) :
    Measurable (correlatedSquaredPearsonT (E := E) m rho) := by
  unfold correlatedSquaredPearsonT squaredPearsonT twoColumnGramDet
    correlatedSecondColumn
  fun_prop

theorem measurable_squaredRubenCoordinateStatistic (m : ℕ) (rho : ℝ) :
    Measurable (squaredRubenCoordinateStatistic m rho) := by
  unfold squaredRubenCoordinateStatistic populationCorrelationOdds
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `squaredRubenT` factors exactly through the three Ruben coordinates. -/
theorem squaredRubenT_eq_squaredRubenCoordinateStatistic
    (m : ℕ) (rho : ℝ) (x e : E) :
    squaredRubenT m rho x e =
      squaredRubenCoordinateStatistic m rho
        (gaussianRubenCoordinates (x, e)) := by
  rfl

/-- Exact finite-sample pushforward law of the squared Pearson `t` statistic
under the canonical correlated Gaussian construction.  The law is the image
of the mutually independent chi--normal--Gamma Ruben product under the
deterministic squared-Ruben statistic.  No asymptotic approximation enters
this identity. -/
theorem map_correlatedSquaredPearsonT_gaussianProduct_eq_rubenProduct
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) :
    Measure.map (correlatedSquaredPearsonT (E := E) m rho)
        ((stdGaussian E).prod (stdGaussian E)) =
      Measure.map (squaredRubenCoordinateStatistic m rho)
        ((chiMeasure m).prod
          ((gaussianReal 0 1).prod
            (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))) := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  have hnonzero : ∀ᵐ z ∂((stdGaussian E).prod (stdGaussian E)), z.1 ≠ 0 := by
    exact (Measure.quasiMeasurePreserving_fst
      (μ := stdGaussian E) (ν := stdGaussian E)).ae
        (p := fun x : E ↦ x ≠ 0)
        (by simpa [ae_iff] using stdGaussian_zero_singleton (E := E))
  have hfactor :
      correlatedSquaredPearsonT (E := E) m rho =ᵐ[
        (stdGaussian E).prod (stdGaussian E)]
        squaredRubenCoordinateStatistic m rho ∘
          gaussianRubenCoordinates (E := E) := by
    filter_upwards [hnonzero] with z hz
    exact (squaredPearsonT_correlatedSecondColumn_eq_squaredRubenT
      m rho z.1 z.2 hrho hz).trans
        (squaredRubenT_eq_squaredRubenCoordinateStatistic
          m rho z.1 z.2)
  calc
    Measure.map (correlatedSquaredPearsonT (E := E) m rho)
        ((stdGaussian E).prod (stdGaussian E)) =
        Measure.map
          (squaredRubenCoordinateStatistic m rho ∘
            gaussianRubenCoordinates (E := E))
          ((stdGaussian E).prod (stdGaussian E)) :=
      Measure.map_congr hfactor
    _ = Measure.map (squaredRubenCoordinateStatistic m rho)
        (Measure.map (gaussianRubenCoordinates (E := E))
          ((stdGaussian E).prod (stdGaussian E))) := by
      exact (Measure.map_map
        (measurable_squaredRubenCoordinateStatistic m rho)
        measurable_gaussianRubenCoordinates).symm
    _ = Measure.map (squaredRubenCoordinateStatistic m rho)
        ((chiMeasure m).prod
          ((gaussianReal 0 1).prod
            (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))) := by
      rw [map_gaussianRubenCoordinates_gaussianProduct m hdim hm]

/-- `HasLaw` packaging of the exact finite-sample noncentral squared-Pearson
Ruben reduction. -/
theorem hasLaw_correlatedSquaredPearsonT_rubenProduct
    (m : ℕ) (hdim : finrank ℝ E = m) (hm : 2 ≤ m)
    (rho : ℝ) (hrho : |rho| < 1) :
    HasLaw (correlatedSquaredPearsonT (E := E) m rho)
      (Measure.map (squaredRubenCoordinateStatistic m rho)
        ((chiMeasure m).prod
          ((gaussianReal 0 1).prod
            (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (1 / 2)))))
      ((stdGaussian E).prod (stdGaussian E)) := by
  exact ⟨(measurable_correlatedSquaredPearsonT m rho).aemeasurable,
    map_correlatedSquaredPearsonT_gaussianProduct_eq_rubenProduct
      m hdim hm rho hrho⟩

end

end LogdetLean.Coherence
