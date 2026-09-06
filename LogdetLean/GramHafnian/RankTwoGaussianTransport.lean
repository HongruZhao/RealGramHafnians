import LogdetLean.GramHafnian.RankOneGaussianBilinear
import LogdetLean.GramHafnian.RankTwoOrthogonalInvariance
/-!
# Coordinate transport for the rank-two Gaussian outer integral

The literal Gram-hafnian construction uses four iid coordinate fields
`Fin k → ℝ`.  The rank-two conditional and radial--angle theorems are most
naturally stated in `EuclideanSpace ℝ (Fin k)`.  This module proves that the
two formulations are exactly the same pushforward integral.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- Apply the canonical `L²` wrapper to each of four real coordinate fields. -/
def fourRealFieldsToEuclidean (k : ℕ) :
    FourRealFields k →
      ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) ×
        ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) :=
  Prod.map
    (Prod.map (WithLp.toLp 2) (WithLp.toLp 2))
    (Prod.map (WithLp.toLp 2) (WithLp.toLp 2))

theorem measurable_fourRealFieldsToEuclidean (k : ℕ) :
    Measurable (fourRealFieldsToEuclidean k) := by
  unfold fourRealFieldsToEuclidean
  fun_prop

/-- Four iid coordinate Gaussian fields push forward to two independent
pairs of standard Euclidean Gaussians. -/
theorem map_fourRealFieldsToEuclidean_eq_prod_prod_stdGaussian (k : ℕ) :
    Measure.map (fourRealFieldsToEuclidean k)
        (fourRealGaussianFieldsMeasure k) =
      ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin k)))).prod
        ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
  let T : TwoRealFields k →
      (EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k)) :=
    Prod.map (WithLp.toLp 2) (WithLp.toLp 2)
  have hprod := (Measure.map_prod_map
    (twoRealGaussianFieldsMeasure k)
    (twoRealGaussianFieldsMeasure k)
    (by fun_prop : Measurable T)
    (by fun_prop : Measurable T)).symm
  have htwo := map_twoRealFields_toLp_eq_prod_stdGaussian k
  simpa only [fourRealFieldsToEuclidean, fourRealGaussianFieldsMeasure, T,
    htwo] using hprod

/-- The coordinate rank-two bilinear form is exactly its Euclidean
inner-product formulation. -/
theorem innerRankTwoBilinear_fourRealFieldsToEuclidean
    {k : ℕ} (w : FourRealFields k) :
    innerRankTwoBilinear
        (WithLp.toLp 2 w.1.1) (WithLp.toLp 2 w.1.2)
        (WithLp.toLp 2 w.2.1, WithLp.toLp 2 w.2.2) =
      rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 := by
  unfold innerRankTwoBilinear rankTwoBilinear
  rw [inner_toLp_eq_bilinearDot, inner_toLp_eq_bilinearDot,
    inner_toLp_eq_bilinearDot, inner_toLp_eq_bilinearDot]

/-- **Literal coordinate-to-Euclidean rank-two integral bridge.** -/
theorem integral_rankTwoBilinear_fourRealFields_eq_euclidean
    (k n : ℕ) :
    (∫ w : FourRealFields k,
        rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 ^ (2 * n)
          ∂fourRealGaussianFieldsMeasure k) =
      ∫ z :
          ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) ×
            ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))),
        innerRankTwoBilinear z.1.1 z.1.2 z.2 ^ (2 * n)
          ∂(((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
              (stdGaussian (EuclideanSpace ℝ (Fin k)))).prod
            ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
              (stdGaussian (EuclideanSpace ℝ (Fin k))))) := by
  let T := fourRealFieldsToEuclidean k
  let μ := fourRealGaussianFieldsMeasure k
  let ν := ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin k)))).prod
    ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin k))))
  have hmap : Measure.map T μ = ν := by
    simpa only [T, μ, ν] using
      map_fourRealFieldsToEuclidean_eq_prod_prod_stdGaussian k
  calc
    (∫ w : FourRealFields k,
        rankTwoBilinear w.1.1 w.1.2 w.2.1 w.2.2 ^ (2 * n) ∂μ) =
        ∫ w : FourRealFields k,
          innerRankTwoBilinear
            (WithLp.toLp 2 w.1.1) (WithLp.toLp 2 w.1.2)
            (WithLp.toLp 2 w.2.1, WithLp.toLp 2 w.2.2) ^ (2 * n) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦
        congrArg (fun x : ℝ ↦ x ^ (2 * n))
          (innerRankTwoBilinear_fourRealFieldsToEuclidean w).symm
    _ = ∫ z :
          ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) ×
            ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))),
          innerRankTwoBilinear z.1.1 z.1.2 z.2 ^ (2 * n)
            ∂Measure.map T μ := by
      have hf : StronglyMeasurable (fun z :
          ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) ×
            ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) ↦
          innerRankTwoBilinear z.1.1 z.1.2 z.2 ^ (2 * n)) := by
        unfold innerRankTwoBilinear
        fun_prop
      rw [integral_map
        (measurable_fourRealFieldsToEuclidean k).aemeasurable
        hf.aestronglyMeasurable]
      rfl
    _ = ∫ z :
          ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))) ×
            ((EuclideanSpace ℝ (Fin k)) × (EuclideanSpace ℝ (Fin k))),
          innerRankTwoBilinear z.1.1 z.1.2 z.2 ^ (2 * n) ∂ν := by
      rw [hmap]

end

end LogdetLean.GramHafnian
