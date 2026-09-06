import RealGramHafnians.Proofs.ReviewEnlargedFinite
import RealGramHafnians.Proofs.SharpRealSymmetricGaussian
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Real ENNReal Nat Topology
namespace LogdetLean.GramHafnian.Review
noncomputable section
set_option maxHeartbeats 1000000

/-- The revised finite envelope uses the proved three-eighths estimate. -/
theorem paperEquation_elementary_B
    {n k : ℕ} (hn : 1 ≤ n) (hkn : n + 2 ≤ k) :
    sharpRealSmallBallCoefficientB n k ≤
      (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) *
        Real.exp ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (4 * ((k - n - 1 : ℕ) : ℝ))) := by
  have hsym : realGaussianIntervalPrefactor 1 * realElementaryKn n =
      sharpRealSymmetricSmallBallCoefficient n := by
    rw [realGaussianIntervalPrefactor_eq_sqrt_two_div_pi_mul,
      sharpRealSymmetricSmallBallCoefficient_eq_product hn,
      realElementaryKn_eq_doubleFactorial_gammaProduct hn]
    ring
  rw [sharpRealSmallBallCoefficientB,
    sharpRealNormalizedCoefficientReal_factorization hn,
    sqrt_dimension_mul_physical_gamma_eq_paired (by omega : n ≤ k), hsym]
  have hD := sharpRealDimensionGammaProductReal_le_exp_sharp hkn
  have hDn : 0 ≤ sharpRealDimensionGammaProductReal n k := by
    unfold sharpRealDimensionGammaProductReal
    apply Finset.prod_nonneg
    intro q hq
    exact mul_nonneg (Real.sqrt_nonneg _) (realAuxiliaryGammaHalfFactorReal_nonneg
      (by have := Finset.mem_range.mp hq; omega))
  exact mul_le_mul (sharpRealSymmetricSmallBallCoefficient_threeEighth_twoSided hn).2
    hD hDn (by positivity)

/-- Literal enlarged density statement, including its attained supremum. -/
theorem paperEquation_density_bound
    {n k : ℕ} (hn : 1 ≤ n) (hdim : n + 1 ≤ k) :
    sSup (Set.range (sharpRealGramHafnianDensity n k hn)) =
        sharpRealGramHafnianDensity n k hn 0 ∧
      sharpRealGramHafnianDensity n k hn 0 ≤
        sharpRealSmallBallCoefficientB n k / (2 * realGramHafnianRMS n k) := by
  refine ⟨sSup_range_sharpRealGramHafnianDensity_eq_zero hn (by omega) hdim, ?_⟩
  have hs : realGramHafnianRMS n k ≠ 0 :=
    ne_of_gt (realGramHafnianRMS_pos n k (by omega))
  have heq : sharpRealSmallBallCoefficientB n k / (2 * realGramHafnianRMS n k) =
      (Real.sqrt (2 * Real.pi))⁻¹ * sharpRealGammaCoefficientReal n k := by
    unfold sharpRealSmallBallCoefficientB realGaussianIntervalPrefactor
    field_simp [hs]
  rw [heq]
  exact sharpRealGramHafnianDensity_zero_le_coefficientReal hn (by omega) hdim

/-- Complete revised Theorem 2.1; the legacy certificate remains a component
so all literal observables, measures, density properties, and normalization
are retained, and the new elementary bound is an additional proved clause. -/
theorem paperTheorem_main_revised
    {n k : ℕ} (hn : 1 ≤ n) (hdim : n + 1 ≤ k) :
    PaperTheorem2_1Certificate n k hn ∧
      (n + 2 ≤ k → sharpRealSmallBallCoefficientB n k ≤
        (2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) *
          Real.exp ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((k - n - 1 : ℕ) : ℝ)))) := by
  exact ⟨paperTheorem2_1_density_and_exact_shifted_anticoncentration hn (by omega) hdim,
    paperEquation_elementary_B hn⟩

theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_exp_sharp
    {n k : ℕ} (hn : 1 ≤ n) (_hk : 2 ≤ k) (hdim : n + 1 ≤ k)
    (hkn : n + 2 ≤ k) (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤ epsilon * realGramHafnianRMS n k} ≤
      ENNReal.ofReal ((2 / Real.sqrt Real.pi) * (n : ℝ) ^ (3 / 8 : ℝ) *
        Real.exp ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (4 * ((k - n - 1 : ℕ) : ℝ)))) * ENNReal.ofReal epsilon := by
  have h := standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
    hn (by omega) hdim z epsilon hepsilon
  rw [sharpRealNormalizedCoefficient_eq_ofReal_coefficientB hn (by omega) hdim] at h
  apply h.trans
  gcongr
  exact paperEquation_elementary_B hn hkn

theorem paperSymmetric_interval_threeEighth
    (n : ℕ) (hn : 1 ≤ n) (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (SymmetricGaussianHafnian.realEdgeGaussian (Fin (2 * n)))
      {x | |SymmetricGaussianHafnian.realEdgeHafnian x - z| ≤
        epsilon * sharpRealSymmetricHafnianRMS n} ≤
      min 1 (ENNReal.ofReal ((2 / Real.sqrt Real.pi) *
        (n : ℝ) ^ (3 / 8 : ℝ) * epsilon)) := by
  apply (sharpRealSymmetricGaussian_shiftedSmallBall n hn z epsilon hepsilon).trans
  exact min_le_min le_rfl (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (sharpRealSymmetricSmallBallCoefficient_threeEighth_twoSided hn).2 hepsilon))

end
end LogdetLean.GramHafnian.Review
