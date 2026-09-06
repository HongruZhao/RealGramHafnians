import RealGramHafnians.Proofs.SharpRealSymmetricGaussian
import RealGramHafnians.Proofs.SharpRealCoefficientLiteral
/-!
# Fixed-degree limits of the sharp real Gram coefficient

This file proves the deterministic limits used when the number of real
Gaussian rows tends to infinity while the hafnian degree stays fixed.  In
particular, the finite Gram small-ball coefficient converges to the exact
independent-edge real symmetric Gaussian coefficient.
-/

open Filter
open scoped BigOperators Real ENNReal Nat Topology

namespace LogdetLean.GramHafnian

noncomputable section

open LogdetLean.Coherence

/-- The elementary half-step Gamma factor tends to one along the positive
integers. -/
theorem tendsto_realElementaryBk_atTop :
    Tendsto realElementaryBk atTop (nhds 1) := by
  have hpred : Tendsto (fun k : ℕ ↦ k - 1) atTop atTop :=
    Filter.tendsto_sub_atTop_nat 1
  have hscale0 := tendsto_gammaHalfRatioScale_nat_half.comp hpred
  have hscale : Tendsto
      (fun k : ℕ ↦ gammaHalfRatioScale (((k : ℝ) - 1) / 2))
      atTop (nhds 1) := by
    refine hscale0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    simp only [Function.comp_apply]
    rw [Nat.cast_sub hk]
    norm_num
  have hpredR : Tendsto (fun k : ℕ ↦ ((k - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpred
  have hinv : Tendsto (fun k : ℕ ↦ 1 / ((k - 1 : ℕ) : ℝ))
      atTop (nhds 0) := hpredR.const_div_atTop 1
  have hratioNat : Tendsto
      (fun k : ℕ ↦ (k : ℝ) / ((k - 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _k : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).add hinv
    have h' : Tendsto
        (fun k : ℕ ↦ (k : ℝ) / ((k - 1 : ℕ) : ℝ))
        atTop (nhds ((1 : ℝ) + 0)) := by
      apply h.congr'
      filter_upwards [eventually_ge_atTop 2] with k hk
      have hden : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show k - 1 ≠ 0 by omega)
      have hkcast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        push_cast
        ring
      rw [hkcast]
      field_simp [hden]
    simpa using h'
  have hratio : Tendsto
      (fun k : ℕ ↦ (k : ℝ) / ((k : ℝ) - 1))
      atTop (nhds 1) := by
    apply hratioNat.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    simp only [Nat.cast_sub hk, Nat.cast_one]
  have hsqrt : Tendsto
      (fun k : ℕ ↦ Real.sqrt ((k : ℝ) / ((k : ℝ) - 1)))
      atTop (nhds 1) := by
    simpa using hratio.sqrt
  have hprod := hsqrt.mul hscale
  have h' : Tendsto realElementaryBk atTop (nhds ((1 : ℝ) * 1)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (realElementaryBk_eq_gammaHalfRatioScale hk).symm
  simpa using h'

/-- For each fixed edge-coordinate index, the corresponding paired RMS and
Gamma factor converges to one. -/
theorem tendsto_sharpRealDimensionGammaFactor (q : ℕ) :
    Tendsto
      (fun k : ℕ ↦
        Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
          realAuxiliaryGammaHalfFactorReal (k - q))
      atTop (nhds 1) := by
  have hsub : Tendsto (fun k : ℕ ↦ k - q) atTop atTop :=
    Filter.tendsto_sub_atTop_nat q
  have hb : Tendsto (fun k : ℕ ↦ realElementaryBk (k - q))
      atTop (nhds 1) := tendsto_realElementaryBk_atTop.comp hsub
  have hsubR : Tendsto (fun k : ℕ ↦ ((k - q : ℕ) : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hsub
  have hzero : Tendsto
      (fun k : ℕ ↦ (3 * (q : ℝ)) / ((k - q : ℕ) : ℝ))
      atTop (nhds 0) := hsubR.const_div_atTop (3 * (q : ℝ))
  have hratio : Tendsto
      (fun k : ℕ ↦
        (((k + 2 * q : ℕ) : ℝ)) / ((k - q : ℕ) : ℝ))
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _k : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).add hzero
    have h' : Tendsto
        (fun k : ℕ ↦
          (((k + 2 * q : ℕ) : ℝ)) / ((k - q : ℕ) : ℝ))
        atTop (nhds ((1 : ℝ) + 0)) := by
      apply h.congr'
      filter_upwards [eventually_ge_atTop (q + 1)] with k hk
      have hden : ((k - q : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show k - q ≠ 0 by omega)
      have hkdecomp : k + 2 * q = (k - q) + 3 * q := by omega
      rw [hkdecomp]
      push_cast
      field_simp [hden]
    simpa using h'
  have hsqrt : Tendsto
      (fun k : ℕ ↦ Real.sqrt
        ((((k + 2 * q : ℕ) : ℝ)) / ((k - q : ℕ) : ℝ)))
      atTop (nhds 1) := by
    simpa using hratio.sqrt
  have hprod := hsqrt.mul hb
  have h' : Tendsto
      (fun k : ℕ ↦
        Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
          realAuxiliaryGammaHalfFactorReal (k - q))
      atTop (nhds ((1 : ℝ) * 1)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop (q + 1)] with k hk
    have hd : 1 ≤ k - q := by omega
    rw [realAuxiliaryGammaHalfFactorReal_eq_bk_div_sqrt hd]
    rw [Real.sqrt_div (by positivity :
      0 ≤ (((k + 2 * q : ℕ) : ℝ)))]
    ring
  simpa using h'

/-- The complete fixed-degree physical Gamma/RMS correction tends to one. -/
theorem tendsto_sharpRealDimensionGammaProductReal (n : ℕ) :
    Tendsto (fun k : ℕ ↦ sharpRealDimensionGammaProductReal n k)
      atTop (nhds 1) := by
  unfold sharpRealDimensionGammaProductReal
  simpa using
    (tendsto_finsetProd (Finset.range n)
      (fun q _hq ↦ tendsto_sharpRealDimensionGammaFactor q))

/-- The product in the exact coefficient factorization tends to one. -/
theorem tendsto_sqrt_dimensionProduct_mul_physicalGamma_fixedDegree
    (n : ℕ) :
    Tendsto
      (fun k : ℕ ↦ Real.sqrt (dimensionProduct k n) *
        sharpRealPhysicalGammaProductReal n k)
      atTop (nhds 1) := by
  apply (tendsto_sharpRealDimensionGammaProductReal n).congr'
  filter_upwards [eventually_ge_atTop n] with k hk
  exact (sqrt_dimension_mul_physical_gamma_eq_paired hk).symm

/-- The square-root dimension product, normalized by `k^(n/2)`, tends to
one at each fixed degree. -/
theorem tendsto_normalized_sqrt_dimensionProduct_fixedDegree (n : ℕ) :
    Tendsto
      (fun k : ℕ ↦
        Real.sqrt (dimensionProduct k n) / (Real.sqrt (k : ℝ)) ^ n)
      atTop (nhds 1) := by
  have hfactor : ∀ q : ℕ, Tendsto
      (fun k : ℕ ↦
        Real.sqrt (((k + 2 * q : ℕ) : ℝ)) / Real.sqrt (k : ℝ))
      atTop (nhds 1) := by
    intro q
    have hzero : Tendsto (fun k : ℕ ↦ (2 * (q : ℝ)) / (k : ℝ))
        atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.const_div_atTop (2 * (q : ℝ))
    have hratio : Tendsto
        (fun k : ℕ ↦ (((k + 2 * q : ℕ) : ℝ)) / (k : ℝ))
        atTop (nhds 1) := by
      have h := (tendsto_const_nhds :
        Tendsto (fun _k : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).add hzero
      have h' : Tendsto
          (fun k : ℕ ↦ (((k + 2 * q : ℕ) : ℝ)) / (k : ℝ))
          atTop (nhds ((1 : ℝ) + 0)) := by
        apply h.congr'
        filter_upwards [eventually_ge_atTop 1] with k hk
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp [hk0]
      simpa using h'
    have hsqrt := hratio.sqrt
    have h' : Tendsto
        (fun k : ℕ ↦
          Real.sqrt (((k + 2 * q : ℕ) : ℝ)) / Real.sqrt (k : ℝ))
        atTop (nhds (Real.sqrt 1)) := by
      apply hsqrt.congr'
      filter_upwards [eventually_ge_atTop 1] with k hk
      rw [Real.sqrt_div (by positivity :
        0 ≤ (((k + 2 * q : ℕ) : ℝ)))]
    simpa using h'
  have hprod := tendsto_finsetProd (Finset.range n)
    (fun q _hq ↦ hfactor q)
  have h' : Tendsto
      (fun k : ℕ ↦
        Real.sqrt (dimensionProduct k n) / (Real.sqrt (k : ℝ)) ^ n)
      atTop (nhds (∏ _q ∈ Finset.range n, (1 : ℝ))) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    unfold dimensionProduct
    rw [Real.sqrt_prod]
    · rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    · intro q hq
      positivity
  simpa using h'

/-- The exact Gram RMS, after the central-limit normalization, converges to
the RMS of the independent-edge real symmetric Gaussian hafnian. -/
theorem tendsto_normalized_realGramHafnianRMS_fixedDegree (n : ℕ) :
    Tendsto
      (fun k : ℕ ↦
        realGramHafnianRMS n k / (Real.sqrt (k : ℝ)) ^ n)
      atTop (nhds (sharpRealSymmetricHafnianRMS n)) := by
  have hconst : Tendsto
      (fun _k : ℕ ↦ Real.sqrt (oddPairingNat n : ℝ))
      atTop (nhds (Real.sqrt (oddPairingNat n : ℝ))) := tendsto_const_nhds
  have h := hconst.mul (tendsto_normalized_sqrt_dimensionProduct_fixedDegree n)
  have h' : Tendsto
      (fun k : ℕ ↦
        realGramHafnianRMS n k / (Real.sqrt (k : ℝ)) ^ n)
      atTop (nhds (Real.sqrt (oddPairingNat n : ℝ))) := by
    have h'' : Tendsto
        (fun k : ℕ ↦
          realGramHafnianRMS n k / (Real.sqrt (k : ℝ)) ^ n)
        atTop (nhds (Real.sqrt (oddPairingNat n : ℝ) * 1)) := by
      apply h.congr'
      filter_upwards with k
      rw [realGramHafnianRMS_eq_sqrt_odd_mul_sqrt_dimension]
      ring
    simpa using h''
  simpa [sharpRealSymmetricHafnianRMS,
    SymmetricGaussianHafnian.sigma] using h'

/-- The limiting coefficient written in the finite Gram factorization agrees
exactly with the independently defined real symmetric Gaussian coefficient. -/
theorem realGaussianIntervalPrefactor_mul_realElementaryKn_eq_symmetricCoefficient
    {n : ℕ} (hn : 1 ≤ n) :
    realGaussianIntervalPrefactor 1 * realElementaryKn n =
      sharpRealSymmetricSmallBallCoefficient n := by
  rw [sharpRealSymmetricSmallBallCoefficient_eq_product hn,
    realElementaryKn_eq_doubleFactorial_gammaProduct hn,
    realGaussianIntervalPrefactor_eq_sqrt_two_div_pi_mul]
  ring

/-- At fixed hafnian degree, the exact sharp finite-Gram coefficient converges
to the exact real symmetric Gaussian hafnian coefficient. -/
theorem tendsto_sharpRealSmallBallCoefficientB_fixedDegree
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun k : ℕ ↦ sharpRealSmallBallCoefficientB n k)
      atTop (nhds (sharpRealSymmetricSmallBallCoefficient n)) := by
  have hphysical :=
    tendsto_sqrt_dimensionProduct_mul_physicalGamma_fixedDegree n
  have hconst : Tendsto
      (fun _k : ℕ ↦
        realGaussianIntervalPrefactor 1 * realElementaryKn n)
      atTop
      (nhds (realGaussianIntervalPrefactor 1 * realElementaryKn n)) :=
    tendsto_const_nhds
  have hprod := hconst.mul hphysical
  have hB : Tendsto (fun k : ℕ ↦ sharpRealSmallBallCoefficientB n k)
      atTop
      (nhds (realGaussianIntervalPrefactor 1 * realElementaryKn n)) := by
    have hB' : Tendsto
        (fun k : ℕ ↦ sharpRealSmallBallCoefficientB n k)
        atTop
        (nhds ((realGaussianIntervalPrefactor 1 * realElementaryKn n) * 1)) := by
      apply hprod.congr'
      filter_upwards [eventually_ge_atTop n] with k hk
      rw [sharpRealSmallBallCoefficientB]
      exact (sharpRealNormalizedCoefficientReal_factorization hn).symm
    simpa using hB'
  simpa [realGaussianIntervalPrefactor_mul_realElementaryKn_eq_symmetricCoefficient hn]
    using hB

end

end LogdetLean.GramHafnian
