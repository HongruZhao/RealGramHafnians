import RealGramHafnians.Proofs.SharpRealSmallBall
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGammaCoefficient
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGammaCoefficientPolynomial
/-!
# Closed products and elementary bounds for the sharp real coefficient
-/

open scoped BigOperators Real ENNReal Nat

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 5000000

def sharpRealPhysicalGammaProductReal (n k : ℕ) : ℝ :=
  ∏ d ∈ Finset.Icc (k - n + 1) k,
    realAuxiliaryGammaHalfFactorReal d

def sharpRealOddGammaProductReal (n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n,
    realAuxiliaryGammaHalfFactorReal (2 * r - 1)

def sharpRealGammaCoefficientReal (n k : ℕ) : ℝ :=
  sharpRealPhysicalGammaProductReal n k *
    sharpRealOddGammaProductReal n

def sharpRealPhysicalGammaRangeProductReal (n k : ℕ) : ℝ :=
  ∏ q ∈ Finset.range n,
    realAuxiliaryGammaHalfFactorReal (k - q)

def sharpRealDimensionGammaProductReal (n k : ℕ) : ℝ :=
  ∏ q ∈ Finset.range n,
    Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
      realAuxiliaryGammaHalfFactorReal (k - q)

theorem sharpRealPhysicalGammaProductReal_eq_range
    {n k : ℕ} (hnk : n ≤ k) :
    sharpRealPhysicalGammaProductReal n k =
      sharpRealPhysicalGammaRangeProductReal n k := by
  unfold sharpRealPhysicalGammaProductReal
    sharpRealPhysicalGammaRangeProductReal
  apply Finset.prod_bij'
      (fun d _hd ↦ k - d) (fun q _hq ↦ k - q)
  · intro d hd
    simp only [Finset.mem_range]
    have hdLower := (Finset.mem_Icc.mp hd).1
    have hdUpper := (Finset.mem_Icc.mp hd).2
    omega
  · intro q hq
    apply Finset.mem_Icc.mpr
    have hq' := Finset.mem_range.mp hq
    omega
  · intro d hd
    have hdUpper := (Finset.mem_Icc.mp hd).2
    omega
  · intro q hq
    have hq' := Finset.mem_range.mp hq
    omega
  · intro d hd
    have hdUpper := (Finset.mem_Icc.mp hd).2
    congr 1
    omega

theorem sqrt_dimension_mul_physical_gamma_eq_paired
    {n k : ℕ} (hnk : n ≤ k) :
    Real.sqrt (dimensionProduct k n) *
        sharpRealPhysicalGammaProductReal n k =
      sharpRealDimensionGammaProductReal n k := by
  rw [sharpRealPhysicalGammaProductReal_eq_range hnk]
  unfold dimensionProduct sharpRealPhysicalGammaRangeProductReal
    sharpRealDimensionGammaProductReal
  rw [Real.sqrt_prod]
  · rw [Finset.prod_mul_distrib]
  · intro q hq
    positivity

theorem sharpRealPhysicalGammaProductReal_one
    {k : ℕ} (hk : 1 ≤ k) :
    sharpRealPhysicalGammaProductReal 1 k =
      realAuxiliaryGammaHalfFactorReal k := by
  unfold sharpRealPhysicalGammaProductReal
  rw [show k - 1 + 1 = k by omega]
  simp

@[simp] theorem sharpRealOddGammaProductReal_one :
    sharpRealOddGammaProductReal 1 = 1 := by
  simp [sharpRealOddGammaProductReal]

theorem sharpRealPhysicalGammaProductReal_succ
    {n k : ℕ} (hn : 1 ≤ n) (hnk : n + 1 ≤ k) :
    sharpRealPhysicalGammaProductReal (n + 1) k =
      sharpRealPhysicalGammaProductReal n (k - 1) *
        realAuxiliaryGammaHalfFactorReal k := by
  unfold sharpRealPhysicalGammaProductReal
  have hlower : k - (n + 1) + 1 = (k - 1) - n + 1 := by omega
  rw [hlower]
  conv_lhs =>
    rw [show k = (k - 1) + 1 by omega]
  rw [Finset.prod_Icc_succ_top (by omega)]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]

theorem sharpRealOddGammaProductReal_succ
    {n : ℕ} (hn : 1 ≤ n) :
    sharpRealOddGammaProductReal (n + 1) =
      sharpRealOddGammaProductReal n *
        realAuxiliaryGammaHalfFactorReal (2 * (n + 1) - 1) := by
  unfold sharpRealOddGammaProductReal
  rw [Finset.prod_Icc_succ_top (by omega)]

theorem sharpRealGammaCoefficientReal_one
    {k : ℕ} (hk : 1 ≤ k) :
    sharpRealGammaCoefficientReal 1 k =
      realAuxiliaryGammaHalfFactorReal k := by
  rw [sharpRealGammaCoefficientReal,
    sharpRealPhysicalGammaProductReal_one hk,
    sharpRealOddGammaProductReal_one, mul_one]

theorem sharpRealGammaCoefficientReal_succ
    {n k : ℕ} (hn : 1 ≤ n) (hnk : n + 1 ≤ k) :
    sharpRealGammaCoefficientReal (n + 1) k =
      sharpRealGammaCoefficientReal n (k - 1) *
        realAuxiliaryGammaHalfFactorReal k *
        realAuxiliaryGammaHalfFactorReal (2 * (n + 1) - 1) := by
  rw [sharpRealGammaCoefficientReal,
    sharpRealPhysicalGammaProductReal_succ hn hnk,
    sharpRealOddGammaProductReal_succ hn]
  unfold sharpRealGammaCoefficientReal
  ring

theorem sharpRealGammaCoefficientReal_nonneg
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    0 ≤ sharpRealGammaCoefficientReal n k := by
  unfold sharpRealGammaCoefficientReal
    sharpRealPhysicalGammaProductReal sharpRealOddGammaProductReal
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro d hd
    have hdLower := (Finset.mem_Icc.mp hd).1
    have hdimd : 2 ≤ d := by omega
    exact realAuxiliaryGammaHalfFactorReal_nonneg hdimd
  · apply Finset.prod_nonneg
    intro r hr
    have hr2 := (Finset.mem_Icc.mp hr).1
    exact realAuxiliaryGammaHalfFactorReal_nonneg (by omega)

theorem sharpRealGammaCoefficient_eq_ofReal
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    sharpRealGammaCoefficient n k =
      ENNReal.ofReal (sharpRealGammaCoefficientReal n k) := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              rw [sharpRealGammaCoefficient_one,
                sharpRealGammaCoefficientReal_one (by omega),
                realAuxiliaryGammaHalfFactor_eq_ofReal]
          | succ n =>
              have hkpos : 1 ≤ k := by omega
              have hdimLower : 2 * (n + 1) - 1 ≤ k - 1 := by omega
              have hkLower : 2 ≤ k - 1 := by omega
              have hih := ih (n + 1) (by omega) (k := k - 1)
                (by omega) hkLower hdimLower
              have hnonnegLower := sharpRealGammaCoefficientReal_nonneg
                (n := n + 1) (k := k - 1) (by omega) hkLower hdimLower
              have hgammaK := realAuxiliaryGammaHalfFactorReal_nonneg
                (by omega : 2 ≤ k)
              rw [sharpRealGammaCoefficient_add_two,
                sharpRealGammaCoefficientReal_succ (by omega) (by omega),
                hih, realAuxiliaryGammaHalfFactor_eq_ofReal,
                realAuxiliaryGammaHalfFactor_eq_ofReal,
                ← ENNReal.ofReal_mul hnonnegLower,
                ← ENNReal.ofReal_mul (mul_nonneg hnonnegLower hgammaK)]

theorem sharpRealNormalizedCoefficient_eq_ofReal
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    sharpRealNormalizedCoefficient n k =
      ENNReal.ofReal
        (realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
          sharpRealGammaCoefficientReal n k) := by
  rw [sharpRealNormalizedCoefficient,
    sharpRealGammaCoefficient_eq_ofReal hn hk hdim]
  rw [ENNReal.ofReal_mul]
  exact realGaussianIntervalPrefactor_nonneg
    (realGramHafnianRMS_nonneg n k)

/-! ## Exact regrouping of the normalized coefficient -/

theorem realGramHafnianRMS_eq_sqrt_odd_mul_sqrt_dimension
    (n k : ℕ) :
    realGramHafnianRMS n k =
      Real.sqrt (oddPairingNat n : ℝ) *
        Real.sqrt (dimensionProduct k n) := by
  unfold realGramHafnianRMS closedFirstMoment
  rw [Real.sqrt_mul]
  positivity

/-- The exact normalized constant separates into the universal interval
constant, the telescoping odd-dimensional product `K_n`, and a physical-row
dimension product.  This regrouping deliberately avoids any asymptotics. -/
theorem sharpRealNormalizedCoefficientReal_factorization
    {n k : ℕ} (hn : 1 ≤ n) :
    realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
        sharpRealGammaCoefficientReal n k =
      realGaussianIntervalPrefactor 1 * realElementaryKn n *
        (Real.sqrt (dimensionProduct k n) *
          sharpRealPhysicalGammaProductReal n k) := by
  rw [realGramHafnianRMS_eq_sqrt_odd_mul_sqrt_dimension]
  rw [realElementaryKn_eq_oddPairing_gammaProduct hn]
  unfold sharpRealGammaCoefficientReal sharpRealOddGammaProductReal
    realGaussianIntervalPrefactor
  ring

theorem sqrt_dimensionProduct_le_pow
    (n k : ℕ) :
    Real.sqrt (dimensionProduct k n) ≤
      (Real.sqrt ((k + 2 * n : ℕ) : ℝ)) ^ n := by
  unfold dimensionProduct
  rw [Real.sqrt_prod]
  · calc
      (∏ q ∈ Finset.range n,
          Real.sqrt (((k + 2 * q : ℕ) : ℝ))) ≤
          ∏ _q ∈ Finset.range n,
            Real.sqrt (((k + 2 * n : ℕ) : ℝ)) := by
        apply Finset.prod_le_prod
        · intro q hq
          positivity
        · intro q hq
          apply Real.sqrt_le_sqrt
          exact_mod_cast Nat.add_le_add_left
            (Nat.mul_le_mul_left 2 (Finset.mem_range.mp hq).le) k
      _ = (Real.sqrt (((k + 2 * n : ℕ) : ℝ))) ^ n := by
        rw [Finset.prod_const, Finset.card_range]
  · intro q hq
    positivity

theorem realAuxiliaryGammaHalfFactorReal_eq_bk_div_sqrt
    {d : ℕ} (hd : 1 ≤ d) :
    realAuxiliaryGammaHalfFactorReal d =
      realElementaryBk d / Real.sqrt (d : ℝ) := by
  unfold realElementaryBk
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  field_simp [hsqrt]

theorem realAuxiliaryGammaHalfFactorReal_sq_le_inv_sub_two
    {d : ℕ} (hd : 3 ≤ d) :
    realAuxiliaryGammaHalfFactorReal d ^ 2 ≤
      1 / ((d : ℝ) - 2) := by
  have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden1 : 0 < (d : ℝ) - 1 := by linarith
  have hden2 : 0 < (d : ℝ) - 2 := by linarith
  have hsqrt : 0 < Real.sqrt (d : ℝ) := by positivity
  have hgamma :
      realAuxiliaryGammaHalfFactorReal d ≤
        ((d : ℝ) / ((d : ℝ) - 1)) / Real.sqrt (d : ℝ) := by
    rw [realAuxiliaryGammaHalfFactorReal_eq_bk_div_sqrt (by omega)]
    exact div_le_div_of_nonneg_right (realElementaryBk_le_div (by omega))
      (Real.sqrt_nonneg _)
  have hgammaNonneg := realAuxiliaryGammaHalfFactorReal_nonneg (by omega : 2 ≤ d)
  have hrightNonneg :
      0 ≤ ((d : ℝ) / ((d : ℝ) - 1)) / Real.sqrt (d : ℝ) := by
    positivity
  calc
    realAuxiliaryGammaHalfFactorReal d ^ 2 ≤
        (((d : ℝ) / ((d : ℝ) - 1)) / Real.sqrt (d : ℝ)) ^ 2 :=
      (sq_le_sq₀ hgammaNonneg hrightNonneg).2 hgamma
    _ = (d : ℝ) / ((d : ℝ) - 1) ^ 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ))]
      field_simp [show (d : ℝ) ≠ 0 by positivity, hden1.ne']
    _ ≤ 1 / ((d : ℝ) - 2) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hden1) hden2).2
      nlinarith

theorem sharpRealDimensionGammaFactor_le_exp
    {n k q : ℕ} (hq : q < n) (hkn : n + 2 ≤ k) :
    Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
        realAuxiliaryGammaHalfFactorReal (k - q) ≤
      Real.exp
        ((3 * (q : ℝ) + 2) /
          (2 * ((k - n - 1 : ℕ) : ℝ))) := by
  have hd3 : 3 ≤ k - q := by omega
  have hgapNat : 0 < k - n - 1 := by omega
  have hgap : 0 < ((k - n - 1 : ℕ) : ℝ) := by exact_mod_cast hgapNat
  have hlocalNat : 0 < k - q - 2 := by omega
  have hlocal : 0 < ((k - q - 2 : ℕ) : ℝ) := by exact_mod_cast hlocalNat
  have hfactorNonneg :
      0 ≤ Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
        realAuxiliaryGammaHalfFactorReal (k - q) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (realAuxiliaryGammaHalfFactorReal_nonneg (by omega))
  have hsq :
      (Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
          realAuxiliaryGammaHalfFactorReal (k - q)) ^ 2 ≤
        ((k + 2 * q : ℕ) : ℝ) / ((k - q - 2 : ℕ) : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ ((k + 2 * q : ℕ) : ℝ))]
    have hgamma := realAuxiliaryGammaHalfFactorReal_sq_le_inv_sub_two hd3
    have hcast : ((k - q : ℕ) : ℝ) - 2 = ((k - q - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 2 ≤ k - q)]
      norm_num
    rw [hcast] at hgamma
    calc
      ((k + 2 * q : ℕ) : ℝ) *
          realAuxiliaryGammaHalfFactorReal (k - q) ^ 2 ≤
        ((k + 2 * q : ℕ) : ℝ) *
          (1 / ((k - q - 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hgamma (by positivity)
      _ = ((k + 2 * q : ℕ) : ℝ) / ((k - q - 2 : ℕ) : ℝ) := by
        ring
  have hratio :
      ((k + 2 * q : ℕ) : ℝ) / ((k - q - 2 : ℕ) : ℝ) ≤
        1 + (3 * (q : ℝ) + 2) / ((k - n - 1 : ℕ) : ℝ) := by
    have hkq : k = (k - q) + q := by omega
    have hlocalEq :
        ((k + 2 * q : ℕ) : ℝ) / ((k - q - 2 : ℕ) : ℝ) =
          1 + (3 * (q : ℝ) + 2) / ((k - q - 2 : ℕ) : ℝ) := by
      have hkqCast : (k : ℝ) = ((k - q : ℕ) : ℝ) + (q : ℝ) := by
        exact_mod_cast hkq
      rw [show ((k + 2 * q : ℕ) : ℝ) = (k : ℝ) + 2 * (q : ℝ) by
        push_cast; ring]
      rw [hkqCast]
      field_simp [hlocal.ne']
      have hsubCast : ((k - q : ℕ) : ℝ) =
          ((k - q - 2 : ℕ) : ℝ) + 2 := by
        exact_mod_cast (show k - q = (k - q - 2) + 2 by omega)
      rw [hsubCast]
      ring
    rw [hlocalEq]
    have hdiv :
        (3 * (q : ℝ) + 2) / ((k - q - 2 : ℕ) : ℝ) ≤
          (3 * (q : ℝ) + 2) / ((k - n - 1 : ℕ) : ℝ) := by
      apply div_le_div₀ (by positivity) le_rfl hgap
      exact_mod_cast (show k - n - 1 ≤ k - q - 2 by omega)
    linarith
  have hx : 0 ≤ (3 * (q : ℝ) + 2) / ((k - n - 1 : ℕ) : ℝ) := by
    positivity
  calc
    Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
        realAuxiliaryGammaHalfFactorReal (k - q) ≤
      Real.sqrt
        (1 + (3 * (q : ℝ) + 2) / ((k - n - 1 : ℕ) : ℝ)) := by
          apply (sq_le_sq₀ hfactorNonneg (Real.sqrt_nonneg _)).1
          rw [Real.sq_sqrt (by linarith)]
          exact hsq.trans hratio
    _ ≤ Real.exp
        (((3 * (q : ℝ) + 2) / ((k - n - 1 : ℕ) : ℝ)) / 2) :=
      sqrt_one_add_le_exp_half hx
    _ = Real.exp
        ((3 * (q : ℝ) + 2) /
          (2 * ((k - n - 1 : ℕ) : ℝ))) := by
      congr 1
      ring

theorem sharpRealDimensionGammaProductReal_le_exp_sharp
    {n k : ℕ} (hkn : n + 2 ≤ k) :
    sharpRealDimensionGammaProductReal n k ≤
      Real.exp
        ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (4 * ((k - n - 1 : ℕ) : ℝ))) := by
  have hgapNat : 0 < k - n - 1 := by omega
  have hgap : 0 < ((k - n - 1 : ℕ) : ℝ) := by exact_mod_cast hgapNat
  let P : ℕ → Prop := fun j ↦ j ≤ n →
    (∏ q ∈ Finset.range j,
      Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
        realAuxiliaryGammaHalfFactorReal (k - q)) ≤
      Real.exp
        ((3 * (j : ℝ) ^ 2 + (j : ℝ)) /
          (4 * ((k - n - 1 : ℕ) : ℝ)))
  have hP : ∀ j, P j := by
    intro j
    induction j with
    | zero =>
        intro _hj
        simp
    | succ j ih =>
        intro hj
        rw [Finset.prod_range_succ]
        have hfactor := sharpRealDimensionGammaFactor_le_exp
          (n := n) (k := k) (q := j) (by omega) hkn
        have hih := ih (by omega)
        have hfactorNonneg :
            0 ≤ Real.sqrt (((k + 2 * j : ℕ) : ℝ)) *
              realAuxiliaryGammaHalfFactorReal (k - j) :=
          mul_nonneg (Real.sqrt_nonneg _)
            (realAuxiliaryGammaHalfFactorReal_nonneg (by omega))
        calc
          (∏ q ∈ Finset.range j,
              Real.sqrt (((k + 2 * q : ℕ) : ℝ)) *
                realAuxiliaryGammaHalfFactorReal (k - q)) *
              (Real.sqrt (((k + 2 * j : ℕ) : ℝ)) *
                realAuxiliaryGammaHalfFactorReal (k - j)) ≤
            Real.exp
                ((3 * (j : ℝ) ^ 2 + (j : ℝ)) /
                  (4 * ((k - n - 1 : ℕ) : ℝ))) *
              Real.exp
                ((3 * (j : ℝ) + 2) /
                  (2 * ((k - n - 1 : ℕ) : ℝ))) := by
            exact mul_le_mul hih hfactor hfactorNonneg (by positivity)
          _ = Real.exp
              ((3 * ((j + 1 : ℕ) : ℝ) ^ 2 + ((j + 1 : ℕ) : ℝ)) /
                (4 * ((k - n - 1 : ℕ) : ℝ))) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            field_simp [hgap.ne']
            ring
  unfold sharpRealDimensionGammaProductReal
  exact hP n le_rfl

/-- Sharper elementary envelope obtained by pairing the physical Gamma
factor `gamma_(k-q)` with the corresponding RMS factor `sqrt(k+2q)`. -/
theorem sharpRealNormalizedCoefficientReal_le_exp_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hkn : n + 2 ≤ k) :
    realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
        sharpRealGammaCoefficientReal n k ≤
      realGaussianIntervalPrefactor 1 *
        Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
        Real.exp
          ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (4 * ((k - n - 1 : ℕ) : ℝ))) := by
  rw [sharpRealNormalizedCoefficientReal_factorization hn]
  rw [sqrt_dimension_mul_physical_gamma_eq_paired (by omega : n ≤ k)]
  have hpref : 0 ≤ realGaussianIntervalPrefactor 1 :=
    realGaussianIntervalPrefactor_nonneg (by norm_num)
  have hK := realElementaryKn_le_sqrt_odd hn
  have hD := sharpRealDimensionGammaProductReal_le_exp_sharp hkn
  have hDnonneg : 0 ≤ sharpRealDimensionGammaProductReal n k := by
    unfold sharpRealDimensionGammaProductReal
    apply Finset.prod_nonneg
    intro q hq
    exact mul_nonneg (Real.sqrt_nonneg _)
      (realAuxiliaryGammaHalfFactorReal_nonneg (by
        have hq' := Finset.mem_range.mp hq
        omega))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hK hpref) hD
    hDnonneg (mul_nonneg hpref (Real.sqrt_nonneg _))

theorem sharpRealNormalizedCoefficient_le_exp_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) (hkn : n + 2 ≤ k) :
    sharpRealNormalizedCoefficient n k ≤
      ENNReal.ofReal
        (realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp
            ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (4 * ((k - n - 1 : ℕ) : ℝ)))) := by
  rw [sharpRealNormalizedCoefficient_eq_ofReal hn hk hdim]
  exact ENNReal.ofReal_le_ofReal
    (sharpRealNormalizedCoefficientReal_le_exp_sharp hn hkn)

theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_exp_sharp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) (hkn : n + 2 ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      ENNReal.ofReal
          (realGaussianIntervalPrefactor 1 *
            Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
            Real.exp
              ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
                (4 * ((k - n - 1 : ℕ) : ℝ)))) *
        ENNReal.ofReal epsilon := by
  calc
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      sharpRealNormalizedCoefficient n k * ENNReal.ofReal epsilon :=
        standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
          hn hk hdim z epsilon hepsilon
    _ ≤ ENNReal.ofReal
          (realGaussianIntervalPrefactor 1 *
            Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
            Real.exp
              ((3 * (n : ℝ) ^ 2 + (n : ℝ)) /
                (4 * ((k - n - 1 : ℕ) : ℝ)))) *
        ENNReal.ofReal epsilon := by
      gcongr
      exact sharpRealNormalizedCoefficient_le_exp_sharp hn hk hdim hkn

theorem realAuxiliaryGammaHalfFactorReal_le_sqrt_top_div_gap
    {n k d : ℕ} (hkn : n < k)
    (hdmem : d ∈ Finset.Icc (k - n + 1) k) :
    realAuxiliaryGammaHalfFactorReal d ≤
      Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ) := by
  have hdLower : k - n + 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
  have hdUpper : d ≤ k := (Finset.mem_Icc.mp hdmem).2
  have hd2 : 2 ≤ d := by omega
  have hgapPosNat : 0 < k - n := Nat.sub_pos_of_lt hkn
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hdPredPos : 0 < (d : ℝ) - 1 := by linarith
  have hgapPos : 0 < ((k - n : ℕ) : ℝ) := by exact_mod_cast hgapPosNat
  have hsqrtdPos : 0 < Real.sqrt (d : ℝ) := by positivity
  rw [realAuxiliaryGammaHalfFactorReal_eq_bk_div_sqrt (by omega)]
  calc
    realElementaryBk d / Real.sqrt (d : ℝ) ≤
        ((d : ℝ) / ((d : ℝ) - 1)) / Real.sqrt (d : ℝ) := by
      exact div_le_div_of_nonneg_right (realElementaryBk_le_div hd2)
        (Real.sqrt_nonneg _)
    _ = Real.sqrt (d : ℝ) / ((d : ℝ) - 1) := by
      field_simp [hsqrtdPos.ne', hdPredPos.ne']
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ))]
    _ ≤ Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ) := by
      apply div_le_div₀ (Real.sqrt_nonneg _)
        (Real.sqrt_le_sqrt (by exact_mod_cast hdUpper)) hgapPos
      have hgapPredNat : k - n + 1 ≤ d := hdLower
      have hgapCast : ((k - n : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by
        exact_mod_cast hgapPredNat
      linarith

theorem sharpRealPhysicalGammaProductReal_le_pow
    {n k : ℕ} (hn : 1 ≤ n) (hkn : n < k) :
    sharpRealPhysicalGammaProductReal n k ≤
      (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ)) ^ n := by
  unfold sharpRealPhysicalGammaProductReal
  calc
    (∏ d ∈ Finset.Icc (k - n + 1) k,
        realAuxiliaryGammaHalfFactorReal d) ≤
        ∏ _d ∈ Finset.Icc (k - n + 1) k,
          (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ)) := by
      apply Finset.prod_le_prod
      · intro d hd
        exact realAuxiliaryGammaHalfFactorReal_nonneg (by
          have := (Finset.mem_Icc.mp hd).1
          omega)
      · intro d hd
        exact realAuxiliaryGammaHalfFactorReal_le_sqrt_top_div_gap
          hkn hd
    _ = (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ)) ^ n := by
      rw [Finset.prod_const, Nat.card_Icc]
      congr 1
      omega

theorem sqrt_k_mul_sqrt_k_add_two_n_le
    (n k : ℕ) :
    Real.sqrt (k : ℝ) * Real.sqrt ((k + 2 * n : ℕ) : ℝ) ≤
      (k + n : ℕ) := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · push_cast
    nlinarith

theorem sqrt_dimension_mul_physical_gamma_le_exp
    {n k : ℕ} (hn : 1 ≤ n) (hkn : n < k) :
    Real.sqrt (dimensionProduct k n) *
        sharpRealPhysicalGammaProductReal n k ≤
      Real.exp
        (2 * (n : ℝ) ^ 2 / ((k - n : ℕ) : ℝ)) := by
  have hdim := sqrt_dimensionProduct_le_pow n k
  have hphys := sharpRealPhysicalGammaProductReal_le_pow hn hkn
  have hdimNonneg : 0 ≤ Real.sqrt (dimensionProduct k n) :=
    Real.sqrt_nonneg _
  have hphysNonneg : 0 ≤ sharpRealPhysicalGammaProductReal n k := by
    unfold sharpRealPhysicalGammaProductReal
    apply Finset.prod_nonneg
    intro d hd
    exact realAuxiliaryGammaHalfFactorReal_nonneg (by
      have := (Finset.mem_Icc.mp hd).1
      omega)
  have hmul :
      Real.sqrt (dimensionProduct k n) *
          sharpRealPhysicalGammaProductReal n k ≤
        (Real.sqrt ((k + 2 * n : ℕ) : ℝ) *
          (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ))) ^ n := by
    calc
      Real.sqrt (dimensionProduct k n) *
          sharpRealPhysicalGammaProductReal n k ≤
        (Real.sqrt ((k + 2 * n : ℕ) : ℝ)) ^ n *
          (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ)) ^ n := by
            exact mul_le_mul hdim hphys hphysNonneg
              (by positivity)
      _ = (Real.sqrt ((k + 2 * n : ℕ) : ℝ) *
          (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ))) ^ n := by
            rw [mul_pow]
  have hgapPosNat : 0 < k - n := Nat.sub_pos_of_lt hkn
  have hgapPos : 0 < ((k - n : ℕ) : ℝ) := by exact_mod_cast hgapPosNat
  have hbase :
      Real.sqrt ((k + 2 * n : ℕ) : ℝ) *
          (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ)) ≤
        Real.exp (2 * (n : ℝ) / ((k - n : ℕ) : ℝ)) := by
    calc
      Real.sqrt ((k + 2 * n : ℕ) : ℝ) *
          (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ)) =
        (Real.sqrt (k : ℝ) *
          Real.sqrt ((k + 2 * n : ℕ) : ℝ)) /
            ((k - n : ℕ) : ℝ) := by ring
      _ ≤ ((k + n : ℕ) : ℝ) / ((k - n : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right
          (sqrt_k_mul_sqrt_k_add_two_n_le n k) hgapPos.le
      _ = 1 + 2 * (n : ℝ) / ((k - n : ℕ) : ℝ) := by
        have hkEq : k = (k - n) + n := by omega
        have hkCast : (k : ℝ) = ((k - n : ℕ) : ℝ) + (n : ℝ) := by
          exact_mod_cast hkEq
        rw [show ((k + n : ℕ) : ℝ) = (k : ℝ) + (n : ℝ) by simp]
        rw [hkCast]
        field_simp [hgapPos.ne']
        ring
      _ ≤ Real.exp (2 * (n : ℝ) / ((k - n : ℕ) : ℝ)) := by
        simpa [add_comm] using
          Real.add_one_le_exp (2 * (n : ℝ) / ((k - n : ℕ) : ℝ))
  calc
    Real.sqrt (dimensionProduct k n) *
        sharpRealPhysicalGammaProductReal n k ≤
      (Real.sqrt ((k + 2 * n : ℕ) : ℝ) *
          (Real.sqrt (k : ℝ) / ((k - n : ℕ) : ℝ))) ^ n := hmul
    _ ≤ (Real.exp (2 * (n : ℝ) / ((k - n : ℕ) : ℝ))) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    _ = Real.exp
        (2 * (n : ℝ) ^ 2 / ((k - n : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Elementary real constant with the sharp high-dimensional scale
`exp (O(n^2/k))`.  The numerical exponent here is intentionally simple;
the exact Gamma product remains available in the preceding theorem. -/
theorem sharpRealNormalizedCoefficientReal_le_exp
    {n k : ℕ} (hn : 1 ≤ n) (hkn : n < k) :
    realGaussianIntervalPrefactor (realGramHafnianRMS n k) *
        sharpRealGammaCoefficientReal n k ≤
      realGaussianIntervalPrefactor 1 *
        Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
        Real.exp (2 * (n : ℝ) ^ 2 / ((k - n : ℕ) : ℝ)) := by
  rw [sharpRealNormalizedCoefficientReal_factorization hn]
  have hpref : 0 ≤ realGaussianIntervalPrefactor 1 :=
    realGaussianIntervalPrefactor_nonneg (by norm_num)
  have hK := realElementaryKn_le_sqrt_odd hn
  have hD := sqrt_dimension_mul_physical_gamma_le_exp hn hkn
  have hphysical : 0 ≤ sharpRealPhysicalGammaProductReal n k := by
    unfold sharpRealPhysicalGammaProductReal
    apply Finset.prod_nonneg
    intro d hd
    exact realAuxiliaryGammaHalfFactorReal_nonneg (by
      have := (Finset.mem_Icc.mp hd).1
      omega)
  have hDnonneg :
      0 ≤ Real.sqrt (dimensionProduct k n) *
        sharpRealPhysicalGammaProductReal n k :=
    mul_nonneg (Real.sqrt_nonneg _) hphysical
  exact mul_le_mul (mul_le_mul_of_nonneg_left hK hpref) hD
    hDnonneg (mul_nonneg hpref (Real.sqrt_nonneg _))

theorem sharpRealNormalizedCoefficient_le_exp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) (hkn : n < k) :
    sharpRealNormalizedCoefficient n k ≤
      ENNReal.ofReal
        (realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp (2 * (n : ℝ) ^ 2 / ((k - n : ℕ) : ℝ))) := by
  rw [sharpRealNormalizedCoefficient_eq_ofReal hn hk hdim]
  exact ENNReal.ofReal_le_ofReal
    (sharpRealNormalizedCoefficientReal_le_exp hn hkn)

/-- Simplified finite shifted-anticoncentration theorem.  Its coefficient is
polynomial whenever `n^2 / k = O(log n)`. -/
theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_exp
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      ENNReal.ofReal
          (realGaussianIntervalPrefactor 1 *
            Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
            Real.exp (2 * (n : ℝ) ^ 2 / ((k - n : ℕ) : ℝ))) *
        ENNReal.ofReal epsilon := by
  have hkn : n < k := by omega
  calc
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      sharpRealNormalizedCoefficient n k * ENNReal.ofReal epsilon :=
        standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
          hn hk hdim z epsilon hepsilon
    _ ≤ ENNReal.ofReal
          (realGaussianIntervalPrefactor 1 *
            Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
            Real.exp (2 * (n : ℝ) ^ 2 / ((k - n : ℕ) : ℝ))) *
        ENNReal.ofReal epsilon := by
      gcongr
      exact sharpRealNormalizedCoefficient_le_exp hn hk hdim hkn

theorem sharpRealNormalizedCoefficient_le_exp_four
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    sharpRealNormalizedCoefficient n k ≤
      ENNReal.ofReal
        (realGaussianIntervalPrefactor 1 *
          Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
          Real.exp (4 * (n : ℝ) ^ 2 / (k : ℝ))) := by
  have hk2 : 2 ≤ k := by omega
  have hdim : 2 * n - 1 ≤ k := by omega
  have hkn : n < k := by omega
  have hkPos : 0 < (k : ℝ) := by positivity
  have hgapPosNat : 0 < k - n := Nat.sub_pos_of_lt hkn
  have hgapPos : 0 < ((k - n : ℕ) : ℝ) := by exact_mod_cast hgapPosNat
  have hden :
      2 * (n : ℝ) ^ 2 / ((k - n : ℕ) : ℝ) ≤
        4 * (n : ℝ) ^ 2 / (k : ℝ) := by
    apply (div_le_div_iff₀ hgapPos hkPos).2
    have hkCast : (k : ℝ) ≤ 2 * ((k - n : ℕ) : ℝ) := by
      have hNat : k ≤ 2 * (k - n) := by omega
      exact_mod_cast hNat
    nlinarith [sq_nonneg (n : ℝ)]
  have hreal := sharpRealNormalizedCoefficientReal_le_exp hn hkn
  rw [sharpRealNormalizedCoefficient_eq_ofReal hn hk2 hdim]
  apply ENNReal.ofReal_le_ofReal
  refine hreal.trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hden)
  exact mul_nonneg
    (realGaussianIntervalPrefactor_nonneg (by norm_num))
    (Real.sqrt_nonneg _)

theorem standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_exp_four
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 * n ≤ k)
    (z epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      ENNReal.ofReal
          (realGaussianIntervalPrefactor 1 *
            Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
            Real.exp (4 * (n : ℝ) ^ 2 / (k : ℝ))) *
        ENNReal.ofReal epsilon := by
  have hk2 : 2 ≤ k := by omega
  have hdim : 2 * n - 1 ≤ k := by omega
  calc
    (standardRealGaussianColumnMatrixMeasure n k)
        {X | |realGramHafnianObservable n k X - z| ≤
          epsilon * realGramHafnianRMS n k} ≤
      sharpRealNormalizedCoefficient n k * ENNReal.ofReal epsilon :=
        standardRealGaussianColumnMatrix_normalizedShiftedSmallBall_le_sharp
          hn hk2 hdim z epsilon hepsilon
    _ ≤ ENNReal.ofReal
          (realGaussianIntervalPrefactor 1 *
            Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) *
            Real.exp (4 * (n : ℝ) ^ 2 / (k : ℝ))) *
        ENNReal.ofReal epsilon := by
      gcongr
      exact sharpRealNormalizedCoefficient_le_exp_four hn hk

end

end LogdetLean.GramHafnian
