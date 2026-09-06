import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralResolventIteration
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealSecondMoment
import LogdetLean.Coherence.BetaHalfNormalization
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.NumberTheory.Harmonic.Bounds
/-!
# Exact normalization of the literal beta-one Gamma coefficient

The bounded-resolvent iteration produces a product of negative-half
chi-square moments.  Multiplication by the exact literal real RMS reorganizes
that raw product into the three paper constants `b_k`, `K_n`, and
`P^{ent}_{k,n}`.  The productwise definitions below are chosen so that the
normalization is an exact successor induction; equivalent displayed Gamma
and square-root forms are recorded separately.
-/

open scoped BigOperators ENNReal Real Nat

namespace LogdetLean.GramHafnian

noncomputable section

open LogdetLean.Coherence

/-- Real-valued version of the negative-half chi-square factor. -/
def realAuxiliaryGammaHalfFactorReal (d : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (1 / 2 : ℝ) *
    Real.Gamma (((d : ℝ) - 1) / 2) /
    Real.Gamma ((d : ℝ) / 2)

@[simp] theorem realAuxiliaryGammaHalfFactor_eq_ofReal (d : ℕ) :
    realAuxiliaryGammaHalfFactor d =
      ENNReal.ofReal (realAuxiliaryGammaHalfFactorReal d) := rfl

theorem realAuxiliaryGammaHalfFactorReal_pos
    {d : ℕ} (hd : 2 ≤ d) :
    0 < realAuxiliaryGammaHalfFactorReal d := by
  have hpow : 0 < (1 / 2 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnumArg : 0 < (((d : ℝ) - 1) / 2) := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hdenArg : 0 < ((d : ℝ) / 2) := by positivity
  exact div_pos
    (mul_pos hpow (Real.Gamma_pos_of_pos hnumArg))
    (Real.Gamma_pos_of_pos hdenArg)

theorem realAuxiliaryGammaHalfFactorReal_nonneg
    {d : ℕ} (hd : 2 ≤ d) :
    0 ≤ realAuxiliaryGammaHalfFactorReal d :=
  (realAuxiliaryGammaHalfFactorReal_pos hd).le

/-- Paper constant `b_k`, in the factorization best suited to the exact
normalization proof. -/
def realElementaryBk (k : ℕ) : ℝ :=
  Real.sqrt (k : ℝ) * realAuxiliaryGammaHalfFactorReal k

/-- Paper constant `K_n`, productwise.  The square roots of the odd factors
multiply to `sqrt ((2n-1)!!)`. -/
def realElementaryKn (n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n,
    Real.sqrt (((2 * r - 1 : ℕ) : ℝ)) *
      realAuxiliaryGammaHalfFactorReal (2 * r - 1)

/-- Elementary dimension-loss product.  This is algebraically the paper's
`prod sqrt(1+(2r-2)/k)/sqrt(1-delta)` form. -/
def realElementaryPEnt (n k : ℕ) (delta : ℝ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n,
    Real.sqrt ((k : ℝ) + 2 * (r : ℝ) - 2) *
      (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹

/-- Real counterpart of the raw ENNReal half-factor product. -/
def pastRealCofactorHalfFactorProductReal
    (n k : ℕ) (delta : ℝ) : ℝ :=
  realAuxiliaryGammaHalfFactorReal k *
    ∏ r ∈ Finset.Icc 2 n,
      (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ *
        realAuxiliaryGammaHalfFactorReal (2 * r - 1)

theorem realElementaryBk_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < realElementaryBk k := by
  unfold realElementaryBk
  exact mul_pos (Real.sqrt_pos.2 (by positivity))
    (realAuxiliaryGammaHalfFactorReal_pos hk)

theorem realElementaryKn_pos {n : ℕ} :
    0 < realElementaryKn n := by
  unfold realElementaryKn
  apply Finset.prod_pos
  intro r hr
  have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
  have hd : 2 ≤ 2 * r - 1 := by omega
  exact mul_pos (Real.sqrt_pos.2 (by positivity))
    (realAuxiliaryGammaHalfFactorReal_pos hd)

theorem realElementaryPEnt_pos
    {n k : ℕ} (hk : 0 < k) {delta : ℝ} (hdeltalt : delta < 1) :
    0 < realElementaryPEnt n k delta := by
  unfold realElementaryPEnt
  apply Finset.prod_pos
  intro r hr
  have hnum : 0 < (k : ℝ) + 2 * (r : ℝ) - 2 := by
    have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    linarith
  have hden : 0 < (k : ℝ) * (1 - delta) :=
    mul_pos (by exact_mod_cast hk) (sub_pos.mpr hdeltalt)
  exact mul_pos (Real.sqrt_pos.2 hnum)
    (inv_pos.mpr (Real.sqrt_pos.2 hden))

theorem pastRealCofactorHalfFactorProductReal_pos
    {n k : ℕ} (hk : 2 ≤ k) {delta : ℝ} (hdeltalt : delta < 1) :
    0 < pastRealCofactorHalfFactorProductReal n k delta := by
  unfold pastRealCofactorHalfFactorProductReal
  apply mul_pos (realAuxiliaryGammaHalfFactorReal_pos hk)
  apply Finset.prod_pos
  intro r hr
  have hd : 2 ≤ 2 * r - 1 := by
    have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
    omega
  have hscale : 0 < (k : ℝ) * (1 - delta) :=
    mul_pos (by positivity) (sub_pos.mpr hdeltalt)
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.2 hscale))
    (realAuxiliaryGammaHalfFactorReal_pos hd)

/-- The ENNReal product used by the probability proof is exactly `ofReal`
of its real counterpart. -/
theorem pastRealCofactorHalfFactorProduct_eq_ofReal
    {n k : ℕ} (hk : 2 ≤ k) {delta : ℝ} (hdeltalt : delta < 1) :
    pastRealCofactorHalfFactorProduct n k delta =
      ENNReal.ofReal
        (pastRealCofactorHalfFactorProductReal n k delta) := by
  have hscale : 0 ≤
      (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ := by positivity
  have hterm : ∀ r ∈ Finset.Icc 2 n,
      0 ≤ (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ *
        realAuxiliaryGammaHalfFactorReal (2 * r - 1) := by
    intro r hr
    have hd : 2 ≤ 2 * r - 1 := by
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      omega
    exact mul_nonneg hscale (realAuxiliaryGammaHalfFactorReal_nonneg hd)
  unfold pastRealCofactorHalfFactorProduct
    pastRealCofactorBaseHalfFactor pastRealCofactorLevelHalfFactor
    pastRealCofactorHalfFactorProductReal
  rw [ENNReal.ofReal_mul (realAuxiliaryGammaHalfFactorReal_nonneg hk)]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg hterm]
  apply Finset.prod_congr rfl
  intro r hr
  rw [ENNReal.ofReal_mul hscale]
  rw [realAuxiliaryGammaHalfFactor_eq_ofReal]

theorem realElementaryKn_succ
    (j : ℕ) (hj : 1 ≤ j) :
    realElementaryKn (j + 1) =
      realElementaryKn j *
        (Real.sqrt (((2 * j + 1 : ℕ) : ℝ)) *
          realAuxiliaryGammaHalfFactorReal (2 * j + 1)) := by
  unfold realElementaryKn
  rw [Finset.prod_Icc_succ_top (by omega)]
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]

theorem realElementaryPEnt_succ
    (j k : ℕ) (hj : 1 ≤ j) (delta : ℝ) :
    realElementaryPEnt (j + 1) k delta =
      realElementaryPEnt j k delta *
        (Real.sqrt ((k : ℝ) + 2 * (j : ℝ)) *
          (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹) := by
  unfold realElementaryPEnt
  rw [Finset.prod_Icc_succ_top (by omega)]
  congr 2
  push_cast
  ring

theorem pastRealCofactorHalfFactorProductReal_succ
    (j k : ℕ) (hj : 1 ≤ j) (delta : ℝ) :
    pastRealCofactorHalfFactorProductReal (j + 1) k delta =
      pastRealCofactorHalfFactorProductReal j k delta *
        ((Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ *
          realAuxiliaryGammaHalfFactorReal (2 * j + 1)) := by
  unfold pastRealCofactorHalfFactorProductReal
  rw [Finset.prod_Icc_succ_top (by omega)]
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
  ring

theorem closedFirstMoment_succ_real (k j : ℕ) :
    closedFirstMoment k (j + 1) =
      closedFirstMoment k j *
        ((((2 * j + 1 : ℕ) : ℝ)) * ((k + 2 * j : ℕ) : ℝ)) := by
  simp only [closedFirstMoment, oddPairingNat_succ, dimensionProduct_succ]
  push_cast
  ring

theorem realGramHafnianRMS_succ
    (k j : ℕ) (hk : 0 < k) :
    realGramHafnianRMS (j + 1) k =
      realGramHafnianRMS j k *
        Real.sqrt
          ((((2 * j + 1 : ℕ) : ℝ)) * ((k + 2 * j : ℕ) : ℝ)) := by
  unfold realGramHafnianRMS
  rw [closedFirstMoment_succ_real]
  exact Real.sqrt_mul (closedFirstMoment_pos k j hk).le _

theorem realGramHafnianRMS_one (k : ℕ) :
    realGramHafnianRMS 1 k = Real.sqrt (k : ℝ) := by
  simp [realGramHafnianRMS, closedFirstMoment, oddPairingNat,
    dimensionProduct]

/-- Exact real regrouping of the raw Gamma product and the RMS. -/
theorem pastRealCofactorHalfFactorProductReal_mul_RMS_eq
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    {delta : ℝ} (hdeltalt : delta < 1) :
    pastRealCofactorHalfFactorProductReal n k delta *
        realGramHafnianRMS n k =
      realElementaryBk k * realElementaryKn n *
        realElementaryPEnt n k delta := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    pastRealCofactorHalfFactorProductReal j k delta *
        realGramHafnianRMS j k =
      realElementaryBk k * realElementaryKn j *
        realElementaryPEnt j k delta
  have hP : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · dsimp [P]
      simp [pastRealCofactorHalfFactorProductReal,
        realElementaryBk, realElementaryKn, realElementaryPEnt,
        realGramHafnianRMS_one]
      ring
    · intro j hj ih
      dsimp [P] at ih ⊢
      have hk0 : 0 < k := by omega
      have hodd0 : 0 ≤ (((2 * j + 1 : ℕ) : ℝ)) := by positivity
      have hdim0 : 0 ≤ (((k + 2 * j : ℕ) : ℝ)) := by positivity
      have hsqrt :
          Real.sqrt
              ((((2 * j + 1 : ℕ) : ℝ)) * ((k + 2 * j : ℕ) : ℝ)) =
            Real.sqrt (((2 * j + 1 : ℕ) : ℝ)) *
              Real.sqrt ((k + 2 * j : ℕ) : ℝ) :=
        Real.sqrt_mul hodd0 _
      rw [pastRealCofactorHalfFactorProductReal_succ j k hj delta,
        realGramHafnianRMS_succ k j hk0,
        realElementaryKn_succ j hj,
        realElementaryPEnt_succ j k hj delta, hsqrt]
      have hcast : ((k + 2 * j : ℕ) : ℝ) =
          (k : ℝ) + 2 * (j : ℝ) := by push_cast; ring
      rw [hcast]
      rw [show
        (pastRealCofactorHalfFactorProductReal j k delta *
            ((Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ *
              realAuxiliaryGammaHalfFactorReal (2 * j + 1))) *
          (realGramHafnianRMS j k *
            (Real.sqrt (((2 * j + 1 : ℕ) : ℝ)) *
              Real.sqrt ((k : ℝ) + 2 * (j : ℝ)))) =
        (pastRealCofactorHalfFactorProductReal j k delta *
            realGramHafnianRMS j k) *
          ((Real.sqrt (((2 * j + 1 : ℕ) : ℝ)) *
              realAuxiliaryGammaHalfFactorReal (2 * j + 1)) *
            (Real.sqrt ((k : ℝ) + 2 * (j : ℝ)) *
              (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹)) by ring]
      rw [ih]
      ring
  exact hP

/-- **Exact paper-coefficient identity.**  The raw ENNReal Gamma product
times the exact literal RMS is precisely `ofReal (b_k K_n P_ent)`. -/
theorem pastRealCofactorHalfFactorProduct_mul_RMS_eq_paperCoefficient
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    {delta : ℝ} (hdeltalt : delta < 1) :
    pastRealCofactorHalfFactorProduct n k delta *
        ENNReal.ofReal (realGramHafnianRMS n k) =
      ENNReal.ofReal
        (realElementaryBk k * realElementaryKn n *
          realElementaryPEnt n k delta) := by
  rw [pastRealCofactorHalfFactorProduct_eq_ofReal hk hdeltalt]
  rw [← ENNReal.ofReal_mul
    (pastRealCofactorHalfFactorProductReal_pos hk hdeltalt).le]
  rw [pastRealCofactorHalfFactorProductReal_mul_RMS_eq
    hn hk hdeltalt]

/-! ## Crosswalk to the displayed paper formulas -/

/-- The productwise definition of `b_k` is the displayed Gamma quotient. -/
theorem realElementaryBk_eq_displayedGamma (k : ℕ) :
    realElementaryBk k =
      Real.sqrt ((k : ℝ) / 2) *
        Real.Gamma (((k : ℝ) - 1) / 2) /
        Real.Gamma ((k : ℝ) / 2) := by
  unfold realElementaryBk realAuxiliaryGammaHalfFactorReal
  rw [← Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (k : ℝ) * Real.sqrt (1 / 2 : ℝ) =
      Real.sqrt ((k : ℝ) / 2) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    congr 1
    ring
  rw [show
    Real.sqrt (k : ℝ) *
          (Real.sqrt (1 / 2 : ℝ) *
            Real.Gamma (((k : ℝ) - 1) / 2) /
            Real.Gamma ((k : ℝ) / 2)) =
      (Real.sqrt (k : ℝ) * Real.sqrt (1 / 2 : ℝ)) *
        Real.Gamma (((k : ℝ) - 1) / 2) /
        Real.Gamma ((k : ℝ) / 2) by ring]
  rw [hsqrt]

/-- The square-root part of `K_n` is exactly the square root of the odd
pairing product. -/
theorem realElementaryKn_eq_oddPairing_gammaProduct
    {n : ℕ} (hn : 1 ≤ n) :
    realElementaryKn n =
      Real.sqrt (oddPairingNat n : ℝ) *
        ∏ r ∈ Finset.Icc 2 n,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    realElementaryKn j =
      Real.sqrt (oddPairingNat j : ℝ) *
        ∏ r ∈ Finset.Icc 2 j,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1)
  have hP : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · dsimp [P]
      simp [realElementaryKn, oddPairingNat]
    · intro j hj ih
      dsimp [P] at ih ⊢
      rw [realElementaryKn_succ j hj, ih]
      rw [Finset.prod_Icc_succ_top (by omega)]
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
      rw [oddPairingNat_succ]
      have hcast :
          ((oddPairingNat j * (2 * j + 1) : ℕ) : ℝ) =
            (oddPairingNat j : ℝ) * ((2 * j + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (oddPairingNat j : ℝ))]
      ring
  exact hP

/-- Double-factorial version of the displayed formula for `K_n`. -/
theorem realElementaryKn_eq_doubleFactorial_gammaProduct
    {n : ℕ} (hn : 1 ≤ n) :
    realElementaryKn n =
      Real.sqrt (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ r ∈ Finset.Icc 2 n,
          realAuxiliaryGammaHalfFactorReal (2 * r - 1) := by
  simpa [oddPairingNat_eq_doubleFactorial] using
    realElementaryKn_eq_oddPairing_gammaProduct hn

/-- Factorwise conversion of the elementary loss to the normalized ratio
used in the paper. -/
theorem realElementaryPEnt_factor_eq_normalized
    {k r : ℕ} (hk : 0 < k) (hr : 2 ≤ r)
    {delta : ℝ} (hdeltalt : delta < 1) :
    Real.sqrt ((k : ℝ) + 2 * (r : ℝ) - 2) *
        (Real.sqrt ((k : ℝ) * (1 - delta)))⁻¹ =
      Real.sqrt (1 + (2 * (r : ℝ) - 2) / (k : ℝ)) *
        (Real.sqrt (1 - delta))⁻¹ := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hratio : 0 ≤ 1 + (2 * (r : ℝ) - 2) / (k : ℝ) := by
    have hu : 0 ≤ 2 * (r : ℝ) - 2 := by linarith
    have hquot : 0 ≤ (2 * (r : ℝ) - 2) / (k : ℝ) :=
      div_nonneg hu hkR.le
    linarith
  have hsnum :
      Real.sqrt ((k : ℝ) + 2 * (r : ℝ) - 2) =
        Real.sqrt (k : ℝ) *
          Real.sqrt (1 + (2 * (r : ℝ) - 2) / (k : ℝ)) := by
    rw [← Real.sqrt_mul hkR.le]
    congr 1
    field_simp [hkR.ne']
    ring
  have hsden :
      Real.sqrt ((k : ℝ) * (1 - delta)) =
        Real.sqrt (k : ℝ) * Real.sqrt (1 - delta) :=
    Real.sqrt_mul hkR.le _
  rw [hsnum, hsden]
  have hkroot : Real.sqrt (k : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hkR).ne'
  have hdeltaRoot : Real.sqrt (1 - delta) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.mpr hdeltalt)).ne'
  field_simp [hkroot, hdeltaRoot]

/-- Productwise conversion of `P_ent` to its displayed normalized-ratio
formula. -/
theorem realElementaryPEnt_eq_normalizedProduct
    {n k : ℕ} (hk : 0 < k)
    {delta : ℝ} (hdeltalt : delta < 1) :
    realElementaryPEnt n k delta =
      ∏ r ∈ Finset.Icc 2 n,
        Real.sqrt (1 + (2 * (r : ℝ) - 2) / (k : ℝ)) /
          Real.sqrt (1 - delta) := by
  unfold realElementaryPEnt
  apply Finset.prod_congr rfl
  intro r hr
  have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
  rw [div_eq_mul_inv]
  exact realElementaryPEnt_factor_eq_normalized hk hr2 hdeltalt

/-! ## Explicit finite coefficient bounds -/

/-- The squared, normalized half-step Gamma ratio satisfies the sharper
midpoint bound needed for the telescoping `K_n` estimate. -/
theorem gammaHalfRatioScale_sq_le_one_add_inv_two
    {x : ℝ} (hx : 0 < x) :
    gammaHalfRatioScale x ^ 2 ≤ 1 + 1 / (2 * x) := by
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGh : 0 < Real.Gamma (x + 1 / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hsqrt : 0 ≤ Real.sqrt (x + 1 / 2) := Real.sqrt_nonneg _
  have hmid := mul_Gamma_le_sqrt_add_half_mul_Gamma_add_half hx
  have hsq : (x * Real.Gamma x) ^ 2 ≤
      (Real.sqrt (x + 1 / 2) * Real.Gamma (x + 1 / 2)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hx.le hG.le)
      (mul_nonneg hsqrt hGh.le)).2 hmid
  simp only [mul_pow] at hsq
  rw [Real.sq_sqrt (by linarith : 0 ≤ x + 1 / 2)] at hsq
  unfold gammaHalfRatioScale
  rw [div_pow, mul_pow, Real.sq_sqrt hx.le]
  apply (div_le_iff₀ (sq_pos_of_pos hGh)).2
  have hxne : x ≠ 0 := hx.ne'
  calc
    x * Real.Gamma x ^ 2 ≤
        ((x + 1 / 2) / x) * Real.Gamma (x + 1 / 2) ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hx).2
      nlinarith
    _ = (1 + 1 / (2 * x)) * Real.Gamma (x + 1 / 2) ^ 2 := by
      field_simp [hxne]

/-- `b_k` expressed through the normalized half-step Gamma ratio. -/
theorem realElementaryBk_eq_gammaHalfRatioScale
    {k : ℕ} (hk : 2 ≤ k) :
    realElementaryBk k =
      Real.sqrt ((k : ℝ) / ((k : ℝ) - 1)) *
        gammaHalfRatioScale (((k : ℝ) - 1) / 2) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx : 0 ≤ (((k : ℝ) - 1) / 2) := by linarith
  have hkm1 : 0 ≤ (k : ℝ) - 1 := by linarith
  have hkm1pos : 0 < (k : ℝ) - 1 := by linarith
  have hratio : 0 ≤ (k : ℝ) / ((k : ℝ) - 1) := by positivity
  have hsleft :
      Real.sqrt (k : ℝ) * Real.sqrt (1 / 2 : ℝ) =
        Real.sqrt ((k : ℝ) / 2) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    congr 1
    ring
  have hsright :
      Real.sqrt ((k : ℝ) / ((k : ℝ) - 1)) *
          Real.sqrt (((k : ℝ) - 1) / 2) =
        Real.sqrt ((k : ℝ) / 2) := by
    rw [← Real.sqrt_mul hratio]
    congr 1
    field_simp [hkm1pos.ne']
  unfold realElementaryBk realAuxiliaryGammaHalfFactorReal
    gammaHalfRatioScale
  rw [← Real.sqrt_eq_rpow]
  rw [show ((k : ℝ) - 1) / 2 + 1 / 2 = (k : ℝ) / 2 by ring]
  rw [show
    Real.sqrt (k : ℝ) *
          (Real.sqrt (1 / 2 : ℝ) *
            Real.Gamma (((k : ℝ) - 1) / 2) /
            Real.Gamma ((k : ℝ) / 2)) =
      (Real.sqrt (k : ℝ) * Real.sqrt (1 / 2 : ℝ)) *
        Real.Gamma (((k : ℝ) - 1) / 2) /
        Real.Gamma ((k : ℝ) / 2) by ring]
  rw [show
    Real.sqrt ((k : ℝ) / ((k : ℝ) - 1)) *
          (Real.sqrt (((k : ℝ) - 1) / 2) *
            Real.Gamma (((k : ℝ) - 1) / 2) /
            Real.Gamma ((k : ℝ) / 2)) =
      (Real.sqrt ((k : ℝ) / ((k : ℝ) - 1)) *
          Real.sqrt (((k : ℝ) - 1) / 2)) *
        Real.Gamma (((k : ℝ) - 1) / 2) /
        Real.Gamma ((k : ℝ) / 2) by ring]
  rw [hsleft, hsright]

/-- Sharp elementary rational upper bound for the base coefficient. -/
theorem realElementaryBk_le_div
    {k : ℕ} (hk : 2 ≤ k) :
    realElementaryBk k ≤ (k : ℝ) / ((k : ℝ) - 1) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  let x : ℝ := ((k : ℝ) - 1) / 2
  let R : ℝ := (k : ℝ) / ((k : ℝ) - 1)
  have hx : 0 < x := by dsimp [x]; linarith
  have hkm1pos : 0 < (k : ℝ) - 1 := by linarith
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (by positivity) hkm1pos
  have hscaleNonneg : 0 ≤ gammaHalfRatioScale x :=
    le_trans (by norm_num) (gammaHalfRatioScale_bounds hx).1
  have hscaleSq : gammaHalfRatioScale x ^ 2 ≤ R := by
    have h := gammaHalfRatioScale_sq_le_one_add_inv_two hx
    dsimp [x, R] at h ⊢
    convert h using 1 <;> field_simp [hkm1pos.ne'] <;> ring
  rw [realElementaryBk_eq_gammaHalfRatioScale hk]
  change Real.sqrt R * gammaHalfRatioScale x ≤ R
  apply (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) hscaleNonneg) hR.le).1
  rw [mul_pow, Real.sq_sqrt hR.le]
  nlinarith

/-- Convenient dimension-free consequence `b_k <= 2`. -/
theorem realElementaryBk_le_two
    {k : ℕ} (hk : 2 ≤ k) :
    realElementaryBk k ≤ 2 := by
  calc
    realElementaryBk k ≤ (k : ℝ) / ((k : ℝ) - 1) :=
      realElementaryBk_le_div hk
    _ ≤ 2 := by
      have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hden : 0 < (k : ℝ) - 1 := by linarith
      apply (div_le_iff₀ hden).2
      linarith

/-- Squared bound for one `K_n` factor; its right-hand side telescopes. -/
theorem realElementaryKn_factor_sq_le_oddRatio
    {r : ℕ} (hr : 2 ≤ r) :
    (Real.sqrt (((2 * r - 1 : ℕ) : ℝ)) *
        realAuxiliaryGammaHalfFactorReal (2 * r - 1)) ^ 2 ≤
      ((2 * r - 1 : ℕ) : ℝ) / ((2 * r - 3 : ℕ) : ℝ) := by
  let x : ℝ := (r : ℝ) - 1
  let d : ℝ := 2 * (r : ℝ) - 1
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hx : 0 < x := by dsimp [x]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hdm2 : 0 < d - 2 := by dsimp [d]; linarith
  have hdcast : (((2 * r - 1 : ℕ) : ℝ)) = d := by
    dsimp [d]
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  have hdm2cast : (((2 * r - 3 : ℕ) : ℝ)) = d - 2 := by
    dsimp [d]
    rw [Nat.cast_sub (by omega : 3 ≤ 2 * r)]
    push_cast
    ring
  have hargNum : ((((2 * r - 1 : ℕ) : ℝ) - 1) / 2) = x := by
    rw [hdcast]
    dsimp [d, x]
    ring
  have hargDen : (((2 * r - 1 : ℕ) : ℝ) / 2) = x + 1 / 2 := by
    rw [hdcast]
    dsimp [d, x]
    ring
  have hfactorSq :
      (Real.sqrt (((2 * r - 1 : ℕ) : ℝ)) *
          realAuxiliaryGammaHalfFactorReal (2 * r - 1)) ^ 2 =
        (d / (2 * x)) * gammaHalfRatioScale x ^ 2 := by
    unfold realAuxiliaryGammaHalfFactorReal gammaHalfRatioScale
    rw [← Real.sqrt_eq_rpow, hargNum, hargDen, hdcast]
    rw [mul_pow, Real.sq_sqrt hd.le]
    simp only [mul_pow, div_pow]
    rw [Real.sq_sqrt hx.le]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    field_simp [hx.ne']
  rw [hfactorSq, hdcast, hdm2cast]
  have hscale := gammaHalfRatioScale_sq_le_one_add_inv_two hx
  have haux : 1 + 1 / (2 * x) ≤ (2 * x) / (2 * x - 1) := by
    have h2xm1 : 0 < 2 * x - 1 := by
      dsimp [x]
      linarith
    apply (le_div_iff₀ h2xm1).2
    field_simp [hx.ne']
    nlinarith
  have hscale' : gammaHalfRatioScale x ^ 2 ≤
      (2 * x) / (2 * x - 1) := hscale.trans haux
  have hcoeff : 0 ≤ d / (2 * x) := by positivity
  calc
    d / (2 * x) * gammaHalfRatioScale x ^ 2 ≤
        d / (2 * x) * ((2 * x) / (2 * x - 1)) :=
      mul_le_mul_of_nonneg_left hscale' hcoeff
    _ = d / (d - 2) := by
      have hrel : 2 * x - 1 = d - 2 := by dsimp [x, d]; ring
      rw [hrel]
      field_simp [hx.ne', hdm2.ne']

/-- Telescoping squared estimate for `K_n`. -/
theorem realElementaryKn_sq_le
    {n : ℕ} (hn : 1 ≤ n) :
    realElementaryKn n ^ 2 ≤ (((2 * n - 1 : ℕ) : ℝ)) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    realElementaryKn j ^ 2 ≤ (((2 * j - 1 : ℕ) : ℝ))
  have hP : P n hn := by
    apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
    · dsimp [P]
      simp [realElementaryKn]
    · intro j hj ih
      dsimp [P] at ih ⊢
      rw [realElementaryKn_succ j hj, mul_pow]
      have hfactor := realElementaryKn_factor_sq_le_oddRatio
        (r := j + 1) (by omega)
      have hmul :
          realElementaryKn j ^ 2 *
              (Real.sqrt (((2 * (j + 1) - 1 : ℕ) : ℝ)) *
                realAuxiliaryGammaHalfFactorReal (2 * (j + 1) - 1)) ^ 2 ≤
            (((2 * j - 1 : ℕ) : ℝ)) *
              ((((2 * (j + 1) - 1 : ℕ) : ℝ)) /
                (((2 * (j + 1) - 3 : ℕ) : ℝ))) :=
        mul_le_mul ih hfactor (sq_nonneg _) (by positivity)
      calc
        realElementaryKn j ^ 2 *
            (Real.sqrt (((2 * j + 1 : ℕ) : ℝ)) *
              realAuxiliaryGammaHalfFactorReal (2 * j + 1)) ^ 2 =
          realElementaryKn j ^ 2 *
            (Real.sqrt (((2 * (j + 1) - 1 : ℕ) : ℝ)) *
              realAuxiliaryGammaHalfFactorReal (2 * (j + 1) - 1)) ^ 2 := by
            congr 3 <;> omega
        _ ≤ (((2 * j - 1 : ℕ) : ℝ)) *
              ((((2 * (j + 1) - 1 : ℕ) : ℝ)) /
                (((2 * (j + 1) - 3 : ℕ) : ℝ))) := hmul
        _ = (((2 * (j + 1) - 1 : ℕ) : ℝ)) := by
          have hdenNat : 2 * (j + 1) - 3 = 2 * j - 1 := by omega
          rw [hdenNat]
          have hdenPos : 0 < (((2 * j - 1 : ℕ) : ℝ)) := by
            exact_mod_cast (show 0 < 2 * j - 1 by omega)
          field_simp [hdenPos.ne']
  exact hP

/-- Polynomial bound `K_n <= sqrt(2n-1)`. -/
theorem realElementaryKn_le_sqrt_odd
    {n : ℕ} (hn : 1 ≤ n) :
    realElementaryKn n ≤ Real.sqrt (((2 * n - 1 : ℕ) : ℝ)) := by
  have hK : 0 ≤ realElementaryKn n := realElementaryKn_pos.le
  have hodd : 0 ≤ (((2 * n - 1 : ℕ) : ℝ)) := by positivity
  apply (sq_le_sq₀ hK (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt hodd]
  exact realElementaryKn_sq_le hn

end

end LogdetLean.GramHafnian
