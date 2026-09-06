import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealTransposeGramGood
import LogdetLean.FixedSubspaceGaussian
import LogdetLean.Coherence.GammaChernoff
import LogdetLean.Coherence.StableMatchingDirtyFiniteUnion
import LogdetLean.GramHafnian.RankOneGaussianBilinear
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLocalCofactorCompression
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic
/-!
# Elementary entry tails for a real Gaussian transpose Gram matrix

Diagonal entries are chi-square variables.  For an off-diagonal entry we
use the polarization identity with `(X+Y)/sqrt 2` and `(X-Y)/sqrt 2`; each
of these two vectors is again standard Gaussian.  Thus the same chi-square
Chernoff estimate controls every Gram entry.  A finite union bound gives the
entrywise certificate used by `RealTransposeGramGood`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace

namespace LogdetLean.GramHafnian

noncomputable section

/-- Squared Euclidean norm of a real coordinate vector. -/
def realGaussianVectorNormSq {k : ℕ} (x : Fin k → ℝ) : ℝ :=
  ∑ a : Fin k, (x a) ^ 2

@[fun_prop] theorem measurable_realGaussianVectorNormSq (k : ℕ) :
    Measurable (realGaussianVectorNormSq : (Fin k → ℝ) → ℝ) := by
  unfold realGaussianVectorNormSq
  fun_prop

/-- The squared norm of a nonzero-dimensional standard real Gaussian vector
has the chi-square Gamma law, proved from the project's internal Gaussian
norm calculation. -/
theorem hasLaw_realGaussianVectorNormSq_gamma
    {k : ℕ} (hk : 0 < k) :
    HasLaw (realGaussianVectorNormSq : (Fin k → ℝ) → ℝ)
      (gammaMeasure ((k : ℝ) / 2) (1 / 2))
      (standardRealGaussianVectorMeasure k) := by
  let E := EuclideanSpace ℝ (Fin k)
  have htoLp : HasLaw (WithLp.toLp 2 : (Fin k → ℝ) → E)
      (stdGaussian E) (standardRealGaussianVectorMeasure k) := by
    exact (measurePreserving_toLp_standardRealGaussianVector k).hasLaw
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hnorm : HasLaw (fun z : E ↦ ‖z‖ ^ 2)
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)) (stdGaussian E) := by
    have h := hasLaw_normSq_stdGaussian E
    rw [stdGaussianNormSqMeasure_eq_gamma E] at h
    simpa [E] using h
  have hcomp := hnorm.fun_comp htoLp
  convert hcomp using 1
  funext x
  simpa [realGaussianVectorNormSq] using
    (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)).symm

/-- Two-sided chi-square concentration in the coordinate-vector model. -/
theorem standardRealGaussianVector_normSq_deviation_le
    {k : ℕ} (hk : 0 < k) {eta : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    (standardRealGaussianVectorMeasure k).real
        {x : Fin k → ℝ |
          |realGaussianVectorNormSq x - (k : ℝ)| > (k : ℝ) * eta} ≤
      2 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
  let mu := standardRealGaussianVectorMeasure k
  let lower : Set ℝ := {x | x ≤ (k : ℝ) * (1 - eta)}
  let upper : Set ℝ := {x | (k : ℝ) * (1 + eta) ≤ x}
  let bad : Set ℝ := {x | |x - (k : ℝ)| > (k : ℝ) * eta}
  letI : IsProbabilityMeasure (gammaMeasure ((k : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have hbad : bad ⊆ lower ∪ upper := by
    intro x hx
    change |x - (k : ℝ)| > (k : ℝ) * eta at hx
    rcases (lt_abs.mp hx) with hx | hx
    · right
      change (k : ℝ) * (1 + eta) ≤ x
      ring_nf at hx ⊢
      linarith
    · left
      change x ≤ (k : ℝ) * (1 - eta)
      ring_nf at hx ⊢
      linarith
  have hlower := LogdetLean.Coherence.chiSquare_lowerTail_le hk heta0
  have hupper := LogdetLean.Coherence.chiSquare_upperTail_le hk heta0 heta1
  have hlowerWeak :
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real lower ≤
        Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
    calc
      _ ≤ Real.exp (-((k : ℝ) * eta ^ 2 / 4)) := by
        simpa [lower] using hlower
      _ ≤ Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
        apply Real.exp_le_exp.mpr
        have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith [mul_nonneg hkR (sq_nonneg eta)]
  have hgamma :
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real bad ≤
        2 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
    calc
      _ ≤ (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real (lower ∪ upper) :=
        measureReal_mono hbad (measure_ne_top _ _)
      _ ≤ (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real lower +
          (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real upper :=
        measureReal_union_le _ _
      _ ≤ Real.exp (-((k : ℝ) * eta ^ 2 / 8)) +
          Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
        exact add_le_add hlowerWeak (by simpa [upper] using hupper)
      _ = 2 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by ring
  have hlaw := hasLaw_realGaussianVectorNormSq_gamma hk
  have heq := hlaw.measureReal_eq
    (p := fun x : ℝ ↦ |x - (k : ℝ)| > (k : ℝ) * eta) (by
      exact measurableSet_lt measurable_const
        ((measurable_id'.sub_const _).abs))
  change (standardRealGaussianVectorMeasure k).real
      {x | |realGaussianVectorNormSq x - (k : ℝ)| > (k : ℝ) * eta} =
    (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real bad at heq
  rw [heq]
  exact hgamma

/-- The coefficient `sqrt(1/2)` used in the polarization argument. -/
def realGaussianPolarizationScale : ℝ := Real.sqrt (1 / 2 : ℝ)

theorem realGaussianPolarizationScale_pos :
    0 < realGaussianPolarizationScale := by
  unfold realGaussianPolarizationScale
  positivity

theorem realGaussianPolarizationScale_sq :
    realGaussianPolarizationScale ^ 2 = (1 / 2 : ℝ) := by
  unfold realGaussianPolarizationScale
  rw [Real.sq_sqrt]
  norm_num

theorem abs_realGaussianPolarizationScale_lt_one :
    |realGaussianPolarizationScale| < 1 := by
  rw [abs_of_pos realGaussianPolarizationScale_pos]
  have hsq := realGaussianPolarizationScale_sq
  nlinarith [sq_nonneg (realGaussianPolarizationScale - 1)]

theorem sqrt_one_sub_realGaussianPolarizationScale_sq :
    Real.sqrt (1 - realGaussianPolarizationScale ^ 2) =
      realGaussianPolarizationScale := by
  rw [realGaussianPolarizationScale_sq]
  norm_num [realGaussianPolarizationScale]

/-- Euclidean mixed vector with correlation parameter `rho`, evaluated on
two raw Gaussian coordinate fields. -/
def realGaussianMixedVector {k : ℕ} (rho : ℝ)
    (p : (Fin k → ℝ) × (Fin k → ℝ)) : EuclideanSpace ℝ (Fin k) :=
  LogdetLean.Coherence.correlatedSecondColumn rho
    (WithLp.toLp 2 p.1) (WithLp.toLp 2 p.2)

@[fun_prop] theorem measurable_realGaussianMixedVector (k : ℕ) (rho : ℝ) :
    Measurable (realGaussianMixedVector (k := k) rho) := by
  unfold realGaussianMixedVector LogdetLean.Coherence.correlatedSecondColumn
  fun_prop

/-- Every strict normalized mixture of two independent standard real
Gaussian vectors is standard Gaussian. -/
theorem hasLaw_realGaussianMixedVector_stdGaussian
    {k : ℕ} (rho : ℝ) (hrho : |rho| < 1) :
    HasLaw (realGaussianMixedVector (k := k) rho)
      (stdGaussian (EuclideanSpace ℝ (Fin k)))
      ((standardRealGaussianVectorMeasure k).prod
        (standardRealGaussianVectorMeasure k)) := by
  let rawToEuclidean :
      ((Fin k → ℝ) × (Fin k → ℝ)) →
        (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
    Prod.map (WithLp.toLp 2) (WithLp.toLp 2)
  let mixed :
      (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) →
        EuclideanSpace ℝ (Fin k) :=
    LogdetLean.Coherence.stableMatchingPairColumn rho 1
  have hraw : HasLaw rawToEuclidean
      ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin k))))
      ((standardRealGaussianVectorMeasure k).prod
        (standardRealGaussianVectorMeasure k)) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [rawToEuclidean, twoRealGaussianFieldsMeasure] using
      (map_twoRealFields_toLp_eq_prod_stdGaussian k)
  have hmix : HasLaw mixed (stdGaussian (EuclideanSpace ℝ (Fin k)))
      ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
    refine ⟨(LogdetLean.Coherence.measurable_stableMatchingPairColumn
      (E := EuclideanSpace ℝ (Fin k)) rho 1).aemeasurable, ?_⟩
    simpa [mixed] using
      (LogdetLean.Coherence.map_stableMatchingPairColumn_eq_stdGaussian
        (m := k) rho hrho 1)
  have hcomp := hmix.fun_comp hraw
  change HasLaw
    (fun p : (Fin k → ℝ) × (Fin k → ℝ) ↦
      LogdetLean.Coherence.correlatedSecondColumn rho
        (WithLp.toLp 2 p.1) (WithLp.toLp 2 p.2))
      (stdGaussian (EuclideanSpace ℝ (Fin k)))
      ((standardRealGaussianVectorMeasure k).prod
        (standardRealGaussianVectorMeasure k))
  simpa [rawToEuclidean, mixed,
    LogdetLean.Coherence.stableMatchingPairColumn] using hcomp

/-- Squared norm of the mixed Euclidean vector. -/
def realGaussianMixedNormSq {k : ℕ} (rho : ℝ)
    (p : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  ‖realGaussianMixedVector rho p‖ ^ 2

@[fun_prop] theorem measurable_realGaussianMixedNormSq (k : ℕ) (rho : ℝ) :
    Measurable (realGaussianMixedNormSq (k := k) rho) := by
  unfold realGaussianMixedNormSq
  fun_prop

theorem hasLaw_realGaussianMixedNormSq_gamma
    {k : ℕ} (hk : 0 < k) (rho : ℝ) (hrho : |rho| < 1) :
    HasLaw (realGaussianMixedNormSq (k := k) rho)
      (gammaMeasure ((k : ℝ) / 2) (1 / 2))
      ((standardRealGaussianVectorMeasure k).prod
        (standardRealGaussianVectorMeasure k)) := by
  let E := EuclideanSpace ℝ (Fin k)
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hnorm : HasLaw (fun z : E ↦ ‖z‖ ^ 2)
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)) (stdGaussian E) := by
    have h := hasLaw_normSq_stdGaussian E
    rw [stdGaussianNormSqMeasure_eq_gamma E] at h
    simpa [E] using h
  have hmix := hasLaw_realGaussianMixedVector_stdGaussian
    (k := k) rho hrho
  have hcomp := hnorm.fun_comp hmix
  change HasLaw (fun p : (Fin k → ℝ) × (Fin k → ℝ) ↦
      ‖realGaussianMixedVector rho p‖ ^ 2)
    (gammaMeasure ((k : ℝ) / 2) (1 / 2))
    ((standardRealGaussianVectorMeasure k).prod
      (standardRealGaussianVectorMeasure k))
  exact hcomp

theorem realGaussianMixed_normSq_deviation_le
    {k : ℕ} (hk : 0 < k) (rho : ℝ) (hrho : |rho| < 1)
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    ((standardRealGaussianVectorMeasure k).prod
      (standardRealGaussianVectorMeasure k)).real
        {p | |realGaussianMixedNormSq rho p - (k : ℝ)| >
          (k : ℝ) * eta} ≤
      2 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
  let bad : Set ℝ :=
    {x | |x - (k : ℝ)| > (k : ℝ) * eta}
  have hbad : MeasurableSet bad := by
    dsimp [bad]
    exact measurableSet_lt measurable_const
      ((measurable_id'.sub_const _).abs)
  have hmixed := (hasLaw_realGaussianMixedNormSq_gamma hk rho hrho).measureReal_eq hbad
  have hraw := (hasLaw_realGaussianVectorNormSq_gamma hk).measureReal_eq hbad
  change ((standardRealGaussianVectorMeasure k).prod
      (standardRealGaussianVectorMeasure k)).real
        {p | |realGaussianMixedNormSq rho p - (k : ℝ)| >
          (k : ℝ) * eta} =
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real bad at hmixed
  change (standardRealGaussianVectorMeasure k).real
        {x | |realGaussianVectorNormSq x - (k : ℝ)| >
          (k : ℝ) * eta} =
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real bad at hraw
  rw [hmixed, ← hraw]
  exact standardRealGaussianVector_normSq_deviation_le hk heta0 heta1

/-- Inner product of two raw real coordinate vectors. -/
def realGaussianPairInner {k : ℕ}
    (p : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  ∑ a : Fin k, p.1 a * p.2 a

@[fun_prop] theorem measurable_realGaussianPairInner (k : ℕ) :
    Measurable (realGaussianPairInner :
      ((Fin k → ℝ) × (Fin k → ℝ)) → ℝ) := by
  unfold realGaussianPairInner
  fun_prop

/-- Polarization identity for the two normalized Gaussian mixtures. -/
theorem realGaussianMixedNormSq_sub_neg_eq_two_pairInner
    {k : ℕ} (p : (Fin k → ℝ) × (Fin k → ℝ)) :
    realGaussianMixedNormSq realGaussianPolarizationScale p -
        realGaussianMixedNormSq (-realGaussianPolarizationScale) p =
      2 * realGaussianPairInner p := by
  let q := realGaussianPolarizationScale
  let x : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 p.1
  let y : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 p.2
  have hqpos : 0 < q := realGaussianPolarizationScale_pos
  have hq : q ^ 2 = (1 / 2 : ℝ) := realGaussianPolarizationScale_sq
  have hsqrt : Real.sqrt (1 - q ^ 2) = q :=
    sqrt_one_sub_realGaussianPolarizationScale_sq
  have hsqrtNeg : Real.sqrt (1 - (-q) ^ 2) = q := by
    simpa only [neg_sq] using hsqrt
  unfold realGaussianMixedNormSq realGaussianMixedVector
    LogdetLean.Coherence.correlatedSecondColumn
  change ‖q • x + Real.sqrt (1 - q ^ 2) • y‖ ^ 2 -
      ‖(-q) • x + Real.sqrt (1 - (-q) ^ 2) • y‖ ^ 2 = _
  rw [hsqrt, hsqrtNeg, norm_add_sq_real, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hqpos,
    abs_neg, inner_smul_left, inner_smul_right, starRingEnd_apply,
    star_trivial]
  rw [inner_toLp_eq_bilinearDot]
  change _ = 2 * (∑ a : Fin k, p.1 a * p.2 a)
  unfold bilinearDot
  calc
    (q * ‖x‖) ^ 2 +
          2 * (q * (q * ∑ i : Fin k, p.1 i * p.2 i)) +
          (q * ‖y‖) ^ 2 -
        ((q * ‖x‖) ^ 2 +
          2 * (q * (-q * ∑ i : Fin k, p.1 i * p.2 i)) +
          (q * ‖y‖) ^ 2) =
        4 * q ^ 2 * (∑ i : Fin k, p.1 i * p.2 i) := by ring
    _ = 2 * (∑ i : Fin k, p.1 i * p.2 i) := by rw [hq]; ring

/-- Off-diagonal inner-product tail under two independent standard real
Gaussian vectors. -/
theorem twoStandardRealGaussianVectors_inner_deviation_le
    {k : ℕ} (hk : 0 < k) {eta : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    ((standardRealGaussianVectorMeasure k).prod
      (standardRealGaussianVectorMeasure k)).real
        {p | |realGaussianPairInner p| > (k : ℝ) * eta} ≤
      4 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
  let mu := (standardRealGaussianVectorMeasure k).prod
    (standardRealGaussianVectorMeasure k)
  let q := realGaussianPolarizationScale
  let plusBad : Set ((Fin k → ℝ) × (Fin k → ℝ)) :=
    {p | |realGaussianMixedNormSq q p - (k : ℝ)| > (k : ℝ) * eta}
  let minusBad : Set ((Fin k → ℝ) × (Fin k → ℝ)) :=
    {p | |realGaussianMixedNormSq (-q) p - (k : ℝ)| > (k : ℝ) * eta}
  have hsubset : {p | |realGaussianPairInner p| > (k : ℝ) * eta} ⊆
      plusBad ∪ minusBad := by
    intro p hp
    by_contra hpUnion
    have hpPlus :
        |realGaussianMixedNormSq q p - (k : ℝ)| ≤ (k : ℝ) * eta := by
      simpa [plusBad] using (not_lt.mp fun h ↦ hpUnion (Or.inl h))
    have hpMinus :
        |realGaussianMixedNormSq (-q) p - (k : ℝ)| ≤ (k : ℝ) * eta := by
      simpa [minusBad] using (not_lt.mp fun h ↦ hpUnion (Or.inr h))
    have hdiff := abs_sub_le
      (realGaussianMixedNormSq q p) (k : ℝ)
      (realGaussianMixedNormSq (-q) p)
    rw [realGaussianMixedNormSq_sub_neg_eq_two_pairInner] at hdiff
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hdiff
    have hminusAbs :
        |(k : ℝ) - realGaussianMixedNormSq (-q) p| =
          |realGaussianMixedNormSq (-q) p - (k : ℝ)| :=
      abs_sub_comm _ _
    rw [hminusAbs] at hdiff
    have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hetaK : 0 ≤ (k : ℝ) * eta := mul_nonneg hkR heta0
    change |realGaussianPairInner p| > (k : ℝ) * eta at hp
    nlinarith [abs_nonneg (realGaussianPairInner p)]
  have hplus := realGaussianMixed_normSq_deviation_le hk q
    abs_realGaussianPolarizationScale_lt_one heta0 heta1
  have hminus := realGaussianMixed_normSq_deviation_le hk (-q)
    (by simpa [q] using abs_realGaussianPolarizationScale_lt_one) heta0 heta1
  calc
    mu.real {p | |realGaussianPairInner p| > (k : ℝ) * eta} ≤
        mu.real (plusBad ∪ minusBad) := measureReal_mono hsubset
    _ ≤ mu.real plusBad + mu.real minusBad := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) +
        2 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
      exact add_le_add (by simpa [mu, plusBad, q] using hplus)
        (by simpa [mu, minusBad, q] using hminus)
    _ = 4 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by ring

section ColumnFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def standardRealGaussianColumnFamilyMeasure (ι : Type*) [Fintype ι]
    (k : ℕ) : Measure (ι → Fin k → ℝ) :=
  Measure.pi fun _ : ι ↦ standardRealGaussianVectorMeasure k

instance (k : ℕ) : IsProbabilityMeasure
    (standardRealGaussianColumnFamilyMeasure ι k) := by
  unfold standardRealGaussianColumnFamilyMeasure
  infer_instance

/-- A single centered Gram entry exceeds the common entrywise threshold. -/
def realTransposeGramEntryBad (k : ℕ) (delta : ℝ) (i j : ι) :
    Set (ι → Fin k → ℝ) :=
  {A | delta * (k : ℝ) / (Fintype.card ι : ℝ) <
    |centeredRealTransposeGramEntry k A i j|}

theorem measurableSet_realTransposeGramEntryBad
    (k : ℕ) (delta : ℝ) (i j : ι) :
    MeasurableSet (realTransposeGramEntryBad (ι := ι) k delta i j) := by
  unfold realTransposeGramEntryBad centeredRealTransposeGramEntry
    realTransposeGramEntry
  exact measurableSet_lt measurable_const
    ((by fun_prop : Measurable (fun A : ι → Fin k → ℝ ↦
      (∑ a : Fin k, A i a * A j a) -
        if i = j then (k : ℝ) else 0)).abs)

/-- Every diagonal or off-diagonal transpose-Gram entry has the common
conservative envelope `4 exp(-k (delta/m)^2 / 8)`. -/
theorem standardRealGaussianColumnFamily_entryBad_le
    {k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) (i j : ι) :
    (standardRealGaussianColumnFamilyMeasure ι k).real
        (realTransposeGramEntryBad k delta i j) ≤
      4 * Real.exp (-((k : ℝ) *
        (delta / (Fintype.card ι : ℝ)) ^ 2 / 8)) := by
  let m : ℝ := Fintype.card ι
  let eta : ℝ := delta / m
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have heta0 : 0 ≤ eta := div_nonneg hdelta0 (by positivity)
  have heta1 : eta ≤ 1 := by
    dsimp [eta]
    exact (div_le_one (by positivity : 0 < m)).mpr (hdelta1.trans hm)
  let mu := standardRealGaussianColumnFamilyMeasure ι k
  by_cases hij : i = j
  · subst j
    have heval : HasLaw (fun A : ι → Fin k → ℝ ↦ A i)
        (standardRealGaussianVectorMeasure k) mu := by
      exact (measurePreserving_eval
        (fun _ : ι ↦ standardRealGaussianVectorMeasure k) i).hasLaw
    let badVec : Set (Fin k → ℝ) :=
      {x | |realGaussianVectorNormSq x - (k : ℝ)| > (k : ℝ) * eta}
    have hmeas : MeasurableSet badVec := by
      dsimp [badVec]
      exact measurableSet_lt measurable_const
        ((measurable_realGaussianVectorNormSq k).sub_const _).abs
    have heq := heval.measureReal_eq
      (p := fun x : Fin k → ℝ ↦ x ∈ badVec) hmeas
    have htail := standardRealGaussianVector_normSq_deviation_le
      hk heta0 heta1
    have hset : realTransposeGramEntryBad (ι := ι) k delta i i =
        {A : ι → Fin k → ℝ | A i ∈ badVec} := by
      ext A
      simp only [realTransposeGramEntryBad, Set.mem_setOf_eq, badVec,
        centeredRealTransposeGramEntry, if_pos, realTransposeGramEntry,
        realGaussianVectorNormSq]
      dsimp [eta, m]
      have hthreshold :
          delta * (k : ℝ) / (Fintype.card ι : ℝ) =
            (k : ℝ) * (delta / (Fintype.card ι : ℝ)) := by ring
      rw [hthreshold]
      simp [pow_two]
    rw [hset, heq]
    calc
      _ ≤ 2 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := htail
      _ ≤ 4 * Real.exp (-((k : ℝ) * eta ^ 2 / 8)) := by
        nlinarith [Real.exp_pos (-((k : ℝ) * eta ^ 2 / 8))]
      _ = 4 * Real.exp (-((k : ℝ) *
          (delta / (Fintype.card ι : ℝ)) ^ 2 / 8)) := by rfl
  · have hcoords : iIndepFun
        (fun a (A : ι → Fin k → ℝ) ↦ A a) mu := by
      exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
    have hind := hcoords.indepFun hij
    have hiLaw : HasLaw (fun A : ι → Fin k → ℝ ↦ A i)
        (standardRealGaussianVectorMeasure k) mu :=
      (measurePreserving_eval
        (fun _ : ι ↦ standardRealGaussianVectorMeasure k) i).hasLaw
    have hjLaw : HasLaw (fun A : ι → Fin k → ℝ ↦ A j)
        (standardRealGaussianVectorMeasure k) mu :=
      (measurePreserving_eval
        (fun _ : ι ↦ standardRealGaussianVectorMeasure k) j).hasLaw
    have hpair : HasLaw
        (fun A : ι → Fin k → ℝ ↦ (A i, A j))
        ((standardRealGaussianVectorMeasure k).prod
          (standardRealGaussianVectorMeasure k)) mu :=
      hind.hasLaw_prod hiLaw hjLaw
    let badPair : Set ((Fin k → ℝ) × (Fin k → ℝ)) :=
      {p | |realGaussianPairInner p| > (k : ℝ) * eta}
    have hmeas : MeasurableSet badPair := by
      dsimp [badPair]
      exact measurableSet_lt measurable_const
        (measurable_realGaussianPairInner k).abs
    have heq := hpair.measureReal_eq
      (p := fun p : (Fin k → ℝ) × (Fin k → ℝ) ↦ p ∈ badPair) hmeas
    have htail := twoStandardRealGaussianVectors_inner_deviation_le
      hk heta0 heta1
    have hset : realTransposeGramEntryBad (ι := ι) k delta i j =
        {A : ι → Fin k → ℝ | (A i, A j) ∈ badPair} := by
      ext A
      simp only [realTransposeGramEntryBad, Set.mem_setOf_eq, badPair,
        centeredRealTransposeGramEntry, if_neg hij,
        sub_zero, realTransposeGramEntry, realGaussianPairInner]
      dsimp [eta, m]
      have hthreshold :
          delta * (k : ℝ) / (Fintype.card ι : ℝ) =
            (k : ℝ) * (delta / (Fintype.card ι : ℝ)) := by ring
      rw [hthreshold]
    rw [hset, heq]
    simpa [eta, m] using htail

/-- Failure of the entrywise certificate is the union of the entry failures. -/
theorem not_realTransposeGramGood_set_eq_iUnion_entryBad
    (k : ℕ) (delta : ℝ) :
    {A : ι → Fin k → ℝ | ¬ realTransposeGramGood k delta A} =
      ⋃ i : ι, ⋃ j : ι, realTransposeGramEntryBad k delta i j := by
  ext A
  simp only [realTransposeGramGood, realTransposeGramEntryBad,
    Set.mem_setOf_eq, Set.mem_iUnion, not_forall, not_le]

/-- Finite-union bound for the full entrywise Gram certificate.  The factor
`4 m^2` is deliberately conservative; it avoids choosing an ordering on the
generic column index type while retaining the required polynomial scale. -/
theorem standardRealGaussianColumnFamily_not_good_le
    {k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (standardRealGaussianColumnFamilyMeasure ι k).real
        {A | ¬ realTransposeGramGood k delta A} ≤
      4 * (Fintype.card ι : ℝ) ^ 2 *
        Real.exp (-((k : ℝ) *
          (delta / (Fintype.card ι : ℝ)) ^ 2 / 8)) := by
  let mu := standardRealGaussianColumnFamilyMeasure ι k
  let B := Real.exp (-((k : ℝ) *
    (delta / (Fintype.card ι : ℝ)) ^ 2 / 8))
  rw [not_realTransposeGramGood_set_eq_iUnion_entryBad]
  calc
    mu.real (⋃ i : ι, ⋃ j : ι, realTransposeGramEntryBad k delta i j) ≤
        ∑ i : ι, mu.real (⋃ j : ι,
          realTransposeGramEntryBad k delta i j) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : ι, ∑ j : ι,
        mu.real (realTransposeGramEntryBad k delta i j) := by
      gcongr with i
      exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : ι, ∑ _j : ι, 4 * B := by
      gcongr with i j
      exact standardRealGaussianColumnFamily_entryBad_le
        hk hdelta0 hdelta1 i j
    _ = 4 * (Fintype.card ι : ℝ) ^ 2 * B := by
      simp [B]
      ring

/-- ENNReal form used directly by the fractional-resolvent recurrence. -/
theorem standardRealGaussianColumnFamily_not_good_le_ennreal
    {k : ℕ} (hk : 0 < k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (standardRealGaussianColumnFamilyMeasure ι k)
        {A | ¬ realTransposeGramGood k delta A} ≤
      ENNReal.ofReal
        (4 * (Fintype.card ι : ℝ) ^ 2 *
          Real.exp (-((k : ℝ) *
            (delta / (Fintype.card ι : ℝ)) ^ 2 / 8))) := by
  apply (ENNReal.toReal_le_toReal
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal]
  · exact standardRealGaussianColumnFamily_not_good_le
      hk hdelta0 hdelta1
  · positivity

end ColumnFamily

end

end LogdetLean.GramHafnian
