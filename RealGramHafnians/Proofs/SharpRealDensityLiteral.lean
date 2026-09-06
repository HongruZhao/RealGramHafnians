import RealGramHafnians.Proofs.SharpRealHeadlinePackaging
/-!
# Literal density conclusions for the sharp real Gram-hafnian theorem

This module records the analytic assertions about the paper's density in a
form that follows the displayed prose as closely as possible.  In particular,
it adds symmetry, two-sided boundedness of the pointwise range, and an exact
attained-supremum identity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Real ENNReal NNReal Nat

namespace LogdetLean.GramHafnian

noncomputable section

/-- A centered one-dimensional Gaussian density is an even function, also
under mathlib's zero-variance convention. -/
theorem gaussianPDFReal_zero_neg (v : ℝ≥0) (z : ℝ) :
    gaussianPDFReal 0 v (-z) = gaussianPDFReal 0 v z := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [gaussianPDFReal, gaussianPDFReal]
    congr 2
    ring

/-- The centered Gaussian-mixture density of the real Gram-hafnian is even. -/
theorem sharpRealGramHafnianDensity_neg
    {n k : ℕ} (hn : 1 ≤ n) (z : ℝ) :
    sharpRealGramHafnianDensity n k hn (-z) =
      sharpRealGramHafnianDensity n k hn z := by
  unfold sharpRealGramHafnianDensity
  apply integral_congr_ae
  filter_upwards [] with A
  exact gaussianPDFReal_zero_neg (pastRealCofactorVarianceNNReal hn A) z

/-- Function-level symmetry of the paper's density. -/
theorem even_sharpRealGramHafnianDensity
    {n k : ℕ} (hn : 1 ≤ n) :
    Function.Even (sharpRealGramHafnianDensity n k hn) := by
  intro z
  exact sharpRealGramHafnianDensity_neg hn z

/-- The full pointwise range lies in the explicit closed interval from zero
to the attained peak. -/
theorem range_sharpRealGramHafnianDensity_subset_Icc
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    Set.range (sharpRealGramHafnianDensity n k hn) ⊆
      Set.Icc 0 (sharpRealGramHafnianDensity n k hn 0) := by
  rintro _ ⟨z, rfl⟩
  exact sharpRealGramHafnianDensity_nonneg_and_le_zero hn hk hdim z

/-- Zero is an explicit lower bound for the range of the density. -/
theorem bddBelow_range_sharpRealGramHafnianDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    BddBelow (Set.range (sharpRealGramHafnianDensity n k hn)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact (sharpRealGramHafnianDensity_nonneg_and_le_zero
    hn hk hdim z).1

/-- The density range is bounded on both sides, with explicit lower and upper
bounds supplied by zero and the value at the origin. -/
theorem bddBelow_and_bddAbove_range_sharpRealGramHafnianDensity
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    BddBelow (Set.range (sharpRealGramHafnianDensity n k hn)) ∧
      BddAbove (Set.range (sharpRealGramHafnianDensity n k hn)) := by
  exact ⟨bddBelow_range_sharpRealGramHafnianDensity hn hk hdim,
    bddAbove_range_sharpRealGramHafnianDensity hn hk hdim⟩

/-- Literal attained-supremum form of
`\|f\|_∞ = f(0)`: since the density is nonnegative, the supremum of its
pointwise values is its sup norm, and the supremum is attained at zero. -/
theorem sSup_range_sharpRealGramHafnianDensity_eq_zero
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    sSup (Set.range (sharpRealGramHafnianDensity n k hn)) =
      sharpRealGramHafnianDensity n k hn 0 := by
  exact (sharpRealGramHafnianDensity_isGreatest_range hn hk hdim).csSup_eq

/-- Every absolute density value is bounded by the attained value at zero;
this is the direct pointwise sup-norm formulation. -/
theorem abs_sharpRealGramHafnianDensity_le_zero
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) (z : ℝ) :
    |sharpRealGramHafnianDensity n k hn z| ≤
      sharpRealGramHafnianDensity n k hn 0 := by
  rw [abs_of_nonneg ((sharpRealGramHafnianDensity_nonneg_and_le_zero
    hn hk hdim z).1)]
  exact (sharpRealGramHafnianDensity_nonneg_and_le_zero hn hk hdim z).2

/-- A bundled, literal certificate for every analytic density assertion in
the finite theorem of the paper. -/
structure SharpRealDensityLiteralCertificate
    (n k : ℕ) (hn : 1 ≤ n) : Prop where
  densityLaw :
    Measure.map (realGramHafnianObservable n k)
        (standardRealGaussianColumnMatrixMeasure n k) =
      volume.withDensity
        (fun z ↦ ENNReal.ofReal (sharpRealGramHafnianDensity n k hn z))
  continuous : Continuous (sharpRealGramHafnianDensity n k hn)
  even : Function.Even (sharpRealGramHafnianDensity n k hn)
  nonnegative : ∀ z, 0 ≤ sharpRealGramHafnianDensity n k hn z
  rangeInExplicitBounds :
    Set.range (sharpRealGramHafnianDensity n k hn) ⊆
      Set.Icc 0 (sharpRealGramHafnianDensity n k hn 0)
  rangeBoundedBelow :
    BddBelow (Set.range (sharpRealGramHafnianDensity n k hn))
  rangeBoundedAbove :
    BddAbove (Set.range (sharpRealGramHafnianDensity n k hn))
  maximumAtZero :
    IsGreatest (Set.range (sharpRealGramHafnianDensity n k hn))
      (sharpRealGramHafnianDensity n k hn 0)
  attainedSupremum :
    sSup (Set.range (sharpRealGramHafnianDensity n k hn)) =
      sharpRealGramHafnianDensity n k hn 0
  pointwiseSupNorm : ∀ z,
    |sharpRealGramHafnianDensity n k hn z| ≤
      sharpRealGramHafnianDensity n k hn 0
  peakBound :
    sharpRealGramHafnianDensity n k hn 0 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        sharpRealGammaCoefficientReal n k
  integrable : Integrable (sharpRealGramHafnianDensity n k hn) volume
  unitMass : ∫ z, sharpRealGramHafnianDensity n k hn z = 1

/-- All literal density assertions are simultaneously proved in the theorem
range of the paper. -/
theorem sharpRealDensityLiteralCertificate
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hdim : 2 * n - 1 ≤ k) :
    SharpRealDensityLiteralCertificate n k hn where
  densityLaw := map_realGramHafnianObservable_eq_withDensity hn hk hdim
  continuous := continuous_sharpRealGramHafnianDensity hn hk hdim
  even := even_sharpRealGramHafnianDensity hn
  nonnegative := fun z ↦
    (sharpRealGramHafnianDensity_nonneg_and_le_zero hn hk hdim z).1
  rangeInExplicitBounds :=
    range_sharpRealGramHafnianDensity_subset_Icc hn hk hdim
  rangeBoundedBelow :=
    bddBelow_range_sharpRealGramHafnianDensity hn hk hdim
  rangeBoundedAbove :=
    bddAbove_range_sharpRealGramHafnianDensity hn hk hdim
  maximumAtZero :=
    sharpRealGramHafnianDensity_isGreatest_range hn hk hdim
  attainedSupremum :=
    sSup_range_sharpRealGramHafnianDensity_eq_zero hn hk hdim
  pointwiseSupNorm := fun z ↦
    abs_sharpRealGramHafnianDensity_le_zero hn hk hdim z
  peakBound :=
    sharpRealGramHafnianDensity_zero_le_coefficientReal hn hk hdim
  integrable := integrable_sharpRealGramHafnianDensity hn hk hdim
  unitMass := integral_sharpRealGramHafnianDensity_eq_one hn hk hdim

end

end LogdetLean.GramHafnian
