import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.BilinearGaussianKernel
/-!
# Finite Fourier-coordinate compression

This file isolates the finite descent argument used after the analytic
two-coordinate estimate.  A local compression step preserves the squared
Euclidean radius and strictly decreases the number of nonzero coordinates.
Consequently it terminates at a singleton.  Coordinate exchangeability and
common-phase invariance identify every singleton with the positive radial
axis.
-/

open Complex
open scoped BigOperators Real

namespace LogdetLean.GramHafnian

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A vector supported at one Fourier coordinate. -/
def singleCoordinate (i : ι) (c : ℂ) : ι → ℂ :=
  fun j => if j = i then c else 0

/-- The finite support of a Fourier vector. -/
def coordinateSupport (z : ι → ℂ) : Finset ι :=
  Finset.univ.filter fun i => z i ≠ 0

/-- Number of nonzero Fourier coordinates. -/
def coordinateSupportCard (z : ι → ℂ) : ℕ :=
  (coordinateSupport z).card

/-- Squared Euclidean radius, written with `Complex.normSq` so that it is
algebraic and manifestly nonnegative. -/
def coordinateEnergy (z : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (z i)

/-- Common multiplication of all Fourier coordinates by one phase. -/
def phaseCoordinates (q : ℂ) (z : ι → ℂ) : ι → ℂ :=
  fun i => q * z i

/-- The singleton has the expected support values. -/
@[simp] theorem singleCoordinate_apply_self (i : ι) (c : ℂ) :
    singleCoordinate i c i = c := by
  simp [singleCoordinate]

@[simp] theorem singleCoordinate_apply_of_ne
    {i j : ι} (hji : j ≠ i) (c : ℂ) :
    singleCoordinate i c j = 0 := by
  simp [singleCoordinate, hji]

/-- Exact energy of a singleton Fourier vector. -/
@[simp] theorem coordinateEnergy_singleCoordinate (i : ι) (c : ℂ) :
    coordinateEnergy (singleCoordinate i c) = Complex.normSq c := by
  unfold coordinateEnergy singleCoordinate
  classical
  calc
    (∑ j, Complex.normSq (if j = i then c else 0)) =
        Complex.normSq (if i = i then c else 0) := by
      apply Finset.sum_eq_single (s := Finset.univ) i
      · intro j hj hji
        simp [hji]
      · simp
    _ = Complex.normSq c := by simp

/-- The Fourier energy is always nonnegative. -/
theorem coordinateEnergy_nonneg (z : ι → ℂ) :
    0 ≤ coordinateEnergy z := by
  unfold coordinateEnergy
  exact Finset.sum_nonneg fun i hi => Complex.normSq_nonneg (z i)

/-- The symmetry property actually needed at the terminal step: singleton
coordinates may be exchanged without changing the characteristic function. -/
def SingletonExchangeable (Φ : (ι → ℂ) → ℂ) : Prop :=
  ∀ i j c, Φ (singleCoordinate i c) = Φ (singleCoordinate j c)

/-- Common-phase invariance of a characteristic function. -/
def CommonPhaseInvariant (Φ : (ι → ℂ) → ℂ) : Prop :=
  ∀ (q : ℂ), ‖q‖ = 1 → ∀ z, Φ (phaseCoordinates q z) = Φ z

/-- A nonzero scalar can be rotated to its positive modulus by a unit complex
phase. -/
theorem exists_unit_phase_mul_eq_norm {c : ℂ} (hc : c ≠ 0) :
    ∃ q : ℂ, ‖q‖ = 1 ∧ q * c = (‖c‖ : ℝ) := by
  refine ⟨((‖c‖ : ℝ) : ℂ) / c, ?_, ?_⟩
  · rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg c), div_self]
    exact norm_ne_zero_iff.mpr hc
  · exact div_mul_cancel₀ _ hc

/-- Common phase rotation sends a singleton to the singleton with rotated
coefficient. -/
theorem phaseCoordinates_singleCoordinate
    (q c : ℂ) (i : ι) :
    phaseCoordinates q (singleCoordinate i c) =
      singleCoordinate i (q * c) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [phaseCoordinates]
  · simp [phaseCoordinates, singleCoordinate, hji]

/-- Exchangeability and common-phase invariance identify all singleton
values with the singleton on a fixed base coordinate having positive real
amplitude. -/
theorem norm_singleton_eq_positive_base
    [Nonempty ι] (Φ : (ι → ℂ) → ℂ) (base i : ι) (c : ℂ)
    (hexchange : SingletonExchangeable Φ)
    (hphase : CommonPhaseInvariant Φ) :
    ‖Φ (singleCoordinate i c)‖ =
      ‖Φ (singleCoordinate base (‖c‖ : ℝ))‖ := by
  by_cases hc : c = 0
  · subst c
    simpa using congrArg norm (hexchange i base 0)
  · obtain ⟨q, hq, hqc⟩ := exists_unit_phase_mul_eq_norm hc
    have hrotate := hphase q hq (singleCoordinate i c)
    rw [phaseCoordinates_singleCoordinate, hqc] at hrotate
    calc
      ‖Φ (singleCoordinate i c)‖ =
          ‖Φ (singleCoordinate i (‖c‖ : ℝ))‖ := by
            rw [hrotate]
      _ = ‖Φ (singleCoordinate base (‖c‖ : ℝ))‖ := by
            rw [hexchange i base]

/-- A vector whose support has at most one element is a singleton vector
(possibly with zero coefficient). -/
theorem eq_singleCoordinate_of_coordinateSupportCard_le_one
    [Nonempty ι] {z : ι → ℂ} (hz : coordinateSupportCard z ≤ 1) :
    ∃ i : ι, z = singleCoordinate i (z i) := by
  have hcard : (coordinateSupport z).card ≤ 1 := hz
  obtain ⟨i, hi⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
  refine ⟨i, ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · have hzj : z j = 0 := by
      by_contra hjzero
      have hjmem : j ∈ coordinateSupport z := by
        simp [coordinateSupport, hjzero]
      have : j ∈ ({i} : Finset ι) := hi hjmem
      simpa using hji (Finset.mem_singleton.mp this)
    simp [singleCoordinate, hji, hzj]

/-- Terminal radial identification for every vector with at most one nonzero
coordinate. -/
theorem norm_eq_radial_of_coordinateSupportCard_le_one
    [Nonempty ι] (Φ : (ι → ℂ) → ℂ) (base : ι) (z : ι → ℂ)
    (hexchange : SingletonExchangeable Φ)
    (hphase : CommonPhaseInvariant Φ)
    (hz : coordinateSupportCard z ≤ 1) :
    ‖Φ z‖ =
      ‖Φ (singleCoordinate base (Real.sqrt (coordinateEnergy z) : ℝ))‖ := by
  obtain ⟨i, hzi⟩ :=
    eq_singleCoordinate_of_coordinateSupportCard_le_one hz
  have henergy : coordinateEnergy z = Complex.normSq (z i) := by
    conv_lhs => rw [hzi]
    rw [coordinateEnergy_singleCoordinate]
  calc
    ‖Φ z‖ = ‖Φ (singleCoordinate i (z i))‖ :=
      congrArg norm (congrArg Φ hzi)
    _ = ‖Φ (singleCoordinate base (‖z i‖ : ℝ))‖ :=
      norm_singleton_eq_positive_base Φ base i _ hexchange hphase
    _ = ‖Φ (singleCoordinate base
          (Real.sqrt (coordinateEnergy z) : ℝ))‖ := by
      congr 2
      rw [henergy, Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg _)]

/-- Finite-coordinate compression iteration.

The hypothesis `hstep` is the directly instantiable output of the analytic
two-coordinate argument: whenever at least two coordinates are nonzero, it
selects one of the two positive endpoints.  That endpoint has smaller
support, exactly the same squared radius, and no smaller characteristic
function modulus. -/
theorem finite_coordinate_compression_iteration
    [Nonempty ι] (Φ : (ι → ℂ) → ℂ) (base : ι)
    (hexchange : SingletonExchangeable Φ)
    (hphase : CommonPhaseInvariant Φ)
    (hstep : ∀ z : ι → ℂ, 1 < coordinateSupportCard z →
      ∃ z' : ι → ℂ,
        coordinateSupportCard z' < coordinateSupportCard z ∧
        coordinateEnergy z' = coordinateEnergy z ∧
        ‖Φ z‖ ≤ ‖Φ z'‖) :
    ∀ z : ι → ℂ,
      ‖Φ z‖ ≤
        ‖Φ (singleCoordinate base
          (Real.sqrt (coordinateEnergy z) : ℝ))‖ := by
  intro z
  generalize hn : coordinateSupportCard z = n
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
      by_cases hterminal : n ≤ 1
      · have hzterminal : coordinateSupportCard z ≤ 1 := by
          simpa [hn] using hterminal
        exact (norm_eq_radial_of_coordinateSupportCard_le_one
          Φ base z hexchange hphase hzterminal).le
      · have htwo : 1 < coordinateSupportCard z := by
          rw [hn]
          omega
        obtain ⟨z', hsupp, henergy, hbound⟩ := hstep z htwo
        calc
          ‖Φ z‖ ≤ ‖Φ z'‖ := hbound
          _ ≤ ‖Φ (singleCoordinate base
              (Real.sqrt (coordinateEnergy z') : ℝ))‖ := by
            apply ih (coordinateSupportCard z')
            · simpa [hn] using hsupp
            · rfl
          _ = ‖Φ (singleCoordinate base
              (Real.sqrt (coordinateEnergy z) : ℝ))‖ := by
            rw [henergy]

/-- Select one of two compressed endpoints.  This is the elementary `max`
step immediately following Hölder in the paper. -/
theorem compressionStep_of_two_endpoints
    (Φ : (ι → ℂ) → ℂ) {z zLeft zRight : ι → ℂ}
    (hsuppLeft : coordinateSupportCard zLeft < coordinateSupportCard z)
    (hsuppRight : coordinateSupportCard zRight < coordinateSupportCard z)
    (henergyLeft : coordinateEnergy zLeft = coordinateEnergy z)
    (henergyRight : coordinateEnergy zRight = coordinateEnergy z)
    (hbound : ‖Φ z‖ ≤ max ‖Φ zLeft‖ ‖Φ zRight‖) :
    ∃ z' : ι → ℂ,
      coordinateSupportCard z' < coordinateSupportCard z ∧
      coordinateEnergy z' = coordinateEnergy z ∧
      ‖Φ z‖ ≤ ‖Φ z'‖ := by
  by_cases hle : ‖Φ zLeft‖ ≤ ‖Φ zRight‖
  · refine ⟨zRight, hsuppRight, henergyRight, ?_⟩
    simpa [max_eq_right hle] using hbound
  · have hge : ‖Φ zRight‖ ≤ ‖Φ zLeft‖ := le_of_not_ge hle
    refine ⟨zLeft, hsuppLeft, henergyLeft, ?_⟩
    simpa [max_eq_left hge] using hbound

/-- Direct two-endpoint form of finite-coordinate compression.  An analytic
application supplies the two endpoint vectors and the `max` inequality;
this theorem performs all remaining finite iteration and symmetry reduction. -/
theorem finite_coordinate_compression_of_two_endpoints
    [Nonempty ι] (Φ : (ι → ℂ) → ℂ) (base : ι)
    (hexchange : SingletonExchangeable Φ)
    (hphase : CommonPhaseInvariant Φ)
    (htwo : ∀ z : ι → ℂ, 1 < coordinateSupportCard z →
      ∃ zLeft zRight : ι → ℂ,
        coordinateSupportCard zLeft < coordinateSupportCard z ∧
        coordinateSupportCard zRight < coordinateSupportCard z ∧
        coordinateEnergy zLeft = coordinateEnergy z ∧
        coordinateEnergy zRight = coordinateEnergy z ∧
        ‖Φ z‖ ≤ max ‖Φ zLeft‖ ‖Φ zRight‖) :
    ∀ z : ι → ℂ,
      ‖Φ z‖ ≤
        ‖Φ (singleCoordinate base
          (Real.sqrt (coordinateEnergy z) : ℝ))‖ := by
  apply finite_coordinate_compression_iteration Φ base hexchange hphase
  intro z hz
  obtain ⟨zLeft, zRight, hsLeft, hsRight, heLeft, heRight, hmax⟩ :=
    htwo z hz
  exact compressionStep_of_two_endpoints Φ hsLeft hsRight heLeft heRight hmax

/-- Fully radial endpoint.  If the singleton characteristic function is a
nonnegative real function `radial`, the modulus on the radial axis can be
removed.  This is the form consumed by Gaussian Fourier averaging. -/
theorem finite_coordinate_compression_to_radial
    [Nonempty ι] (Φ : (ι → ℂ) → ℂ) (base : ι)
    (radial : ℝ → ℝ)
    (hexchange : SingletonExchangeable Φ)
    (hphase : CommonPhaseInvariant Φ)
    (hstep : ∀ z : ι → ℂ, 1 < coordinateSupportCard z →
      ∃ z' : ι → ℂ,
        coordinateSupportCard z' < coordinateSupportCard z ∧
        coordinateEnergy z' = coordinateEnergy z ∧
        ‖Φ z‖ ≤ ‖Φ z'‖)
    (hradial : ∀ r : ℝ, 0 ≤ r →
      Φ (singleCoordinate base (r : ℂ)) = (radial r : ℂ))
    (hradial_nonneg : ∀ r : ℝ, 0 ≤ r → 0 ≤ radial r) :
    ∀ z : ι → ℂ,
      ‖Φ z‖ ≤ radial (Real.sqrt (coordinateEnergy z)) := by
  intro z
  have hcompression :=
    finite_coordinate_compression_iteration Φ base hexchange hphase hstep z
  have hsqrt : 0 ≤ Real.sqrt (coordinateEnergy z) := Real.sqrt_nonneg _
  rw [hradial _ hsqrt, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hradial_nonneg _ hsqrt)] at hcompression
  exact hcompression

end

end LogdetLean.GramHafnian
