import LogdetLean.GramHafnian.RealComplexAnticoncentration.AuxiliaryRadiusResolvent
/-!
# Finite real Fourier-coordinate compression

This is the beta-one analogue of the complex coordinate descent.  A local
two-coordinate compression preserves squared radius and removes a nonzero
coordinate.  Exchangeability and evenness of singleton characteristic
functions identify the terminal vector with the positive radial axis.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realSingleCoordinate (i : ι) (c : ℝ) : ι → ℝ :=
  fun j ↦ if j = i then c else 0

def realCoordinateSupport (z : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i ↦ z i ≠ 0

def realCoordinateSupportCard (z : ι → ℝ) : ℕ :=
  (realCoordinateSupport z).card

def realCoordinateEnergy (z : ι → ℝ) : ℝ :=
  ∑ i, (z i) ^ 2

@[simp] theorem realSingleCoordinate_apply_self (i : ι) (c : ℝ) :
    realSingleCoordinate i c i = c := by
  simp [realSingleCoordinate]

@[simp] theorem realSingleCoordinate_apply_of_ne
    {i j : ι} (hji : j ≠ i) (c : ℝ) :
    realSingleCoordinate i c j = 0 := by
  simp [realSingleCoordinate, hji]

@[simp] theorem realCoordinateEnergy_singleCoordinate (i : ι) (c : ℝ) :
    realCoordinateEnergy (realSingleCoordinate i c) = c ^ 2 := by
  unfold realCoordinateEnergy realSingleCoordinate
  classical
  calc
    (∑ j, (if j = i then c else 0) ^ 2) =
        (if i = i then c else 0) ^ 2 := by
      apply Finset.sum_eq_single (s := Finset.univ) i
      · intro j hj hji
        simp [hji]
      · simp
    _ = c ^ 2 := by simp

theorem realCoordinateEnergy_nonneg (z : ι → ℝ) :
    0 ≤ realCoordinateEnergy z := by
  unfold realCoordinateEnergy
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (z i)

def RealSingletonExchangeable (Phi : (ι → ℝ) → ℂ) : Prop :=
  ∀ i j c, Phi (realSingleCoordinate i c) =
    Phi (realSingleCoordinate j c)

/-- The one-coordinate characteristic function is even. -/
def RealSingletonEven (Phi : (ι → ℝ) → ℂ) : Prop :=
  ∀ i c, ‖Phi (realSingleCoordinate i (-c))‖ =
    ‖Phi (realSingleCoordinate i c)‖

theorem norm_realSingleton_eq_nonnegative_base
    [Nonempty ι] (Phi : (ι → ℝ) → ℂ) (base i : ι) (c : ℝ)
    (hexchange : RealSingletonExchangeable Phi)
    (heven : RealSingletonEven Phi) :
    ‖Phi (realSingleCoordinate i c)‖ =
      ‖Phi (realSingleCoordinate base |c|)‖ := by
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
    exact congrArg norm (hexchange i base c)
  · have hcneg : c < 0 := lt_of_not_ge hc
    rw [abs_of_neg hcneg]
    calc
      ‖Phi (realSingleCoordinate i c)‖ =
          ‖Phi (realSingleCoordinate i (-c))‖ := (heven i c).symm
      _ = ‖Phi (realSingleCoordinate base (-c))‖ :=
        congrArg norm (hexchange i base (-c))

theorem eq_realSingleCoordinate_of_supportCard_le_one
    [Nonempty ι] {z : ι → ℝ} (hz : realCoordinateSupportCard z ≤ 1) :
    ∃ i : ι, z = realSingleCoordinate i (z i) := by
  have hcard : (realCoordinateSupport z).card ≤ 1 := hz
  obtain ⟨i, hi⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
  refine ⟨i, ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · have hzj : z j = 0 := by
      by_contra hjzero
      have hjmem : j ∈ realCoordinateSupport z := by
        simp [realCoordinateSupport, hjzero]
      have : j ∈ ({i} : Finset ι) := hi hjmem
      exact hji (Finset.mem_singleton.mp this)
    simp [realSingleCoordinate, hji, hzj]

theorem norm_eq_realRadial_of_supportCard_le_one
    [Nonempty ι] (Phi : (ι → ℝ) → ℂ) (base : ι) (z : ι → ℝ)
    (hexchange : RealSingletonExchangeable Phi)
    (heven : RealSingletonEven Phi)
    (hz : realCoordinateSupportCard z ≤ 1) :
    ‖Phi z‖ =
      ‖Phi (realSingleCoordinate base
        (Real.sqrt (realCoordinateEnergy z)))‖ := by
  obtain ⟨i, hzi⟩ := eq_realSingleCoordinate_of_supportCard_le_one hz
  have henergy : realCoordinateEnergy z = (z i) ^ 2 := by
    conv_lhs => rw [hzi]
    rw [realCoordinateEnergy_singleCoordinate]
  calc
    ‖Phi z‖ = ‖Phi (realSingleCoordinate i (z i))‖ :=
      congrArg norm (congrArg Phi hzi)
    _ = ‖Phi (realSingleCoordinate base |z i|)‖ :=
      norm_realSingleton_eq_nonnegative_base Phi base i _ hexchange heven
    _ = ‖Phi (realSingleCoordinate base
          (Real.sqrt (realCoordinateEnergy z)))‖ := by
      congr 2
      rw [henergy, Real.sqrt_sq_eq_abs]

theorem finite_real_coordinate_compression_iteration
    [Nonempty ι] (Phi : (ι → ℝ) → ℂ) (base : ι)
    (hexchange : RealSingletonExchangeable Phi)
    (heven : RealSingletonEven Phi)
    (hstep : ∀ z : ι → ℝ, 1 < realCoordinateSupportCard z →
      ∃ z' : ι → ℝ,
        realCoordinateSupportCard z' < realCoordinateSupportCard z ∧
        realCoordinateEnergy z' = realCoordinateEnergy z ∧
        ‖Phi z‖ ≤ ‖Phi z'‖) :
    ∀ z : ι → ℝ,
      ‖Phi z‖ ≤
        ‖Phi (realSingleCoordinate base
          (Real.sqrt (realCoordinateEnergy z)))‖ := by
  intro z
  generalize hn : realCoordinateSupportCard z = n
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
      by_cases hterminal : n ≤ 1
      · have hzterminal : realCoordinateSupportCard z ≤ 1 := by
          simpa [hn] using hterminal
        exact (norm_eq_realRadial_of_supportCard_le_one
          Phi base z hexchange heven hzterminal).le
      · have htwo : 1 < realCoordinateSupportCard z := by
          rw [hn]
          omega
        obtain ⟨z', hsupp, henergy, hbound⟩ := hstep z htwo
        calc
          ‖Phi z‖ ≤ ‖Phi z'‖ := hbound
          _ ≤ ‖Phi (realSingleCoordinate base
              (Real.sqrt (realCoordinateEnergy z')))‖ := by
            apply ih (realCoordinateSupportCard z')
            · simpa [hn] using hsupp
            · rfl
          _ = ‖Phi (realSingleCoordinate base
              (Real.sqrt (realCoordinateEnergy z)))‖ := by
            rw [henergy]

theorem realCompressionStep_of_two_endpoints
    (Phi : (ι → ℝ) → ℂ) {z zLeft zRight : ι → ℝ}
    (hsuppLeft : realCoordinateSupportCard zLeft < realCoordinateSupportCard z)
    (hsuppRight : realCoordinateSupportCard zRight < realCoordinateSupportCard z)
    (henergyLeft : realCoordinateEnergy zLeft = realCoordinateEnergy z)
    (henergyRight : realCoordinateEnergy zRight = realCoordinateEnergy z)
    (hbound : ‖Phi z‖ ≤ max ‖Phi zLeft‖ ‖Phi zRight‖) :
    ∃ z' : ι → ℝ,
      realCoordinateSupportCard z' < realCoordinateSupportCard z ∧
      realCoordinateEnergy z' = realCoordinateEnergy z ∧
      ‖Phi z‖ ≤ ‖Phi z'‖ := by
  by_cases hle : ‖Phi zLeft‖ ≤ ‖Phi zRight‖
  · refine ⟨zRight, hsuppRight, henergyRight, ?_⟩
    simpa [max_eq_right hle] using hbound
  · have hge : ‖Phi zRight‖ ≤ ‖Phi zLeft‖ := le_of_not_ge hle
    refine ⟨zLeft, hsuppLeft, henergyLeft, ?_⟩
    simpa [max_eq_left hge] using hbound

theorem finite_real_coordinate_compression_to_radial
    [Nonempty ι] (Phi : (ι → ℝ) → ℂ) (base : ι)
    (radial : ℝ → ℝ)
    (hexchange : RealSingletonExchangeable Phi)
    (heven : RealSingletonEven Phi)
    (hstep : ∀ z : ι → ℝ, 1 < realCoordinateSupportCard z →
      ∃ z' : ι → ℝ,
        realCoordinateSupportCard z' < realCoordinateSupportCard z ∧
        realCoordinateEnergy z' = realCoordinateEnergy z ∧
        ‖Phi z‖ ≤ ‖Phi z'‖)
    (hradial : ∀ r : ℝ, 0 ≤ r →
      Phi (realSingleCoordinate base r) = (radial r : ℂ))
    (hradial_nonneg : ∀ r : ℝ, 0 ≤ r → 0 ≤ radial r) :
    ∀ z : ι → ℝ,
      ‖Phi z‖ ≤ radial (Real.sqrt (realCoordinateEnergy z)) := by
  intro z
  have hcompression := finite_real_coordinate_compression_iteration
    Phi base hexchange heven hstep z
  have hsqrt : 0 ≤ Real.sqrt (realCoordinateEnergy z) := Real.sqrt_nonneg _
  rw [hradial _ hsqrt, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hradial_nonneg _ hsqrt)] at hcompression
  exact hcompression

theorem realCoordinateEnergy_euclideanSpace_coe
    {d : ℕ} (xi : RealGaussianEuclideanSpace d) :
    realCoordinateEnergy (fun i : Fin d ↦ xi i) = ‖xi‖ ^ 2 := by
  unfold realCoordinateEnergy
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Real.norm_eq_abs, sq_abs]

variable {Omega : Type*} [MeasurableSpace Omega]

/-- End-to-end beta-one Fourier resolvent step from finite coordinate
compression, with an arbitrary auxiliary-radius threshold. -/
theorem ennHalfResolvent_norm_sq_le_threshold_of_realCoordinateCompression
    {d : ℕ} (hd : 1 ≤ d) (base : Fin d)
    (mu : Measure (RealGaussianEuclideanSpace d)) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (rawPhi : (Fin d → ℝ) → ℂ)
    (hrawPhi : ∀ xi : RealGaussianEuclideanSpace d,
      rawPhi (fun i ↦ xi i) = charFun mu xi)
    (hexchange : RealSingletonExchangeable rawPhi)
    (heven : RealSingletonEven rawPhi)
    (hstep : ∀ z : Fin d → ℝ, 1 < realCoordinateSupportCard z →
      ∃ z' : Fin d → ℝ,
        realCoordinateSupportCard z' < realCoordinateSupportCard z ∧
        realCoordinateEnergy z' = realCoordinateEnergy z ∧
        ‖rawPhi z‖ ≤ ‖rawPhi z'‖)
    (hsingleton : ∀ r : ℝ, 0 ≤ r →
      rawPhi (realSingleCoordinate base r) =
        ((∫ w, Real.exp (-(V w * r ^ 2) / 2) ∂nu) : ℝ))
    (a lambda : ℝ) (ha : 0 < a) (hlambda : 0 < lambda) :
    ennHalfResolvent mu (fun x ↦ ‖x‖ ^ 2) lambda ≤
      ennHalfResolvent nu V (lambda / a) +
        (stdGaussian (RealGaussianEuclideanSpace d))
          {g | realAuxiliaryNormSq g < a} := by
  let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let radial : ℝ → ℝ := fun r ↦
    ∫ w, Real.exp (-(V w * r ^ 2) / 2) ∂nu
  have hradial_nonneg : ∀ r : ℝ, 0 ≤ r → 0 ≤ radial r := by
    intro r hr
    dsimp [radial]
    apply integral_nonneg
    intro w
    exact (Real.exp_pos _).le
  have hcompressionRaw : ∀ z : Fin d → ℝ,
      ‖rawPhi z‖ ≤ radial (Real.sqrt (realCoordinateEnergy z)) :=
    finite_real_coordinate_compression_to_radial rawPhi base radial
      hexchange heven hstep (by simpa [radial] using hsingleton)
      hradial_nonneg
  have hcompression : ∀ xi : RealGaussianEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 2) ∂nu := by
    intro xi
    let z : Fin d → ℝ := fun i ↦ xi i
    calc
      (charFun mu xi).re ≤ ‖charFun mu xi‖ := Complex.re_le_norm _
      _ = ‖rawPhi z‖ := by rw [hrawPhi xi]
      _ ≤ radial (Real.sqrt (realCoordinateEnergy z)) := hcompressionRaw z
      _ = ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 2) ∂nu := by
        dsimp [radial]
        apply integral_congr_ae
        filter_upwards [] with w
        congr 1
        rw [Real.sq_sqrt (realCoordinateEnergy_nonneg z),
          realCoordinateEnergy_euclideanSpace_coe xi]
  exact ennHalfResolvent_norm_sq_le_threshold_of_compression
    mu nu V hV hVnonneg hcompression a lambda ha hlambda

end

end LogdetLean.GramHafnian
