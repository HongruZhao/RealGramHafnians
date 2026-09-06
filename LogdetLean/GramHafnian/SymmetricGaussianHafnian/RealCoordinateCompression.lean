import LogdetLean.GramHafnian.SymmetricGaussianHafnian.RealConditionalKernel
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CoordinateExposure
/-!
# Finite real Fourier-coordinate compression

This is the one-dimensional-coefficient counterpart of the complex
coordinate descent.  The terminal symmetry needed over `ℝ` is only equality
of characteristic-function norms under `w ↦ -w`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

def realSingleCoordinate {iota : Type*} [DecidableEq iota]
    (i : iota) (c : ℝ) : iota → ℝ := fun j ↦ if j = i then c else 0

def realCoordinateSupport {iota : Type*} [Fintype iota]
    (z : iota → ℝ) : Finset iota := Finset.univ.filter fun i ↦ z i ≠ 0

def realCoordinateSupportCard {iota : Type*} [Fintype iota]
    (z : iota → ℝ) : ℕ := (realCoordinateSupport z).card

def realCoordinateEnergy {iota : Type*} [Fintype iota]
    (z : iota → ℝ) : ℝ := ∑ i, (z i) ^ 2

@[simp] theorem realSingleCoordinate_self {iota : Type*} [DecidableEq iota]
    (i : iota) (c : ℝ) : realSingleCoordinate i c i = c := by
  simp [realSingleCoordinate]

@[simp] theorem realSingleCoordinate_of_ne {iota : Type*} [DecidableEq iota]
    {i j : iota} (hji : j ≠ i) (c : ℝ) : realSingleCoordinate i c j = 0 := by
  simp [realSingleCoordinate, hji]

@[simp] theorem realCoordinateEnergy_singleCoordinate
    {iota : Type*} [Fintype iota] [DecidableEq iota] (i : iota) (c : ℝ) :
    realCoordinateEnergy (realSingleCoordinate i c) = c ^ 2 := by
  unfold realCoordinateEnergy realSingleCoordinate
  classical
  calc
    (∑ j, (if j = i then c else 0) ^ 2) =
        (if i = i then c else 0) ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hji]
      · simp
    _ = c ^ 2 := by simp

theorem realCoordinateEnergy_nonneg {iota : Type*} [Fintype iota]
    (z : iota → ℝ) : 0 ≤ realCoordinateEnergy z := by
  unfold realCoordinateEnergy
  positivity

def RealSingletonNormExchangeable {iota : Type*} [DecidableEq iota]
    (Phi : (iota → ℝ) → ℂ) : Prop :=
  ∀ i j c, ‖Phi (realSingleCoordinate i c)‖ = ‖Phi (realSingleCoordinate j c)‖

def RealNegNormInvariant {iota : Type*} (Phi : (iota → ℝ) → ℂ) : Prop :=
  ∀ z, ‖Phi (fun i ↦ -z i)‖ = ‖Phi z‖

theorem real_eq_singleCoordinate_of_support_le_one
    {iota : Type*} [Fintype iota] [DecidableEq iota] [Nonempty iota]
    {z : iota → ℝ} (hz : realCoordinateSupportCard z ≤ 1) :
    ∃ i, z = realSingleCoordinate i (z i) := by
  have hcard : (realCoordinateSupport z).card ≤ 1 := hz
  obtain ⟨i, hi⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
  refine ⟨i, ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · have hzj : z j = 0 := by
      by_contra hj
      have hjmem : j ∈ realCoordinateSupport z := by
        simp [realCoordinateSupport, hj]
      have : j ∈ ({i} : Finset iota) := hi hjmem
      exact hji (Finset.mem_singleton.mp this)
    simp [realSingleCoordinate, hji, hzj]

theorem real_norm_terminal_radial
    {iota : Type*} [Fintype iota] [DecidableEq iota] [Nonempty iota]
    (Phi : (iota → ℝ) → ℂ) (base : iota) (z : iota → ℝ)
    (hexchange : RealSingletonNormExchangeable Phi)
    (hneg : RealNegNormInvariant Phi)
    (hz : realCoordinateSupportCard z ≤ 1) :
    ‖Phi z‖ =
      ‖Phi (realSingleCoordinate base (Real.sqrt (realCoordinateEnergy z)))‖ := by
  obtain ⟨i, hzi⟩ := real_eq_singleCoordinate_of_support_le_one hz
  have henergy : realCoordinateEnergy z = (z i) ^ 2 := by
    conv_lhs => rw [hzi]
    rw [realCoordinateEnergy_singleCoordinate]
  rw [henergy, Real.sqrt_sq_eq_abs]
  by_cases hc : 0 ≤ z i
  · rw [abs_of_nonneg hc]
    calc
      ‖Phi z‖ = ‖Phi (realSingleCoordinate i (z i))‖ :=
        congrArg (fun v ↦ ‖Phi v‖) hzi
      _ = _ := hexchange i base (z i)
  · have hcneg : z i < 0 := lt_of_not_ge hc
    rw [abs_of_neg hcneg]
    calc
      ‖Phi z‖ = ‖Phi (realSingleCoordinate i (z i))‖ :=
        congrArg (fun v ↦ ‖Phi v‖) hzi
      _ =
          ‖Phi (fun j ↦ -realSingleCoordinate i (z i) j)‖ := (hneg _).symm
      _ = ‖Phi (realSingleCoordinate i (-z i))‖ := by
        congr 2
        ext j
        by_cases hji : j = i <;> simp [realSingleCoordinate, hji]
      _ = ‖Phi (realSingleCoordinate base (-z i))‖ := hexchange i base (-z i)

theorem real_compressionStep_of_two_endpoints
    {iota : Type*} [Fintype iota] (Phi : (iota → ℝ) → ℂ)
    {z zLeft zRight : iota → ℝ}
    (hsL : realCoordinateSupportCard zLeft < realCoordinateSupportCard z)
    (hsR : realCoordinateSupportCard zRight < realCoordinateSupportCard z)
    (heL : realCoordinateEnergy zLeft = realCoordinateEnergy z)
    (heR : realCoordinateEnergy zRight = realCoordinateEnergy z)
    (hb : ‖Phi z‖ ≤ max ‖Phi zLeft‖ ‖Phi zRight‖) :
    ∃ z', realCoordinateSupportCard z' < realCoordinateSupportCard z ∧
      realCoordinateEnergy z' = realCoordinateEnergy z ∧ ‖Phi z‖ ≤ ‖Phi z'‖ := by
  by_cases h : ‖Phi zLeft‖ ≤ ‖Phi zRight‖
  · exact ⟨zRight, hsR, heR, by simpa [max_eq_right h] using hb⟩
  · have h' : ‖Phi zRight‖ ≤ ‖Phi zLeft‖ := le_of_not_ge h
    exact ⟨zLeft, hsL, heL, by simpa [max_eq_left h'] using hb⟩

theorem finite_real_coordinate_compression
    {iota : Type*} [Fintype iota] [DecidableEq iota] [Nonempty iota]
    (Phi : (iota → ℝ) → ℂ) (base : iota)
    (hexchange : RealSingletonNormExchangeable Phi)
    (hneg : RealNegNormInvariant Phi)
    (htwo : ∀ z, 1 < realCoordinateSupportCard z →
      ∃ zLeft zRight,
        realCoordinateSupportCard zLeft < realCoordinateSupportCard z ∧
        realCoordinateSupportCard zRight < realCoordinateSupportCard z ∧
        realCoordinateEnergy zLeft = realCoordinateEnergy z ∧
        realCoordinateEnergy zRight = realCoordinateEnergy z ∧
        ‖Phi z‖ ≤ max ‖Phi zLeft‖ ‖Phi zRight‖) :
    ∀ z, ‖Phi z‖ ≤
      ‖Phi (realSingleCoordinate base (Real.sqrt (realCoordinateEnergy z)))‖ := by
  intro z
  generalize hn : realCoordinateSupportCard z = n
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
      by_cases hterminal : n ≤ 1
      · exact (real_norm_terminal_radial Phi base z hexchange hneg
          (by simpa [hn] using hterminal)).le
      · have htwo' : 1 < realCoordinateSupportCard z := by rw [hn]; omega
        obtain ⟨zL, zR, hsL, hsR, heL, heR, hmax⟩ := htwo z htwo'
        obtain ⟨z', hs, he, hb⟩ := real_compressionStep_of_two_endpoints Phi
          hsL hsR heL heR hmax
        calc
          ‖Phi z‖ ≤ ‖Phi z'‖ := hb
          _ ≤ ‖Phi (realSingleCoordinate base
              (Real.sqrt (realCoordinateEnergy z')))‖ := by
            apply ih (realCoordinateSupportCard z')
            · simpa [hn] using hs
            · rfl
          _ = ‖Phi (realSingleCoordinate base
              (Real.sqrt (realCoordinateEnergy z)))‖ := by rw [he]

/-! Distinguished endpoint maps. -/

def realLeftExposedEndpoint {m : ℕ} (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    Fin (m + 2) → ℝ := fun i ↦
  if i = exposedXIndex m then (Real.sqrt theta)⁻¹ * w i
  else if i = exposedYIndex m then 0 else w i

def realRightExposedEndpoint {m : ℕ} (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    Fin (m + 2) → ℝ := fun i ↦
  if i = exposedXIndex m then 0
  else if i = exposedYIndex m then (Real.sqrt (1 - theta))⁻¹ * w i else w i

def realExposedTheta {m : ℕ} (w : Fin (m + 2) → ℝ) : ℝ :=
  w (exposedXIndex m) ^ 2 /
    (w (exposedXIndex m) ^ 2 + w (exposedYIndex m) ^ 2)

@[simp] theorem realLeftEndpoint_background {m : ℕ}
    (w : Fin (m + 2) → ℝ) (theta : ℝ) (i : Fin m) :
    realLeftExposedEndpoint w theta (remainingIndex m i) = w (remainingIndex m i) := by
  simp [realLeftExposedEndpoint, ne_exposedXIndex_of_remaining,
    ne_exposedYIndex_of_remaining]

@[simp] theorem realRightEndpoint_background {m : ℕ}
    (w : Fin (m + 2) → ℝ) (theta : ℝ) (i : Fin m) :
    realRightExposedEndpoint w theta (remainingIndex m i) = w (remainingIndex m i) := by
  simp [realRightExposedEndpoint, ne_exposedXIndex_of_remaining,
    ne_exposedYIndex_of_remaining]

@[simp] theorem realLeftEndpoint_X {m : ℕ} (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    realLeftExposedEndpoint w theta (exposedXIndex m) =
      (Real.sqrt theta)⁻¹ * w (exposedXIndex m) := by simp [realLeftExposedEndpoint]

@[simp] theorem realLeftEndpoint_Y {m : ℕ} (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    realLeftExposedEndpoint w theta (exposedYIndex m) = 0 := by
  simp [realLeftExposedEndpoint, Ne.symm (exposedXIndex_ne_exposedYIndex m)]

@[simp] theorem realRightEndpoint_X {m : ℕ} (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    realRightExposedEndpoint w theta (exposedXIndex m) = 0 := by simp [realRightExposedEndpoint]

@[simp] theorem realRightEndpoint_Y {m : ℕ} (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    realRightExposedEndpoint w theta (exposedYIndex m) =
      (Real.sqrt (1 - theta))⁻¹ * w (exposedYIndex m) := by
  simp [realRightExposedEndpoint, Ne.symm (exposedXIndex_ne_exposedYIndex m)]

theorem realExposedTheta_pos {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0) (hY : w (exposedYIndex m) ≠ 0) :
    0 < realExposedTheta w := by
  unfold realExposedTheta
  positivity

theorem realExposedTheta_lt_one {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0) (hY : w (exposedYIndex m) ≠ 0) :
    realExposedTheta w < 1 := by
  unfold realExposedTheta
  apply (div_lt_one (by positivity)).mpr
  nlinarith [sq_pos_of_ne_zero hY]

private theorem invSqrt_mul_sq {theta x : ℝ} (ht : 0 < theta) :
    ((Real.sqrt theta)⁻¹ * x) ^ 2 = x ^ 2 / theta := by
  have hs : Real.sqrt theta ≠ 0 := Real.sqrt_ne_zero'.mpr ht
  rw [mul_pow, inv_pow, show (Real.sqrt theta) ^ 2 = theta by
    exact Real.sq_sqrt ht.le]
  field_simp [hs]

theorem realCoordinateEnergy_leftEndpoint {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0) (hY : w (exposedYIndex m) ≠ 0) :
    realCoordinateEnergy (realLeftExposedEndpoint w (realExposedTheta w)) =
      realCoordinateEnergy w := by
  have ht := realExposedTheta_pos hX hY
  have hden : w (exposedXIndex m) ^ 2 + w (exposedYIndex m) ^ 2 ≠ 0 := by
    positivity
  have hx : w (exposedXIndex m) ^ 2 ≠ 0 := pow_ne_zero 2 hX
  have hratio : w (exposedXIndex m) ^ 2 / realExposedTheta w =
      w (exposedXIndex m) ^ 2 + w (exposedYIndex m) ^ 2 := by
    unfold realExposedTheta
    field_simp [hden, hx]
  unfold realCoordinateEnergy
  rw [sum_fin_two_exposed (f := fun i ↦ (realLeftExposedEndpoint w (realExposedTheta w) i) ^ 2),
    sum_fin_two_exposed (f := fun i ↦ (w i) ^ 2)]
  simp_rw [realLeftEndpoint_background]
  rw [realLeftEndpoint_X, realLeftEndpoint_Y, invSqrt_mul_sq ht, hratio]
  ring

theorem realCoordinateEnergy_rightEndpoint {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0) (hY : w (exposedYIndex m) ≠ 0) :
    realCoordinateEnergy (realRightExposedEndpoint w (realExposedTheta w)) =
      realCoordinateEnergy w := by
  have ht : 0 < 1 - realExposedTheta w := sub_pos.mpr (realExposedTheta_lt_one hX hY)
  have hden : w (exposedXIndex m) ^ 2 + w (exposedYIndex m) ^ 2 ≠ 0 := by
    positivity
  have hy : w (exposedYIndex m) ^ 2 ≠ 0 := pow_ne_zero 2 hY
  have hratio : w (exposedYIndex m) ^ 2 / (1 - realExposedTheta w) =
      w (exposedXIndex m) ^ 2 + w (exposedYIndex m) ^ 2 := by
    unfold realExposedTheta
    field_simp [hden, hy]
    ring
  unfold realCoordinateEnergy
  rw [sum_fin_two_exposed (f := fun i ↦ (realRightExposedEndpoint w (realExposedTheta w) i) ^ 2),
    sum_fin_two_exposed (f := fun i ↦ (w i) ^ 2)]
  simp_rw [realRightEndpoint_background]
  rw [realRightEndpoint_X, realRightEndpoint_Y, invSqrt_mul_sq ht, hratio]
  ring

theorem realSupport_leftEndpoint_lt {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0) (hY : w (exposedYIndex m) ≠ 0) :
    realCoordinateSupportCard (realLeftExposedEndpoint w (realExposedTheta w)) <
      realCoordinateSupportCard w := by
  have hsubset : realCoordinateSupport (realLeftExposedEndpoint w (realExposedTheta w)) ⊆
      realCoordinateSupport w := by
    intro i hi
    simp only [realCoordinateSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases hiX : i = exposedXIndex m
    · simpa [hiX] using hX
    · by_cases hiY : i = exposedYIndex m
      · subst i; simp at hi
      · simpa [realLeftExposedEndpoint, hiX, hiY] using hi
  unfold realCoordinateSupportCard
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsubset, ?_⟩
  intro heq
  have hm : exposedYIndex m ∈ realCoordinateSupport w := by simp [realCoordinateSupport, hY]
  rw [← heq] at hm
  simpa [realCoordinateSupport] using hm

theorem realSupport_rightEndpoint_lt {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0) (hY : w (exposedYIndex m) ≠ 0) :
    realCoordinateSupportCard (realRightExposedEndpoint w (realExposedTheta w)) <
      realCoordinateSupportCard w := by
  have hsubset : realCoordinateSupport (realRightExposedEndpoint w (realExposedTheta w)) ⊆
      realCoordinateSupport w := by
    intro i hi
    simp only [realCoordinateSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases hiX : i = exposedXIndex m
    · subst i; simp at hi
    · by_cases hiY : i = exposedYIndex m
      · simpa [hiY] using hY
      · simpa [realRightExposedEndpoint, hiX, hiY] using hi
  unfold realCoordinateSupportCard
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsubset, ?_⟩
  intro heq
  have hm : exposedXIndex m ∈ realCoordinateSupport w := by simp [realCoordinateSupport, hX]
  rw [← heq] at hm
  simpa [realCoordinateSupport] using hm

/-! Permuting two nonzero coordinates into the distinguished positions. -/

def realPermuteCoordinates {d : ℕ} (sigma : Equiv.Perm (Fin d))
    (z : Fin d → ℝ) : Fin d → ℝ := z ∘ sigma.symm

theorem realEnergy_permute {d : ℕ} (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) :
    realCoordinateEnergy (realPermuteCoordinates sigma z) = realCoordinateEnergy z := by
  unfold realCoordinateEnergy realPermuteCoordinates
  simpa [Function.comp_def] using sigma.symm.sum_comp (fun i : Fin d ↦ (z i) ^ 2)

theorem realSupportCard_permute {d : ℕ} (sigma : Equiv.Perm (Fin d))
    (z : Fin d → ℝ) :
    realCoordinateSupportCard (realPermuteCoordinates sigma z) =
      realCoordinateSupportCard z := by
  classical
  unfold realCoordinateSupportCard realCoordinateSupport realPermuteCoordinates
  have h : (Finset.univ.filter fun i ↦ z (sigma.symm i) ≠ 0) =
      (Finset.univ.filter fun i ↦ z i ≠ 0).map sigma.toEmbedding := by
    ext i
    simp
  simp only [Function.comp_apply]
  rw [h, Finset.card_map]

def RealPermutationInvariant {d : ℕ} (Phi : (Fin d → ℝ) → ℂ) : Prop :=
  ∀ sigma z, Phi (realPermuteCoordinates sigma z) = Phi z

theorem real_exists_permutation_nonzero_last_two
    {n : ℕ} (z : Fin (n + 2) → ℝ) (hz : 1 < realCoordinateSupportCard z) :
    ∃ sigma : Equiv.Perm (Fin (n + 2)),
      realPermuteCoordinates sigma z (exposedXIndex n) ≠ 0 ∧
      realPermuteCoordinates sigma z (exposedYIndex n) ≠ 0 := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ :=
    Finset.one_lt_card.mp (show 1 < (realCoordinateSupport z).card from hz)
  have hzi : z i ≠ 0 := by simpa [realCoordinateSupport] using hi
  have hzj : z j ≠ 0 := by simpa [realCoordinateSupport] using hj
  let f : Bool → Fin (n + 2) := fun b ↦ if b then j else i
  let g : Bool → Fin (n + 2) := fun b ↦ if b then exposedYIndex n else exposedXIndex n
  have hf : Function.Injective f := by intro a b hab; cases a <;> cases b <;> simp_all [f]
  have hg : Function.Injective g := by
    intro a b hab; cases a <;> cases b <;>
      simp_all [g, exposedXIndex_ne_exposedYIndex,
        Ne.symm (exposedXIndex_ne_exposedYIndex n)]
  obtain ⟨sigma, hsigma⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨sigma, ?_, ?_⟩
  · have hi' : sigma.symm (exposedXIndex n) = i := by
      rw [← show sigma i = exposedXIndex n by simpa [f, g] using hsigma false]
      simp
    simpa [realPermuteCoordinates, hi'] using hzi
  · have hj' : sigma.symm (exposedYIndex n) = j := by
      rw [← show sigma j = exposedYIndex n by simpa [f, g] using hsigma true]
      simp
    simpa [realPermuteCoordinates, hj'] using hzj

theorem real_global_two_endpoints_of_last_two
    {n : ℕ} (Phi : (Fin (n + 2) → ℝ) → ℂ)
    (hperm : RealPermutationInvariant Phi)
    (hlocal : ∀ w, w (exposedXIndex n) ≠ 0 → w (exposedYIndex n) ≠ 0 →
      ∃ wL wR,
        realCoordinateSupportCard wL < realCoordinateSupportCard w ∧
        realCoordinateSupportCard wR < realCoordinateSupportCard w ∧
        realCoordinateEnergy wL = realCoordinateEnergy w ∧
        realCoordinateEnergy wR = realCoordinateEnergy w ∧
        ‖Phi w‖ ≤ max ‖Phi wL‖ ‖Phi wR‖) :
    ∀ z, 1 < realCoordinateSupportCard z →
      ∃ zL zR,
        realCoordinateSupportCard zL < realCoordinateSupportCard z ∧
        realCoordinateSupportCard zR < realCoordinateSupportCard z ∧
        realCoordinateEnergy zL = realCoordinateEnergy z ∧
        realCoordinateEnergy zR = realCoordinateEnergy z ∧
        ‖Phi z‖ ≤ max ‖Phi zL‖ ‖Phi zR‖ := by
  intro z hz
  obtain ⟨sigma, hx, hy⟩ := real_exists_permutation_nonzero_last_two z hz
  obtain ⟨wL, wR, hsL, hsR, heL, heR, hb⟩ :=
    hlocal (realPermuteCoordinates sigma z) hx hy
  refine ⟨realPermuteCoordinates sigma.symm wL,
    realPermuteCoordinates sigma.symm wR, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [realSupportCard_permute] using hsL.trans_eq (realSupportCard_permute sigma z)
  · simpa only [realSupportCard_permute] using hsR.trans_eq (realSupportCard_permute sigma z)
  · rw [realEnergy_permute, heL, realEnergy_permute]
  · rw [realEnergy_permute, heR, realEnergy_permute]
  · rw [← hperm sigma z, hperm sigma.symm wL, hperm sigma.symm wR]
    exact hb

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
