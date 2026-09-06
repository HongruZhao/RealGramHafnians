import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLocalCofactorCompression
/-!
# Global real Fourier compression for the literal Gram-cofactor law

This file turns the distinguished last-two-coordinate estimate into a
finite-coordinate radial estimate.  All operations are literal: endpoint
vectors are written explicitly, an actual finite permutation exposes two
nonzero coordinates, and the terminal singleton is identified by the
permutation symmetry of the iid real column model.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal ComplexConjugate

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Explicit real endpoint weights -/

def realLeftExposedEndpoint {m : ℕ} (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    Fin (m + 2) → ℝ :=
  fun i ↦ if i = exposedXIndex m then
      (Real.sqrt theta)⁻¹ * w i
    else if i = exposedYIndex m then 0 else w i

def realRightExposedEndpoint {m : ℕ} (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    Fin (m + 2) → ℝ :=
  fun i ↦ if i = exposedXIndex m then 0
    else if i = exposedYIndex m then
      (Real.sqrt (1 - theta))⁻¹ * w i
    else w i

@[simp] theorem realLeftExposedEndpoint_background {m : ℕ}
    (w : Fin (m + 2) → ℝ) (theta : ℝ) (i : Fin m) :
    realLeftExposedEndpoint w theta (remainingIndex m i) =
      w (remainingIndex m i) := by
  simp [realLeftExposedEndpoint, ne_exposedXIndex_of_remaining,
    ne_exposedYIndex_of_remaining]

@[simp] theorem realRightExposedEndpoint_background {m : ℕ}
    (w : Fin (m + 2) → ℝ) (theta : ℝ) (i : Fin m) :
    realRightExposedEndpoint w theta (remainingIndex m i) =
      w (remainingIndex m i) := by
  simp [realRightExposedEndpoint, ne_exposedXIndex_of_remaining,
    ne_exposedYIndex_of_remaining]

@[simp] theorem realLeftExposedEndpoint_X {m : ℕ}
    (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    realLeftExposedEndpoint w theta (exposedXIndex m) =
      (Real.sqrt theta)⁻¹ * w (exposedXIndex m) := by
  simp [realLeftExposedEndpoint]

@[simp] theorem realLeftExposedEndpoint_Y {m : ℕ}
    (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    realLeftExposedEndpoint w theta (exposedYIndex m) = 0 := by
  simp [realLeftExposedEndpoint, Ne.symm (exposedXIndex_ne_exposedYIndex m)]

@[simp] theorem realRightExposedEndpoint_X {m : ℕ}
    (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    realRightExposedEndpoint w theta (exposedXIndex m) = 0 := by
  simp [realRightExposedEndpoint]

@[simp] theorem realRightExposedEndpoint_Y {m : ℕ}
    (w : Fin (m + 2) → ℝ) (theta : ℝ) :
    realRightExposedEndpoint w theta (exposedYIndex m) =
      (Real.sqrt (1 - theta))⁻¹ * w (exposedYIndex m) := by
  simp [realRightExposedEndpoint, Ne.symm (exposedXIndex_ne_exposedYIndex m)]

theorem real_endpoint_scale {theta : ℝ} (htheta : 0 < theta) (z : ℝ) :
    z = Real.sqrt theta • ((Real.sqrt theta)⁻¹ * z) := by
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr htheta), one_mul]

theorem sq_inv_sqrt_mul {theta : ℝ} (htheta : 0 < theta) (z : ℝ) :
    ((Real.sqrt theta)⁻¹ * z) ^ 2 = z ^ 2 / theta := by
  have hsqrt : Real.sqrt theta ≠ 0 := Real.sqrt_ne_zero'.mpr htheta
  field_simp [hsqrt]
  rw [Real.sq_sqrt htheta.le]
  ring

def realExposedTheta {m : ℕ} (w : Fin (m + 2) → ℝ) : ℝ :=
  (w (exposedXIndex m)) ^ 2 /
    ((w (exposedXIndex m)) ^ 2 + (w (exposedYIndex m)) ^ 2)

theorem realExposedTheta_pos {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    0 < realExposedTheta w := by
  unfold realExposedTheta
  exact div_pos (sq_pos_iff.mpr hX)
    (add_pos (sq_pos_iff.mpr hX) (sq_pos_iff.mpr hY))

theorem realExposedTheta_lt_one {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    realExposedTheta w < 1 := by
  unfold realExposedTheta
  apply (div_lt_one (add_pos (sq_pos_iff.mpr hX) (sq_pos_iff.mpr hY))).mpr
  linarith [sq_pos_iff.mpr hY]

theorem realCoordinateEnergy_leftExposedEndpoint
    {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    realCoordinateEnergy
        (realLeftExposedEndpoint w (realExposedTheta w)) =
      realCoordinateEnergy w := by
  have ht := realExposedTheta_pos hX hY
  have hden : (w (exposedXIndex m)) ^ 2 +
      (w (exposedYIndex m)) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos (sq_pos_iff.mpr hX) (sq_pos_iff.mpr hY))
  have hxden : (w (exposedXIndex m)) ^ 2 ≠ 0 := ne_of_gt (sq_pos_iff.mpr hX)
  have hratio : (w (exposedXIndex m)) ^ 2 / realExposedTheta w =
      (w (exposedXIndex m)) ^ 2 + (w (exposedYIndex m)) ^ 2 := by
    unfold realExposedTheta
    field_simp [hden, hxden]
  unfold realCoordinateEnergy
  rw [sum_fin_two_exposed
    (f := fun i ↦ (realLeftExposedEndpoint w (realExposedTheta w) i) ^ 2)]
  rw [sum_fin_two_exposed (f := fun i ↦ (w i) ^ 2)]
  simp_rw [realLeftExposedEndpoint_background]
  rw [realLeftExposedEndpoint_X, realLeftExposedEndpoint_Y,
    sq_inv_sqrt_mul ht]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  rw [hratio]
  ring

theorem realCoordinateEnergy_rightExposedEndpoint
    {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    realCoordinateEnergy
        (realRightExposedEndpoint w (realExposedTheta w)) =
      realCoordinateEnergy w := by
  have ht1 : 0 < 1 - realExposedTheta w :=
    sub_pos.mpr (realExposedTheta_lt_one hX hY)
  have hden : (w (exposedXIndex m)) ^ 2 +
      (w (exposedYIndex m)) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos (sq_pos_iff.mpr hX) (sq_pos_iff.mpr hY))
  have hyden : (w (exposedYIndex m)) ^ 2 ≠ 0 := ne_of_gt (sq_pos_iff.mpr hY)
  have hratio : (w (exposedYIndex m)) ^ 2 / (1 - realExposedTheta w) =
      (w (exposedXIndex m)) ^ 2 + (w (exposedYIndex m)) ^ 2 := by
    unfold realExposedTheta
    field_simp [hden, hyden]
    ring
  unfold realCoordinateEnergy
  rw [sum_fin_two_exposed
    (f := fun i ↦ (realRightExposedEndpoint w (realExposedTheta w) i) ^ 2)]
  rw [sum_fin_two_exposed (f := fun i ↦ (w i) ^ 2)]
  simp_rw [realRightExposedEndpoint_background]
  rw [realRightExposedEndpoint_X, realRightExposedEndpoint_Y,
    sq_inv_sqrt_mul ht1]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  rw [hratio]
  ring

theorem realCoordinateSupportCard_leftExposedEndpoint_lt
    {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    realCoordinateSupportCard
        (realLeftExposedEndpoint w (realExposedTheta w)) <
      realCoordinateSupportCard w := by
  have ht := realExposedTheta_pos hX hY
  have hsubset :
      realCoordinateSupport (realLeftExposedEndpoint w (realExposedTheta w)) ⊆
        realCoordinateSupport w := by
    intro i hi
    simp only [realCoordinateSupport, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi ⊢
    by_cases hiX : i = exposedXIndex m
    · simpa [hiX] using hX
    · by_cases hiY : i = exposedYIndex m
      · subst i
        simp at hi
      · simpa [realLeftExposedEndpoint, hiX, hiY] using hi
  have hYmem : exposedYIndex m ∈ realCoordinateSupport w := by
    simp [realCoordinateSupport, hY]
  have hYnot : exposedYIndex m ∉
      realCoordinateSupport (realLeftExposedEndpoint w (realExposedTheta w)) := by
    simp [realCoordinateSupport]
  unfold realCoordinateSupportCard
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsubset, ?_⟩
  intro heq
  apply hYnot
  rw [heq]
  exact hYmem

theorem realCoordinateSupportCard_rightExposedEndpoint_lt
    {m : ℕ} {w : Fin (m + 2) → ℝ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    realCoordinateSupportCard
        (realRightExposedEndpoint w (realExposedTheta w)) <
      realCoordinateSupportCard w := by
  have ht1 : 0 < 1 - realExposedTheta w :=
    sub_pos.mpr (realExposedTheta_lt_one hX hY)
  have hsubset :
      realCoordinateSupport (realRightExposedEndpoint w (realExposedTheta w)) ⊆
        realCoordinateSupport w := by
    intro i hi
    simp only [realCoordinateSupport, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi ⊢
    by_cases hiX : i = exposedXIndex m
    · subst i
      simp at hi
    · by_cases hiY : i = exposedYIndex m
      · simpa [hiY] using hY
      · simpa [realRightExposedEndpoint, hiX, hiY] using hi
  have hXmem : exposedXIndex m ∈ realCoordinateSupport w := by
    simp [realCoordinateSupport, hX]
  have hXnot : exposedXIndex m ∉
      realCoordinateSupport (realRightExposedEndpoint w (realExposedTheta w)) := by
    simp [realCoordinateSupport]
  unfold realCoordinateSupportCard
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsubset, ?_⟩
  intro heq
  apply hXnot
  rw [heq]
  exact hXmem

/-- The exact distinguished-pair endpoint interface. -/
theorem finiteRealGramCofactorCharacteristic_penultimate_final_two_endpoints
    (m k : ℕ) (w : Fin (m + 2) → ℝ)
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    ∃ wLeft wRight : Fin (m + 2) → ℝ,
      realCoordinateSupportCard wLeft < realCoordinateSupportCard w ∧
      realCoordinateSupportCard wRight < realCoordinateSupportCard w ∧
      realCoordinateEnergy wLeft = realCoordinateEnergy w ∧
      realCoordinateEnergy wRight = realCoordinateEnergy w ∧
      ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
        max ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖
          ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wRight‖ := by
  let theta := realExposedTheta w
  let wLeft := realLeftExposedEndpoint w theta
  let wRight := realRightExposedEndpoint w theta
  have ht : 0 < theta := realExposedTheta_pos hX hY
  have ht1 : theta < 1 := realExposedTheta_lt_one hX hY
  refine ⟨wLeft, wRight,
    realCoordinateSupportCard_leftExposedEndpoint_lt hX hY,
    realCoordinateSupportCard_rightExposedEndpoint_lt hX hY,
    realCoordinateEnergy_leftExposedEndpoint hX hY,
    realCoordinateEnergy_rightExposedEndpoint hX hY, ?_⟩
  apply finiteRealGramCofactorCharacteristic_two_exposed_max
    w wLeft wRight theta ht ht1
  · intro i
    exact realLeftExposedEndpoint_background w theta i
  · intro i
    exact realRightExposedEndpoint_background w theta i
  · exact realLeftExposedEndpoint_Y w theta
  · exact realRightExposedEndpoint_X w theta
  · dsimp [wLeft]
    rw [realLeftExposedEndpoint_X]
    exact real_endpoint_scale ht _
  · dsimp [wRight]
    rw [realRightExposedEndpoint_Y]
    exact real_endpoint_scale (sub_pos.mpr ht1) _

/-! ## Real coordinate exposure and pullback -/

def realPermuteCoordinates {d : ℕ} (sigma : Equiv.Perm (Fin d))
    (z : Fin d → ℝ) : Fin d → ℝ :=
  z ∘ sigma.symm

@[simp] theorem realPermuteCoordinates_apply {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) (i : Fin d) :
    realPermuteCoordinates sigma z i = z (sigma.symm i) := rfl

@[simp] theorem realPermuteCoordinates_symm_perm {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) :
    realPermuteCoordinates sigma.symm (realPermuteCoordinates sigma z) = z := by
  ext i
  simp [realPermuteCoordinates]

theorem realCoordinateEnergy_realPermuteCoordinates {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) :
    realCoordinateEnergy (realPermuteCoordinates sigma z) =
      realCoordinateEnergy z := by
  unfold realCoordinateEnergy realPermuteCoordinates
  simpa [Function.comp_def] using
    (sigma.symm.sum_comp (fun i : Fin d ↦ (z i) ^ 2))

theorem realCoordinateSupport_realPermuteCoordinates {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) :
    realCoordinateSupport (realPermuteCoordinates sigma z) =
      (realCoordinateSupport z).map sigma.toEmbedding := by
  classical
  ext i
  constructor
  · intro hi
    have hi' : z (sigma.symm i) ≠ 0 := (Finset.mem_filter.mp hi).2
    apply Finset.mem_map.mpr
    refine ⟨sigma.symm i, ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    have hj' : z j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hjeq : j = sigma.symm i := by
      apply sigma.injective
      simpa using hji
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change z (sigma.symm i) ≠ 0
    simpa [hjeq] using hj'

theorem realCoordinateSupportCard_realPermuteCoordinates {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) :
    realCoordinateSupportCard (realPermuteCoordinates sigma z) =
      realCoordinateSupportCard z := by
  unfold realCoordinateSupportCard
  rw [realCoordinateSupport_realPermuteCoordinates]
  exact Finset.card_map _

theorem exists_real_permutation_nonzero_penultimate_final
    {n : ℕ} (z : Fin (n + 2) → ℝ)
    (hz : 1 < realCoordinateSupportCard z) :
    ∃ sigma : Equiv.Perm (Fin (n + 2)),
      realPermuteCoordinates sigma z (penultimateCoordinate n) ≠ 0 ∧
      realPermuteCoordinates sigma z (finalCoordinate n) ≠ 0 := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ :=
    Finset.one_lt_card.mp
      (show 1 < (realCoordinateSupport z).card from hz)
  have hzi : z i ≠ 0 := by
    simpa [realCoordinateSupport] using hi
  have hzj : z j ≠ 0 := by
    simpa [realCoordinateSupport] using hj
  let f : Bool → Fin (n + 2) := fun b ↦ if b then j else i
  let g : Bool → Fin (n + 2) := fun b ↦
    if b then finalCoordinate n else penultimateCoordinate n
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b <;> simp_all [f]
  have hg : Function.Injective g := by
    intro a b hab
    cases a <;> cases b <;>
      simp_all [g, penultimateCoordinate_ne_finalCoordinate,
        Ne.symm (penultimateCoordinate_ne_finalCoordinate n)]
  obtain ⟨sigma, hsigma⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hsigmai : sigma i = penultimateCoordinate n := by
    simpa [f, g] using hsigma false
  have hsigj : sigma j = finalCoordinate n := by
    simpa [f, g] using hsigma true
  refine ⟨sigma, ?_, ?_⟩
  · have hinv : sigma.symm (penultimateCoordinate n) = i := by
      rw [← hsigmai]
      simp
    simpa [realPermuteCoordinates, hinv] using hzi
  · have hinv : sigma.symm (finalCoordinate n) = j := by
      rw [← hsigj]
      simp
    simpa [realPermuteCoordinates, hinv] using hzj

def RealPermutationInvariant {d : ℕ}
    (Phi : (Fin d → ℝ) → ℂ) : Prop :=
  ∀ (sigma : Equiv.Perm (Fin d)) z,
    Phi (realPermuteCoordinates sigma z) = Phi z

theorem pullback_real_two_endpoints_permutation
    {d : ℕ} (Phi : (Fin d → ℝ) → ℂ)
    (hperm : RealPermutationInvariant Phi)
    (sigma : Equiv.Perm (Fin d)) (z wLeft wRight : Fin d → ℝ)
    (hsuppLeft : realCoordinateSupportCard wLeft <
      realCoordinateSupportCard (realPermuteCoordinates sigma z))
    (hsuppRight : realCoordinateSupportCard wRight <
      realCoordinateSupportCard (realPermuteCoordinates sigma z))
    (henergyLeft : realCoordinateEnergy wLeft =
      realCoordinateEnergy (realPermuteCoordinates sigma z))
    (henergyRight : realCoordinateEnergy wRight =
      realCoordinateEnergy (realPermuteCoordinates sigma z))
    (hbound : ‖Phi (realPermuteCoordinates sigma z)‖ ≤
      max ‖Phi wLeft‖ ‖Phi wRight‖) :
    ∃ zLeft zRight : Fin d → ℝ,
      realCoordinateSupportCard zLeft < realCoordinateSupportCard z ∧
      realCoordinateSupportCard zRight < realCoordinateSupportCard z ∧
      realCoordinateEnergy zLeft = realCoordinateEnergy z ∧
      realCoordinateEnergy zRight = realCoordinateEnergy z ∧
      ‖Phi z‖ ≤ max ‖Phi zLeft‖ ‖Phi zRight‖ := by
  refine ⟨realPermuteCoordinates sigma.symm wLeft,
    realPermuteCoordinates sigma.symm wRight, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [realCoordinateSupportCard_realPermuteCoordinates] using
      (hsuppLeft.trans_eq
        (realCoordinateSupportCard_realPermuteCoordinates sigma z))
  · simpa only [realCoordinateSupportCard_realPermuteCoordinates] using
      (hsuppRight.trans_eq
        (realCoordinateSupportCard_realPermuteCoordinates sigma z))
  · rw [realCoordinateEnergy_realPermuteCoordinates, henergyLeft,
      realCoordinateEnergy_realPermuteCoordinates]
  · rw [realCoordinateEnergy_realPermuteCoordinates, henergyRight,
      realCoordinateEnergy_realPermuteCoordinates]
  · rw [← hperm sigma z, hperm sigma.symm wLeft, hperm sigma.symm wRight]
    exact hbound

theorem global_real_two_endpoints_of_penultimate_final
    {n : ℕ} (Phi : (Fin (n + 2) → ℝ) → ℂ)
    (hperm : RealPermutationInvariant Phi)
    (hlocal : ∀ w : Fin (n + 2) → ℝ,
      w (penultimateCoordinate n) ≠ 0 →
      w (finalCoordinate n) ≠ 0 →
      ∃ wLeft wRight : Fin (n + 2) → ℝ,
        realCoordinateSupportCard wLeft < realCoordinateSupportCard w ∧
        realCoordinateSupportCard wRight < realCoordinateSupportCard w ∧
        realCoordinateEnergy wLeft = realCoordinateEnergy w ∧
        realCoordinateEnergy wRight = realCoordinateEnergy w ∧
        ‖Phi w‖ ≤ max ‖Phi wLeft‖ ‖Phi wRight‖) :
    ∀ z : Fin (n + 2) → ℝ, 1 < realCoordinateSupportCard z →
      ∃ zLeft zRight : Fin (n + 2) → ℝ,
        realCoordinateSupportCard zLeft < realCoordinateSupportCard z ∧
        realCoordinateSupportCard zRight < realCoordinateSupportCard z ∧
        realCoordinateEnergy zLeft = realCoordinateEnergy z ∧
        realCoordinateEnergy zRight = realCoordinateEnergy z ∧
        ‖Phi z‖ ≤ max ‖Phi zLeft‖ ‖Phi zRight‖ := by
  intro z hz
  obtain ⟨sigma, hzPen, hzLast⟩ :=
    exists_real_permutation_nonzero_penultimate_final z hz
  obtain ⟨wLeft, wRight, hsLeft, hsRight, heLeft, heRight, hmax⟩ :=
    hlocal (realPermuteCoordinates sigma z) hzPen hzLast
  exact pullback_real_two_endpoints_permutation Phi hperm sigma z wLeft wRight
    hsLeft hsRight heLeft heRight hmax

/-! ## Literal symmetry and radial endpoint -/

theorem finiteRealGramCofactorCharacteristic_permutationInvariant
    (m k : ℕ) :
    RealPermutationInvariant
      (finiteRealGramCofactorCharacteristic (Fin (m + 2)) k) := by
  intro sigma z
  change finiteRealGramCofactorCharacteristic (Fin (m + 2)) k
    (fun i ↦ z (sigma.symm i)) =
      finiteRealGramCofactorCharacteristic (Fin (m + 2)) k z
  exact finiteRealGramCofactorCharacteristic_reindex_perm
    (k := k) sigma.symm z

theorem finiteRealGramCofactorCharacteristic_singletonExchangeable
    {iota : Type*} [Fintype iota] [LinearOrder iota] {k : ℕ} :
    RealSingletonExchangeable
      (finiteRealGramCofactorCharacteristic iota k) := by
  intro i j z
  classical
  by_cases hij : i = j
  · subst j
    rfl
  let sigma : Equiv.Perm iota := Equiv.swap i j
  have h := finiteRealGramCofactorCharacteristic_reindex_perm
    (k := k) sigma (realSingleCoordinate j z)
  rw [show (fun l ↦ realSingleCoordinate j z (sigma l)) =
      realSingleCoordinate i z by
    funext l
    by_cases hli : l = i
    · subst l
      simp [sigma, realSingleCoordinate, hij]
    · by_cases hlj : l = j
      · subst l
        simp [sigma, realSingleCoordinate, hij, hli]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
        simp [realSingleCoordinate, hli, hlj]] at h
  exact h

theorem finiteRealGramCofactorPhase_neg
    {iota : Type*} [Fintype iota] [LinearOrder iota] {k : ℕ}
    (A : iota → (Fin k → ℝ)) (w : iota → ℝ) :
    finiteRealGramCofactorPhase A (fun i ↦ -w i) =
      -finiteRealGramCofactorPhase A w := by
  unfold finiteRealGramCofactorPhase
  simp only [neg_mul, Finset.sum_neg_distrib]

theorem finiteRealGramCofactorCharacteristic_neg
    {iota : Type*} [Fintype iota] [LinearOrder iota] {k : ℕ}
    (w : iota → ℝ) :
    finiteRealGramCofactorCharacteristic iota k (fun i ↦ -w i) =
      conj (finiteRealGramCofactorCharacteristic iota k w) := by
  unfold finiteRealGramCofactorCharacteristic
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with A
  unfold finiteRealGramCofactorPhaseCharacter
  rw [finiteRealGramCofactorPhase_neg]
  simp [← Complex.exp_conj]

theorem finiteRealGramCofactorCharacteristic_singletonEven
    {iota : Type*} [Fintype iota] [LinearOrder iota] {k : ℕ} :
    RealSingletonEven
      (finiteRealGramCofactorCharacteristic iota k) := by
  intro i c
  have h := finiteRealGramCofactorCharacteristic_neg
    (k := k) (realSingleCoordinate i c)
  have hfun : (fun j ↦ -realSingleCoordinate i c j) =
      realSingleCoordinate i (-c) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [realSingleCoordinate, hji]
  rw [hfun] at h
  rw [h, norm_conj]

theorem finiteRealGramCofactorCharacteristic_global_two_endpoints
    (m k : ℕ) :
    ∀ z : Fin (m + 2) → ℝ, 1 < realCoordinateSupportCard z →
      ∃ zLeft zRight : Fin (m + 2) → ℝ,
        realCoordinateSupportCard zLeft < realCoordinateSupportCard z ∧
        realCoordinateSupportCard zRight < realCoordinateSupportCard z ∧
        realCoordinateEnergy zLeft = realCoordinateEnergy z ∧
        realCoordinateEnergy zRight = realCoordinateEnergy z ∧
        ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k z‖ ≤
          max ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k zLeft‖
            ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k zRight‖ := by
  apply global_real_two_endpoints_of_penultimate_final
    (finiteRealGramCofactorCharacteristic (Fin (m + 2)) k)
    (finiteRealGramCofactorCharacteristic_permutationInvariant m k)
  intro w hPen hFinal
  apply finiteRealGramCofactorCharacteristic_penultimate_final_two_endpoints
    m k w
  · have hi : penultimateCoordinate m = exposedXIndex m := by
      apply Fin.ext
      rfl
    rwa [hi] at hPen
  · have hi : finalCoordinate m = exposedYIndex m := by
      apply Fin.ext
      rfl
    rwa [hi] at hFinal

/-- Full literal radial compression for a finite real Gram-cofactor law. -/
theorem finiteRealGramCofactorCharacteristic_radial_compression
    (m k : ℕ) (base : Fin (m + 2)) (z : Fin (m + 2) → ℝ) :
    ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k z‖ ≤
      ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k
        (realSingleCoordinate base
          (Real.sqrt (realCoordinateEnergy z)))‖ := by
  apply finite_real_coordinate_compression_iteration
    (finiteRealGramCofactorCharacteristic (Fin (m + 2)) k) base
    finiteRealGramCofactorCharacteristic_singletonExchangeable
    finiteRealGramCofactorCharacteristic_singletonEven
  intro w hw
  obtain ⟨wLeft, wRight, hsLeft, hsRight, heLeft, heRight, hmax⟩ :=
    finiteRealGramCofactorCharacteristic_global_two_endpoints m k w hw
  exact realCompressionStep_of_two_endpoints
    (finiteRealGramCofactorCharacteristic (Fin (m + 2)) k)
    hsLeft hsRight heLeft heRight hmax

/-- Dimension-indexed form, convenient for the literal `2r-1` cofactor
vector. -/
theorem finiteRealGramCofactorCharacteristic_radial_compression_dim
    (d k : ℕ) (hd : 2 ≤ d) (base : Fin d) (z : Fin d → ℝ) :
    ‖finiteRealGramCofactorCharacteristic (Fin d) k z‖ ≤
      ‖finiteRealGramCofactorCharacteristic (Fin d) k
        (realSingleCoordinate base
          (Real.sqrt (realCoordinateEnergy z)))‖ := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 2 := ⟨d - 2, by omega⟩
  exact finiteRealGramCofactorCharacteristic_radial_compression m k base z

end

end LogdetLean.GramHafnian
