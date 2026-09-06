import LogdetLean.GramHafnian.SymmetricGaussianHafnian.RealCoordinateCompression
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.EdgeMatrixReconstruction
/-!
# Literal Fourier compression for the real independent-edge ensemble

The characteristic functional in this file is built from the actual
`N(0,1)` edge product and the literal principal hafnian cofactors.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 1800000

/-! ## Two-edge-star exposure -/

def realUnpackTwoVertexCoordinates {iota : Type*}
    (x : (Edge iota ⊕ (Unit ⊕ (iota ⊕ iota))) → ℝ) :
    (Edge iota → ℝ) × (ℝ × ((iota → ℝ) × (iota → ℝ))) :=
  (fun e ↦ x (.inl e),
    (x (.inr (.inl ())),
      (fun i ↦ x (.inr (.inr (.inl i))), fun i ↦ x (.inr (.inr (.inr i))))))

theorem measurePreserving_realUnpackTwoVertexCoordinates
    {iota : Type*} [Fintype iota] :
    MeasurePreserving (realUnpackTwoVertexCoordinates (iota := iota))
      (standardRealGaussianProduct (Edge iota ⊕ (Unit ⊕ (iota ⊕ iota))))
      ((realEdgeGaussian iota).prod ((gaussianReal 0 1).prod
        ((standardRealGaussianProduct iota).prod
          (standardRealGaussianProduct iota)))) := by
  have hxy := measurePreserving_standardRealGaussianProduct_splitSum
    (ι := iota) (κ := iota)
  have hu : MeasurePreserving (fun x : Unit → ℝ ↦ x ())
      (standardRealGaussianProduct Unit) (gaussianReal 0 1) :=
    ⟨measurable_pi_apply (), standardRealGaussianProduct_map_eval ()⟩
  have huxy := (hu.prod hxy).comp
    (measurePreserving_standardRealGaussianProduct_splitSum
      (ι := Unit) (κ := iota ⊕ iota))
  have hall := ((MeasurePreserving.id (realEdgeGaussian iota)).prod huxy).comp
    (measurePreserving_standardRealGaussianProduct_splitSum
      (ι := Edge iota) (κ := Unit ⊕ (iota ⊕ iota)))
  exact hall

def realTwoExposedSplit (m : ℕ) (x : Edge (Fin (m + 2)) → ℝ) :
    (Edge (Fin m) → ℝ) × (ℝ × ((Fin m → ℝ) × (Fin m → ℝ))) :=
  realUnpackTwoVertexCoordinates (fun e ↦ x (twoExposedEdgeEmbedding m e))

theorem measurePreserving_realTwoExposedSplit (m : ℕ) :
    MeasurePreserving (realTwoExposedSplit m) (realEdgeGaussian (Fin (m + 2)))
      ((realEdgeGaussian (Fin m)).prod (realExposedMeasure m)) := by
  exact measurePreserving_realUnpackTwoVertexCoordinates.comp
    (measurePreserving_standardRealGaussianProduct_restrict
      (twoExposedEdgeEmbedding m))

@[simp] theorem realTwoExposedSplit_background (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℝ) :
    (realTwoExposedSplit m x).1 = realRestrictEdges (remainingVertexEmbedding m) x := rfl

@[simp] theorem realTwoExposedSplit_scalar (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℝ) :
    (realTwoExposedSplit m x).2.1 =
      realMatrixOfEdges x (exposedXIndex m) (exposedYIndex m) := by
  change x (edgeOfNe (exposedXIndex m) (exposedYIndex m)
    (exposedXIndex_ne_exposedYIndex m)) = _
  exact (realMatrixOfEdges_apply_ne x _ _ _).symm

@[simp] theorem realTwoExposedSplit_X (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℝ) (i : Fin m) :
    (realTwoExposedSplit m x).2.2.1 i =
      realMatrixOfEdges x (remainingIndex m i) (exposedXIndex m) := by
  change x (edgeOfNe (remainingIndex m i) (exposedXIndex m)
    (ne_exposedXIndex_of_remaining m i)) = _
  exact (realMatrixOfEdges_apply_ne x _ _ _).symm

@[simp] theorem realTwoExposedSplit_Y (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℝ) (i : Fin m) :
    (realTwoExposedSplit m x).2.2.2 i =
      realMatrixOfEdges x (remainingIndex m i) (exposedYIndex m) := by
  change x (edgeOfNe (remainingIndex m i) (exposedYIndex m)
    (ne_exposedYIndex_of_remaining m i)) = _
  exact (realMatrixOfEdges_apply_ne x _ _ _).symm

theorem realTwoExposedMatrix_realTwoExposedSplit (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℝ) :
    twoExposedMatrix (realMatrixOfEdges (realTwoExposedSplit m x).1)
      (realTwoExposedSplit m x).2.1
      (realTwoExposedSplit m x).2.2.1
      (realTwoExposedSplit m x).2.2.2 = realMatrixOfEdges x := by
  have hA : realMatrixOfEdges (realTwoExposedSplit m x).1 =
      fun i j : Fin m ↦ realMatrixOfEdges x (remainingIndex m i) (remainingIndex m j) := by
    rw [realTwoExposedSplit_background, realMatrixOfEdges_restrict]
    rfl
  have hX : (realTwoExposedSplit m x).2.2.1 =
      fun i : Fin m ↦ realMatrixOfEdges x (remainingIndex m i) (exposedXIndex m) := by
    funext i; exact realTwoExposedSplit_X m x i
  have hY : (realTwoExposedSplit m x).2.2.2 =
      fun i : Fin m ↦ realMatrixOfEdges x (remainingIndex m i) (exposedYIndex m) := by
    funext i; exact realTwoExposedSplit_Y m x i
  rw [hA, hX, hY, realTwoExposedSplit_scalar]
  unfold twoExposedMatrix
  let B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    fun i j ↦ realMatrixOfEdges x i.castSucc j.castSucc
  have hB : appendMatrix
      (fun i j : Fin m ↦ realMatrixOfEdges x (remainingIndex m i) (remainingIndex m j))
      (fun i : Fin m ↦ realMatrixOfEdges x (remainingIndex m i) (exposedXIndex m)) = B := by
    exact appendMatrix_reconstruct B
      (fun i j ↦ realMatrixOfEdges_symmetric x i.castSucc j.castSucc)
      (realMatrixOfEdges_diag x (Fin.last m).castSucc)
  rw [hB]
  have hg : Fin.lastCases
      (realMatrixOfEdges x (exposedXIndex m) (exposedYIndex m))
      (fun i : Fin m ↦ realMatrixOfEdges x (remainingIndex m i) (exposedYIndex m)) =
      fun i : Fin (m + 1) ↦ realMatrixOfEdges x i.castSucc (Fin.last (m + 1)) := by
    funext i
    refine Fin.lastCases ?_ (fun a ↦ ?_) i <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc] <;> rfl
  rw [hg]
  exact appendMatrix_reconstruct (realMatrixOfEdges x)
    (realMatrixOfEdges_symmetric x) (realMatrixOfEdges_diag x (Fin.last (m + 1)))

/-! ## Real weighted cofactor algebra -/

def realBackgroundEll {m : ℕ} (R : Edge (Fin m) → ℝ)
    (w : Fin (m + 2) → ℝ) : ℝ :=
  ∑ j, w (remainingIndex m j) * realEdgeCofactor R j

def realBackgroundMatrix {m : ℕ} (R : Edge (Fin m) → ℝ)
    (w : Fin (m + 2) → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun a b ↦ ∑ j, w (remainingIndex m j) * fixedBackgroundM (realMatrixOfEdges R) j a b

@[fun_prop] theorem measurable_realBackgroundEll {m : ℕ} (w : Fin (m + 2) → ℝ) :
    Measurable (fun R : Edge (Fin m) → ℝ ↦ realBackgroundEll R w) := by
  unfold realBackgroundEll
  fun_prop

@[fun_prop] theorem measurable_realBackgroundMatrix_entry
    {m : ℕ} (w : Fin (m + 2) → ℝ) (a b : Fin m) :
    Measurable (fun R : Edge (Fin m) → ℝ ↦ realBackgroundMatrix R w a b) := by
  unfold realBackgroundMatrix
  apply Finset.measurable_sum
  intro j _
  apply measurable_const.mul
  by_cases h : b ≠ j ∧ a ≠ j ∧ a ≠ b
  · simp only [fixedBackgroundM, if_pos h]
    exact (show Continuous (fun R : Edge (Fin m) → ℝ ↦
        typeHafnian (fun s t : {s : Fin m // s ≠ j ∧ s ≠ a ∧ s ≠ b} ↦
          realMatrixOfEdges R s.1 t.1)) by
      unfold typeHafnian typeMatchingMonomial
      fun_prop).measurable
  · simp only [fixedBackgroundM, if_neg h]
    exact measurable_const

theorem realWeightedCofactorSum_twoExposedMatrix
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (u : ℝ)
    (X Y : Fin m → ℝ) (w : Fin (m + 2) → ℝ) :
    (∑ i, w i * matrixCofactor (twoExposedMatrix A u X Y) i) =
      u * (∑ j, w (remainingIndex m j) * matrixCofactor A j) +
        LogdetLean.GramHafnian.realTransposeBilinearPhase X
          (fun a b ↦ ∑ j, w (remainingIndex m j) * fixedBackgroundM A j a b) Y +
        w (exposedXIndex m) * realTransposeDot Y (matrixCofactor A) +
        w (exposedYIndex m) * realTransposeDot X (matrixCofactor A) := by
  have hscalar :
      (∑ j, w (remainingIndex m j) * (u * matrixCofactor A j)) =
        u * ∑ j, w (remainingIndex m j) * matrixCofactor A j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hbilinear :
      (∑ j, w (remainingIndex m j) *
        (∑ a, ∑ b, X a * fixedBackgroundM A j a b * Y b)) =
      LogdetLean.GramHafnian.realTransposeBilinearPhase X
        (fun a b ↦ ∑ j, w (remainingIndex m j) * fixedBackgroundM A j a b) Y := by
    unfold LogdetLean.GramHafnian.realTransposeBilinearPhase
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  change
    ((∑ j : Fin m, w (remainingIndex m j) *
      matrixCofactor (twoExposedMatrix A u X Y) (remainingIndex m j)) +
      w (exposedXIndex m) * matrixCofactor (twoExposedMatrix A u X Y) (exposedXIndex m)) +
      w (exposedYIndex m) * matrixCofactor (twoExposedMatrix A u X Y) (exposedYIndex m) = _
  rw [matrixCofactor_X_eq_sum_Y_Q, matrixCofactor_Y_eq_sum_X_Q]
  simp_rw [matrixCofactor_background_eq_UQ_add_bilinear]
  simp only [matrixX_twoExposedMatrix, matrixY_twoExposedMatrix,
    matrixU_twoExposedMatrix, backgroundQ_twoExposedMatrix, backgroundM_twoExposedMatrix]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hscalar, hbilinear]
  unfold realTransposeDot
  ring

/-! ## Literal characteristic functional and symmetries -/

def realEdgeCofactorPhase {iota : Type*} [Fintype iota] [LinearOrder iota]
    (x : Edge iota → ℝ) (w : iota → ℝ) : ℝ :=
  ∑ j, w j * realEdgeCofactor x j

def realEdgeCofactorPhaseCharacter {iota : Type*} [Fintype iota] [LinearOrder iota]
    (w : iota → ℝ) (x : Edge iota → ℝ) : ℂ :=
  Complex.exp (((realEdgeCofactorPhase x w : ℝ) : ℂ) * Complex.I)

def realEdgeCofactorCharacteristic (iota : Type*) [Fintype iota] [LinearOrder iota]
    (w : iota → ℝ) : ℂ :=
  ∫ x, realEdgeCofactorPhaseCharacter w x ∂realEdgeGaussian iota

@[fun_prop] theorem measurable_realEdgeCofactorPhaseCharacter
    {iota : Type*} [Fintype iota] [LinearOrder iota] (w : iota → ℝ) :
    Measurable (realEdgeCofactorPhaseCharacter w) := by
  unfold realEdgeCofactorPhaseCharacter realEdgeCofactorPhase
  fun_prop

theorem integrable_realEdgeCofactorPhaseCharacter
    {iota : Type*} [Fintype iota] [LinearOrder iota] (w : iota → ℝ) :
    Integrable (realEdgeCofactorPhaseCharacter w) (realEdgeGaussian iota) := by
  apply Integrable.of_bound (measurable_realEdgeCofactorPhaseCharacter w).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [realEdgeCofactorPhaseCharacter, Complex.norm_exp]
  simp

theorem realEdgeCofactor_restrict_equiv
    {alpha beta : Type*} [Fintype alpha] [LinearOrder alpha]
    [Fintype beta] [LinearOrder beta]
    (e : alpha ≃ beta) (x : Edge beta → ℝ) (j : alpha) :
    realEdgeCofactor (realRestrictEdges e.toEmbedding x) j = realEdgeCofactor x (e j) := by
  unfold realEdgeCofactor
  rw [realMatrixOfEdges_restrict]
  exact matrixCofactor_reindex e (realMatrixOfEdges x) (realMatrixOfEdges_symmetric x) j

theorem realEdgeCofactorCharacteristic_reindex
    {alpha beta : Type*} [Fintype alpha] [LinearOrder alpha]
    [Fintype beta] [LinearOrder beta]
    (e : alpha ≃ beta) (w : beta → ℝ) :
    realEdgeCofactorCharacteristic alpha (fun j ↦ w (e j)) =
      realEdgeCofactorCharacteristic beta w := by
  unfold realEdgeCofactorCharacteristic
  rw [← (measurePreserving_realRestrictEdges e.toEmbedding).map_eq,
    integral_map (measurable_realRestrictEdges e.toEmbedding).aemeasurable
      (measurable_realEdgeCofactorPhaseCharacter (fun j ↦ w (e j))).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold realEdgeCofactorPhaseCharacter realEdgeCofactorPhase
  simp_rw [realEdgeCofactor_restrict_equiv]
  congr 3
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

theorem realEdgeCofactorCharacteristic_permutationInvariant (d : ℕ) :
    RealPermutationInvariant (realEdgeCofactorCharacteristic (Fin d)) := by
  intro sigma w
  exact realEdgeCofactorCharacteristic_reindex sigma.symm w

theorem realEdgeCofactorCharacteristic_singletonNormExchangeable
    {iota : Type*} [Fintype iota] [LinearOrder iota] :
    RealSingletonNormExchangeable (realEdgeCofactorCharacteristic iota) := by
  intro i j c
  classical
  by_cases hij : i = j
  · subst j; rfl
  let sigma : Equiv.Perm iota := Equiv.swap i j
  have h := realEdgeCofactorCharacteristic_reindex sigma (realSingleCoordinate j c)
  have hw : (fun l ↦ realSingleCoordinate j c (sigma l)) = realSingleCoordinate i c := by
    funext l
    by_cases hli : l = i
    · subst l; simp [sigma, realSingleCoordinate]
    · by_cases hlj : l = j
      · subst l; simp [sigma, realSingleCoordinate, hij, hli]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
        simp [realSingleCoordinate, hli, hlj]
  rw [hw] at h
  exact congrArg norm h

theorem realEdgeCofactorCharacteristic_negNormInvariant
    {iota : Type*} [Fintype iota] [LinearOrder iota] :
    RealNegNormInvariant (realEdgeCofactorCharacteristic iota) := by
  intro w
  have hpoint (x : Edge iota → ℝ) :
      realEdgeCofactorPhaseCharacter (fun i ↦ -w i) x =
        starRingEnd ℂ (realEdgeCofactorPhaseCharacter w x) := by
    unfold realEdgeCofactorPhaseCharacter realEdgeCofactorPhase
    change Complex.exp (((↑(∑ i, (-w i) * realEdgeCofactor x i) : ℂ) * Complex.I)) =
      starRingEnd ℂ
        (Complex.exp (((↑(∑ i, w i * realEdgeCofactor x i) : ℂ) * Complex.I)))
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, conj_I]
    push_cast
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib]
    ring
  unfold realEdgeCofactorCharacteristic
  simp_rw [hpoint]
  rw [integral_conj, Complex.norm_conj]

/-! ## Conditional representation and compression -/

theorem realCofactorPhase_twoExposedSplit {m : ℕ}
    (x : Edge (Fin (m + 2)) → ℝ) (w : Fin (m + 2) → ℝ) :
    realEdgeCofactorPhase x w =
      (realTwoExposedSplit m x).2.1 * realBackgroundEll (realTwoExposedSplit m x).1 w +
      realBilinearPhase (realBackgroundMatrix (realTwoExposedSplit m x).1 w)
        (realEdgeCofactor (realTwoExposedSplit m x).1)
        (w (exposedXIndex m)) (w (exposedYIndex m))
        (realTwoExposedSplit m x).2.2.1 (realTwoExposedSplit m x).2.2.2 := by
  unfold realEdgeCofactorPhase realBackgroundEll realBackgroundMatrix realBilinearPhase
  unfold realEdgeCofactor
  rw [← realTwoExposedMatrix_realTwoExposedSplit m x,
    realWeightedCofactorSum_twoExposedMatrix]
  ring

theorem realEdgeCofactorCharacteristic_eq_conditional
    {m : ℕ} (w : Fin (m + 2) → ℝ) :
    realEdgeCofactorCharacteristic (Fin (m + 2)) w =
      ∫ R : Edge (Fin m) → ℝ,
        realConditionalKernel (realBackgroundEll R w) (realBackgroundMatrix R w)
          (realEdgeCofactor R) (w (exposedXIndex m)) (w (exposedYIndex m))
        ∂realEdgeGaussian (Fin m) := by
  let f : (Edge (Fin m) → ℝ) × RealExposedSample m → ℂ := fun p ↦
    Complex.exp (((((p.2.1 * realBackgroundEll p.1 w +
      realBilinearPhase (realBackgroundMatrix p.1 w) (realEdgeCofactor p.1)
        (w (exposedXIndex m)) (w (exposedYIndex m)) p.2.2.1 p.2.2.2) : ℝ) : ℂ) *
          Complex.I))
  have hfmeas : Measurable f := by
    unfold f realBilinearPhase realTransposeDot
    unfold LogdetLean.GramHafnian.realTransposeBilinearPhase
    fun_prop
  have hf : Integrable f ((realEdgeGaussian (Fin m)).prod (realExposedMeasure m)) := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with p
    unfold f
    rw [Complex.norm_exp]
    simp
  unfold realEdgeCofactorCharacteristic
  calc
    _ = ∫ x : Edge (Fin (m + 2)) → ℝ, f (realTwoExposedSplit m x)
        ∂realEdgeGaussian (Fin (m + 2)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold realEdgeCofactorPhaseCharacter f
      rw [realCofactorPhase_twoExposedSplit]
    _ = ∫ p, f p ∂((realEdgeGaussian (Fin m)).prod (realExposedMeasure m)) := by
      rw [← (measurePreserving_realTwoExposedSplit m).map_eq]
      symm
      exact integral_map (measurePreserving_realTwoExposedSplit m).measurable.aemeasurable
        (by rw [(measurePreserving_realTwoExposedSplit m).map_eq]; exact hf.aestronglyMeasurable)
    _ = _ := by
      rw [integral_prod _ hf]
      rfl

theorem realEdgeCofactorCharacteristic_two_exposed_max
    {m : ℕ} (w wL wR : Fin (m + 2) → ℝ)
    {theta : ℝ} (ht : 0 < theta) (ht1 : theta < 1)
    (hbgL : ∀ j : Fin m, wL (remainingIndex m j) = w (remainingIndex m j))
    (hbgR : ∀ j : Fin m, wR (remainingIndex m j) = w (remainingIndex m j))
    (hLY : wL (exposedYIndex m) = 0) (hRX : wR (exposedXIndex m) = 0)
    (hX : w (exposedXIndex m) = Real.sqrt theta * wL (exposedXIndex m))
    (hY : w (exposedYIndex m) = Real.sqrt (1 - theta) * wR (exposedYIndex m)) :
    ‖realEdgeCofactorCharacteristic (Fin (m + 2)) w‖ ≤
      max ‖realEdgeCofactorCharacteristic (Fin (m + 2)) wL‖
        ‖realEdgeCofactorCharacteristic (Fin (m + 2)) wR‖ := by
  have hellL R : realBackgroundEll R wL = realBackgroundEll R w := by
    unfold realBackgroundEll
    apply Finset.sum_congr rfl
    intro j _; rw [hbgL j]
  have hellR R : realBackgroundEll R wR = realBackgroundEll R w := by
    unfold realBackgroundEll
    apply Finset.sum_congr rfl
    intro j _; rw [hbgR j]
  have hML R : realBackgroundMatrix R wL = realBackgroundMatrix R w := by
    funext a b
    unfold realBackgroundMatrix
    apply Finset.sum_congr rfl
    intro j _; rw [hbgL j]
  have hMR R : realBackgroundMatrix R wR = realBackgroundMatrix R w := by
    funext a b
    unfold realBackgroundMatrix
    apply Finset.sum_congr rfl
    intro j _; rw [hbgR j]
  rw [realEdgeCofactorCharacteristic_eq_conditional w,
    realEdgeCofactorCharacteristic_eq_conditional wL,
    realEdgeCofactorCharacteristic_eq_conditional wR]
  simp_rw [hellL, hellR, hML, hMR, hLY, hRX, hX, hY]
  exact norm_integral_realConditionalKernel_sqrt_le_max
    (realEdgeGaussian (Fin m)) (fun R ↦ realBackgroundEll R w)
    (fun R ↦ realBackgroundMatrix R w) realEdgeCofactor
    (measurable_realBackgroundEll w) (measurable_realBackgroundMatrix_entry w)
    measurable_realEdgeCofactor (wL (exposedXIndex m)) (wR (exposedYIndex m)) ht ht1

theorem realEdgeCofactorCharacteristic_last_two_endpoints
    (m : ℕ) (w : Fin (m + 2) → ℝ)
    (hX : w (exposedXIndex m) ≠ 0) (hY : w (exposedYIndex m) ≠ 0) :
    ∃ wL wR,
      realCoordinateSupportCard wL < realCoordinateSupportCard w ∧
      realCoordinateSupportCard wR < realCoordinateSupportCard w ∧
      realCoordinateEnergy wL = realCoordinateEnergy w ∧
      realCoordinateEnergy wR = realCoordinateEnergy w ∧
      ‖realEdgeCofactorCharacteristic (Fin (m + 2)) w‖ ≤
        max ‖realEdgeCofactorCharacteristic (Fin (m + 2)) wL‖
          ‖realEdgeCofactorCharacteristic (Fin (m + 2)) wR‖ := by
  let theta := realExposedTheta w
  let wL := realLeftExposedEndpoint w theta
  let wR := realRightExposedEndpoint w theta
  refine ⟨wL, wR, realSupport_leftEndpoint_lt hX hY,
    realSupport_rightEndpoint_lt hX hY, realCoordinateEnergy_leftEndpoint hX hY,
    realCoordinateEnergy_rightEndpoint hX hY, ?_⟩
  apply realEdgeCofactorCharacteristic_two_exposed_max w wL wR
    (realExposedTheta_pos hX hY) (realExposedTheta_lt_one hX hY)
  · exact realLeftEndpoint_background w theta
  · exact realRightEndpoint_background w theta
  · exact realLeftEndpoint_Y w theta
  · exact realRightEndpoint_X w theta
  · change w (exposedXIndex m) = Real.sqrt theta *
      realLeftExposedEndpoint w theta (exposedXIndex m)
    rw [realLeftEndpoint_X]
    simpa [theta, div_eq_mul_inv, mul_comm] using
      (mul_div_cancel₀ (w (exposedXIndex m))
        (Real.sqrt_ne_zero'.mpr (realExposedTheta_pos hX hY))).symm
  · change w (exposedYIndex m) = Real.sqrt (1 - theta) *
      realRightExposedEndpoint w theta (exposedYIndex m)
    rw [realRightEndpoint_Y]
    simpa [theta, div_eq_mul_inv, mul_comm] using
      (mul_div_cancel₀ (w (exposedYIndex m))
        (Real.sqrt_ne_zero'.mpr
          (sub_pos.mpr (realExposedTheta_lt_one hX hY)))).symm

theorem realEdgeCofactorCharacteristic_global_two_endpoints (m : ℕ) :
    ∀ w : Fin (m + 2) → ℝ, 1 < realCoordinateSupportCard w →
      ∃ wLeft wRight : Fin (m + 2) → ℝ,
        realCoordinateSupportCard wLeft < realCoordinateSupportCard w ∧
        realCoordinateSupportCard wRight < realCoordinateSupportCard w ∧
        realCoordinateEnergy wLeft = realCoordinateEnergy w ∧
        realCoordinateEnergy wRight = realCoordinateEnergy w ∧
        ‖realEdgeCofactorCharacteristic (Fin (m + 2)) w‖ ≤
          max ‖realEdgeCofactorCharacteristic (Fin (m + 2)) wLeft‖
            ‖realEdgeCofactorCharacteristic (Fin (m + 2)) wRight‖ := by
  apply real_global_two_endpoints_of_last_two
    (realEdgeCofactorCharacteristic (Fin (m + 2)))
    (realEdgeCofactorCharacteristic_permutationInvariant (m + 2))
  intro w hX hY
  exact realEdgeCofactorCharacteristic_last_two_endpoints m w hX hY

theorem realEdgeCofactorCharacteristic_norm_le_singleton
    (r : ℕ) (hr : 2 ≤ r) (base : Fin (2 * r - 1))
    (w : Fin (2 * r - 1) → ℝ) :
    ‖realEdgeCofactorCharacteristic (Fin (2 * r - 1)) w‖ ≤
      ‖realEdgeCofactorCharacteristic (Fin (2 * r - 1))
        (realSingleCoordinate base (Real.sqrt (realCoordinateEnergy w)))‖ := by
  let _ : Nonempty (Fin (2 * r - 1)) := ⟨base⟩
  have hdim : (2 * r - 3) + 2 = 2 * r - 1 := by omega
  have hglobal := realEdgeCofactorCharacteristic_global_two_endpoints (2 * r - 3)
  rw [hdim] at hglobal
  exact finite_real_coordinate_compression
    (realEdgeCofactorCharacteristic (Fin (2 * r - 1))) base
    realEdgeCofactorCharacteristic_singletonNormExchangeable
    realEdgeCofactorCharacteristic_negNormInvariant
    hglobal w

/-! ## Singleton variance mixture -/

theorem realEdgeCofactor_last_eq_restrictedHafnian {n : ℕ}
    (x : Edge (Fin (n + 1)) → ℝ) :
    realEdgeCofactor x (Fin.last n) =
      realEdgeHafnian (realRestrictEdges (initialVertexEmbedding n) x) := by
  unfold realEdgeCofactor matrixCofactor realEdgeHafnian
  rw [realMatrixOfEdges_restrict]
  have h := typeHafnian_reindex_orderIso (withoutLastOrderIso n)
    (fun a b : {a : Fin (n + 1) // a ≠ Fin.last n} ↦ realMatrixOfEdges x a.1 b.1)
  simpa [withoutLastOrderIso, initialVertexEmbedding] using h.symm

theorem integral_exp_mul_realEdgeHafnian_eq_energy_mixture (n : ℕ) (t : ℝ) :
    (∫ x : Edge (Fin (n + 1)) → ℝ,
      Complex.exp ((((t * realEdgeHafnian x : ℝ) : ℂ) * Complex.I))
      ∂realEdgeGaussian (Fin (n + 1))) =
      ∫ A : Edge (Fin n) → ℝ,
        Complex.exp (-(((realEdgeCofactorEnergy A * t ^ 2 : ℝ) : ℂ) / 2))
        ∂realEdgeGaussian (Fin n) := by
  let f : (Edge (Fin n) → ℝ) × (Fin n → ℝ) → ℂ := fun p ↦
    Complex.exp ((((t * iidRealLinearForm (realEdgeCofactor p.1) p.2 : ℝ) : ℂ) *
      Complex.I))
  have hf : Integrable f
      ((realEdgeGaussian (Fin n)).prod (standardRealGaussianProduct (Fin n))) := by
    apply Integrable.of_bound (by unfold f iidRealLinearForm; fun_prop) 1
    filter_upwards [] with p
    unfold f
    rw [Complex.norm_exp]
    simp
  calc
    _ = ∫ x : Edge (Fin (n + 1)) → ℝ, f (realLastVertexSplit n x)
        ∂realEdgeGaussian (Fin (n + 1)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold f
      rw [realEdgeHafnian_eq_lastVertexLinearForm]
    _ = ∫ p, f p ∂((realEdgeGaussian (Fin n)).prod
        (standardRealGaussianProduct (Fin n))) := by
      rw [← (measurePreserving_realLastVertexSplit n).map_eq]
      symm
      exact integral_map (measurePreserving_realLastVertexSplit n).measurable.aemeasurable
        (by rw [(measurePreserving_realLastVertexSplit n).map_eq]; exact hf.aestronglyMeasurable)
    _ = ∫ A, ∫ g, f (A, g) ∂standardRealGaussianProduct (Fin n)
        ∂realEdgeGaussian (Fin n) := integral_prod _ hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with A
      change (∫ g : Fin n → ℝ,
        Complex.exp ((((t * iidRealLinearForm (realEdgeCofactor A) g : ℝ) : ℂ) *
          Complex.I)) ∂standardRealGaussianProduct (Fin n)) = _
      calc
        _ = ∫ g : Fin n → ℝ,
            Complex.exp ((((iidRealLinearForm (realEdgeCofactor A) g * t : ℝ) : ℂ) *
              Complex.I)) ∂standardRealGaussianProduct (Fin n) := by
          apply integral_congr_ae
          filter_upwards [] with g
          rw [mul_comm t]
        _ = charFun ((standardRealGaussianProduct (Fin n)).map
              (iidRealLinearForm (realEdgeCofactor A))) t := by
          rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
          apply integral_congr_ae
          filter_upwards [] with g
          congr 2
          push_cast
          rw [RCLike.inner_apply]
          simp [mul_comm]
        _ = _ := by
          rw [charFun_iidRealLinearForm]
          congr 1
          unfold realEdgeCofactorEnergy realCoefficientEnergy
          push_cast
          ring

theorem realEdgeCofactorCharacteristic_singleton_last (n : ℕ) (t : ℝ) :
    realEdgeCofactorCharacteristic (Fin (n + 2))
      (realSingleCoordinate (Fin.last (n + 1)) t) =
      ∫ A : Edge (Fin n) → ℝ,
        Complex.exp (-(((realEdgeCofactorEnergy A * t ^ 2 : ℝ) : ℂ) / 2))
        ∂realEdgeGaussian (Fin n) := by
  unfold realEdgeCofactorCharacteristic
  have hphase (x : Edge (Fin (n + 2)) → ℝ) :
      realEdgeCofactorPhaseCharacter (realSingleCoordinate (Fin.last (n + 1)) t) x =
        Complex.exp ((((t * realEdgeHafnian
          (realRestrictEdges (initialVertexEmbedding (n + 1)) x) : ℝ) : ℂ) *
            Complex.I)) := by
    unfold realEdgeCofactorPhaseCharacter realEdgeCofactorPhase
    simp [realSingleCoordinate, realEdgeCofactor_last_eq_restrictedHafnian]
  simp_rw [hphase]
  calc
    _ = ∫ x : Edge (Fin (n + 1)) → ℝ,
        Complex.exp ((((t * realEdgeHafnian x : ℝ) : ℂ) * Complex.I))
        ∂realEdgeGaussian (Fin (n + 1)) := by
      rw [← (measurePreserving_realRestrictEdges
        (initialVertexEmbedding (n + 1))).map_eq]
      symm
      exact integral_map
        (measurePreserving_realRestrictEdges (initialVertexEmbedding (n + 1))).measurable.aemeasurable
        (by fun_prop)
    _ = _ := integral_exp_mul_realEdgeHafnian_eq_energy_mixture n t

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
