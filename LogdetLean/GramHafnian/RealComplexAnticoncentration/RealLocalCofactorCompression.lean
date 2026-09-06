import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealCofactorPhaseAlgebra
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.LocalCofactorCompression
/-!
# Literal local Fourier compression for real Gram cofactors

Two real Gaussian columns are exposed.  Conditional on all remaining
columns, their cofactor Fourier phase is the general bilinear Gaussian phase
`gᵀTh + gᵀqb + hᵀqa`.  The already internal completed-square theorem then
gives endpoint positivity and exact geometric interpolation.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 2000000

abbrev RealCofactorSpace (k : ℕ) := RealGaussianEuclideanSpace k

def finiteRealGramCofactorPhase
    {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
    (A : ι → (Fin k → ℝ)) (w : ι → ℝ) : ℝ :=
  ∑ j : ι, w j * finiteRealGramCofactorVector A j

def finiteRealGramCofactorPhaseCharacter
    {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
    (w : ι → ℝ) (A : ι → (Fin k → ℝ)) : ℂ :=
  Complex.exp ((finiteRealGramCofactorPhase A w : ℂ) * Complex.I)

def finiteRealGramCofactorCharacteristic
    (ι : Type*) [Fintype ι] [LinearOrder ι] (k : ℕ) :
    (ι → ℝ) → ℂ :=
  fun w ↦ ∫ A : ι → (Fin k → ℝ),
    finiteRealGramCofactorPhaseCharacter w A
      ∂(Measure.pi fun _ : ι ↦ standardRealGaussianVectorMeasure k)

theorem continuous_finiteRealGramCofactorVector_apply
    {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ} (j : ι) :
    Continuous (fun A : ι → (Fin k → ℝ) ↦
      finiteRealGramCofactorVector A j) := by
  unfold finiteRealGramCofactorVector realColumnTransposeGram typeHafnian
    typeMatchingMonomial
  fun_prop

@[fun_prop] theorem measurable_finiteRealGramCofactorVector_apply
    {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ} (j : ι) :
    Measurable (fun A : ι → (Fin k → ℝ) ↦
      finiteRealGramCofactorVector A j) :=
  (continuous_finiteRealGramCofactorVector_apply j).measurable

@[fun_prop] theorem measurable_finiteRealGramCofactorPhaseCharacter
    {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
    (w : ι → ℝ) :
    Measurable (finiteRealGramCofactorPhaseCharacter (k := k) w) := by
  unfold finiteRealGramCofactorPhaseCharacter finiteRealGramCofactorPhase
  fun_prop

theorem finiteRealGramCofactorVector_reindex_equiv
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] {k : ℕ}
    (e : α ≃ β) (A : β → (Fin k → ℝ)) (i : α) :
    finiteRealGramCofactorVector (fun j ↦ A (e j)) i =
      finiteRealGramCofactorVector A (e i) := by
  apply Complex.ofReal_injective
  rw [ofReal_finiteRealGramCofactorVector,
    ofReal_finiteRealGramCofactorVector]
  have h := finiteGramCofactorVector_reindex_equiv e
    (complexifyRealColumns A) i
  change finiteGramCofactorVector
      (complexifyRealColumns (fun j ↦ A (e j))) i =
    finiteGramCofactorVector (complexifyRealColumns A) (e i) at h
  change finiteGramCofactorVector
      (complexifyRealColumns (fun j ↦ A (e j))) i =
    finiteGramCofactorVector (complexifyRealColumns A) (e i)
  exact h

theorem finiteRealGramCofactorPhase_reindex_equiv
    {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] {k : ℕ}
    (e : α ≃ β) (A : β → (Fin k → ℝ)) (w : β → ℝ) :
    finiteRealGramCofactorPhase (fun i ↦ A (e i)) (fun i ↦ w (e i)) =
      finiteRealGramCofactorPhase A w := by
  unfold finiteRealGramCofactorPhase
  simp_rw [finiteRealGramCofactorVector_reindex_equiv]
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

def reindexFiniteRealColumnFamily
    {α β : Type*} {k : ℕ} (e : α ≃ β)
    (A : β → (Fin k → ℝ)) : α → (Fin k → ℝ) :=
  fun i ↦ A (e i)

theorem measurePreserving_reindexFiniteRealColumnFamily_pi
    {ι : Type*} [Fintype ι] {k : ℕ} (sigma : Equiv.Perm ι) :
    MeasurePreserving (reindexFiniteRealColumnFamily (k := k) sigma)
      (Measure.pi fun _ : ι ↦ standardRealGaussianVectorMeasure k)
      (Measure.pi fun _ : ι ↦ standardRealGaussianVectorMeasure k) := by
  have hfun : reindexFiniteRealColumnFamily (k := k) sigma =
      (MeasurableEquiv.piCongrLeft
        (fun _ : ι ↦ Fin k → ℝ) sigma.symm :
          (ι → (Fin k → ℝ)) → (ι → (Fin k → ℝ))) := by
    funext A
    ext i p
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ι ↦ Fin k → ℝ) sigma.symm A (sigma i)
    simpa [reindexFiniteRealColumnFamily] using congrArg (fun f ↦ f p) h.symm
  rw [hfun]
  simpa using (measurePreserving_piCongrLeft
    (α := fun _ : ι ↦ Fin k → ℝ)
    (fun _ : ι ↦ standardRealGaussianVectorMeasure k) sigma.symm)

theorem finiteRealGramCofactorCharacteristic_reindex_perm
    {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
    (sigma : Equiv.Perm ι) (w : ι → ℝ) :
    finiteRealGramCofactorCharacteristic ι k (fun i ↦ w (sigma i)) =
      finiteRealGramCofactorCharacteristic ι k w := by
  let e : (ι → (Fin k → ℝ)) ≃ᵐ (ι → (Fin k → ℝ)) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι ↦ Fin k → ℝ) sigma.symm
  have he : MeasurePreserving e
      (Measure.pi fun _ : ι ↦ standardRealGaussianVectorMeasure k)
      (Measure.pi fun _ : ι ↦ standardRealGaussianVectorMeasure k) := by
    have h := measurePreserving_reindexFiniteRealColumnFamily_pi
      (k := k) sigma
    rw [show (e : (ι → (Fin k → ℝ)) → (ι → (Fin k → ℝ))) =
      reindexFiniteRealColumnFamily (k := k) sigma by
        funext A
        ext i p
        have h := MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : ι ↦ Fin k → ℝ) sigma.symm A (sigma i)
        simpa [e, reindexFiniteRealColumnFamily] using
          congrArg (fun f ↦ f p) h]
    exact h
  unfold finiteRealGramCofactorCharacteristic
  rw [← he.integral_comp']
  apply integral_congr_ae
  filter_upwards [] with A
  unfold finiteRealGramCofactorPhaseCharacter
  congr 2
  have he_apply : e A = reindexFiniteRealColumnFamily (k := k) sigma A := by
    ext i p
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ι ↦ Fin k → ℝ) sigma.symm A (sigma i)
    simpa [e, reindexFiniteRealColumnFamily] using
      congrArg (fun f ↦ f p) h
  rw [he_apply]
  exact congrArg ((↑) : ℝ → ℂ)
    (finiteRealGramCofactorPhase_reindex_equiv sigma A w)

/-! ## Exact iid disintegration into background and two displayed columns -/

def splitTwoExposedRealColumns (m k : ℕ) :
    (Fin (m + 2) → (Fin k → ℝ)) ≃ᵐ
      (Fin k → ℝ) × ((Fin k → ℝ) × (Fin m → (Fin k → ℝ))) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 2) ↦ Fin k → ℝ) (Fin.last (m + 1))).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin k → ℝ))
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (m + 1) ↦ Fin k → ℝ) (Fin.last m)))

theorem splitTwoExposedRealColumns_apply
    {m k : ℕ} (A : Fin (m + 2) → (Fin k → ℝ)) :
    splitTwoExposedRealColumns m k A =
      (A (exposedYIndex m),
        (A (exposedXIndex m), fun i ↦ A (remainingIndex m i))) := by
  unfold splitTwoExposedRealColumns
  rw [MeasurableEquiv.trans_apply]
  change (A (Fin.last (m + 1)),
    (A ((Fin.last (m + 1)).succAbove (Fin.last m)),
      fun i ↦ A ((Fin.last (m + 1)).succAbove ((Fin.last m).succAbove i)))) = _
  apply Prod.ext
  · change A (Fin.last (m + 1)) = A (exposedYIndex m)
    congr 1
  · change
      (A ((Fin.last (m + 1)).succAbove (Fin.last m)),
        fun i ↦ A ((Fin.last (m + 1)).succAbove ((Fin.last m).succAbove i))) =
      (A (exposedXIndex m), fun i ↦ A (remainingIndex m i))
    apply Prod.ext
    · change A ((Fin.last (m + 1)).succAbove (Fin.last m)) =
        A (exposedXIndex m)
      rw [Fin.succAbove_last_apply]
      congr 1
    · funext i
      change A ((Fin.last (m + 1)).succAbove ((Fin.last m).succAbove i)) =
        A (remainingIndex m i)
      rw [Fin.succAbove_last_apply, Fin.succAbove_last_apply]
      congr 1

theorem measurePreserving_splitTwoExposedRealColumns (m k : ℕ) :
    MeasurePreserving (splitTwoExposedRealColumns m k)
      (Measure.pi fun _ : Fin (m + 2) ↦ standardRealGaussianVectorMeasure k)
      ((standardRealGaussianVectorMeasure k).prod
        ((standardRealGaussianVectorMeasure k).prod
          (Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k))) := by
  have hY := measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 2) ↦ standardRealGaussianVectorMeasure k)
      (Fin.last (m + 1))
  have hX := measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) ↦ standardRealGaussianVectorMeasure k) (Fin.last m)
  exact ((MeasurePreserving.id (standardRealGaussianVectorMeasure k)).prod hX).comp hY

def splitTwoExposedRealColumnsRXY (m k : ℕ) :
    (Fin (m + 2) → (Fin k → ℝ)) ≃ᵐ
      (Fin m → (Fin k → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ)) :=
  (splitTwoExposedRealColumns m k).trans yxrToRxy

theorem splitTwoExposedRealColumnsRXY_apply
    {m k : ℕ} (A : Fin (m + 2) → (Fin k → ℝ)) :
    splitTwoExposedRealColumnsRXY m k A =
      ((fun i ↦ A (remainingIndex m i)),
        (A (exposedXIndex m), A (exposedYIndex m))) := by
  rw [splitTwoExposedRealColumnsRXY, MeasurableEquiv.trans_apply,
    splitTwoExposedRealColumns_apply]
  rfl

theorem measurePreserving_splitTwoExposedRealColumnsRXY (m k : ℕ) :
    MeasurePreserving (splitTwoExposedRealColumnsRXY m k)
      (Measure.pi fun _ : Fin (m + 2) ↦ standardRealGaussianVectorMeasure k)
      ((Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k).prod
        ((standardRealGaussianVectorMeasure k).prod
          (standardRealGaussianVectorMeasure k))) := by
  exact (measurePreserving_yxrToRxy
    (standardRealGaussianVectorMeasure k) (standardRealGaussianVectorMeasure k)
      (Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k)).comp
        (measurePreserving_splitTwoExposedRealColumns m k)

def assembleTwoExposedRealColumns {m k : ℕ}
    (R : Fin m → (Fin k → ℝ)) (X Y : Fin k → ℝ) :
    Fin (m + 2) → (Fin k → ℝ) :=
  (splitTwoExposedRealColumnsRXY m k).symm (R, (X, Y))

theorem assembleTwoExposedRealColumns_coordinates
    {m k : ℕ} (R : Fin m → (Fin k → ℝ)) (X Y : Fin k → ℝ) :
    ((fun i ↦ assembleTwoExposedRealColumns R X Y (remainingIndex m i)) = R) ∧
      assembleTwoExposedRealColumns R X Y (exposedXIndex m) = X ∧
      assembleTwoExposedRealColumns R X Y (exposedYIndex m) = Y := by
  have h := splitTwoExposedRealColumnsRXY_apply
    (assembleTwoExposedRealColumns R X Y)
  rw [assembleTwoExposedRealColumns,
    (splitTwoExposedRealColumnsRXY m k).apply_symm_apply] at h
  rcases Prod.mk.inj h with ⟨hR, hXY⟩
  rcases Prod.mk.inj hXY with ⟨hX, hY⟩
  exact ⟨hR.symm, hX.symm, hY.symm⟩

/-! ## The background-dependent continuous maps -/

def realCofactorBackgroundPhaseMatrix {m k : ℕ}
    (A : RealTwoExposedColumnFamily m k) (w : Fin (m + 2) → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun p q ↦ ∑ j : Fin m, w (remainingIndex m j) * realCofactorM A j p q

def realCofactorBackgroundPhaseCLM {m k : ℕ}
    (A : RealTwoExposedColumnFamily m k) (w : Fin (m + 2) → ℝ) :
    RealCofactorSpace k →L[ℝ] RealCofactorSpace k :=
  (Matrix.toEuclideanLin (realCofactorBackgroundPhaseMatrix A w)).toContinuousLinearMap

def realCofactorLinearPhaseCLM {m k : ℕ}
    (A : RealTwoExposedColumnFamily m k) : ℝ →L[ℝ] RealCofactorSpace k :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    (WithLp.toLp 2 (realCofactorQ A))

theorem inner_realCofactorBackgroundPhaseCLM_eq
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k)
    (w : Fin (m + 2) → ℝ) (X Y : Fin k → ℝ) :
    inner ℝ (WithLp.toLp 2 X)
        (realCofactorBackgroundPhaseCLM A w (WithLp.toLp 2 Y)) =
      ∑ j : Fin m, w (remainingIndex m j) *
        realTransposeBilinear X (realCofactorM A j) Y := by
  unfold realCofactorBackgroundPhaseCLM
  change
    inner ℝ (WithLp.toLp 2 X)
        (Matrix.toEuclideanLin (realCofactorBackgroundPhaseMatrix A w)
          (WithLp.toLp 2 Y)) = _
  rw [inner_toEuclideanLin_eq_realTransposeBilinearPhase]
  unfold realTransposeBilinearPhase realCofactorBackgroundPhaseMatrix
    realTransposeBilinear
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    enter [2, p]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  ring

theorem inner_realCofactorLinearPhaseCLM_eq
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k)
    (X : Fin k → ℝ) (a : ℝ) :
    inner ℝ (WithLp.toLp 2 X) (realCofactorLinearPhaseCLM A a) =
      a * realTransposeDot X (realCofactorQ A) := by
  unfold realCofactorLinearPhaseCLM realTransposeDot
  rw [PiLp.inner_apply]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    PiLp.toLp_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  change (a * realCofactorQ A p) * X p =
    a * (X p * realCofactorQ A p)
  ring

theorem realRemainingHafnianDeleteOne_congr_background
    {m k : ℕ} {A B : RealTwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i))
    (a : Fin m) :
    realRemainingHafnianDeleteOne A a =
      realRemainingHafnianDeleteOne B a := by
  unfold realRemainingHafnianDeleteOne
  congr 1
  funext i j
  unfold realColumnTransposeGram
  apply Finset.sum_congr rfl
  intro p _hp
  change A (remainingIndex m i.1) p * A (remainingIndex m j.1) p =
    B (remainingIndex m i.1) p * B (remainingIndex m j.1) p
  rw [hAB i.1, hAB j.1]

theorem realRemainingHafnianDeleteThree_congr_background
    {m k : ℕ} {A B : RealTwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i))
    (j a b : Fin m) :
    realRemainingHafnianDeleteThree A j a b =
      realRemainingHafnianDeleteThree B j a b := by
  unfold realRemainingHafnianDeleteThree
  congr 1
  funext i l
  unfold realColumnTransposeGram
  apply Finset.sum_congr rfl
  intro p _hp
  change A (remainingIndex m i.1) p * A (remainingIndex m l.1) p =
    B (remainingIndex m i.1) p * B (remainingIndex m l.1) p
  rw [hAB i.1, hAB l.1]

theorem realCofactorQ_congr_background
    {m k : ℕ} {A B : RealTwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i)) :
    realCofactorQ A = realCofactorQ B := by
  funext p
  unfold realCofactorQ
  apply Finset.sum_congr rfl
  intro a _ha
  rw [realRemainingHafnianDeleteOne_congr_background hAB a, hAB a]

theorem realCofactorM_congr_background
    {m k : ℕ} {A B : RealTwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i))
    (j : Fin m) : realCofactorM A j = realCofactorM B j := by
  funext p q
  unfold realCofactorM
  rw [realRemainingHafnianDeleteOne_congr_background hAB j]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro b _hb
  apply Finset.sum_congr rfl
  intro a _ha
  rw [realRemainingHafnianDeleteThree_congr_background hAB j a.1 b.1,
    hAB a.1, hAB b.1]

def backgroundRealCofactorT {m k : ℕ}
    (R : Fin m → (Fin k → ℝ)) (w : Fin (m + 2) → ℝ) :
    RealCofactorSpace k →L[ℝ] RealCofactorSpace k :=
  realCofactorBackgroundPhaseCLM (assembleTwoExposedRealColumns R 0 0) w

def backgroundRealCofactorL {m k : ℕ}
    (R : Fin m → (Fin k → ℝ)) : ℝ →L[ℝ] RealCofactorSpace k :=
  realCofactorLinearPhaseCLM (assembleTwoExposedRealColumns R 0 0)

theorem realCofactorBackgroundPhaseCLM_assemble_eq
    {m k : ℕ} (R : Fin m → (Fin k → ℝ)) (X Y : Fin k → ℝ)
    (w : Fin (m + 2) → ℝ) :
    realCofactorBackgroundPhaseCLM (assembleTwoExposedRealColumns R X Y) w =
      backgroundRealCofactorT R w := by
  unfold realCofactorBackgroundPhaseCLM backgroundRealCofactorT
  apply congrArg (fun M : Matrix (Fin k) (Fin k) ℝ ↦
    (Matrix.toEuclideanLin M).toContinuousLinearMap)
  funext p q
  unfold realCofactorBackgroundPhaseMatrix
  apply Finset.sum_congr rfl
  intro j _hj
  rw [realCofactorM_congr_background
    (fun i ↦ (congrFun (assembleTwoExposedRealColumns_coordinates R X Y).1 i).trans
      (congrFun (assembleTwoExposedRealColumns_coordinates R (0 : Fin k → ℝ) 0).1 i).symm)
    j]

theorem realCofactorLinearPhaseCLM_assemble_eq
    {m k : ℕ} (R : Fin m → (Fin k → ℝ)) (X Y : Fin k → ℝ) :
    realCofactorLinearPhaseCLM (assembleTwoExposedRealColumns R X Y) =
      backgroundRealCofactorL R := by
  unfold realCofactorLinearPhaseCLM backgroundRealCofactorL
  rw [realCofactorQ_congr_background
    (fun i ↦ (congrFun (assembleTwoExposedRealColumns_coordinates R X Y).1 i).trans
      (congrFun (assembleTwoExposedRealColumns_coordinates R (0 : Fin k → ℝ) 0).1 i).symm)]
  rfl

theorem finiteRealGramCofactorPhase_assemble_eq_bilinear
    {m k : ℕ} (R : Fin m → (Fin k → ℝ))
    (X Y : Fin k → ℝ) (w : Fin (m + 2) → ℝ) :
    finiteRealGramCofactorPhase (assembleTwoExposedRealColumns R X Y) w =
      inner ℝ (WithLp.toLp 2 X)
          (backgroundRealCofactorT R w (WithLp.toLp 2 Y)) +
        inner ℝ (WithLp.toLp 2 X)
          (backgroundRealCofactorL R (w (exposedYIndex m))) +
        inner ℝ (WithLp.toLp 2 Y)
          (backgroundRealCofactorL R (w (exposedXIndex m))) := by
  let A := assembleTwoExposedRealColumns R X Y
  have hcoord := assembleTwoExposedRealColumns_coordinates R X Y
  unfold finiteRealGramCofactorPhase
  rw [sum_fin_two_exposed]
  change
    (∑ j : Fin m, w (remainingIndex m j) *
        finiteRealGramCofactorVector A (remainingIndex m j)) +
      w (exposedXIndex m) * finiteRealGramCofactorVector A (exposedXIndex m) +
      w (exposedYIndex m) * finiteRealGramCofactorVector A (exposedYIndex m) = _
  simp_rw [finiteRealGramCofactor_background_eq_realTransposeBilinear_X_M_Y,
    finiteRealGramCofactor_X_eq_realTransposeDot_Y_q,
    finiteRealGramCofactor_Y_eq_realTransposeDot_X_q]
  rw [← inner_realCofactorBackgroundPhaseCLM_eq A w
      (A (exposedXIndex m)) (A (exposedYIndex m)),
    ← inner_realCofactorLinearPhaseCLM_eq A (A (exposedXIndex m))
      (w (exposedYIndex m)),
    ← inner_realCofactorLinearPhaseCLM_eq A (A (exposedYIndex m))
      (w (exposedXIndex m)),
    realCofactorBackgroundPhaseCLM_assemble_eq,
    realCofactorLinearPhaseCLM_assemble_eq]
  dsimp [A]
  rw [hcoord.2.1, hcoord.2.2]
  ring

theorem measurePreserving_toLp_standardRealGaussianVector (k : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : (Fin k → ℝ) → RealCofactorSpace k)
      (standardRealGaussianVectorMeasure k) (stdGaussian (RealCofactorSpace k)) := by
  refine ⟨WithLp.measurable_toLp 2 (Fin k → ℝ), ?_⟩
  simpa [standardRealGaussianVectorMeasure] using
    (map_pi_eq_stdGaussian :
      (Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1)).map (WithLp.toLp 2) =
        stdGaussian (RealCofactorSpace k))

def conditionalRealCofactorCharacteristic {m k : ℕ}
    (R : Fin m → (Fin k → ℝ)) (w : Fin (m + 2) → ℝ) : ℂ :=
  ∫ p : (Fin k → ℝ) × (Fin k → ℝ),
    finiteRealGramCofactorPhaseCharacter w
      (assembleTwoExposedRealColumns R p.1 p.2)
    ∂((standardRealGaussianVectorMeasure k).prod
      (standardRealGaussianVectorMeasure k))

theorem conditionalRealCofactorCharacteristic_eq_bilinearGaussianIntegral
    {m k : ℕ} (R : Fin m → (Fin k → ℝ))
    (w : Fin (m + 2) → ℝ) :
    conditionalRealCofactorCharacteristic R w =
      bilinearGaussianIntegral (backgroundRealCofactorT R w)
        (backgroundRealCofactorL R)
        (w (exposedXIndex m)) (w (exposedYIndex m)) := by
  let rho : ((Fin k → ℝ) × (Fin k → ℝ)) →
      (RealCofactorSpace k × RealCofactorSpace k) :=
    fun p ↦ (WithLp.toLp 2 p.1, WithLp.toLp 2 p.2)
  let kernel : RealCofactorSpace k × RealCofactorSpace k → ℂ :=
    fun p ↦ Complex.exp (((inner ℝ p.1 (backgroundRealCofactorT R w p.2) +
      inner ℝ p.1 (backgroundRealCofactorL R (w (exposedYIndex m))) +
      inner ℝ p.2 (backgroundRealCofactorL R (w (exposedXIndex m))) : ℝ) : ℂ) *
        Complex.I)
  have hrho : MeasurePreserving rho
      ((standardRealGaussianVectorMeasure k).prod
        (standardRealGaussianVectorMeasure k))
      ((stdGaussian (RealCofactorSpace k)).prod
        (stdGaussian (RealCofactorSpace k))) := by
    exact (measurePreserving_toLp_standardRealGaussianVector k).prod
      (measurePreserving_toLp_standardRealGaussianVector k)
  have htransport :
      (∫ p, kernel (rho p)
          ∂((standardRealGaussianVectorMeasure k).prod
            (standardRealGaussianVectorMeasure k))) =
        ∫ q, kernel q
          ∂((stdGaussian (RealCofactorSpace k)).prod
            (stdGaussian (RealCofactorSpace k))) := by
    rw [← hrho.map_eq]
    symm
    exact integral_map hrho.measurable.aemeasurable
      (by fun_prop : Continuous kernel).aestronglyMeasurable
  unfold conditionalRealCofactorCharacteristic bilinearGaussianIntegral
  rw [← htransport]
  apply integral_congr_ae
  filter_upwards [] with p
  dsimp [kernel, rho, finiteRealGramCofactorPhaseCharacter]
  rw [finiteRealGramCofactorPhase_assemble_eq_bilinear]

theorem finiteRealGramCofactorCharacteristic_eq_integral_conditional
    (m k : ℕ) (w : Fin (m + 2) → ℝ) :
    finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w =
      ∫ R : Fin m → (Fin k → ℝ), conditionalRealCofactorCharacteristic R w
        ∂(Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) := by
  let split := splitTwoExposedRealColumnsRXY m k
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  let muX := standardRealGaussianVectorMeasure k
  let f : (Fin m → (Fin k → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ)) → ℂ :=
    fun q ↦ finiteRealGramCofactorPhaseCharacter w (split.symm q)
  have hf : Integrable f (muR.prod (muX.prod muX)) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with q
    unfold f finiteRealGramCofactorPhaseCharacter
    rw [Complex.norm_exp]
    simp
  unfold finiteRealGramCofactorCharacteristic
  calc
    (∫ A : Fin (m + 2) → (Fin k → ℝ),
        finiteRealGramCofactorPhaseCharacter w A
          ∂(Measure.pi fun _ : Fin (m + 2) ↦ standardRealGaussianVectorMeasure k)) =
      ∫ q, f q ∂(muR.prod (muX.prod muX)) := by
        have h := (measurePreserving_splitTwoExposedRealColumnsRXY m k).integral_comp' f
        simpa [split, muR, muX, f] using h
    _ = ∫ R, ∫ p, f (R, p) ∂(muX.prod muX) ∂muR := integral_prod f hf
    _ = ∫ R, conditionalRealCofactorCharacteristic R w ∂muR := by
      apply integral_congr_ae
      filter_upwards [] with R
      unfold conditionalRealCofactorCharacteristic f split
      apply integral_congr_ae
      filter_upwards [] with p
      rw [assembleTwoExposedRealColumns]

theorem integrable_conditionalRealCofactorCharacteristic
    (m k : ℕ) (w : Fin (m + 2) → ℝ) :
    Integrable (fun R : Fin m → (Fin k → ℝ) ↦
      conditionalRealCofactorCharacteristic R w)
      (Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) := by
  let split := splitTwoExposedRealColumnsRXY m k
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  let muX := standardRealGaussianVectorMeasure k
  let f : (Fin m → (Fin k → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ)) → ℂ :=
    fun q ↦ finiteRealGramCofactorPhaseCharacter w (split.symm q)
  have hf : Integrable f (muR.prod (muX.prod muX)) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with q
    unfold f finiteRealGramCofactorPhaseCharacter
    rw [Complex.norm_exp]
    simp
  have hsection := hf.integral_prod_left
  simpa [f, split, muR, muX, conditionalRealCofactorCharacteristic,
    assembleTwoExposedRealColumns] using hsection

/-! ## Integrated real endpoint compression -/

theorem backgroundRealCofactorT_congr_weights
    {m k : ℕ} (R : Fin m → (Fin k → ℝ))
    {w v : Fin (m + 2) → ℝ}
    (hwv : ∀ i : Fin m, w (remainingIndex m i) = v (remainingIndex m i)) :
    backgroundRealCofactorT R w = backgroundRealCofactorT R v := by
  unfold backgroundRealCofactorT realCofactorBackgroundPhaseCLM
  apply congrArg (fun M : Matrix (Fin k) (Fin k) ℝ ↦
    (Matrix.toEuclideanLin M).toContinuousLinearMap)
  funext p q
  unfold realCofactorBackgroundPhaseMatrix
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hwv i]

/-- At a left endpoint the conditional characteristic is positive real,
so the norm of the averaged characteristic is exactly the integral of its
positive real part. -/
theorem ofReal_norm_finiteRealGramCofactorCharacteristic_eq_lintegral_left
    {m k : ℕ} (w : Fin (m + 2) → ℝ)
    (hY : w (exposedYIndex m) = 0) :
    ENNReal.ofReal ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w‖ =
      ∫⁻ R : Fin m → (Fin k → ℝ),
        ENNReal.ofReal (conditionalRealCofactorCharacteristic R w).re
        ∂(Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) := by
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  have hint := integrable_conditionalRealCofactorCharacteristic m k w
  have hpos : ∀ R : Fin m → (Fin k → ℝ),
      0 < (conditionalRealCofactorCharacteristic R w).re := by
    intro R
    rw [conditionalRealCofactorCharacteristic_eq_bilinearGaussianIntegral, hY]
    exact (bilinearGaussianIntegral_endpoints_pos
      (n := Module.finrank ℝ (RealCofactorSpace k)) rfl
      (backgroundRealCofactorT R w) (backgroundRealCofactorL R)
      (w (exposedXIndex m)) (0 : ℝ)).1
  have him : ∀ R : Fin m → (Fin k → ℝ),
      (conditionalRealCofactorCharacteristic R w).im = 0 := by
    intro R
    rw [conditionalRealCofactorCharacteristic_eq_bilinearGaussianIntegral, hY]
    exact bilinearGaussianIntegral_left_endpoint_im
      (backgroundRealCofactorT R w) (backgroundRealCofactorL R)
      (w (exposedXIndex m))
  have hchar : finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w =
      ((∫ R, (conditionalRealCofactorCharacteristic R w).re ∂muR : ℝ) : ℂ) := by
    rw [finiteRealGramCofactorCharacteristic_eq_integral_conditional]
    calc
      (∫ R, conditionalRealCofactorCharacteristic R w ∂muR) =
          ∫ R, (((conditionalRealCofactorCharacteristic R w).re : ℝ) : ℂ) ∂muR := by
        apply integral_congr_ae
        filter_upwards [] with R
        apply Complex.ext
        · simp
        · simpa using him R
      _ = ((∫ R, (conditionalRealCofactorCharacteristic R w).re ∂muR : ℝ) : ℂ) :=
        integral_ofReal
  rw [hchar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun R ↦ (hpos R).le)]
  exact ofReal_integral_eq_lintegral_ofReal hint.re
    (Filter.Eventually.of_forall fun R ↦ (hpos R).le)

/-- Symmetric right-endpoint identity. -/
theorem ofReal_norm_finiteRealGramCofactorCharacteristic_eq_lintegral_right
    {m k : ℕ} (w : Fin (m + 2) → ℝ)
    (hX : w (exposedXIndex m) = 0) :
    ENNReal.ofReal ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w‖ =
      ∫⁻ R : Fin m → (Fin k → ℝ),
        ENNReal.ofReal (conditionalRealCofactorCharacteristic R w).re
        ∂(Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) := by
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  have hint := integrable_conditionalRealCofactorCharacteristic m k w
  have hpos : ∀ R : Fin m → (Fin k → ℝ),
      0 < (conditionalRealCofactorCharacteristic R w).re := by
    intro R
    rw [conditionalRealCofactorCharacteristic_eq_bilinearGaussianIntegral, hX]
    exact (bilinearGaussianIntegral_endpoints_pos
      (n := Module.finrank ℝ (RealCofactorSpace k)) rfl
      (backgroundRealCofactorT R w) (backgroundRealCofactorL R)
      (0 : ℝ) (w (exposedYIndex m))).2
  have him : ∀ R : Fin m → (Fin k → ℝ),
      (conditionalRealCofactorCharacteristic R w).im = 0 := by
    intro R
    rw [conditionalRealCofactorCharacteristic_eq_bilinearGaussianIntegral, hX]
    exact bilinearGaussianIntegral_right_endpoint_im
      (backgroundRealCofactorT R w) (backgroundRealCofactorL R)
      (w (exposedYIndex m))
  have hchar : finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w =
      ((∫ R, (conditionalRealCofactorCharacteristic R w).re ∂muR : ℝ) : ℂ) := by
    rw [finiteRealGramCofactorCharacteristic_eq_integral_conditional]
    calc
      (∫ R, conditionalRealCofactorCharacteristic R w ∂muR) =
          ∫ R, (((conditionalRealCofactorCharacteristic R w).re : ℝ) : ℂ) ∂muR := by
        apply integral_congr_ae
        filter_upwards [] with R
        apply Complex.ext
        · simp
        · simpa using him R
      _ = ((∫ R, (conditionalRealCofactorCharacteristic R w).re ∂muR : ℝ) : ℂ) :=
        integral_ofReal
  rw [hchar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun R ↦ (hpos R).le)]
  exact ofReal_integral_eq_lintegral_ofReal hint.re
    (Filter.Eventually.of_forall fun R ↦ (hpos R).le)

/-- Literal integrated two-coordinate compression for real Gram cofactors.
The two endpoint weights keep all background coordinates fixed and move the
displayed Euclidean energy to one of the two exposed coordinates. -/
theorem finiteRealGramCofactorCharacteristic_two_exposed_max
    {m k : ℕ}
    (w wLeft wRight : Fin (m + 2) → ℝ) (theta : ℝ)
    (htheta : 0 < theta) (htheta_one : theta < 1)
    (hbgLeft : ∀ i : Fin m,
      wLeft (remainingIndex m i) = w (remainingIndex m i))
    (hbgRight : ∀ i : Fin m,
      wRight (remainingIndex m i) = w (remainingIndex m i))
    (hLeftY : wLeft (exposedYIndex m) = 0)
    (hRightX : wRight (exposedXIndex m) = 0)
    (hscaleX : w (exposedXIndex m) =
      Real.sqrt theta • wLeft (exposedXIndex m))
    (hscaleY : w (exposedYIndex m) =
      Real.sqrt (1 - theta) • wRight (exposedYIndex m)) :
    ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
      max ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖
        ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wRight‖ := by
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  let a := wLeft (exposedXIndex m)
  let b := wRight (exposedYIndex m)
  let fLeft : (Fin m → (Fin k → ℝ)) → ENNReal := fun R ↦
    ENNReal.ofReal
      ((bilinearGaussianIntegral (backgroundRealCofactorT R w)
        (backgroundRealCofactorL R) a 0).re)
  let fRight : (Fin m → (Fin k → ℝ)) → ENNReal := fun R ↦
    ENNReal.ofReal
      ((bilinearGaussianIntegral (backgroundRealCofactorT R w)
        (backgroundRealCofactorL R) 0 b).re)
  have hleftPoint : ∀ R : Fin m → (Fin k → ℝ),
      conditionalRealCofactorCharacteristic R wLeft =
        bilinearGaussianIntegral (backgroundRealCofactorT R w)
          (backgroundRealCofactorL R) a 0 := by
    intro R
    rw [conditionalRealCofactorCharacteristic_eq_bilinearGaussianIntegral,
      backgroundRealCofactorT_congr_weights R hbgLeft, hLeftY]
  have hrightPoint : ∀ R : Fin m → (Fin k → ℝ),
      conditionalRealCofactorCharacteristic R wRight =
        bilinearGaussianIntegral (backgroundRealCofactorT R w)
          (backgroundRealCofactorL R) 0 b := by
    intro R
    rw [conditionalRealCofactorCharacteristic_eq_bilinearGaussianIntegral,
      backgroundRealCofactorT_congr_weights R hbgRight, hRightX]
  have hleftMeas : AEMeasurable fLeft muR := by
    have h :=
      (integrable_conditionalRealCofactorCharacteristic m k wLeft).1.re.aemeasurable
    have hof := ENNReal.measurable_ofReal.comp_aemeasurable h
    change AEMeasurable
      (fun R => ENNReal.ofReal (conditionalRealCofactorCharacteristic R wLeft).re)
      (Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) at hof
    dsimp only [fLeft]
    simpa only [hleftPoint] using hof
  have hrightMeas : AEMeasurable fRight muR := by
    have h :=
      (integrable_conditionalRealCofactorCharacteristic m k wRight).1.re.aemeasurable
    have hof := ENNReal.measurable_ofReal.comp_aemeasurable h
    change AEMeasurable
      (fun R => ENNReal.ofReal (conditionalRealCofactorCharacteristic R wRight).re)
      (Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) at hof
    dsimp only [fRight]
    simpa only [hrightPoint] using hof
  have hholder := lintegral_norm_bilinearGaussianIntegral_sqrt_le
    (n := Module.finrank ℝ (RealCofactorSpace k)) rfl muR
    (fun R ↦ backgroundRealCofactorT R w)
    (fun R ↦ backgroundRealCofactorL R) a b
    htheta.le htheta_one.le hleftMeas hrightMeas
  have hnorm : ENNReal.ofReal
      ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
      ∫⁻ R, ENNReal.ofReal ‖conditionalRealCofactorCharacteristic R w‖ ∂muR := by
    rw [finiteRealGramCofactorCharacteristic_eq_integral_conditional]
    have hreal := norm_integral_le_integral_norm
      (fun R ↦ conditionalRealCofactorCharacteristic R w) (μ := muR)
    have hof := ENNReal.ofReal_le_ofReal hreal
    rw [ofReal_integral_norm_eq_lintegral_enorm
      (integrable_conditionalRealCofactorCharacteristic m k w)] at hof
    simpa [muR, ofReal_norm] using hof
  have hscaled :
      (∫⁻ R, ENNReal.ofReal ‖conditionalRealCofactorCharacteristic R w‖ ∂muR) ≤
        (∫⁻ R, fLeft R ∂muR) ^ theta *
          (∫⁻ R, fRight R ∂muR) ^ (1 - theta) := by
    calc
      (∫⁻ R, ENNReal.ofReal ‖conditionalRealCofactorCharacteristic R w‖ ∂muR) =
          ∫⁻ R, ENNReal.ofReal
            ‖bilinearGaussianIntegral (backgroundRealCofactorT R w)
              (backgroundRealCofactorL R)
              (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)‖ ∂muR := by
        apply lintegral_congr
        intro R
        rw [conditionalRealCofactorCharacteristic_eq_bilinearGaussianIntegral,
          hscaleX, hscaleY]
      _ ≤ (∫⁻ R, fLeft R ∂muR) ^ theta *
          (∫⁻ R, fRight R ∂muR) ^ (1 - theta) := by
        simpa [fLeft, fRight] using hholder
  let Lval : ENNReal := ∫⁻ R, fLeft R ∂muR
  let Rval : ENNReal := ∫⁻ R, fRight R ∂muR
  have hgeom : Lval ^ theta * Rval ^ (1 - theta) ≤ max Lval Rval := by
    let M := max Lval Rval
    have hLM : Lval ≤ M := le_max_left _ _
    have hRM : Rval ≤ M := le_max_right _ _
    have hpowers : Lval ^ theta * Rval ^ (1 - theta) ≤
        M ^ theta * M ^ (1 - theta) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hLM htheta.le)
        (ENNReal.rpow_le_rpow hRM (sub_nonneg.mpr htheta_one.le))
    by_cases hM0 : M = 0
    · have hL0 : Lval = 0 := le_antisymm (hLM.trans_eq hM0) bot_le
      have hR0 : Rval = 0 := le_antisymm (hRM.trans_eq hM0) bot_le
      simp [hL0, hR0, htheta.ne', sub_pos.mpr htheta_one]
    · by_cases hMtop : M = ∞
      · change max Lval Rval = ∞ at hMtop
        rw [hMtop]
        exact le_top
      · calc
          Lval ^ theta * Rval ^ (1 - theta) ≤
              M ^ theta * M ^ (1 - theta) := hpowers
          _ = M ^ (theta + (1 - theta)) :=
            (ENNReal.rpow_add _ _ hM0 hMtop).symm
          _ = M := by ring_nf; simp
  have hLval : Lval = ENNReal.ofReal
      ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖ := by
    dsimp [Lval, fLeft]
    calc
      (∫⁻ R, ENNReal.ofReal
          (bilinearGaussianIntegral (backgroundRealCofactorT R w)
            (backgroundRealCofactorL R) a 0).re ∂muR) =
          ∫⁻ R, ENNReal.ofReal
            (conditionalRealCofactorCharacteristic R wLeft).re ∂muR := by
        apply lintegral_congr
        intro R
        rw [hleftPoint]
      _ = ENNReal.ofReal
          ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖ := by
        simpa [muR] using
          (ofReal_norm_finiteRealGramCofactorCharacteristic_eq_lintegral_left
            (m := m) (k := k) wLeft hLeftY).symm
  have hRval : Rval = ENNReal.ofReal
      ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wRight‖ := by
    dsimp [Rval, fRight]
    calc
      (∫⁻ R, ENNReal.ofReal
          (bilinearGaussianIntegral (backgroundRealCofactorT R w)
            (backgroundRealCofactorL R) 0 b).re ∂muR) =
          ∫⁻ R, ENNReal.ofReal
            (conditionalRealCofactorCharacteristic R wRight).re ∂muR := by
        apply lintegral_congr
        intro R
        rw [hrightPoint]
      _ = ENNReal.ofReal
          ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wRight‖ := by
        simpa [muR] using
          (ofReal_norm_finiteRealGramCofactorCharacteristic_eq_lintegral_right
            (m := m) (k := k) wRight hRightX).symm
  have hENN : ENNReal.ofReal
      ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
      ENNReal.ofReal (max
        ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖
        ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wRight‖) := by
    rw [ENNReal.ofReal_max]
    calc
      ENNReal.ofReal
          ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
          ∫⁻ R, ENNReal.ofReal ‖conditionalRealCofactorCharacteristic R w‖ ∂muR :=
        hnorm
      _ ≤ Lval ^ theta * Rval ^ (1 - theta) := by
        simpa [Lval, Rval] using hscaled
      _ ≤ max Lval Rval := hgeom
      _ = max (ENNReal.ofReal
          ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖)
          (ENNReal.ofReal
            ‖finiteRealGramCofactorCharacteristic (Fin (m + 2)) k wRight‖) := by
        rw [hLval, hRval]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN

end

end LogdetLean.GramHafnian
