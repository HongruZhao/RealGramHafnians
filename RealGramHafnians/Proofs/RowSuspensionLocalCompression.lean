import RealGramHafnians.Proofs.RowSuspensionAlgebra
/-!
# Local row-suspension compression

This file isolates the new algebraic step in the sharp real proof.  Two
background Gaussian columns are exposed after their first coordinates have
been frozen.  The resulting phase is a bilinear Gaussian phase in the two
tails, plus a scalar `x*y` phase.  The scalar phase has modulus one and
vanishes at both coordinate-compression endpoints.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 4000000

def rowSuspensionBackground {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) :
    Fin m → (Fin (k + 1) → ℝ) :=
  fun i ↦ prependRealCoordinate (z (remainingIndex m i)) (R i)

def rowSuspensionFullBackgroundFamily {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) :
    RealTwoExposedColumnFamily m (k + 1) :=
  assembleTwoExposedRealColumns (rowSuspensionBackground z R) 0 0

def rowSuspensionFullTMatrix {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  realCofactorBackgroundPhaseMatrix (rowSuspensionFullBackgroundFamily z R) z

def rowSuspensionFullQ {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) :
    Fin (k + 1) → ℝ :=
  realCofactorQ (rowSuspensionFullBackgroundFamily z R)

def rowSuspensionTailTMatrix {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun p q ↦ rowSuspensionFullTMatrix z R p.succ q.succ

def rowSuspensionTailT {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) :
    RealCofactorSpace k →L[ℝ] RealCofactorSpace k :=
  (Matrix.toEuclideanLin (rowSuspensionTailTMatrix z R)).toContinuousLinearMap

def rowSuspensionLeftVector {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) :
    RealCofactorSpace k :=
  WithLp.toLp 2 (fun p ↦
    rowSuspensionFullTMatrix z R p.succ 0 + rowSuspensionFullQ z R p.succ)

def rowSuspensionRightVector {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) :
    RealCofactorSpace k :=
  WithLp.toLp 2 (fun q ↦
    rowSuspensionFullTMatrix z R 0 q.succ + rowSuspensionFullQ z R q.succ)

def rowSuspensionPureCoefficient {m k : ℕ}
    (z : Fin (m + 2) → ℝ) (R : Fin m → (Fin k → ℝ)) : ℝ :=
  rowSuspensionFullTMatrix z R 0 0 + 2 * rowSuspensionFullQ z R 0

theorem rowSuspensionColumns_assembleTwoExposed
    {m k : ℕ} (z : Fin (m + 2) → ℝ)
    (R : Fin m → (Fin k → ℝ)) (X Y : Fin k → ℝ) :
    rowSuspensionColumns z (assembleTwoExposedRealColumns R X Y) =
      assembleTwoExposedRealColumns (rowSuspensionBackground z R)
        (prependRealCoordinate (z (exposedXIndex m)) X)
        (prependRealCoordinate (z (exposedYIndex m)) Y) := by
  apply (splitTwoExposedRealColumnsRXY m (k + 1)).injective
  rw [splitTwoExposedRealColumnsRXY_apply,
    splitTwoExposedRealColumnsRXY_apply]
  apply Prod.ext
  · funext i
    change prependRealCoordinate (z (remainingIndex m i))
        (assembleTwoExposedRealColumns R X Y (remainingIndex m i)) =
      assembleTwoExposedRealColumns (rowSuspensionBackground z R)
        (prependRealCoordinate (z (exposedXIndex m)) X)
        (prependRealCoordinate (z (exposedYIndex m)) Y) (remainingIndex m i)
    rw [congrFun (assembleTwoExposedRealColumns_coordinates R X Y).1 i,
      congrFun (assembleTwoExposedRealColumns_coordinates
        (rowSuspensionBackground z R)
        (prependRealCoordinate (z (exposedXIndex m)) X)
        (prependRealCoordinate (z (exposedYIndex m)) Y)).1 i]
    rfl
  · apply Prod.ext
    · change prependRealCoordinate (z (exposedXIndex m))
          (assembleTwoExposedRealColumns R X Y (exposedXIndex m)) =
        assembleTwoExposedRealColumns (rowSuspensionBackground z R)
          (prependRealCoordinate (z (exposedXIndex m)) X)
          (prependRealCoordinate (z (exposedYIndex m)) Y) (exposedXIndex m)
      rw [(assembleTwoExposedRealColumns_coordinates R X Y).2.1,
        (assembleTwoExposedRealColumns_coordinates
          (rowSuspensionBackground z R)
          (prependRealCoordinate (z (exposedXIndex m)) X)
          (prependRealCoordinate (z (exposedYIndex m)) Y)).2.1]
    · change prependRealCoordinate (z (exposedYIndex m))
          (assembleTwoExposedRealColumns R X Y (exposedYIndex m)) =
        assembleTwoExposedRealColumns (rowSuspensionBackground z R)
          (prependRealCoordinate (z (exposedXIndex m)) X)
          (prependRealCoordinate (z (exposedYIndex m)) Y) (exposedYIndex m)
      rw [(assembleTwoExposedRealColumns_coordinates R X Y).2.2,
        (assembleTwoExposedRealColumns_coordinates
          (rowSuspensionBackground z R)
          (prependRealCoordinate (z (exposedXIndex m)) X)
          (prependRealCoordinate (z (exposedYIndex m)) Y)).2.2]

theorem realTransposeDot_prependRealCoordinate
    {k : ℕ} (x : ℝ) (X : Fin k → ℝ) (q : Fin (k + 1) → ℝ) :
    realTransposeDot (prependRealCoordinate x X) q =
      x * q 0 + ∑ p : Fin k, X p * q p.succ := by
  unfold realTransposeDot
  rw [Fin.sum_univ_succ]
  rfl

theorem realTransposeBilinear_prependRealCoordinate
    {k : ℕ} (x y : ℝ) (X Y : Fin k → ℝ)
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    realTransposeBilinear (prependRealCoordinate x X) M
        (prependRealCoordinate y Y) =
      (∑ p : Fin k, ∑ q : Fin k, X p * M p.succ q.succ * Y q) +
      y * (∑ p : Fin k, X p * M p.succ 0) +
      x * (∑ q : Fin k, M 0 q.succ * Y q) +
      x * y * M 0 0 := by
  unfold realTransposeBilinear
  rw [Fin.sum_univ_succ]
  simp only [prependRealCoordinate_zero, prependRealCoordinate_succ]
  rw [Fin.sum_univ_succ]
  simp only [prependRealCoordinate_zero, prependRealCoordinate_succ]
  simp_rw [Fin.sum_univ_succ]
  simp only [prependRealCoordinate_zero, prependRealCoordinate_succ]
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  ring

theorem rowSuspensionPhase_assembleTwoExposed_eq
    {m k : ℕ} (z : Fin (m + 2) → ℝ)
    (R : Fin m → (Fin k → ℝ)) (X Y : Fin k → ℝ) :
    rowSuspensionPhase z (assembleTwoExposedRealColumns R X Y) =
      inner ℝ (WithLp.toLp 2 X)
          (rowSuspensionTailT z R (WithLp.toLp 2 Y)) +
      z (exposedYIndex m) * inner ℝ (WithLp.toLp 2 X)
          (rowSuspensionLeftVector z R) +
      z (exposedXIndex m) * inner ℝ (WithLp.toLp 2 Y)
          (rowSuspensionRightVector z R) +
      z (exposedXIndex m) * z (exposedYIndex m) *
          rowSuspensionPureCoefficient z R := by
  rw [rowSuspensionPhase, rowSuspensionColumns_assembleTwoExposed]
  rw [finiteRealGramCofactorPhase_assemble_eq_bilinear]
  let A := rowSuspensionFullBackgroundFamily z R
  let M := rowSuspensionFullTMatrix z R
  let q := rowSuspensionFullQ z R
  have hT : backgroundRealCofactorT (rowSuspensionBackground z R) z =
      (Matrix.toEuclideanLin M).toContinuousLinearMap := by
    rfl
  have hL : backgroundRealCofactorL (rowSuspensionBackground z R) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (WithLp.toLp 2 q) := by
    rfl
  rw [hT, hL]
  have hbil :
      inner ℝ (WithLp.toLp 2
          (prependRealCoordinate (z (exposedXIndex m)) X))
          ((Matrix.toEuclideanLin M).toContinuousLinearMap
            (WithLp.toLp 2
              (prependRealCoordinate (z (exposedYIndex m)) Y))) =
        realTransposeBilinear
          (prependRealCoordinate (z (exposedXIndex m)) X) M
          (prependRealCoordinate (z (exposedYIndex m)) Y) := by
    change inner ℝ (WithLp.toLp 2
        (prependRealCoordinate (z (exposedXIndex m)) X))
        (Matrix.toEuclideanLin M (WithLp.toLp 2
          (prependRealCoordinate (z (exposedYIndex m)) Y))) = _
    exact inner_toEuclideanLin_eq_realTransposeBilinearPhase _ _ _
  rw [hbil]
  rw [realTransposeBilinear_prependRealCoordinate]
  have hlinX :
      inner ℝ (WithLp.toLp 2
          (prependRealCoordinate (z (exposedXIndex m)) X))
          (((ContinuousLinearMap.id ℝ ℝ).smulRight
            (WithLp.toLp 2 q)) (z (exposedYIndex m))) =
        z (exposedYIndex m) *
          (z (exposedXIndex m) * q 0 + ∑ p : Fin k, X p * q p.succ) := by
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
      WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_succ]
    simp only [prependRealCoordinate_zero, prependRealCoordinate_succ]
    rw [mul_add, Finset.mul_sum]
    apply congrArg₂ (fun a b : ℝ ↦ a + b)
    · ring
    · apply Finset.sum_congr rfl
      intro p _hp
      ring
  have hlinY :
      inner ℝ (WithLp.toLp 2
          (prependRealCoordinate (z (exposedYIndex m)) Y))
          (((ContinuousLinearMap.id ℝ ℝ).smulRight
            (WithLp.toLp 2 q)) (z (exposedXIndex m))) =
        z (exposedXIndex m) *
          (z (exposedYIndex m) * q 0 + ∑ p : Fin k, Y p * q p.succ) := by
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
      WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_succ]
    simp only [prependRealCoordinate_zero, prependRealCoordinate_succ]
    rw [mul_add, Finset.mul_sum]
    apply congrArg₂ (fun a b : ℝ ↦ a + b)
    · ring
    · apply Finset.sum_congr rfl
      intro p _hp
      ring
  rw [hlinX, hlinY]
  have htail :
      inner ℝ (WithLp.toLp 2 X)
          (rowSuspensionTailT z R (WithLp.toLp 2 Y)) =
        ∑ p : Fin k, ∑ q : Fin k,
          X p * rowSuspensionFullTMatrix z R p.succ q.succ * Y q := by
    unfold rowSuspensionTailT rowSuspensionTailTMatrix
    simpa [realTransposeBilinearPhase] using
      (inner_toEuclideanLin_eq_realTransposeBilinearPhase
        X (fun (p : Fin k) (q : Fin k) ↦
          rowSuspensionFullTMatrix z R p.succ q.succ) Y)
  have hleft :
      inner ℝ (WithLp.toLp 2 X) (rowSuspensionLeftVector z R) =
        (∑ p : Fin k, X p * rowSuspensionFullTMatrix z R p.succ 0) +
          ∑ p : Fin k, X p * rowSuspensionFullQ z R p.succ := by
    unfold rowSuspensionLeftVector
    simp only [PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply,
      starRingEnd_apply, star_trivial]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro p _hp <;>
    ring
  have hright :
      inner ℝ (WithLp.toLp 2 Y) (rowSuspensionRightVector z R) =
        (∑ p : Fin k, rowSuspensionFullTMatrix z R 0 p.succ * Y p) +
          ∑ p : Fin k, Y p * rowSuspensionFullQ z R p.succ := by
    unfold rowSuspensionRightVector
    simp only [PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply,
      starRingEnd_apply, star_trivial]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro p _hp <;>
    ring
  rw [htail, hleft, hright]
  unfold rowSuspensionPureCoefficient
  dsimp [M, q]
  ring

def conditionalRowSuspensionCharacteristic {m k : ℕ}
    (t : ℝ) (R : Fin m → (Fin k → ℝ)) (z : Fin (m + 2) → ℝ) : ℂ :=
  ∫ p : (Fin k → ℝ) × (Fin k → ℝ),
    rowSuspensionPhaseCharacter t z
      (assembleTwoExposedRealColumns R p.1 p.2)
    ∂((standardRealGaussianVectorMeasure k).prod
      (standardRealGaussianVectorMeasure k))

def rowSuspensionPurePhase {m k : ℕ}
    (t : ℝ) (R : Fin m → (Fin k → ℝ)) (z : Fin (m + 2) → ℝ) : ℂ :=
  Complex.exp (((t * z (exposedXIndex m) * z (exposedYIndex m) *
    rowSuspensionPureCoefficient z R : ℝ) : ℂ) * Complex.I)

def rowSuspensionBilinearIntegral {m k : ℕ}
    (t : ℝ) (R : Fin m → (Fin k → ℝ)) (z : Fin (m + 2) → ℝ) : ℂ :=
  bilinearGaussianIntegral (t • rowSuspensionTailT z R)
    (ContinuousLinearMap.id ℝ (RealCofactorSpace k))
    ((t * z (exposedXIndex m)) • rowSuspensionRightVector z R)
    ((t * z (exposedYIndex m)) • rowSuspensionLeftVector z R)

theorem norm_rowSuspensionPurePhase {m k : ℕ}
    (t : ℝ) (R : Fin m → (Fin k → ℝ)) (z : Fin (m + 2) → ℝ) :
    ‖rowSuspensionPurePhase t R z‖ = 1 := by
  unfold rowSuspensionPurePhase
  rw [Complex.norm_exp]
  simp

theorem conditionalRowSuspensionCharacteristic_eq
    {m k : ℕ} (t : ℝ) (R : Fin m → (Fin k → ℝ))
    (z : Fin (m + 2) → ℝ) :
    conditionalRowSuspensionCharacteristic t R z =
      rowSuspensionPurePhase t R z * rowSuspensionBilinearIntegral t R z := by
  let E := RealCofactorSpace k
  let rho : ((Fin k → ℝ) × (Fin k → ℝ)) → E × E :=
    fun p ↦ (WithLp.toLp 2 p.1, WithLp.toLp 2 p.2)
  let mu := (standardRealGaussianVectorMeasure k).prod
      (standardRealGaussianVectorMeasure k)
  let gamma := (stdGaussian E).prod (stdGaussian E)
  let tailKernel : E × E → ℂ := fun p ↦
    Complex.exp (((inner ℝ p.1 ((t • rowSuspensionTailT z R) p.2) +
      inner ℝ p.1 ((t * z (exposedYIndex m)) • rowSuspensionLeftVector z R) +
      inner ℝ p.2 ((t * z (exposedXIndex m)) • rowSuspensionRightVector z R) : ℝ) : ℂ) *
        Complex.I)
  have hrho : MeasurePreserving rho mu gamma := by
    exact (measurePreserving_toLp_standardRealGaussianVector k).prod
      (measurePreserving_toLp_standardRealGaussianVector k)
  have htailContinuous : Continuous tailKernel := by
    dsimp [tailKernel]
    fun_prop
  have htransport :
      (∫ p, tailKernel (rho p) ∂mu) = ∫ q, tailKernel q ∂gamma := by
    rw [← hrho.map_eq]
    symm
    exact integral_map hrho.measurable.aemeasurable
      htailContinuous.aestronglyMeasurable
  unfold conditionalRowSuspensionCharacteristic
  calc
    (∫ p : (Fin k → ℝ) × (Fin k → ℝ),
        rowSuspensionPhaseCharacter t z
          (assembleTwoExposedRealColumns R p.1 p.2) ∂mu) =
      rowSuspensionPurePhase t R z * ∫ p, tailKernel (rho p) ∂mu := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with p
        unfold rowSuspensionPhaseCharacter
        rw [rowSuspensionPhase_assembleTwoExposed_eq]
        dsimp [tailKernel, rho, rowSuspensionPurePhase]
        simp only [ContinuousLinearMap.id_apply, inner_smul_right,
          ContinuousLinearMap.smul_apply]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
    _ = rowSuspensionPurePhase t R z * ∫ q, tailKernel q ∂gamma := by
      rw [htransport]
    _ = rowSuspensionPurePhase t R z * rowSuspensionBilinearIntegral t R z := by
      congr 1

theorem norm_conditionalRowSuspensionCharacteristic_eq
    {m k : ℕ} (t : ℝ) (R : Fin m → (Fin k → ℝ))
    (z : Fin (m + 2) → ℝ) :
    ‖conditionalRowSuspensionCharacteristic t R z‖ =
      ‖rowSuspensionBilinearIntegral t R z‖ := by
  rw [conditionalRowSuspensionCharacteristic_eq, norm_mul,
    norm_rowSuspensionPurePhase, one_mul]

/-! ## Dependence only on the background coordinates -/

theorem rowSuspensionBackground_congr
    {m k : ℕ} {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (R : Fin m → (Fin k → ℝ)) :
    rowSuspensionBackground v R = rowSuspensionBackground z R := by
  funext i
  unfold rowSuspensionBackground
  rw [hbg i]

theorem rowSuspensionFullBackgroundFamily_congr
    {m k : ℕ} {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (R : Fin m → (Fin k → ℝ)) :
    rowSuspensionFullBackgroundFamily v R =
      rowSuspensionFullBackgroundFamily z R := by
  unfold rowSuspensionFullBackgroundFamily
  rw [rowSuspensionBackground_congr hbg]

theorem rowSuspensionFullTMatrix_congr_background
    {m k : ℕ} {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (R : Fin m → (Fin k → ℝ)) :
    rowSuspensionFullTMatrix v R = rowSuspensionFullTMatrix z R := by
  unfold rowSuspensionFullTMatrix realCofactorBackgroundPhaseMatrix
  rw [rowSuspensionFullBackgroundFamily_congr hbg]
  funext p q
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hbg i]

theorem rowSuspensionFullQ_congr_background
    {m k : ℕ} {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (R : Fin m → (Fin k → ℝ)) :
    rowSuspensionFullQ v R = rowSuspensionFullQ z R := by
  unfold rowSuspensionFullQ
  rw [rowSuspensionFullBackgroundFamily_congr hbg]

theorem rowSuspensionTailT_congr_background
    {m k : ℕ} {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (R : Fin m → (Fin k → ℝ)) :
    rowSuspensionTailT v R = rowSuspensionTailT z R := by
  unfold rowSuspensionTailT rowSuspensionTailTMatrix
  rw [rowSuspensionFullTMatrix_congr_background hbg]

theorem rowSuspensionLeftVector_congr_background
    {m k : ℕ} {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (R : Fin m → (Fin k → ℝ)) :
    rowSuspensionLeftVector v R = rowSuspensionLeftVector z R := by
  unfold rowSuspensionLeftVector
  rw [rowSuspensionFullTMatrix_congr_background hbg,
    rowSuspensionFullQ_congr_background hbg]

theorem rowSuspensionRightVector_congr_background
    {m k : ℕ} {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (R : Fin m → (Fin k → ℝ)) :
    rowSuspensionRightVector v R = rowSuspensionRightVector z R := by
  unfold rowSuspensionRightVector
  rw [rowSuspensionFullTMatrix_congr_background hbg,
    rowSuspensionFullQ_congr_background hbg]

theorem rowSuspensionBilinearIntegral_left_endpoint
    {m k : ℕ} (t : ℝ) (R : Fin m → (Fin k → ℝ))
    {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (hY : v (exposedYIndex m) = 0) :
    rowSuspensionBilinearIntegral t R v =
      bilinearGaussianIntegral (t • rowSuspensionTailT z R)
        (ContinuousLinearMap.id ℝ (RealCofactorSpace k))
        ((t * v (exposedXIndex m)) • rowSuspensionRightVector z R) 0 := by
  unfold rowSuspensionBilinearIntegral
  rw [rowSuspensionTailT_congr_background hbg,
    rowSuspensionLeftVector_congr_background hbg,
    rowSuspensionRightVector_congr_background hbg, hY]
  simp

theorem rowSuspensionBilinearIntegral_right_endpoint
    {m k : ℕ} (t : ℝ) (R : Fin m → (Fin k → ℝ))
    {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (hX : v (exposedXIndex m) = 0) :
    rowSuspensionBilinearIntegral t R v =
      bilinearGaussianIntegral (t • rowSuspensionTailT z R)
        (ContinuousLinearMap.id ℝ (RealCofactorSpace k)) 0
        ((t * v (exposedYIndex m)) • rowSuspensionLeftVector z R) := by
  unfold rowSuspensionBilinearIntegral
  rw [rowSuspensionTailT_congr_background hbg,
    rowSuspensionLeftVector_congr_background hbg,
    rowSuspensionRightVector_congr_background hbg, hX]
  simp

theorem conditionalRowSuspensionCharacteristic_left_endpoint
    {m k : ℕ} (t : ℝ) (R : Fin m → (Fin k → ℝ))
    {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (hY : v (exposedYIndex m) = 0) :
    conditionalRowSuspensionCharacteristic t R v =
      bilinearGaussianIntegral (t • rowSuspensionTailT z R)
        (ContinuousLinearMap.id ℝ (RealCofactorSpace k))
        ((t * v (exposedXIndex m)) • rowSuspensionRightVector z R) 0 := by
  rw [conditionalRowSuspensionCharacteristic_eq,
    rowSuspensionBilinearIntegral_left_endpoint t R hbg hY]
  unfold rowSuspensionPurePhase
  rw [hY]
  simp

theorem conditionalRowSuspensionCharacteristic_right_endpoint
    {m k : ℕ} (t : ℝ) (R : Fin m → (Fin k → ℝ))
    {z v : Fin (m + 2) → ℝ}
    (hbg : ∀ i : Fin m, v (remainingIndex m i) = z (remainingIndex m i))
    (hX : v (exposedXIndex m) = 0) :
    conditionalRowSuspensionCharacteristic t R v =
      bilinearGaussianIntegral (t • rowSuspensionTailT z R)
        (ContinuousLinearMap.id ℝ (RealCofactorSpace k)) 0
        ((t * v (exposedYIndex m)) • rowSuspensionLeftVector z R) := by
  rw [conditionalRowSuspensionCharacteristic_eq,
    rowSuspensionBilinearIntegral_right_endpoint t R hbg hX]
  unfold rowSuspensionPurePhase
  rw [hX]
  simp

/-- Exact conditional geometric interpolation for the two exposed top-row
coordinates.  This is the new lossless local compression statement. -/
theorem conditionalRowSuspensionCharacteristic_endpoints_pos_and_geometric
    {m k : ℕ} (t : ℝ) (R : Fin m → (Fin k → ℝ))
    (z zLeft zRight : Fin (m + 2) → ℝ) (theta : ℝ)
    (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (hbgLeft : ∀ i : Fin m,
      zLeft (remainingIndex m i) = z (remainingIndex m i))
    (hbgRight : ∀ i : Fin m,
      zRight (remainingIndex m i) = z (remainingIndex m i))
    (hLeftY : zLeft (exposedYIndex m) = 0)
    (hRightX : zRight (exposedXIndex m) = 0)
    (hscaleX : z (exposedXIndex m) =
      Real.sqrt theta • zLeft (exposedXIndex m))
    (hscaleY : z (exposedYIndex m) =
      Real.sqrt (1 - theta) • zRight (exposedYIndex m)) :
    (0 < (conditionalRowSuspensionCharacteristic t R zLeft).re ∧
      0 < (conditionalRowSuspensionCharacteristic t R zRight).re) ∧
    ‖conditionalRowSuspensionCharacteristic t R z‖ =
      (conditionalRowSuspensionCharacteristic t R zLeft).re ^ theta *
        (conditionalRowSuspensionCharacteristic t R zRight).re ^
          (1 - theta) := by
  let T := t • rowSuspensionTailT z R
  let L := ContinuousLinearMap.id ℝ (RealCofactorSpace k)
  let a := (t * zLeft (exposedXIndex m)) • rowSuspensionRightVector z R
  let b := (t * zRight (exposedYIndex m)) • rowSuspensionLeftVector z R
  have hA :
      (t * z (exposedXIndex m)) • rowSuspensionRightVector z R =
        Real.sqrt theta • a := by
    dsimp [a]
    rw [smul_smul]
    congr 1
    simp only [smul_eq_mul] at hscaleX ⊢
    rw [hscaleX]
    ring
  have hB :
      (t * z (exposedYIndex m)) • rowSuspensionLeftVector z R =
        Real.sqrt (1 - theta) • b := by
    dsimp [b]
    rw [smul_smul]
    congr 1
    simp only [smul_eq_mul] at hscaleY ⊢
    rw [hscaleY]
    ring
  have hgeom := bilinearGaussianIntegral_endpoints_pos_and_geometric
    (n := Module.finrank ℝ (RealCofactorSpace k)) rfl
      T L a b htheta htheta_one
  have hleft : conditionalRowSuspensionCharacteristic t R zLeft =
      bilinearGaussianIntegral T L a 0 := by
    simpa [T, L, a] using
      conditionalRowSuspensionCharacteristic_left_endpoint
        t R hbgLeft hLeftY
  have hright : conditionalRowSuspensionCharacteristic t R zRight =
      bilinearGaussianIntegral T L 0 b := by
    simpa [T, L, b] using
      conditionalRowSuspensionCharacteristic_right_endpoint
        t R hbgRight hRightX
  constructor
  · simpa [hleft, hright] using hgeom.1
  · rw [norm_conditionalRowSuspensionCharacteristic_eq]
    unfold rowSuspensionBilinearIntegral
    rw [hA, hB]
    simpa [T, L, hleft, hright] using hgeom.2

/-! ## Disintegration over the two exposed tail columns -/

theorem rowSuspensionCharacteristic_eq_integral_conditional
    (m k : ℕ) (t : ℝ) (z : Fin (m + 2) → ℝ) :
    rowSuspensionCharacteristic (m + 2) k t z =
      ∫ R : Fin m → (Fin k → ℝ),
        conditionalRowSuspensionCharacteristic t R z
        ∂(Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) := by
  let split := splitTwoExposedRealColumnsRXY m k
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  let muX := standardRealGaussianVectorMeasure k
  let f : (Fin m → (Fin k → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ)) → ℂ :=
    fun q ↦ rowSuspensionPhaseCharacter t z (split.symm q)
  have hf : Integrable f (muR.prod (muX.prod muX)) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with q
    exact norm_rowSuspensionPhaseCharacter t z (split.symm q) |>.le
  unfold rowSuspensionCharacteristic
  calc
    (∫ B : Fin (m + 2) → (Fin k → ℝ),
        rowSuspensionPhaseCharacter t z B
          ∂(Measure.pi fun _ : Fin (m + 2) ↦ standardRealGaussianVectorMeasure k)) =
      ∫ q, f q ∂(muR.prod (muX.prod muX)) := by
        have h := (measurePreserving_splitTwoExposedRealColumnsRXY m k).integral_comp' f
        simpa [split, muR, muX, f] using h
    _ = ∫ R, ∫ p, f (R, p) ∂(muX.prod muX) ∂muR := integral_prod f hf
    _ = ∫ R, conditionalRowSuspensionCharacteristic t R z ∂muR := by
      apply integral_congr_ae
      filter_upwards [] with R
      unfold conditionalRowSuspensionCharacteristic f split
      apply integral_congr_ae
      filter_upwards [] with p
      rw [assembleTwoExposedRealColumns]

theorem integrable_conditionalRowSuspensionCharacteristic
    (m k : ℕ) (t : ℝ) (z : Fin (m + 2) → ℝ) :
    Integrable (fun R : Fin m → (Fin k → ℝ) ↦
      conditionalRowSuspensionCharacteristic t R z)
      (Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) := by
  let split := splitTwoExposedRealColumnsRXY m k
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  let muX := standardRealGaussianVectorMeasure k
  let f : (Fin m → (Fin k → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ)) → ℂ :=
    fun q ↦ rowSuspensionPhaseCharacter t z (split.symm q)
  have hf : Integrable f (muR.prod (muX.prod muX)) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with q
    exact norm_rowSuspensionPhaseCharacter t z (split.symm q) |>.le
  have hsection := hf.integral_prod_left
  simpa [f, split, muR, muX, conditionalRowSuspensionCharacteristic,
    assembleTwoExposedRealColumns] using hsection

theorem ofReal_norm_rowSuspensionCharacteristic_eq_lintegral_left
    {m k : ℕ} (t : ℝ) (z : Fin (m + 2) → ℝ)
    (hY : z (exposedYIndex m) = 0) :
    ENNReal.ofReal ‖rowSuspensionCharacteristic (m + 2) k t z‖ =
      ∫⁻ R : Fin m → (Fin k → ℝ),
        ENNReal.ofReal (conditionalRowSuspensionCharacteristic t R z).re
        ∂(Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) := by
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  have hint := integrable_conditionalRowSuspensionCharacteristic m k t z
  have hpos : ∀ R : Fin m → (Fin k → ℝ),
      0 < (conditionalRowSuspensionCharacteristic t R z).re := by
    intro R
    rw [conditionalRowSuspensionCharacteristic_left_endpoint t R
      (z := z) (v := z) (fun _ ↦ rfl) hY]
    exact (bilinearGaussianIntegral_endpoints_pos
      (n := Module.finrank ℝ (RealCofactorSpace k)) rfl
      (t • rowSuspensionTailT z R)
      (ContinuousLinearMap.id ℝ (RealCofactorSpace k))
      ((t * z (exposedXIndex m)) • rowSuspensionRightVector z R) 0).1
  have him : ∀ R : Fin m → (Fin k → ℝ),
      (conditionalRowSuspensionCharacteristic t R z).im = 0 := by
    intro R
    rw [conditionalRowSuspensionCharacteristic_left_endpoint t R
      (z := z) (v := z) (fun _ ↦ rfl) hY]
    exact bilinearGaussianIntegral_left_endpoint_im
      (t • rowSuspensionTailT z R)
      (ContinuousLinearMap.id ℝ (RealCofactorSpace k))
      ((t * z (exposedXIndex m)) • rowSuspensionRightVector z R)
  have hchar : rowSuspensionCharacteristic (m + 2) k t z =
      ((∫ R, (conditionalRowSuspensionCharacteristic t R z).re ∂muR : ℝ) : ℂ) := by
    rw [rowSuspensionCharacteristic_eq_integral_conditional]
    calc
      (∫ R, conditionalRowSuspensionCharacteristic t R z ∂muR) =
          ∫ R, (((conditionalRowSuspensionCharacteristic t R z).re : ℝ) : ℂ) ∂muR := by
        apply integral_congr_ae
        filter_upwards [] with R
        apply Complex.ext
        · simp
        · simpa using him R
      _ = ((∫ R, (conditionalRowSuspensionCharacteristic t R z).re ∂muR : ℝ) : ℂ) :=
        integral_ofReal
  rw [hchar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun R ↦ (hpos R).le)]
  exact ofReal_integral_eq_lintegral_ofReal hint.re
    (Filter.Eventually.of_forall fun R ↦ (hpos R).le)

theorem ofReal_norm_rowSuspensionCharacteristic_eq_lintegral_right
    {m k : ℕ} (t : ℝ) (z : Fin (m + 2) → ℝ)
    (hX : z (exposedXIndex m) = 0) :
    ENNReal.ofReal ‖rowSuspensionCharacteristic (m + 2) k t z‖ =
      ∫⁻ R : Fin m → (Fin k → ℝ),
        ENNReal.ofReal (conditionalRowSuspensionCharacteristic t R z).re
        ∂(Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k) := by
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  have hint := integrable_conditionalRowSuspensionCharacteristic m k t z
  have hpos : ∀ R : Fin m → (Fin k → ℝ),
      0 < (conditionalRowSuspensionCharacteristic t R z).re := by
    intro R
    rw [conditionalRowSuspensionCharacteristic_right_endpoint t R
      (z := z) (v := z) (fun _ ↦ rfl) hX]
    exact (bilinearGaussianIntegral_endpoints_pos
      (n := Module.finrank ℝ (RealCofactorSpace k)) rfl
      (t • rowSuspensionTailT z R)
      (ContinuousLinearMap.id ℝ (RealCofactorSpace k)) 0
      ((t * z (exposedYIndex m)) • rowSuspensionLeftVector z R)).2
  have him : ∀ R : Fin m → (Fin k → ℝ),
      (conditionalRowSuspensionCharacteristic t R z).im = 0 := by
    intro R
    rw [conditionalRowSuspensionCharacteristic_right_endpoint t R
      (z := z) (v := z) (fun _ ↦ rfl) hX]
    exact bilinearGaussianIntegral_right_endpoint_im
      (t • rowSuspensionTailT z R)
      (ContinuousLinearMap.id ℝ (RealCofactorSpace k))
      ((t * z (exposedYIndex m)) • rowSuspensionLeftVector z R)
  have hchar : rowSuspensionCharacteristic (m + 2) k t z =
      ((∫ R, (conditionalRowSuspensionCharacteristic t R z).re ∂muR : ℝ) : ℂ) := by
    rw [rowSuspensionCharacteristic_eq_integral_conditional]
    calc
      (∫ R, conditionalRowSuspensionCharacteristic t R z ∂muR) =
          ∫ R, (((conditionalRowSuspensionCharacteristic t R z).re : ℝ) : ℂ) ∂muR := by
        apply integral_congr_ae
        filter_upwards [] with R
        apply Complex.ext
        · simp
        · simpa using him R
      _ = ((∫ R, (conditionalRowSuspensionCharacteristic t R z).re ∂muR : ℝ) : ℂ) :=
        integral_ofReal
  rw [hchar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun R ↦ (hpos R).le)]
  exact ofReal_integral_eq_lintegral_ofReal hint.re
    (Filter.Eventually.of_forall fun R ↦ (hpos R).le)

/-- Integrated lossless compression for the two exposed top-row
coordinates. -/
theorem rowSuspensionCharacteristic_two_exposed_max
    {m k : ℕ} (t : ℝ)
    (z zLeft zRight : Fin (m + 2) → ℝ) (theta : ℝ)
    (htheta : 0 < theta) (htheta_one : theta < 1)
    (hbgLeft : ∀ i : Fin m,
      zLeft (remainingIndex m i) = z (remainingIndex m i))
    (hbgRight : ∀ i : Fin m,
      zRight (remainingIndex m i) = z (remainingIndex m i))
    (hLeftY : zLeft (exposedYIndex m) = 0)
    (hRightX : zRight (exposedXIndex m) = 0)
    (hscaleX : z (exposedXIndex m) =
      Real.sqrt theta • zLeft (exposedXIndex m))
    (hscaleY : z (exposedYIndex m) =
      Real.sqrt (1 - theta) • zRight (exposedYIndex m)) :
    ‖rowSuspensionCharacteristic (m + 2) k t z‖ ≤
      max ‖rowSuspensionCharacteristic (m + 2) k t zLeft‖
        ‖rowSuspensionCharacteristic (m + 2) k t zRight‖ := by
  let muR := Measure.pi fun _ : Fin m ↦ standardRealGaussianVectorMeasure k
  let fLeft : (Fin m → (Fin k → ℝ)) → ENNReal := fun R ↦
    ENNReal.ofReal (conditionalRowSuspensionCharacteristic t R zLeft).re
  let fRight : (Fin m → (Fin k → ℝ)) → ENNReal := fun R ↦
    ENNReal.ofReal (conditionalRowSuspensionCharacteristic t R zRight).re
  have hleftMeas : AEMeasurable fLeft muR := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_conditionalRowSuspensionCharacteristic m k t zLeft).1.re.aemeasurable
  have hrightMeas : AEMeasurable fRight muR := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_conditionalRowSuspensionCharacteristic m k t zRight).1.re.aemeasurable
  have hpoint := fun R : Fin m → (Fin k → ℝ) ↦
    conditionalRowSuspensionCharacteristic_endpoints_pos_and_geometric
      t R z zLeft zRight theta htheta.le htheta_one.le
      hbgLeft hbgRight hLeftY hRightX hscaleX hscaleY
  have hnorm : ENNReal.ofReal
      ‖rowSuspensionCharacteristic (m + 2) k t z‖ ≤
      ∫⁻ R, ENNReal.ofReal
        ‖conditionalRowSuspensionCharacteristic t R z‖ ∂muR := by
    rw [rowSuspensionCharacteristic_eq_integral_conditional]
    have hreal := norm_integral_le_integral_norm
      (fun R ↦ conditionalRowSuspensionCharacteristic t R z) (μ := muR)
    have hof := ENNReal.ofReal_le_ofReal hreal
    rw [ofReal_integral_norm_eq_lintegral_enorm
      (integrable_conditionalRowSuspensionCharacteristic m k t z)] at hof
    simpa [muR, ofReal_norm] using hof
  have hscaled :
      (∫⁻ R, ENNReal.ofReal
          ‖conditionalRowSuspensionCharacteristic t R z‖ ∂muR) ≤
        (∫⁻ R, fLeft R ∂muR) ^ theta *
          (∫⁻ R, fRight R ∂muR) ^ (1 - theta) := by
    calc
      (∫⁻ R, ENNReal.ofReal
          ‖conditionalRowSuspensionCharacteristic t R z‖ ∂muR) =
        ∫⁻ R, (fLeft R) ^ theta * (fRight R) ^ (1 - theta) ∂muR := by
          apply lintegral_congr
          intro R
          rw [(hpoint R).2]
          rw [ENNReal.ofReal_mul
            (Real.rpow_nonneg (hpoint R).1.1.le theta)]
          rw [ENNReal.ofReal_rpow_of_nonneg (hpoint R).1.1.le htheta.le,
            ENNReal.ofReal_rpow_of_nonneg (hpoint R).1.2.le
              (sub_nonneg.mpr htheta_one.le)]
      _ ≤ (∫⁻ R, fLeft R ∂muR) ^ theta *
          (∫⁻ R, fRight R ∂muR) ^ (1 - theta) :=
        lintegral_geometric_interpolation_le muR fLeft fRight theta
          hleftMeas hrightMeas htheta.le htheta_one.le
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
      ‖rowSuspensionCharacteristic (m + 2) k t zLeft‖ := by
    dsimp [Lval, fLeft]
    simpa [muR] using
      (ofReal_norm_rowSuspensionCharacteristic_eq_lintegral_left
        t zLeft hLeftY).symm
  have hRval : Rval = ENNReal.ofReal
      ‖rowSuspensionCharacteristic (m + 2) k t zRight‖ := by
    dsimp [Rval, fRight]
    simpa [muR] using
      (ofReal_norm_rowSuspensionCharacteristic_eq_lintegral_right
        t zRight hRightX).symm
  have hENN : ENNReal.ofReal
      ‖rowSuspensionCharacteristic (m + 2) k t z‖ ≤
      ENNReal.ofReal (max
        ‖rowSuspensionCharacteristic (m + 2) k t zLeft‖
        ‖rowSuspensionCharacteristic (m + 2) k t zRight‖) := by
    rw [ENNReal.ofReal_max]
    calc
      ENNReal.ofReal ‖rowSuspensionCharacteristic (m + 2) k t z‖ ≤
          ∫⁻ R, ENNReal.ofReal
            ‖conditionalRowSuspensionCharacteristic t R z‖ ∂muR := hnorm
      _ ≤ Lval ^ theta * Rval ^ (1 - theta) := by
        simpa [Lval, Rval] using hscaled
      _ ≤ max Lval Rval := hgeom
      _ = max (ENNReal.ofReal
          ‖rowSuspensionCharacteristic (m + 2) k t zLeft‖)
          (ENNReal.ofReal
            ‖rowSuspensionCharacteristic (m + 2) k t zRight‖) := by
        rw [hLval, hRval]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN

end

end LogdetLean.GramHafnian
