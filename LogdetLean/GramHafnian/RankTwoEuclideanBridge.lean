import LogdetLean.GramHafnian.RankTwoQuadraticTransform
import LogdetLean.GramHafnian.RankTwoOrthogonalInvariance
import LogdetLean.GramHafnian.RankTwoEigenReduction
import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Two-dimensional Euclidean bridge for the rank-two Gaussian moment

This file transports the already-proved four-scalar Gaussian calculation to
the standard Gaussian on two-dimensional Euclidean space.  It then gives a
coordinate-free interface: any explicit orthogonal diagonalisation of the
rank-two kernel can be plugged in without repeating measure theory.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

abbrev RealEuclideanTwo := EuclideanSpace Real (Fin 2)

/-- The canonical measurable isometry from a pair of reals to Euclidean
two-space. -/
def pairToRealEuclideanTwo (x : Real × Real) : RealEuclideanTwo :=
  WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm x)

theorem measurable_pairToRealEuclideanTwo :
    Measurable pairToRealEuclideanTwo := by
  unfold pairToRealEuclideanTwo
  fun_prop

theorem map_pairToRealEuclideanTwo_standardGaussianPair :
    Measure.map pairToRealEuclideanTwo standardGaussianPair =
      stdGaussian RealEuclideanTwo := by
  have hpair :=
    (measurePreserving_finTwoArrow (gaussianReal 0 1)).symm
  change Measure.map
      (fun x : Real × Real ↦
        WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm x))
      standardGaussianPair = stdGaussian RealEuclideanTwo
  have hcomp :
      (fun x : Real × Real ↦
        WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm x)) =
        (fun y : Fin 2 → Real ↦ WithLp.toLp 2 y) ∘
          MeasurableEquiv.finTwoArrow.symm := rfl
  rw [hcomp]
  rw [← Measure.map_map]
  · rw [show standardGaussianPair =
        (gaussianReal 0 1).prod (gaussianReal 0 1) by rfl,
      hpair.map_eq, map_pi_eq_stdGaussian]
  · fun_prop
  · fun_prop

theorem map_prod_pairToRealEuclideanTwo_twoStandardGaussianPairs :
    Measure.map (Prod.map pairToRealEuclideanTwo pairToRealEuclideanTwo)
        twoStandardGaussianPairs =
      (stdGaussian RealEuclideanTwo).prod (stdGaussian RealEuclideanTwo) := by
  rw [twoStandardGaussianPairs]
  rw [← Measure.map_prod_map]
  · rw [map_pairToRealEuclideanTwo_standardGaussianPair]
  all_goals exact measurable_pairToRealEuclideanTwo

/-- Diagonal bilinear form on two-dimensional Euclidean space. -/
def euclideanDiagonalRankTwoBilinear (lambdaPlus lambdaMinus : Real)
    (w : RealEuclideanTwo × RealEuclideanTwo) : Real :=
  lambdaPlus * w.1 0 * w.2 0 + lambdaMinus * w.1 1 * w.2 1

theorem euclideanDiagonalRankTwoBilinear_pairToRealEuclideanTwo
    (lambdaPlus lambdaMinus : Real)
    (w : (Real × Real) × (Real × Real)) :
    euclideanDiagonalRankTwoBilinear lambdaPlus lambdaMinus
        (pairToRealEuclideanTwo w.1, pairToRealEuclideanTwo w.2) =
      diagonalRankTwoBilinear lambdaPlus lambdaMinus w := by
  unfold euclideanDiagonalRankTwoBilinear pairToRealEuclideanTwo
  simp [diagonalRankTwoBilinear, MeasurableEquiv.finTwoArrow]

/-- The exact squared-binomial formula on standard Gaussian Euclidean
two-space. -/
theorem integral_euclideanDiagonalRankTwoBilinear_add_sub_pow_two_mul
    (C D : Real) (n : Nat) :
    (∫ w : RealEuclideanTwo × RealEuclideanTwo,
        euclideanDiagonalRankTwoBilinear (C + D) (C - D) w ^ (2 * n)
          ∂((stdGaussian RealEuclideanTwo).prod
            (stdGaussian RealEuclideanTwo))) =
      ((2 * n).factorial : Real) *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : Nat) : Real) ^ 2 *
            C ^ (2 * j) * D ^ (2 * (n - j)) := by
  rw [← map_prod_pairToRealEuclideanTwo_twoStandardGaussianPairs]
  rw [integral_map]
  · convert integral_diagonalRankTwoBilinear_add_sub_pow_two_mul C D n using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w ↦ by
      change
        euclideanDiagonalRankTwoBilinear (C + D) (C - D)
            (pairToRealEuclideanTwo w.1, pairToRealEuclideanTwo w.2) ^
              (2 * n) =
          diagonalRankTwoBilinear (C + D) (C - D) w ^ (2 * n)
      rw [euclideanDiagonalRankTwoBilinear_pairToRealEuclideanTwo]
  · exact (measurable_pairToRealEuclideanTwo.prodMap
      measurable_pairToRealEuclideanTwo).aemeasurable
  · apply Measurable.aestronglyMeasurable
    unfold euclideanDiagonalRankTwoBilinear
    fun_prop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- The rank-two action bundled as a linear endomorphism. -/
def rankTwoActionLinear (g₁ g₂ : E) : E →ₗ[Real] E where
  toFun := rankTwoAction g₁ g₂
  map_add' x y := by
    unfold rankTwoAction
    simp only [inner_add_right, add_smul]
    module
  map_smul' c x := by
    unfold rankTwoAction
    simp only [inner_smul_right, RingHom.id_apply, smul_add, smul_smul]

@[simp] theorem rankTwoActionLinear_apply (g₁ g₂ x : E) :
    rankTwoActionLinear g₁ g₂ x = rankTwoAction g₁ g₂ x := rfl

/-- A two-vector orthonormal eigenbasis diagonalizes the rank-two bilinear
form pointwise in its Euclidean coordinates. -/
theorem innerRankTwoBilinear_eq_euclideanDiagonal_of_eigenbasis
    (g₁ g₂ : E) (b : OrthonormalBasis (Fin 2) Real E)
    (lambdaPlus lambdaMinus : Real)
    (hplus : rankTwoAction g₁ g₂ (b 0) = lambdaPlus • b 0)
    (hminus : rankTwoAction g₁ g₂ (b 1) = lambdaMinus • b 1)
    (w : E × E) :
    innerRankTwoBilinear g₁ g₂ w =
      euclideanDiagonalRankTwoBilinear lambdaPlus lambdaMinus
        (b.repr w.1, b.repr w.2) := by
  have haction (x : E) :
      rankTwoAction g₁ g₂ x =
        (lambdaPlus * b.repr x 0) • b 0 +
          (lambdaMinus * b.repr x 1) • b 1 := by
    change rankTwoActionLinear g₁ g₂ x = _
    calc
      rankTwoActionLinear g₁ g₂ x =
          rankTwoActionLinear g₁ g₂
            (∑ i, b.repr x i • b i) := by rw [b.sum_repr]
      _ = ∑ i, b.repr x i • rankTwoActionLinear g₁ g₂ (b i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul]
      _ = (lambdaPlus * b.repr x 0) • b 0 +
          (lambdaMinus * b.repr x 1) • b 1 := by
        rw [Fin.sum_univ_two]
        simp only [rankTwoActionLinear_apply, hplus, hminus, smul_smul]
        module
  rw [← inner_rankTwoAction_eq_innerRankTwoBilinear, haction]
  unfold euclideanDiagonalRankTwoBilinear
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have hcoord0 : inner Real w.1 (b 0) = b.repr w.1 0 := by
    calc
      inner Real w.1 (b 0) = inner Real (b 0) w.1 := real_inner_comm _ _
      _ = b.repr w.1 0 := (b.repr_apply_apply w.1 0).symm
  have hcoord1 : inner Real w.1 (b 1) = b.repr w.1 1 := by
    calc
      inner Real w.1 (b 1) = inner Real (b 1) w.1 := real_inner_comm _ _
      _ = b.repr w.1 1 := (b.repr_apply_apply w.1 1).symm
  rw [hcoord0, hcoord1]
  simp only [Prod.fst, Prod.snd]
  ring

theorem map_prod_stdGaussian_linearIsometryEquiv_to_two
    (O : E ≃ₗᵢ[Real] RealEuclideanTwo) :
    Measure.map (Prod.map O O)
        ((stdGaussian E).prod (stdGaussian E)) =
      (stdGaussian RealEuclideanTwo).prod
        (stdGaussian RealEuclideanTwo) := by
  have h := (Measure.map_prod_map (stdGaussian E) (stdGaussian E)
    (by fun_prop : Measurable O) (by fun_prop : Measurable O)).symm
  simpa only [stdGaussian_map] using h

/-- Plug-in theorem for an explicit orthogonal diagonalisation of the
rank-two kernel.  The hypothesis is purely pointwise algebra; all Gaussian
transport and moment evaluation are proved here. -/
theorem integral_innerRankTwoBilinear_pow_of_diagonalization
    (g₁ g₂ : E) (O : E ≃ₗᵢ[Real] RealEuclideanTwo)
    (C D : Real) (n : Nat)
    (hdiag : ∀ w : E × E,
      innerRankTwoBilinear g₁ g₂ w =
        euclideanDiagonalRankTwoBilinear (C + D) (C - D)
          (O w.1, O w.2)) :
    (∫ w : E × E, innerRankTwoBilinear g₁ g₂ w ^ (2 * n)
        ∂((stdGaussian E).prod (stdGaussian E))) =
      ((2 * n).factorial : Real) *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : Nat) : Real) ^ 2 *
            C ^ (2 * j) * D ^ (2 * (n - j)) := by
  calc
    (∫ w : E × E, innerRankTwoBilinear g₁ g₂ w ^ (2 * n)
        ∂((stdGaussian E).prod (stdGaussian E))) =
        ∫ w : E × E,
          euclideanDiagonalRankTwoBilinear (C + D) (C - D)
            (O w.1, O w.2) ^ (2 * n)
          ∂((stdGaussian E).prod (stdGaussian E)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ congrArg (· ^ (2 * n)) (hdiag w)
    _ = ∫ z : RealEuclideanTwo × RealEuclideanTwo,
          euclideanDiagonalRankTwoBilinear (C + D) (C - D) z ^ (2 * n)
          ∂((stdGaussian RealEuclideanTwo).prod
            (stdGaussian RealEuclideanTwo)) := by
      rw [← map_prod_stdGaussian_linearIsometryEquiv_to_two O, integral_map]
      · rfl
      · fun_prop
      · apply Measurable.aestronglyMeasurable
        unfold euclideanDiagonalRankTwoBilinear
        fun_prop
    _ = _ :=
      integral_euclideanDiagonalRankTwoBilinear_add_sub_pow_two_mul C D n

/-- Exact Gaussian moment from a proved two-vector orthonormal eigenbasis;
there is no remaining pointwise diagonalisation hypothesis. -/
theorem integral_innerRankTwoBilinear_pow_of_eigenbasis
    (g₁ g₂ : E) (b : OrthonormalBasis (Fin 2) Real E)
    (C D : Real) (n : Nat)
    (hplus : rankTwoAction g₁ g₂ (b 0) = (C + D) • b 0)
    (hminus : rankTwoAction g₁ g₂ (b 1) = (C - D) • b 1) :
    (∫ w : E × E, innerRankTwoBilinear g₁ g₂ w ^ (2 * n)
        ∂((stdGaussian E).prod (stdGaussian E))) =
      ((2 * n).factorial : Real) *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : Nat) : Real) ^ 2 *
            C ^ (2 * j) * D ^ (2 * (n - j)) := by
  apply integral_innerRankTwoBilinear_pow_of_diagonalization
    g₁ g₂ b.repr C D n
  intro w
  exact innerRankTwoBilinear_eq_euclideanDiagonal_of_eigenbasis
    g₁ g₂ b (C + D) (C - D) hplus hminus w

end

end LogdetLean.GramHafnian
