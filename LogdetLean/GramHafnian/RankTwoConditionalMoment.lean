import LogdetLean.GramHafnian.RankTwoEuclideanBridge
import LogdetLean.FixedSubspaceGaussian
/-!
# Coordinate-free conditional rank-two Gaussian moment

The ambient Gaussian vectors are first projected onto the span of the two
fixed vectors.  The existing fixed-subspace Gaussian theorem makes this an
exact equality of laws, so the subsequent diagonalisation is intrinsically
at most two-dimensional.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LogdetLean.GramHafnian

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- The deterministic subspace carrying the rank-two kernel. -/
def rankTwoSpan (g₁ g₂ : E) : Submodule Real E :=
  Submodule.span Real (Set.range ![g₁, g₂])

/-- The first fixed vector, regarded as a vector in its two-vector span. -/
def rankTwoSpanFirst (g₁ g₂ : E) : rankTwoSpan g₁ g₂ :=
  ⟨g₁, Submodule.subset_span ⟨0, by simp [rankTwoSpan]⟩⟩

/-- The second fixed vector, regarded as a vector in its two-vector span. -/
def rankTwoSpanSecond (g₁ g₂ : E) : rankTwoSpan g₁ g₂ :=
  ⟨g₂, Submodule.subset_span ⟨1, by simp [rankTwoSpan]⟩⟩

@[simp] theorem rankTwoSpanFirst_coe (g₁ g₂ : E) :
    ((rankTwoSpanFirst g₁ g₂ : rankTwoSpan g₁ g₂) : E) = g₁ := rfl

@[simp] theorem rankTwoSpanSecond_coe (g₁ g₂ : E) :
    ((rankTwoSpanSecond g₁ g₂ : rankTwoSpan g₁ g₂) : E) = g₂ := rfl

/-- The rank-two form only sees the orthogonal projections onto the span of
its two deterministic vectors. -/
theorem innerRankTwoBilinear_eq_spanProjection
    (g₁ g₂ : E) (w : E × E) :
    innerRankTwoBilinear g₁ g₂ w =
      innerRankTwoBilinear (rankTwoSpanFirst g₁ g₂)
        (rankTwoSpanSecond g₁ g₂)
        ((rankTwoSpan g₁ g₂).orthogonalProjectionOnto w.1,
          (rankTwoSpan g₁ g₂).orthogonalProjectionOnto w.2) := by
  let K := rankTwoSpan g₁ g₂
  let u₁ : K := rankTwoSpanFirst g₁ g₂
  let u₂ : K := rankTwoSpanSecond g₁ g₂
  have h11 : inner Real u₁ (K.orthogonalProjectionOnto w.1) =
      inner Real g₁ w.1 := by
    simpa [K, u₁] using K.inner_orthogonalProjectionOnto_eq_of_mem_left u₁ w.1
  have h12 : inner Real u₁ (K.orthogonalProjectionOnto w.2) =
      inner Real g₁ w.2 := by
    simpa [K, u₁] using K.inner_orthogonalProjectionOnto_eq_of_mem_left u₁ w.2
  have h21 : inner Real u₂ (K.orthogonalProjectionOnto w.1) =
      inner Real g₂ w.1 := by
    simpa [K, u₂] using K.inner_orthogonalProjectionOnto_eq_of_mem_left u₂ w.1
  have h22 : inner Real u₂ (K.orthogonalProjectionOnto w.2) =
      inner Real g₂ w.2 := by
    simpa [K, u₂] using K.inner_orthogonalProjectionOnto_eq_of_mem_left u₂ w.2
  unfold innerRankTwoBilinear
  change _ =
    inner Real u₁ (K.orthogonalProjectionOnto w.1) *
        inner Real u₂ (K.orthogonalProjectionOnto w.2) +
      inner Real u₁ (K.orthogonalProjectionOnto w.2) *
        inner Real u₂ (K.orthogonalProjectionOnto w.1)
  rw [h11, h12, h21, h22]

theorem map_prod_rankTwoSpanProjection_stdGaussian
    (g₁ g₂ : E) :
    Measure.map
        (Prod.map (rankTwoSpan g₁ g₂).orthogonalProjectionOnto
          (rankTwoSpan g₁ g₂).orthogonalProjectionOnto)
        ((stdGaussian E).prod (stdGaussian E)) =
      (stdGaussian (rankTwoSpan g₁ g₂)).prod
        (stdGaussian (rankTwoSpan g₁ g₂)) := by
  rw [← Measure.map_prod_map]
  · rw [(LogdetLean.hasLaw_orthogonalProjectionOnto_stdGaussian
        (rankTwoSpan g₁ g₂)).map_eq]
  all_goals fun_prop

/-- Exact reduction of the ambient conditional moment to the at-most
two-dimensional span. -/
theorem integral_innerRankTwoBilinear_eq_rankTwoSpan
    (g₁ g₂ : E) (m : Nat) :
    (∫ w : E × E, innerRankTwoBilinear g₁ g₂ w ^ m
        ∂((stdGaussian E).prod (stdGaussian E))) =
      ∫ z : (rankTwoSpan g₁ g₂) × (rankTwoSpan g₁ g₂),
        innerRankTwoBilinear (rankTwoSpanFirst g₁ g₂)
          (rankTwoSpanSecond g₁ g₂) z ^ m
        ∂((stdGaussian (rankTwoSpan g₁ g₂)).prod
          (stdGaussian (rankTwoSpan g₁ g₂))) := by
  rw [← map_prod_rankTwoSpanProjection_stdGaussian g₁ g₂, integral_map]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w ↦ by
      change innerRankTwoBilinear g₁ g₂ w ^ m =
        innerRankTwoBilinear
          (rankTwoSpanFirst g₁ g₂) (rankTwoSpanSecond g₁ g₂)
          ((rankTwoSpan g₁ g₂).orthogonalProjectionOnto w.1,
            (rankTwoSpan g₁ g₂).orthogonalProjectionOnto w.2) ^ m
      exact congrArg (· ^ m) (innerRankTwoBilinear_eq_spanProjection g₁ g₂ w)
  · fun_prop
  · apply Measurable.aestronglyMeasurable
    unfold innerRankTwoBilinear
    fun_prop

/-- Linear independence is unchanged when the two vectors are regarded in
their own span. -/
theorem linearIndependent_rankTwoSpan
    (g₁ g₂ : E) (hli : LinearIndependent Real ![g₁, g₂]) :
    LinearIndependent Real
      ![rankTwoSpanFirst g₁ g₂, rankTwoSpanSecond g₁ g₂] := by
  let K := rankTwoSpan g₁ g₂
  let u : Fin 2 → K :=
    ![rankTwoSpanFirst g₁ g₂, rankTwoSpanSecond g₁ g₂]
  apply (K.subtype.linearIndependent_iff (by simp)).mp
  have hu : K.subtype ∘ u = ![g₁, g₂] := by
    funext i
    fin_cases i <;> rfl
  rw [hu]
  exact hli

/-- Under linear independence, the carrier span has dimension exactly two. -/
theorem finrank_rankTwoSpan_eq_two
    (g₁ g₂ : E) (hli : LinearIndependent Real ![g₁, g₂]) :
    Module.finrank Real (rankTwoSpan g₁ g₂) = 2 := by
  rw [rankTwoSpan, finrank_span_eq_card hli]
  simp

theorem rankTwoEigenPlus_norm_ne_zero_of_linearIndependent
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    (u₁ u₂ : F) (hli : LinearIndependent Real ![u₁, u₂]) :
    rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂ ≠ 0 := by
  intro hzero
  have hsum :
      ∑ i : Fin 2, ![‖u₂‖, ‖u₁‖] i • ![u₁, u₂] i = 0 := by
    rw [Fin.sum_univ_two]
    simpa [rankTwoEigenPlus] using hzero
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) _ hsum
  have hnorm : ‖u₂‖ = 0 := hcoeff 0
  exact (norm_ne_zero_iff.mpr (hli.ne_zero 1)) hnorm

theorem rankTwoEigenMinus_norm_ne_zero_of_linearIndependent
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    (u₁ u₂ : F) (hli : LinearIndependent Real ![u₁, u₂]) :
    rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂ ≠ 0 := by
  intro hzero
  have hsum :
      ∑ i : Fin 2, ![‖u₂‖, -‖u₁‖] i • ![u₁, u₂] i = 0 := by
    rw [Fin.sum_univ_two]
    simpa [rankTwoEigenMinus, sub_eq_add_neg, neg_smul] using hzero
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) _ hsum
  have hnorm : ‖u₂‖ = 0 := hcoeff 0
  exact (norm_ne_zero_iff.mpr (hli.ne_zero 1)) hnorm

/-- Normalized plus/minus eigenvectors form an orthonormal pair whenever the
two input vectors are linearly independent. -/
theorem orthonormal_normalize_rankTwoEigen
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    (u₁ u₂ : F) (hli : LinearIndependent Real ![u₁, u₂]) :
    Orthonormal Real
      ![NormedSpace.normalize
          (rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂),
        NormedSpace.normalize
          (rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂)] := by
  let ep := rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂
  let em := rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂
  have hep : ep ≠ 0 := by
    exact rankTwoEigenPlus_norm_ne_zero_of_linearIndependent u₁ u₂ hli
  have hem : em ≠ 0 := by
    exact rankTwoEigenMinus_norm_ne_zero_of_linearIndependent u₁ u₂ hli
  have horth : inner Real ep em = 0 := by
    apply inner_rankTwoEigenPlus_eigenMinus u₁ u₂ ‖u₁‖ ‖u₂‖
      (inner Real u₁ u₂)
    · exact real_inner_self_eq_norm_sq u₁
    · exact real_inner_self_eq_norm_sq u₂
    · rfl
  have hselfp : inner Real (NormedSpace.normalize ep)
      (NormedSpace.normalize ep) = 1 := by
    rw [real_inner_self_eq_norm_sq, NormedSpace.norm_normalize hep]
    norm_num
  have hselfm : inner Real (NormedSpace.normalize em)
      (NormedSpace.normalize em) = 1 := by
    rw [real_inner_self_eq_norm_sq, NormedSpace.norm_normalize hem]
    norm_num
  have hpm : inner Real (NormedSpace.normalize ep)
      (NormedSpace.normalize em) = 0 := by
    unfold NormedSpace.normalize
    simp only [inner_smul_left, inner_smul_right, starRingEnd_apply,
      star_trivial, horth, mul_zero]
  have hmp : inner Real (NormedSpace.normalize em)
      (NormedSpace.normalize ep) = 0 := by
    rw [real_inner_comm]
    exact hpm
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [ep, em]

/-- Normalizing the plus eigenvector preserves its exact eigenvalue. -/
theorem rankTwoAction_normalize_eigenPlus
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    (u₁ u₂ : F) :
    rankTwoAction u₁ u₂
        (NormedSpace.normalize
          (rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂)) =
      (inner Real u₁ u₂ + ‖u₁‖ * ‖u₂‖) •
        NormedSpace.normalize
          (rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂) := by
  unfold NormedSpace.normalize
  rw [show rankTwoAction u₁ u₂
      (‖rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂‖⁻¹ •
        rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂) =
      ‖rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂‖⁻¹ •
        rankTwoAction u₁ u₂
          (rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂) by
        unfold rankTwoAction
        simp only [inner_smul_right, smul_add, smul_smul],
    rankTwoAction_eigenPlus u₁ u₂ ‖u₁‖ ‖u₂‖ (inner Real u₁ u₂)
      (real_inner_self_eq_norm_sq u₁) (real_inner_self_eq_norm_sq u₂) rfl]
  module

/-- Normalizing the minus eigenvector preserves its exact eigenvalue. -/
theorem rankTwoAction_normalize_eigenMinus
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    (u₁ u₂ : F) :
    rankTwoAction u₁ u₂
        (NormedSpace.normalize
          (rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂)) =
      (inner Real u₁ u₂ - ‖u₁‖ * ‖u₂‖) •
        NormedSpace.normalize
          (rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂) := by
  unfold NormedSpace.normalize
  rw [show rankTwoAction u₁ u₂
      (‖rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂‖⁻¹ •
        rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂) =
      ‖rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂‖⁻¹ •
        rankTwoAction u₁ u₂
          (rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂) by
        unfold rankTwoAction
        simp only [inner_smul_right, smul_add, smul_smul],
    rankTwoAction_eigenMinus u₁ u₂ ‖u₁‖ ‖u₂‖ (inner Real u₁ u₂)
      (real_inner_self_eq_norm_sq u₁) (real_inner_self_eq_norm_sq u₂) rfl]
  module

/-- In the two-vector span, the normalized algebraic eigenvectors extend
directly to an orthonormal basis. -/
theorem exists_rankTwoEigenOrthonormalBasis
    (g₁ g₂ : E) (hli : LinearIndependent Real ![g₁, g₂]) :
    ∃ b : OrthonormalBasis (Fin 2) Real (rankTwoSpan g₁ g₂),
      b 0 = NormedSpace.normalize
          (rankTwoEigenPlus
            ‖rankTwoSpanFirst g₁ g₂‖ ‖rankTwoSpanSecond g₁ g₂‖
            (rankTwoSpanFirst g₁ g₂) (rankTwoSpanSecond g₁ g₂)) ∧
      b 1 = NormedSpace.normalize
          (rankTwoEigenMinus
            ‖rankTwoSpanFirst g₁ g₂‖ ‖rankTwoSpanSecond g₁ g₂‖
            (rankTwoSpanFirst g₁ g₂) (rankTwoSpanSecond g₁ g₂)) := by
  let u₁ : rankTwoSpan g₁ g₂ := rankTwoSpanFirst g₁ g₂
  let u₂ : rankTwoSpan g₁ g₂ := rankTwoSpanSecond g₁ g₂
  let v : Fin 2 → rankTwoSpan g₁ g₂ :=
    ![NormedSpace.normalize (rankTwoEigenPlus ‖u₁‖ ‖u₂‖ u₁ u₂),
      NormedSpace.normalize (rankTwoEigenMinus ‖u₁‖ ‖u₂‖ u₁ u₂)]
  have hliK : LinearIndependent Real ![u₁, u₂] := by
    simpa [u₁, u₂] using linearIndependent_rankTwoSpan g₁ g₂ hli
  have hon : Orthonormal Real v := by
    simpa [v] using orthonormal_normalize_rankTwoEigen u₁ u₂ hliK
  have hcard : Fintype.card (Fin 2) =
      Module.finrank Real (rankTwoSpan g₁ g₂) := by
    simpa using (finrank_rankTwoSpan_eq_two g₁ g₂ hli).symm
  have hspan : ⊤ ≤ Submodule.span Real (Set.range v) := by
    rw [hon.linearIndependent.span_eq_top_of_card_eq_finrank hcard]
  let b : OrthonormalBasis (Fin 2) Real (rankTwoSpan g₁ g₂) :=
    OrthonormalBasis.mk hon hspan
  refine ⟨b, ?_, ?_⟩
  · have hb := congrFun (OrthonormalBasis.coe_mk hon hspan) 0
    simpa [b, v, u₁, u₂] using hb
  · have hb := congrFun (OrthonormalBasis.coe_mk hon hspan) 1
    simpa [b, v, u₁, u₂] using hb

/-- Exact conditional even moment for a linearly independent fixed pair,
in the spectral factorization most directly produced by diagonalization. -/
theorem integral_innerRankTwoBilinear_pow_two_mul_spectral_of_linearIndependent
    (g₁ g₂ : E) (n : Nat)
    (hli : LinearIndependent Real ![g₁, g₂]) :
    (∫ w : E × E, innerRankTwoBilinear g₁ g₂ w ^ (2 * n)
        ∂((stdGaussian E).prod (stdGaussian E))) =
      ((2 * n).factorial : Real) *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : Nat) : Real) ^ 2 *
            (inner Real g₁ g₂) ^ (2 * j) *
              (‖g₁‖ * ‖g₂‖) ^ (2 * (n - j)) := by
  let u₁ : rankTwoSpan g₁ g₂ := rankTwoSpanFirst g₁ g₂
  let u₂ : rankTwoSpan g₁ g₂ := rankTwoSpanSecond g₁ g₂
  obtain ⟨b, hb0, hb1⟩ := exists_rankTwoEigenOrthonormalBasis g₁ g₂ hli
  have hplus : rankTwoAction u₁ u₂ (b 0) =
      (inner Real u₁ u₂ + ‖u₁‖ * ‖u₂‖) • b 0 := by
    rw [hb0]
    exact rankTwoAction_normalize_eigenPlus u₁ u₂
  have hminus : rankTwoAction u₁ u₂ (b 1) =
      (inner Real u₁ u₂ - ‖u₁‖ * ‖u₂‖) • b 1 := by
    rw [hb1]
    exact rankTwoAction_normalize_eigenMinus u₁ u₂
  rw [integral_innerRankTwoBilinear_eq_rankTwoSpan]
  have hmoment := integral_innerRankTwoBilinear_pow_of_eigenbasis
    u₁ u₂ b (inner Real u₁ u₂) (‖u₁‖ * ‖u₂‖) n hplus hminus
  simpa [u₁, u₂] using hmoment

theorem normProduct_pow_two_mul (x y : Real) (r : Nat) :
    (x * y) ^ (2 * r) = (x ^ 2 * y ^ 2) ^ r := by
  calc
    (x * y) ^ (2 * r) = x ^ (2 * r) * y ^ (2 * r) := mul_pow x y _
    _ = (x ^ 2) ^ r * (y ^ 2) ^ r := by rw [pow_mul, pow_mul]
    _ = (x ^ 2 * y ^ 2) ^ r := (mul_pow (x ^ 2) (y ^ 2) r).symm

/-- Paper-facing conditional moment formula.  This is algebraically the same
as the spectral version, but displays the radial factor as a product of
squared norms, in the form used by the outer Gamma--Beta calculation. -/
theorem integral_innerRankTwoBilinear_pow_two_mul_of_linearIndependent
    (g₁ g₂ : E) (n : Nat)
    (hli : LinearIndependent Real ![g₁, g₂]) :
    (∫ w : E × E, innerRankTwoBilinear g₁ g₂ w ^ (2 * n)
        ∂((stdGaussian E).prod (stdGaussian E))) =
      ((2 * n).factorial : Real) *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : Nat) : Real) ^ 2 *
            (‖g₁‖ ^ 2 * ‖g₂‖ ^ 2) ^ (n - j) *
              (inner Real g₁ g₂) ^ (2 * j) := by
  rw [integral_innerRankTwoBilinear_pow_two_mul_spectral_of_linearIndependent
    g₁ g₂ n hli]
  apply congrArg (((2 * n).factorial : Real) * ·)
  apply Finset.sum_congr rfl
  intro j hj
  rw [normProduct_pow_two_mul]
  ring

end

end LogdetLean.GramHafnian
