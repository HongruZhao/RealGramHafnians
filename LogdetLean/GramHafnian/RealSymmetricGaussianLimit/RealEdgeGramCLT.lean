import LogdetLean.GramHafnian.SymmetricGaussianHafnian.RealSmallBallLowerCore
import LogdetLean.GramHafnian.AuxiliaryGaussian
import LogdetLean.GramHafnian.RealSymmetricGaussianLimit.FiniteDimensionalCLT
import Mathlib.Probability.Independence.InfinitePi
/-!
# Fixed-dimensional real strict-upper Gram CLT

For one standard real Gaussian row `x`, this file uses the quadratic vector
`(x_i x_j)_{i<j}`.  Literal product-Gaussian moment calculations prove that
this vector is centered and has identity covariance.  The generic finite
dimensional CLT therefore sends the normalized sum of iid rows to a standard
real Gaussian vector indexed by the strict upper triangle.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace LogdetLean.GramHafnian.RealSymmetricGaussianLimit

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Strictly ordered pairs parametrizing the upper triangle. -/
abbrev RealStrictUpperPair (N : ℕ) :=
  {p : Fin N × Fin N // p.1 < p.2}

/-- The Euclidean space of real strict-upper coordinates. -/
abbrev RealStrictUpperSpace (N : ℕ) :=
  EuclideanSpace ℝ (RealStrictUpperPair N)

theorem pairExponent_le_one_of_ne {N : ℕ}
    (a b i : Fin N) (h : a ≠ b) :
    pairExponent a b i ≤ 1 := by
  unfold pairExponent
  split_ifs <;> omega

theorem RealStrictUpperPair.ne {N : ℕ} (p : RealStrictUpperPair N) :
    p.1.1 ≠ p.1.2 :=
  ne_of_lt p.2

/-- Total coordinate exponent in a product of two edge monomials. -/
def realFourExponent {N : ℕ} (a b c d : Fin N) (i : Fin N) : ℕ :=
  pairExponent a b i + pairExponent c d i

/-- A finite real coordinate monomial. -/
def realMultiMonomial {N : ℕ} (e : Fin N → ℕ) (x : Fin N → ℝ) : ℝ :=
  ∏ i, x i ^ e i

theorem integrable_realMultiMonomial {N : ℕ} (e : Fin N → ℕ) :
    Integrable (realMultiMonomial e)
      (standardRealGaussianProduct (Fin N)) := by
  unfold realMultiMonomial standardRealGaussianProduct
  exact Integrable.fintype_prod fun i ↦ integrable_pow_gaussianReal (e i)

theorem integral_realMultiMonomial {N : ℕ} (e : Fin N → ℕ) :
    (∫ x, realMultiMonomial e x ∂standardRealGaussianProduct (Fin N)) =
      ∏ i, standardRealGaussianMoment (e i) := by
  unfold realMultiMonomial standardRealGaussianProduct
  convert integral_fintype_prod_eq_prod
    (fun (i : Fin N) (x : ℝ) ↦ x ^ e i)
      (μ := fun _ : Fin N ↦ gaussianReal 0 1) using 1
  simp_rw [integral_pow_gaussianReal_eq_standardRealGaussianMoment]

theorem realPairProduct_eq_monomial {N : ℕ}
    (p q : RealStrictUpperPair N) (x : Fin N → ℝ) :
    x p.1.1 * x p.1.2 * x q.1.1 * x q.1.2 =
      realMultiMonomial
        (realFourExponent p.1.1 p.1.2 q.1.1 q.1.2) x := by
  unfold realMultiMonomial realFourExponent
  simp_rw [pow_add, Finset.prod_mul_distrib]
  have h1 : (∏ i, x i ^ pairExponent p.1.1 p.1.2 i) =
      x p.1.1 * x p.1.2 := by
    unfold pairExponent
    simp_rw [pow_add, Finset.prod_mul_distrib]
    simp
  have h2 : (∏ i, x i ^ pairExponent q.1.1 q.1.2 i) =
      x q.1.1 * x q.1.2 := by
    unfold pairExponent
    simp_rw [pow_add, Finset.prod_mul_distrib]
    simp
  rw [h1, h2]
  ring

theorem pairExponent_ne_of_realStrictUpperPair_ne {N : ℕ}
    (p q : RealStrictUpperPair N) (hpq : p ≠ q) :
    pairExponent p.1.1 p.1.2 ≠ pairExponent q.1.1 q.1.2 := by
  intro h
  rcases (pairExponent_eq_iff p.1.1 p.1.2 q.1.1 q.1.2).mp h with hf | hs
  · apply hpq
    apply Subtype.ext
    exact Prod.ext hf.1 hf.2
  · have hp := p.2
    have hq := q.2
    omega

/-- Exact real fourth-moment kernel on strictly ordered pairs. -/
theorem realStrictUpperFourthMomentKernel {N : ℕ}
    (p q : RealStrictUpperPair N) :
    (∏ i, standardRealGaussianMoment
      (realFourExponent p.1.1 p.1.2 q.1.1 q.1.2 i)) =
      if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp only [if_pos]
    apply Finset.prod_eq_one
    intro i _hi
    have hle := pairExponent_le_one_of_ne
      p.1.1 p.1.2 i p.ne
    have hv : pairExponent p.1.1 p.1.2 i = 0 ∨
        pairExponent p.1.1 p.1.2 i = 1 := by omega
    rcases hv with h0 | h1
    · simp [realFourExponent, h0, standardRealGaussianMoment]
    · simp [realFourExponent, h1, standardRealGaussianMoment]
  · rw [if_neg hpq]
    have hfun := pairExponent_ne_of_realStrictUpperPair_ne p q hpq
    have hex : ∃ i, pairExponent p.1.1 p.1.2 i ≠
        pairExponent q.1.1 q.1.2 i := by
      by_contra h
      push Not at h
      exact hfun (funext h)
    rcases hex with ⟨i, hi⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    have hp_le := pairExponent_le_one_of_ne p.1.1 p.1.2 i p.ne
    have hq_le := pairExponent_le_one_of_ne q.1.1 q.1.2 i q.ne
    have hsum : realFourExponent p.1.1 p.1.2 q.1.1 q.1.2 i = 1 := by
      unfold realFourExponent
      omega
    simp [hsum, standardRealGaussianMoment]

theorem integral_realStrictUpperPairProduct {N : ℕ}
    (p q : RealStrictUpperPair N) :
    (∫ x : Fin N → ℝ,
      x p.1.1 * x p.1.2 * x q.1.1 * x q.1.2
      ∂standardRealGaussianProduct (Fin N)) =
      if p = q then 1 else 0 := by
  rw [integral_congr_ae
    (Filter.Eventually.of_forall (realPairProduct_eq_monomial p q))]
  rw [integral_realMultiMonomial, realStrictUpperFourthMomentKernel]

/-- One real Gaussian row, restricted to its strict-upper quadratic entries. -/
def realStrictUpperGramRow (N : ℕ) (x : Fin N → ℝ) :
    RealStrictUpperSpace N :=
  WithLp.toLp 2 fun p ↦ x p.1.1 * x p.1.2

/-- Scalar projection of one real quadratic row. -/
def realStrictUpperGramProjection {N : ℕ}
    (t : RealStrictUpperSpace N) (x : Fin N → ℝ) : ℝ :=
  ∑ p, t p * (x p.1.1 * x p.1.2)

theorem inner_realStrictUpperGramRow_eq_projection {N : ℕ}
    (t : RealStrictUpperSpace N) (x : Fin N → ℝ) :
    inner ℝ t (realStrictUpperGramRow N x) =
      realStrictUpperGramProjection t x := by
  rw [PiLp.inner_apply]
  unfold realStrictUpperGramRow realStrictUpperGramProjection
  simp only [RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

theorem realPairMonomial_eq_realMultiMonomial {N : ℕ}
    (p : RealStrictUpperPair N) (x : Fin N → ℝ) :
    x p.1.1 * x p.1.2 =
      realMultiMonomial (pairExponent p.1.1 p.1.2) x := by
  unfold realMultiMonomial pairExponent
  simp_rw [pow_add, Finset.prod_mul_distrib]
  simp

theorem integrable_realStrictUpperPairMonomial {N : ℕ}
    (p : RealStrictUpperPair N) :
    Integrable (fun x : Fin N → ℝ ↦ x p.1.1 * x p.1.2)
      (standardRealGaussianProduct (Fin N)) := by
  rw [show (fun x : Fin N → ℝ ↦ x p.1.1 * x p.1.2) =
      realMultiMonomial (pairExponent p.1.1 p.1.2) by
    funext x
    exact realPairMonomial_eq_realMultiMonomial p x]
  exact integrable_realMultiMonomial _

theorem integral_realStrictUpperPairMonomial {N : ℕ}
    (p : RealStrictUpperPair N) :
    (∫ x : Fin N → ℝ, x p.1.1 * x p.1.2
      ∂standardRealGaussianProduct (Fin N)) = 0 := by
  rw [integral_congr_ae
      (Filter.Eventually.of_forall (realPairMonomial_eq_realMultiMonomial p)),
    integral_realMultiMonomial]
  classical
  rw [Finset.prod_eq_zero (Finset.mem_univ p.1.1)]
  have hval : pairExponent p.1.1 p.1.2 p.1.1 = 1 := by
    simp [pairExponent, p.ne]
  simp [hval, standardRealGaussianMoment]

theorem integrable_realStrictUpperGramProjection {N : ℕ}
    (t : RealStrictUpperSpace N) :
    Integrable (realStrictUpperGramProjection t)
      (standardRealGaussianProduct (Fin N)) := by
  unfold realStrictUpperGramProjection
  exact integrable_finsetSum _ fun p _ ↦
    (integrable_realStrictUpperPairMonomial p).const_mul (t p)

theorem integral_realStrictUpperGramProjection {N : ℕ}
    (t : RealStrictUpperSpace N) :
    (∫ x, realStrictUpperGramProjection t x
      ∂standardRealGaussianProduct (Fin N)) = 0 := by
  unfold realStrictUpperGramProjection
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro p _hp
    rw [integral_const_mul, integral_realStrictUpperPairMonomial, mul_zero]
  · intro p _hp
    exact (integrable_realStrictUpperPairMonomial p).const_mul (t p)

def expandedRealStrictUpperGramProjectionSq {N : ℕ}
    (t : RealStrictUpperSpace N) (x : Fin N → ℝ) : ℝ :=
  ∑ p, ∑ q, (t p * t q) *
    (x p.1.1 * x p.1.2 * x q.1.1 * x q.1.2)

theorem realStrictUpperGramProjection_sq_eq_expanded {N : ℕ}
    (t : RealStrictUpperSpace N) (x : Fin N → ℝ) :
    realStrictUpperGramProjection t x ^ 2 =
      expandedRealStrictUpperGramProjectionSq t x := by
  classical
  unfold realStrictUpperGramProjection
    expandedRealStrictUpperGramProjectionSq
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

theorem integrable_realStrictUpperPairProduct {N : ℕ}
    (p q : RealStrictUpperPair N) :
    Integrable (fun x : Fin N → ℝ ↦
      x p.1.1 * x p.1.2 * x q.1.1 * x q.1.2)
      (standardRealGaussianProduct (Fin N)) := by
  rw [show (fun x : Fin N → ℝ ↦
      x p.1.1 * x p.1.2 * x q.1.1 * x q.1.2) =
      realMultiMonomial
        (realFourExponent p.1.1 p.1.2 q.1.1 q.1.2) by
    funext x
    exact realPairProduct_eq_monomial p q x]
  exact integrable_realMultiMonomial _

theorem integrable_expandedRealStrictUpperGramProjectionSq {N : ℕ}
    (t : RealStrictUpperSpace N) :
    Integrable (expandedRealStrictUpperGramProjectionSq t)
      (standardRealGaussianProduct (Fin N)) := by
  unfold expandedRealStrictUpperGramProjectionSq
  apply integrable_finsetSum
  intro p _hp
  apply integrable_finsetSum
  intro q _hq
  exact (integrable_realStrictUpperPairProduct p q).const_mul _

/-- One real quadratic row has identity covariance. -/
theorem integral_sq_realStrictUpperGramProjection {N : ℕ}
    (t : RealStrictUpperSpace N) :
    (∫ x, realStrictUpperGramProjection t x ^ 2
      ∂standardRealGaussianProduct (Fin N)) = ‖t‖ ^ 2 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (realStrictUpperGramProjection_sq_eq_expanded t))]
  unfold expandedRealStrictUpperGramProjectionSq
  rw [integral_finsetSum]
  · calc
      (∑ p, ∫ x, ∑ q, (t p * t q) *
          (x p.1.1 * x p.1.2 * x q.1.1 * x q.1.2)
          ∂standardRealGaussianProduct (Fin N)) =
          ∑ p, ∑ q, (t p * t q) * (if p = q then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro p _hp
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro q _hq
          rw [integral_const_mul, integral_realStrictUpperPairProduct]
        · intro q _hq
          exact (integrable_realStrictUpperPairProduct p q).const_mul _
      _ = ∑ p, t p ^ 2 := by simp [pow_two]
      _ = ‖t‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        apply Finset.sum_congr rfl
        intro p _hp
        simp [Real.norm_eq_abs, sq_abs]
  · intro p _hp
    apply integrable_finsetSum
    intro q _hq
    exact (integrable_realStrictUpperPairProduct p q).const_mul _

@[fun_prop] theorem measurable_realStrictUpperGramRow (N : ℕ) :
    Measurable (realStrictUpperGramRow N) := by
  unfold realStrictUpperGramRow
  fun_prop

/-- One row is centered in every Euclidean direction. -/
theorem integral_inner_realStrictUpperGramRow {N : ℕ}
    (t : RealStrictUpperSpace N) :
    (∫ x, inner ℝ t (realStrictUpperGramRow N x)
      ∂standardRealGaussianProduct (Fin N)) = 0 := by
  rw [show (fun x ↦ inner ℝ t (realStrictUpperGramRow N x)) =
      realStrictUpperGramProjection t by
    funext x
    exact inner_realStrictUpperGramRow_eq_projection t x]
  exact integral_realStrictUpperGramProjection t

/-- One row has identity covariance in every Euclidean direction. -/
theorem integral_sq_inner_realStrictUpperGramRow {N : ℕ}
    (t : RealStrictUpperSpace N) :
    (∫ x, inner ℝ t (realStrictUpperGramRow N x) ^ 2
      ∂standardRealGaussianProduct (Fin N)) = ‖t‖ ^ 2 := by
  rw [show (fun x ↦ inner ℝ t (realStrictUpperGramRow N x) ^ 2) =
      fun x ↦ realStrictUpperGramProjection t x ^ 2 by
    funext x
    congr 1
    exact inner_realStrictUpperGramRow_eq_projection t x]
  exact integral_sq_realStrictUpperGramProjection t

/-- Canonical countable stream of iid standard real Gaussian rows. -/
abbrev RealStrictUpperGramStream (N : ℕ) := ℕ → (Fin N → ℝ)

def realStrictUpperGramStreamMeasure (N : ℕ) :
    Measure (RealStrictUpperGramStream N) :=
  Measure.infinitePi fun _ : ℕ ↦ standardRealGaussianProduct (Fin N)

instance (N : ℕ) : IsProbabilityMeasure
    (realStrictUpperGramStreamMeasure N) := by
  unfold realStrictUpperGramStreamMeasure
  infer_instance

def realStrictUpperGramRowStream (N : ℕ) (i : ℕ)
    (omega : RealStrictUpperGramStream N) : RealStrictUpperSpace N :=
  realStrictUpperGramRow N (omega i)

@[fun_prop] theorem measurable_realStrictUpperGramRowStream (N i : ℕ) :
    Measurable (realStrictUpperGramRowStream N i) := by
  unfold realStrictUpperGramRowStream
  fun_prop

theorem iIndepFun_realStrictUpperGramRowStream (N : ℕ) :
    iIndepFun (realStrictUpperGramRowStream N)
      (realStrictUpperGramStreamMeasure N) := by
  have hEval : iIndepFun
      (fun i (omega : RealStrictUpperGramStream N) ↦ omega i)
      (realStrictUpperGramStreamMeasure N) := by
    exact iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
  have h := hEval.comp
    (fun _ ↦ realStrictUpperGramRow N)
    (fun _ ↦ measurable_realStrictUpperGramRow N)
  change iIndepFun
    (fun i (omega : RealStrictUpperGramStream N) ↦
      realStrictUpperGramRow N (omega i))
    (realStrictUpperGramStreamMeasure N)
  exact h

theorem identDistrib_realStrictUpperGramRowStream (N i : ℕ) :
    IdentDistrib
      (realStrictUpperGramRowStream N i)
      (realStrictUpperGramRowStream N 0)
      (realStrictUpperGramStreamMeasure N)
      (realStrictUpperGramStreamMeasure N) := by
  have hi := MeasurePreserving.hasLaw
    (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ standardRealGaussianProduct (Fin N)) i)
  have h0 := MeasurePreserving.hasLaw
    (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ standardRealGaussianProduct (Fin N)) 0)
  have heval := hi.identDistrib h0
  have hcomp := heval.comp (measurable_realStrictUpperGramRow N)
  change IdentDistrib
    (fun omega : RealStrictUpperGramStream N ↦
      realStrictUpperGramRow N (omega i))
    (fun omega : RealStrictUpperGramStream N ↦
      realStrictUpperGramRow N (omega 0))
    (realStrictUpperGramStreamMeasure N)
    (realStrictUpperGramStreamMeasure N)
  exact hcomp

theorem hasLaw_eval_realStrictUpperGramStream (N i : ℕ) :
    HasLaw (fun omega : RealStrictUpperGramStream N ↦ omega i)
      (standardRealGaussianProduct (Fin N))
      (realStrictUpperGramStreamMeasure N) :=
  MeasurePreserving.hasLaw
    (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ standardRealGaussianProduct (Fin N)) i)

theorem integral_inner_realStrictUpperGramRowStream {N : ℕ}
    (i : ℕ) (t : RealStrictUpperSpace N) :
    (∫ omega, inner ℝ t (realStrictUpperGramRowStream N i omega)
      ∂realStrictUpperGramStreamMeasure N) = 0 := by
  have hmeas : AEStronglyMeasurable
      (fun x : Fin N → ℝ ↦ inner ℝ t (realStrictUpperGramRow N x))
      (standardRealGaussianProduct (Fin N)) := by
    fun_prop
  have htransport :=
    (hasLaw_eval_realStrictUpperGramStream N i).integral_comp hmeas
  change (∫ omega, inner ℝ t (realStrictUpperGramRow N (omega i))
      ∂realStrictUpperGramStreamMeasure N) =
    ∫ x, inner ℝ t (realStrictUpperGramRow N x)
      ∂standardRealGaussianProduct (Fin N) at htransport
  rw [integral_inner_realStrictUpperGramRow] at htransport
  simpa [realStrictUpperGramRowStream] using htransport

theorem integral_sq_inner_realStrictUpperGramRowStream {N : ℕ}
    (i : ℕ) (t : RealStrictUpperSpace N) :
    (∫ omega, inner ℝ t (realStrictUpperGramRowStream N i omega) ^ 2
      ∂realStrictUpperGramStreamMeasure N) = ‖t‖ ^ 2 := by
  have hmeas : AEStronglyMeasurable
      (fun x : Fin N → ℝ ↦ inner ℝ t (realStrictUpperGramRow N x) ^ 2)
      (standardRealGaussianProduct (Fin N)) := by
    fun_prop
  have htransport :=
    (hasLaw_eval_realStrictUpperGramStream N i).integral_comp hmeas
  change (∫ omega, inner ℝ t (realStrictUpperGramRow N (omega i)) ^ 2
      ∂realStrictUpperGramStreamMeasure N) =
    ∫ x, inner ℝ t (realStrictUpperGramRow N x) ^ 2
      ∂standardRealGaussianProduct (Fin N) at htransport
  rw [integral_sq_inner_realStrictUpperGramRow] at htransport
  simpa [realStrictUpperGramRowStream] using htransport

/-- **Fixed-dimensional real strict-upper Gram CLT.**  The normalized sum of
literal iid quadratic rows converges in distribution to the standard real
Gaussian law on the strict upper triangle. -/
theorem tendstoInDistribution_realStrictUpperGramNormalizedSum_stdGaussian
    (N : ℕ) :
    TendstoInDistribution
      (normalizedPartialSum (realStrictUpperGramRowStream N)) Filter.atTop id
      (fun _ ↦ realStrictUpperGramStreamMeasure N)
      (stdGaussian (RealStrictUpperSpace N)) := by
  exact tendstoInDistribution_normalizedPartialSum_stdGaussian
    (realStrictUpperGramStreamMeasure N)
    (realStrictUpperGramRowStream N)
    (fun i ↦ (measurable_realStrictUpperGramRowStream N i).aemeasurable)
    (iIndepFun_realStrictUpperGramRowStream N)
    (identDistrib_realStrictUpperGramRowStream N)
    (fun t ↦ integral_inner_realStrictUpperGramRowStream 0 t)
    (fun t ↦ integral_sq_inner_realStrictUpperGramRowStream 0 t)

end

end LogdetLean.GramHafnian.RealSymmetricGaussianLimit
