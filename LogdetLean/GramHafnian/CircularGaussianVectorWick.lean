import LogdetLean.GramHafnian.CircularGaussianMoments
import LogdetLean.GramHafnian.ColumnProductWick
/-!
# The literal iid circular-Gaussian vector Wick bridge

This file instantiates the abstract one-column and independent-column
contraction theorems with the actual circular complex Gaussian constructed in
`CircularGaussianMoments`.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

variable {n k : ℕ}

/-- The law of a vector of `k` independent standard circular complex
Gaussians. -/
def circularGaussianVector (k : ℕ) : Measure (Fin k → ℂ) :=
  Measure.pi fun _ : Fin k ↦ circularGaussian

instance (k : ℕ) : SigmaFinite (circularGaussianVector k) := by
  unfold circularGaussianVector
  infer_instance

instance (k : ℕ) : IsProbabilityMeasure (circularGaussianVector k) := by
  unfold circularGaussianVector
  infer_instance

/-- Number of occurrences of `i` in the ordered pair `(a,b)`. -/
def pairExponent (a b i : Fin k) : ℕ :=
  (if i = a then 1 else 0) + (if i = b then 1 else 0)

theorem pairExponent_le_two (a b i : Fin k) : pairExponent a b i ≤ 2 := by
  unfold pairExponent
  split_ifs <;> omega

theorem pair_multiset_eq_iff (a b c d : Fin k) :
    ({a, b} : Multiset (Fin k)) = {c, d} ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  change a ::ₘ ({b} : Multiset (Fin k)) = c ::ₘ {d} ↔ _
  constructor
  · intro h
    rcases Multiset.cons_eq_cons.mp h with
      (⟨hac, hbd⟩ | ⟨hac, t, ht1, ht2⟩)
    · exact Or.inl ⟨hac, by simpa using hbd⟩
    · right
      have hbc : b = c :=
        (Multiset.singleton_eq_cons_iff t).mp ht1 |>.1
      have hda : d = a :=
        (Multiset.singleton_eq_cons_iff t).mp ht2 |>.1
      exact ⟨hda.symm, hbc⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.pair_comm _ _

theorem pairExponent_eq_multiset_count (a b i : Fin k) :
    pairExponent a b i = ({a, b} : Multiset (Fin k)).count i := by
  change (if i = a then 1 else 0) + (if i = b then 1 else 0) =
    Multiset.count i (a ::ₘ b ::ₘ 0)
  rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  split_ifs <;> omega

theorem pairExponent_eq_iff (a b c d : Fin k) :
    pairExponent a b = pairExponent c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [← pair_multiset_eq_iff]
  constructor
  · intro h
    apply Multiset.ext.mpr
    intro i
    rw [← pairExponent_eq_multiset_count, ← pairExponent_eq_multiset_count]
    exact congrFun h i
  · intro h
    funext i
    rw [pairExponent_eq_multiset_count, pairExponent_eq_multiset_count, h]

theorem prod_pairExponent_factorial (a b : Fin k) :
    (∏ i, ((pairExponent a b i).factorial : ℂ)) =
      if a = b then 2 else 1 := by
  classical
  by_cases hab : a = b
  · subst b
    rw [Finset.prod_eq_single a]
    · simp [pairExponent]
    · intro i _ hia
      simp [pairExponent, hia]
    · simp
  · rw [if_neg hab]
    apply Finset.prod_eq_one
    intro i _
    by_cases hia : i = a
    · simp [pairExponent, hia, hab]
    · by_cases hib : i = b
      · simp [pairExponent, hia, hib, hab, Ne.symm hab]
      · simp [pairExponent, hia, hib]

theorem coordinateFourthMonomial_eq_mixedComplexMultiMonomial
    (x : Fin k → ℂ) (a b c d : Fin k) :
    coordinateFourthMonomial x a b c d =
      mixedComplexMultiMonomial (pairExponent a b) (pairExponent c d) x := by
  classical
  unfold coordinateFourthMonomial mixedComplexMultiMonomial
    mixedComplexMonomial pairExponent
  simp only [pow_add, Finset.prod_mul_distrib]
  simp
  ring

/-- Every coordinate fourth monomial is integrable for the literal iid
circular-Gaussian vector law. -/
theorem integrable_coordinateFourthMonomial_circularGaussianVector
    (a b c d : Fin k) :
    Integrable (fun x ↦ coordinateFourthMonomial x a b c d)
      (circularGaussianVector k) := by
  rw [show (fun x ↦ coordinateFourthMonomial x a b c d) =
      mixedComplexMultiMonomial (pairExponent a b) (pairExponent c d) by
    funext x
    exact coordinateFourthMonomial_eq_mixedComplexMultiMonomial x a b c d]
  unfold circularGaussianVector mixedComplexMultiMonomial
  exact Integrable.fintype_prod fun i ↦
    integrable_mixedComplexMonomial_circularGaussian _ _
      (pairExponent_le_two a b i) (pairExponent_le_two c d i)

/-- Product-form evaluation of the literal iid-vector fourth monomial. -/
theorem integral_coordinateFourthMonomial_circularGaussianVector_product
    (a b c d : Fin k) :
    (∫ x, coordinateFourthMonomial x a b c d
        ∂(circularGaussianVector k)) =
      ∏ i, if pairExponent a b i = pairExponent c d i then
        ((pairExponent a b i).factorial : ℂ) else 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    coordinateFourthMonomial_eq_mixedComplexMultiMonomial x a b c d)]
  unfold circularGaussianVector
  rw [integral_mixedComplexMultiMonomial_iid]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_mixedComplexMonomial_circularGaussian _ _
    (pairExponent_le_two a b i) (pairExponent_le_two c d i)

/-- The finite scalar product resulting from coordinate independence is
exactly the two-pairing circular fourth kernel. -/
theorem prod_pairExponent_moments_eq_circularFourthKernel
    (a b c d : Fin k) :
    (∏ i, if pairExponent a b i = pairExponent c d i then
        ((pairExponent a b i).factorial : ℂ) else 0) =
      circularFourthKernel a b c d := by
  classical
  by_cases hEq : pairExponent a b = pairExponent c d
  · rcases (pairExponent_eq_iff a b c d).mp hEq with
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hprod :
          (∏ i, if pairExponent a b i = pairExponent a b i then
              ((pairExponent a b i).factorial : ℂ) else 0) =
            ∏ i, ((pairExponent a b i).factorial : ℂ) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [if_pos rfl]
      rw [hprod, prod_pairExponent_factorial]
      by_cases hab : a = b
      · subst b
        norm_num [circularFourthKernel, kroneckerDelta]
      · simp [circularFourthKernel, kroneckerDelta, hab, Ne.symm hab]
    · have hswap : pairExponent a b = pairExponent b a := by
        funext i
        simp only [pairExponent]
        omega
      simp_rw [if_pos (congrFun hswap _)]
      rw [prod_pairExponent_factorial]
      by_cases hab : a = b
      · subst b
        norm_num [circularFourthKernel, kroneckerDelta]
      · simp [circularFourthKernel, kroneckerDelta, hab, Ne.symm hab]
  · have hPair : ¬((a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
      intro hp
      exact hEq ((pairExponent_eq_iff a b c d).mpr hp)
    have hex : ∃ i, pairExponent a b i ≠ pairExponent c d i := by
      by_contra h
      push_neg at h
      exact hEq (funext h)
    obtain ⟨i, hi⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · by_cases hac : a = c <;> by_cases hbd : b = d <;>
        by_cases had : a = d <;> by_cases hbc : b = c <;>
          simp_all [circularFourthKernel, kroneckerDelta]
    · simp [hi]

/-- Literal iid circular-Gaussian fourth tensor. -/
theorem integral_coordinateFourthMonomial_circularGaussianVector
    (a b c d : Fin k) :
    (∫ x, coordinateFourthMonomial x a b c d
        ∂(circularGaussianVector k)) = circularFourthKernel a b c d := by
  rw [integral_coordinateFourthMonomial_circularGaussianVector_product]
  exact prod_pairExponent_moments_eq_circularFourthKernel a b c d

/-- Actual one-column circular-Gaussian Wick contraction, with no moment
assumption in the statement. -/
theorem integral_columnFourthIntegrand_circularGaussianVector
    (g₁ g₂ h₁ h₂ : Fin k → ℂ) :
    ∫ x, columnFourthIntegrand g₁ g₂ h₁ h₂ x
        ∂(circularGaussianVector k) =
      rankTwoBilinear g₁ g₂ h₁ h₂ := by
  exact integral_columnFourthIntegrand_eq_rankTwoBilinear
    (circularGaussianVector k) g₁ g₂ h₁ h₂
    integrable_coordinateFourthMonomial_circularGaussianVector
    integral_coordinateFourthMonomial_circularGaussianVector

/-- Actual `2n`-independent-column Wick bridge for literal iid circular
complex Gaussians. -/
theorem integral_columnFourthProduct_circularGaussianVector
    (g₁ g₂ h₁ h₂ : Fin k → ℂ) :
    ∫ X, columnFourthProduct (n := n) g₁ g₂ h₁ h₂ X
        ∂(Measure.pi fun _ : Fin (2 * n) ↦ circularGaussianVector k) =
      rankTwoBilinear g₁ g₂ h₁ h₂ ^ (2 * n) := by
  exact integral_columnFourthProduct_eq_rankTwo_pow
    (circularGaussianVector k) g₁ g₂ h₁ h₂
    integrable_coordinateFourthMonomial_circularGaussianVector
    integral_coordinateFourthMonomial_circularGaussianVector

end

end LogdetLean.GramHafnian
