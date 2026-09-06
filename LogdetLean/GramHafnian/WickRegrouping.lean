import LogdetLean.GramHafnian.PerfectMatchingCount
import LogdetLean.GramHafnian.AuxiliaryHafnianEndpoint
/-!
# Finite Wick regrouping

The Gaussian colouring sum is regrouped by perfect matchings.  The central
finite object is a perfect matching that preserves every fibre of a vertex
colouring.
-/

open scoped BigOperators Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

namespace TypePerfectMatching

/-- A matching that preserves the fibres of `c`. -/
abbrev Compatible {I K : Type*} (c : I → K) :=
  {M : TypePerfectMatching I // ∀ i, c (M i) = c i}

/-- Restrict a compatible matching to one colour fibre. -/
def restrictToColor {I K : Type*} (c : I → K)
    (M : TypePerfectMatching I) (hM : ∀ i, c (M i) = c i) (a : K) :
    TypePerfectMatching {i : I // c i = a} := by
  let f : {i : I // c i = a} → {i : I // c i = a} := fun i ↦
    ⟨M i.1, by rw [hM i.1, i.2]⟩
  have hf : Function.Involutive f := by
    intro i
    apply Subtype.ext
    exact M.mate_mate i.1
  exact
    { mate := hf.toPerm
      mate_ne := by
        intro i hi
        apply M.mate_ne i.1
        exact congrArg Subtype.val hi
      mate_mate := hf }

/-- The disjoint union of one matching on every colour fibre. -/
def sigmaColorMatching {I K : Type*} (c : I → K)
    (N : ∀ a, TypePerfectMatching {i : I // c i = a}) :
    TypePerfectMatching (Σ a, {i : I // c i = a}) := by
  let f : (Σ a, {i : I // c i = a}) → (Σ a, {i : I // c i = a}) :=
    fun z ↦ ⟨z.1, N z.1 z.2⟩
  have hf : Function.Involutive f := by
    rintro ⟨a, i⟩
    simpa [f] using congrArg
      (fun j : {i : I // c i = a} ↦
        (⟨a, j⟩ : Σ b, {i : I // c i = b}))
      ((N a).mate_mate i)
  exact
    { mate := hf.toPerm
      mate_ne := by
        rintro ⟨a, i⟩
        change f ⟨a, i⟩ ≠ ⟨a, i⟩
        intro hi
        apply (N a).mate_ne i
        simpa [f] using hi
      mate_mate := hf }

/-- Combine one matching on every colour fibre into a global matching. -/
def combineColorFibers {I K : Type*} (c : I → K)
    (N : ∀ a, TypePerfectMatching {i : I // c i = a}) :
    TypePerfectMatching I :=
  TypePerfectMatching.congr (Equiv.sigmaFiberEquiv c) (sigmaColorMatching c N)

theorem combineColorFibers_compatible {I K : Type*} (c : I → K)
    (N : ∀ a, TypePerfectMatching {i : I // c i = a}) (i : I) :
    c (combineColorFibers c N i) = c i := by
  exact (N (c i) ⟨i, rfl⟩).2

/-- Compatible global matchings are exactly independent choices of a
matching inside every colour fibre. -/
def compatibleEquivPi {I K : Type*} (c : I → K) :
    Compatible c ≃ ∀ a, TypePerfectMatching {i : I // c i = a} where
  toFun M a := restrictToColor c M.1 M.2 a
  invFun N := ⟨combineColorFibers c N, combineColorFibers_compatible c N⟩
  left_inv M := by
    apply Subtype.ext
    apply TypePerfectMatching.ext
    intro i
    rfl
  right_inv N := by
    funext a
    apply TypePerfectMatching.ext
    intro i
    apply Subtype.ext
    rcases i with ⟨i, hi⟩
    subst a
    rfl

/-- Number of pairings on an arbitrary finite linearly ordered type of even
cardinality. -/
theorem card_eq_doubleFactorial_of_even
    {α : Type*} [Fintype α] [DecidableEq α]
    (hEven : Even (Fintype.card α)) :
    Fintype.card (TypePerfectMatching α) =
      (Fintype.card α - 1)‼ := by
  rcases hEven with ⟨q, hq⟩
  have hcard : Fintype.card α = 2 * q := by omega
  let e : α ≃ Fin (2 * q) := Fintype.equivOfCardEq (by simpa using hcard)
  calc
    Fintype.card (TypePerfectMatching α) =
        Fintype.card (TypePerfectMatching (Fin (2 * q))) :=
      Fintype.card_congr (TypePerfectMatching.congr e)
    _ = Fintype.card (PerfectMatching q) :=
      Fintype.card_congr (TypePerfectMatching.finEquiv q).symm
    _ = (2 * q - 1)‼ := TypePerfectMatching.card_perfectMatching q
    _ = (Fintype.card α - 1)‼ := by rw [hcard]

/-- Pair representatives for a matching on a linearly ordered type. -/
def genericPairReps {α : Type*} [Fintype α] [LinearOrder α]
    (M : TypePerfectMatching α) : Finset α :=
  Finset.univ.filter fun i ↦ i < M i

theorem card_genericPairReps_two_mul
    {α : Type*} [Fintype α] [LinearOrder α]
    (M : TypePerfectMatching α) :
    2 * (genericPairReps M).card = Fintype.card α := by
  classical
  let upper : Finset α := Finset.univ.filter fun i ↦ M i < i
  have himage : (genericPairReps M).image M = upper := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_image] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      simpa [genericPairReps, upper, M.mate_mate] using hj
    · intro hi
      rw [Finset.mem_image]
      refine ⟨M i, ?_, M.mate_mate i⟩
      simpa [genericPairReps, upper, M.mate_mate] using hi
  have hdisj : Disjoint (genericPairReps M) upper := by
    rw [Finset.disjoint_left]
    intro i hlo hiup
    exact (lt_asymm (by simpa [genericPairReps] using hlo)
      (by simpa [upper] using hiup))
  have hunion : genericPairReps M ∪ upper = Finset.univ := by
    ext i
    simp only [Finset.mem_union, genericPairReps, upper, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    exact lt_or_gt_of_ne (M.mate_ne i).symm
  have hcardUpper : upper.card = (genericPairReps M).card := by
    rw [← himage]
    exact Finset.card_image_of_injective _ M.mate.injective
  calc
    2 * (genericPairReps M).card =
        (genericPairReps M).card + (genericPairReps M).card := by omega
    _ = (genericPairReps M).card + upper.card := by rw [hcardUpper]
    _ = (genericPairReps M ∪ upper).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = Fintype.card α := by rw [hunion, Finset.card_univ]

theorem even_card_of_nonempty
    {α : Type*} [Fintype α] [LinearOrder α]
    (M : TypePerfectMatching α) : Even (Fintype.card α) := by
  refine ⟨(genericPairReps M).card, ?_⟩
  simpa [two_mul] using (card_genericPairReps_two_mul M).symm

/-- The cardinality of pairings on a finite ordered type, including the odd
case where no pairing exists. -/
theorem card_eq_wickMultiplicity
    {α : Type*} [Fintype α] [LinearOrder α] :
    Fintype.card (TypePerfectMatching α) =
      if Even (Fintype.card α) then (Fintype.card α - 1)‼ else 0 := by
  classical
  by_cases hEven : Even (Fintype.card α)
  · simp [hEven, card_eq_doubleFactorial_of_even hEven]
  · simp only [hEven, ↓reduceIte]
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro M
    exact hEven (even_card_of_nonempty M)

end TypePerfectMatching

theorem card_colorFiber_eq_colorMultiplicity
    {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (c : I → K) (a : K) :
    Fintype.card {i : I // c i = a} = colorMultiplicity c a := by
  simp [Fintype.card_subtype, colorMultiplicity]

/-- The number of matchings compatible with a vertex colouring is the
product of the pairing counts of its colour fibres. -/
theorem card_compatible_eq_prod_wickMultiplicity
    {I K : Type*} [Fintype I] [LinearOrder I]
    [Fintype K] [DecidableEq K] (c : I → K) :
    Fintype.card (TypePerfectMatching.Compatible c) =
      ∏ a, if Even (colorMultiplicity c a) then
        (colorMultiplicity c a - 1)‼ else 0 := by
  classical
  calc
    Fintype.card (TypePerfectMatching.Compatible c) =
        Fintype.card (∀ a, TypePerfectMatching {i : I // c i = a}) :=
      Fintype.card_congr (TypePerfectMatching.compatibleEquivPi c)
    _ = ∏ a, Fintype.card (TypePerfectMatching {i : I // c i = a}) := by
      rw [Fintype.card_pi]
    _ = ∏ a, if Even (colorMultiplicity c a) then
          (colorMultiplicity c a - 1)‼ else 0 := by
      apply Finset.prod_congr rfl
      intro a _
      rw [TypePerfectMatching.card_eq_wickMultiplicity,
        card_colorFiber_eq_colorMultiplicity]

/-- Complex-cast form matching the scalar Gaussian moment convention used
in `gaussianWickColoringSum`. -/
theorem cast_card_compatible_eq_prod_standardRealGaussianMoment
    {I K : Type*} [Fintype I] [LinearOrder I]
    [Fintype K] [DecidableEq K] (c : I → K) :
    (Fintype.card (TypePerfectMatching.Compatible c) : ℂ) =
      ∏ a, (standardRealGaussianMoment (colorMultiplicity c a) : ℂ) := by
  rw [card_compatible_eq_prod_wickMultiplicity]
  push_cast
  apply Finset.prod_congr rfl
  intro a _
  by_cases hEven : Even (colorMultiplicity c a)
  · simp [standardRealGaussianMoment, hEven]
  · simp [standardRealGaussianMoment, hEven]

theorem cast_natCard_compatible_eq_prod_standardRealGaussianMoment
    {I K : Type*} [Fintype I] [LinearOrder I]
    [Fintype K] [DecidableEq K] (c : I → K) :
    (Nat.card (TypePerfectMatching.Compatible c) : ℂ) =
      ∏ a, (standardRealGaussianMoment (colorMultiplicity c a) : ℂ) := by
  rw [Nat.card_eq_fintype_card]
  exact cast_card_compatible_eq_prod_standardRealGaussianMoment c

namespace PerfectMatching

theorem mate_mem_pairReps_iff_not_mem (M : PerfectMatching n)
    (i : Fin (2 * n)) :
    M i ∈ M.pairReps ↔ i ∉ M.pairReps := by
  constructor
  · intro hmate hi
    exact (M.exactly_one_mem_pairReps i).2 ⟨hi, hmate⟩
  · intro hi
    exact (M.exactly_one_mem_pairReps i).1.resolve_left hi

theorem not_mate_mem_pairReps_iff_mem (M : PerfectMatching n)
    (i : Fin (2 * n)) :
    M i ∉ M.pairReps ↔ i ∈ M.pairReps := by
  rw [M.mate_mem_pairReps_iff_not_mem]
  exact not_not

end PerfectMatching

/-- Extend a colour on the pair representatives to both endpoints of each
pair. -/
def vertexColoringOfPairColoring (M : PerfectMatching n)
    (d : PairColoring M k) : Fin (2 * n) → Fin k :=
  fun i ↦ if hi : i ∈ M.pairReps then d ⟨i, hi⟩
    else d ⟨M i, (M.mate_mem_pairReps_iff_not_mem i).2 hi⟩

@[simp] theorem vertexColoringOfPairColoring_apply_rep
    (M : PerfectMatching n) (d : PairColoring M k) (i : M.pairReps) :
    vertexColoringOfPairColoring M d i.1 = d i := by
  simp [vertexColoringOfPairColoring, i.2]

@[simp] theorem vertexColoringOfPairColoring_apply_mate_rep
    (M : PerfectMatching n) (d : PairColoring M k) (i : M.pairReps) :
    vertexColoringOfPairColoring M d (M i.1) = d i := by
  have hmate : M i.1 ∉ M.pairReps :=
    (M.not_mate_mem_pairReps_iff_mem i.1).2 i.2
  simp [vertexColoringOfPairColoring, hmate, M.apply_apply]

theorem vertexColoringOfPairColoring_compatible
    (M : PerfectMatching n) (d : PairColoring M k) (i : Fin (2 * n)) :
    vertexColoringOfPairColoring M d (M i) =
      vertexColoringOfPairColoring M d i := by
  by_cases hi : i ∈ M.pairReps
  · have hmate : M i ∉ M.pairReps :=
      (M.not_mate_mem_pairReps_iff_mem i).2 hi
    simp [vertexColoringOfPairColoring, hi, hmate, M.apply_apply]
  · have hmate : M i ∈ M.pairReps :=
      (M.mate_mem_pairReps_iff_not_mem i).2 hi
    simp [vertexColoringOfPairColoring, hi, hmate, M.apply_apply]

/-- Vertex colourings preserved by a concrete matching. -/
abbrev CompatibleVertexColoring (M : PerfectMatching n) (k : ℕ) :=
  {c : Fin (2 * n) → Fin k // ∀ i, c (M i) = c i}

/-- A colour per pair is equivalent to a vertex colouring constant on every
matched edge. -/
def pairColoringEquivCompatibleVertexColoring (M : PerfectMatching n) (k : ℕ) :
    PairColoring M k ≃ CompatibleVertexColoring M k where
  toFun d := ⟨vertexColoringOfPairColoring M d,
    vertexColoringOfPairColoring_compatible M d⟩
  invFun c := fun i ↦ c.1 i.1
  left_inv d := by
    funext i
    exact vertexColoringOfPairColoring_apply_rep M d i
  right_inv c := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ M.pairReps
    · simp [vertexColoringOfPairColoring, hi]
    · simp [vertexColoringOfPairColoring, hi, c.2 i]

/-- Concrete perfect matchings compatible with a fixed vertex colouring. -/
abbrev CompatiblePerfectMatching
    (c : Fin (2 * n) → Fin k) :=
  {M : PerfectMatching n // ∀ i, c (M i) = c i}

/-- Swap the two indices in the incidence relation “matching compatible with
vertex colouring”. -/
def matchingCompatibleColoringSwap (n k : ℕ) :
    (Σ M : PerfectMatching n, CompatibleVertexColoring M k) ≃
      (Σ c : Fin (2 * n) → Fin k, CompatiblePerfectMatching c) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv z := by rcases z with ⟨M, c, h⟩; rfl
  right_inv z := by rcases z with ⟨c, M, h⟩; rfl

/-- Global reindexing equivalence behind finite Wick regrouping. -/
def matchingPairColoringEquivColoringCompatible (n k : ℕ) :
    (Σ M : PerfectMatching n, PairColoring M k) ≃
      (Σ c : Fin (2 * n) → Fin k, CompatiblePerfectMatching c) :=
  (Equiv.sigmaCongrRight fun M ↦
    pairColoringEquivCompatibleVertexColoring M k).trans
      (matchingCompatibleColoringSwap n k)

@[simp] theorem matchingPairColoringEquivColoringCompatible_apply
    (M : PerfectMatching n) (d : PairColoring M k) :
    matchingPairColoringEquivColoringCompatible n k ⟨M, d⟩ =
      ⟨vertexColoringOfPairColoring M d,
        ⟨M, vertexColoringOfPairColoring_compatible M d⟩⟩ := rfl

/-- The concrete and transportable compatible-matching representations are
equivalent. -/
def compatiblePerfectMatchingEquivTypeCompatible
    (c : Fin (2 * n) → Fin k) :
    CompatiblePerfectMatching c ≃ TypePerfectMatching.Compatible c where
  toFun M := ⟨TypePerfectMatching.finEquiv n M.1, M.2⟩
  invFun M := ⟨(TypePerfectMatching.finEquiv n).symm M.1, M.2⟩
  left_inv M := by apply Subtype.ext; rfl
  right_inv M := by apply Subtype.ext; rfl

theorem cast_card_compatiblePerfectMatching_eq_prod_standardRealGaussianMoment
    (c : Fin (2 * n) → Fin k) :
    (Fintype.card (CompatiblePerfectMatching c) : ℂ) =
      ∏ a, (standardRealGaussianMoment (colorMultiplicity c a) : ℂ) := by
  calc
    (Fintype.card (CompatiblePerfectMatching c) : ℂ) =
        (Nat.card (CompatiblePerfectMatching c) : ℂ) := by
      rw [Nat.card_eq_fintype_card]
    _ = (Nat.card (TypePerfectMatching.Compatible c) : ℂ) := by
      congr 1
      exact Nat.card_congr (compatiblePerfectMatchingEquivTypeCompatible c)
    _ = ∏ a, (standardRealGaussianMoment
          (colorMultiplicity c a) : ℂ) :=
      cast_natCard_compatible_eq_prod_standardRealGaussianMoment c

/-- Extending a pair colouring does not change its monomial: it merely
rewrites the product once per vertex instead of once per pair. -/
theorem complexColoringCoefficient_vertexColoringOfPairColoring
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ)
    (M : PerfectMatching n) (d : PairColoring M k) :
    complexColoringCoefficient X (vertexColoringOfPairColoring M d) =
      coloredMatchingMonomial X M d := by
  classical
  have hlower :
      (∏ i ∈ M.pairReps,
          X (vertexColoringOfPairColoring M d i) i) =
        ∏ i : M.pairReps, X (d i) i.1 := by
    calc
      (∏ i ∈ M.pairReps,
          X (vertexColoringOfPairColoring M d i) i) =
          ∏ i : M.pairReps,
            X (vertexColoringOfPairColoring M d i.1) i.1 :=
        Finset.prod_subtype M.pairReps (fun _ ↦ Iff.rfl)
          (fun i ↦ X (vertexColoringOfPairColoring M d i) i)
      _ = ∏ i : M.pairReps, X (d i) i.1 := by
        apply Finset.prod_congr rfl
        intro i _
        exact congrArg (fun a ↦ X a i.1)
          (vertexColoringOfPairColoring_apply_rep M d i)
  have hupper :
      (∏ i ∈ M.upperReps,
          X (vertexColoringOfPairColoring M d i) i) =
        ∏ i : M.pairReps, X (d i) (M i.1) := by
    calc
      (∏ i ∈ M.upperReps,
          X (vertexColoringOfPairColoring M d i) i) =
          ∏ i ∈ M.pairReps.image M,
            X (vertexColoringOfPairColoring M d i) i := by
        rw [M.image_mate_pairReps]
      _ = ∏ i ∈ M.pairReps,
            X (vertexColoringOfPairColoring M d (M i)) (M i) :=
        Finset.prod_image M.mate.injective.injOn
      _ = ∏ i : M.pairReps,
            X (vertexColoringOfPairColoring M d (M i.1)) (M i.1) :=
        Finset.prod_subtype M.pairReps (fun _ ↦ Iff.rfl)
          (fun i ↦ X (vertexColoringOfPairColoring M d (M i)) (M i))
      _ = ∏ i : M.pairReps, X (d i) (M i.1) := by
        apply Finset.prod_congr rfl
        intro i _
        exact congrArg (fun a ↦ X a (M i.1))
          (vertexColoringOfPairColoring_apply_mate_rep M d i)
  unfold complexColoringCoefficient coloredMatchingMonomial
  calc
    (∏ i, X (vertexColoringOfPairColoring M d i) i) =
        ∏ i ∈ M.pairReps ∪ M.upperReps,
          X (vertexColoringOfPairColoring M d i) i := by
      rw [M.pairReps_union_upperReps]
    _ = (∏ i ∈ M.pairReps,
          X (vertexColoringOfPairColoring M d i) i) *
        ∏ i ∈ M.upperReps,
          X (vertexColoringOfPairColoring M d i) i := by
      rw [Finset.prod_union M.pairReps_disjoint_upperReps]
    _ = (∏ i : M.pairReps, X (d i) i.1) *
        ∏ i : M.pairReps, X (d i) (M i.1) := by
      rw [hlower, hupper]
    _ = ∏ i : M.pairReps,
          X (d i) i.1 * X (d i) (M i.1) := by
      rw [Finset.prod_mul_distrib]

/-- **Finite Wick regrouping.**  The literal Gaussian moment colouring sum
is exactly the literal Gram-hafnian matching-colouring sum.  This theorem is
purely finite and contains no measure theory or probabilistic axiom. -/
theorem gaussianWickColoringSum_eq_gramMatchingColoringSum
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ) :
    gaussianWickColoringSum X = gramMatchingColoringSum X := by
  classical
  unfold gaussianWickColoringSum gramMatchingColoringSum
  symm
  calc
    (∑ M : PerfectMatching n, ∑ d : PairColoring M k,
        coloredMatchingMonomial X M d) =
        ∑ z : Σ M : PerfectMatching n, PairColoring M k,
          coloredMatchingMonomial X z.1 z.2 :=
      (Fintype.sum_sigma' fun M d ↦ coloredMatchingMonomial X M d).symm
    _ = ∑ z : Σ c : Fin (2 * n) → Fin k, CompatiblePerfectMatching c,
          complexColoringCoefficient X z.1 := by
      apply Fintype.sum_equiv
        (matchingPairColoringEquivColoringCompatible n k)
      intro z
      rcases z with ⟨M, d⟩
      exact
        (complexColoringCoefficient_vertexColoringOfPairColoring X M d).symm
    _ = ∑ c : Fin (2 * n) → Fin k,
          ∑ _M : CompatiblePerfectMatching c,
            complexColoringCoefficient X c :=
      Fintype.sum_sigma' fun c _M ↦ complexColoringCoefficient X c
    _ = ∑ c : Fin (2 * n) → Fin k,
          complexColoringCoefficient X c *
            ∏ a, (standardRealGaussianMoment
              (colorMultiplicity c a) : ℂ) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [show (∑ _M : CompatiblePerfectMatching c,
          complexColoringCoefficient X c) =
          (Fintype.card (CompatiblePerfectMatching c) : ℂ) *
            complexColoringCoefficient X c by simp]
      rw [cast_card_compatiblePerfectMatching_eq_prod_standardRealGaussianMoment]
      exact mul_comm _ _

/-- The analytic auxiliary-field identity obtained by combining the already
verified iid Gaussian integration formula with finite Wick regrouping. -/
theorem integral_complexAuxiliaryFieldProduct_eq_gramHafnian
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ) :
    (∫ g, complexAuxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : Fin k ↦ gaussianReal 0 1)) = gramHafnian X := by
  rw [integral_complexAuxiliaryFieldProduct_eq_gaussianWickColoringSum,
    gaussianWickColoringSum_eq_gramMatchingColoringSum,
    ← gramHafnian_eq_gramMatchingColoringSum]

end LogdetLean.GramHafnian
