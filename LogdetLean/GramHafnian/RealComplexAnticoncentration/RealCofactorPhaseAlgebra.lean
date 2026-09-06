import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralCofactorLaw
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseBackground
/-!
# Real two-column cofactor phase algebra

The existing deterministic two-exposed-column identities are polynomial
identities over `ℂ`.  This file transports them faithfully to `ℝ` through
the injective ring homomorphism `Complex.ofReal`.  No probability or analytic
input is used here.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 1600000

abbrev RealTwoExposedColumnFamily (m k : ℕ) :=
  Fin (m + 2) → (Fin k → ℝ)

def realColumnTransposeGram {ι : Type*} [Fintype ι] {k : ℕ}
    (A : ι → (Fin k → ℝ)) : Matrix ι ι ℝ :=
  fun i j ↦ ∑ a : Fin k, A i a * A j a

def finiteRealGramCofactorVector
    {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
    (A : ι → (Fin k → ℝ)) (j : ι) : ℝ :=
  typeHafnian
    (realColumnTransposeGram (fun i : {i : ι // i ≠ j} ↦ A i.1))

def realRemainingHafnianDeleteOne {m k : ℕ}
    (A : RealTwoExposedColumnFamily m k) (a : Fin m) : ℝ :=
  typeHafnian (realColumnTransposeGram
    (fun i : {i : Fin m // i ≠ a} ↦ A (remainingIndex m i.1)))

def realRemainingHafnianDeleteThree {m k : ℕ}
    (A : RealTwoExposedColumnFamily m k) (j a b : Fin m) : ℝ :=
  typeHafnian (realColumnTransposeGram
    (fun i : {i : Fin m // i ≠ j ∧ i ≠ a ∧ i ≠ b} ↦
      A (remainingIndex m i.1)))

def realCofactorQ {m k : ℕ} (A : RealTwoExposedColumnFamily m k) :
    Fin k → ℝ :=
  fun p ↦ ∑ a : Fin m,
    realRemainingHafnianDeleteOne A a * A (remainingIndex m a) p

def realCofactorM {m k : ℕ} (A : RealTwoExposedColumnFamily m k)
    (j : Fin m) : Matrix (Fin k) (Fin k) ℝ :=
  fun p q ↦
    (if p = q then realRemainingHafnianDeleteOne A j else 0) +
      ∑ b : {b : Fin m // b ≠ j},
        ∑ a : {a : Fin m // a ≠ j ∧ a ≠ b.1},
          realRemainingHafnianDeleteThree A j a.1 b.1 *
            A (remainingIndex m a.1) p * A (remainingIndex m b.1) q

def realTransposeDot {k : ℕ} (x y : Fin k → ℝ) : ℝ :=
  ∑ p : Fin k, x p * y p

def realTransposeBilinear {k : ℕ} (x : Fin k → ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) (y : Fin k → ℝ) : ℝ :=
  ∑ p : Fin k, ∑ q : Fin k, x p * M p q * y q

def complexifyRealColumns {ι : Type*} {k : ℕ}
    (A : ι → (Fin k → ℝ)) : ι → (Fin k → ℂ) :=
  fun i p ↦ A i p

theorem map_typeMatchingMonomial
    {α R S : Type*} [Fintype α] [LinearOrder α]
    [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : Matrix α α R) (M : TypePerfectMatching α) :
    f (typeMatchingMonomial A M) =
      typeMatchingMonomial (fun i j ↦ f (A i j)) M := by
  classical
  unfold typeMatchingMonomial
  rw [map_prod]

theorem map_typeHafnian
    {α R S : Type*} [Fintype α] [LinearOrder α]
    [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : Matrix α α R) :
    f (typeHafnian A) = typeHafnian (fun i j ↦ f (A i j)) := by
  classical
  unfold typeHafnian
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro M _hM
  exact map_typeMatchingMonomial f A M

theorem ofReal_realColumnTransposeGram
    {ι : Type*} [Fintype ι] {k : ℕ}
    (A : ι → (Fin k → ℝ)) (i j : ι) :
    ((realColumnTransposeGram A i j : ℝ) : ℂ) =
      columnTransposeGram (complexifyRealColumns A) i j := by
  unfold realColumnTransposeGram columnTransposeGram complexifyRealColumns
  push_cast
  rfl

theorem ofReal_finiteRealGramCofactorVector
    {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
    (A : ι → (Fin k → ℝ)) (j : ι) :
    ((finiteRealGramCofactorVector A j : ℝ) : ℂ) =
      finiteGramCofactorVector (complexifyRealColumns A) j := by
  unfold finiteRealGramCofactorVector finiteGramCofactorVector
  rw [show ((typeHafnian
      (realColumnTransposeGram (fun i : {i : ι // i ≠ j} ↦ A i.1)) : ℝ) : ℂ) =
      typeHafnian (fun i l ↦
        ((realColumnTransposeGram
          (fun i : {i : ι // i ≠ j} ↦ A i.1) i l : ℝ) : ℂ)) by
    exact map_typeHafnian Complex.ofRealHom _]
  congr 1
  funext i l
  exact ofReal_realColumnTransposeGram
    (fun i : {i : ι // i ≠ j} ↦ A i.1) i l

theorem ofReal_realRemainingHafnianDeleteOne
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k) (a : Fin m) :
    ((realRemainingHafnianDeleteOne A a : ℝ) : ℂ) =
      remainingHafnianDeleteOne (complexifyRealColumns A) a := by
  unfold realRemainingHafnianDeleteOne remainingHafnianDeleteOne
  rw [show ((typeHafnian
      (realColumnTransposeGram
        (fun i : {i : Fin m // i ≠ a} ↦ A (remainingIndex m i.1))) : ℝ) : ℂ) =
      typeHafnian (fun i l ↦
        ((realColumnTransposeGram
          (fun i : {i : Fin m // i ≠ a} ↦ A (remainingIndex m i.1))
            i l : ℝ) : ℂ)) by
    exact map_typeHafnian Complex.ofRealHom _]
  congr 1
  funext i l
  exact ofReal_realColumnTransposeGram
    (fun i : {i : Fin m // i ≠ a} ↦ A (remainingIndex m i.1)) i l

theorem ofReal_realRemainingHafnianDeleteThree
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k) (j a b : Fin m) :
    ((realRemainingHafnianDeleteThree A j a b : ℝ) : ℂ) =
      remainingHafnianDeleteThree (complexifyRealColumns A) j a b := by
  unfold realRemainingHafnianDeleteThree remainingHafnianDeleteThree
  rw [show ((typeHafnian
      (realColumnTransposeGram
        (fun i : {i : Fin m // i ≠ j ∧ i ≠ a ∧ i ≠ b} ↦
          A (remainingIndex m i.1))) : ℝ) : ℂ) =
      typeHafnian (fun i l ↦
        ((realColumnTransposeGram
          (fun i : {i : Fin m // i ≠ j ∧ i ≠ a ∧ i ≠ b} ↦
            A (remainingIndex m i.1)) i l : ℝ) : ℂ)) by
    exact map_typeHafnian Complex.ofRealHom _]
  congr 1
  funext i l
  exact ofReal_realColumnTransposeGram
    (fun i : {i : Fin m // i ≠ j ∧ i ≠ a ∧ i ≠ b} ↦
      A (remainingIndex m i.1)) i l

theorem ofReal_realCofactorQ
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k) (p : Fin k) :
    ((realCofactorQ A p : ℝ) : ℂ) =
      cofactorQ (complexifyRealColumns A) p := by
  unfold realCofactorQ cofactorQ complexifyRealColumns
  push_cast
  apply Finset.sum_congr rfl
  intro a _ha
  have h := ofReal_realRemainingHafnianDeleteOne A a
  change ((realRemainingHafnianDeleteOne A a : ℝ) : ℂ) =
    remainingHafnianDeleteOne (fun i p ↦ (A i p : ℂ)) a at h
  rw [h]

theorem ofReal_realCofactorM
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k)
    (j : Fin m) (p q : Fin k) :
    ((realCofactorM A j p q : ℝ) : ℂ) =
      cofactorM (complexifyRealColumns A) j p q := by
  unfold realCofactorM cofactorM complexifyRealColumns
  push_cast
  congr 1
  · split_ifs
    · have h := ofReal_realRemainingHafnianDeleteOne A j
      change ((realRemainingHafnianDeleteOne A j : ℝ) : ℂ) =
        remainingHafnianDeleteOne (fun i p ↦ (A i p : ℂ)) j at h
      exact h
    · simp
  · apply Finset.sum_congr rfl
    intro b _hb
    apply Finset.sum_congr rfl
    intro a _ha
    have h := ofReal_realRemainingHafnianDeleteThree A j a.1 b.1
    change ((realRemainingHafnianDeleteThree A j a.1 b.1 : ℝ) : ℂ) =
      remainingHafnianDeleteThree (fun i p ↦ (A i p : ℂ))
        j a.1 b.1 at h
    rw [h]

theorem ofReal_realTransposeDot
    {k : ℕ} (x y : Fin k → ℝ) :
    ((realTransposeDot x y : ℝ) : ℂ) =
      transposeDot (fun p ↦ (x p : ℂ)) (fun p ↦ (y p : ℂ)) := by
  unfold realTransposeDot transposeDot
  push_cast
  rfl

theorem ofReal_realTransposeBilinear
    {k : ℕ} (x : Fin k → ℝ) (M : Matrix (Fin k) (Fin k) ℝ)
    (y : Fin k → ℝ) :
    ((realTransposeBilinear x M y : ℝ) : ℂ) =
      transposeBilinear (fun p ↦ (x p : ℂ))
        (fun p q ↦ (M p q : ℂ)) (fun p ↦ (y p : ℂ)) := by
  unfold realTransposeBilinear transposeBilinear
  push_cast
  rfl

theorem finiteRealGramCofactor_X_eq_realTransposeDot_Y_q
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k) :
    finiteRealGramCofactorVector A (exposedXIndex m) =
      realTransposeDot (A (exposedYIndex m)) (realCofactorQ A) := by
  apply Complex.ofReal_injective
  rw [ofReal_finiteRealGramCofactorVector, ofReal_realTransposeDot]
  simp_rw [ofReal_realCofactorQ]
  have h := twoExposedCofactor_X_eq_transposeDot_Y_q
    (complexifyRealColumns A)
  change finiteGramCofactorVector (complexifyRealColumns A)
      (exposedXIndex m) =
    transposeDot (complexifyRealColumns A (exposedYIndex m))
      (cofactorQ (complexifyRealColumns A))
  simpa only [twoExposedCofactorVector] using h

theorem finiteRealGramCofactor_Y_eq_realTransposeDot_X_q
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k) :
    finiteRealGramCofactorVector A (exposedYIndex m) =
      realTransposeDot (A (exposedXIndex m)) (realCofactorQ A) := by
  apply Complex.ofReal_injective
  rw [ofReal_finiteRealGramCofactorVector, ofReal_realTransposeDot]
  simp_rw [ofReal_realCofactorQ]
  have h := twoExposedCofactor_Y_eq_transposeDot_X_q
    (complexifyRealColumns A)
  change finiteGramCofactorVector (complexifyRealColumns A)
      (exposedYIndex m) =
    transposeDot (complexifyRealColumns A (exposedXIndex m))
      (cofactorQ (complexifyRealColumns A))
  simpa only [twoExposedCofactorVector] using h

theorem finiteRealGramCofactor_background_eq_realTransposeBilinear_X_M_Y
    {m k : ℕ} (A : RealTwoExposedColumnFamily m k) (j : Fin m) :
    finiteRealGramCofactorVector A (remainingIndex m j) =
      realTransposeBilinear (A (exposedXIndex m)) (realCofactorM A j)
        (A (exposedYIndex m)) := by
  apply Complex.ofReal_injective
  rw [ofReal_finiteRealGramCofactorVector, ofReal_realTransposeBilinear]
  simp_rw [ofReal_realCofactorM]
  have h := twoExposedCofactor_background_eq_transposeBilinear_X_M_Y
    (complexifyRealColumns A) j
  change finiteGramCofactorVector (complexifyRealColumns A)
      (remainingIndex m j) =
    transposeBilinear (complexifyRealColumns A (exposedXIndex m))
      (cofactorM (complexifyRealColumns A) j)
      (complexifyRealColumns A (exposedYIndex m))
  simpa only [twoExposedCofactorVector] using h

end

end LogdetLean.GramHafnian
