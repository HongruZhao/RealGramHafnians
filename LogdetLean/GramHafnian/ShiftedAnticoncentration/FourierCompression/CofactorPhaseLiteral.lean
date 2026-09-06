import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseLaw
import LogdetLean.GramHafnian.ShiftedAnticoncentration.LastColumnProduct
/-!
# Literal odd-cofactor bridges

This file identifies the abstract finite cofactor vector used by Fourier
compression with the literal `ComplexColumnMatrix` odd cofactor vector.  It
also singles out a canonical coordinate: deleting the first and last columns
gives exactly a level-`r-1` Gram hafnian, and that deleted-column submatrix has
the exact iid circular Gaussian marginal law.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- Deleting `j` after first passing to the non-final columns is the same
ordered finite type as deleting the pair `(last,j)` in the full column set. -/
def oddDeleteOrderIsoPairComplement
    (r : ℕ) (hr : 1 ≤ r) (j : OddCofactorIndex r hr) :
    {i : OddCofactorIndex r hr // i ≠ j} ≃o
      TypePerfectMatching.PairComplement (evenLastIndex r hr) j.1 where
  toFun i := ⟨i.1.1, i.1.2, by
    intro h
    apply i.2
    apply Subtype.ext
    exact h⟩
  invFun u := ⟨⟨u.1, u.2.1⟩, by
    intro h
    apply u.2.2
    exact congrArg Subtype.val h⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    rfl
  map_rel_iff' := by intro i l; rfl

/-- Pointwise identification of the literal odd cofactor with the abstract
finite Gram-cofactor vector on the non-final columns. -/
theorem oddHafnianCofactorVector_eq_finiteGramCofactorVector
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k)
    (j : OddCofactorIndex r hr) :
    oddHafnianCofactorVector hr X j =
      finiteGramCofactorVector (fun i : OddCofactorIndex r hr ↦ X i.1) j := by
  unfold oddHafnianCofactorVector hafnianPairCofactor
    finiteGramCofactorVector
  let e := oddDeleteOrderIsoPairComplement r hr j
  rw [← typeHafnian_reindex_orderIso e
    (fun i l : TypePerfectMatching.PairComplement
      (evenLastIndex r hr) j.1 ↦
      transposeGram (rowMatrix X) i.1 l.1)]
  rfl

/-- On the canonical past representative, the literal odd cofactor vector is
literally the abstract finite Gram-cofactor vector of the iid past family. -/
theorem oddHafnianCofactorVector_pastCofactorMatrix
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (j : OddCofactorIndex r hr) :
    oddHafnianCofactorVector hr (pastCofactorMatrix hr A) j =
      finiteGramCofactorVector A j := by
  rw [oddHafnianCofactorVector_eq_finiteGramCofactorVector]
  apply congrArg (fun B ↦ finiteGramCofactorVector B j)
  funext i p
  exact congrArg (fun f ↦ f p)
    (lastColumnProductEquiv_apply_nonlast hr (A, 0) i)

/-- Fourier characteristic functional of the literal odd cofactor vector,
written on its exact iid non-final-column marginal. -/
def oddHafnianCofactorCharacteristic
    {r k : ℕ} (hr : 1 ≤ r) :
    (OddCofactorIndex r hr → ℂ) → ℂ :=
  fun w ↦ ∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
    Complex.exp
      ((((∑ j : OddCofactorIndex r hr,
        w j * oddHafnianCofactorVector hr
          (pastCofactorMatrix hr A) j).re : ℝ) : ℂ) * Complex.I)
      ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)

/-- The literal odd-cofactor Fourier functional is exactly the generic
finite Gram-cofactor characteristic functional used by coordinate
compression. -/
theorem oddHafnianCofactorCharacteristic_eq_finite
    {r k : ℕ} (hr : 1 ≤ r) :
    oddHafnianCofactorCharacteristic (k := k) hr =
      finiteGramCofactorCharacteristic (OddCofactorIndex r hr) k := by
  funext w
  unfold oddHafnianCofactorCharacteristic
    finiteGramCofactorCharacteristic finiteGramCofactorPhaseCharacter
    finiteGramCofactorPhase
  apply integral_congr_ae
  filter_upwards [] with A
  simp_rw [oddHafnianCofactorVector_pastCofactorMatrix]

/-- Exact `CoordinateIteration` symmetry interface for the literal odd
cofactor law at every nontrivial level `r ≥ 2`. -/
theorem oddHafnianCofactorCharacteristic_compression_symmetries
    {r k : ℕ} (hr : 1 ≤ r) (hr2 : 2 ≤ r) :
    SingletonExchangeable
        (oddHafnianCofactorCharacteristic (k := k) hr) ∧
      CommonPhaseInvariant
        (oddHafnianCofactorCharacteristic (k := k) hr) := by
  rw [oddHafnianCofactorCharacteristic_eq_finite]
  apply finiteGramCofactorCharacteristic_compression_symmetries
    (d := 2 * r - 2)
  · rw [card_oddCofactorIndex]
    omega
  · omega
  · exact ⟨r - 1, by omega⟩

/-- Canonical first coordinate of the odd cofactor vector. -/
def oddFirstCofactorIndex (r : ℕ) (hr : 1 ≤ r) :
    OddCofactorIndex r hr :=
  ⟨⟨0, by omega⟩, by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 2 * r - 1 at hv
    omega⟩

/-- The `2(r-1)`-column matrix obtained by deleting the first and last
columns of a level-`r` literal column matrix. -/
def canonicalCofactorSubmatrix
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k) :
    ComplexColumnMatrix (r - 1) k :=
  fun i p ↦ X ⟨i.1 + 1, by
    have hi := i.2
    omega⟩ p

/-- The canonical order identification between the new lower-level columns
and the complement of the deleted first/last pair. -/
def canonicalCofactorSubmatrixOrderIso
    (r : ℕ) (hr : 1 ≤ r) :
    Fin (2 * (r - 1)) ≃o
      TypePerfectMatching.PairComplement
        (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 where
  toFun i := ⟨⟨i.1 + 1, by
      have hi := i.2
      omega⟩, by
        constructor
        · intro h
          have hv := congrArg Fin.val h
          change i.1 + 1 = 2 * r - 1 at hv
          have hi := i.2
          omega
        · intro h
          have hv := congrArg Fin.val h
          change i.1 + 1 = 0 at hv
          omega⟩
  invFun u := ⟨u.1.1 - 1, by
    have hpos : 0 < u.1.1 := by
      by_contra h
      have hz : u.1.1 = 0 := by omega
      apply u.2.2
      apply Fin.ext
      exact hz
    have hlast : u.1.1 ≠ 2 * r - 1 := by
      intro h
      apply u.2.1
      apply Fin.ext
      exact h
    have hub := u.1.2
    omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv u := by
    apply Subtype.ext
    apply Fin.ext
    have hpos : 0 < u.1.1 := by
      by_contra h
      have hz : u.1.1 = 0 := by omega
      apply u.2.2
      apply Fin.ext
      exact hz
    change (u.1.1 - 1) + 1 = u.1.1
    omega
  map_rel_iff' := by
    intro i l
    change i.1 + 1 ≤ l.1 + 1 ↔ i.1 ≤ l.1
    omega

/-- A canonical odd cofactor coordinate at level `r` is exactly the literal
Gram hafnian of the `2(r-1)`-column submatrix obtained by deleting first and
last columns. -/
theorem oddFirstCofactor_eq_gramHafnian_canonicalSubmatrix
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k) :
    oddHafnianCofactorVector hr X (oddFirstCofactorIndex r hr) =
      gramHafnian
        (rowMatrix (canonicalCofactorSubmatrix hr X)) := by
  rw [gramHafnian_eq_typeHafnian_transposeGram]
  unfold oddHafnianCofactorVector hafnianPairCofactor
  let e := canonicalCofactorSubmatrixOrderIso r hr
  rw [← typeHafnian_reindex_orderIso e
    (fun i j : TypePerfectMatching.PairComplement
      (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 ↦
      transposeGram (rowMatrix X) i.1 j.1)]
  rfl

/-- The canonical deleted-column submatrix has exactly the lower-level iid
circular Gaussian column law. -/
theorem map_canonicalCofactorSubmatrix_circularGaussianColumnMatrixMeasure
    (r k : ℕ) (hr : 1 ≤ r) :
    Measure.map (canonicalCofactorSubmatrix (k := k) hr)
        (circularGaussianColumnMatrixMeasure r k) =
      circularGaussianColumnMatrixMeasure (r - 1) k := by
  let p : Fin (2 * r) → Prop := fun i ↦
    i ≠ evenLastIndex r hr ∧ i ≠ (oddFirstCofactorIndex r hr).1
  let Col := Fin k → ℂ
  let μ : Measure Col := circularGaussianVector k
  let split := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (2 * r) ↦ Col) p
  have hsplit : MeasurePreserving split
      (Measure.pi fun _ : Fin (2 * r) ↦ μ)
      ((Measure.pi fun _ : Subtype p ↦ μ).prod
        (Measure.pi fun _ : {i : Fin (2 * r) // ¬p i} ↦ μ)) := by
    exact measurePreserving_piEquivPiSubtypeProd
      (fun _ : Fin (2 * r) ↦ μ) p
  have hfst : MeasurePreserving Prod.fst
      ((Measure.pi fun _ : Subtype p ↦ μ).prod
        (Measure.pi fun _ : {i : Fin (2 * r) // ¬p i} ↦ μ))
      (Measure.pi fun _ : Subtype p ↦ μ) :=
    measurePreserving_fst
  let e := canonicalCofactorSubmatrixOrderIso r hr
  let reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : TypePerfectMatching.PairComplement
        (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 ↦ Col)
      e.toEquiv).symm
  have hreindex : MeasurePreserving reindex
      (Measure.pi fun _ : Subtype p ↦ μ)
      (Measure.pi fun _ : Fin (2 * (r - 1)) ↦ μ) := by
    have h := (measurePreserving_piCongrLeft
      (α := fun _ : TypePerfectMatching.PairComplement
        (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 ↦ Col)
      (fun _ : TypePerfectMatching.PairComplement
        (evenLastIndex r hr) (oddFirstCofactorIndex r hr).1 ↦ μ) e.toEquiv)
    simpa [p, reindex] using h.symm
  have htotal := hreindex.comp (hfst.comp hsplit)
  change Measure.map (canonicalCofactorSubmatrix (k := k) hr)
      (Measure.pi fun _ : Fin (2 * r) ↦ μ) =
    Measure.pi fun _ : Fin (2 * (r - 1)) ↦ μ
  rw [← htotal.map_eq]
  congr 1

end

end LogdetLean.GramHafnian
