import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseLiteral
import LogdetLean.GramHafnian.ShiftedAnticoncentration.ComplexGaussianFullRank
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorPositivity
import LogdetLean.GramHafnian.ShiftedAnticoncentration.BaseInverseMoment
/-!
# Almost-sure nonvanishing and positivity of odd Gram-hafnian cofactors

The induction has two simultaneous conclusions.  A canonical coordinate of
the level-`r` odd cofactor vector is a level-`r-1` Gram hafnian, so
nonvanishing at the preceding level makes the cofactor vector nonzero almost
surely.  Almost-sure complex full rank of the `2r-1` past columns then makes
the cofactor energy strictly positive.  Finally, the fresh last circular
Gaussian column makes the level-`r` Gram hafnian nonzero almost surely.
-/

open MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian

noncomputable section

/-- The odd cofactor column combination, hence also its squared norm, only
depends on the non-final columns. -/
theorem oddCofactorColumnCombination_congr_off_last
    {r k : ℕ} (hr : 1 ≤ r) {X Y : ComplexColumnMatrix r k}
    (hXY : ∀ i : Fin (2 * r), i ≠ evenLastIndex r hr → X i = Y i) :
    oddCofactorColumnCombination hr X =
      oddCofactorColumnCombination hr Y := by
  funext a
  unfold oddCofactorColumnCombination
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hXY j.1 j.2,
    oddHafnianCofactorVector_congr_off_last hr hXY j]

/-- The literal cofactor energy is unchanged when only the exposed final
column is changed. -/
theorem oddCofactorV_congr_off_last
    {r k : ℕ} (hr : 1 ≤ r) {X Y : ComplexColumnMatrix r k}
    (hXY : ∀ i : Fin (2 * r), i ≠ evenLastIndex r hr → X i = Y i) :
    oddCofactorV hr X = oddCofactorV hr Y := by
  unfold oddCofactorV
  rw [oddCofactorColumnCombination_congr_off_last hr hXY]

/-- Under the exact last-column product decomposition, the literal full
matrix cofactor energy is exactly the energy of the past family. -/
theorem oddCofactorV_lastColumnProductEquiv_eq_pastCofactorV
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) :
    oddCofactorV hr (lastColumnProductEquiv r k hr p) =
      pastCofactorV hr p.1 := by
  unfold pastCofactorV pastCofactorMatrix
  apply oddCofactorV_congr_off_last hr
  intro i hi
  rw [lastColumnProductEquiv_apply_nonlast hr p ⟨i, hi⟩,
    lastColumnProductEquiv_apply_nonlast hr (p.1, 0) ⟨i, hi⟩]

/-- The `2r-1` non-final columns of the literal iid matrix are complex
linearly independent almost surely whenever `2r-1 ≤ k`. -/
theorem ae_oddPastColumns_complexLinearIndependent
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      LinearIndependent ℂ
        (fun j : OddCofactorIndex r hr ↦
          (WithLp.toLp 2 (X j.1) : CircularEuclideanSpace k)) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let μ : Measure (Fin k → ℂ) := circularGaussianVector k
  let e := lastColumnProductEquiv r k hr
  have hpast :
      ∀ᵐ A ∂ν,
        LinearIndependent ℂ
          (fun j : OddCofactorIndex r hr ↦
            (WithLp.toLp 2 (A j) : CircularEuclideanSpace k)) := by
    apply ae_complexLinearIndependent_pi_circularGaussianVectors_fintype
    simpa [card_oddCofactorIndex] using hk
  have hprod :
      ∀ᵐ p ∂ν.prod μ,
        LinearIndependent ℂ
          (fun j : OddCofactorIndex r hr ↦
            (WithLp.toLp 2 (p.1 j) : CircularEuclideanSpace k)) :=
    Measure.quasiMeasurePreserving_fst.ae hpast
  have he : MeasurePreserving e (ν.prod μ)
      (circularGaussianColumnMatrixMeasure r k) := by
    simpa [ν, μ, e] using
      measurePreserving_lastColumnProductEquiv r k hr
  have hinv : MeasurePreserving e.symm
      (circularGaussianColumnMatrixMeasure r k) (ν.prod μ) :=
    he.symm e
  have hfull :
      ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
        LinearIndependent ℂ
          (fun j : OddCofactorIndex r hr ↦
            (WithLp.toLp 2 ((e.symm X).1 j) :
              CircularEuclideanSpace k)) :=
    hinv.quasiMeasurePreserving.ae hprod
  filter_upwards [hfull] with X hX
  have hfun :
      (fun j : OddCofactorIndex r hr ↦
          (WithLp.toLp 2 ((e.symm X).1 j) :
            CircularEuclideanSpace k)) =
        (fun j : OddCofactorIndex r hr ↦
          (WithLp.toLp 2 (X j.1) : CircularEuclideanSpace k)) := by
    funext j
    congr 1
  rwa [hfun] at hX

/-- Full rank upgrades almost-sure nonvanishing of the odd cofactor vector
to almost-sure strict positivity of its energy. -/
theorem ae_oddCofactorV_pos_of_ae_cofactorVector_ne_zero
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k)
    (hC : ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      oddHafnianCofactorVector hr X ≠ 0) :
    ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      0 < oddCofactorV hr X := by
  have hLI := ae_oddPastColumns_complexLinearIndependent hr hk
  filter_upwards [hLI, hC] with X hXLI hXC
  exact oddCofactorV_pos_of_linearIndependent_of_cofactor_ne_zero
    hr X hXLI hXC

/-- Positivity of the full-matrix cofactor energy descends to the exact iid
past marginal because the energy ignores the fresh final column. -/
theorem ae_pastCofactorV_pos_of_ae_oddCofactorV_pos
    {r k : ℕ} (hr : 1 ≤ r)
    (hV : ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      0 < oddCofactorV hr X) :
    ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
        circularGaussianVector k),
      0 < pastCofactorV hr A := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let μ : Measure (Fin k → ℂ) := circularGaussianVector k
  let e := lastColumnProductEquiv r k hr
  have he : MeasurePreserving e (ν.prod μ)
      (circularGaussianColumnMatrixMeasure r k) := by
    simpa [ν, μ, e] using
      measurePreserving_lastColumnProductEquiv r k hr
  have hprodRaw :
      ∀ᵐ p ∂ν.prod μ, 0 < oddCofactorV hr (e p) :=
    he.quasiMeasurePreserving.ae hV
  have hprod :
      ∀ᵐ p ∂ν.prod μ, 0 < pastCofactorV hr p.1 := by
    filter_upwards [hprodRaw] with p hp
    rwa [oddCofactorV_lastColumnProductEquiv_eq_pastCofactorV] at hp
  have hsections :
      ∀ᵐ A ∂ν, ∀ᵐ _x ∂μ, 0 < pastCofactorV hr A :=
    Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hsections] with A hA
  exact Filter.eventually_const.mp hA

/-- A positive cofactor energy and the fresh circular Gaussian final column
make the literal Gram hafnian nonzero almost surely. -/
theorem ae_gramHafnian_ne_zero_of_ae_oddCofactorV_pos
    {r k : ℕ} (hr : 1 ≤ r)
    (hV : ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      0 < oddCofactorV hr X) :
    ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      gramHafnianObservable r k X ≠ 0 := by
  have hVpast := ae_pastCofactorV_pos_of_ae_oddCofactorV_pos hr hV
  have hbound :=
    circularGaussianColumnMatrix_shiftedSmallBall_le_pastInverseMoment
      hr hVpast (0 : ℂ) 0 (by norm_num)
  have hzero :
      (circularGaussianColumnMatrixMeasure r k)
          {X | ‖gramHafnianObservable r k X - 0‖ ≤ 0} = 0 := by
    apply nonpos_iff_eq_zero.mp
    simpa using hbound
  rw [ae_iff]
  simpa using hzero

/-- At level one the odd cofactor vector is deterministically nonzero: its
unique coordinate is the empty hafnian `1`. -/
theorem oddHafnianCofactorVector_ne_zero_level_one
    {k : ℕ} (X : ComplexColumnMatrix 1 k) :
    oddHafnianCofactorVector (by omega) X ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero
    (oddFirstCofactorIndex 1 (by omega))
  rw [oddHafnianCofactorVector_level_one X] at hcoord
  norm_num at hcoord

/-- A canonical odd cofactor coordinate is nonzero almost surely whenever
the lower-level Gram hafnian is nonzero almost surely. -/
theorem ae_cofactorVector_ne_zero_of_ae_lower_gramHafnian_ne_zero
    {r k : ℕ} (hr : 1 ≤ r) (_hr2 : 2 ≤ r)
    (hlower :
      ∀ᵐ Y ∂(circularGaussianColumnMatrixMeasure (r - 1) k),
        gramHafnianObservable (r - 1) k Y ≠ 0) :
    ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      oddHafnianCofactorVector hr X ≠ 0 := by
  let f : ComplexColumnMatrix r k → ComplexColumnMatrix (r - 1) k :=
    canonicalCofactorSubmatrix hr
  have hf : Measurable f := by
    unfold f canonicalCofactorSubmatrix
    fun_prop
  have hmp : MeasurePreserving f
      (circularGaussianColumnMatrixMeasure r k)
      (circularGaussianColumnMatrixMeasure (r - 1) k) := by
    refine ⟨hf, ?_⟩
    exact map_canonicalCofactorSubmatrix_circularGaussianColumnMatrixMeasure
      r k hr
  have hpull :
      ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
        gramHafnianObservable (r - 1) k (f X) ≠ 0 :=
    hmp.quasiMeasurePreserving.ae hlower
  filter_upwards [hpull] with X hX
  intro hzero
  have hcoord := congrFun hzero (oddFirstCofactorIndex r hr)
  rw [oddFirstCofactor_eq_gramHafnian_canonicalSubmatrix] at hcoord
  apply hX
  simpa [f, gramHafnianObservable] using hcoord

/-- Simultaneous induction: the odd cofactor energy is positive and the
Gram hafnian is nonzero almost surely at every admissible level. -/
theorem ae_oddCofactorV_pos_and_gramHafnian_ne_zero
    (k : ℕ) :
    ∀ r : ℕ, ∀ hr : 1 ≤ r, 2 * r - 1 ≤ k →
      (∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
          0 < oddCofactorV hr X) ∧
        (∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
          gramHafnianObservable r k X ≠ 0) := by
  intro r
  induction r with
  | zero =>
      intro hr
      omega
  | succ n ih =>
      intro hr hk
      by_cases hn : n = 0
      · subst n
        have hC :
            ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure 1 k),
              oddHafnianCofactorVector hr X ≠ 0 :=
          Filter.Eventually.of_forall fun X ↦
            oddHafnianCofactorVector_ne_zero_level_one X
        have hV :=
          ae_oddCofactorV_pos_of_ae_cofactorVector_ne_zero hr hk hC
        exact ⟨hV,
          ae_gramHafnian_ne_zero_of_ae_oddCofactorV_pos hr hV⟩
      · have hnpos : 1 ≤ n := by omega
        have hnk : 2 * n - 1 ≤ k := by omega
        have hprev := ih hnpos hnk
        have hC :
            ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure (n + 1) k),
              oddHafnianCofactorVector hr X ≠ 0 := by
          apply ae_cofactorVector_ne_zero_of_ae_lower_gramHafnian_ne_zero
            hr (by omega)
          simpa using hprev.2
        have hV :=
          ae_oddCofactorV_pos_of_ae_cofactorVector_ne_zero hr hk hC
        exact ⟨hV,
          ae_gramHafnian_ne_zero_of_ae_oddCofactorV_pos hr hV⟩

/-- Public positivity endpoint for the literal odd cofactor energy. -/
theorem ae_oddCofactorV_pos_circularGaussianColumnMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      0 < oddCofactorV hr X :=
  (ae_oddCofactorV_pos_and_gramHafnian_ne_zero k r hr hk).1

/-- Public nonvanishing endpoint for the literal Gaussian Gram hafnian. -/
theorem ae_gramHafnian_ne_zero_circularGaussianColumnMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k) :
    ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure r k),
      gramHafnianObservable r k X ≠ 0 :=
  (ae_oddCofactorV_pos_and_gramHafnian_ne_zero k r hr hk).2

end

end LogdetLean.GramHafnian
