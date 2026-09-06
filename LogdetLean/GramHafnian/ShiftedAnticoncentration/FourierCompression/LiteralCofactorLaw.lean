import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseLiteral
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.SingletonCofactorCharacteristic
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CompressionToInverseMoment
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorInverseMomentAssembly
import Mathlib.Data.Complex.BigOperators
/-!
# The literal odd-cofactor law on finite Euclidean coordinates

This file is the law/reindexing bridge between the abstract finite-coordinate
Fourier-compression theorem and the literal odd hafnian-cofactor random
variables.  Complex conjugation is inserted in the Euclidean realization so
that the real Hilbert pairing is exactly `Re sum w_j C_j`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ENNReal Real

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 1600000

/-- The canonical enumeration of the indices strictly before the exposed
last column. -/
def finOddCofactorEquiv (r : ℕ) (hr : 1 ≤ r) :
    Fin (2 * r - 1) ≃ OddCofactorIndex r hr :=
  Equiv.ofBijective
    (fun i ↦
      (⟨⟨i.1, by
          have hi := i.2
          omega⟩, by
        intro h
        have hv := congrArg Fin.val h
        change i.1 = 2 * r - 1 at hv
        omega⟩ : OddCofactorIndex r hr))
    ⟨by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun x ↦ x.1.1) hij,
    by
      intro j
      have hjlt := lt_evenLastIndex hr j.1 j.2
      refine ⟨⟨j.1.1, ?_⟩, ?_⟩
      · change j.1.1 < 2 * r - 1
        exact Fin.lt_iff_val_lt_val.mp hjlt
      · apply Subtype.ext
        apply Fin.ext
        rfl⟩

/-- The literal odd cofactor vector, conjugated and enumerated by
`Fin (2r-1)`, as a complex Euclidean vector. -/
def pastConjugateCofactorEuclidean
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    CircularEuclideanSpace (2 * r - 1) :=
  WithLp.toLp 2 (fun i ↦
    star (pastHafnianCofactorVector hr A (finOddCofactorEquiv r hr i)))

@[fun_prop]
theorem measurable_pastConjugateCofactorEuclidean
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (pastConjugateCofactorEuclidean (k := k) hr) := by
  unfold pastConjugateCofactorEuclidean
  apply (WithLp.measurable_toLp 2
    (Fin (2 * r - 1) → ℂ)).comp
  rw [measurable_pi_iff]
  intro i
  exact Complex.continuous_conj.measurable.comp
    ((measurable_pi_apply (finOddCofactorEquiv r hr i)).comp
      (measurable_pastHafnianCofactorVector hr))

/-- Pushforward law of the Euclidean cofactor vector. -/
def pastConjugateCofactorEuclideanLaw
    (r k : ℕ) (hr : 1 ≤ r) :
    Measure (CircularEuclideanSpace (2 * r - 1)) :=
  Measure.map (pastConjugateCofactorEuclidean (k := k) hr)
    (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)

instance pastConjugateCofactorEuclideanLaw_isProbabilityMeasure
    (r k : ℕ) (hr : 1 ≤ r) :
    IsProbabilityMeasure (pastConjugateCofactorEuclideanLaw r k hr) := by
  unfold pastConjugateCofactorEuclideanLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_pastConjugateCofactorEuclidean hr).aemeasurable

/-- The Euclidean squared norm is literally the cofactor energy `W_r`. -/
theorem norm_sq_pastConjugateCofactorEuclidean
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    ‖pastConjugateCofactorEuclidean hr A‖ ^ 2 = pastCofactorW hr A := by
  rw [EuclideanSpace.norm_sq_eq, pastCofactorW_eq_sum_normSq]
  unfold pastConjugateCofactorEuclidean
  simp only [PiLp.toLp_apply, Complex.normSq_eq_norm_sq,
    norm_star]
  exact Fintype.sum_equiv (finOddCofactorEquiv r hr)
    (fun i ↦ ‖pastHafnianCofactorVector hr A
      (finOddCofactorEquiv r hr i)‖ ^ 2)
    (fun j ↦ ‖pastHafnianCofactorVector hr A j‖ ^ 2)
    (fun _ ↦ rfl)

/-- The odd characteristic function written on the canonical `Fin`
enumeration. -/
def oddCofactorRawCharacteristic
    {r k : ℕ} (hr : 1 ≤ r) :
    (Fin (2 * r - 1) → ℂ) → ℂ :=
  fun w ↦ oddHafnianCofactorCharacteristic (k := k) hr
    (fun j ↦ w ((finOddCofactorEquiv r hr).symm j))

/-- The Euclidean pushforward has exactly the raw odd-cofactor
characteristic function. -/
theorem oddCofactorRawCharacteristic_eq_charFun
    {r k : ℕ} (hr : 1 ≤ r)
    (xi : CircularEuclideanSpace (2 * r - 1)) :
    oddCofactorRawCharacteristic (k := k) hr (fun i ↦ xi i) =
      charFun (pastConjugateCofactorEuclideanLaw r k hr) xi := by
  unfold oddCofactorRawCharacteristic oddHafnianCofactorCharacteristic
    pastConjugateCofactorEuclideanLaw charFun
  rw [integral_map
    (measurable_pastConjugateCofactorEuclidean hr).aemeasurable
    (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with A
  congr 2
  norm_cast
  rw [PiLp.inner_apply]
  unfold pastConjugateCofactorEuclidean
  simp only [PiLp.toLp_apply, Complex.inner, starRingEnd_apply,
    star_star]
  change
    (∑ j : OddCofactorIndex r hr,
      xi ((finOddCofactorEquiv r hr).symm j) *
        pastHafnianCofactorVector hr A j).re =
      ∑ i : Fin (2 * r - 1),
        (xi i * pastHafnianCofactorVector hr A
          (finOddCofactorEquiv r hr i)).re
  rw [Complex.re_sum]
  exact Fintype.sum_equiv (finOddCofactorEquiv r hr).symm
    (fun j ↦ (xi ((finOddCofactorEquiv r hr).symm j) *
      pastHafnianCofactorVector hr A j).re)
    (fun i ↦ (xi i * pastHafnianCofactorVector hr A
      (finOddCofactorEquiv r hr i)).re)
    (fun _ ↦ by simp)

end

end LogdetLean.GramHafnian
