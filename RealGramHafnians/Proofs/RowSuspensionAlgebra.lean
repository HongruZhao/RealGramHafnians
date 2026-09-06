import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLocalCofactorCompression
/-!
# Algebraic model for row-suspension compression

The top coordinate of every column is deterministic and the remaining
coordinates are iid real Gaussians.  The Fourier weight equals that same
top-coordinate vector.  This is the self-coupling whose singleton endpoint
deletes all collisions in the displayed physical row.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

def prependRealCoordinate {k : ℕ} (x : ℝ) (X : Fin k → ℝ) :
    Fin (k + 1) → ℝ :=
  Fin.cases x X

@[simp] theorem prependRealCoordinate_zero {k : ℕ} (x : ℝ)
    (X : Fin k → ℝ) :
    prependRealCoordinate x X 0 = x := by
  rfl

@[simp] theorem prependRealCoordinate_succ {k : ℕ} (x : ℝ)
    (X : Fin k → ℝ) (i : Fin k) :
    prependRealCoordinate x X i.succ = X i := by
  rfl

def rowSuspensionColumns {d k : ℕ} (z : Fin d → ℝ)
    (B : Fin d → (Fin k → ℝ)) : Fin d → (Fin (k + 1) → ℝ) :=
  fun i => prependRealCoordinate (z i) (B i)

def rowSuspensionPhase {d k : ℕ} (z : Fin d → ℝ)
    (B : Fin d → (Fin k → ℝ)) : ℝ :=
  finiteRealGramCofactorPhase (rowSuspensionColumns z B) z

def rowSuspensionPhaseCharacter {d k : ℕ} (t : ℝ)
    (z : Fin d → ℝ) (B : Fin d → (Fin k → ℝ)) : ℂ :=
  Complex.exp (((t * rowSuspensionPhase z B : ℝ) : ℂ) * Complex.I)

def rowSuspensionCharacteristic (d k : ℕ) (t : ℝ) :
    (Fin d → ℝ) → ℂ :=
  fun z => ∫ B : Fin d → (Fin k → ℝ),
    rowSuspensionPhaseCharacter t z B
      ∂(Measure.pi fun _ : Fin d => standardRealGaussianVectorMeasure k)

@[fun_prop] theorem continuous_rowSuspensionColumns
    {d k : ℕ} (z : Fin d → ℝ) :
    Continuous (rowSuspensionColumns (k := k) z) := by
  unfold rowSuspensionColumns prependRealCoordinate
  apply continuous_pi
  intro i
  apply continuous_pi
  intro p
  refine Fin.cases ?_ (fun j => ?_) p
  · exact continuous_const
  · exact (continuous_apply j).comp (continuous_apply i)

theorem rowSuspensionPhaseCharacter_eq
    {d k : ℕ} (t : ℝ) (z : Fin d → ℝ)
    (B : Fin d → (Fin k → ℝ)) :
    rowSuspensionPhaseCharacter t z B =
      finiteRealGramCofactorPhaseCharacter (fun i => t * z i)
        (rowSuspensionColumns z B) := by
  unfold rowSuspensionPhaseCharacter rowSuspensionPhase
    finiteRealGramCofactorPhaseCharacter finiteRealGramCofactorPhase
  congr 2
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

@[fun_prop] theorem measurable_rowSuspensionPhaseCharacter
    {d k : ℕ} (t : ℝ) (z : Fin d → ℝ) :
    Measurable (rowSuspensionPhaseCharacter (k := k) t z) := by
  have h := (measurable_finiteRealGramCofactorPhaseCharacter
    (k := k + 1) (fun i => t * z i)).comp
      (continuous_rowSuspensionColumns z).measurable
  convert h using 1
  funext B
  exact rowSuspensionPhaseCharacter_eq t z B

theorem norm_rowSuspensionPhaseCharacter
    {d k : ℕ} (t : ℝ) (z : Fin d → ℝ)
    (B : Fin d → (Fin k → ℝ)) :
    ‖rowSuspensionPhaseCharacter t z B‖ = 1 := by
  unfold rowSuspensionPhaseCharacter
  rw [Complex.norm_exp]
  simp

end

end LogdetLean.GramHafnian
