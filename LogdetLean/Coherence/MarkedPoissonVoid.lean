import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ConditionalProbability
/-!
# A finite marked Poisson--void Stein decomposition

This file isolates the deterministic and measure-theoretic lemma needed for
quantitative joint approximation of a mark and a rare-event void event.

For finitely many Bernoulli events `A i`, write

* `W` for their total count;
* `p i = P(A i)` and `lambda = sum_i p i`;
* `B i` for a local neighborhood of event `i`;
* `WOutside i` for the count outside `B i`;
* `h` for the tested mark and `hLeave i` for a leave-one/localized version.

The Poisson Stein equation for the void test is solved exactly.  Substitution
then splits the marked error into five explicit channels: forward mark
replacement, forward count replacement, far-field dependence, backward count
replacement, and backward mark replacement.  The final theorem bounds

`|E[h 1_{W=0}] - E[h] exp(-lambda)|`

by the sum of the absolute expectations of those local errors.  No
independence assumption is built into the lemma; a model adapter proves that
the five displayed terms are small.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Real-valued indicator of the void state. -/
def markedVoidIndicator (w : ℕ) : ℝ :=
  if w = 0 then 1 else 0

/-- Recursive solution of the Poisson Stein equation for the test
`1_{w=0}`.  The value at zero is immaterial to the Stein operator and is fixed
to zero. -/
def poissonVoidStein (lambda : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      ((n : ℝ) * poissonVoidStein lambda n + markedVoidIndicator n -
          Real.exp (-lambda)) / lambda

@[simp]
theorem poissonVoidStein_zero (lambda : ℝ) :
    poissonVoidStein lambda 0 = 0 :=
  rfl

theorem poissonVoidStein_succ (lambda : ℝ) (n : ℕ) :
    poissonVoidStein lambda (n + 1) =
      ((n : ℝ) * poissonVoidStein lambda n + markedVoidIndicator n -
          Real.exp (-lambda)) / lambda :=
  rfl

/-- Exact Poisson void Stein equation. -/
theorem poissonVoidStein_equation
    {lambda : ℝ} (hlambda : lambda ≠ 0) (w : ℕ) :
    lambda * poissonVoidStein lambda (w + 1) -
        (w : ℝ) * poissonVoidStein lambda w =
      markedVoidIndicator w - Real.exp (-lambda) := by
  rw [poissonVoidStein_succ]
  field_simp
  ring

/-- Natural-valued indicator of a Bernoulli event. -/
def bernoulliEventIndicator {Omega : Type*} (A : Set Omega) (omega : Omega) : ℕ := by
  classical
  exact if omega ∈ A then 1 else 0

@[simp]
theorem bernoulliEventIndicator_of_mem
    {Omega : Type*} {A : Set Omega} {omega : Omega} (homega : omega ∈ A) :
    bernoulliEventIndicator A omega = 1 := by
  classical
  simp [bernoulliEventIndicator, homega]

@[simp]
theorem bernoulliEventIndicator_of_not_mem
    {Omega : Type*} {A : Set Omega} {omega : Omega} (homega : omega ∉ A) :
    bernoulliEventIndicator A omega = 0 := by
  classical
  simp [bernoulliEventIndicator, homega]

theorem bernoulliEventIndicator_eq_zero_or_one
    {Omega : Type*} (A : Set Omega) (omega : Omega) :
    bernoulliEventIndicator A omega = 0 ∨
      bernoulliEventIndicator A omega = 1 := by
  classical
  by_cases homega : omega ∈ A
  · exact Or.inr (bernoulliEventIndicator_of_mem homega)
  · exact Or.inl (bernoulliEventIndicator_of_not_mem homega)

/-- Total number of active events. -/
def markedBernoulliCount
    {I Omega : Type*} [Fintype I]
    (A : I → Set Omega) (omega : Omega) : ℕ :=
  ∑ i, bernoulliEventIndicator (A i) omega

/-- Sum of the individual event probabilities. -/
def markedBernoulliIntensity
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) : ℝ :=
  ∑ i, mu.real (A i)

/-- Count outside the prescribed local neighborhood `B i`. -/
def markedOutsideNeighborhoodCount
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega) : ℕ :=
  ∑ j, if j ∈ B i then 0 else bernoulliEventIndicator (A j) omega

/-- Count inside the prescribed local neighborhood `B i`. -/
def markedNeighborhoodCount
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega) : ℕ :=
  ∑ j, if j ∈ B i then bernoulliEventIndicator (A j) omega else 0

/-- The outside and inside counts partition the full event count. -/
theorem markedOutside_add_neighborhood_eq_count
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Omega) (B : I → Finset I) (i : I) (omega : Omega) :
    markedOutsideNeighborhoodCount A B i omega +
        markedNeighborhoodCount A B i omega =
      markedBernoulliCount A omega := by
  classical
  unfold markedOutsideNeighborhoodCount markedNeighborhoodCount
    markedBernoulliCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hji : j ∈ B i <;> simp [hji]

/-- Measurability of one Bernoulli indicator. -/
theorem measurable_bernoulliEventIndicator
    {Omega : Type*} [MeasurableSpace Omega]
    {A : Set Omega} (hA : MeasurableSet A) :
    Measurable (bernoulliEventIndicator A) := by
  classical
  exact Measurable.ite hA measurable_const measurable_const

/-- Measurability of the finite event count. -/
theorem measurable_markedBernoulliCount
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (markedBernoulliCount A) := by
  unfold markedBernoulliCount
  exact Finset.measurable_sum Finset.univ fun i _hi ↦
    measurable_bernoulliEventIndicator (hA i)

/-- Measurability of the real void indicator of the finite count. -/
theorem measurable_markedVoidIndicator_count
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    {A : I → Set Omega} (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (fun omega ↦ markedVoidIndicator (markedBernoulliCount A omega)) := by
  unfold markedVoidIndicator
  apply Measurable.ite
  · exact (measurable_markedBernoulliCount hA) (measurableSet_singleton 0)
  · exact measurable_const
  · exact measurable_const

/-- Multiplying an integrable mark by the bounded void indicator preserves
integrability. -/
theorem integrable_markedVoidIndicator_mul
    {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
    {mu : Measure Omega} {A : I → Set Omega} {h : Omega → ℝ}
    (hA : ∀ i, MeasurableSet (A i)) (hh : Integrable h mu) :
    Integrable
      (fun omega ↦ h omega * markedVoidIndicator (markedBernoulliCount A omega))
      mu := by
  have hmeas : AEStronglyMeasurable
      (fun omega ↦ markedVoidIndicator (markedBernoulliCount A omega)) mu :=
    (measurable_markedVoidIndicator_count hA).aestronglyMeasurable
  have hbound : ∀ᵐ omega ∂mu,
      ‖markedVoidIndicator (markedBernoulliCount A omega)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with omega
    unfold markedVoidIndicator
    split <;> simp
  simpa [mul_comm] using hh.bdd_mul hmeas hbound

/-- The five-channel local marked Stein error.  This algebraic kernel is
stated for arbitrary counts; the Bernoulli-event theorem below supplies the
specific total and outside-neighborhood counts. -/
def markedPoissonVoidLocalError
    {I Omega : Type*}
    (f : ℕ → ℝ) (p : I → ℝ) (xi : I → Omega → ℕ)
    (W : Omega → ℕ) (WLeave : I → Omega → ℕ)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (i : I) (omega : Omega) : ℝ :=
  p i * (h omega - hLeave i omega) * f (W omega + 1) +
  p i * hLeave i omega * (f (W omega + 1) - f (WLeave i omega + 1)) +
  (p i - (xi i omega : ℝ)) * hLeave i omega * f (WLeave i omega + 1) +
  (xi i omega : ℝ) * hLeave i omega *
    (f (WLeave i omega + 1) - f (W omega)) +
  (xi i omega : ℝ) * (hLeave i omega - h omega) * f (W omega)

/-- The five local channels telescope to the one-index Stein summand. -/
theorem markedPoissonVoidLocalError_eq
    {I Omega : Type*}
    (f : ℕ → ℝ) (p : I → ℝ) (xi : I → Omega → ℕ)
    (W : Omega → ℕ) (WLeave : I → Omega → ℕ)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (i : I) (omega : Omega) :
    markedPoissonVoidLocalError f p xi W WLeave h hLeave i omega =
      p i * h omega * f (W omega + 1) -
        (xi i omega : ℝ) * h omega * f (W omega) := by
  unfold markedPoissonVoidLocalError
  ring

/-- Summing the local errors gives the marked Poisson Stein operator whenever
`W` is the sum of the elementary counts `xi i`. -/
theorem sum_markedPoissonVoidLocalError_eq
    {I Omega : Type*} [Fintype I]
    (f : ℕ → ℝ) (p : I → ℝ) (xi : I → Omega → ℕ)
    (W : Omega → ℕ) (WLeave : I → Omega → ℕ)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hW : ∀ omega, W omega = ∑ i, xi i omega) (omega : Omega) :
    ∑ i, markedPoissonVoidLocalError f p xi W WLeave h hLeave i omega =
      h omega *
        ((∑ i, p i) * f (W omega + 1) -
          (W omega : ℝ) * f (W omega)) := by
  classical
  simp_rw [markedPoissonVoidLocalError_eq]
  rw [Finset.sum_sub_distrib]
  have hxi : (W omega : ℝ) = ∑ i, (xi i omega : ℝ) := by
    rw [hW]
    simp
  calc
    (∑ i, p i * h omega * f (W omega + 1)) -
          ∑ i, (xi i omega : ℝ) * h omega * f (W omega) =
        ((∑ i, p i) * h omega * f (W omega + 1)) -
          (∑ i, (xi i omega : ℝ)) * h omega * f (W omega) := by
            rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
              Finset.sum_mul]
    _ = h omega *
        ((∑ i, p i) * f (W omega + 1) -
          (W omega : ℝ) * f (W omega)) := by
            rw [hxi]
            ring

/-- Event-specific five-channel local error, using probabilities, total event
count, and the count outside `B i`. -/
def markedBernoulliVoidLocalError
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (i : I) (omega : Omega) : ℝ :=
  let lambda := markedBernoulliIntensity mu A
  markedPoissonVoidLocalError
    (poissonVoidStein lambda)
    (fun j ↦ mu.real (A j))
    (fun j ↦ bernoulliEventIndicator (A j))
    (markedBernoulliCount A)
    (markedOutsideNeighborhoodCount A B)
    h hLeave i omega

/-- Pointwise Bernoulli-event form of the marked void Stein decomposition. -/
theorem sum_markedBernoulliVoidLocalError_eq
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hlambda : markedBernoulliIntensity mu A ≠ 0) (omega : Omega) :
    ∑ i, markedBernoulliVoidLocalError mu A B h hLeave i omega =
      h omega *
        (markedVoidIndicator (markedBernoulliCount A omega) -
          Real.exp (-markedBernoulliIntensity mu A)) := by
  classical
  let lambda := markedBernoulliIntensity mu A
  have hsum := sum_markedPoissonVoidLocalError_eq
    (poissonVoidStein lambda)
    (fun j ↦ mu.real (A j))
    (fun j ↦ bernoulliEventIndicator (A j))
    (markedBernoulliCount A)
    (markedOutsideNeighborhoodCount A B)
    h hLeave (fun _omega ↦ rfl) omega
  change (∑ i, markedPoissonVoidLocalError
      (poissonVoidStein lambda)
      (fun j ↦ mu.real (A j))
      (fun j ↦ bernoulliEventIndicator (A j))
      (markedBernoulliCount A)
      (markedOutsideNeighborhoodCount A B)
      h hLeave i omega) = _
  rw [hsum]
  change h omega *
      (lambda * poissonVoidStein lambda (markedBernoulliCount A omega + 1) -
        (markedBernoulliCount A omega : ℝ) *
          poissonVoidStein lambda (markedBernoulliCount A omega)) = _
  rw [poissonVoidStein_equation hlambda]

/-- Exact expectation decomposition.  Integrability of each local error is
kept explicit because this is the point where a concrete model supplies its
mark bounds. -/
theorem markedBernoulliVoid_expectation_decomposition
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (A : I → Set Omega) (B : I → Finset I)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hA : ∀ i, MeasurableSet (A i))
    (hlambda : markedBernoulliIntensity mu A ≠ 0)
    (hh : Integrable h mu)
    (herror : ∀ i, Integrable
      (markedBernoulliVoidLocalError mu A B h hLeave i) mu) :
    (∫ omega, h omega * markedVoidIndicator (markedBernoulliCount A omega) ∂mu) -
        (∫ omega, h omega ∂mu) *
          Real.exp (-markedBernoulliIntensity mu A) =
      ∑ i, ∫ omega, markedBernoulliVoidLocalError mu A B h hLeave i omega ∂mu := by
  have hvoid := integrable_markedVoidIndicator_mul hA hh
  have hexp : Integrable
      (fun omega ↦ h omega * Real.exp (-markedBernoulliIntensity mu A)) mu :=
    hh.mul_const _
  calc
    (∫ omega, h omega * markedVoidIndicator (markedBernoulliCount A omega) ∂mu) -
          (∫ omega, h omega ∂mu) *
            Real.exp (-markedBernoulliIntensity mu A) =
        ∫ omega,
          h omega * markedVoidIndicator (markedBernoulliCount A omega) -
            h omega * Real.exp (-markedBernoulliIntensity mu A) ∂mu := by
              rw [integral_sub hvoid hexp, integral_mul_const]
    _ = ∫ omega, h omega *
        (markedVoidIndicator (markedBernoulliCount A omega) -
          Real.exp (-markedBernoulliIntensity mu A)) ∂mu := by
            apply integral_congr_ae
            filter_upwards [] with omega
            ring
    _ = ∫ omega, ∑ i,
        markedBernoulliVoidLocalError mu A B h hLeave i omega ∂mu := by
            apply integral_congr_ae
            filter_upwards [] with omega
            exact (sum_markedBernoulliVoidLocalError_eq
              mu A B h hLeave hlambda omega).symm
    _ = ∑ i, ∫ omega,
        markedBernoulliVoidLocalError mu A B h hLeave i omega ∂mu := by
            exact integral_finsetSum Finset.univ fun i _hi ↦ herror i

/-- Generic finite marked Poisson--void Stein bound. -/
theorem markedBernoulliVoid_stein_bound
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (A : I → Set Omega) (B : I → Finset I)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hA : ∀ i, MeasurableSet (A i))
    (hlambda : markedBernoulliIntensity mu A ≠ 0)
    (hh : Integrable h mu)
    (herror : ∀ i, Integrable
      (markedBernoulliVoidLocalError mu A B h hLeave i) mu) :
    |(∫ omega, h omega * markedVoidIndicator (markedBernoulliCount A omega) ∂mu) -
        (∫ omega, h omega ∂mu) *
          Real.exp (-markedBernoulliIntensity mu A)| ≤
      ∑ i, |∫ omega,
        markedBernoulliVoidLocalError mu A B h hLeave i omega ∂mu| := by
  rw [markedBernoulliVoid_expectation_decomposition
    A B h hLeave hA hlambda hh herror]
  exact Finset.abs_sum_le_sum_abs
    (fun i ↦ ∫ omega, markedBernoulliVoidLocalError mu A B h hLeave i omega ∂mu)
    Finset.univ

/-- A slightly looser but often easier-to-estimate version, with expected
absolute local errors on the right. -/
theorem markedBernoulliVoid_stein_bound_integral_abs
    {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (A : I → Set Omega) (B : I → Finset I)
    (h : Omega → ℝ) (hLeave : I → Omega → ℝ)
    (hA : ∀ i, MeasurableSet (A i))
    (hlambda : markedBernoulliIntensity mu A ≠ 0)
    (hh : Integrable h mu)
    (herror : ∀ i, Integrable
      (markedBernoulliVoidLocalError mu A B h hLeave i) mu) :
    |(∫ omega, h omega * markedVoidIndicator (markedBernoulliCount A omega) ∂mu) -
        (∫ omega, h omega ∂mu) *
          Real.exp (-markedBernoulliIntensity mu A)| ≤
      ∑ i, ∫ omega,
        |markedBernoulliVoidLocalError mu A B h hLeave i omega| ∂mu := by
  refine (markedBernoulliVoid_stein_bound
    A B h hLeave hA hlambda hh herror).trans ?_
  apply Finset.sum_le_sum
  intro i _hi
  exact abs_integral_le_integral_abs

/-- Event-specific local error with the tested mark written explicitly as
`test (X omega)` and the leave-one mark as `test (XLeave i omega)`. -/
def markedBernoulliVoidLocalErrorOfMarks
    {I Omega Mark : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) (A : I → Set Omega) (B : I → Finset I)
    (test : Mark → ℝ) (X : Omega → Mark) (XLeave : I → Omega → Mark)
    (i : I) (omega : Omega) : ℝ :=
  markedBernoulliVoidLocalError mu A B
    (fun eta ↦ test (X eta))
    (fun j eta ↦ test (XLeave j eta)) i omega

/-- Mark-valued form of `markedBernoulliVoid_stein_bound`.  This is the
literal finite inequality

`|E[test(X) 1_{W=0}] - E[test(X)] exp(-lambda)|`

with arbitrary leave-one marks `XLeave i`. -/
theorem markedBernoulliVoid_stein_bound_of_marks
    {I Omega Mark : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (A : I → Set Omega) (B : I → Finset I)
    (test : Mark → ℝ) (X : Omega → Mark) (XLeave : I → Omega → Mark)
    (hA : ∀ i, MeasurableSet (A i))
    (hlambda : markedBernoulliIntensity mu A ≠ 0)
    (hX : Integrable (fun omega ↦ test (X omega)) mu)
    (herror : ∀ i, Integrable
      (markedBernoulliVoidLocalErrorOfMarks mu A B test X XLeave i) mu) :
    |(∫ omega, test (X omega) *
          markedVoidIndicator (markedBernoulliCount A omega) ∂mu) -
        (∫ omega, test (X omega) ∂mu) *
          Real.exp (-markedBernoulliIntensity mu A)| ≤
      ∑ i, |∫ omega,
        markedBernoulliVoidLocalErrorOfMarks
          mu A B test X XLeave i omega ∂mu| := by
  exact markedBernoulliVoid_stein_bound A B
    (fun omega ↦ test (X omega))
    (fun i omega ↦ test (XLeave i omega))
    hA hlambda hX herror

end

end LogdetLean.Coherence
