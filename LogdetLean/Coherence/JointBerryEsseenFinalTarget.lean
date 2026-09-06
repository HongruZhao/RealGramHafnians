import LogdetLean.Coherence.ProvedLogdetBerryEsseenEnvelope
/-!
# Final quantitative normal--Gumbel target

This file states the exact compact-threshold theorem sought in the paper with
the dimension-free Gumbel CDF.  It uses the *proved finite* null
log-determinant envelope, rather than treating the sharp asymptotic scale as
if it were already a finite inequality.

The final assembly theorem below is proved.  Its two probabilistic/analytic
inputs are named propositions, not axioms: the marked Poisson--Stein joint
bound and the finite Beta-intensity replacement bound.
-/

namespace LogdetLean.Coherence

noncomputable section

/-- The finite exact-intensity joint rate supported by the marked one-edge
deletion argument. -/
def provedExactIntensityJointRateEnvelope (m p : ℕ) : ℝ :=
  provedNullLogdetKolmogorovEnvelope m p +
    |Real.log (p : ℝ) /
      ((m : ℝ) * Real.sqrt (nullVariance m p))| +
    |1 / (p : ℝ)|

/-- The final rate after replacing the finite Beta intensity by the fixed
Gumbel intensity. -/
def provedFixedGumbelJointRateEnvelope (m p : ℕ) : ℝ :=
  provedExactIntensityJointRateEnvelope m p +
    intensityReplacementRateEnvelope m p

theorem provedExactIntensityJointRateEnvelope_nonneg (m p : ℕ) :
    0 ≤ provedExactIntensityJointRateEnvelope m p := by
  unfold provedExactIntensityJointRateEnvelope
  exact add_nonneg
    (add_nonneg (provedNullLogdetKolmogorovEnvelope_nonneg m p)
      (abs_nonneg _)) (abs_nonneg _)

theorem provedFixedGumbelJointRateEnvelope_nonneg (m p : ℕ) :
    0 ≤ provedFixedGumbelJointRateEnvelope m p := by
  unfold provedFixedGumbelJointRateEnvelope
  exact add_nonneg (provedExactIntensityJointRateEnvelope_nonneg m p)
    (intensityReplacementRateEnvelope_nonneg m p)

/-- Named model-specific component: a compact-`x` marked Poisson--Stein
bound relative to the exact finite intensity.  It is proved in
`GaussianMarkedJointConcrete.lean`. -/
def CompactMarkedExactIntensityJointBound : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ P : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (m p : ℕ) (z x : ℝ), P ≤ p → p ≤ m → |x| ≤ M →
      exactIntensityJointError m p z x ≤
        C * provedExactIntensityJointRateEnvelope m p

/-- Named finite analytic component: uniform replacement of the finite Beta
intensity on each compact threshold window.  It is proved in
`JointBerryEsseenIntensityDischarge.lean`. -/
def CompactFiniteIntensityReplacementBound : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ P : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (m p : ℕ) (x : ℝ), P ≤ p → p ≤ m → |x| ≤ M →
      |Real.exp (-finiteCoherenceIntensity m p x) -
          Real.exp (-classicalCoherenceIntensity x)| ≤
        C * intensityReplacementRateEnvelope m p

/-- Desired dimension-free compact-threshold joint Berry--Esseen theorem. -/
def CompactFixedGumbelJointBerryEsseenFinal : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ P : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (m p : ℕ) (z x : ℝ), P ≤ p → p ≤ m → |x| ≤ M →
      limitingJointError m p z x ≤
        C * provedFixedGumbelJointRateEnvelope m p

/-- Once the marked joint bound and finite-intensity estimate are supplied,
the desired fixed-Gumbel theorem follows by the triangle inequality, with no
further probability argument. -/
theorem compactFixedGumbelJointBerryEsseenFinal_of_components
    (hjoint : CompactMarkedExactIntensityJointBound)
    (hintensity : CompactFiniteIntensityReplacementBound) :
    CompactFixedGumbelJointBerryEsseenFinal := by
  intro M hM
  obtain ⟨P₁, C₁, hC₁, hjointBound⟩ := hjoint M hM
  obtain ⟨P₂, C₂, hC₂, hintensityBound⟩ := hintensity M hM
  refine ⟨max P₁ P₂, C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro m p z x hp hpm hx
  have hp₁ : P₁ ≤ p := (le_max_left P₁ P₂).trans hp
  have hp₂ : P₂ ≤ p := (le_max_right P₁ P₂).trans hp
  have h₁ := hjointBound m p z x hp₁ hpm hx
  have h₂ := hintensityBound m p x hp₂ hpm hx
  have htransfer := limitingJointError_le_of_two_bounds h₁ h₂
  have hE₁ := provedExactIntensityJointRateEnvelope_nonneg m p
  have hE₂ := intensityReplacementRateEnvelope_nonneg m p
  unfold provedFixedGumbelJointRateEnvelope
  calc
    limitingJointError m p z x ≤
        C₁ * provedExactIntensityJointRateEnvelope m p +
          C₂ * intensityReplacementRateEnvelope m p := htransfer
    _ ≤ (C₁ + C₂) *
          (provedExactIntensityJointRateEnvelope m p +
            intensityReplacementRateEnvelope m p) := by
      nlinarith [mul_nonneg hC₁ hE₂, mul_nonneg hC₂ hE₁]

end

end LogdetLean.Coherence
