import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
/-!
# A deterministic Edgeworth-to-Kolmogorov transfer

The probabilistic work in an Edgeworth theorem produces a uniform remainder
bound.  The checked results below formalize the deterministic step that turns
that bound into a sharp Kolmogorov estimate.  They also prove, from elementary
exponential inequalities, the exact maximizer of the first normal Edgeworth
shape.
-/

namespace LogdetLean

noncomputable section

/-- Supremum distance between real-valued functions.  On cumulative
distribution functions this is the Kolmogorov distance. -/
def supDistance (F G : ℝ → ℝ) : ℝ :=
  sSup (Set.range fun x ↦ |F x - G x|)

/-- A pointwise bound controls the supremum distance. -/
theorem supDistance_le_of_bound {F G : ℝ → ℝ} {B : ℝ}
    (hB : ∀ x, |F x - G x| ≤ B) : supDistance F G ≤ B := by
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨x, rfl⟩
    exact hB x

/-- Every pointwise discrepancy is at most the supremum distance, provided a
finite uniform bound is available. -/
theorem point_le_supDistance {F G : ℝ → ℝ} {B : ℝ}
    (hB : ∀ x, |F x - G x| ≤ B) (x : ℝ) :
    |F x - G x| ≤ supDistance F G := by
  apply le_csSup
  · exact ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩
  · exact ⟨x, rfl⟩

/-- An elementary exponential bound used to control the Edgeworth shape. -/
theorem exp_quarter_sq_le_exp_half {y : ℝ} (hy : 0 ≤ y) :
    (1 + y / 4) ^ 2 ≤ Real.exp (y / 2) := by
  have hbase : 1 + y / 4 ≤ Real.exp (y / 4) := by
    simpa [add_comm] using Real.add_one_le_exp (y / 4)
  have hbase0 : 0 ≤ 1 + y / 4 := by positivity
  have hsquare := (sq_le_sq₀ hbase0 (Real.exp_nonneg _)).2 hbase
  calc
    (1 + y / 4) ^ 2 ≤ (Real.exp (y / 4)) ^ 2 := hsquare
    _ = Real.exp (y / 2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- For nonnegative `y`, the exponential dominates the linear term needed in
the tail half of the maximizer proof. -/
theorem linear_le_exp_half {y : ℝ} (hy : 0 ≤ y) :
    y - 1 ≤ Real.exp (y / 2) := by
  calc
    y - 1 ≤ (1 + y / 4) ^ 2 := by nlinarith [sq_nonneg (y - 4)]
    _ ≤ Real.exp (y / 2) := exp_quarter_sq_le_exp_half hy

/-- Exact elementary inequality behind the first Edgeworth maximizer. -/
theorem abs_one_sub_mul_exp_neg_half_le_one (y : ℝ) (hy : 0 ≤ y) :
    |1 - y| * Real.exp (-y / 2) ≤ 1 := by
  by_cases hy1 : y ≤ 1
  · rw [abs_of_nonneg (sub_nonneg.mpr hy1)]
    have hexp : Real.exp (-y / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.exp_nonneg (-y / 2)]
  · have hy1' : 1 ≤ y := le_of_not_ge hy1
    rw [abs_of_nonpos (sub_nonpos.mpr hy1'), neg_sub]
    have hlin := linear_le_exp_half hy
    have hmul : (y - 1) * Real.exp (-y / 2) ≤
        Real.exp (y / 2) * Real.exp (-y / 2) := by
      exact mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
    calc
      (y - 1) * Real.exp (-y / 2) ≤
          Real.exp (y / 2) * Real.exp (-y / 2) := hmul
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp

/-- The unnormalized Gaussian core. -/
def gaussianCore (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)

/-- The first normal Edgeworth correction without the constant
`1 / sqrt (2π)`. -/
def edgeworthShapeCore (x : ℝ) : ℝ := (1 - x ^ 2) * gaussianCore x

/-- The first Edgeworth shape has absolute value at most one. -/
theorem abs_edgeworthShapeCore_le_one (x : ℝ) :
    |edgeworthShapeCore x| ≤ 1 := by
  rw [edgeworthShapeCore, gaussianCore, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact abs_one_sub_mul_exp_neg_half_le_one (x ^ 2) (sq_nonneg x)

/-- The upper bound is attained at zero; hence the shape supremum is exactly
one. -/
@[simp] theorem edgeworthShapeCore_zero : edgeworthShapeCore 0 = 1 := by
  simp [edgeworthShapeCore, gaussianCore]

/-- Standard normal density, written in terms of the unnormalized Gaussian
core used above. -/
def standardNormalDensity (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * gaussianCore x

/-- Bridge to mathlib's standard normal density. -/
theorem standardNormalDensity_eq_gaussianPDFReal (x : ℝ) :
    standardNormalDensity x =
      ProbabilityTheory.gaussianPDFReal 0 1 x := by
  simp [standardNormalDensity, gaussianCore,
    ProbabilityTheory.gaussianPDFReal]

/-- The actual first normal Edgeworth shape `(1-x²)φ(x)`. -/
def normalEdgeworthShape (x : ℝ) : ℝ :=
  (1 - x ^ 2) * standardNormalDensity x

theorem normalEdgeworthShape_eq_core (x : ℝ) :
    normalEdgeworthShape x =
      edgeworthShapeCore x / Real.sqrt (2 * Real.pi) := by
  simp [normalEdgeworthShape, standardNormalDensity, edgeworthShapeCore,
    div_eq_mul_inv]
  ring

/-- The exact uniform bound for `(1-x²)φ(x)`. -/
theorem abs_normalEdgeworthShape_le (x : ℝ) :
    |normalEdgeworthShape x| ≤ 1 / Real.sqrt (2 * Real.pi) := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  rw [normalEdgeworthShape_eq_core, abs_div, abs_of_pos hsqrt]
  exact div_le_div_of_nonneg_right (abs_edgeworthShapeCore_le_one x) hsqrt.le

/-- The exact normal Edgeworth bound is attained at zero. -/
@[simp] theorem normalEdgeworthShape_zero :
    normalEdgeworthShape 0 = 1 / Real.sqrt (2 * Real.pi) := by
  simp [normalEdgeworthShape_eq_core]

/-- Consequently the supremum of the absolute normal Edgeworth shape is
exactly `1 / sqrt (2π)`. -/
theorem supDistance_normalEdgeworthShape_zero :
    supDistance normalEdgeworthShape (fun _ ↦ 0) =
      1 / Real.sqrt (2 * Real.pi) := by
  have hbound : ∀ x, |normalEdgeworthShape x - 0| ≤
      1 / Real.sqrt (2 * Real.pi) := by
    intro x
    simpa using abs_normalEdgeworthShape_le x
  apply le_antisymm (supDistance_le_of_bound hbound)
  have hpoint := point_le_supDistance hbound 0
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
  rw [normalEdgeworthShape_zero, sub_zero, abs_of_nonneg hc] at hpoint
  exact hpoint

/-- Deterministic sharp Edgeworth transfer.  A uniform remainder bound for
`F-G+λh`, together with the exact supremum and maximizer of `h`, yields the
finite-error estimate `|d_K-λc| ≤ remainder`. -/
theorem edgeworth_transfer
    {F G h : ℝ → ℝ} {lambda remainder c : ℝ}
    (hlambda : 0 ≤ lambda) (hc : 0 ≤ c)
    (hshape : ∀ x, |h x| ≤ c) (hzero : h 0 = c)
    (hexpansion : ∀ x, |(F x - G x) + lambda * h x| ≤ remainder) :
    |supDistance F G - lambda * c| ≤ remainder := by
  have hpoint : ∀ x, |F x - G x| ≤ lambda * c + remainder := by
    intro x
    calc
      |F x - G x| = |((F x - G x) + lambda * h x) - lambda * h x| := by ring_nf
      _ ≤ |(F x - G x) + lambda * h x| + |lambda * h x| := abs_sub _ _
      _ ≤ remainder + lambda * c := by
        apply add_le_add
        · exact hexpansion x
        · rw [abs_mul, abs_of_nonneg hlambda]
          exact mul_le_mul_of_nonneg_left (hshape x) hlambda
      _ = lambda * c + remainder := by ring
  have hu : supDistance F G ≤ lambda * c + remainder :=
    supDistance_le_of_bound hpoint
  have hzeroerr := hexpansion 0
  rw [hzero] at hzeroerr
  have hreverse : lambda * c - remainder ≤ |F 0 - G 0| := by
    calc
      lambda * c - remainder ≤ lambda * c - |(F 0 - G 0) + lambda * c| := by
        linarith
      _ ≤ |F 0 - G 0| := by
        have htri := abs_sub_abs_le_abs_sub (lambda * c)
          ((F 0 - G 0) + lambda * c)
        rw [abs_of_nonneg (mul_nonneg hlambda hc)] at htri
        calc
          lambda * c - |F 0 - G 0 + lambda * c| ≤
              |lambda * c - (F 0 - G 0 + lambda * c)| := htri
          _ = |F 0 - G 0| := by
            rw [show lambda * c - (F 0 - G 0 + lambda * c) = -(F 0 - G 0) by ring,
              abs_neg]
  have hl : lambda * c - remainder ≤ supDistance F G :=
    hreverse.trans (point_le_supDistance hpoint 0)
  rw [abs_le]
  constructor <;> linarith

/-- Paper-specialized transfer: the exact leading Kolmogorov constant is
`λ / sqrt (2π)` whenever the uniform Edgeworth remainder uses the normal
shape `(1-x²)φ(x)`. -/
theorem normal_edgeworth_transfer
    {F G : ℝ → ℝ} {lambda remainder : ℝ}
    (hlambda : 0 ≤ lambda)
    (hexpansion : ∀ x,
      |(F x - G x) + lambda * normalEdgeworthShape x| ≤ remainder) :
    |supDistance F G - lambda / Real.sqrt (2 * Real.pi)| ≤ remainder := by
  simpa [div_eq_mul_inv] using
    (edgeworth_transfer hlambda
      (show 0 ≤ 1 / Real.sqrt (2 * Real.pi) by positivity)
      abs_normalEdgeworthShape_le normalEdgeworthShape_zero hexpansion)

end

end LogdetLean
