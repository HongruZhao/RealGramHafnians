import LogdetLean.FixedSubspaceGaussian
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianDisk
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianGamma
/-!
# Squared norms of iid circular Gaussians and the Gamma convention

Mathlib's real standard-Gaussian norm theorem uses rate `1/2`.  The circular
normalization divides every real coordinate by `sqrt 2`; consequently its
squared norm is one half of that Gamma variable.  This module records that
normalization exactly, before any optional identification of the pushforward
with a rate-one Gamma density.
-/

open scoped ENNReal NNReal Real
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- Squared Euclidean norm of `k` complex coordinates. -/
def circularVectorNormSq {k : ℕ} (x : CircularEuclideanSpace k) : ℝ :=
  ‖x‖ ^ 2

@[fun_prop]
theorem measurable_circularVectorNormSq {k : ℕ} :
    Measurable (circularVectorNormSq (k := k)) := by
  unfold circularVectorNormSq
  fun_prop

/-- Exact convention bridge: the squared norm of `k>0` iid circular
coordinates is the image under `u ↦ u/2` of a Gamma variable with shape `k`
and rate `1/2`.  Equivalently, it is the usual rate-one Gamma normalization. -/
theorem map_circularVectorNormSq_iid_circular_eq_half_gamma
    {k : ℕ} (hk : 0 < k) :
    ((Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)).map
        (circularVectorNormSq (k := k)) =
      (gammaMeasure (k : ℝ) (1 / 2)).map (fun u : ℝ ↦ u / 2) := by
  let E := CircularEuclideanSpace k
  let r : ℝ := (Real.sqrt 2)⁻¹
  let _ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let _ : Nontrivial E := inferInstance
  have hnorm :
      circularVectorNormSq ∘ (fun x : E ↦ r • x) =
        (fun u : ℝ ↦ u / 2) ∘ circularVectorNormSq := by
    funext x
    dsimp [r]
    simp only [Function.comp_apply, circularVectorNormSq, norm_smul,
      Real.norm_eq_abs, abs_inv,
      abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)), mul_pow]
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    rw [inv_pow, hsqrt_sq]
    ring
  rw [map_toLp_pi_circularGaussian_eq_scaled_stdGaussian]
  change ((stdGaussian E).map (fun x : E ↦ r • x)).map
      circularVectorNormSq = _
  rw [Measure.map_map measurable_circularVectorNormSq
      (measurable_const_smul r),
    hnorm,
    ← Measure.map_map (by fun_prop) measurable_circularVectorNormSq]
  unfold circularVectorNormSq
  change (LogdetLean.stdGaussianNormSqMeasure E).map
      (fun u : ℝ ↦ u / 2) = _
  rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma E]
  congr 3
  rw [finrank_real_of_complex E]
  simp [E, CircularEuclideanSpace]

/-- Exact inverse squared-norm moment in the circular normalization:
for `k≥2`, `E[‖Z‖⁻²] = 1/(k-1)`. -/
theorem integral_inv_circularVectorNormSq_iid_circular
    {k : ℕ} (hk : 2 ≤ k) :
    ∫ x : CircularEuclideanSpace k,
        (circularVectorNormSq x)⁻¹
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2) =
      ((k : ℝ) - 1)⁻¹ := by
  have hkpos : 0 < k := by omega
  have hkshape : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [← integral_map
      (measurable_circularVectorNormSq (k := k)).aemeasurable (by fun_prop),
    map_circularVectorNormSq_iid_circular_eq_half_gamma hkpos,
    integral_map (by fun_prop) (by fun_prop)]
  have hpoint : (fun u : ℝ ↦ (u / 2)⁻¹) = fun u ↦ 2 * u⁻¹ := by
    funext u
    field_simp
  rw [hpoint, integral_const_mul,
    integral_inv_gammaMeasure hkshape (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

/-- Extended-nonnegative form of the same exact inverse squared-norm
moment.  This is the base value used by the Tonelli recurrence. -/
theorem lintegral_ofReal_inv_circularVectorNormSq_iid_circular
    {k : ℕ} (hk : 2 ≤ k) :
    ∫⁻ x : CircularEuclideanSpace k,
        ENNReal.ofReal (circularVectorNormSq x)⁻¹
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2) =
      ENNReal.ofReal (((k : ℝ) - 1)⁻¹) := by
  have hkpos : 0 < k := by omega
  have hkshape : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  let P : Measure (CircularEuclideanSpace k) :=
    (Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)
  let f : ℝ → ℝ≥0∞ := fun u ↦ ENNReal.ofReal u⁻¹
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  calc
    (∫⁻ x : CircularEuclideanSpace k,
        ENNReal.ofReal (circularVectorNormSq x)⁻¹ ∂P) =
        ∫⁻ u : ℝ, f u ∂P.map circularVectorNormSq := by
      rw [lintegral_map hf measurable_circularVectorNormSq]
    _ = ∫⁻ u : ℝ, f u
          ∂(gammaMeasure (k : ℝ) (1 / 2)).map (fun u : ℝ ↦ u / 2) := by
      rw [map_circularVectorNormSq_iid_circular_eq_half_gamma hkpos]
    _ = ∫⁻ u : ℝ, f (u / 2) ∂gammaMeasure (k : ℝ) (1 / 2) := by
      rw [lintegral_map hf (by fun_prop)]
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (2 * u⁻¹)
          ∂gammaMeasure (k : ℝ) (1 / 2) := by
      apply lintegral_congr
      intro u
      congr 1
      dsimp [f]
      field_simp
    _ = ENNReal.ofReal 2 *
        ∫⁻ u : ℝ, ENNReal.ofReal u⁻¹
          ∂gammaMeasure (k : ℝ) (1 / 2) := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [lintegral_const_mul (ENNReal.ofReal 2) (by fun_prop)]
    _ = ENNReal.ofReal (((k : ℝ) - 1)⁻¹) := by
      rw [lintegral_ofReal_inv_gammaMeasure hkshape
        (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      field_simp

end

end LogdetLean.GramHafnian
