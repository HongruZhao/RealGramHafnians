import LogdetLean.GammaMellin
import Mathlib.MeasureTheory.Integral.Pi
/-!
# Exact scalar Gamma factors for all three field dimensions

`gammaMeasure` uses a rate, whereas the paper quotes a scale. Thus the
rate here is beta/2. These are literal Gamma integral identities, not an
assumed hafnian-to-Gamma comparison.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

def gammaShape (β : ℝ) (r : ℕ) : ℝ := β * (2 * r - 1) / 2

def gammaNegativeFactor (β : ℝ) (r : ℕ) (p : ℝ) : ℝ :=
  (β / 2) ^ p * Real.Gamma (gammaShape β r - p) / Real.Gamma (gammaShape β r)

theorem gammaShape_pos {β : ℝ} (hβ : 0 < β) {r : ℕ} (hr : 1 ≤ r) :
    0 < gammaShape β r := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold gammaShape
  exact div_pos (mul_pos hβ (by linarith)) (by norm_num)

theorem gammaShape_sub_pos {β p : ℝ} (hβ : 0 < β)
    {r : ℕ} (hr : 2 ≤ r) (hp : p < 3 * β / 2) :
    0 < gammaShape β r - p := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hm : β * 3 ≤ β * (2 * (r : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hβ.le
  unfold gammaShape
  linarith

theorem gammaNegativeFactor_pos {β p : ℝ} (hβ : 0 < β)
    {r : ℕ} (hr : 2 ≤ r) (hp : p < 3 * β / 2) :
    0 < gammaNegativeFactor β r p := by
  unfold gammaNegativeFactor
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.Gamma_pos_of_pos (gammaShape_sub_pos hβ hr hp)))
    (Real.Gamma_pos_of_pos (gammaShape_pos hβ (by omega)))

theorem integral_gamma_negative_factor {β p : ℝ} (hβ : 0 < β)
    {r : ℕ} (hr : 2 ≤ r) (hp : p < 3 * β / 2) :
    (∫ x : ℝ, x ^ (-p) ∂gammaMeasure (gammaShape β r) (β / 2)) =
      gammaNegativeFactor β r p := by
  have h := LogdetLean.integral_rpow_gammaMeasure
    (t := -p) (gammaShape_pos (r := r) hβ (by omega))
    (show 0 < β / 2 by linarith)
    (by simpa only [sub_eq_add_neg] using gammaShape_sub_pos hβ hr hp)
  simpa only [gammaNegativeFactor, neg_neg, sub_eq_add_neg] using h

theorem integrable_gamma_negative_factor {β p : ℝ} (hβ : 0 < β)
    {r : ℕ} (hr : 2 ≤ r) (hp : p < 3 * β / 2) :
    Integrable (fun x : ℝ => x ^ (-p))
      (gammaMeasure (gammaShape β r) (β / 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gamma_negative_factor hβ hr hp]
  exact (gammaNegativeFactor_pos hβ hr hp).ne'

abbrev BenchmarkIndex (n : ℕ) := {r : ℕ // r ∈ Finset.Icc 2 n}

def gammaBenchmarkMeasure (β : ℝ) (n : ℕ) : Measure (BenchmarkIndex n → ℝ) :=
  Measure.pi fun r => gammaMeasure (gammaShape β r.val) (β / 2)

theorem gammaBenchmarkMeasure_probability {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    IsProbabilityMeasure (gammaBenchmarkMeasure β n) := by
  let (r : BenchmarkIndex n) :
      IsProbabilityMeasure (gammaMeasure (gammaShape β r.val) (β / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (gammaShape_pos hβ (by have := (Finset.mem_Icc.mp r.property).1; omega))
      (by linarith)
  unfold gammaBenchmarkMeasure
  infer_instance

/-- Exact product of Gamma inverse factors for the genuine independent
Gamma benchmark. Written as a product of powers, avoiding any convention
for nonpositive arguments outside the Gamma support. -/
theorem integral_gammaBenchmark_negative_product {β p : ℝ} (hβ : 0 < β)
    (n : ℕ) (hp : p < 3 * β / 2) :
    (∫ x : BenchmarkIndex n → ℝ,
      ∏ r : BenchmarkIndex n, (x r) ^ (-p) ∂gammaBenchmarkMeasure β n) =
      ∏ r : BenchmarkIndex n, gammaNegativeFactor β r.val p := by
  let (r : BenchmarkIndex n) :
      IsProbabilityMeasure (gammaMeasure (gammaShape β r.val) (β / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (gammaShape_pos hβ (by have := (Finset.mem_Icc.mp r.property).1; omega))
      (by linarith)
  unfold gammaBenchmarkMeasure
  rw [integral_fintype_prod_eq_prod (fun (_ : BenchmarkIndex n) (x : ℝ) => x ^ (-p))]
  apply Finset.prod_congr rfl
  intro r _
  exact integral_gamma_negative_factor hβ (Finset.mem_Icc.mp r.property).1 hp

theorem integrable_gammaBenchmark_negative_product {β p : ℝ} (hβ : 0 < β)
    (n : ℕ) (hp : p < 3 * β / 2) :
    Integrable (fun x : BenchmarkIndex n → ℝ =>
      ∏ r : BenchmarkIndex n, (x r) ^ (-p)) (gammaBenchmarkMeasure β n) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gammaBenchmark_negative_product hβ n hp]
  apply ne_of_gt
  apply Finset.prod_pos
  intro r _
  exact gammaNegativeFactor_pos hβ (Finset.mem_Icc.mp r.property).1 hp

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
