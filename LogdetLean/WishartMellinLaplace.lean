import LogdetLean.WishartBetaGammaFactors
import LogdetLean.BetaMellin
import LogdetLean.GammaMellin
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-!
# A real Mellin--Laplace transform for Gaussian Gram matrices

This file evaluates the finite-dimensional transform behind the central
Wishart matrix-gamma identity by the already formalized Bartlett
Beta--Gamma factors.  It is a scalar proof of the real-parameter identity,
not an invocation of an unformalized matrix-valued integral.

For provenance, the resulting formula is the restriction to real parameters
of Muirhead (1982), Theorem 2.1.11, as used in Zhao,
arXiv:2608.00565v1, equations (5.17)--(5.20) and Appendix A.  The proof route
here instead uses the classical Bartlett decomposition and the Beta--Gamma
independence proved in `WishartBetaGammaFactors`.
-/

namespace LogdetLean

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal

set_option linter.style.haveILetI false

/-- Multiplying a Gamma density by a real Mellin power and an exponential
tilt changes both its shape and rate. -/
private theorem rpow_exp_mul_gammaPDFReal
    {a r t c x : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hat : 0 < a + t) (hrc : 0 < r + c) (hx : 0 < x) :
    x ^ t * Real.exp (-c * x) * gammaPDFReal a r x =
      (r ^ a * Real.Gamma (a + t) /
          (Real.Gamma a * (r + c) ^ (a + t))) *
        gammaPDFReal (a + t) (r + c) x := by
  rw [gammaPDFReal, gammaPDFReal, if_pos hx.le, if_pos hx.le]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGat : Real.Gamma (a + t) ≠ 0 :=
    (Real.Gamma_pos_of_pos hat).ne'
  have hxp : x ^ t * x ^ (a - 1) = x ^ (a + t - 1) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hexp : Real.exp (-c * x) * Real.exp (-(r * x)) =
      Real.exp (-((r + c) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    x ^ t * Real.exp (-c * x) *
          (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
        (r ^ a / Real.Gamma a) * (x ^ t * x ^ (a - 1)) *
          (Real.exp (-c * x) * Real.exp (-(r * x))) := by ring
    _ = (r ^ a / Real.Gamma a) * x ^ (a + t - 1) *
          Real.exp (-((r + c) * x)) := by rw [hxp, hexp]
    _ = (r ^ a * Real.Gamma (a + t) /
          (Real.Gamma a * (r + c) ^ (a + t))) *
        ((r + c) ^ (a + t) / Real.Gamma (a + t) *
          x ^ (a + t - 1) * Real.exp (-((r + c) * x))) := by
      field_simp [hGa, hGat, (Real.rpow_pos_of_pos hrc _).ne']

/-- Exact real Mellin--Laplace transform of a Gamma law. -/
theorem integral_rpow_mul_exp_neg_mul_gammaMeasure
    {a r t c : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hat : 0 < a + t) (hrc : 0 < r + c) :
    ∫ x, x ^ t * Real.exp (-c * x) ∂gammaMeasure a r =
      r ^ a * Real.Gamma (a + t) /
        (Real.Gamma a * (r + c) ^ (a + t)) := by
  rw [gammaMeasure]
  change (∫ x, x ^ t * Real.exp (-c * x)
      ∂volume.withDensity
        (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal a r).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  have hae :
      (fun x ↦ x ^ t * Real.exp (-c * x) * gammaPDFReal a r x) =ᵐ[volume]
        (fun x ↦
          (r ^ a * Real.Gamma (a + t) /
            (Real.Gamma a * (r + c) ^ (a + t))) *
              gammaPDFReal (a + t) (r + c) x) := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx0
    by_cases hx : 0 < x
    · exact rpow_exp_mul_gammaPDFReal ha hr hat hrc hx
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      simp [gammaPDFReal, not_le.mpr hxneg]
  have hae' :
      (fun x ↦ gammaPDFReal a r x *
          (x ^ t * Real.exp (-c * x))) =ᵐ[volume]
        (fun x ↦
          (r ^ a * Real.Gamma (a + t) /
            (Real.Gamma a * (r + c) ^ (a + t))) *
              gammaPDFReal (a + t) (r + c) x) := by
    filter_upwards [hae] with x hx
    rw [← hx]
    ring
  rw [integral_congr_ae hae', integral_const_mul,
    integral_gammaPDFReal_eq_one hat hrc, mul_one]

/-- Multiply one stage function for every coordinate of a right-nested
tuple. -/
def nestedStageProduct {B : Type*} (f : ℕ → B → ℝ) :
    (p : ℕ) → NestedTuple B p → ℝ
  | 0, _ => 1
  | p + 1, z => nestedStageProduct f p z.1 * f p z.2

theorem measurable_nestedStageProduct
    {B : Type*} [MeasurableSpace B]
    (f : ℕ → B → ℝ) (hf : ∀ n, Measurable (f n)) :
    ∀ p, Measurable (nestedStageProduct f p) := by
  intro p
  induction p with
  | zero => exact measurable_const
  | succ p ih =>
      exact (ih.comp measurable_fst).mul ((hf p).comp measurable_snd)

/-- Fubini factorization for a finite nested product.  The identity remains
valid with mathlib's convention that a nonintegrable Bochner integral is
zero. -/
theorem integral_nestedStageProduct
    {B : Type*} [MeasurableSpace B]
    (nu : ℕ → Measure B) [∀ n, SFinite (nu n)]
    (f : ℕ → B → ℝ) :
    ∀ p,
      ∫ z, nestedStageProduct f p z ∂nestedProductMeasureFamily nu p =
        ∏ n ∈ Finset.range p, ∫ x, f n x ∂nu n := by
  intro p
  induction p with
  | zero => simp [nestedStageProduct, nestedProductMeasureFamily]
  | succ p ih =>
      rw [nestedProductMeasureFamily]
      change (∫ z : NestedTuple B p × B,
          nestedStageProduct f p z.1 * f p z.2
            ∂(nestedProductMeasureFamily nu p).prod (nu p)) = _
      rw [integral_prod_mul, ih, Finset.prod_range_succ]

/-- One real Mellin--Laplace factor in the independent Bartlett
representation. -/
def wishartBetaGammaStage (t : ℝ) (c : ℕ → ℝ)
    (n : ℕ) (y : ℝ × ℝ) : ℝ :=
  y.1 ^ t * (y.2 ^ t * Real.exp (-(c n) * y.2))

theorem measurable_wishartBetaGammaStage (t : ℝ) (c : ℕ → ℝ)
    (n : ℕ) : Measurable (wishartBetaGammaStage t c n) := by
  unfold wishartBetaGammaStage
  fun_prop

/-- Closed real transform contributed by stage `n`.  The expression is
written before cancellation so its Beta and Gamma provenance is visible. -/
def wishartBetaGammaStageTransform (m n : ℕ) (t c : ℝ) : ℝ :=
  (if n = 0 then 1 else
    (Real.Gamma ((((m - n : ℕ) : ℝ) / 2) + t) *
          Real.Gamma (((n : ℕ) : ℝ) / 2) /
        Real.Gamma (((m : ℕ) : ℝ) / 2 + t)) /
      (Real.Gamma (((m - n : ℕ) : ℝ) / 2) *
          Real.Gamma (((n : ℕ) : ℝ) / 2) /
        Real.Gamma (((m : ℕ) : ℝ) / 2))) *
    ((1 / 2 : ℝ) ^ (((m : ℕ) : ℝ) / 2) *
        Real.Gamma (((m : ℕ) : ℝ) / 2 + t) /
      (Real.Gamma (((m : ℕ) : ℝ) / 2) *
        ((1 / 2 : ℝ) + c) ^ (((m : ℕ) : ℝ) / 2 + t)))

/-- The same stage transform after the Beta--Gamma cancellation.  This is
the scalar diagonal form of the matrix-gamma factor. -/
def wishartDiagonalStageTransform (m n : ℕ) (t c : ℝ) : ℝ :=
  (Real.Gamma ((((m - n : ℕ) : ℝ) / 2) + t) /
      Real.Gamma (((m - n : ℕ) : ℝ) / 2)) *
    ((1 / 2 : ℝ) ^ (((m : ℕ) : ℝ) / 2) /
      ((1 / 2 : ℝ) + c) ^ (((m : ℕ) : ℝ) / 2 + t))

/-- Algebraic cancellation of the visible Beta and full-column Gamma
normalizers. -/
theorem wishartBetaGammaStageTransform_eq_diagonal
    {m n : ℕ} (hm : 0 < m) (hnm : n < m)
    {t c : ℝ} (ht : 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (_hrate : 0 < (1 / 2 : ℝ) + c) :
    wishartBetaGammaStageTransform m n t c =
      wishartDiagonalStageTransform m n t c := by
  have halpha : 0 < (m : ℝ) / 2 := by positivity
  have halphat : 0 < (m : ℝ) / 2 + t := by
    have hle : (m - n : ℕ) ≤ m := Nat.sub_le _ _
    have hcast : (((m - n : ℕ) : ℝ) / 2) ≤ (m : ℝ) / 2 := by
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) (by norm_num)
    linarith
  by_cases hn : n = 0
  · subst n
    unfold wishartBetaGammaStageTransform wishartDiagonalStageTransform
    simp only [Nat.sub_zero]
    field_simp [
      (Real.Gamma_pos_of_pos halpha).ne',
      (Real.Gamma_pos_of_pos halphat).ne']
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hres : 0 < (((m - n : ℕ) : ℝ) / 2) := by
      have : 0 < m - n := Nat.sub_pos_of_lt hnm
      positivity
    unfold wishartBetaGammaStageTransform wishartDiagonalStageTransform
    rw [if_neg hn]
    field_simp [
      (Real.Gamma_pos_of_pos hres).ne',
      (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) / 2)).ne',
      (Real.Gamma_pos_of_pos halpha).ne',
      (Real.Gamma_pos_of_pos ht).ne',
      (Real.Gamma_pos_of_pos halphat).ne']
    have harg : ((m : ℝ) + 2 * t) / 2 = (m : ℝ) / 2 + t := by
      ring
    have hG : Real.Gamma (((m : ℝ) + 2 * t) / 2) ≠ 0 := by
      rw [harg]
      exact (Real.Gamma_pos_of_pos halphat).ne'
    field_simp [hG]

/-- Exact integral of one independent Beta--Gamma stage. -/
theorem integral_wishartBetaGammaStage
    {m n : ℕ} (hm : 0 < m) (hnm : n < m)
    {t c : ℝ} (ht : 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : 0 < (1 / 2 : ℝ) + c) :
    ∫ y, wishartBetaGammaStage t (fun _ ↦ c) n y
        ∂gaussianGramBetaGammaFactorMeasure m n =
      wishartBetaGammaStageTransform m n t c := by
  have halpha : 0 < (m : ℝ) / 2 := by positivity
  let _ : IsProbabilityMeasure
      (gammaMeasure ((m : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure halpha (by norm_num)
  unfold gaussianGramBetaGammaFactorMeasure wishartBetaGammaStage
  change (∫ y : ℝ × ℝ,
      (fun b : ℝ ↦ b ^ t) y.1 *
        (fun s : ℝ ↦ s ^ t * Real.exp (-c * s)) y.2
        ∂(gaussianGramSchmidtFactorMeasure m n).prod
          (gammaMeasure ((m : ℝ) / 2) (1 / 2))) = _
  rw [MeasureTheory.integral_prod_mul
    (fun b : ℝ ↦ b ^ t)
    (fun s : ℝ ↦ s ^ t * Real.exp (-c * s))]
  have halphat : 0 < (m : ℝ) / 2 + t := by
    have hle : (m - n : ℕ) ≤ m := Nat.sub_le _ _
    have hcast : (((m - n : ℕ) : ℝ) / 2) ≤ (m : ℝ) / 2 := by
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) (by norm_num)
    linarith
  rw [integral_rpow_mul_exp_neg_mul_gammaMeasure
    halpha (by norm_num) halphat hrate]
  by_cases hn : n = 0
  · subst n
    simp [gaussianGramSchmidtFactorMeasure,
      wishartBetaGammaStageTransform]
  · cases n with
    | zero => exact (hn rfl).elim
    | succ k =>
        have hres : 0 < (((m - (k + 1) : ℕ) : ℝ) / 2) := by
          have : 0 < m - (k + 1) := Nat.sub_pos_of_lt hnm
          positivity
        rw [gaussianGramSchmidtFactorMeasure]
        rw [integral_rpow_betaMeasure_eq_gamma_quotient
          hres (by positivity) ht]
        unfold wishartBetaGammaStageTransform
        rw [if_neg (Nat.succ_ne_zero k)]
        have hsum :
            (((m - (k + 1) : ℕ) : ℝ) / 2) +
                (((k + 1 : ℕ) : ℝ) / 2) = (m : ℝ) / 2 := by
          rw [Nat.cast_sub (Nat.le_of_lt hnm)]
          push_cast
          ring
        have hsumt :
            (((m - (k + 1) : ℕ) : ℝ) / 2) + t +
                (((k + 1 : ℕ) : ℝ) / 2) = (m : ℝ) / 2 + t := by
          linarith [hsum]
        rw [hsum]
        rw [hsumt]

/-- Exact finite product transform of the independent Bartlett
Beta--Gamma representation. -/
theorem integral_nestedWishartBetaGammaTransform
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    {t : ℝ} (c : ℕ → ℝ)
    (ht : ∀ n < p, 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : ∀ n < p, 0 < (1 / 2 : ℝ) + c n) :
    ∫ y,
        nestedStageProduct (wishartBetaGammaStage t c) p y
          ∂nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p =
      ∏ n ∈ Finset.range p,
        wishartBetaGammaStageTransform m n t (c n) := by
  rw [integral_nestedStageProduct]
  apply Finset.prod_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  exact integral_wishartBetaGammaStage hm (lt_of_lt_of_le hn hp)
    (ht n hn) (hrate n hn)

/-- Exact finite diagonal matrix-gamma product, with all intermediate
Beta normalizers cancelled. -/
theorem integral_nestedWishartBetaGammaTransform_eq_diagonal
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    {t : ℝ} (c : ℕ → ℝ)
    (ht : ∀ n < p, 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : ∀ n < p, 0 < (1 / 2 : ℝ) + c n) :
    ∫ y,
        nestedStageProduct (wishartBetaGammaStage t c) p y
          ∂nestedProductMeasureFamily
            (gaussianGramBetaGammaFactorMeasure m) p =
      ∏ n ∈ Finset.range p,
        wishartDiagonalStageTransform m n t (c n) := by
  rw [integral_nestedWishartBetaGammaTransform hm hp c ht hrate]
  apply Finset.prod_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  exact wishartBetaGammaStageTransform_eq_diagonal hm
    (lt_of_lt_of_le hn hp) (ht n hn) (hrate n hn)

end

end LogdetLean
