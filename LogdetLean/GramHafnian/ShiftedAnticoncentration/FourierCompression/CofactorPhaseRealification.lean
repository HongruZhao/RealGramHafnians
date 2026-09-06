import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseBackground
/-!
# Exact complex-to-real phase identities

This file formalizes the normalization used in the Fourier-compression
argument.  The realification has a factor `sqrt 2`, `L(q)` has a factor
`1 / sqrt 2`, and `T(w,M)` has a factor `1 / 2`.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

/-- The two real blocks of a complex `k`-vector. -/
abbrev ComplexRealificationIndex (k : ℕ) := Sum (Fin k) (Fin k)

/-- `sqrt 2 (Re x, Im x)`, so a standard complex Gaussian realifies to a
standard real Gaussian. -/
def complexRealification {k : ℕ} (x : Fin k → ℂ) :
    ComplexRealificationIndex k → ℝ
  | Sum.inl p => Real.sqrt 2 * (x p).re
  | Sum.inr p => Real.sqrt 2 * (x p).im

/-- The two real coordinates `(Re w, Im w)`. -/
def complexPhaseCoordinates (w : ℂ) : Fin 2 → ℝ :=
  fun s ↦ if s = 0 then w.re else w.im

/-- The exact real matrix `L(q)` from the manuscript. -/
def cofactorLinearPhaseMatrix {k : ℕ} (q : Fin k → ℂ) :
    Matrix (ComplexRealificationIndex k) (Fin 2) ℝ
  | Sum.inl p, s =>
      if s = 0 then (q p).re / Real.sqrt 2 else -(q p).im / Real.sqrt 2
  | Sum.inr p, s =>
      if s = 0 then -(q p).im / Real.sqrt 2 else -(q p).re / Real.sqrt 2

/-- The exact real block matrix `T(w,M)` from the manuscript. -/
def cofactorBilinearPhaseMatrix {k : ℕ} (w : ℂ)
    (M : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (ComplexRealificationIndex k) (ComplexRealificationIndex k) ℝ
  | Sum.inl p, Sum.inl q =>
      (w.re * (M p q).re - w.im * (M p q).im) / 2
  | Sum.inl p, Sum.inr q =>
      (-w.re * (M p q).im - w.im * (M p q).re) / 2
  | Sum.inr p, Sum.inl q =>
      (-w.re * (M p q).im - w.im * (M p q).re) / 2
  | Sum.inr p, Sum.inr q =>
      (-w.re * (M p q).re + w.im * (M p q).im) / 2

/-- A real transpose linear phase `g^T L a`. -/
def realTransposeLinearPhase {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → ℝ) (L : Matrix ι κ ℝ) (a : κ → ℝ) : ℝ :=
  ∑ i : ι, ∑ s : κ, g i * L i s * a s

/-- A real transpose bilinear phase `g^T T h`. -/
def realTransposeBilinearPhase {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → ℝ) (T : Matrix ι κ ℝ) (h : κ → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : κ, g i * T i j * h j

theorem real_sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  positivity

theorem real_sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem complex_sum_re {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ i : ι, f i).re = ∑ i : ι, (f i).re := by
  change Complex.reCLM (∑ i : ι, f i) = _
  rw [map_sum]
  rfl

theorem complex_sum_im {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ i : ι, f i).im = ∑ i : ι, (f i).im := by
  change Complex.imCLM (∑ i : ι, f i) = _
  rw [map_sum]
  rfl

def complexLinearPhaseCoordinate {k : ℕ}
    (w : ℂ) (x q : Fin k → ℂ) (p : Fin k) : ℝ :=
  w.re * ((x p).re * (q p).re - (x p).im * (q p).im) -
    w.im * ((x p).re * (q p).im + (x p).im * (q p).re)

/-- Coordinate expansion of the left side of the linear realification
identity. -/
theorem complex_linear_phase_re_eq_sum {k : ℕ}
    (w : ℂ) (x q : Fin k → ℂ) :
    (w * transposeDot x q).re =
      ∑ p : Fin k, complexLinearPhaseCoordinate w x q p := by
  unfold transposeDot
  rw [Complex.mul_re, complex_sum_re, complex_sum_im]
  simp_rw [Complex.mul_re, Complex.mul_im, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  unfold complexLinearPhaseCoordinate
  rfl

theorem real_linear_phase_coordinate_eq {k : ℕ}
    (w : ℂ) (x q : Fin k → ℂ) (p : Fin k) :
    (∑ s : Fin 2,
        complexRealification x (Sum.inl p) *
          cofactorLinearPhaseMatrix q (Sum.inl p) s *
          complexPhaseCoordinates w s) +
      (∑ s : Fin 2,
        complexRealification x (Sum.inr p) *
          cofactorLinearPhaseMatrix q (Sum.inr p) s *
          complexPhaseCoordinates w s) =
      complexLinearPhaseCoordinate w x q p := by
  simp only [Fin.sum_univ_two]
  simp [complexRealification, cofactorLinearPhaseMatrix,
    complexPhaseCoordinates, complexLinearPhaseCoordinate]
  field_simp [real_sqrt_two_ne_zero]
  ring

/-- Exact identity
`Re (w x^T q) = R(x)^T L(q) (Re w, Im w)` with all normalizing factors. -/
theorem complex_linear_phase_realification {k : ℕ}
    (w : ℂ) (x q : Fin k → ℂ) :
    (w * transposeDot x q).re =
      realTransposeLinearPhase (complexRealification x)
        (cofactorLinearPhaseMatrix q) (complexPhaseCoordinates w) := by
  rw [complex_linear_phase_re_eq_sum]
  unfold realTransposeLinearPhase
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  exact (real_linear_phase_coordinate_eq w x q p).symm

def complexBilinearPhaseCoordinate {k : ℕ} (w : ℂ)
    (x : Fin k → ℂ) (M : Matrix (Fin k) (Fin k) ℂ)
    (y : Fin k → ℂ) (p q : Fin k) : ℝ :=
  (w * (x p * M p q * y q)).re

def realBilinearPhaseCoordinate {k : ℕ} (w : ℂ)
    (x : Fin k → ℂ) (M : Matrix (Fin k) (Fin k) ℂ)
    (y : Fin k → ℂ) (p q : Fin k) : ℝ :=
  (complexRealification x (Sum.inl p) *
      cofactorBilinearPhaseMatrix w M (Sum.inl p) (Sum.inl q) *
      complexRealification y (Sum.inl q) +
    complexRealification x (Sum.inl p) *
      cofactorBilinearPhaseMatrix w M (Sum.inl p) (Sum.inr q) *
      complexRealification y (Sum.inr q)) +
  (complexRealification x (Sum.inr p) *
      cofactorBilinearPhaseMatrix w M (Sum.inr p) (Sum.inl q) *
      complexRealification y (Sum.inl q) +
    complexRealification x (Sum.inr p) *
      cofactorBilinearPhaseMatrix w M (Sum.inr p) (Sum.inr q) *
      complexRealification y (Sum.inr q))

/-- The four real block entries of `T(w,M)` reproduce one complex
coordinate of `Re (w x^T M y)`. -/
theorem real_bilinear_phase_coordinate_eq {k : ℕ} (w : ℂ)
    (x : Fin k → ℂ) (M : Matrix (Fin k) (Fin k) ℂ)
    (y : Fin k → ℂ) (p q : Fin k) :
    realBilinearPhaseCoordinate w x M y p q =
      complexBilinearPhaseCoordinate w x M y p q := by
  calc
    realBilinearPhaseCoordinate w x M y p q =
        (Real.sqrt 2 * Real.sqrt 2 / 2) *
          complexBilinearPhaseCoordinate w x M y p q := by
      simp [realBilinearPhaseCoordinate, complexBilinearPhaseCoordinate,
        complexRealification, cofactorBilinearPhaseMatrix,
        Complex.mul_re, Complex.mul_im]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = complexBilinearPhaseCoordinate w x M y p q := by
      rw [real_sqrt_two_mul_self]
      norm_num

theorem complex_bilinear_phase_re_eq_sum {k : ℕ} (w : ℂ)
    (x : Fin k → ℂ) (M : Matrix (Fin k) (Fin k) ℂ)
    (y : Fin k → ℂ) :
    (w * transposeBilinear x M y).re =
      ∑ p : Fin k, ∑ q : Fin k,
        complexBilinearPhaseCoordinate w x M y p q := by
  unfold transposeBilinear
  calc
    (w * ∑ p : Fin k, ∑ q : Fin k, x p * M p q * y q).re =
        (∑ p : Fin k, ∑ q : Fin k,
          w * (x p * M p q * y q)).re := by
      congr 1
      simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [complex_sum_re]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [complex_sum_re]
      rfl

theorem real_bilinear_phase_eq_sum {k : ℕ} (w : ℂ)
    (x : Fin k → ℂ) (M : Matrix (Fin k) (Fin k) ℂ)
    (y : Fin k → ℂ) :
    realTransposeBilinearPhase (complexRealification x)
        (cofactorBilinearPhaseMatrix w M) (complexRealification y) =
      ∑ p : Fin k, ∑ q : Fin k,
        realBilinearPhaseCoordinate w x M y p q := by
  unfold realTransposeBilinearPhase realBilinearPhaseCoordinate
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  simp_rw [← Finset.sum_add_distrib]

/-- Exact identity
`Re (w x^T M y) = R(x)^T T(w,M) R(y)` with the factor `1/2`. -/
theorem complex_bilinear_phase_realification {k : ℕ} (w : ℂ)
    (x : Fin k → ℂ) (M : Matrix (Fin k) (Fin k) ℂ)
    (y : Fin k → ℂ) :
    (w * transposeBilinear x M y).re =
      realTransposeBilinearPhase (complexRealification x)
        (cofactorBilinearPhaseMatrix w M) (complexRealification y) := by
  rw [complex_bilinear_phase_re_eq_sum, real_bilinear_phase_eq_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  exact (real_bilinear_phase_coordinate_eq w x M y p q).symm

end

end LogdetLean.GramHafnian
