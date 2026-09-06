import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.BilinearGaussianKernel
import Mathlib.Analysis.InnerProductSpace.Spectrum
/-!
# Arbitrary-basis bilinear Gaussian completed square

This file transports the diagonal Gaussian calculation to an arbitrary real
matrix/operator.  We diagonalize the positive operator `D = I + T†T` by its
orthonormal eigenbasis.  Standard Gaussian measure is invariant under that
orthogonal change of coordinates, so the finite diagonal identity applies
with no Jacobian or missing normalization.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 1600000

/-- Completed square for an arbitrary positive symmetric operator, expressed
in its orthonormal eigenbasis. -/
theorem integral_cexp_symmetric_tilted_stdGaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (D : E →ₗ[ℝ] E) (hD : D.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hpos : ∀ i : Fin n, 0 < hD.eigenvalues hn i)
    (q r : E) :
    ∫ h : E, Complex.exp
        (-(((inner ℝ h ((D - (LinearMap.id : E →ₗ[ℝ] E)) h) / 2 : ℝ) : ℂ)) +
          ((-inner ℝ h q : ℝ) : ℂ) +
          ((inner ℝ h r : ℝ) : ℂ) * Complex.I)
        ∂(stdGaussian E) =
      (∏ i : Fin n,
          ((Real.sqrt (hD.eigenvalues hn i))⁻¹ : ℂ)) *
        Complex.exp (∑ i : Fin n,
          (-((inner ℝ (hD.eigenvectorBasis hn i) q : ℝ) : ℂ) +
            ((inner ℝ (hD.eigenvectorBasis hn i) r : ℝ) : ℂ) * Complex.I) ^ 2 /
              (2 * hD.eigenvalues hn i)) := by
  let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis hn
  let lambda : Fin n → ℝ := hD.eigenvalues hn
  let d : Fin n → ℂ := fun i =>
    -((inner ℝ (B i) q : ℝ) : ℂ) +
      ((inner ℝ (B i) r : ℝ) : ℂ) * Complex.I
  rw [stdGaussian_eq_map_pi_orthonormalBasis B]
  have hrecon : (fun x : Fin n → ℝ => ∑ i, x i • B i) =
      ⇑((EuclideanSpace.basisFun (Fin n) ℝ).equiv B (Equiv.refl (Fin n))) ∘
        (WithLp.toLp 2) := by
    simp_rw [← B.equiv_apply_euclideanSpace]
    rfl
  have hrecon_meas : Measurable (fun x : Fin n → ℝ => ∑ i, x i • B i) := by
    rw [hrecon]
    exact ((EuclideanSpace.basisFun (Fin n) ℝ).equiv B
      (Equiv.refl (Fin n))).continuous.measurable.comp
        (WithLp.measurable_toLp 2 (Fin n → ℝ))
  rw [integral_map hrecon_meas.aemeasurable (by fun_prop)]
  have hfun : (fun x : Fin n → ℝ => Complex.exp
      (-(((inner ℝ (∑ i, x i • B i)
          ((D - (LinearMap.id : E →ₗ[ℝ] E)) (∑ i, x i • B i)) / 2 : ℝ) : ℂ)) +
        ((-inner ℝ (∑ i, x i • B i) q : ℝ) : ℂ) +
        ((inner ℝ (∑ i, x i • B i) r : ℝ) : ℂ) * Complex.I)) =
      (fun x : Fin n → ℝ => Complex.exp (∑ i,
        (-((((lambda i - 1) / 2 : ℝ) : ℂ)) * (x i : ℂ) ^ 2 +
          d i * x i))) := by
    funext x
    congr 1
    have hmap :
        (D - (LinearMap.id : E →ₗ[ℝ] E)) (∑ i, x i • B i) =
          ∑ i, (x i * (lambda i - 1)) • B i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, LinearMap.sub_apply, LinearMap.id_apply]
      rw [hD.apply_eigenvectorBasis hn]
      dsimp [lambda, B]
      module
    rw [hmap]
    have hquad : inner ℝ (∑ i, x i • B i)
        (∑ i, (x i * (lambda i - 1)) • B i) =
        ∑ i, x i ^ 2 * (lambda i - 1) := by
      simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
        orthonormal_iff_ite.mp B.orthonormal]
      simp
      ring
    rw [hquad]
    have hq : inner ℝ (∑ i, x i • B i) q =
        ∑ i, x i * inner ℝ (B i) q := by
      simp_rw [sum_inner, real_inner_smul_left]
    have hr : inner ℝ (∑ i, x i • B i) r =
        ∑ i, x i * inner ℝ (B i) r := by
      simp_rw [sum_inner, real_inner_smul_left]
    rw [hq, hr]
    dsimp [d]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_neg_distrib,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun]
  rw [integral_cexp_diagonal_tilted_standardGaussian lambda
    (by simpa [lambda] using hpos) d]

/-- Every eigenvalue of `I + T†T` is strictly positive. -/
theorem bilinearGramOperator_eigenvalues_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (T : E →L[ℝ] E) :
    let D : E →ₗ[ℝ] E := LinearMap.id +
      (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
    let hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
      (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
    ∀ i : Fin n, 0 < hD.eigenvalues hn i := by
  dsimp only
  let D : E →ₗ[ℝ] E := LinearMap.id +
    (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
  have hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
    (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
  let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis hn
  intro i
  have heig := hD.apply_eigenvectorBasis hn i
  have hinner : inner ℝ (B i) (D (B i)) = hD.eigenvalues hn i := by
    rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq]
    simp [B]
  rw [← hinner]
  have hDapply : D (B i) = B i +
      LinearMap.adjoint T.toLinearMap (T (B i)) := by
    simp [D]
  rw [hDapply, inner_add_right, LinearMap.adjoint_inner_right]
  have hTself : inner ℝ (T.toLinearMap (B i)) (T (B i)) =
      ‖T (B i)‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [real_inner_self_eq_norm_sq, hTself]
  have hbone : ‖B i‖ = 1 := B.orthonormal.1 i
  rw [hbone]
  positivity

/-- Raw completed-square formula for arbitrary `T,L`, with determinant
normalization written as the product of the eigenvalues of `I + T†T`. -/
theorem bilinearGaussianIntegral_eq_spectral_completedSquare_raw
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) :
    let D : E →ₗ[ℝ] E := LinearMap.id +
      (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
    let hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
      (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
    let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis hn
    let lambda : Fin n → ℝ := hD.eigenvalues hn
    let q : E := LinearMap.adjoint T.toLinearMap (L b)
    bilinearGaussianIntegral T L a b =
      Complex.exp (-((‖L b‖ : ℂ) ^ 2) / 2) *
        ((∏ i : Fin n, ((Real.sqrt (lambda i))⁻¹ : ℂ)) *
          Complex.exp (∑ i : Fin n,
            (-((inner ℝ (B i) q : ℝ) : ℂ) +
              ((inner ℝ (B i) (L a) : ℝ) : ℂ) * Complex.I) ^ 2 /
                (2 * lambda i))) := by
  dsimp only
  let D : E →ₗ[ℝ] E := LinearMap.id +
    (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
  have hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
    (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
  let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis hn
  let lambda : Fin n → ℝ := hD.eigenvalues hn
  let q : E := LinearMap.adjoint T.toLinearMap (L b)
  have hpos : ∀ i : Fin n, 0 < lambda i := by
    simpa [lambda, D, hD] using bilinearGramOperator_eigenvalues_pos hn T
  rw [bilinearGaussianIntegral_eq_integral_after_first]
  have hnorm (h : E) :
      ‖T h + L b‖ ^ 2 = ‖L b‖ ^ 2 +
        inner ℝ h ((D - (LinearMap.id : E →ₗ[ℝ] E)) h) +
        2 * inner ℝ h q := by
    have hDsub : (D - (LinearMap.id : E →ₗ[ℝ] E)) h =
        LinearMap.adjoint T.toLinearMap (T h) := by
      simp [D]
    calc
      ‖T h + L b‖ ^ 2 = inner ℝ (T h + L b) (T h + L b) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ (T h) (T h) + 2 * inner ℝ (T h) (L b) +
          inner ℝ (L b) (L b) := by
        simp only [inner_add_left, inner_add_right]
        rw [real_inner_comm (L b) (T h)]
        ring
      _ = ‖L b‖ ^ 2 +
          inner ℝ h ((D - (LinearMap.id : E →ₗ[ℝ] E)) h) +
          2 * inner ℝ h q := by
        rw [hDsub]
        dsimp [q]
        rw [LinearMap.adjoint_inner_right,
          LinearMap.adjoint_inner_right,
          real_inner_self_eq_norm_sq]
        have hTself : inner ℝ (T.toLinearMap h) (T h) = ‖T h‖ ^ 2 :=
          real_inner_self_eq_norm_sq _
        rw [hTself, real_inner_self_eq_norm_sq]
        have hcross : inner ℝ (T.toLinearMap h) (L b) =
            inner ℝ (T h) (L b) := rfl
        rw [hcross]
        ring
  have hintegrand : (fun h : E =>
      Complex.exp (-((‖T h + L b‖ : ℂ) ^ 2) / 2) *
        Complex.exp (((inner ℝ h (L a) : ℝ) : ℂ) * Complex.I)) =
      (fun h : E =>
        Complex.exp (-((‖L b‖ : ℂ) ^ 2) / 2) *
          Complex.exp
            (-(((inner ℝ h ((D - (LinearMap.id : E →ₗ[ℝ] E)) h) / 2 : ℝ) : ℂ)) +
              ((-inner ℝ h q : ℝ) : ℂ) +
              ((inner ℝ h (L a) : ℝ) : ℂ) * Complex.I)) := by
    funext h
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
    rw [hnorm]
    push_cast
    ring
  rw [hintegrand, integral_const_mul]
  rw [integral_cexp_symmetric_tilted_stdGaussian D hD hn
    (by simpa [lambda] using hpos) q (L a)]

/-- Exact arbitrary-operator normal form: a positive determinant factor,
two real endpoint quadratic forms, and one mixed pure phase. -/
theorem bilinearGaussianIntegral_eq_spectral_completedSquareKernel
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) :
    let D : E →ₗ[ℝ] E := LinearMap.id +
      (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
    let hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
      (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
    let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis hn
    let lambda : Fin n → ℝ := hD.eigenvalues hn
    let q : E := LinearMap.adjoint T.toLinearMap (L b)
    let u : Fin n → ℝ := fun i => inner ℝ (B i) (L a)
    let v : Fin n → ℝ := fun i => inner ℝ (B i) q
    bilinearGaussianIntegral T L a b =
      completedSquareKernel
        (∏ i : Fin n, (Real.sqrt (lambda i))⁻¹)
        (∑ i : Fin n, (u i) ^ 2 / lambda i)
        (‖L b‖ ^ 2 - ∑ i : Fin n, (v i) ^ 2 / lambda i)
        (∑ i : Fin n, v i * u i / lambda i) 1 1 := by
  dsimp only
  let D : E →ₗ[ℝ] E := LinearMap.id +
    (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
  have hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
    (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
  let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis hn
  let lambda : Fin n → ℝ := hD.eigenvalues hn
  let q : E := LinearMap.adjoint T.toLinearMap (L b)
  let u : Fin n → ℝ := fun i => inner ℝ (B i) (L a)
  let v : Fin n → ℝ := fun i => inner ℝ (B i) q
  have hpos : ∀ i : Fin n, 0 < lambda i := by
    simpa [lambda, D, hD] using bilinearGramOperator_eigenvalues_pos hn T
  rw [bilinearGaussianIntegral_eq_spectral_completedSquare_raw hn T L a b]
  unfold completedSquareKernel
  simp only [one_pow, one_mul]
  dsimp [D, hD, B, lambda, q, u, v] at *
  let pref : ℂ := (∏ i : Fin n,
    ((Real.sqrt (hD.eigenvalues hn i))⁻¹ : ℂ))
  let uu : Fin n → ℝ := fun i =>
    inner ℝ (hD.eigenvectorBasis hn i) (L a)
  let vv : Fin n → ℝ := fun i =>
    inner ℝ (hD.eigenvectorBasis hn i)
      (LinearMap.adjoint T.toLinearMap (L b))
  let ll : Fin n → ℝ := hD.eigenvalues hn
  have hpoint : ∀ i : Fin n,
      (-((vv i : ℝ) : ℂ) + ((uu i : ℝ) : ℂ) * Complex.I) ^ 2 /
          (2 * ll i) =
        (((vv i ^ 2 - uu i ^ 2) / (2 * ll i) : ℝ) : ℂ) -
          ((vv i * uu i / ll i : ℝ) : ℂ) * Complex.I := by
    intro i
    have hne : (ll i : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hpos i))
    push_cast
    field_simp [hne]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hhalf_u :
      (∑ i : Fin n, uu i ^ 2 / (2 * ll i)) =
        (∑ i : Fin n, uu i ^ 2 / ll i) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hne : ll i ≠ 0 := ne_of_gt (hpos i)
    field_simp [hne]
  have hhalf_v :
      (∑ i : Fin n, vv i ^ 2 / (2 * ll i)) =
        (∑ i : Fin n, vv i ^ 2 / ll i) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hne : ll i ≠ 0 := ne_of_gt (hpos i)
    field_simp [hne]
  have hpref_cast :
      (((∏ i : Fin n,
          (Real.sqrt (hD.eigenvalues hn i))⁻¹ : ℝ) : ℂ)) = pref := by
    dsimp [pref]
    push_cast
    rfl
  have hhalf_u_complex :
      (∑ i : Fin n, (uu i : ℂ) ^ 2 / (2 * (ll i : ℂ))) =
        (∑ i : Fin n, (uu i : ℂ) ^ 2 / (ll i : ℂ)) / 2 := by
    exact_mod_cast hhalf_u
  have hhalf_v_complex :
      (∑ i : Fin n, (vv i : ℂ) ^ 2 / (2 * (ll i : ℂ))) =
        (∑ i : Fin n, (vv i : ℂ) ^ 2 / (ll i : ℂ)) / 2 := by
    exact_mod_cast hhalf_v
  have hsplit_complex :
      (∑ i : Fin n,
          ((vv i : ℂ) ^ 2 - (uu i : ℂ) ^ 2) / (2 * (ll i : ℂ))) =
        (∑ i : Fin n, (vv i : ℂ) ^ 2 / (2 * (ll i : ℂ))) -
          ∑ i : Fin n, (uu i : ℂ) ^ 2 / (2 * (ll i : ℂ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hpref_cast]
  change Complex.exp (-((‖L b‖ : ℂ) ^ 2) / 2) *
      (pref * Complex.exp (∑ i : Fin n,
        (-((vv i : ℝ) : ℂ) + ((uu i : ℝ) : ℂ) * Complex.I) ^ 2 /
          (2 * ll i))) =
    pref * Complex.exp
      (-(((∑ i : Fin n, uu i ^ 2 / ll i) +
        (‖L b‖ ^ 2 - ∑ i : Fin n, vv i ^ 2 / ll i) : ℝ) : ℂ) / 2) *
      Complex.exp
        (-(((∑ i : Fin n, vv i * uu i / ll i) : ℝ) : ℂ) * Complex.I)
  calc
    Complex.exp (-((‖L b‖ : ℂ) ^ 2) / 2) *
        (pref * Complex.exp (∑ i : Fin n,
          (-((vv i : ℝ) : ℂ) + ((uu i : ℝ) : ℂ) * Complex.I) ^ 2 /
            (2 * ll i))) =
      pref * (Complex.exp (-((‖L b‖ : ℂ) ^ 2) / 2) *
        Complex.exp (∑ i : Fin n,
          (-((vv i : ℝ) : ℂ) + ((uu i : ℝ) : ℂ) * Complex.I) ^ 2 /
            (2 * ll i))) := by ring
    _ = pref * (Complex.exp
        (-(((∑ i : Fin n, uu i ^ 2 / ll i) +
          (‖L b‖ ^ 2 - ∑ i : Fin n, vv i ^ 2 / ll i) : ℝ) : ℂ) / 2) *
        Complex.exp
          (-(((∑ i : Fin n, vv i * uu i / ll i) : ℝ) : ℂ) * Complex.I)) := by
      congr 1
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp_rw [hpoint]
      rw [Finset.sum_sub_distrib]
      push_cast
      rw [hsplit_complex, hhalf_u_complex, hhalf_v_complex]
      ring_nf
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = pref * Complex.exp
        (-(((∑ i : Fin n, uu i ^ 2 / ll i) +
          (‖L b‖ ^ 2 - ∑ i : Fin n, vv i ^ 2 / ll i) : ℝ) : ℂ) / 2) *
        Complex.exp
          (-(((∑ i : Fin n, vv i * uu i / ll i) : ℝ) : ℂ) * Complex.I) := by
      exact (mul_assoc _ _ _).symm

/-- Exact two-coordinate scaling formula for arbitrary `T,L`.  This is the
direct analytic interface used after conditioning on the remainder columns:
the two exposed coefficients enter only through `s²`, `t²`, and the pure
mixed phase `s*t`. -/
theorem bilinearGaussianIntegral_smul_eq_spectral_completedSquareKernel
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) (s t : ℝ) :
    let D : E →ₗ[ℝ] E := LinearMap.id +
      (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
    let hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
      (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
    let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis hn
    let lambda : Fin n → ℝ := hD.eigenvalues hn
    let q : E := LinearMap.adjoint T.toLinearMap (L b)
    let u : Fin n → ℝ := fun i => inner ℝ (B i) (L a)
    let v : Fin n → ℝ := fun i => inner ℝ (B i) q
    bilinearGaussianIntegral T L (s • a) (t • b) =
      completedSquareKernel
        (∏ i : Fin n, (Real.sqrt (lambda i))⁻¹)
        (∑ i : Fin n, (u i) ^ 2 / lambda i)
        (‖L b‖ ^ 2 - ∑ i : Fin n, (v i) ^ 2 / lambda i)
        (∑ i : Fin n, v i * u i / lambda i) s t := by
  dsimp only
  rw [bilinearGaussianIntegral_eq_spectral_completedSquareKernel
    hn T L (s • a) (t • b)]
  unfold completedSquareKernel
  simp only [map_smul, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
  push_cast
  simp only [one_pow, one_mul]
  congr 1
  · congr 1
    apply congrArg Complex.exp
    simp_rw [mul_pow]
    ring_nf
    have habs : (((|t| : ℝ) : ℂ) ^ 2) = (t : ℂ) ^ 2 := by
      exact_mod_cast sq_abs t
    rw [habs]
    rw [Finset.mul_sum, Finset.mul_sum]
    ring_nf
  · apply congrArg Complex.exp
    ring_nf
    congr 1
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Arbitrary `T,L` endpoint positivity and the exact geometric interpolation
identity.  This is the matrix-free form used in the conditional cofactor
argument. -/
theorem bilinearGaussianIntegral_endpoints_pos_and_geometric
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1) :
    (0 < (bilinearGaussianIntegral T L a 0).re ∧
      0 < (bilinearGaussianIntegral T L 0 b).re) ∧
    ‖bilinearGaussianIntegral T L (Real.sqrt theta • a)
        (Real.sqrt (1 - theta) • b)‖ =
      (bilinearGaussianIntegral T L a 0).re ^ theta *
        (bilinearGaussianIntegral T L 0 b).re ^ (1 - theta) := by
  let D : E →ₗ[ℝ] E := LinearMap.id +
    (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
  have hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
    (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
  let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis hn
  let lambda : Fin n → ℝ := hD.eigenvalues hn
  let q : E := LinearMap.adjoint T.toLinearMap (L b)
  let u : Fin n → ℝ := fun i => inner ℝ (B i) (L a)
  let v : Fin n → ℝ := fun i => inner ℝ (B i) q
  let pref : ℝ := ∏ i : Fin n, (Real.sqrt (lambda i))⁻¹
  let qLeft : ℝ := ∑ i : Fin n, (u i) ^ 2 / lambda i
  let qRight : ℝ := ‖L b‖ ^ 2 - ∑ i : Fin n, (v i) ^ 2 / lambda i
  let phase : ℝ := ∑ i : Fin n, v i * u i / lambda i
  have hpos : ∀ i : Fin n, 0 < lambda i := by
    simpa [lambda, D, hD] using bilinearGramOperator_eigenvalues_pos hn T
  have hpref : 0 < pref := by
    dsimp [pref]
    apply Finset.prod_pos
    intro i hi
    exact inv_pos.mpr (Real.sqrt_pos.2 (hpos i))
  have hscaled (s t : ℝ) :
      bilinearGaussianIntegral T L (s • a) (t • b) =
        completedSquareKernel pref qLeft qRight phase s t := by
    simpa [pref, qLeft, qRight, phase, D, hD, B, lambda, q, u, v] using
      bilinearGaussianIntegral_smul_eq_spectral_completedSquareKernel
        hn T L a b s t
  have hleft : bilinearGaussianIntegral T L a 0 =
      (pref * Real.exp (-qLeft / 2) : ℝ) := by
    have h := hscaled 1 0
    rw [completedSquareKernel_left_endpoint] at h
    simpa using h
  have hright : bilinearGaussianIntegral T L 0 b =
      (pref * Real.exp (-qRight / 2) : ℝ) := by
    have h := hscaled 0 1
    rw [completedSquareKernel_right_endpoint] at h
    simpa using h
  constructor
  · constructor
    · rw [hleft]
      simp only [Complex.ofReal_re]
      positivity
    · rw [hright]
      simp only [Complex.ofReal_re]
      positivity
  · calc
      ‖bilinearGaussianIntegral T L (Real.sqrt theta • a)
          (Real.sqrt (1 - theta) • b)‖ =
          ‖completedSquareKernel pref qLeft qRight phase
            (Real.sqrt theta) (Real.sqrt (1 - theta))‖ := by
            rw [hscaled]
      _ = (pref * Real.exp (-qLeft / 2)) ^ theta *
          (pref * Real.exp (-qRight / 2)) ^ (1 - theta) :=
        norm_completedSquareKernel_sqrt_interpolation hpref htheta htheta_one
      _ = (bilinearGaussianIntegral T L a 0).re ^ theta *
          (bilinearGaussianIntegral T L 0 b).re ^ (1 - theta) := by
        rw [hleft, hright]
        simp only [Complex.ofReal_re]

/-- Positive endpoint corollary, separated for direct use. -/
theorem bilinearGaussianIntegral_endpoints_pos
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) :
    0 < (bilinearGaussianIntegral T L a 0).re ∧
      0 < (bilinearGaussianIntegral T L 0 b).re :=
  (bilinearGaussianIntegral_endpoints_pos_and_geometric
    hn T L a b (theta := 0) (by positivity) (by norm_num)).1

/-- Both endpoint kernels are represented by real scalars. -/
theorem bilinearGaussianIntegral_endpoints_eq_real
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) :
    ∃ x y : ℝ, bilinearGaussianIntegral T L a 0 = (x : ℂ) ∧
      bilinearGaussianIntegral T L 0 b = (y : ℂ) := by
  let n := Module.finrank ℝ E
  let D : E →ₗ[ℝ] E := LinearMap.id +
    (LinearMap.adjoint T.toLinearMap ∘ₗ T.toLinearMap)
  have hD : D.IsSymmetric := LinearMap.IsSymmetric.id.add
    (LinearMap.isSymmetric_adjoint_comp_self T.toLinearMap)
  let B : OrthonormalBasis (Fin n) ℝ E := hD.eigenvectorBasis rfl
  let lambda : Fin n → ℝ := hD.eigenvalues rfl
  let q : E := LinearMap.adjoint T.toLinearMap (L b)
  let u : Fin n → ℝ := fun i ↦ inner ℝ (B i) (L a)
  let v : Fin n → ℝ := fun i ↦ inner ℝ (B i) q
  let pref : ℝ := ∏ i : Fin n, (Real.sqrt (lambda i))⁻¹
  let qLeft : ℝ := ∑ i : Fin n, (u i) ^ 2 / lambda i
  let qRight : ℝ := ‖L b‖ ^ 2 - ∑ i : Fin n, (v i) ^ 2 / lambda i
  let phase : ℝ := ∑ i : Fin n, v i * u i / lambda i
  have hscaled (s t : ℝ) :
      bilinearGaussianIntegral T L (s • a) (t • b) =
        completedSquareKernel pref qLeft qRight phase s t := by
    simpa [pref, qLeft, qRight, phase, D, hD, B, lambda, q, u, v] using
      bilinearGaussianIntegral_smul_eq_spectral_completedSquareKernel
        rfl T L a b s t
  have hleft : bilinearGaussianIntegral T L a 0 =
      (pref * Real.exp (-qLeft / 2) : ℝ) := by
    have h := hscaled 1 0
    rw [completedSquareKernel_left_endpoint] at h
    simpa using h
  have hright : bilinearGaussianIntegral T L 0 b =
      (pref * Real.exp (-qRight / 2) : ℝ) := by
    have h := hscaled 0 1
    rw [completedSquareKernel_right_endpoint] at h
    simpa using h
  exact ⟨pref * Real.exp (-qLeft / 2), pref * Real.exp (-qRight / 2),
    hleft, hright⟩

/-- The left endpoint kernel is a real number (indeed a strictly positive
one).  This is useful when integrating endpoint kernels over a remainder
measure. -/
theorem bilinearGaussianIntegral_left_endpoint_im
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a : A) :
    (bilinearGaussianIntegral T L a 0).im = 0 := by
  obtain ⟨x, y, hx, hy⟩ :=
    bilinearGaussianIntegral_endpoints_eq_real T L a (0 : A)
  rw [hx]
  simp

/-- The right endpoint kernel is a real number (indeed a strictly positive
one). -/
theorem bilinearGaussianIntegral_right_endpoint_im
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (b : A) :
    (bilinearGaussianIntegral T L 0 b).im = 0 := by
  obtain ⟨x, y, hx, hy⟩ :=
    bilinearGaussianIntegral_endpoints_eq_real T L (0 : A) b
  rw [hy]
  simp

/-- Exact geometric interpolation corollary, separated for direct use by
Hölder averaging. -/
theorem norm_bilinearGaussianIntegral_sqrt_interpolation
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1) :
    ‖bilinearGaussianIntegral T L (Real.sqrt theta • a)
        (Real.sqrt (1 - theta) • b)‖ =
      (bilinearGaussianIntegral T L a 0).re ^ theta *
        (bilinearGaussianIntegral T L 0 b).re ^ (1 - theta) :=
  (bilinearGaussianIntegral_endpoints_pos_and_geometric
    hn T L a b htheta htheta_one).2

/-- Integrated two-coordinate compression for an arbitrary remainder
measure.  The operator and linear map may depend on the remainder; only the
two positive endpoint functions need to be a.e. measurable. -/
theorem lintegral_norm_bilinearGaussianIntegral_sqrt_le
    {Omega E A : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    (mu : Measure Omega) (T : Omega → E →L[ℝ] E)
    (L : Omega → A →L[ℝ] E) (a b : A)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (hleft : AEMeasurable (fun omega ↦ ENNReal.ofReal
      ((bilinearGaussianIntegral (T omega) (L omega) a 0).re)) mu)
    (hright : AEMeasurable (fun omega ↦ ENNReal.ofReal
      ((bilinearGaussianIntegral (T omega) (L omega) 0 b).re)) mu) :
    ∫⁻ omega, ENNReal.ofReal
        ‖bilinearGaussianIntegral (T omega) (L omega)
          (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)‖ ∂mu ≤
      (∫⁻ omega, ENNReal.ofReal
          ((bilinearGaussianIntegral (T omega) (L omega) a 0).re) ∂mu) ^ theta *
        (∫⁻ omega, ENNReal.ofReal
          ((bilinearGaussianIntegral (T omega) (L omega) 0 b).re) ∂mu) ^
            (1 - theta) := by
  let f : Omega → ENNReal := fun omega ↦ ENNReal.ofReal
    ((bilinearGaussianIntegral (T omega) (L omega) a 0).re)
  let g : Omega → ENNReal := fun omega ↦ ENNReal.ofReal
    ((bilinearGaussianIntegral (T omega) (L omega) 0 b).re)
  calc
    (∫⁻ omega, ENNReal.ofReal
        ‖bilinearGaussianIntegral (T omega) (L omega)
          (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)‖ ∂mu) =
        ∫⁻ omega, f omega ^ theta * g omega ^ (1 - theta) ∂mu := by
      apply lintegral_congr
      intro omega
      have hpos := bilinearGaussianIntegral_endpoints_pos
        hn (T omega) (L omega) a b
      rw [norm_bilinearGaussianIntegral_sqrt_interpolation
        hn (T omega) (L omega) a b htheta htheta_one]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hpos.1.le theta)]
      rw [ENNReal.ofReal_rpow_of_nonneg hpos.1.le htheta,
        ENNReal.ofReal_rpow_of_nonneg hpos.2.le
          (sub_nonneg.mpr htheta_one)]
    _ ≤ (∫⁻ omega, f omega ∂mu) ^ theta *
        (∫⁻ omega, g omega ∂mu) ^ (1 - theta) :=
      lintegral_geometric_interpolation_le mu f g theta
        (by simpa [f] using hleft) (by simpa [g] using hright)
        htheta htheta_one
    _ = _ := by rfl

end

end LogdetLean.GramHafnian
