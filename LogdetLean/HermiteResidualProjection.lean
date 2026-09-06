import LogdetLean.HermiteResidualAlgebra
import LogdetLean.GeneralRResidualMoments
/-!
# Verified low-degree Hermite projection of the radial residual

This file formalizes the coefficient-by-coefficient argument on printed
pp. 11--12 of Zhao, arXiv:2608.00565v1.  It proves directly that `e_m` is
orthogonal under standard Gaussian measure to every basis vector of the
first and second Hermite chaoses:

* every coordinate `x_k`;
* every mixed quadratic `x_k x_l`, `k != l`;
* every diagonal quadratic `H_2(x_k)=x_k^2-1`.

The proof constructs coordinate sign flips and transpositions as genuine
linear isometric equivalences, proves that they preserve standard Gaussian
measure, and combines those symmetries with the exact radial moment
calculation in `GeneralRResidualMoments`.

This closes the finite coefficient computation `u_m = J_2 h_m`.  It does not
provide the infinite-dimensional `L^2` completeness of multivariate Hermite
polynomials or the correlated Mehler identity; those remain the exact
analytic bridge needed for the full covariance series (4.4).
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Module WithLp
open scoped BigOperators MatrixOrder RealInnerProductSpace

namespace GeneralRDecomposition

/-! ## Gaussian coordinate symmetries -/

/-- Sign flip of one Euclidean coordinate as a linear isometric equivalence. -/
def flipCoordinateLIE {m : ℕ} (k : Fin m) :
    EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin m ↦ if i = k then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ)

@[simp]
theorem flipCoordinateLIE_apply {m : ℕ} (k : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    flipCoordinateLIE k x = flipCoordinate k x := by
  ext i
  by_cases hi : i = k
  · subst i
    simp [flipCoordinateLIE, flipCoordinate]
  · simp [flipCoordinateLIE, flipCoordinate, hi]

/-- A coordinate sign flip preserves the standard multivariate Gaussian. -/
theorem measurePreserving_flipCoordinateLIE {m : ℕ} (k : Fin m) :
    MeasurePreserving (flipCoordinateLIE k)
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
  ⟨(flipCoordinateLIE k).continuous.measurable,
    stdGaussian_map (flipCoordinateLIE k)⟩

/-- Transposition of two Euclidean coordinates as a linear isometric
equivalence. -/
def swapCoordinateLIE {m : ℕ} (k l : Fin m) :
    EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap k l)

/-- A coordinate transposition preserves the standard multivariate Gaussian. -/
theorem measurePreserving_swapCoordinateLIE {m : ℕ} (k l : Fin m) :
    MeasurePreserving (swapCoordinateLIE k l)
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
  ⟨(swapCoordinateLIE k l).continuous.measurable,
    stdGaussian_map (swapCoordinateLIE k l)⟩

@[simp]
theorem swapCoordinateLIE_apply_left {m : ℕ} (k l : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    swapCoordinateLIE k l x k = x l := by
  simp [swapCoordinateLIE, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', Equiv.swap_apply_def]

@[simp]
theorem swapCoordinateLIE_apply_right {m : ℕ} (k l : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    swapCoordinateLIE k l x l = x k := by
  change x ((Equiv.swap k l).symm l) = x k
  rw [Equiv.symm_swap, Equiv.swap_apply_right]

@[simp]
theorem e_m_swapCoordinateLIE {m : ℕ} (k l : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    e_m m (swapCoordinateLIE k l x) = e_m m x := by
  simp only [e_m, h_m, u_m, (swapCoordinateLIE k l).norm_map]

/-! ## Square integrability on standard Gaussian space -/

/-- The already verified common-space `L^2` result transported back to the
standard Gaussian law. -/
theorem memLp_e_m_stdGaussian_two {m : ℕ} (hm : 0 < m) :
    MemLp (e_m m) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  let R : CorrelationMatrix 1 := CorrelationMatrix.identity 1
  let i : Fin 1 := 0
  have hG := hasLaw_G_stdGaussian (m := m) R i
  have hid : HasLaw (id : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m))
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := HasLaw.id
  have hident := hG.identDistrib hid
  have heident := hident.comp (measurable_e_m m)
  exact heident.memLp_iff.mp (memLp_e_m_G_two hm R i)

/-- Every coordinatewise `H_2` polynomial belongs to Gaussian `L^2`. -/
theorem memLp_hermite_two_coordinate {m : ℕ} (k : Fin m) :
    MemLp (fun x : EuclideanSpace ℝ (Fin m) ↦ x k ^ 2 - 1) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have hid4 : MemLp (id : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m)) 4
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    IsGaussian.memLp_id _ 4 (by simp)
  have hk4 : MemLp (fun x : EuclideanSpace ℝ (Fin m) ↦ x k) 4
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    simpa [Function.comp_def] using
      hid4.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) k)
  have htriple : ENNReal.HolderTriple 4 4 2 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := htriple
  have hsq : MemLp (fun x : EuclideanSpace ℝ (Fin m) ↦ x k * x k) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := hk4.mul' hk4
  apply (hsq.sub (memLp_const 1)).ae_eq
  filter_upwards [] with x
  simp only [Pi.sub_apply, pow_two]

/-! ## Exact first- and second-chaos coefficient vanishings -/

/-- The residual is orthogonal to every first-chaos coordinate. -/
theorem integral_e_m_mul_coordinate_eq_zero {m : ℕ} (k : Fin m) :
    ∫ x, e_m m x * x k
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0 := by
  let T := flipCoordinateLIE k
  have hinv := (measurePreserving_flipCoordinateLIE k).integral_comp
    T.toHomeomorph.measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin m) ↦ e_m m x * x k)
  have hTf (x : EuclideanSpace ℝ (Fin m)) :
      e_m m (T x) * T x k = -(e_m m x * x k) := by
    rw [show T x = flipCoordinate k x by
      exact flipCoordinateLIE_apply k x]
    rw [e_m_flipCoordinate, flipCoordinate_apply_same]
    ring
  rw [show (fun x : EuclideanSpace ℝ (Fin m) ↦ e_m m (T x) * T x k) =
      (fun x ↦ -(e_m m x * x k)) by funext x; exact hTf x,
    integral_neg] at hinv
  linarith

/-- Every mixed quadratic Hermite coefficient of the residual vanishes. -/
theorem integral_e_m_mul_mixed_second_eq_zero {m : ℕ}
    (k l : Fin m) (hkl : k ≠ l) :
    ∫ x, e_m m x * (x k * x l)
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0 := by
  let T := flipCoordinateLIE k
  have hinv := (measurePreserving_flipCoordinateLIE k).integral_comp
    T.toHomeomorph.measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin m) ↦ e_m m x * (x k * x l))
  have hTk (x : EuclideanSpace ℝ (Fin m)) : T x k = -x k := by
    simp [T, flipCoordinateLIE]
  have hTl (x : EuclideanSpace ℝ (Fin m)) : T x l = x l := by
    simp [T, flipCoordinateLIE, hkl.symm]
  have hTe (x : EuclideanSpace ℝ (Fin m)) : e_m m (T x) = e_m m x := by
    rw [show T x = flipCoordinate k x by
      exact flipCoordinateLIE_apply k x]
    exact e_m_flipCoordinate k x
  rw [show (fun x : EuclideanSpace ℝ (Fin m) ↦
      e_m m (T x) * (T x k * T x l)) =
      (fun x ↦ -(e_m m x * (x k * x l))) by
        funext x
        rw [hTe, hTk, hTl]
        ring,
    integral_neg] at hinv
  linarith

/-- Exchangeability makes every diagonal `H_2` coefficient identical. -/
theorem integral_e_m_mul_hermite_two_coordinate_eq
    {m : ℕ} (k l : Fin m) :
    (∫ x, e_m m x * (x k ^ 2 - 1)
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      ∫ x, e_m m x * (x l ^ 2 - 1)
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let T := swapCoordinateLIE k l
  have hinv := (measurePreserving_swapCoordinateLIE k l).integral_comp
    T.toHomeomorph.measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin m) ↦ e_m m x * (x k ^ 2 - 1))
  rw [show (fun x : EuclideanSpace ℝ (Fin m) ↦
      e_m m (T x) * (T x k ^ 2 - 1)) =
      (fun x ↦ e_m m x * (x l ^ 2 - 1)) by
        funext x
        rw [e_m_swapCoordinateLIE, swapCoordinateLIE_apply_left]] at hinv
  exact hinv.symm

/-- The residual is orthogonal to its radial second-chaos candidate under the
standard Gaussian law. -/
theorem integral_e_m_mul_u_m_stdGaussian_eq_zero {m : ℕ} (hm : 0 < m) :
    ∫ x, e_m m x * u_m m x
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0 := by
  let R : CorrelationMatrix 1 := CorrelationMatrix.identity 1
  let i : Fin 1 := 0
  have hG := hasLaw_G_stdGaussian (m := m) R i
  have h := hG.integral_comp
    (((measurable_e_m m).mul (measurable_u_m m)).aestronglyMeasurable)
  change (∫ z, e_m m (G R z i) * u_m m (G R z i)
    ∂standardGaussianDataMeasure m 1) = _ at h
  rw [integral_e_m_G_mul_u_m_G_eq_zero hm R i] at h
  exact h.symm

/-- Every diagonal quadratic Hermite coefficient of the residual vanishes.
Together with `integral_e_m_mul_mixed_second_eq_zero`, this is the complete
coefficient-level statement that `u_m` is the second-chaos projection of
`h_m`. -/
theorem integral_e_m_mul_hermite_two_coordinate_eq_zero
    {m : ℕ} (hm : 0 < m) (k : Fin m) :
    ∫ x, e_m m x * (x k ^ 2 - 1)
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0 := by
  let I : Fin m → ℝ := fun l ↦
    ∫ x, e_m m x * (x l ^ 2 - 1)
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))
  have heLp := memLp_e_m_stdGaussian_two hm
  have hint (l : Fin m) : Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦
      e_m m x * (x l ^ 2 - 1))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    MemLp.integrable_mul heLp (memLp_hermite_two_coordinate l)
  have hsum : ∑ l, I l = 0 := by
    calc
      ∑ l, I l = ∫ x, ∑ l, e_m m x * (x l ^ 2 - 1)
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
        rw [integral_finsetSum Finset.univ fun l _ ↦ hint l]
      _ = ∫ x, (m : ℝ) * (e_m m x * u_m m x)
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← Finset.mul_sum]
        have hu := u_m_eq_average_hermite_two m x
        simp only [probabilistsHermiteEval_two] at hu
        have hm0 : (m : ℝ) ≠ 0 := by positivity
        field_simp at hu
        rw [← hu]
        ring
      _ = (m : ℝ) * ∫ x, e_m m x * u_m m x
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
        rw [integral_const_mul]
      _ = 0 := by
        rw [integral_e_m_mul_u_m_stdGaussian_eq_zero hm, mul_zero]
  have hall (l : Fin m) : I l = I k := by
    unfold I
    exact integral_e_m_mul_hermite_two_coordinate_eq l k
  have hmk : (m : ℝ) * I k = 0 := by
    rw [← hsum]
    simp_rw [hall]
    simp
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  change I k = 0
  exact (mul_eq_zero.mp hmk).resolve_left hm0

end GeneralRDecomposition

end
end LogdetLean
