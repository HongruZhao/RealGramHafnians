import LogdetLean.GramHafnian.SymmetricGaussianHafnian.MatrixAssembly
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.EdgeSplitting
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.EdgeMatrixReconstruction
import LogdetLean.GramHafnian.ShiftedAnticoncentration.ConditionalSmallBall
/-!
# Literal last-vertex Gaussian mixture

This file identifies the actual independent-edge hafnian with a Gaussian
linear form after the measure-preserving last-vertex split.  The coefficients
are the literal principal hafnian cofactors of the background matrix.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Order-preserving deletion of the greatest vertex. -/
def withoutLastOrderIso (n : ℕ) :
    Fin n ≃o {j : Fin (n + 1) // j ≠ Fin.last n} where
  toFun j := ⟨j.castSucc, Fin.castSucc_ne_last j⟩
  invFun j := ⟨j.1.1, by
    have hbound := j.1.2
    have hne : j.1.1 ≠ n := by
      intro h
      exact j.2 (Fin.ext h)
    omega⟩
  left_inv j := by apply Fin.ext; rfl
  right_inv j := by apply Subtype.ext; apply Fin.ext; rfl
  map_rel_iff' := by intro a b; rfl

/-- The pair complement left by matching the last vertex with `j` is the
background vertex set with `j` deleted, in the same inherited order. -/
def appendPairComplementOrderIso (n : ℕ) (j : Fin n) :
    {a : Fin n // a ≠ j} ≃o
      TypePerfectMatching.PairComplement (Fin.last n) j.castSucc where
  toFun a := ⟨a.1.castSucc, Fin.castSucc_ne_last a.1,
    fun h ↦ a.2 (Fin.ext (congrArg (fun t : Fin (n + 1) ↦ t.1) h))⟩
  invFun a := ⟨⟨a.1.1, by
    have hbound := a.1.2
    have hne : a.1.1 ≠ n := by
      intro h
      exact a.2.1 (Fin.ext h)
    omega⟩, by
      intro h
      exact a.2.2 (Fin.ext (congrArg (fun t : Fin n ↦ t.1) h))⟩
  left_inv a := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv a := by apply Subtype.ext; apply Fin.ext; rfl
  map_rel_iff' := by intro a b; rfl

theorem hafnianPairCofactor_appendMatrix
    {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) (g : Fin n → R) (j : Fin n) :
    hafnianPairCofactor (appendMatrix A g) (Fin.last n) (withoutLastOrderIso n j) =
      matrixCofactor A j := by
  unfold hafnianPairCofactor matrixCofactor
  have h := typeHafnian_reindex_orderIso (appendPairComplementOrderIso n j)
    (fun a b : TypePerfectMatching.PairComplement (Fin.last n) j.castSucc ↦
      appendMatrix A g a.1 b.1)
  simpa [appendPairComplementOrderIso, withoutLastOrderIso] using h.symm

/-- Exact last-vertex expansion into the literal odd cofactor vector. -/
theorem typeHafnian_appendMatrix_eq_sum
    {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) (g : Fin n → R) :
    typeHafnian (appendMatrix A g) = ∑ j : Fin n, g j * matrixCofactor A j := by
  rw [matrixHafnian_expand_last]
  apply Fintype.sum_equiv (withoutLastOrderIso n).symm
  intro y
  obtain ⟨j, rfl⟩ := (withoutLastOrderIso n).surjective y
  rw [hafnianPairCofactor_appendMatrix]
  simp [withoutLastOrderIso]

/-- The actual hafnian, not an abstract surrogate, is the conditional
circular Gaussian linear form after splitting off the last vertex. -/
theorem edgeHafnian_eq_lastVertexLinearForm {n : ℕ}
    (x : Edge (Fin (n + 1)) → ℂ) :
    edgeHafnian x = conditionalCircularLinearForm edgeCofactor (lastVertexSplit n x) := by
  unfold edgeHafnian
  rw [← appendMatrix_lastVertexSplit n x, typeHafnian_appendMatrix_eq_sum]
  rfl

/-- For every fixed background matrix, the appended hafnian has exactly the
circular Gaussian law with variance equal to the squared cofactor norm.
The equality also includes the degenerate zero-variance case. -/
theorem map_typeHafnian_appendMatrix_gaussian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (standardGaussianProduct (Fin n)).map (fun g ↦ typeHafnian (appendMatrix A g)) =
      circularGaussian.map (fun z : ℂ ↦
        Real.sqrt (circularCoefficientEnergy (matrixCofactor A)) • z) := by
  have hfun : (fun g ↦ typeHafnian (appendMatrix A g)) =
      iidCircularTransposeLinearForm (matrixCofactor A) := by
    funext g
    exact typeHafnian_appendMatrix_eq_sum A g
  rw [hfun]
  exact map_iidCircularTransposeLinearForm_eq_scaled_circular (matrixCofactor A)

/-- Exact pushforward law under the actual independent last-vertex split. -/
theorem edgeHafnianLaw_eq_lastVertexProduct (n : ℕ) :
    edgeHafnianLaw (Fin (n + 1)) =
      ((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n))).map
        (conditionalCircularLinearForm edgeCofactor) := by
  rw [← (measurePreserving_lastVertexSplit n).map_eq,
    Measure.map_map (measurable_conditionalCircularLinearForm measurable_edgeCofactor)
      (measurePreserving_lastVertexSplit n).measurable]
  unfold edgeHafnianLaw
  congr 1
  funext x
  exact edgeHafnian_eq_lastVertexLinearForm x

/-- The sharp shifted-disk estimate for the literal independent-edge
hafnian, conditional only on positivity of its actual odd cofactor energy.
The inverse moment is extended-valued, so no finiteness is presumed. -/
theorem edgeHafnian_smallBall_of_cofactorEnergy_pos (n : ℕ)
    (hpos : ∀ᵐ x ∂edgeGaussian (Fin n), 0 < edgeCofactorEnergy x)
    (z : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (edgeGaussian (Fin (n + 1))) {x | ‖edgeHafnian x - z‖ ≤ rho} ≤
      ENNReal.ofReal (rho ^ 2) *
        ennInverseMoment (edgeGaussian (Fin n)) edgeCofactorEnergy := by
  let s : Set ((Edge (Fin n) → ℂ) × (Fin n → ℂ)) :=
    {p | ‖conditionalCircularLinearForm edgeCofactor p - z‖ ≤ rho}
  have hs : MeasurableSet s := by
    exact measurableSet_le
      ((measurable_conditionalCircularLinearForm measurable_edgeCofactor).sub_const z).norm
      measurable_const
  have hset : {x : Edge (Fin (n + 1)) → ℂ | ‖edgeHafnian x - z‖ ≤ rho} =
      lastVertexSplit n ⁻¹' s := by
    ext x
    change (‖edgeHafnian x - z‖ ≤ rho) ↔
      (‖conditionalCircularLinearForm edgeCofactor (lastVertexSplit n x) - z‖ ≤ rho)
    rw [edgeHafnian_eq_lastVertexLinearForm]
  rw [hset, (measurePreserving_lastVertexSplit n).measure_preimage hs.nullMeasurableSet]
  exact prod_pi_circularGaussian_shiftedSmallBall_le_inverseMoment
    (edgeGaussian (Fin n)) edgeCofactor measurable_edgeCofactor hpos z rho hrho

theorem ae_edgeHafnian_ne_zero_of_energy_pos (n : ℕ)
    (hpos : ∀ᵐ x ∂edgeGaussian (Fin n), 0 < edgeCofactorEnergy x) :
    ∀ᵐ x ∂edgeGaussian (Fin (n + 1)), edgeHafnian x ≠ 0 := by
  have hbound := edgeHafnian_smallBall_of_cofactorEnergy_pos n hpos 0 0 (by norm_num)
  have hzero :
      (edgeGaussian (Fin (n + 1))) {x | ‖edgeHafnian x - 0‖ ≤ 0} = 0 := by
    apply nonpos_iff_eq_zero.mp
    simpa using hbound
  rw [ae_iff]
  simpa using hzero

/-- A canonical cofactor is literally the hafnian of the preceding
principal submatrix, whose independent-edge law is already established. -/
theorem edgeCofactor_last_eq_restrictedHafnian {n : ℕ}
    (x : Edge (Fin (n + 1)) → ℂ) :
    edgeCofactor x (Fin.last n) =
      edgeHafnian (restrictEdges (initialVertexEmbedding n) x) := by
  unfold edgeCofactor edgeHafnian
  rw [matrixOfEdges_restrict]
  have h := typeHafnian_reindex_orderIso (withoutLastOrderIso n)
    (fun a b : {a : Fin (n + 1) // a ≠ Fin.last n} ↦ matrixOfEdges x a.1 b.1)
  simpa [withoutLastOrderIso, initialVertexEmbedding] using h.symm

theorem ae_edgeEnergy_succ_pos_of_hafnian_ne_zero (n : ℕ)
    (hH : ∀ᵐ x ∂edgeGaussian (Fin n), edgeHafnian x ≠ 0) :
    ∀ᵐ x ∂edgeGaussian (Fin (n + 1)), 0 < edgeCofactorEnergy x := by
  have hpull :=
    (measurePreserving_restrictEdges (initialVertexEmbedding n)).quasiMeasurePreserving.ae hH
  filter_upwards [hpull] with x hx
  have hc : edgeCofactor x (Fin.last n) ≠ 0 := by
    rwa [edgeCofactor_last_eq_restrictedHafnian]
  have hs : 0 < ‖edgeCofactor x (Fin.last n)‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hc)
  apply lt_of_lt_of_le hs
  unfold edgeCofactorEnergy
  exact Finset.single_le_sum
    (fun j _hj ↦ sq_nonneg (‖edgeCofactor x j‖)) (Finset.mem_univ _)

/-- Every even-order literal independent-edge Gaussian hafnian is
nonzero almost surely, including the empty hafnian at `n = 0`. -/
theorem ae_edgeHafnian_nonzero_even (n : ℕ) :
    ∀ᵐ x ∂edgeGaussian (Fin (2 * n)), edgeHafnian x ≠ 0 := by
  induction n with
  | zero =>
      apply Filter.Eventually.of_forall
      intro x
      simp [edgeHafnian, typeHafnian_eq_one_of_isEmpty]
  | succ n ih =>
      have hp := ae_edgeEnergy_succ_pos_of_hafnian_ne_zero (2 * n) ih
      have hn := ae_edgeHafnian_ne_zero_of_energy_pos (2 * n + 1) hp
      have hdim : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [hdim]
      exact hn

/-- Positivity of every actual odd cofactor energy.  No inverse-moment,
polynomial-zero-set, or matrix-rank assertion is assumed. -/
theorem ae_edgeCofactorEnergy_pos_odd (n : ℕ) :
    ∀ᵐ x ∂edgeGaussian (Fin (2 * n + 1)), 0 < edgeCofactorEnergy x :=
  ae_edgeEnergy_succ_pos_of_hafnian_ne_zero (2 * n) (ae_edgeHafnian_nonzero_even n)

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
