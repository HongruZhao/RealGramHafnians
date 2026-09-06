import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic
/-!
# The last Gram--Schmidt residual as an orthogonal projection

This is the deterministic link between Rouault's QR factor and the
fixed-subspace Gaussian projection theorem.
-/

namespace LogdetLean

noncomputable section

open InnerProductSpace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Span of the Gram--Schmidt vectors strictly preceding the last element of
a finite tuple. -/
def gramSchmidtPastSpan {n : ℕ} (w : Fin (n + 1) → E) : Submodule ℝ E :=
  Submodule.span ℝ
    (gramSchmidt ℝ w '' Set.Iio (Fin.last n))

/-- The last Gram--Schmidt vector is exactly the projection of the last input
onto the orthogonal complement of the preceding Gram--Schmidt span. -/
theorem gramSchmidt_last_eq_starProjection_orthogonal {n : ℕ}
    (w : Fin (n + 1) → E) :
    gramSchmidt ℝ w (Fin.last n) =
      (gramSchmidtPastSpan w)ᗮ.starProjection (w (Fin.last n)) := by
  let K : Submodule ℝ E := gramSchmidtPastSpan w
  let g : E := gramSchmidt ℝ w (Fin.last n)
  have hg : g ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    have hle : K ≤ LinearMap.ker (innerSL ℝ g).toLinearMap := by
      change Submodule.span ℝ
        (gramSchmidt ℝ w '' Set.Iio (Fin.last n)) ≤
          LinearMap.ker (innerSL ℝ g).toLinearMap
      rw [Submodule.span_le]
      rintro z ⟨i, hi, rfl⟩
      change (innerSL ℝ g) (gramSchmidt ℝ w i) = 0
      change ⟪g, gramSchmidt ℝ w i⟫_ℝ = 0
      exact gramSchmidt_orthogonal ℝ w
        (ne_of_gt hi)
    have hker := hle hy
    rw [LinearMap.mem_ker] at hker
    exact hker
  have hdiff : w (Fin.last n) - g ∈ K := by
    change w (Fin.last n) - gramSchmidt ℝ w (Fin.last n) ∈ K
    rw [gramSchmidt_def]
    rw [sub_sub_cancel]
    apply Submodule.sum_mem
    intro i hi
    rw [starProjection_singleton]
    apply K.smul_mem
    exact Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩
  have hproj : Kᗮ.starProjection (w (Fin.last n)) = g :=
    Kᗮ.eq_starProjection_of_mem_orthogonal hg
      (K.le_orthogonal_orthogonal hdiff)
  simpa [g, K] using hproj.symm

/-- Norm form of the preceding projection identity. -/
theorem norm_gramSchmidt_last_eq_norm_orthogonalProjectionOnto {n : ℕ}
    (w : Fin (n + 1) → E) :
    ‖gramSchmidt ℝ w (Fin.last n)‖ =
      ‖(gramSchmidtPastSpan w)ᗮ.orthogonalProjectionOnto (w (Fin.last n))‖ := by
  rw [gramSchmidt_last_eq_starProjection_orthogonal]
  rfl

omit [FiniteDimensional ℝ E] in
/-- For a linearly independent `(n+1)`-tuple, the preceding
Gram--Schmidt span has dimension exactly `n`. -/
theorem finrank_gramSchmidtPastSpan_eq {n : ℕ} {w : Fin (n + 1) → E}
    (hw : LinearIndependent ℝ w) :
    Module.finrank ℝ (gramSchmidtPastSpan w) = n := by
  let f : Set.Iio (Fin.last n) → E :=
    fun i ↦ gramSchmidt ℝ w i
  have hgs : LinearIndependent ℝ (gramSchmidt ℝ w) :=
    gramSchmidt_linearIndependent hw
  have hf : LinearIndependent ℝ f :=
    hgs.comp Subtype.val Subtype.val_injective
  have hdim := finrank_span_eq_card hf
  have hrange : Set.range f =
      gramSchmidt ℝ w '' Set.Iio (Fin.last n) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hcard : Fintype.card (Set.Iio (Fin.last n)) = n := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_eq_toFinset_card]
    convert Fin.card_Iio (Fin.last n) using 1 <;> simp
  change Module.finrank ℝ
      (Submodule.span ℝ
        (gramSchmidt ℝ w '' Set.Iio (Fin.last n))) = n
  rw [← hrange, hdim, hcard]

/-- Dimension of the residual orthogonal complement. -/
theorem finrank_orthogonal_gramSchmidtPastSpan_eq {m n : ℕ}
    {w : Fin (n + 1) → E} (hw : LinearIndependent ℝ w)
    (hdim : Module.finrank ℝ E = m) :
    Module.finrank ℝ (gramSchmidtPastSpan w)ᗮ = m - n := by
  have hadd := (gramSchmidtPastSpan w).finrank_add_finrank_orthogonal
  rw [finrank_gramSchmidtPastSpan_eq hw, hdim] at hadd
  omega

end

end LogdetLean
