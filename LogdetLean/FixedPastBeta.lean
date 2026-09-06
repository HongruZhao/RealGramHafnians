import LogdetLean.FixedSubspaceGaussian
import LogdetLean.SequentialBeta
/-!
# Fixed-past Beta law for normalized Gram factors

This file joins the deterministic Gram--Schmidt factorization to the
fixed-subspace Gaussian Beta theorem.  For a fixed linearly independent past
of length `n < m`, the next normalized-Gram determinant ratio has a law that
does not depend on the past: it is the stage-`n` measure used by the
sequential product-law theorem.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Gram--Schmidt span preceding a newly appended last vector is exactly
the span of the fixed past; in particular, it does not depend on the new
vector. -/
theorem gramSchmidtPastSpan_snoc_eq_span_range {n : ℕ}
    (v : Fin n → E) (x : E) :
    gramSchmidtPastSpan (Fin.snoc v x) =
      Submodule.span ℝ (Set.range v) := by
  rw [gramSchmidtPastSpan, InnerProductSpace.span_gramSchmidt_Iio]
  congr 1
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hilast : i ≠ Fin.last n := Fin.ne_of_lt hi
    let j : Fin n := i.castPred hilast
    refine ⟨j, ?_⟩
    simpa [j] using
      (@Fin.snoc_castSucc n (fun _ : Fin (n + 1) ↦ E) x v j).symm
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.castSucc_lt_last,
      @Fin.snoc_castSucc n (fun _ : Fin (n + 1) ↦ E) x v j⟩

/-- **Fixed-past one-step law.**  In an `m`-dimensional real Gaussian space,
for every fixed linearly independent past of length `n < m`, the next
normalized-Gram determinant factor has exactly
`gaussianGramSchmidtFactorMeasure m n`.  This includes `n=0`, where the law
is the point mass at one. -/
theorem map_nestedNormalizedGramFactor_stdGaussian_fixedPast
    (m n : ℕ) (hdim : Module.finrank ℝ E = m)
    (past : NestedTuple E n)
    (hpast : LinearIndependent ℝ (nestedTupleToFin n past))
    (hnm : n < m) :
    Measure.map (nestedNormalizedGramFactor (E := E) n past)
        (stdGaussian E) = gaussianGramSchmidtFactorMeasure m n := by
  let v : Fin n → E := nestedTupleToFin n past
  have hnrank : n < Module.finrank ℝ E := by omega
  have hfull : ∀ᵐ x ∂(stdGaussian E),
      LinearIndependent ℝ (Fin.snoc v x) :=
    ae_linearIndependent_snoc_stdGaussian hpast hnrank
  cases n with
  | zero =>
      have hone : (nestedNormalizedGramFactor (E := E) 0 past) =ᵐ[(stdGaussian E)]
          (fun _ ↦ (1 : ℝ)) := by
        filter_upwards [hfull] with x hx
        rw [nestedNormalizedGramFactor_eq_orthogonalProjection past x hx,
          gramSchmidtPastSpan_snoc_eq_span_range v x]
        have hx0 : x ≠ 0 := by
          intro hzero
          apply hx.ne_zero (Fin.last 0)
          subst x
          simpa using
            (@Fin.snoc_last 0 (fun _ : Fin 1 ↦ E) (0 : E) v)
        simp [v]
        rw [Submodule.starProjection_top]
        exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0))
      calc
        Measure.map (nestedNormalizedGramFactor (E := E) 0 past) (stdGaussian E) =
            Measure.map (fun _ : E ↦ (1 : ℝ)) (stdGaussian E) :=
          Measure.map_congr hone
        _ = Measure.dirac 1 := by simp
        _ = gaussianGramSchmidtFactorMeasure m 0 := rfl
  | succ k =>
      let S : Submodule ℝ E := Submodule.span ℝ (Set.range v)
      have hfinS : Module.finrank ℝ S = k + 1 := by
        simpa [S, v] using finrank_span_eq_card hpast
      have hfinPerp : Module.finrank ℝ Sᗮ = m - (k + 1) := by
        have hadd := S.finrank_add_finrank_orthogonal
        rw [hfinS, hdim] at hadd
        omega
      let _ : Nontrivial S :=
        Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ S)
      let _ : Nontrivial Sᗮ :=
        Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ Sᗮ)
      let _ : Nontrivial Sᗮᗮ := by
        rw [S.orthogonal_orthogonal]
        infer_instance
      have hbeta := hasLaw_orthogonalProjection_normSq_ratio_beta (K := Sᗮ)
      have hfinDouble : Module.finrank ℝ Sᗮᗮ = k + 1 := by
        rw [S.orthogonal_orthogonal, hfinS]
      have hratio : HasLaw
          (fun x : E ↦ ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 / ‖x‖ ^ 2)
          (betaMeasure (((m - (k + 1) : ℕ) : ℝ) / 2)
            (((k + 1 : ℕ) : ℝ) / 2))
          (stdGaussian E) := by
        rw [hfinPerp, hfinDouble] at hbeta
        exact hbeta
      have heq : (nestedNormalizedGramFactor (E := E) (k + 1) past) =ᵐ[(stdGaussian E)]
          (fun x : E ↦ ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 / ‖x‖ ^ 2) := by
        filter_upwards [hfull] with x hx
        rw [nestedNormalizedGramFactor_eq_orthogonalProjection past x hx,
          gramSchmidtPastSpan_snoc_eq_span_range v x]
      calc
        Measure.map (nestedNormalizedGramFactor (E := E) (k + 1) past)
            (stdGaussian E) =
            Measure.map
              (fun x : E ↦ ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2 / ‖x‖ ^ 2)
              (stdGaussian E) := Measure.map_congr heq
        _ = betaMeasure (((m - (k + 1) : ℕ) : ℝ) / 2)
              (((k + 1 : ℕ) : ℝ) / 2) := hratio.map_eq
        _ = gaussianGramSchmidtFactorMeasure m (k + 1) := rfl

end

end LogdetLean
