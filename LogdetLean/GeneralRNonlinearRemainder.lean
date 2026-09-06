import LogdetLean.CorrelationMatrixAlgebra
import LogdetLean.GeneralRDecomposition
import LogdetLean.GeneralRResidualMoments
import LogdetLean.HermiteTailCovariance
/-!
# Shared foundations for the general-R nonlinear remainder

This file formalizes the common-space covariance geometry used in Zhao,
*On the Log Determinant of Sample Correlation Matrices under Gaussianity*,
arXiv:2608.00565v1, Lemma 5.2 (printed p. 11), and in the manuscript
subsection “Construction of the coordinate vectors and the uniform
remainder,” equations `gi-definition`, `gi-covariance`, `Qi-gi`, and
`remainder-var`.

It proves the exact covariance of the Gaussian columns, the universal entry
bound for a correlation matrix, and the deterministic fourth-power sum
bound.  The separate `HermiteResidualProjection` module verifies every
first- and second-chaos coefficient of the particular residual.  This file
then states a transparent, data-carrying Hermite representation predicate and
proves the covariance consequence from it.  The still-missing infinite `L^2`
completeness/Mehler bridge is **not** assumed as an axiom and is not claimed
here.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Module WithLp
open scoped BigOperators MatrixOrder RealInnerProductSpace

namespace CorrelationMatrix

variable {p : ℕ} (R : CorrelationMatrix p)

/-- Every entry of a positive-definite correlation matrix has absolute value
at most one.  For distinct indices the proof takes the `2 x 2` principal
submatrix, whose positive determinant is `1-r_ij^2`. -/
theorem abs_apply_le_one (i j : Fin p) : |R.val i j| ≤ 1 := by
  by_cases hij : i = j
  · subst j
    simp
  · let e : Fin 2 → Fin p := ![i, j]
    have he : Function.Injective e := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [e]
    have hdet : 0 < (R.val.submatrix e e).det :=
      (R.posDef.submatrix he).det_pos
    rw [Matrix.det_fin_two] at hdet
    have hsymm : R.val j i = R.val i j := by
      have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A i j)
        R.transpose_eq
      simpa using h
    simp only [e, Matrix.submatrix_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, R.apply_self, one_mul, hsymm] at hdet
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (R.val i j - 1),
      sq_nonneg (R.val i j + 1)]

/-- The sum of all entry squares is `tr(R^2)`. -/
theorem sum_sq_apply_eq_trace_square :
    ∑ i, ∑ j, (R.val i j) ^ 2 = Matrix.trace (R.val * R.val) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  have hsymm : R.val j i = R.val i j := by
    have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A i j)
      R.transpose_eq
    simpa using h
  rw [hsymm]
  ring

/-- The deterministic fourth-power estimate in the proof of the nonlinear
remainder: `sum r_ij^4 <= p+a_R`. -/
theorem sum_fourth_apply_le_dimension_add_energy :
    ∑ i, ∑ j, (R.val i j) ^ 4 ≤ (p : ℝ) + R.deviationEnergy := by
  calc
    ∑ i, ∑ j, (R.val i j) ^ 4 ≤
        ∑ i, ∑ j, (R.val i j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      have habs := R.abs_apply_le_one i j
      have hsquare : (R.val i j) ^ 2 ≤ 1 := by
        rw [abs_le] at habs
        nlinarith [sq_nonneg (R.val i j - 1),
          sq_nonneg (R.val i j + 1)]
      nlinarith [sq_nonneg (R.val i j),
        sq_nonneg ((R.val i j) ^ 2)]
    _ = Matrix.trace (R.val * R.val) := R.sum_sq_apply_eq_trace_square
    _ = (p : ℝ) + R.deviationEnergy :=
      R.trace_square_eq_dimension_add_energy

end CorrelationMatrix

namespace GeneralRDecomposition

variable {m p : ℕ}

private theorem memLp_correlatedGaussianData_entry
    (R : CorrelationMatrix p) (k : Fin m) (i : Fin p) :
    MemLp (fun x : GaussianData m p ↦ x k i) 2
      (correlatedGaussianDataMeasure m R) := by
  have hident :=
    (measurePreserving_correlatedGaussianData_entry R k i).hasLaw.identDistrib
      (HasLaw.id : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1))
  exact hident.memLp_iff.mpr (memLp_id_gaussianReal' 2 (by simp))

private theorem covariance_correlatedGaussianData_entries
    (R : CorrelationMatrix p) (i j : Fin p) (k l : Fin m) :
    cov[fun x : GaussianData m p ↦ x k i,
      fun x ↦ x l j; correlatedGaussianDataMeasure m R] =
        if k = l then R.val i j else 0 := by
  by_cases hkl : k = l
  · subst l
    simp only
    exact covariance_correlatedGaussianData_entry R k i j
  · rw [if_neg hkl]
    have hrows : iIndepFun
        (fun r : Fin m ↦ fun x : GaussianData m p ↦ x r)
        (correlatedGaussianDataMeasure m R) := by
      unfold correlatedGaussianDataMeasure
      exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
    have hindep : IndepFun
        (fun x : GaussianData m p ↦ x k i)
        (fun x : GaussianData m p ↦ x l j)
        (correlatedGaussianDataMeasure m R) := by
      simpa only [Function.comp_def] using
        (hrows.indepFun hkl).comp
          (show Measurable
              (fun x : CorrelationMatrix.Observation p ↦ x i) by fun_prop)
          (show Measurable
              (fun x : CorrelationMatrix.Observation p ↦ x j) by fun_prop)
    exact hindep.covariance_eq_zero
      (memLp_correlatedGaussianData_entry R k i)
      (memLp_correlatedGaussianData_entry R l j)

/-- Equation `gi-covariance` on the canonical standard-data probability
space: the two Gaussian columns have cross-covariance `r_ij I_m`. -/
theorem covariance_G_apply (R : CorrelationMatrix p)
    (i j : Fin p) (k l : Fin m) :
    cov[fun z : GaussianData m p ↦ G R z i k,
      fun z ↦ G R z j l; standardGaussianDataMeasure m p] =
        if k = l then R.val i j else 0 := by
  have hrows : HasLaw (correlateRows R)
      (correlatedGaussianDataMeasure m R)
      (standardGaussianDataMeasure m p) :=
    ⟨(measurable_correlateRows R).aemeasurable,
      map_correlateRows_standardGaussianDataMeasure R⟩
  have htransfer := hrows.covariance_fun_comp
    (show AEMeasurable (fun x : GaussianData m p ↦ x k i)
      (correlatedGaussianDataMeasure m R) by
        exact (measurePreserving_correlatedGaussianData_entry
          R k i).measurable.aemeasurable)
    (show AEMeasurable (fun x : GaussianData m p ↦ x l j)
      (correlatedGaussianDataMeasure m R) by
        exact (measurePreserving_correlatedGaussianData_entry
          R l j).measurable.aemeasurable)
  simpa [G, Function.comp_def] using htransfer.trans
    (covariance_correlatedGaussianData_entries R i j k l)

/-- The exact missing analytic bridge packaged as transparent data, not as an
axiom: a common nonnegative Hermite-energy tail represents both the pair
covariance and the one-column variance. -/
def HasResidualFourthChaosRepresentation (R : CorrelationMatrix p)
    (i j : Fin p) : Prop :=
  ∃ P : FourthChaosEnergy,
    cov[fun z : GaussianData m p ↦ e_m m (G R z i),
      fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] =
        P.covarianceSeries (R.val i j) ∧
    Var[fun z : GaussianData m p ↦ e_m m (G R z i);
      standardGaussianDataMeasure m p] = P.total

/-- Once the actual Hermite representation is supplied, the exact
fourth-power covariance estimate follows from the compiled series lemma. -/
theorem residual_covariance_nonneg_and_le_fourth
    (R : CorrelationMatrix p) (i j : Fin p)
    (hrep : HasResidualFourthChaosRepresentation (m := m) R i j) :
    0 ≤ cov[fun z : GaussianData m p ↦ e_m m (G R z i),
        fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] ∧
    cov[fun z : GaussianData m p ↦ e_m m (G R z i),
        fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] ≤
      (R.val i j) ^ 4 *
        Var[fun z : GaussianData m p ↦ e_m m (G R z i);
          standardGaussianDataMeasure m p] := by
  obtain ⟨P, hcov, hvar⟩ := hrep
  exact P.covariance_nonneg_and_le_of_representation
    (R.abs_apply_le_one i j) hcov hvar

/-- Conditional assembly of equation `remainder-var`.  Every algebraic and
finite-sum step is proved here; the hypotheses name precisely the two analytic
facts still needed for the particular logarithmic residual: its L2 Hermite
representation and its one-column variance bound. -/
theorem variance_E_R_le_dimension_add_energy_of_fourthChaos
    (hm : 0 < m) (R : CorrelationMatrix p)
    (hmem : ∀ i : Fin p,
      MemLp (fun z : GaussianData m p ↦ e_m m (G R z i)) 2
        (standardGaussianDataMeasure m p))
    (hrep : ∀ i j : Fin p,
      HasResidualFourthChaosRepresentation (m := m) R i j)
    (hvar : ∀ i : Fin p,
      Var[fun z : GaussianData m p ↦ e_m m (G R z i);
        standardGaussianDataMeasure m p] ≤ 4 / (m : ℝ) ^ 2) :
    Var[E_R m R; standardGaussianDataMeasure m p] ≤
      (4 / (m : ℝ) ^ 2) * ((p : ℝ) + R.deviationEnergy) := by
  rw [show E_R m R = fun z ↦ ∑ i, e_m m (G R z i) by
    rfl, variance_fun_sum hmem]
  calc
    ∑ i, ∑ j,
        cov[fun z : GaussianData m p ↦ e_m m (G R z i),
          fun z ↦ e_m m (G R z j); standardGaussianDataMeasure m p] ≤
        ∑ i, ∑ j,
          (4 / (m : ℝ) ^ 2) * (R.val i j) ^ 4 := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      calc
        cov[fun z : GaussianData m p ↦ e_m m (G R z i),
          fun z ↦ e_m m (G R z j);
          standardGaussianDataMeasure m p] ≤
            (R.val i j) ^ 4 *
              Var[fun z : GaussianData m p ↦ e_m m (G R z i);
                standardGaussianDataMeasure m p] :=
          (residual_covariance_nonneg_and_le_fourth R i j (hrep i j)).2
        _ ≤ (R.val i j) ^ 4 * (4 / (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hvar i) (by positivity)
        _ = (4 / (m : ℝ) ^ 2) * (R.val i j) ^ 4 := by ring
    _ = (4 / (m : ℝ) ^ 2) *
        (∑ i, ∑ j, (R.val i j) ^ 4) := by
      simp_rw [Finset.mul_sum]
    _ ≤ (4 / (m : ℝ) ^ 2) *
        ((p : ℝ) + R.deviationEnergy) :=
      mul_le_mul_of_nonneg_left
        R.sum_fourth_apply_le_dimension_add_energy (by positivity)

/-- After the exact Gamma-radial calculation in
`GeneralRResidualMoments`, the actual Hermite/Mehler representation is the
only remaining hypothesis in the general-`R` nonlinear remainder bound. -/
theorem variance_E_R_le_dimension_add_energy_of_fourthChaosRepresentation
    (hm : 0 < m) (R : CorrelationMatrix p)
    (hrep : ∀ i j : Fin p,
      HasResidualFourthChaosRepresentation (m := m) R i j) :
    Var[E_R m R; standardGaussianDataMeasure m p] ≤
      (4 / (m : ℝ) ^ 2) * ((p : ℝ) + R.deviationEnergy) := by
  exact variance_E_R_le_dimension_add_energy_of_fourthChaos hm R
    (fun i ↦ memLp_e_m_G_two hm R i) hrep
    (fun i ↦ variance_e_m_G_le_four_div_sq hm R i)

/-- A completely unconditional fallback bound.  It uses only the verified
one-column variance and positivity of the variance of every pairwise
difference, hence does not exploit the Gaussian cross-correlation structure.
The sharper `p + a_R` bound above still needs the actual Mehler/Hermite
identification. -/
theorem variance_E_R_le_four_mul_dimension_sq (hm : 0 < m)
    (R : CorrelationMatrix p) :
    Var[E_R m R; standardGaussianDataMeasure m p] ≤
      (4 / (m : ℝ) ^ 2) * (p : ℝ) ^ 2 := by
  let X : Fin p → GaussianData m p → ℝ :=
    fun i z ↦ e_m m (G R z i)
  have hmem (i : Fin p) :
      MemLp (X i) 2 (standardGaussianDataMeasure m p) :=
    memLp_e_m_G_two hm R i
  have hcov (i j : Fin p) :
      cov[X i, X j; standardGaussianDataMeasure m p] ≤
        4 / (m : ℝ) ^ 2 := by
    have hdiff := variance_nonneg
      (fun z : GaussianData m p ↦ X i z - X j z)
      (standardGaussianDataMeasure m p)
    rw [variance_fun_sub (hmem i) (hmem j)] at hdiff
    have hi := variance_e_m_G_le_four_div_sq hm R i
    have hj := variance_e_m_G_le_four_div_sq hm R j
    change Var[X i; standardGaussianDataMeasure m p] ≤
      4 / (m : ℝ) ^ 2 at hi
    change Var[X j; standardGaussianDataMeasure m p] ≤
      4 / (m : ℝ) ^ 2 at hj
    linarith
  change Var[fun z ↦ ∑ i, X i z;
    standardGaussianDataMeasure m p] ≤ _
  rw [variance_fun_sum hmem]
  calc
    ∑ i, ∑ j,
        cov[X i, X j; standardGaussianDataMeasure m p] ≤
        ∑ i : Fin p, ∑ _j : Fin p, 4 / (m : ℝ) ^ 2 := by
      exact Finset.sum_le_sum fun i _hi ↦
        Finset.sum_le_sum fun j _hj ↦ hcov i j
    _ = (4 / (m : ℝ) ^ 2) * (p : ℝ) ^ 2 := by
      simp [pow_two]
      ring

end GeneralRDecomposition

end

end LogdetLean
