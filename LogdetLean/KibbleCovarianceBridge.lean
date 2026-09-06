import LogdetLean.GeneralRFrullaniLaplace
import LogdetLean.GeneralRExactVarianceSeries
/-!
# Exact boundary of the Kibble probability bridge

`GeneralRFrullaniLaplace` proves that one explicit compact-window scalar
integral converges to the actual covariance of two Gaussian log radii.  This
file names the remaining scalar limit certificate and proves that it transfers
to the actual covariance, then assembles the actual `tau_R^2` formula from
the classical Bartlett/Schur determinant moment inputs.

No scalar limit or Wishart moment is postulated as an axiom: every still-open
input is an ordinary hypothesis of the transfer theorem.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Interval

/-- The compact Frullani window whose limit is the Kibble covariance. -/
def kibbleWindowIntegral (m : ℕ) (rho : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
    ∫ t in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
      GeneralRDecomposition.weightedPairCovarianceKernel m rho s t

/-- The one faithful scalar analytic obligation left after the common-space
Frullani/Fubini bridge: evaluate the compact-window limit as the coefficient
series. -/
def KibbleScalarLimitCertificate (m : ℕ) (rho : ℝ) : Prop :=
  Tendsto (kibbleWindowIntegral m rho) atTop
    (nhds (logRadiusCovarianceSeries m rho))

/-- A scalar limit certificate identifies the actual common-space log-radius
covariance with the Kibble series. -/
theorem covariance_log_Q_eq_logRadiusCovarianceSeries_of_scalarLimit
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p)
    (hlimit : KibbleScalarLimitCertificate m (R.val i j)) :
    cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
        fun z ↦ Real.log (GeneralRDecomposition.Q R z j);
        standardGaussianDataMeasure m p] =
      logRadiusCovarianceSeries m (R.val i j) := by
  have hactual :=
    GeneralRDecomposition.tendsto_double_kernel_eq_covariance_log_Q hm R i j
  unfold KibbleScalarLimitCertificate kibbleWindowIntegral at hlimit
  exact tendsto_nhds_unique hactual hlimit

/-- The actual diagonal log-radius covariance is already closed, without the
scalar Kibble limit, by the exact Gamma log-variance theorem. -/
theorem covariance_log_Q_self_eq_trigamma
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) (i : Fin p) :
    cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
        fun z ↦ Real.log (GeneralRDecomposition.Q R z i);
        standardGaussianDataMeasure m p] =
      trigammaSeries ((m : ℝ) / 2) := by
  rw [covariance_self]
  · exact GeneralRDecomposition.variance_log_Q_eq_trigamma hm R i
  · exact (GeneralRDecomposition.measurable_Q R i).log.aemeasurable

/-- The uncentered random numerator whose variance is denoted `tau_R^2`.
Adding population and expectation constants does not change its variance. -/
def generalRLogDetNumerator {m p : ℕ} (R : CorrelationMatrix p) :
    GaussianData m p → ℝ := fun z ↦
  Real.log (GeneralRDecomposition.W0 z).det -
    ∑ i : Fin p, Real.log (GeneralRDecomposition.Q R z i)

/-- Exact actual-variance assembly.  Its remaining hypotheses are precisely
the Bartlett determinant variance, the Schur-complement covariance, and the
scalar Kibble limit for off-diagonal pairs. -/
theorem variance_generalRLogDetNumerator_eq_exactVarianceSeries
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p)
    (hW : MemLp (fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det) 2
      (standardGaussianDataMeasure m p))
    (hvarW : Var[fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det;
        standardGaussianDataMeasure m p] =
      nullVSeries m p + (p : ℝ) * trigammaSeries ((m : ℝ) / 2))
    (hcovW : ∀ i : Fin p,
      cov[fun z : GaussianData m p ↦
          Real.log (GeneralRDecomposition.W0 z).det,
        fun z ↦ Real.log (GeneralRDecomposition.Q R z i);
        standardGaussianDataMeasure m p] =
          trigammaSeries ((m : ℝ) / 2))
    (hlimit : ∀ i j : Fin p, i ≠ j →
      KibbleScalarLimitCertificate m (R.val i j)) :
    Var[generalRLogDetNumerator R;
        standardGaussianDataMeasure m p] =
      generalRExactVarianceSeries m R := by
  let L : GaussianData m p → ℝ := fun z ↦
    Real.log (GeneralRDecomposition.W0 z).det
  let q : Fin p → GaussianData m p → ℝ := fun i z ↦
    Real.log (GeneralRDecomposition.Q R z i)
  have hq : ∀ i : Fin p, MemLp (q i) 2
      (standardGaussianDataMeasure m p) := by
    intro i
    exact GeneralRDecomposition.memLp_log_Q_two hm R i
  have hpair : ∀ i j : Fin p,
      cov[q i, q j;
          standardGaussianDataMeasure m p] =
        if i = j then trigammaSeries ((m : ℝ) / 2)
        else logRadiusCovarianceSeries m (R.val i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact covariance_log_Q_self_eq_trigamma hm R i
    · rw [if_neg hij]
      exact covariance_log_Q_eq_logRadiusCovarianceSeries_of_scalarLimit
        hm R i j (hlimit i j hij)
  have hassembly := variance_sub_finsetSum_eq_base_add_offDiag
    L q (nullVSeries m p) (trigammaSeries ((m : ℝ) / 2))
      (fun i j ↦ logRadiusCovarianceSeries m (R.val i j))
    hW hq (by simpa [L] using hvarW) (by simpa [L, q] using hcovW) hpair
  change Var[fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det -
        ∑ i : Fin p, Real.log (GeneralRDecomposition.Q R z i);
      standardGaussianDataMeasure m p] = generalRExactVarianceSeries m R
  simpa [generalRExactVarianceSeries, L, q] using hassembly

/-- Once the three explicit model bridges above are supplied, the actual
variance inherits the sharp deterministic proxy comparison. -/
theorem variance_generalRLogDetNumerator_proxy_bounds
    {m p : ℕ} (hm : 2 ≤ m) (R : CorrelationMatrix p)
    (hW : MemLp (fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det) 2
      (standardGaussianDataMeasure m p))
    (hvarW : Var[fun z : GaussianData m p ↦
        Real.log (GeneralRDecomposition.W0 z).det;
        standardGaussianDataMeasure m p] =
      nullVSeries m p + (p : ℝ) * trigammaSeries ((m : ℝ) / 2))
    (hcovW : ∀ i : Fin p,
      cov[fun z : GaussianData m p ↦
          Real.log (GeneralRDecomposition.W0 z).det,
        fun z ↦ Real.log (GeneralRDecomposition.Q R z i);
        standardGaussianDataMeasure m p] =
          trigammaSeries ((m : ℝ) / 2))
    (hlimit : ∀ i j : Fin p, i ≠ j →
      KibbleScalarLimitCertificate m (R.val i j)) :
    0 ≤ Var[generalRLogDetNumerator R;
          standardGaussianDataMeasure m p] -
        generalRSeriesVarianceProxy m R ∧
      Var[generalRLogDetNumerator R;
          standardGaussianDataMeasure m p] -
        generalRSeriesVarianceProxy m R ≤
          4 * R.deviationEnergy / (m : ℝ) ^ 2 := by
  apply variance_proxy_bounds_of_eq_generalRExactVarianceSeries hm R
  exact variance_generalRLogDetNumerator_eq_exactVarianceSeries
    (by omega) R hW hvarW hcovW hlimit

end

end LogdetLean
