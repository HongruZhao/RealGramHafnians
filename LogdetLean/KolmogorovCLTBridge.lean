import LogdetLean.KolmogorovDistance
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
/-!
# A Kolmogorov bound implies the CDF form of a central limit theorem

This small module records the precise overlap between a Berry--Esseen theorem
and an ordinary real-valued CLT.  A quantitative Kolmogorov-distance bound
tending to zero immediately gives pointwise convergence of every cumulative
distribution function.  The argument is elementary and is proved directly;
no external probability theorem is imported.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- Every pointwise CDF difference is bounded by Kolmogorov distance. -/
theorem abs_cdf_sub_le_kolmogorovDistance
    (μ ν : Measure ℝ) (x : ℝ) :
    |cdf μ x - cdf ν x| ≤ kolmogorovDistance μ ν := by
  exact point_le_supDistance (fun y ↦ abs_cdf_sub_cdf_le_one μ ν y) x

/-- If the Kolmogorov distance from `μ_i` to `ν` tends to zero, then the CDFs
converge pointwise to the CDF of `ν`.  When `ν` is standard normal, this is the
usual CDF formulation of the central limit theorem. -/
theorem tendsto_cdf_of_tendsto_kolmogorovDistance
    {ι : Type*} {l : Filter ι} (μ : ι → Measure ℝ) (ν : Measure ℝ)
    (hK : Tendsto (fun i ↦ kolmogorovDistance (μ i) ν) l (nhds 0))
    (x : ℝ) :
    Tendsto (fun i ↦ cdf (μ i) x) l (nhds (cdf ν x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ ?_) hK
  simpa [Real.dist_eq] using
    (abs_cdf_sub_le_kolmogorovDistance (μ i) ν x)

/-- A deterministic Berry--Esseen bound whose right-hand side tends to zero
forces the Kolmogorov distance itself to tend to zero. -/
theorem tendsto_kolmogorovDistance_of_bound
    {ι : Type*} {l : Filter ι} (μ : ι → Measure ℝ) (ν : Measure ℝ)
    (rate : ι → ℝ)
    (hbound : ∀ i, kolmogorovDistance (μ i) ν ≤ rate i)
    (hrate : Tendsto rate l (nhds 0)) :
    Tendsto (fun i ↦ kolmogorovDistance (μ i) ν) l (nhds 0) := by
  exact squeeze_zero
    (fun i ↦ kolmogorovDistance_nonneg (μ i) ν)
    hbound hrate

/-- Hence any explicit Berry--Esseen rate tending to zero yields the CDF form
of the CLT.  This is the reusable bridge between the sharp project and the
qualitative null CLT in arXiv:2608.00565v1. -/
theorem tendsto_cdf_of_kolmogorov_bound
    {ι : Type*} {l : Filter ι} (μ : ι → Measure ℝ) (ν : Measure ℝ)
    (rate : ι → ℝ)
    (hbound : ∀ i, kolmogorovDistance (μ i) ν ≤ rate i)
    (hrate : Tendsto rate l (nhds 0)) (x : ℝ) :
    Tendsto (fun i ↦ cdf (μ i) x) l (nhds (cdf ν x)) := by
  exact tendsto_cdf_of_tendsto_kolmogorovDistance μ ν
    (tendsto_kolmogorovDistance_of_bound μ ν rate hbound hrate) x

end

end LogdetLean
