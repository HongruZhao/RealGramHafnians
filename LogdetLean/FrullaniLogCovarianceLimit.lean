import LogdetLean.GeneralRRadialMoments
import LogdetLean.FrullaniLogTruncation
/-! Dominated-convergence transfer from Frullani truncations to log-energy covariance. -/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology Interval

noncomputable section

namespace LogdetLean

def frullaniLogApprox (n : ℕ) (q : ℝ) : ℝ :=
  frullaniLogTrunc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) q

@[fun_prop]
lemma measurable_frullaniLogApprox (n : ℕ) :
    Measurable (frullaniLogApprox n) :=
  measurable_frullaniLogTrunc _ _

lemma frullaniApprox_eps_pos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity

lemma frullaniApprox_eps_le_T (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
  nlinarith [sq_nonneg ((n : ℝ) + 1)]

lemma tendsto_frullaniLogApprox {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n : ℕ ↦ frullaniLogApprox n q) atTop
      (nhds (Real.log q)) := by
  have hpair : Tendsto
      (fun n : ℕ ↦ (1 / ((n : ℝ) + 1), (n : ℝ) + 1)) atTop
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop) := by
    apply Filter.Tendsto.prodMk
    · refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
      · filter_upwards [] with n
        exact frullaniApprox_eps_pos n
    · exact tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
  exact ((tendsto_frullaniLogTrunc hq).comp hpair).congr'
    (Eventually.of_forall fun _n ↦ rfl)

lemma abs_frullaniLogApprox_le_abs_log (n : ℕ) {q : ℝ} (hq : 0 < q) :
    |frullaniLogApprox n q| ≤ |Real.log q| := by
  exact abs_frullaniLogTrunc_le_abs_log
    (frullaniApprox_eps_pos n) (frullaniApprox_eps_le_T n) hq

namespace GeneralRDecomposition

variable {m p : ℕ}

lemma gammaMeasure_Iic_zero (a r : ℝ) : gammaMeasure a r (Iic 0) = 0 := by
  have hset : Iic (0 : ℝ) = Iio 0 ∪ {0} := by
    ext x
    simp [le_iff_lt_or_eq]
  rw [hset]
  rw [measure_union_null]
  · rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos (le_refl 0)
  · simp [gammaMeasure]

lemma ae_Q_pos_of_m_pos (hm : 0 < m) (R : CorrelationMatrix p) (i : Fin p) :
    ∀ᵐ z ∂standardGaussianDataMeasure m p, 0 < Q R z i := by
  apply (hasLaw_Q_gamma hm R i).ae_iff
    (by fun_prop : Measurable fun q : ℝ ↦ 0 < q) |>.2
  rw [ae_iff]
  rw [show {a : ℝ | ¬ 0 < a} = Iic 0 by ext a; simp]
  exact gammaMeasure_Iic_zero _ _

lemma tendsto_integral_frullaniLogApprox_Q (hm : 0 < m)
    (R : CorrelationMatrix p) (i : Fin p) :
    Tendsto (fun n : ℕ ↦ ∫ z, frullaniLogApprox n (Q R z i)
        ∂standardGaussianDataMeasure m p) atTop
      (nhds (∫ z, Real.log (Q R z i)
        ∂standardGaussianDataMeasure m p)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun z ↦ |Real.log (Q R z i)|)
  · intro n
    exact ((measurable_frullaniLogApprox n).comp
      (measurable_Q R i)).aestronglyMeasurable
  · exact (integrable_log_Q hm R i).abs
  · intro n
    filter_upwards [ae_Q_pos_of_m_pos hm R i] with z hz
    rw [Real.norm_eq_abs]
    exact abs_frullaniLogApprox_le_abs_log n hz
  · filter_upwards [ae_Q_pos_of_m_pos hm R i] with z hz
    exact tendsto_frullaniLogApprox hz

lemma tendsto_integral_frullaniLogApprox_Q_mul
    (hm : 0 < m) (R : CorrelationMatrix p) (i j : Fin p) :
    Tendsto (fun n : ℕ ↦ ∫ z,
        frullaniLogApprox n (Q R z i) * frullaniLogApprox n (Q R z j)
        ∂standardGaussianDataMeasure m p) atTop
      (nhds (∫ z, Real.log (Q R z i) * Real.log (Q R z j)
        ∂standardGaussianDataMeasure m p)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun z ↦ |Real.log (Q R z i)| * |Real.log (Q R z j)|)
  · intro n
    exact (((measurable_frullaniLogApprox n).comp
      (measurable_Q R i)).mul ((measurable_frullaniLogApprox n).comp
      (measurable_Q R j))).aestronglyMeasurable
  · have hmul := MemLp.integrable_mul
      (memLp_log_Q_two hm R i) (memLp_log_Q_two hm R j)
    simpa [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using hmul.norm
  · intro n
    filter_upwards [ae_Q_pos_of_m_pos hm R i,
      ae_Q_pos_of_m_pos hm R j] with z hzi hzj
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul
      (abs_frullaniLogApprox_le_abs_log n hzi)
      (abs_frullaniLogApprox_le_abs_log n hzj)
      (abs_nonneg _) (abs_nonneg _)
  · filter_upwards [ae_Q_pos_of_m_pos hm R i,
      ae_Q_pos_of_m_pos hm R j] with z hzi hzj
    exact (tendsto_frullaniLogApprox hzi).mul
      (tendsto_frullaniLogApprox hzj)

def frullaniQApprox (n : ℕ) (R : CorrelationMatrix p) (i : Fin p) :
    GaussianData m p → ℝ := fun z ↦ frullaniLogApprox n (Q R z i)

@[fun_prop]
lemma measurable_frullaniQApprox (n : ℕ) (R : CorrelationMatrix p)
    (i : Fin p) : Measurable (frullaniQApprox (m := m) n R i) := by
  exact (measurable_frullaniLogApprox n).comp (measurable_Q R i)

lemma memLp_frullaniQApprox_two (hm : 0 < m)
    (n : ℕ) (R : CorrelationMatrix p) (i : Fin p) :
    MemLp (frullaniQApprox (m := m) n R i) 2
      (standardGaussianDataMeasure m p) := by
  apply (memLp_log_Q_two hm R i).of_le
  · exact (by fun_prop : AEStronglyMeasurable
      (frullaniQApprox (m := m) n R i)
      (standardGaussianDataMeasure m p))
  · filter_upwards [ae_Q_pos_of_m_pos hm R i] with z hz
    simp only [frullaniQApprox, Real.norm_eq_abs]
    exact abs_frullaniLogApprox_le_abs_log n hz

lemma tendsto_covariance_frullaniQApprox (hm : 0 < m)
    (R : CorrelationMatrix p) (i j : Fin p) :
    Tendsto (fun n : ℕ ↦ cov[frullaniQApprox (m := m) n R i,
        frullaniQApprox (m := m) n R j;
        standardGaussianDataMeasure m p]) atTop
      (nhds (cov[fun z ↦ Real.log (Q R z i),
        fun z ↦ Real.log (Q R z j);
        standardGaussianDataMeasure m p])) := by
  have hmul := tendsto_integral_frullaniLogApprox_Q_mul hm R i j
  have hi := tendsto_integral_frullaniLogApprox_Q hm R i
  have hj := tendsto_integral_frullaniLogApprox_Q hm R j
  have hmean := hi.mul hj
  have hrepr (n : ℕ) :
      cov[frullaniQApprox (m := m) n R i,
        frullaniQApprox (m := m) n R j;
        standardGaussianDataMeasure m p] =
      (∫ z, frullaniLogApprox n (Q R z i) *
        frullaniLogApprox n (Q R z j)
        ∂standardGaussianDataMeasure m p) -
      (∫ z, frullaniLogApprox n (Q R z i)
        ∂standardGaussianDataMeasure m p) *
      (∫ z, frullaniLogApprox n (Q R z j)
        ∂standardGaussianDataMeasure m p) := by
    rw [covariance_eq_sub
      (memLp_frullaniQApprox_two hm n R i)
      (memLp_frullaniQApprox_two hm n R j)]
    rfl
  have htarget :
      cov[fun z ↦ Real.log (Q R z i), fun z ↦ Real.log (Q R z j);
        standardGaussianDataMeasure m p] =
      (∫ z, Real.log (Q R z i) * Real.log (Q R z j)
        ∂standardGaussianDataMeasure m p) -
      (∫ z, Real.log (Q R z i)
        ∂standardGaussianDataMeasure m p) *
      (∫ z, Real.log (Q R z j)
        ∂standardGaussianDataMeasure m p) := by
    rw [covariance_eq_sub (memLp_log_Q_two hm R i)
      (memLp_log_Q_two hm R j)]
    rfl
  rw [htarget]
  exact (hmul.sub hmean).congr' (Eventually.of_forall fun n ↦ (hrepr n).symm)

end GeneralRDecomposition
end LogdetLean
