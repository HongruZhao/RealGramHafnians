import LogdetLean.ComplexBetaMellin
import LogdetLean.ConvolutionMoments
/-!
# Exact characteristic function of the finite log-Beta sum

For `2 ≤ p ≤ m`, this file proves the exact Gamma product for the
characteristic function of the recursively convolved log-Beta law and for its
exactly centered image.  The published formulas followed are Xie--Sun (2021),
equations (13)--(16), printed pp. 435--436.  Their sample-size symbol `n` is
our effective centered dimension `m`; their `j = 1` factor equals one, so our
product starts at `j = 2`.  The underlying one-factor Mellin identity is
Rouault (2007), equation (2.10), printed p. 189.

The proof is a direct Lean derivation from `ComplexBetaMellin` and mathlib's
characteristic-function-of-convolution theorem.  The published formulas are
not introduced as axioms.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal Topology ComplexConjugate

noncomputable section

set_option linter.style.haveILetI false

/-- The exact Gamma quotient contributed by the `j`th log-Beta factor. -/
def logBetaCharacteristicFactor (m j : ℕ) (t : ℝ) : ℂ :=
  complexBetaMellinQuotient (betaShapeA m j) (betaShapeB j)
    ((t : ℂ) * Complex.I)

/-- The finite Gamma product for the characteristic function of the null
log-Beta sum. -/
def logBetaCharacteristicProduct (m p : ℕ) (t : ℝ) : ℂ :=
  ∏ j ∈ Finset.Icc 2 p, logBetaCharacteristicFactor m j t

/-- Exact characteristic function of one Bartlett/Gram log-Beta factor. -/
theorem charFun_logBetaLaw_eq_logBetaCharacteristicFactor
    {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) (t : ℝ) :
    charFun (logBetaLaw m j) t = logBetaCharacteristicFactor m j t := by
  unfold logBetaLaw logBetaCharacteristicFactor
  exact charFun_map_log_betaMeasure_eq_complexBetaMellinQuotient
    (betaShapeA_pos_of_le hjm) (betaShapeB_pos_of_two_le hj) t

/-- The preceding one-factor identity with every Gamma quotient displayed.
This statement makes all real-to-complex coercions explicit. -/
theorem charFun_logBetaLaw_eq_gammaQuotient
    {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) (t : ℝ) :
    charFun (logBetaLaw m j) t =
      Complex.Gamma
          ((betaShapeA m j : ℂ) + (t : ℂ) * Complex.I) *
        Complex.Gamma
          (((betaShapeA m j + betaShapeB j : ℝ) : ℂ)) /
        (Complex.Gamma (betaShapeA m j : ℂ) *
          Complex.Gamma
            (((betaShapeA m j + betaShapeB j : ℝ) : ℂ) +
              (t : ℂ) * Complex.I)) := by
  rw [charFun_logBetaLaw_eq_logBetaCharacteristicFactor hjm hj]
  rfl

/-- Each factor in the admissible Gamma product is nonzero on the whole real
frequency axis. -/
theorem logBetaCharacteristicFactor_ne_zero
    {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) (t : ℝ) :
    logBetaCharacteristicFactor m j t ≠ 0 := by
  unfold logBetaCharacteristicFactor
  have hA : 0 < betaShapeA m j := betaShapeA_pos_of_le hjm
  have hB : 0 < betaShapeB j := betaShapeB_pos_of_two_le hj
  exact complexBetaMellinQuotient_ne_zero
    (α := betaShapeA m j) (β := betaShapeB j)
    (z := (t : ℂ) * Complex.I) hA hB (by simpa using hA)

/-- The one-factor Gamma quotient is measurable as a function of the real
frequency.  We obtain this from its proved equality with a characteristic
function, avoiding a separate meromorphic-function argument. -/
theorem measurable_logBetaCharacteristicFactor
    {m j : ℕ} (hjm : j ≤ m) (hj : 2 ≤ j) :
    Measurable (logBetaCharacteristicFactor m j) := by
  letI : IsProbabilityMeasure (logBetaLaw m j) :=
    isProbabilityMeasure_logBetaLaw hjm hj
  have hcf : Measurable (charFun (logBetaLaw m j)) := measurable_charFun
  have hfun : logBetaCharacteristicFactor m j = charFun (logBetaLaw m j) := by
    funext t
    exact (charFun_logBetaLaw_eq_logBetaCharacteristicFactor hjm hj t).symm
  rw [hfun]
  exact hcf

/-- Exact Gamma-product characteristic function of the complete finite
log-Beta sum.  This is the finite identity underlying Xie--Sun (2021),
equations (13)--(16), without their proportional-growth restriction. -/
theorem charFun_logBetaSumLaw_eq_logBetaCharacteristicProduct
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    charFun (logBetaSumLaw m p) t =
      logBetaCharacteristicProduct m p t := by
  induction p with
  | zero =>
      simp [logBetaSumLaw, logBetaCharacteristicProduct]
  | succ p ih =>
      by_cases hp2 : 2 ≤ p + 1
      · have hpm' : p ≤ m := by omega
        letI : IsProbabilityMeasure (logBetaSumLaw m p) :=
          isProbabilityMeasure_logBetaSumLaw hpm'
        letI : IsProbabilityMeasure (logBetaLaw m (p + 1)) :=
          isProbabilityMeasure_logBetaLaw hpm hp2
        rw [logBetaSumLaw, if_pos hp2, charFun_conv, ih hpm']
        rw [charFun_logBetaLaw_eq_logBetaCharacteristicFactor hpm hp2]
        unfold logBetaCharacteristicProduct
        rw [Finset.prod_Icc_succ_top hp2]
      · have hp0 : p = 0 := by omega
        subst p
        simp [logBetaSumLaw, logBetaCharacteristicProduct]

/-- The finite-sum characteristic function with the full Gamma product
displayed.  This is the exact finite identity in Xie--Sun (2021),
equations (13)--(16), after the notation map stated in the module header. -/
theorem charFun_logBetaSumLaw_eq_gammaQuotientProduct
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    charFun (logBetaSumLaw m p) t =
      ∏ j ∈ Finset.Icc 2 p,
        (Complex.Gamma
            ((betaShapeA m j : ℂ) + (t : ℂ) * Complex.I) *
          Complex.Gamma
            (((betaShapeA m j + betaShapeB j : ℝ) : ℂ)) /
          (Complex.Gamma (betaShapeA m j : ℂ) *
            Complex.Gamma
              (((betaShapeA m j + betaShapeB j : ℝ) : ℂ) +
                (t : ℂ) * Complex.I))) := by
  rw [charFun_logBetaSumLaw_eq_logBetaCharacteristicProduct hpm]
  rfl

/-- The complete finite Gamma product is nonzero at every real frequency. -/
theorem logBetaCharacteristicProduct_ne_zero
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    logBetaCharacteristicProduct m p t ≠ 0 := by
  unfold logBetaCharacteristicProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact logBetaCharacteristicFactor_ne_zero (hj.2.trans hpm) hj.1 t

/-- The exact finite Gamma product is measurable in frequency. -/
theorem measurable_logBetaCharacteristicProduct
    {m p : ℕ} (hpm : p ≤ m) :
    Measurable (logBetaCharacteristicProduct m p) := by
  letI : IsProbabilityMeasure (logBetaSumLaw m p) :=
    isProbabilityMeasure_logBetaSumLaw hpm
  have hcf : Measurable (charFun (logBetaSumLaw m p)) := measurable_charFun
  have hfun : logBetaCharacteristicProduct m p = charFun (logBetaSumLaw m p) := by
    funext t
    exact (charFun_logBetaSumLaw_eq_logBetaCharacteristicProduct hpm t).symm
  rw [hfun]
  exact hcf

/-- Exact centering of the finite log-Beta sum, represented as a pushforward
law. -/
def centeredLogBetaSumLaw (m p : ℕ) : Measure ℝ :=
  (logBetaSumLaw m p).map (fun x ↦ x - nullCenter m p)

/-- The centering map is measurable. -/
theorem measurable_sub_nullCenter (m p : ℕ) :
    Measurable (fun x : ℝ ↦ x - nullCenter m p) := by fun_prop

set_option linter.style.multiGoal false in
/-- Centering preserves probability mass. -/
theorem isProbabilityMeasure_centeredLogBetaSumLaw
    {m p : ℕ} (hpm : p ≤ m) :
    IsProbabilityMeasure (centeredLogBetaSumLaw m p) := by
  letI : IsProbabilityMeasure (logBetaSumLaw m p) :=
    isProbabilityMeasure_logBetaSumLaw hpm
  unfold centeredLogBetaSumLaw
  exact Measure.isProbabilityMeasure_map (measurable_sub_nullCenter m p).aemeasurable

/-- The centered law has expectation zero.  Thus the phase used below is the
actual probabilistic centering, not merely a symbolic constant. -/
theorem integral_id_centeredLogBetaSumLaw_eq_zero
    {m p : ℕ} (hpm : p ≤ m) :
    ∫ x : ℝ, x ∂centeredLogBetaSumLaw m p = 0 := by
  letI : IsProbabilityMeasure (logBetaSumLaw m p) :=
    isProbabilityMeasure_logBetaSumLaw hpm
  have hL3 : MemLp (fun x : ℝ ↦ x) 3 (logBetaSumLaw m p) :=
    memLp_id_logBetaSumLaw hpm
  have hL1 : Integrable (fun x : ℝ ↦ x) (logBetaSumLaw m p) :=
    hL3.integrable (by norm_num)
  rw [centeredLogBetaSumLaw,
    integral_map_of_stronglyMeasurable (measurable_sub_nullCenter m p) (by fun_prop)]
  rw [integral_sub hL1 (integrable_const (nullCenter m p)), integral_const]
  simp [nullCenter]

/-- The exact centered Gamma product, including the deterministic phase. -/
def centeredLogBetaCharacteristicProduct (m p : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-(((nullCenter m p * t : ℝ) : ℂ) * Complex.I)) *
    logBetaCharacteristicProduct m p t

/-- Exact characteristic function of the centered finite log-Beta sum. -/
theorem charFun_centeredLogBetaSumLaw_eq_centeredGammaProduct
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    charFun (centeredLogBetaSumLaw m p) t =
      centeredLogBetaCharacteristicProduct m p t := by
  letI : IsProbabilityMeasure (logBetaSumLaw m p) :=
    isProbabilityMeasure_logBetaSumLaw hpm
  rw [centeredLogBetaSumLaw]
  change charFun ((logBetaSumLaw m p).map
      (fun x : ℝ ↦ x + (-nullCenter m p))) t = _
  rw [charFun_map_add_const]
  rw [charFun_logBetaSumLaw_eq_logBetaCharacteristicProduct hpm]
  unfold centeredLogBetaCharacteristicProduct
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  rw [mul_comm (logBetaCharacteristicProduct m p t)]
  congr 2
  ring

/-- The centered characteristic function with both its phase and all Gamma
factors displayed. -/
theorem charFun_centeredLogBetaSumLaw_eq_explicitGammaProduct
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    charFun (centeredLogBetaSumLaw m p) t =
      Complex.exp (-(((nullCenter m p * t : ℝ) : ℂ) * Complex.I)) *
        ∏ j ∈ Finset.Icc 2 p,
          (Complex.Gamma
              ((betaShapeA m j : ℂ) + (t : ℂ) * Complex.I) *
            Complex.Gamma
              (((betaShapeA m j + betaShapeB j : ℝ) : ℂ)) /
            (Complex.Gamma (betaShapeA m j : ℂ) *
              Complex.Gamma
                (((betaShapeA m j + betaShapeB j : ℝ) : ℂ) +
                  (t : ℂ) * Complex.I))) := by
  rw [charFun_centeredLogBetaSumLaw_eq_centeredGammaProduct hpm]
  rfl

/-- The centered characteristic function is nonzero at every real frequency. -/
theorem centeredLogBetaCharacteristicProduct_ne_zero
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    centeredLogBetaCharacteristicProduct m p t ≠ 0 := by
  unfold centeredLogBetaCharacteristicProduct
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (logBetaCharacteristicProduct_ne_zero hpm t)

/-- The centered Gamma product is measurable in frequency. -/
theorem measurable_centeredLogBetaCharacteristicProduct
    {m p : ℕ} (hpm : p ≤ m) :
    Measurable (centeredLogBetaCharacteristicProduct m p) := by
  letI : IsProbabilityMeasure (centeredLogBetaSumLaw m p) :=
    isProbabilityMeasure_centeredLogBetaSumLaw hpm
  have hcf : Measurable (charFun (centeredLogBetaSumLaw m p)) := measurable_charFun
  have hfun : centeredLogBetaCharacteristicProduct m p =
      charFun (centeredLogBetaSumLaw m p) := by
    funext t
    exact (charFun_centeredLogBetaSumLaw_eq_centeredGammaProduct hpm t).symm
  rw [hfun]
  exact hcf

/-- The exact Gamma product after centering and division by the exact standard
deviation.  No positivity hypothesis is required to define this expression;
in the nontrivial range `2 ≤ p ≤ m`, positivity of the variance is proved in
`NullVA` and `NullCenterStandardization`. -/
def standardizedLogBetaCharacteristicProduct (m p : ℕ) (t : ℝ) : ℂ :=
  centeredLogBetaCharacteristicProduct m p
    (t / Real.sqrt (nullVariance m p))

/-- Exact characteristic function of the centered and variance-normalized
finite log-Beta sum.  This is the standardized form of the finite Gamma
product in Xie--Sun (2021), equations (13)--(16), pp. 435--436. -/
theorem charFun_standardizedNullLaw_eq_standardizedGammaProduct
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    charFun (standardizedNullLaw m p) t =
      standardizedLogBetaCharacteristicProduct m p t := by
  letI : IsProbabilityMeasure (logBetaSumLaw m p) :=
    isProbabilityMeasure_logBetaSumLaw hpm
  unfold standardizedNullLaw
  rw [show (fun x : ℝ ↦
      (x - nullCenter m p) / Real.sqrt (nullVariance m p)) =
      (fun x : ℝ ↦ (1 / Real.sqrt (nullVariance m p)) *
        (x - nullCenter m p)) by
    funext x
    ring]
  rw [charFun_map_mul_comp
    (measurable_sub_nullCenter m p).aemeasurable]
  change charFun (centeredLogBetaSumLaw m p)
      ((1 / Real.sqrt (nullVariance m p)) * t) = _
  rw [charFun_centeredLogBetaSumLaw_eq_centeredGammaProduct hpm]
  unfold standardizedLogBetaCharacteristicProduct
  apply congrArg (centeredLogBetaCharacteristicProduct m p)
  ring

/-- The standardized characteristic function with the rescaled frequency,
centering phase, and every Gamma factor displayed. -/
theorem charFun_standardizedNullLaw_eq_explicitGammaProduct
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    let q := t / Real.sqrt (nullVariance m p)
    charFun (standardizedNullLaw m p) t =
      Complex.exp (-(((nullCenter m p * q : ℝ) : ℂ) * Complex.I)) *
        ∏ j ∈ Finset.Icc 2 p,
          (Complex.Gamma
              ((betaShapeA m j : ℂ) + (q : ℂ) * Complex.I) *
            Complex.Gamma
              (((betaShapeA m j + betaShapeB j : ℝ) : ℂ)) /
            (Complex.Gamma (betaShapeA m j : ℂ) *
              Complex.Gamma
                (((betaShapeA m j + betaShapeB j : ℝ) : ℂ) +
                  (q : ℂ) * Complex.I))) := by
  dsimp only
  rw [charFun_standardizedNullLaw_eq_standardizedGammaProduct hpm]
  rfl

/-- The standardized exact Gamma product is nonzero on the real frequency
axis. -/
theorem standardizedLogBetaCharacteristicProduct_ne_zero
    {m p : ℕ} (hpm : p ≤ m) (t : ℝ) :
    standardizedLogBetaCharacteristicProduct m p t ≠ 0 := by
  unfold standardizedLogBetaCharacteristicProduct
  exact centeredLogBetaCharacteristicProduct_ne_zero hpm _

/-- The standardized exact Gamma product is measurable in frequency. -/
theorem measurable_standardizedLogBetaCharacteristicProduct
    {m p : ℕ} (hpm : p ≤ m) :
    Measurable (standardizedLogBetaCharacteristicProduct m p) := by
  unfold standardizedLogBetaCharacteristicProduct
  exact (measurable_centeredLogBetaCharacteristicProduct hpm).comp (by fun_prop)

end

end LogdetLean
