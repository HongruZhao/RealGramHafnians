import LogdetLean.GramHafnian.AsymptoticLogBoundary
/-!
# A finite-term certificate for the logarithmic converse

The exact correction factor is a positive finite sum.  Retaining a carefully
chosen summand gives a deterministic upper bound on the normalized second
moment.  This module develops that bound without any asymptotic axiom.
-/

open scoped BigOperators Topology
open Finset Filter Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- Elementary lower envelope for the Pochhammer quotient. -/
theorem factorial_div_pow_le_pochhammerRatio
    (k j : ℕ) (hk : 0 < k) :
    (j.factorial : ℝ) / ((k + 2 * j : ℕ) : ℝ) ^ j ≤
      pochhammerRatio k j := by
  rw [pochhammerRatio]
  have hprod :
      (∏ i ∈ range j,
          (((i + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ))) ≤
        ∏ i ∈ range j,
          (((2 * i + 1 : ℕ) : ℝ) / ((k + 2 * i : ℕ) : ℝ)) := by
    apply Finset.prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      have hij : i ≤ j := Nat.le_of_lt (Finset.mem_range.mp hi)
      have hnum : i + 1 ≤ 2 * i + 1 := by omega
      have hden : k + 2 * i ≤ k + 2 * j := by omega
      calc
        (((i + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) ≤
            (((2 * i + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)
        _ ≤ (((2 * i + 1 : ℕ) : ℝ) / ((k + 2 * i : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (by exact_mod_cast hden)
  calc
    (j.factorial : ℝ) / ((k + 2 * j : ℕ) : ℝ) ^ j =
        ∏ i ∈ range j,
          (((i + 1 : ℕ) : ℝ) / ((k + 2 * j : ℕ) : ℝ)) := by
      rw [Finset.prod_div_distrib]
      push_cast
      congr 1
      · exact_mod_cast (Finset.prod_range_add_one_eq_factorial j).symm
      · simp
    _ ≤ ∏ i ∈ range j,
          (((2 * i + 1 : ℕ) : ℝ) / ((k + 2 * i : ℕ) : ℝ)) := hprod

/-- A completely explicit factorial lower bound for one exact correction
summand.  It is useful because it remains exact enough when `j` grows like
`log n`. -/
theorem finiteTerm_factorial_lower_certificate
    (k n j : ℕ) (hk : 0 < k) :
    ((n + 1 - j : ℕ) : ℝ) ^ (2 * j) /
        ((j.factorial : ℝ) * ((k + 2 * j : ℕ) : ℝ) ^ j) ≤
      finiteTerm k n j := by
  have hchoose :
      ((n + 1 - j : ℕ) : ℝ) ^ j / (j.factorial : ℝ) ≤
        ((n.choose j : ℕ) : ℝ) := by
    simpa using (Nat.pow_le_choose (r := j) (n := n) (α := ℝ))
  have hpoch := factorial_div_pow_le_pochhammerRatio k j hk
  have hchoose0 :
      0 ≤ ((n + 1 - j : ℕ) : ℝ) ^ j / (j.factorial : ℝ) := by
    positivity
  have hchooseNat0 : 0 ≤ ((n.choose j : ℕ) : ℝ) := by positivity
  have hsquare :
      (((n + 1 - j : ℕ) : ℝ) ^ j / (j.factorial : ℝ)) ^ 2 ≤
        ((n.choose j : ℕ) : ℝ) ^ 2 := by
    nlinarith
  rw [finiteTerm]
  calc
    ((n + 1 - j : ℕ) : ℝ) ^ (2 * j) /
          ((j.factorial : ℝ) * ((k + 2 * j : ℕ) : ℝ) ^ j) =
        (((n + 1 - j : ℕ) : ℝ) ^ j / (j.factorial : ℝ)) ^ 2 *
          ((j.factorial : ℝ) / ((k + 2 * j : ℕ) : ℝ) ^ j) := by
      have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
      have hden : ((k + 2 * j : ℕ) : ℝ) ≠ 0 := by positivity
      rw [pow_mul]
      field_simp
      ring
    _ ≤ ((n.choose j : ℕ) : ℝ) ^ 2 *
          ((j.factorial : ℝ) / ((k + 2 * j : ℕ) : ℝ) ^ j) := by
      exact mul_le_mul_of_nonneg_right hsquare (by positivity)
    _ ≤ ((n.choose j : ℕ) : ℝ) ^ 2 * pochhammerRatio k j := by
      exact mul_le_mul_of_nonneg_left hpoch (sq_nonneg _)

/-- The central-binomial baseline is at most one. -/
theorem centralBaseline_le_one (n : ℕ) : centralBaseline n ≤ 1 := by
  rw [centralBaseline]
  apply (div_le_one (by positivity : (0 : ℝ) < (4 : ℝ) ^ n)).2
  have hchoose := Nat.choose_le_two_pow (2 * n) n
  have hcast :
      (((Nat.choose (2 * n) n : ℕ) : ℝ)) ≤
        (((2 : ℕ) ^ (2 * n) : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  calc
    (((Nat.choose (2 * n) n : ℕ) : ℝ)) ≤
        (((2 : ℕ) ^ (2 * n) : ℕ) : ℝ) := hcast
    _ = (4 : ℝ) ^ n := by
      push_cast
      rw [pow_mul]
      norm_num

/-- If a single summand has enough factorial mass, the whole correction is
at least `2^j`.  This is the exact finite certificate used in the converse. -/
theorem pow_two_le_finiteCorrection_of_factorial_certificate
    (k n j : ℕ) (hk : 0 < k) (hj : j ≤ n)
    (hcert :
      (2 : ℝ) ^ j * (j.factorial : ℝ) *
          ((k + 2 * j : ℕ) : ℝ) ^ j ≤
        ((n + 1 - j : ℕ) : ℝ) ^ (2 * j)) :
    (2 : ℝ) ^ j ≤ finiteCorrection k n := by
  have hlower := finiteTerm_factorial_lower_certificate k n j hk
  have hden :
      0 < (j.factorial : ℝ) * ((k + 2 * j : ℕ) : ℝ) ^ j := by
    positivity
  have hpowterm :
      (2 : ℝ) ^ j ≤
        ((n + 1 - j : ℕ) : ℝ) ^ (2 * j) /
          ((j.factorial : ℝ) * ((k + 2 * j : ℕ) : ℝ) ^ j) := by
    rw [le_div_iff₀ hden]
    simpa [mul_assoc] using hcert
  exact hpowterm.trans (hlower.trans (finiteTerm_le_finiteCorrection k n j hj))

/-- Paper-friendly consequence of the one-summand certificate: the exact
normalized moment is at most `2^{-j}`. -/
theorem gramSecondMomentRatio_le_two_pow_neg_of_factorial_certificate
    (k n j : ℕ) (hk : 0 < k) (hj : j ≤ n)
    (hcert :
      (2 : ℝ) ^ j * (j.factorial : ℝ) *
          ((k + 2 * j : ℕ) : ℝ) ^ j ≤
        ((n + 1 - j : ℕ) : ℝ) ^ (2 * j)) :
    gramSecondMomentRatio k n ≤ 1 / (2 : ℝ) ^ j := by
  have hF := pow_two_le_finiteCorrection_of_factorial_certificate
    k n j hk hj hcert
  rw [gramSecondMomentRatio]
  calc
    centralBaseline n / finiteCorrection k n ≤
        centralBaseline n / (2 : ℝ) ^ j := by
      exact div_le_div_of_nonneg_left (centralBaseline_nonneg n)
        (by positivity) hF
    _ ≤ 1 / (2 : ℝ) ^ j := by
      exact div_le_div_of_nonneg_right (centralBaseline_le_one n) (by positivity)

/-- The geometric certificate implies the factorial certificate because
`j! ≤ j^j`. -/
theorem factorial_certificate_of_geometric
    (k n j : ℕ)
    (hscale :
      (2 : ℝ) * (j : ℝ) * ((k + 2 * j : ℕ) : ℝ) ≤
        ((n + 1 - j : ℕ) : ℝ) ^ 2) :
    (2 : ℝ) ^ j * (j.factorial : ℝ) *
          ((k + 2 * j : ℕ) : ℝ) ^ j ≤
        ((n + 1 - j : ℕ) : ℝ) ^ (2 * j) := by
  have hfacNat := Nat.factorial_le_pow j
  have hfac : (j.factorial : ℝ) ≤ (j : ℝ) ^ j := by
    exact_mod_cast hfacNat
  have hpow := pow_le_pow_left₀
    (by positivity : 0 ≤ (2 : ℝ) * (j : ℝ) *
      ((k + 2 * j : ℕ) : ℝ)) hscale j
  calc
    (2 : ℝ) ^ j * (j.factorial : ℝ) *
          ((k + 2 * j : ℕ) : ℝ) ^ j ≤
        (2 : ℝ) ^ j * (j : ℝ) ^ j *
          ((k + 2 * j : ℕ) : ℝ) ^ j := by
      gcongr
    _ = ((2 : ℝ) * (j : ℝ) *
          ((k + 2 * j : ℕ) : ℝ)) ^ j := by ring
    _ ≤ (((n + 1 - j : ℕ) : ℝ) ^ 2) ^ j := hpow
    _ = ((n + 1 - j : ℕ) : ℝ) ^ (2 * j) := by rw [pow_mul]

/-- A simpler geometric certificate.  It replaces `j!` by `j^j`; hence the
single transparent condition `2 j (k+2j) ≤ (n+1-j)^2` already forces a
`2^{-j}` upper bound. -/
theorem gramSecondMomentRatio_le_two_pow_neg_of_geometric_certificate
    (k n j : ℕ) (hk : 0 < k) (hj : j ≤ n)
    (hscale :
      (2 : ℝ) * (j : ℝ) * ((k + 2 * j : ℕ) : ℝ) ≤
        ((n + 1 - j : ℕ) : ℝ) ^ 2) :
    gramSecondMomentRatio k n ≤ 1 / (2 : ℝ) ^ j := by
  have hcert := factorial_certificate_of_geometric k n j hscale
  exact gramSecondMomentRatio_le_two_pow_neg_of_factorial_certificate
    k n j hk hj hcert

/-- The logarithmic summand index used in the direct converse. -/
noncomputable def logarithmicWitness (d n : ℕ) : ℕ :=
  Nat.ceil ((((d + 1 : ℕ) : ℝ) / Real.log 2) * Real.log (n : ℝ))

/-- The ceiling witness is asymptotic to its underlying logarithmic scale. -/
theorem tendsto_logarithmicWitness_div_log (d : ℕ) :
    Tendsto (fun n : ℕ ↦
      (logarithmicWitness d n : ℝ) / Real.log (n : ℝ)) atTop
      (nhds (((d + 1 : ℕ) : ℝ) / Real.log 2)) := by
  have hA :
      0 ≤ (((d + 1 : ℕ) : ℝ) / Real.log 2) := by
    positivity
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa [logarithmicWitness, Function.comp_def] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hA).comp hlog

/-- By construction, `2^logarithmicWitness` dominates the requested power of
`n`. -/
theorem pow_le_two_pow_logarithmicWitness
    (d n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (d + 1) ≤ (2 : ℝ) ^ logarithmicWitness d n := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hceil :
      (((d + 1 : ℕ) : ℝ) / Real.log 2) * Real.log (n : ℝ) ≤
        (logarithmicWitness d n : ℝ) := by
    simpa [logarithmicWitness] using
      (Nat.le_ceil ((((d + 1 : ℕ) : ℝ) / Real.log 2) *
        Real.log (n : ℝ)))
  have hlogs :
      ((d + 1 : ℕ) : ℝ) * Real.log (n : ℝ) ≤
        (logarithmicWitness d n : ℝ) * Real.log 2 := by
    calc
      ((d + 1 : ℕ) : ℝ) * Real.log (n : ℝ) =
          ((((d + 1 : ℕ) : ℝ) / Real.log 2) * Real.log (n : ℝ)) *
            Real.log 2 := by
        field_simp [hlogTwo.ne']
      _ ≤ (logarithmicWitness d n : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hceil hlogTwo.le
  have hexp := Real.exp_le_exp.mpr hlogs
  calc
    (n : ℝ) ^ (d + 1) = Real.exp (Real.log (n : ℝ)) ^ (d + 1) := by
      rw [Real.exp_log hnR]
    _ = Real.exp (((d + 1 : ℕ) : ℝ) * Real.log (n : ℝ)) := by
      exact (Real.exp_nat_mul (Real.log (n : ℝ)) (d + 1)).symm
    _ ≤ Real.exp ((logarithmicWitness d n : ℝ) * Real.log 2) := hexp
    _ = Real.exp (Real.log 2) ^ logarithmicWitness d n :=
      Real.exp_nat_mul (Real.log 2) (logarithmicWitness d n)
    _ = (2 : ℝ) ^ logarithmicWitness d n := by
      rw [Real.exp_log (by norm_num)]

/-- A sequence-level converse stated exactly at the finite certificate needed
by the proof.  For every requested polynomial degree, it suffices to find an
eventual summand whose factorial lower envelope dominates both `2^j` and the
corresponding power of `n`. -/
theorem not_hasWeakAntiConcentration_of_eventually_factorial_certificates
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hcert : ∀ d : ℕ, ∀ᶠ n : ℕ in atTop, ∃ j : ℕ,
      j ≤ n ∧
      (2 : ℝ) ^ j * (j.factorial : ℝ) *
          ((kseq n + 2 * j : ℕ) : ℝ) ^ j ≤
        ((n + 1 - j : ℕ) : ℝ) ^ (2 * j) ∧
      (n : ℝ) ^ (d + 1) ≤ (2 : ℝ) ^ j) :
    ¬ HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio (kseq n) n) := by
  rintro ⟨C, hC, d, hweak⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < C :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hC)
  obtain ⟨n, hkn, hncert, hnweak, hnsmall, hn⟩ :=
    (hk.and ((hcert d).and (hweak.and
      (hsmall.and (eventually_ge_atTop 1))))).exists
  obtain ⟨j, hjn, hfactorial, hjpower⟩ := hncert
  have hratio :=
    gramSecondMomentRatio_le_two_pow_neg_of_factorial_certificate
      (kseq n) n j hkn hjn hfactorial
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hinv :
      1 / (2 : ℝ) ^ j ≤ 1 / (n : ℝ) ^ (d + 1) := by
    exact div_le_div_of_nonneg_left (by norm_num)
      (pow_pos hnR (d + 1)) hjpower
  have hchain :
      C / (n : ℝ) ^ d ≤ 1 / (n : ℝ) ^ (d + 1) :=
    hnweak.trans (hratio.trans hinv)
  have hcross :
      C * (n : ℝ) ^ (d + 1) ≤ (n : ℝ) ^ d := by
    rw [div_le_div_iff₀ (pow_pos hnR d) (pow_pos hnR (d + 1))] at hchain
    simpa using hchain
  have hCn : C * (n : ℝ) ≤ 1 := by
    have hpow : 0 < (n : ℝ) ^ d := pow_pos hnR d
    apply le_of_mul_le_mul_left ?_ hpow
    calc
      (n : ℝ) ^ d * (C * n) = C * (n : ℝ) ^ (d + 1) := by
        rw [pow_succ]
        ring
      _ ≤ (n : ℝ) ^ d := hcross
      _ = (n : ℝ) ^ d * 1 := by ring
  have hCle : C ≤ 1 / (n : ℝ) := by
    rw [le_div_iff₀ hnR]
    simpa [mul_comm] using hCn
  linarith

/-- Geometric-certificate form of the general logarithmic converse.  This is
often the most convenient endpoint for an asymptotic argument: choose
`j ≈ A log n`, verify the displayed quadratic inequality, and make `A`
larger than the requested polynomial degree. -/
theorem not_hasWeakAntiConcentration_of_eventually_geometric_certificates
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hcert : ∀ d : ℕ, ∀ᶠ n : ℕ in atTop, ∃ j : ℕ,
      j ≤ n ∧
      (2 : ℝ) * (j : ℝ) * ((kseq n + 2 * j : ℕ) : ℝ) ≤
        ((n + 1 - j : ℕ) : ℝ) ^ 2 ∧
      (n : ℝ) ^ (d + 1) ≤ (2 : ℝ) ^ j) :
    ¬ HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio (kseq n) n) := by
  apply not_hasWeakAntiConcentration_of_eventually_factorial_certificates
    kseq hk
  intro d
  filter_upwards [hcert d] with n hn
  obtain ⟨j, hjn, hscale, hjpower⟩ := hn
  exact ⟨j, hjn, factorial_certificate_of_geometric
    (kseq n) n j hscale, hjpower⟩

/-- Full logarithmic converse.  If

`k_n log n / n² → 0`,

then the exact normalized second moment is smaller than every inverse
polynomial along the explicit bounds used below, and in particular it cannot
be eventually bounded below by any inverse polynomial.  Thus weak
anticoncentration fails.  The proof chooses
`j = ceil((d+1) log n / log 2)` and applies the geometric one-summand
certificate. -/
theorem not_hasWeakAntiConcentration_of_log_dimension_ratio_zero
    (kseq : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 0 < kseq n)
    (hratio : Tendsto (fun n : ℕ ↦
      (kseq n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0)) :
    ¬ HasWeakAntiConcentration
      (fun n ↦ gramSecondMomentRatio (kseq n) n) := by
  apply not_hasWeakAntiConcentration_of_eventually_geometric_certificates
    kseq hk
  intro d
  have hjLog := tendsto_logarithmicWitness_div_log d
  have hlogOverN : Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hjOverNraw : Tendsto (fun n : ℕ ↦
      ((logarithmicWitness d n : ℝ) / Real.log (n : ℝ)) *
        (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 0) := by
    simpa using hjLog.mul hlogOverN
  have hjOverN : Tendsto (fun n : ℕ ↦
      (logarithmicWitness d n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    apply hjOverNraw.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    field_simp [hn0, hlog0]
  have hjKraw : Tendsto (fun n : ℕ ↦
      ((logarithmicWitness d n : ℝ) / Real.log (n : ℝ)) *
        ((kseq n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2))
      atTop (nhds 0) := by
    simpa using hjLog.mul hratio
  have hjK : Tendsto (fun n : ℕ ↦
      (logarithmicWitness d n : ℝ) * (kseq n : ℝ) /
        (n : ℝ) ^ 2) atTop (nhds 0) := by
    apply hjKraw.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    field_simp [hn0, hlog0]
  have hjSqRaw := hjOverN.mul hjOverN
  have hjSq : Tendsto (fun n : ℕ ↦
      (logarithmicWitness d n : ℝ) ^ 2 / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
    have hraw : Tendsto (fun n : ℕ ↦
        ((logarithmicWitness d n : ℝ) / (n : ℝ)) *
          ((logarithmicWitness d n : ℝ) / (n : ℝ)))
        atTop (nhds 0) := by simpa using hjSqRaw
    apply hraw.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp [hn0]
  have hgeomRaw : Tendsto (fun n : ℕ ↦
      2 * ((logarithmicWitness d n : ℝ) * (kseq n : ℝ) /
        (n : ℝ) ^ 2) +
      4 * ((logarithmicWitness d n : ℝ) ^ 2 / (n : ℝ) ^ 2))
      atTop (nhds 0) := by
    simpa using (Tendsto.const_mul 2 hjK).add (Tendsto.const_mul 4 hjSq)
  have hgeom : Tendsto (fun n : ℕ ↦
      2 * (logarithmicWitness d n : ℝ) *
          ((kseq n + 2 * logarithmicWitness d n : ℕ) : ℝ) /
        (n : ℝ) ^ 2) atTop (nhds 0) := by
    apply hgeomRaw.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hn0]
    ring
  have hjSmall : ∀ᶠ n : ℕ in atTop,
      (logarithmicWitness d n : ℝ) / (n : ℝ) < 1 / 2 :=
    hjOverN.eventually (Iio_mem_nhds (by norm_num))
  have hgeomSmall : ∀ᶠ n : ℕ in atTop,
      2 * (logarithmicWitness d n : ℝ) *
          ((kseq n + 2 * logarithmicWitness d n : ℕ) : ℝ) /
        (n : ℝ) ^ 2 < 1 / 4 :=
    hgeom.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hjSmall, hgeomSmall, eventually_ge_atTop 2]
    with n hjnSmall hgeomN hn
  let j := logarithmicWitness d n
  have hnR : 0 < (n : ℝ) := by positivity
  have hjR : (j : ℝ) < (n : ℝ) / 2 := by
    rw [div_lt_iff₀ hnR] at hjnSmall
    change (j : ℝ) < (1 / 2 : ℝ) * (n : ℝ) at hjnSmall
    linarith
  have hjn : j ≤ n := by
    exact_mod_cast (lt_trans hjR (by linarith : (n : ℝ) / 2 < n)).le
  refine ⟨j, hjn, ?_, ?_⟩
  · have hleft :
        (2 : ℝ) * (j : ℝ) * ((kseq n + 2 * j : ℕ) : ℝ) ≤
          (n : ℝ) ^ 2 / 4 := by
      rw [div_lt_iff₀ (sq_pos_of_pos hnR)] at hgeomN
      change (2 : ℝ) * (j : ℝ) *
          ((kseq n + 2 * j : ℕ) : ℝ) <
        1 / 4 * (n : ℝ) ^ 2 at hgeomN
      nlinarith
    have hsub :
        ((n + 1 - j : ℕ) : ℝ) = (n : ℝ) + 1 - (j : ℝ) := by
      rw [Nat.cast_sub (by omega : j ≤ n + 1)]
      norm_num
    have hhalf :
        (n : ℝ) / 2 ≤ ((n + 1 - j : ℕ) : ℝ) := by
      rw [hsub]
      linarith
    calc
      (2 : ℝ) * (j : ℝ) * ((kseq n + 2 * j : ℕ) : ℝ) ≤
          (n : ℝ) ^ 2 / 4 := hleft
      _ = ((n : ℝ) / 2) ^ 2 := by ring
      _ ≤ ((n + 1 - j : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hhalf 2
  · simpa [j] using pow_le_two_pow_logarithmicWitness d n (by omega)

end

end LogdetLean.GramHafnian
