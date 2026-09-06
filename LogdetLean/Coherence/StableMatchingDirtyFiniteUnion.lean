import LogdetLean.Coherence.StableMatchingCleanFiniteUnion
import LogdetLean.Coherence.StableMatchingDirtyRate
import LogdetLean.Coherence.StableMatchingPairBlock
import LogdetLean.Coherence.StableMatchingAlternativeLogdet
import LogdetLean.GeneralRResidualCovariance
import Mathlib.Tactic
/-!
# Dirty edges in the stable matching alternative

This file controls the nonplanted edges incident to one of the special
two-column blocks.  Every such edge joins two distinct population blocks,
so its two columns have the ordinary independent standard-Gaussian product
law.  A union bound then gives the all-regime `O(s p q_{m,p})` estimate.
-/

namespace LogdetLean.Coherence

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators RealInnerProductSpace Topology

attribute [local instance] Classical.propDecidable

/-- One output column of a homogeneous planted Gaussian pair. -/
def stableMatchingPairColumn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (rho : ℝ) : Fin 2 → E × E → E
  | 0, z => z.1
  | 1, z => correlatedSecondColumn rho z.1 z.2

theorem measurable_stableMatchingPairColumn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (rho : ℝ) (i : Fin 2) :
    Measurable (stableMatchingPairColumn (E := E) rho i) := by
  fin_cases i
  · change Measurable (fun z : E × E ↦ z.1)
    exact measurable_fst
  · change Measurable (fun z : E × E ↦
      correlatedSecondColumn rho z.1 z.2)
    unfold correlatedSecondColumn
    exact (measurable_const.smul measurable_fst).add
      (measurable_const.smul measurable_snd)

@[simp] theorem stableMatchingPairColumn_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : ℝ) (z : E × E) :
    stableMatchingPairColumn rho 0 z = z.1 := by
  simp [stableMatchingPairColumn]

@[simp] theorem stableMatchingPairColumn_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : ℝ) (z : E × E) :
    stableMatchingPairColumn rho 1 z =
      correlatedSecondColumn rho z.1 z.2 := by
  simp [stableMatchingPairColumn]

/-- Each output of a strict correlated Gaussian pair is marginally standard
Gaussian.  This is proved from the already verified canonical two-column
Gaussian row law. -/
theorem map_stableMatchingPairColumn_eq_stdGaussian
    {m : ℕ} (rho : ℝ) (hrho : |rho| < 1) (i : Fin 2) :
    Measure.map
        (stableMatchingPairColumn
          (E := EuclideanSpace ℝ (Fin m)) rho i)
        ((stdGaussian (EuclideanSpace ℝ (Fin m))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin m)))) =
      stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let E := EuclideanSpace ℝ (Fin m)
  let pairLaw : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let toPair : (Fin 2 → E) → E × E :=
    (MeasurableEquiv.finTwoArrow : (Fin 2 → E) ≃ᵐ E × E)
  let pull : GaussianData m 2 → E × E := toPair ∘ dataColumns
  have hpull : MeasurePreserving pull
      (standardGaussianDataMeasure m 2) pairLaw := by
    exact (measurePreserving_finTwoArrow (stdGaussian E)).comp
      (measurePreserving_dataColumns_standardGaussianDataMeasure m 2)
  fin_cases i
  · change Measure.map Prod.fst
        ((stdGaussian E).prod (stdGaussian E)) = stdGaussian E
    rw [Measure.map_fst_prod]
    simp
  · let R : CorrelationMatrix 2 :=
      strictPairCorrelation rho hrho
    have hfun :
        stableMatchingPairColumn (E := E) rho 1 ∘ pull =
          (fun x : GaussianData m 2 ↦ dataColumn x 1) ∘
            GeneralRDecomposition.canonicalPairRows rho := by
      funext z
      rw [Function.comp_apply, Function.comp_apply,
        GeneralRDecomposition.dataColumn_canonicalPairRows_one]
      rfl
    change Measure.map (stableMatchingPairColumn (E := E) rho 1) pairLaw = _
    rw [← hpull.map_eq]
    rw [Measure.map_map
      (measurable_stableMatchingPairColumn (E := E) rho 1)
      hpull.measurable]
    rw [hfun]
    calc
      Measure.map
          ((fun x : GaussianData m 2 ↦ dataColumn x 1) ∘
            GeneralRDecomposition.canonicalPairRows rho)
          (standardGaussianDataMeasure m 2) =
        Measure.map (fun x : GaussianData m 2 ↦ dataColumn x 1)
          (Measure.map (GeneralRDecomposition.canonicalPairRows rho)
            (standardGaussianDataMeasure m 2)) := by
              exact (Measure.map_map
                (((measurable_pi_apply 1).comp measurable_dataColumns))
                (GeneralRDecomposition.measurable_canonicalPairRows rho)).symm
      _ = Measure.map (fun x : GaussianData m 2 ↦ dataColumn x 1)
          (correlatedGaussianDataMeasure m R) := by
            rw [GeneralRDecomposition.map_canonicalPairRows_standardGaussianDataMeasure
              hrho.le]
            rfl
      _ = _ := GeneralRDecomposition.map_dataColumn_correlatedGaussianDataMeasure
        R 1

/-- Reading either output column from one coordinate of an iid block array
still has the standard Gaussian law. -/
theorem map_eval_stableMatchingPairColumn_eq_stdGaussian
    {m s : ℕ} (rho : ℝ) (hrho : |rho| < 1)
    (i : Fin 2) (e : Fin s) :
    Measure.map
        (fun v : Fin s →
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) ↦
          stableMatchingPairColumn rho i (v e))
        (Measure.pi fun _ : Fin s ↦
          (stdGaussian (EuclideanSpace ℝ (Fin m))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin m)))) =
      stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let E := EuclideanSpace ℝ (Fin m)
  let muPair : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let evalE : (Fin s → E × E) → E × E := fun v ↦ v e
  have heval := (measurePreserving_eval (fun _ : Fin s ↦ muPair) e).map_eq
  calc
    Measure.map (fun v : Fin s → E × E ↦
        stableMatchingPairColumn rho i (v e))
        (Measure.pi fun _ : Fin s ↦ muPair) =
      Measure.map (stableMatchingPairColumn (E := E) rho i)
        (Measure.map (fun v : Fin s → E × E ↦ v e)
          (Measure.pi fun _ : Fin s ↦ muPair)) := by
            change Measure.map
                (stableMatchingPairColumn (E := E) rho i ∘ evalE)
                (Measure.pi fun _ : Fin s ↦ muPair) = _
            exact (Measure.map_map
              (measurable_stableMatchingPairColumn rho i)
              ((measurable_pi_apply e) : Measurable evalE)).symm
    _ = Measure.map (stableMatchingPairColumn (E := E) rho i) muPair := by
      rw [heval]
    _ = _ := map_stableMatchingPairColumn_eq_stdGaussian rho hrho i

/-- Output columns belonging to two distinct planted blocks are exactly
independent standard Gaussians. -/
theorem map_two_distinct_pairBlockColumns_eq_gaussianProduct
    {m s : ℕ} (rho : ℝ) (hrho : |rho| < 1)
    (i j : Fin 2) {e f : Fin s} (hef : e ≠ f) :
    Measure.map
        (fun v : Fin s →
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) ↦
          (stableMatchingPairColumn rho i (v e),
            stableMatchingPairColumn rho j (v f)))
        (Measure.pi fun _ : Fin s ↦
          (stdGaussian (EuclideanSpace ℝ (Fin m))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin m)))) =
      (stdGaussian (EuclideanSpace ℝ (Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  let E := EuclideanSpace ℝ (Fin m)
  let muPair : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let muBlocks : Measure (Fin s → E × E) := Measure.pi fun _ : Fin s ↦ muPair
  let X : (Fin s → E × E) → E :=
    fun v ↦ stableMatchingPairColumn rho i (v e)
  let Y : (Fin s → E × E) → E :=
    fun v ↦ stableMatchingPairColumn rho j (v f)
  have hcoords : iIndepFun (fun a (v : Fin s → E × E) ↦ v a) muBlocks :=
    iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hind : IndepFun X Y muBlocks :=
    (hcoords.indepFun hef).comp
      (measurable_stableMatchingPairColumn rho i)
      (measurable_stableMatchingPairColumn rho j)
  have hmap := hind.map_prod_eq_prod_map_map
    ((measurable_stableMatchingPairColumn rho i).comp
      (measurable_pi_apply e) : Measurable X).aemeasurable
    ((measurable_stableMatchingPairColumn rho j).comp
      (measurable_pi_apply f) : Measurable Y).aemeasurable
  have hX : Measure.map X muBlocks = stdGaussian E := by
    simpa [X, muBlocks, muPair] using
      map_eval_stableMatchingPairColumn_eq_stdGaussian
        (m := m) rho hrho i e
  have hY : Measure.map Y muBlocks = stdGaussian E := by
    simpa [Y, muBlocks, muPair] using
      map_eval_stableMatchingPairColumn_eq_stdGaussian
        (m := m) rho hrho j f
  calc
    Measure.map (fun v ↦ (X v, Y v)) muBlocks =
        (Measure.map X muBlocks).prod (Measure.map Y muBlocks) := by
      simpa [X, Y, Function.comp_def] using hmap
    _ = _ := by rw [hX, hY]

/-- Homogeneous alternative columns written without the matrix wrapper. -/
def stableMatchingHomogeneousAlternativeColumns
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s r : ℕ) (rho : ℝ) (w : StableMatchingBaseSample E s r) :
    Sum (Fin 2 × Fin s) (Fin r) → E
  | Sum.inl (i, e) => stableMatchingPairColumn rho i (w.1 e)
  | Sum.inr j => w.2 j

theorem measurable_stableMatchingHomogeneousAlternativeColumns
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s r : ℕ) (rho : ℝ) :
    Measurable (stableMatchingHomogeneousAlternativeColumns
      (E := E) s r rho) := by
  unfold stableMatchingHomogeneousAlternativeColumns
  refine measurable_pi_lambda _ fun j ↦ ?_
  rcases j with ⟨i, e⟩ | j
  · exact (measurable_stableMatchingPairColumn rho i).comp
      ((measurable_pi_apply e).comp measurable_fst)
  · exact (measurable_pi_apply j).comp measurable_snd

/-- A special-block column and a singleton column have the independent
standard Gaussian product law. -/
theorem map_pairBlock_singletonColumns_eq_gaussianProduct
    {m s r : ℕ} (rho : ℝ) (hrho : |rho| < 1)
    (i : Fin 2) (e : Fin s) (j : Fin r) :
    Measure.map
        (fun w : StableMatchingBaseSample
            (EuclideanSpace ℝ (Fin m)) s r ↦
          (stableMatchingPairColumn rho i (w.1 e), w.2 j))
        (stableMatchingBaseMeasure (EuclideanSpace ℝ (Fin m)) s r) =
      (stdGaussian (EuclideanSpace ℝ (Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  let E := EuclideanSpace ℝ (Fin m)
  let muPair : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let muBlocks : Measure (Fin s → E × E) := Measure.pi fun _ : Fin s ↦ muPair
  let muSingles : Measure (Fin r → E) := Measure.pi fun _ : Fin r ↦ stdGaussian E
  let F : (Fin s → E × E) → E :=
    fun v ↦ stableMatchingPairColumn rho i (v e)
  let G : (Fin r → E) → E := fun v ↦ v j
  have hprod := Measure.map_prod_map muBlocks muSingles
    ((measurable_stableMatchingPairColumn rho i).comp (measurable_pi_apply e))
    (measurable_pi_apply j)
  have hF : Measure.map F muBlocks = stdGaussian E := by
    simpa [F, muBlocks, muPair] using
      map_eval_stableMatchingPairColumn_eq_stdGaussian
        (m := m) rho hrho i e
  have hG : Measure.map G muSingles = stdGaussian E := by
    exact (measurePreserving_eval (fun _ : Fin r ↦ stdGaussian E) j).map_eq
  change Measure.map (Prod.map F G) (muBlocks.prod muSingles) = _
  calc
    Measure.map (Prod.map F G) (muBlocks.prod muSingles) =
        (Measure.map F muBlocks).prod (Measure.map G muSingles) := by
      simpa [F, G, Function.comp_def] using hprod.symm
    _ = _ := by rw [hF, hG]

/-- A special-block column and a column of another planted block have the
independent standard Gaussian product law on the full base space. -/
theorem map_pairBlock_otherBlockColumns_eq_gaussianProduct
    {m s r : ℕ} (rho : ℝ) (hrho : |rho| < 1)
    (i j : Fin 2) {e f : Fin s} (hef : e ≠ f) :
    Measure.map
        (fun w : StableMatchingBaseSample
            (EuclideanSpace ℝ (Fin m)) s r ↦
          (stableMatchingPairColumn rho i (w.1 e),
            stableMatchingPairColumn rho j (w.1 f)))
        (stableMatchingBaseMeasure (EuclideanSpace ℝ (Fin m)) s r) =
      (stdGaussian (EuclideanSpace ℝ (Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  let E := EuclideanSpace ℝ (Fin m)
  let muPair : Measure (E × E) := (stdGaussian E).prod (stdGaussian E)
  let muBlocks : Measure (Fin s → E × E) := Measure.pi fun _ : Fin s ↦ muPair
  let muSingles : Measure (Fin r → E) := Measure.pi fun _ : Fin r ↦ stdGaussian E
  let F : (Fin s → E × E) → E × E := fun v ↦
    (stableMatchingPairColumn rho i (v e),
      stableMatchingPairColumn rho j (v f))
  have hfst : Measure.map Prod.fst (muBlocks.prod muSingles) = muBlocks := by
    rw [Measure.map_fst_prod]
    simp
  change Measure.map (F ∘ Prod.fst) (muBlocks.prod muSingles) = _
  calc
    Measure.map (F ∘ Prod.fst) (muBlocks.prod muSingles) =
        Measure.map F (Measure.map Prod.fst (muBlocks.prod muSingles)) := by
      exact (Measure.map_map
        (((measurable_stableMatchingPairColumn rho i).comp
          (measurable_pi_apply e)).prodMk
            ((measurable_stableMatchingPairColumn rho j).comp
              (measurable_pi_apply f)))
        measurable_fst).symm
    _ = Measure.map F muBlocks := by rw [hfst]
    _ = _ := by
      simpa [F, muBlocks, muPair] using
        map_two_distinct_pairBlockColumns_eq_gaussianProduct
          (m := m) rho hrho i j hef

/-- Exact pair law for every nonplanted edge incident to a special block. -/
theorem map_special_nonpartner_columns_eq_gaussianProduct
    {m s r : ℕ} (rho : ℝ) (hrho : |rho| < 1)
    (i : Fin 2) (e : Fin s)
    (j : Sum (Fin 2 × Fin s) (Fin r))
    (hj : ∀ k : Fin 2, j ≠ Sum.inl (k, e)) :
    Measure.map
        (fun w : StableMatchingBaseSample
            (EuclideanSpace ℝ (Fin m)) s r ↦
          (stableMatchingHomogeneousAlternativeColumns s r rho w
              (Sum.inl (i, e)),
            stableMatchingHomogeneousAlternativeColumns s r rho w j))
        (stableMatchingBaseMeasure (EuclideanSpace ℝ (Fin m)) s r) =
      (stdGaussian (EuclideanSpace ℝ (Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  rcases j with ⟨k, f⟩ | j
  · have hef : e ≠ f := by
      intro h
      subst f
      exact hj k rfl
    simpa [stableMatchingHomogeneousAlternativeColumns] using
      map_pairBlock_otherBlockColumns_eq_gaussianProduct
        (m := m) (r := r) rho hrho i k hef
  · simpa [stableMatchingHomogeneousAlternativeColumns] using
      map_pairBlock_singletonColumns_eq_gaussianProduct
        (m := m) rho hrho i e j

/-- Ambient-normalized Pearson height of two columns in the homogeneous
alternative family. -/
def stableMatchingHomogeneousPointScore
    (m p s r : ℕ) (rho : ℝ)
    (w : StableMatchingBaseSample (EuclideanSpace ℝ (Fin m)) s r)
    (u v : Sum (Fin 2 × Fin s) (Fin r)) : ℝ :=
  (m : ℝ) * squaredNormalizedInner
      (stableMatchingHomogeneousAlternativeColumns s r rho w u)
      (stableMatchingHomogeneousAlternativeColumns s r rho w v) -
    classicalCoherenceThreshold m p 0

theorem measurable_stableMatchingHomogeneousPointScore
    (m p s r : ℕ) (rho : ℝ)
    (u v : Sum (Fin 2 × Fin s) (Fin r)) :
    Measurable (fun w : StableMatchingBaseSample
        (EuclideanSpace ℝ (Fin m)) s r ↦
      stableMatchingHomogeneousPointScore m p s r rho w u v) := by
  unfold stableMatchingHomogeneousPointScore
  have hcols := measurable_stableMatchingHomogeneousAlternativeColumns
    (E := EuclideanSpace ℝ (Fin m)) s r rho
  exact (measurable_const.mul
    (measurable_uncurry_squaredNormalizedInner.comp
      (((measurable_pi_apply u).comp hcols).prodMk
        ((measurable_pi_apply v).comp hcols)))).sub measurable_const

/-- One potential dirty edge: it is active only when the second endpoint is
outside the planted block of the first endpoint. -/
def stableMatchingDirtyPairWindowEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s r : ℕ) (rho : ℝ) (q : Fin 2 × Fin s)
    (j : Sum (Fin 2 × Fin s) (Fin r)) :
    Set (StableMatchingBaseSample (EuclideanSpace ℝ (Fin m)) s r) :=
  if ∀ k : Fin 2, j ≠ Sum.inl (k, q.2) then
    (fun w ↦ stableMatchingHomogeneousPointScore m p s r rho w
      (Sum.inl q) j) ⁻¹' finiteScoreWindowUnion W
  else ∅

theorem measurableSet_stableMatchingDirtyPairWindowEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s r : ℕ) (rho : ℝ) (q : Fin 2 × Fin s)
    (j : Sum (Fin 2 × Fin s) (Fin r)) :
    MeasurableSet (stableMatchingDirtyPairWindowEvent W m p s r rho q j) := by
  unfold stableMatchingDirtyPairWindowEvent
  split_ifs
  · exact (measurableSet_finiteScoreWindowUnion W).preimage
      (measurable_stableMatchingHomogeneousPointScore
        m p s r rho (Sum.inl q) j)
  · exact MeasurableSet.empty

/-- Union of all nonplanted window hits incident to special vertices.  The
indexing deliberately counts every edge at most twice; this gives the clean
`2 s p` envelope used asymptotically. -/
def stableMatchingDirtyFiniteUnionEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s r : ℕ) (rho : ℝ) :
    Set (StableMatchingBaseSample (EuclideanSpace ℝ (Fin m)) s r) :=
  ⋃ q : Fin 2 × Fin s, ⋃ j : Sum (Fin 2 × Fin s) (Fin r),
    stableMatchingDirtyPairWindowEvent W m p s r rho q j

theorem measurableSet_stableMatchingDirtyFiniteUnionEvent
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (m p s r : ℕ) (rho : ℝ) :
    MeasurableSet (stableMatchingDirtyFiniteUnionEvent W m p s r rho) := by
  exact MeasurableSet.iUnion fun q ↦ MeasurableSet.iUnion fun j ↦
    measurableSet_stableMatchingDirtyPairWindowEvent W m p s r rho q j

/-- Every active dirty pair is central and its window probability is bounded
by the null tail at a common lower endpoint. -/
theorem measureReal_stableMatchingDirtyPairWindowEvent_le_betaTail
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p s r : ℕ} (hm : 2 ≤ m) (rho : ℝ) (hrho : |rho| < 1)
    (c : ℝ) (hc : ∀ i, c ≤ W.lower i)
    (q : Fin 2 × Fin s)
    (j : Sum (Fin 2 × Fin s) (Fin r)) :
    (stableMatchingBaseMeasure (EuclideanSpace ℝ (Fin m)) s r).real
        (stableMatchingDirtyPairWindowEvent W m p s r rho q j) ≤
      betaCorrelationTailProbability m p c := by
  by_cases hj : ∀ k : Fin 2, j ≠ Sum.inl (k, q.2)
  · let E := EuclideanSpace ℝ (Fin m)
    let mu := stableMatchingBaseMeasure E s r
    letI : IsProbabilityMeasure mu := by
      dsimp [mu, stableMatchingBaseMeasure]
      infer_instance
    let F : StableMatchingBaseSample E s r → E × E := fun w ↦
      (stableMatchingHomogeneousAlternativeColumns s r rho w (Sum.inl q),
        stableMatchingHomogeneousAlternativeColumns s r rho w j)
    let A : Set (E × E) := {z |
      classicalCoherenceThreshold m p c <
        (m : ℝ) * squaredNormalizedInner z.1 z.2}
    have hmap : Measure.map F mu = (stdGaussian E).prod (stdGaussian E) := by
      simpa [F, mu] using map_special_nonpartner_columns_eq_gaussianProduct
        (m := m) rho hrho q.1 q.2 j hj
    have hsubset : stableMatchingDirtyPairWindowEvent W m p s r rho q j ⊆
        F ⁻¹' A := by
      intro w hw
      rw [stableMatchingDirtyPairWindowEvent, if_pos hj] at hw
      have hscore := finiteScoreWindowUnion_subset_Ioi W c hc hw
      change classicalCoherenceThreshold m p c <
        (m : ℝ) * squaredNormalizedInner
          (stableMatchingHomogeneousAlternativeColumns s r rho w (Sum.inl q))
          (stableMatchingHomogeneousAlternativeColumns s r rho w j)
      change c < (m : ℝ) * squaredNormalizedInner
          (stableMatchingHomogeneousAlternativeColumns s r rho w (Sum.inl q))
          (stableMatchingHomogeneousAlternativeColumns s r rho w j) -
        classicalCoherenceThreshold m p 0 at hscore
      have hshift := classicalCoherenceThreshold_eq_zero_add m p c
      linarith
    have hmeasA : MeasurableSet A := by
      exact measurableSet_Ioi.preimage
        (measurable_const.mul measurable_uncurry_squaredNormalizedInner)
    calc
      mu.real (stableMatchingDirtyPairWindowEvent W m p s r rho q j) ≤
          mu.real (F ⁻¹' A) := measureReal_mono hsubset
      _ = ((stdGaussian E).prod (stdGaussian E)).real A := by
        let hcols := measurable_stableMatchingHomogeneousAlternativeColumns
          (E := E) s r rho
        have hF : Measurable F :=
          ((measurable_pi_apply (Sum.inl q)).comp hcols).prodMk
            ((measurable_pi_apply j).comp hcols)
        change (mu (F ⁻¹' A)).toReal =
          (((stdGaussian E).prod (stdGaussian E)) A).toReal
        rw [← Measure.map_apply hF hmeasA, hmap]
      _ = betaCorrelationTailProbability m p c := by
        exact gaussianPair_classicalExceedanceProbability_eq_betaCorrelationTail
          m p (by simp [E]) hm c
  · rw [stableMatchingDirtyPairWindowEvent, if_neg hj]
    simp only [measureReal_empty]
    exact measureReal_nonneg

/-- Finite-sample union bound for the complete dirty event. -/
theorem measureReal_stableMatchingDirtyFiniteUnionEvent_le
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    {m p s r : ℕ} (hm : 2 ≤ m) (rho : ℝ) (hrho : |rho| < 1)
    (c : ℝ) (hc : ∀ i, c ≤ W.lower i) :
    (stableMatchingBaseMeasure (EuclideanSpace ℝ (Fin m)) s r).real
        (stableMatchingDirtyFiniteUnionEvent W m p s r rho) ≤
      2 * (s : ℝ) * ((2 * s + r : ℕ) : ℝ) *
        betaCorrelationTailProbability m p c := by
  let mu := stableMatchingBaseMeasure (EuclideanSpace ℝ (Fin m)) s r
  calc
    mu.real (stableMatchingDirtyFiniteUnionEvent W m p s r rho) ≤
        ∑ q : Fin 2 × Fin s, ∑ j : Sum (Fin 2 × Fin s) (Fin r),
          mu.real (stableMatchingDirtyPairWindowEvent W m p s r rho q j) := by
      unfold stableMatchingDirtyFiniteUnionEvent
      exact (measureReal_iUnion_fintype_le _).trans
        (Finset.sum_le_sum fun q _hq ↦ measureReal_iUnion_fintype_le _)
    _ ≤ ∑ _q : Fin 2 × Fin s,
        ∑ _j : Sum (Fin 2 × Fin s) (Fin r),
          betaCorrelationTailProbability m p c := by
      exact Finset.sum_le_sum fun q _hq ↦ Finset.sum_le_sum fun j _hj ↦
        measureReal_stableMatchingDirtyPairWindowEvent_le_betaTail
          W hm rho hrho c hc q j
    _ = _ := by
      simp [Fintype.card_sum, Fintype.card_prod]
      ring

/-- Along every all-gap sequence with `s_p=o(p)`, all dirty edges disappear
from a fixed finite score union in probability. -/
theorem tendsto_measureReal_stableMatchingDirtyFiniteUnionEvent_zero
    {ι : Type*} [Fintype ι] (W : FiniteScoreWindowFamily ι)
    (c : ℝ) (hc : ∀ i, c ≤ W.lower i)
    {mseq sseq rseq : ℕ → ℕ} {rhoSeq : ℕ → ℝ}
    (hdecomp : ∀ p, 2 * sseq p + rseq p = p)
    (hadm : ∀ᶠ p in atTop, Admissible (mseq p) p)
    (hsparse : Tendsto (fun p : ℕ ↦ (sseq p : ℝ) / (p : ℝ))
      atTop (nhds 0))
    (hrho : ∀ᶠ p in atTop, |rhoSeq p| < 1) :
    Tendsto (fun p : ℕ ↦
      (stableMatchingBaseMeasure
        (EuclideanSpace ℝ (Fin (mseq p))) (sseq p) (rseq p)).real
          (stableMatchingDirtyFiniteUnionEvent W (mseq p) p
            (sseq p) (rseq p) (rhoSeq p)))
      atTop (nhds 0) := by
  have henv := tendsto_two_mul_matching_mul_ambient_mul_betaTail_zero
    hadm hsparse c
  apply squeeze_zero'
  · filter_upwards with p
    exact measureReal_nonneg
  · filter_upwards [hadm, hrho] with p hp hstrict
    calc
      (stableMatchingBaseMeasure
        (EuclideanSpace ℝ (Fin (mseq p))) (sseq p) (rseq p)).real
          (stableMatchingDirtyFiniteUnionEvent W (mseq p) p
            (sseq p) (rseq p) (rhoSeq p)) ≤
        2 * (sseq p : ℝ) *
          ((2 * sseq p + rseq p : ℕ) : ℝ) *
            betaCorrelationTailProbability (mseq p) p c :=
        measureReal_stableMatchingDirtyFiniteUnionEvent_le
          W (hp.1.trans hp.2) (rhoSeq p) hstrict c hc
      _ = 2 * (sseq p : ℝ) * (p : ℝ) *
          betaCorrelationTailProbability (mseq p) p c := by
        rw [hdecomp p]
  · exact henv

end

end LogdetLean.Coherence
