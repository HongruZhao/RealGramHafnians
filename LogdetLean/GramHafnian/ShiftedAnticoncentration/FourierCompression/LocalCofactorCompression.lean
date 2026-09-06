import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.GeneralBilinearGaussian
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseLiteral
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CoordinateExposure
import Mathlib.MeasureTheory.Integral.Pi
/-!
# Literal local Fourier compression for the odd cofactor vector

This file disintegrates the iid column law into a background family and two
exposed circular columns.  It then transports the exposed columns to real
standard Gaussian Euclidean space and applies the arbitrary-operator
completed-square kernel.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 1600000

/-- Real Euclidean space obtained by separating real and imaginary
coordinates of a complex `k`-column. -/
abbrev CofactorRealSpace (k : ℕ) :=
  EuclideanSpace ℝ (ComplexRealificationIndex k)

/-- The unscaled real/imaginary coordinate isometry. -/
def complexEuclideanRealificationIsometry (k : ℕ) :
    CircularEuclideanSpace k ≃ₗᵢ[ℝ] CofactorRealSpace k where
  toFun x := WithLp.toLp 2 (fun s ↦ match s with
    | Sum.inl p => (x p).re
    | Sum.inr p => (x p).im)
  invFun y := WithLp.toLp 2 (fun p ↦
    ((y (Sum.inl p) : ℝ) : ℂ) + ((y (Sum.inr p) : ℝ) : ℂ) * Complex.I)
  left_inv x := by
    ext p
    apply Complex.ext <;> simp
  right_inv y := by
    ext s
    cases s <;> simp
  map_add' x y := by
    ext s
    cases s <;> simp
  map_smul' c x := by
    ext s
    cases s <;> simp [Complex.real_smul]
  norm_map' x := by
    have hsquare :
        ‖(WithLp.toLp 2 (fun s ↦ match s with
          | Sum.inl p => (x p).re
          | Sum.inr p => (x p).im) : CofactorRealSpace k)‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      rw [Fintype.sum_sum_type]
      simp only [PiLp.toLp_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Real.norm_eq_abs, sq_abs]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    change ‖(WithLp.toLp 2 (fun s ↦ match s with
      | Sum.inl p => (x p).re
      | Sum.inr p => (x p).im) : CofactorRealSpace k)‖ = ‖x‖
    nlinarith [norm_nonneg
      (WithLp.toLp 2 (fun s ↦ match s with
        | Sum.inl p => (x p).re
        | Sum.inr p => (x p).im) : CofactorRealSpace k), norm_nonneg x]

/-- The manuscript realification `sqrt 2 (Re x, Im x)` as an ordinary
measurable map into real Euclidean space. -/
def complexRealificationEuclidean {k : ℕ} (x : Fin k → ℂ) :
    CofactorRealSpace k :=
  WithLp.toLp 2 (complexRealification x)

@[fun_prop]
theorem measurable_complexRealificationEuclidean {k : ℕ} :
    Measurable (complexRealificationEuclidean (k := k)) := by
  unfold complexRealificationEuclidean complexRealification
  apply (WithLp.measurable_toLp 2 (ComplexRealificationIndex k → ℝ)).comp
  rw [measurable_pi_iff]
  intro s
  cases s with
  | inl p =>
      exact measurable_const.mul
        (Complex.measurable_re.comp (measurable_pi_apply p))
  | inr p =>
      exact measurable_const.mul
        (Complex.measurable_im.comp (measurable_pi_apply p))

/-- The manuscript realification sends one iid circular column exactly to
real standard Gaussian measure. -/
theorem map_complexRealificationEuclidean_circularGaussianVector (k : ℕ) :
    (circularGaussianVector k).map complexRealificationEuclidean =
      stdGaussian (CofactorRealSpace k) := by
  let K := complexEuclideanRealificationIsometry k
  let r : ℝ := (Real.sqrt 2)⁻¹
  let s : ℝ := Real.sqrt 2
  have hfactor : Real.sqrt 2 * r = 1 := by
    dsimp [r]
    exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hmap := map_toLp_pi_circularGaussian_eq_scaled_stdGaussian k
  change (Measure.pi fun _ : Fin k ↦ circularGaussian).map
      complexRealificationEuclidean = _
  have hrealify : complexRealificationEuclidean =
      (fun x : CircularEuclideanSpace k ↦ s • K x) ∘ WithLp.toLp 2 := by
    funext x
    ext u
    cases u <;>
      rfl
  rw [hrealify, ← Measure.map_map (by fun_prop)
    (WithLp.measurable_toLp 2 (Fin k → ℂ))]
  rw [hmap]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun :
      (fun x : CircularEuclideanSpace k ↦ s • K x) ∘
          (fun x : CircularEuclideanSpace k ↦ r • x) =
        K := by
    funext x
    change s • K (r • x) = K x
    rw [map_smul, smul_smul]
    change (Real.sqrt 2 * r) • K x = K x
    rw [hfactor, one_smul]
  rw [hfun]
  exact stdGaussian_map K

/-- Split an iid family into its last column `Y`, penultimate column `X`,
and the first `m` background columns. -/
def splitTwoExposedColumns (m k : ℕ) :
    (Fin (m + 2) → (Fin k → ℂ)) ≃ᵐ
      (Fin k → ℂ) × ((Fin k → ℂ) × (Fin m → (Fin k → ℂ))) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 2) ↦ Fin k → ℂ) (Fin.last (m + 1))).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin k → ℂ))
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (m + 1) ↦ Fin k → ℂ) (Fin.last m)))

theorem splitTwoExposedColumns_apply
    {m k : ℕ} (A : Fin (m + 2) → (Fin k → ℂ)) :
    splitTwoExposedColumns m k A =
      (A (exposedYIndex m),
        (A (exposedXIndex m), fun i ↦ A (remainingIndex m i))) := by
  unfold splitTwoExposedColumns
  rw [MeasurableEquiv.trans_apply]
  change
    (A (Fin.last (m + 1)),
      (A ((Fin.last (m + 1)).succAbove (Fin.last m)),
        fun i ↦ A ((Fin.last (m + 1)).succAbove ((Fin.last m).succAbove i)))) = _
  apply Prod.ext
  · change A (Fin.last (m + 1)) = A (exposedYIndex m)
    congr 1
  · change
      (A ((Fin.last (m + 1)).succAbove (Fin.last m)),
        fun i ↦ A ((Fin.last (m + 1)).succAbove ((Fin.last m).succAbove i))) =
      (A (exposedXIndex m), fun i ↦ A (remainingIndex m i))
    apply Prod.ext
    · change A ((Fin.last (m + 1)).succAbove (Fin.last m)) =
        A (exposedXIndex m)
      rw [Fin.succAbove_last_apply]
      congr 1
    · funext i
      change A ((Fin.last (m + 1)).succAbove ((Fin.last m).succAbove i)) =
        A (remainingIndex m i)
      rw [Fin.succAbove_last_apply, Fin.succAbove_last_apply]
      congr 1

/-- Exact iid measure disintegration into `Y × (X × background)`. -/
theorem measurePreserving_splitTwoExposedColumns (m k : ℕ) :
    MeasurePreserving (splitTwoExposedColumns m k)
      (Measure.pi fun _ : Fin (m + 2) ↦ circularGaussianVector k)
      ((circularGaussianVector k).prod
        ((circularGaussianVector k).prod
          (Measure.pi fun _ : Fin m ↦ circularGaussianVector k))) := by
  have hY := measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 2) ↦ circularGaussianVector k) (Fin.last (m + 1))
  have hX := measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) ↦ circularGaussianVector k) (Fin.last m)
  have hprod := (MeasurePreserving.id (circularGaussianVector k)).prod hX
  exact hprod.comp hY

/-- Reassociate and permute `Y × (X × R)` into `R × (X × Y)`. -/
def yxrToRxy {Y X R : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace R] :
    Y × (X × R) ≃ᵐ R × (X × Y) :=
  (MeasurableEquiv.prodAssoc : (Y × X) × R ≃ᵐ Y × (X × R)).symm |>.trans
    ((MeasurableEquiv.prodComm : (Y × X) × R ≃ᵐ R × (Y × X)).trans
      ((MeasurableEquiv.refl R).prodCongr
        (MeasurableEquiv.prodComm : Y × X ≃ᵐ X × Y)))

@[simp]
theorem yxrToRxy_apply {Y X R : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace R]
    (y : Y) (x : X) (r : R) :
    yxrToRxy (y, (x, r)) = (r, (x, y)) := by
  rfl

/-- The reassociation/permutation is measure preserving for product
measures. -/
theorem measurePreserving_yxrToRxy
    {Y X R : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    [MeasurableSpace R] (muY : Measure Y) (muX : Measure X)
    (muR : Measure R) [SFinite muY] [SFinite muX] [SFinite muR] :
    MeasurePreserving (yxrToRxy (Y := Y) (X := X) (R := R))
      (muY.prod (muX.prod muR)) (muR.prod (muX.prod muY)) := by
  have h1 := (measurePreserving_prodAssoc muY muX muR).symm
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodComm : (Y × X) × R ≃ᵐ R × (Y × X))
      ((muY.prod muX).prod muR) (muR.prod (muY.prod muX)) := by
    simpa [MeasurableEquiv.prodComm] using
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := muY.prod muX) (ν := muR))
  have h3 : MeasurePreserving
      ((MeasurableEquiv.refl R).prodCongr
        (MeasurableEquiv.prodComm : Y × X ≃ᵐ X × Y))
      (muR.prod (muY.prod muX)) (muR.prod (muX.prod muY)) := by
    simpa [MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm] using
      ((MeasurePreserving.id muR).prod
        (MeasureTheory.Measure.measurePreserving_swap
          (μ := muY) (ν := muX)))
  refine (h3.comp (h2.comp h1)).congr
    (yxrToRxy (Y := Y) (X := X) (R := R)).measurable ?_
  filter_upwards [] with p
  rcases p with ⟨y, x, r⟩
  rfl

/-- Split directly into `background × (X × Y)`, the order used for
conditional integration. -/
def splitTwoExposedColumnsRXY (m k : ℕ) :
    (Fin (m + 2) → (Fin k → ℂ)) ≃ᵐ
      (Fin m → (Fin k → ℂ)) × ((Fin k → ℂ) × (Fin k → ℂ)) :=
  (splitTwoExposedColumns m k).trans yxrToRxy

theorem splitTwoExposedColumnsRXY_apply
    {m k : ℕ} (A : Fin (m + 2) → (Fin k → ℂ)) :
    splitTwoExposedColumnsRXY m k A =
      ((fun i ↦ A (remainingIndex m i)),
        (A (exposedXIndex m), A (exposedYIndex m))) := by
  rw [splitTwoExposedColumnsRXY, MeasurableEquiv.trans_apply,
    splitTwoExposedColumns_apply]
  rfl

/-- Exact iid measure disintegration in conditional-integration order. -/
theorem measurePreserving_splitTwoExposedColumnsRXY (m k : ℕ) :
    MeasurePreserving (splitTwoExposedColumnsRXY m k)
      (Measure.pi fun _ : Fin (m + 2) ↦ circularGaussianVector k)
      ((Measure.pi fun _ : Fin m ↦ circularGaussianVector k).prod
        ((circularGaussianVector k).prod (circularGaussianVector k))) := by
  exact (measurePreserving_yxrToRxy
    (circularGaussianVector k) (circularGaussianVector k)
      (Measure.pi fun _ : Fin m ↦ circularGaussianVector k)).comp
        (measurePreserving_splitTwoExposedColumns m k)

/-- Reassemble a background family and two displayed columns. -/
def assembleTwoExposedColumns {m k : ℕ}
    (R : Fin m → (Fin k → ℂ)) (X Y : Fin k → ℂ) :
    Fin (m + 2) → (Fin k → ℂ) :=
  (splitTwoExposedColumnsRXY m k).symm (R, (X, Y))

theorem assembleTwoExposedColumns_coordinates
    {m k : ℕ} (R : Fin m → (Fin k → ℂ)) (X Y : Fin k → ℂ) :
    ((fun i ↦ assembleTwoExposedColumns R X Y (remainingIndex m i)) = R) ∧
      assembleTwoExposedColumns R X Y (exposedXIndex m) = X ∧
      assembleTwoExposedColumns R X Y (exposedYIndex m) = Y := by
  have h := splitTwoExposedColumnsRXY_apply
    (assembleTwoExposedColumns R X Y)
  rw [assembleTwoExposedColumns,
    (splitTwoExposedColumnsRXY m k).apply_symm_apply] at h
  rcases Prod.mk.inj h with ⟨hR, hXY⟩
  rcases Prod.mk.inj hXY with ⟨hX, hY⟩
  exact ⟨hR.symm, hX.symm, hY.symm⟩

/-! ## Matrices as continuous maps on Euclidean realifications -/

/-- The two real coordinates of a complex Fourier weight, bundled as a
two-dimensional Euclidean vector. -/
def complexPhaseCoordinatesEuclidean (w : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (complexPhaseCoordinates w)

/-- The background bilinear phase matrix as a continuous endomorphism. -/
def cofactorBackgroundPhaseCLM {m k : ℕ}
    (A : TwoExposedColumnFamily m k) (w : Fin (m + 2) → ℂ) :
    CofactorRealSpace k →L[ℝ] CofactorRealSpace k :=
  (Matrix.toEuclideanLin (cofactorBackgroundPhaseMatrix A w)).toContinuousLinearMap

/-- The common endpoint phase matrix as a continuous map from the two
Fourier-weight coordinates. -/
def cofactorLinearPhaseCLM {m k : ℕ}
    (A : TwoExposedColumnFamily m k) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] CofactorRealSpace k :=
  (Matrix.toEuclideanLin
    (cofactorLinearPhaseMatrix (cofactorQ A))).toContinuousLinearMap

/-- Matrix multiplication in Euclidean coordinates is exactly the
manuscript transpose-bilinear expression. -/
theorem inner_toEuclideanLin_eq_realTransposeBilinearPhase
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (g : ι → ℝ) (T : Matrix ι κ ℝ) (h : κ → ℝ) :
    inner ℝ (WithLp.toLp 2 g)
        (Matrix.toEuclideanLin T (WithLp.toLp 2 h)) =
      realTransposeBilinearPhase g T h := by
  rw [Matrix.toEuclideanLin_toLp]
  unfold realTransposeBilinearPhase
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [mul_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exact bilinear phase bridge for the conditioned cofactor kernel. -/
theorem inner_cofactorBackgroundPhaseCLM_eq
    {m k : ℕ} (A : TwoExposedColumnFamily m k)
    (w : Fin (m + 2) → ℂ) (X Y : Fin k → ℂ) :
    inner ℝ (complexRealificationEuclidean X)
        (cofactorBackgroundPhaseCLM A w
          (complexRealificationEuclidean Y)) =
      realTransposeBilinearPhase (complexRealification X)
        (cofactorBackgroundPhaseMatrix A w) (complexRealification Y) := by
  exact inner_toEuclideanLin_eq_realTransposeBilinearPhase
    (complexRealification X) (cofactorBackgroundPhaseMatrix A w)
      (complexRealification Y)

/-- Exact linear phase bridge for the common endpoint matrix. -/
theorem inner_cofactorLinearPhaseCLM_eq
    {m k : ℕ} (A : TwoExposedColumnFamily m k)
    (X : Fin k → ℂ) (w : ℂ) :
    inner ℝ (complexRealificationEuclidean X)
        (cofactorLinearPhaseCLM A (complexPhaseCoordinatesEuclidean w)) =
      realTransposeLinearPhase (complexRealification X)
        (cofactorLinearPhaseMatrix (cofactorQ A))
        (complexPhaseCoordinates w) := by
  exact inner_toEuclideanLin_eq_realTransposeBilinearPhase
    (complexRealification X) (cofactorLinearPhaseMatrix (cofactorQ A))
      (complexPhaseCoordinates w)

/-! ## Dependence only on the background columns -/

theorem remainingHafnianDeleteOne_congr_background
    {m k : ℕ} {A B : TwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i))
    (a : Fin m) :
    remainingHafnianDeleteOne A a = remainingHafnianDeleteOne B a := by
  unfold remainingHafnianDeleteOne
  congr 1
  funext i j
  unfold columnTransposeGram
  apply Finset.sum_congr rfl
  intro p _hp
  change A (remainingIndex m i.1) p * A (remainingIndex m j.1) p =
    B (remainingIndex m i.1) p * B (remainingIndex m j.1) p
  rw [hAB i.1, hAB j.1]

theorem remainingHafnianDeleteThree_congr_background
    {m k : ℕ} {A B : TwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i))
    (j a b : Fin m) :
    remainingHafnianDeleteThree A j a b =
      remainingHafnianDeleteThree B j a b := by
  unfold remainingHafnianDeleteThree
  congr 1
  funext i l
  unfold columnTransposeGram
  apply Finset.sum_congr rfl
  intro p _hp
  change A (remainingIndex m i.1) p * A (remainingIndex m l.1) p =
    B (remainingIndex m i.1) p * B (remainingIndex m l.1) p
  rw [hAB i.1, hAB l.1]

theorem cofactorQ_congr_background
    {m k : ℕ} {A B : TwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i)) :
    cofactorQ A = cofactorQ B := by
  funext p
  unfold cofactorQ
  apply Finset.sum_congr rfl
  intro a _ha
  rw [remainingHafnianDeleteOne_congr_background hAB a, hAB a]

theorem cofactorM_congr_background
    {m k : ℕ} {A B : TwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i))
    (j : Fin m) :
    cofactorM A j = cofactorM B j := by
  funext p q
  unfold cofactorM
  rw [remainingHafnianDeleteOne_congr_background hAB j]
  congr 1
  apply Finset.sum_congr rfl
  intro b _hb
  apply Finset.sum_congr rfl
  intro a _ha
  rw [remainingHafnianDeleteThree_congr_background hAB j a.1 b.1,
    hAB a.1, hAB b.1]

theorem cofactorBackgroundPhaseMatrix_congr_background
    {m k : ℕ} {A B : TwoExposedColumnFamily m k}
    (hAB : ∀ i : Fin m, A (remainingIndex m i) = B (remainingIndex m i))
    (w : Fin (m + 2) → ℂ) :
    cofactorBackgroundPhaseMatrix A w = cofactorBackgroundPhaseMatrix B w := by
  funext p q
  unfold cofactorBackgroundPhaseMatrix
  apply Finset.sum_congr rfl
  intro j _hj
  rw [cofactorM_congr_background hAB j]

/-- Canonical background-dependent bilinear operator (zero displayed
columns are used only as a representative). -/
def backgroundCofactorT {m k : ℕ}
    (R : Fin m → (Fin k → ℂ)) (w : Fin (m + 2) → ℂ) :
    CofactorRealSpace k →L[ℝ] CofactorRealSpace k :=
  cofactorBackgroundPhaseCLM (assembleTwoExposedColumns R 0 0) w

/-- Canonical background-dependent common endpoint map. -/
def backgroundCofactorL {m k : ℕ}
    (R : Fin m → (Fin k → ℂ)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] CofactorRealSpace k :=
  cofactorLinearPhaseCLM (assembleTwoExposedColumns R 0 0)

theorem cofactorBackgroundPhaseCLM_assemble_eq
    {m k : ℕ} (R : Fin m → (Fin k → ℂ))
    (X Y : Fin k → ℂ) (w : Fin (m + 2) → ℂ) :
    cofactorBackgroundPhaseCLM (assembleTwoExposedColumns R X Y) w =
      backgroundCofactorT R w := by
  simp only [cofactorBackgroundPhaseCLM, backgroundCofactorT]
  apply congrArg (fun M : Matrix (ComplexRealificationIndex k)
    (ComplexRealificationIndex k) ℝ ↦
      (Matrix.toEuclideanLin M).toContinuousLinearMap)
  apply cofactorBackgroundPhaseMatrix_congr_background
  intro i
  have hXY := congrFun (assembleTwoExposedColumns_coordinates R X Y).1 i
  have h00 := congrFun
    (assembleTwoExposedColumns_coordinates R (0 : Fin k → ℂ) 0).1 i
  exact hXY.trans h00.symm

theorem cofactorLinearPhaseCLM_assemble_eq
    {m k : ℕ} (R : Fin m → (Fin k → ℂ))
    (X Y : Fin k → ℂ) :
    cofactorLinearPhaseCLM (assembleTwoExposedColumns R X Y) =
      backgroundCofactorL R := by
  simp only [cofactorLinearPhaseCLM, backgroundCofactorL]
  apply congrArg (fun M : Matrix (ComplexRealificationIndex k) (Fin 2) ℝ ↦
    (Matrix.toEuclideanLin M).toContinuousLinearMap)
  apply congrArg cofactorLinearPhaseMatrix
  apply cofactorQ_congr_background
  intro i
  have hXY := congrFun (assembleTwoExposedColumns_coordinates R X Y).1 i
  have h00 := congrFun
    (assembleTwoExposedColumns_coordinates R (0 : Fin k → ℂ) 0).1 i
  exact hXY.trans h00.symm

/-! ## The exact conditional characteristic kernel -/

theorem sum_fin_two_exposed {m : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin (m + 2) → M) :
    ∑ i, f i =
      (∑ i : Fin m, f (remainingIndex m i)) +
        f (exposedXIndex m) + f (exposedYIndex m) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  congr 1

/-- After fixing the background, the full cofactor Fourier phase is exactly
the arbitrary-operator bilinear Gaussian phase. -/
theorem finiteGramCofactorPhase_assemble_eq_bilinear
    {m k : ℕ} (R : Fin m → (Fin k → ℂ))
    (X Y : Fin k → ℂ) (w : Fin (m + 2) → ℂ) :
    finiteGramCofactorPhase (assembleTwoExposedColumns R X Y) w =
      inner ℝ (complexRealificationEuclidean X)
          (backgroundCofactorT R w (complexRealificationEuclidean Y)) +
        inner ℝ (complexRealificationEuclidean X)
          (backgroundCofactorL R
            (complexPhaseCoordinatesEuclidean (w (exposedYIndex m)))) +
        inner ℝ (complexRealificationEuclidean Y)
          (backgroundCofactorL R
            (complexPhaseCoordinatesEuclidean (w (exposedXIndex m)))) := by
  let A := assembleTwoExposedColumns R X Y
  have hcoord := assembleTwoExposedColumns_coordinates R X Y
  unfold finiteGramCofactorPhase
  rw [sum_fin_two_exposed]
  simp only [Complex.add_re]
  change
    ((∑ j : Fin m,
        w (remainingIndex m j) *
          twoExposedCofactorVector A (remainingIndex m j)).re +
      (w (exposedXIndex m) *
        twoExposedCofactorVector A (exposedXIndex m)).re +
      (w (exposedYIndex m) *
        twoExposedCofactorVector A (exposedYIndex m)).re) = _
  rw [two_exposed_cofactor_phase_exact_T_L_form]
  rw [← inner_cofactorBackgroundPhaseCLM_eq A
    w (A (exposedXIndex m)) (A (exposedYIndex m))]
  rw [← inner_cofactorLinearPhaseCLM_eq A
    (A (exposedXIndex m)) (w (exposedYIndex m))]
  rw [← inner_cofactorLinearPhaseCLM_eq A
    (A (exposedYIndex m)) (w (exposedXIndex m))]
  rw [cofactorBackgroundPhaseCLM_assemble_eq,
    cofactorLinearPhaseCLM_assemble_eq]
  change
    inner ℝ (complexRealificationEuclidean (A (exposedXIndex m)))
          (backgroundCofactorT R w
            (complexRealificationEuclidean (A (exposedYIndex m)))) +
        inner ℝ (complexRealificationEuclidean (A (exposedXIndex m)))
          (backgroundCofactorL R
            (complexPhaseCoordinatesEuclidean (w (exposedYIndex m)))) +
        inner ℝ (complexRealificationEuclidean (A (exposedYIndex m)))
          (backgroundCofactorL R
            (complexPhaseCoordinatesEuclidean (w (exposedXIndex m)))) = _
  dsimp [A]
  rw [hcoord.2.1, hcoord.2.2]

/-- Realification itself, not merely its pushforward equality, is a
measure-preserving map. -/
theorem measurePreserving_complexRealificationEuclidean (k : ℕ) :
    MeasurePreserving (complexRealificationEuclidean (k := k))
      (circularGaussianVector k) (stdGaussian (CofactorRealSpace k)) := by
  constructor
  · exact measurable_complexRealificationEuclidean
  · exact map_complexRealificationEuclidean_circularGaussianVector k

/-- Conditional characteristic function after fixing all background
columns and integrating only the two displayed circular columns. -/
def conditionalCofactorCharacteristic {m k : ℕ}
    (R : Fin m → (Fin k → ℂ)) (w : Fin (m + 2) → ℂ) : ℂ :=
  ∫ p : (Fin k → ℂ) × (Fin k → ℂ),
    finiteGramCofactorPhaseCharacter w
      (assembleTwoExposedColumns R p.1 p.2)
    ∂((circularGaussianVector k).prod (circularGaussianVector k))

/-- The conditional cofactor characteristic is literally the arbitrary
real bilinear Gaussian kernel with the background-dependent `T_R,L_R`. -/
theorem conditionalCofactorCharacteristic_eq_bilinearGaussianIntegral
    {m k : ℕ} (R : Fin m → (Fin k → ℂ))
    (w : Fin (m + 2) → ℂ) :
    conditionalCofactorCharacteristic R w =
      bilinearGaussianIntegral (backgroundCofactorT R w)
        (backgroundCofactorL R)
        (complexPhaseCoordinatesEuclidean (w (exposedXIndex m)))
        (complexPhaseCoordinatesEuclidean (w (exposedYIndex m))) := by
  let rho : ((Fin k → ℂ) × (Fin k → ℂ)) →
      (CofactorRealSpace k × CofactorRealSpace k) :=
    fun p ↦ (complexRealificationEuclidean p.1,
      complexRealificationEuclidean p.2)
  let kernel : CofactorRealSpace k × CofactorRealSpace k → ℂ :=
    fun p ↦ Complex.exp (((inner ℝ p.1
        (backgroundCofactorT R w p.2) +
      inner ℝ p.1 (backgroundCofactorL R
        (complexPhaseCoordinatesEuclidean (w (exposedYIndex m)))) +
      inner ℝ p.2 (backgroundCofactorL R
        (complexPhaseCoordinatesEuclidean (w (exposedXIndex m)))) : ℝ) : ℂ) *
          Complex.I)
  have hrho : MeasurePreserving rho
      ((circularGaussianVector k).prod (circularGaussianVector k))
      ((stdGaussian (CofactorRealSpace k)).prod
        (stdGaussian (CofactorRealSpace k))) := by
    have hp := (measurePreserving_complexRealificationEuclidean k).prod
      (measurePreserving_complexRealificationEuclidean k)
    refine hp.congr (by fun_prop) ?_
    filter_upwards [] with p
    rfl
  have htransport :
      (∫ p : (Fin k → ℂ) × (Fin k → ℂ), kernel (rho p)
          ∂((circularGaussianVector k).prod (circularGaussianVector k))) =
        ∫ q : CofactorRealSpace k × CofactorRealSpace k, kernel q
          ∂((stdGaussian (CofactorRealSpace k)).prod
            (stdGaussian (CofactorRealSpace k))) := by
    rw [← hrho.map_eq]
    symm
    apply integral_map hrho.measurable.aemeasurable
    exact (by fun_prop : Continuous kernel).aestronglyMeasurable
  unfold conditionalCofactorCharacteristic bilinearGaussianIntegral
  rw [← htransport]
  apply integral_congr_ae
  filter_upwards [] with p
  dsimp [kernel, rho, finiteGramCofactorPhaseCharacter]
  rw [finiteGramCofactorPhase_assemble_eq_bilinear]

/-- Full iid characteristic disintegrated into background columns and the
exact conditional two-column kernel. -/
theorem finiteGramCofactorCharacteristic_eq_integral_conditional
    (m k : ℕ) (w : Fin (m + 2) → ℂ) :
    finiteGramCofactorCharacteristic (Fin (m + 2)) k w =
      ∫ R : Fin m → (Fin k → ℂ), conditionalCofactorCharacteristic R w
        ∂(Measure.pi fun _ : Fin m ↦ circularGaussianVector k) := by
  let split := splitTwoExposedColumnsRXY m k
  let muR := Measure.pi fun _ : Fin m ↦ circularGaussianVector k
  let muX := circularGaussianVector k
  let targetIntegrand :
      (Fin m → (Fin k → ℂ)) × ((Fin k → ℂ) × (Fin k → ℂ)) → ℂ :=
    fun q ↦ finiteGramCofactorPhaseCharacter w (split.symm q)
  have hmeas : Measurable targetIntegrand := by
    exact (measurable_finiteGramCofactorPhaseCharacter w).comp
      split.symm.measurable
  have hint : Integrable targetIntegrand
      (muR.prod (muX.prod muX)) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with q
    unfold targetIntegrand finiteGramCofactorPhaseCharacter
    rw [Complex.norm_exp]
    simp
  unfold finiteGramCofactorCharacteristic
  calc
    (∫ A : Fin (m + 2) → (Fin k → ℂ),
        finiteGramCofactorPhaseCharacter w A
          ∂(Measure.pi fun _ : Fin (m + 2) ↦ circularGaussianVector k)) =
      ∫ q, targetIntegrand q ∂(muR.prod (muX.prod muX)) := by
        have h := (measurePreserving_splitTwoExposedColumnsRXY m k).integral_comp'
          targetIntegrand
        simpa [split, muR, muX, targetIntegrand] using h
    _ = ∫ R, ∫ p, targetIntegrand (R, p) ∂(muX.prod muX) ∂muR := by
      exact integral_prod targetIntegrand hint
    _ = ∫ R, conditionalCofactorCharacteristic R w ∂muR := by
      apply integral_congr_ae
      filter_upwards [] with R
      unfold conditionalCofactorCharacteristic targetIntegrand split
      apply integral_congr_ae
      filter_upwards [] with p
      rw [assembleTwoExposedColumns]

/-- The conditional characteristic is integrable as a function of the
background. -/
theorem integrable_conditionalCofactorCharacteristic
    (m k : ℕ) (w : Fin (m + 2) → ℂ) :
    Integrable (fun R : Fin m → (Fin k → ℂ) ↦
      conditionalCofactorCharacteristic R w)
      (Measure.pi fun _ : Fin m ↦ circularGaussianVector k) := by
  let split := splitTwoExposedColumnsRXY m k
  let muR := Measure.pi fun _ : Fin m ↦ circularGaussianVector k
  let muX := circularGaussianVector k
  let f :
      (Fin m → (Fin k → ℂ)) × ((Fin k → ℂ) × (Fin k → ℂ)) → ℂ :=
    fun q ↦ finiteGramCofactorPhaseCharacter w (split.symm q)
  have hfmeas : Measurable f :=
    (measurable_finiteGramCofactorPhaseCharacter w).comp split.symm.measurable
  have hf : Integrable f (muR.prod (muX.prod muX)) := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with q
    unfold f finiteGramCofactorPhaseCharacter
    rw [Complex.norm_exp]
    simp
  have hsection := hf.integral_prod_left
  simpa [f, split, muR, muX, conditionalCofactorCharacteristic,
    assembleTwoExposedColumns] using hsection

theorem backgroundCofactorT_congr_weights
    {m k : ℕ} (R : Fin m → (Fin k → ℂ))
    {w v : Fin (m + 2) → ℂ}
    (hwv : ∀ i : Fin m, w (remainingIndex m i) = v (remainingIndex m i)) :
    backgroundCofactorT R w = backgroundCofactorT R v := by
  unfold backgroundCofactorT cofactorBackgroundPhaseCLM
  apply congrArg (fun M : Matrix (ComplexRealificationIndex k)
    (ComplexRealificationIndex k) ℝ ↦
      (Matrix.toEuclideanLin M).toContinuousLinearMap)
  funext p q
  unfold cofactorBackgroundPhaseMatrix
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hwv i]

@[simp]
theorem complexPhaseCoordinatesEuclidean_zero :
    complexPhaseCoordinatesEuclidean (0 : ℂ) = 0 := by
  ext i
  fin_cases i <;>
    simp [complexPhaseCoordinatesEuclidean, complexPhaseCoordinates]

/-- If the displayed `Y` Fourier weight vanishes, the full endpoint
characteristic norm is exactly the lintegral of the positive conditional
left endpoint. -/
theorem ofReal_norm_finiteGramCofactorCharacteristic_eq_lintegral_left
    {m k : ℕ} (w : Fin (m + 2) → ℂ)
    (hY : w (exposedYIndex m) = 0) :
    ENNReal.ofReal ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k w‖ =
      ∫⁻ R : Fin m → (Fin k → ℂ),
        ENNReal.ofReal (conditionalCofactorCharacteristic R w).re
        ∂(Measure.pi fun _ : Fin m ↦ circularGaussianVector k) := by
  let muR := Measure.pi fun _ : Fin m ↦ circularGaussianVector k
  have hint := integrable_conditionalCofactorCharacteristic m k w
  have hpos : ∀ R : Fin m → (Fin k → ℂ),
      0 < (conditionalCofactorCharacteristic R w).re := by
    intro R
    rw [conditionalCofactorCharacteristic_eq_bilinearGaussianIntegral, hY]
    have hp := bilinearGaussianIntegral_endpoints_pos
      (n := Module.finrank ℝ (CofactorRealSpace k)) rfl
      (backgroundCofactorT R w) (backgroundCofactorL R)
      (complexPhaseCoordinatesEuclidean (w (exposedXIndex m)))
      (0 : EuclideanSpace ℝ (Fin 2))
    rw [complexPhaseCoordinatesEuclidean_zero]
    exact hp.1
  have him : ∀ R : Fin m → (Fin k → ℂ),
      (conditionalCofactorCharacteristic R w).im = 0 := by
    intro R
    rw [conditionalCofactorCharacteristic_eq_bilinearGaussianIntegral, hY]
    rw [complexPhaseCoordinatesEuclidean_zero]
    exact bilinearGaussianIntegral_left_endpoint_im
        (backgroundCofactorT R w) (backgroundCofactorL R)
          (complexPhaseCoordinatesEuclidean (w (exposedXIndex m)))
  have hchar : finiteGramCofactorCharacteristic (Fin (m + 2)) k w =
      ((∫ R, (conditionalCofactorCharacteristic R w).re ∂muR : ℝ) : ℂ) := by
    rw [finiteGramCofactorCharacteristic_eq_integral_conditional]
    calc
      (∫ R, conditionalCofactorCharacteristic R w ∂muR) =
          ∫ R, (((conditionalCofactorCharacteristic R w).re : ℝ) : ℂ) ∂muR := by
        apply integral_congr_ae
        filter_upwards [] with R
        apply Complex.ext
        · simp
        · simpa using him R
      _ = ((∫ R, (conditionalCofactorCharacteristic R w).re ∂muR : ℝ) : ℂ) :=
        integral_ofReal
  rw [hchar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun R ↦ (hpos R).le)]
  exact ofReal_integral_eq_lintegral_ofReal hint.re
    (Filter.Eventually.of_forall fun R ↦ (hpos R).le)

/-- Symmetric right-endpoint version. -/
theorem ofReal_norm_finiteGramCofactorCharacteristic_eq_lintegral_right
    {m k : ℕ} (w : Fin (m + 2) → ℂ)
    (hX : w (exposedXIndex m) = 0) :
    ENNReal.ofReal ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k w‖ =
      ∫⁻ R : Fin m → (Fin k → ℂ),
        ENNReal.ofReal (conditionalCofactorCharacteristic R w).re
        ∂(Measure.pi fun _ : Fin m ↦ circularGaussianVector k) := by
  let muR := Measure.pi fun _ : Fin m ↦ circularGaussianVector k
  have hint := integrable_conditionalCofactorCharacteristic m k w
  have hpos : ∀ R : Fin m → (Fin k → ℂ),
      0 < (conditionalCofactorCharacteristic R w).re := by
    intro R
    rw [conditionalCofactorCharacteristic_eq_bilinearGaussianIntegral, hX]
    have hp := bilinearGaussianIntegral_endpoints_pos
      (n := Module.finrank ℝ (CofactorRealSpace k)) rfl
      (backgroundCofactorT R w) (backgroundCofactorL R)
      (0 : EuclideanSpace ℝ (Fin 2))
      (complexPhaseCoordinatesEuclidean (w (exposedYIndex m)))
    rw [complexPhaseCoordinatesEuclidean_zero]
    exact hp.2
  have him : ∀ R : Fin m → (Fin k → ℂ),
      (conditionalCofactorCharacteristic R w).im = 0 := by
    intro R
    rw [conditionalCofactorCharacteristic_eq_bilinearGaussianIntegral, hX]
    rw [complexPhaseCoordinatesEuclidean_zero]
    exact bilinearGaussianIntegral_right_endpoint_im
        (backgroundCofactorT R w) (backgroundCofactorL R)
          (complexPhaseCoordinatesEuclidean (w (exposedYIndex m)))
  have hchar : finiteGramCofactorCharacteristic (Fin (m + 2)) k w =
      ((∫ R, (conditionalCofactorCharacteristic R w).re ∂muR : ℝ) : ℂ) := by
    rw [finiteGramCofactorCharacteristic_eq_integral_conditional]
    calc
      (∫ R, conditionalCofactorCharacteristic R w ∂muR) =
          ∫ R, (((conditionalCofactorCharacteristic R w).re : ℝ) : ℂ) ∂muR := by
        apply integral_congr_ae
        filter_upwards [] with R
        apply Complex.ext
        · simp
        · simpa using him R
      _ = ((∫ R, (conditionalCofactorCharacteristic R w).re ∂muR : ℝ) : ℂ) :=
        integral_ofReal
  rw [hchar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun R ↦ (hpos R).le)]
  exact ofReal_integral_eq_lintegral_ofReal hint.re
    (Filter.Eventually.of_forall fun R ↦ (hpos R).le)

/-- Integrated local two-coordinate compression.  The hypotheses expose
exactly the algebraic relationship between an input weight and its two
endpoint weights; all Gaussian integration and Hölder averaging are
discharged here. -/
theorem finiteGramCofactorCharacteristic_two_exposed_max
    {m k : ℕ}
    (w wLeft wRight : Fin (m + 2) → ℂ) (theta : ℝ)
    (htheta : 0 < theta) (htheta_one : theta < 1)
    (hbgLeft : ∀ i : Fin m,
      wLeft (remainingIndex m i) = w (remainingIndex m i))
    (hbgRight : ∀ i : Fin m,
      wRight (remainingIndex m i) = w (remainingIndex m i))
    (hLeftY : wLeft (exposedYIndex m) = 0)
    (hRightX : wRight (exposedXIndex m) = 0)
    (hscaleX : complexPhaseCoordinatesEuclidean (w (exposedXIndex m)) =
      Real.sqrt theta •
        complexPhaseCoordinatesEuclidean (wLeft (exposedXIndex m)))
    (hscaleY : complexPhaseCoordinatesEuclidean (w (exposedYIndex m)) =
      Real.sqrt (1 - theta) •
        complexPhaseCoordinatesEuclidean (wRight (exposedYIndex m))) :
    ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
      max ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖
        ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wRight‖ := by
  let muR := Measure.pi fun _ : Fin m ↦ circularGaussianVector k
  let a := complexPhaseCoordinatesEuclidean (wLeft (exposedXIndex m))
  let b := complexPhaseCoordinatesEuclidean (wRight (exposedYIndex m))
  let fLeft : (Fin m → (Fin k → ℂ)) → ENNReal := fun R ↦
    ENNReal.ofReal
      ((bilinearGaussianIntegral (backgroundCofactorT R w)
        (backgroundCofactorL R) a 0).re)
  let fRight : (Fin m → (Fin k → ℂ)) → ENNReal := fun R ↦
    ENNReal.ofReal
      ((bilinearGaussianIntegral (backgroundCofactorT R w)
        (backgroundCofactorL R) 0 b).re)
  have hleftPoint : ∀ R : Fin m → (Fin k → ℂ),
      conditionalCofactorCharacteristic R wLeft =
        bilinearGaussianIntegral (backgroundCofactorT R w)
          (backgroundCofactorL R) a 0 := by
    intro R
    rw [conditionalCofactorCharacteristic_eq_bilinearGaussianIntegral,
      backgroundCofactorT_congr_weights R hbgLeft, hLeftY,
      complexPhaseCoordinatesEuclidean_zero]
  have hrightPoint : ∀ R : Fin m → (Fin k → ℂ),
      conditionalCofactorCharacteristic R wRight =
        bilinearGaussianIntegral (backgroundCofactorT R w)
          (backgroundCofactorL R) 0 b := by
    intro R
    rw [conditionalCofactorCharacteristic_eq_bilinearGaussianIntegral,
      backgroundCofactorT_congr_weights R hbgRight, hRightX,
      complexPhaseCoordinatesEuclidean_zero]
  have hleftMeas : AEMeasurable fLeft muR := by
    have h := (integrable_conditionalCofactorCharacteristic m k wLeft).1.re.aemeasurable
    have hof := ENNReal.measurable_ofReal.comp_aemeasurable h
    change AEMeasurable
      (fun R => ENNReal.ofReal (conditionalCofactorCharacteristic R wLeft).re)
      (Measure.pi fun _ : Fin m ↦ circularGaussianVector k) at hof
    dsimp only [fLeft]
    change AEMeasurable
      (fun R => ENNReal.ofReal
        (bilinearGaussianIntegral (backgroundCofactorT R w)
          (backgroundCofactorL R) a 0).re)
      (Measure.pi fun _ : Fin m ↦ circularGaussianVector k)
    simpa only [hleftPoint] using hof
  have hrightMeas : AEMeasurable fRight muR := by
    have h := (integrable_conditionalCofactorCharacteristic m k wRight).1.re.aemeasurable
    have hof := ENNReal.measurable_ofReal.comp_aemeasurable h
    change AEMeasurable
      (fun R => ENNReal.ofReal (conditionalCofactorCharacteristic R wRight).re)
      (Measure.pi fun _ : Fin m ↦ circularGaussianVector k) at hof
    dsimp only [fRight]
    change AEMeasurable
      (fun R => ENNReal.ofReal
        (bilinearGaussianIntegral (backgroundCofactorT R w)
          (backgroundCofactorL R) 0 b).re)
      (Measure.pi fun _ : Fin m ↦ circularGaussianVector k)
    simpa only [hrightPoint] using hof
  have hholder := lintegral_norm_bilinearGaussianIntegral_sqrt_le
    (n := Module.finrank ℝ (CofactorRealSpace k)) rfl muR
    (fun R ↦ backgroundCofactorT R w)
    (fun R ↦ backgroundCofactorL R) a b
    htheta.le htheta_one.le hleftMeas hrightMeas
  have hnorm : ENNReal.ofReal
      ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
      ∫⁻ R, ENNReal.ofReal ‖conditionalCofactorCharacteristic R w‖ ∂muR := by
    rw [finiteGramCofactorCharacteristic_eq_integral_conditional]
    have hreal := norm_integral_le_integral_norm
      (fun R ↦ conditionalCofactorCharacteristic R w) (μ := muR)
    have hof := ENNReal.ofReal_le_ofReal hreal
    rw [ofReal_integral_norm_eq_lintegral_enorm
      (integrable_conditionalCofactorCharacteristic m k w)] at hof
    simpa [muR, ofReal_norm] using hof
  have hscaled :
      (∫⁻ R, ENNReal.ofReal ‖conditionalCofactorCharacteristic R w‖ ∂muR) ≤
        (∫⁻ R, fLeft R ∂muR) ^ theta *
          (∫⁻ R, fRight R ∂muR) ^ (1 - theta) := by
    calc
      (∫⁻ R, ENNReal.ofReal ‖conditionalCofactorCharacteristic R w‖ ∂muR) =
          ∫⁻ R, ENNReal.ofReal
            ‖bilinearGaussianIntegral (backgroundCofactorT R w)
              (backgroundCofactorL R)
              (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)‖ ∂muR := by
        apply lintegral_congr
        intro R
        rw [conditionalCofactorCharacteristic_eq_bilinearGaussianIntegral,
          hscaleX, hscaleY]
      _ ≤ (∫⁻ R, fLeft R ∂muR) ^ theta *
          (∫⁻ R, fRight R ∂muR) ^ (1 - theta) := by
        simpa [fLeft, fRight] using hholder
  let Lval : ENNReal := ∫⁻ R, fLeft R ∂muR
  let Rval : ENNReal := ∫⁻ R, fRight R ∂muR
  have hgeom : Lval ^ theta * Rval ^ (1 - theta) ≤ max Lval Rval := by
    let M := max Lval Rval
    have hLM : Lval ≤ M := le_max_left _ _
    have hRM : Rval ≤ M := le_max_right _ _
    have hpowers : Lval ^ theta * Rval ^ (1 - theta) ≤
        M ^ theta * M ^ (1 - theta) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hLM htheta.le)
        (ENNReal.rpow_le_rpow hRM (sub_nonneg.mpr htheta_one.le))
    by_cases hM0 : M = 0
    · have hL0 : Lval = 0 := le_antisymm (hLM.trans_eq hM0) bot_le
      have hR0 : Rval = 0 := le_antisymm (hRM.trans_eq hM0) bot_le
      simp [hL0, hR0, htheta.ne', sub_pos.mpr htheta_one]
    · by_cases hMtop : M = ∞
      · change max Lval Rval = ∞ at hMtop
        rw [hMtop]
        exact le_top
      · calc
          Lval ^ theta * Rval ^ (1 - theta) ≤
              M ^ theta * M ^ (1 - theta) := hpowers
          _ = M ^ (theta + (1 - theta)) :=
            (ENNReal.rpow_add _ _ hM0 hMtop).symm
          _ = M := by ring_nf; simp
  have hLval : Lval = ENNReal.ofReal
      ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖ := by
    dsimp [Lval, fLeft]
    calc
      (∫⁻ R, ENNReal.ofReal
          (bilinearGaussianIntegral (backgroundCofactorT R w)
            (backgroundCofactorL R) a 0).re ∂muR) =
          ∫⁻ R, ENNReal.ofReal
            (conditionalCofactorCharacteristic R wLeft).re ∂muR := by
        apply lintegral_congr
        intro R
        rw [hleftPoint]
      _ = ENNReal.ofReal
          ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖ := by
        simpa [muR] using
          (ofReal_norm_finiteGramCofactorCharacteristic_eq_lintegral_left
            (m := m) (k := k) wLeft hLeftY).symm
  have hRval : Rval = ENNReal.ofReal
      ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wRight‖ := by
    dsimp [Rval, fRight]
    calc
      (∫⁻ R, ENNReal.ofReal
          (bilinearGaussianIntegral (backgroundCofactorT R w)
            (backgroundCofactorL R) 0 b).re ∂muR) =
          ∫⁻ R, ENNReal.ofReal
            (conditionalCofactorCharacteristic R wRight).re ∂muR := by
        apply lintegral_congr
        intro R
        rw [hrightPoint]
      _ = ENNReal.ofReal
          ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wRight‖ := by
        simpa [muR] using
          (ofReal_norm_finiteGramCofactorCharacteristic_eq_lintegral_right
            (m := m) (k := k) wRight hRightX).symm
  have hENN : ENNReal.ofReal
      ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
      ENNReal.ofReal (max
        ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖
        ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wRight‖) := by
    rw [ENNReal.ofReal_max]
    calc
      ENNReal.ofReal
          ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
          ∫⁻ R, ENNReal.ofReal ‖conditionalCofactorCharacteristic R w‖ ∂muR := hnorm
      _ ≤ Lval ^ theta * Rval ^ (1 - theta) := by
        simpa [Lval, Rval] using hscaled
      _ ≤ max Lval Rval := hgeom
      _ = max (ENNReal.ofReal
          ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖)
          (ENNReal.ofReal
            ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wRight‖) := by
        rw [hLval, hRval]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN

/-! ## Explicit last-two endpoint weights -/

/-- Endpoint obtained by concentrating the displayed `X,Y` energy at `X`. -/
def leftExposedEndpoint {m : ℕ} (w : Fin (m + 2) → ℂ) (theta : ℝ) :
    Fin (m + 2) → ℂ :=
  fun i ↦ if i = exposedXIndex m then
      (Real.sqrt theta)⁻¹ • w i
    else if i = exposedYIndex m then 0 else w i

/-- Endpoint obtained by concentrating the displayed `X,Y` energy at `Y`. -/
def rightExposedEndpoint {m : ℕ} (w : Fin (m + 2) → ℂ) (theta : ℝ) :
    Fin (m + 2) → ℂ :=
  fun i ↦ if i = exposedXIndex m then 0
    else if i = exposedYIndex m then
      (Real.sqrt (1 - theta))⁻¹ • w i
    else w i

@[simp]
theorem leftExposedEndpoint_background {m : ℕ}
    (w : Fin (m + 2) → ℂ) (theta : ℝ) (i : Fin m) :
    leftExposedEndpoint w theta (remainingIndex m i) =
      w (remainingIndex m i) := by
  simp [leftExposedEndpoint, ne_exposedXIndex_of_remaining,
    ne_exposedYIndex_of_remaining]

@[simp]
theorem rightExposedEndpoint_background {m : ℕ}
    (w : Fin (m + 2) → ℂ) (theta : ℝ) (i : Fin m) :
    rightExposedEndpoint w theta (remainingIndex m i) =
      w (remainingIndex m i) := by
  simp [rightExposedEndpoint, ne_exposedXIndex_of_remaining,
    ne_exposedYIndex_of_remaining]

@[simp]
theorem leftExposedEndpoint_X {m : ℕ}
    (w : Fin (m + 2) → ℂ) (theta : ℝ) :
    leftExposedEndpoint w theta (exposedXIndex m) =
      (Real.sqrt theta)⁻¹ • w (exposedXIndex m) := by
  simp [leftExposedEndpoint]

@[simp]
theorem leftExposedEndpoint_Y {m : ℕ}
    (w : Fin (m + 2) → ℂ) (theta : ℝ) :
    leftExposedEndpoint w theta (exposedYIndex m) = 0 := by
  simp [leftExposedEndpoint, Ne.symm (exposedXIndex_ne_exposedYIndex m)]

@[simp]
theorem rightExposedEndpoint_X {m : ℕ}
    (w : Fin (m + 2) → ℂ) (theta : ℝ) :
    rightExposedEndpoint w theta (exposedXIndex m) = 0 := by
  simp [rightExposedEndpoint]

@[simp]
theorem rightExposedEndpoint_Y {m : ℕ}
    (w : Fin (m + 2) → ℂ) (theta : ℝ) :
    rightExposedEndpoint w theta (exposedYIndex m) =
      (Real.sqrt (1 - theta))⁻¹ • w (exposedYIndex m) := by
  simp [rightExposedEndpoint, Ne.symm (exposedXIndex_ne_exposedYIndex m)]

theorem complexPhaseCoordinatesEuclidean_real_smul
    (s : ℝ) (z : ℂ) :
    complexPhaseCoordinatesEuclidean (s • z) =
      s • complexPhaseCoordinatesEuclidean z := by
  ext i
  fin_cases i <;>
    simp [complexPhaseCoordinatesEuclidean, complexPhaseCoordinates,
      Complex.real_smul]

theorem complexPhaseCoordinatesEuclidean_endpoint_scale
    {theta : ℝ} (htheta : 0 < theta) (z : ℂ) :
    complexPhaseCoordinatesEuclidean z =
      Real.sqrt theta •
        complexPhaseCoordinatesEuclidean ((Real.sqrt theta)⁻¹ • z) := by
  rw [complexPhaseCoordinatesEuclidean_real_smul, smul_smul]
  rw [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr htheta), one_smul]

theorem normSq_inv_sqrt_real_smul
    {theta : ℝ} (htheta : 0 < theta) (z : ℂ) :
    Complex.normSq ((Real.sqrt theta)⁻¹ • z) =
      Complex.normSq z / theta := by
  rw [Complex.real_smul]
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  have hsqrt : Real.sqrt theta ≠ 0 := Real.sqrt_ne_zero'.mpr htheta
  have hsquare : Real.sqrt theta * Real.sqrt theta = theta := by
    nlinarith [Real.sq_sqrt htheta.le]
  field_simp [hsqrt]
  rw [pow_two, hsquare]
  ring

/-- Fraction of the displayed two-coordinate energy carried by `X`. -/
def exposedTheta {m : ℕ} (w : Fin (m + 2) → ℂ) : ℝ :=
  Complex.normSq (w (exposedXIndex m)) /
    (Complex.normSq (w (exposedXIndex m)) +
      Complex.normSq (w (exposedYIndex m)))

theorem exposedTheta_pos {m : ℕ} {w : Fin (m + 2) → ℂ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    0 < exposedTheta w := by
  unfold exposedTheta
  exact div_pos (Complex.normSq_pos.mpr hX)
    (add_pos (Complex.normSq_pos.mpr hX) (Complex.normSq_pos.mpr hY))

theorem exposedTheta_lt_one {m : ℕ} {w : Fin (m + 2) → ℂ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    exposedTheta w < 1 := by
  unfold exposedTheta
  apply (div_lt_one
    (add_pos (Complex.normSq_pos.mpr hX) (Complex.normSq_pos.mpr hY))).mpr
  linarith [Complex.normSq_pos.mpr hY]

theorem coordinateEnergy_leftExposedEndpoint
    {m : ℕ} {w : Fin (m + 2) → ℂ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    coordinateEnergy (leftExposedEndpoint w (exposedTheta w)) =
      coordinateEnergy w := by
  have ht := exposedTheta_pos hX hY
  have hden : Complex.normSq (w (exposedXIndex m)) +
      Complex.normSq (w (exposedYIndex m)) ≠ 0 := by
    exact ne_of_gt (add_pos (Complex.normSq_pos.mpr hX)
      (Complex.normSq_pos.mpr hY))
  have hxden : Complex.normSq (w (exposedXIndex m)) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hX)
  have hratio : Complex.normSq (w (exposedXIndex m)) / exposedTheta w =
      Complex.normSq (w (exposedXIndex m)) +
        Complex.normSq (w (exposedYIndex m)) := by
    unfold exposedTheta
    field_simp [hden, hxden]
  unfold coordinateEnergy
  rw [sum_fin_two_exposed
    (f := fun i ↦ Complex.normSq (leftExposedEndpoint w (exposedTheta w) i))]
  rw [sum_fin_two_exposed (f := fun i ↦ Complex.normSq (w i))]
  simp_rw [leftExposedEndpoint_background]
  rw [leftExposedEndpoint_X, leftExposedEndpoint_Y,
    normSq_inv_sqrt_real_smul ht]
  simp only [Complex.normSq_zero, add_zero]
  rw [hratio]
  ring

theorem coordinateEnergy_rightExposedEndpoint
    {m : ℕ} {w : Fin (m + 2) → ℂ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    coordinateEnergy (rightExposedEndpoint w (exposedTheta w)) =
      coordinateEnergy w := by
  have ht1 : 0 < 1 - exposedTheta w := sub_pos.mpr
    (exposedTheta_lt_one hX hY)
  have hden : Complex.normSq (w (exposedXIndex m)) +
      Complex.normSq (w (exposedYIndex m)) ≠ 0 := by
    exact ne_of_gt (add_pos (Complex.normSq_pos.mpr hX)
      (Complex.normSq_pos.mpr hY))
  have hyden : Complex.normSq (w (exposedYIndex m)) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hY)
  have hratio : Complex.normSq (w (exposedYIndex m)) /
      (1 - exposedTheta w) =
      Complex.normSq (w (exposedXIndex m)) +
        Complex.normSq (w (exposedYIndex m)) := by
    unfold exposedTheta
    field_simp [hden, hyden]
    ring
  unfold coordinateEnergy
  rw [sum_fin_two_exposed
    (f := fun i ↦ Complex.normSq (rightExposedEndpoint w (exposedTheta w) i))]
  rw [sum_fin_two_exposed (f := fun i ↦ Complex.normSq (w i))]
  simp_rw [rightExposedEndpoint_background]
  rw [rightExposedEndpoint_X, rightExposedEndpoint_Y,
    normSq_inv_sqrt_real_smul ht1]
  simp only [Complex.normSq_zero, zero_add]
  rw [hratio]
  ring

theorem coordinateSupportCard_leftExposedEndpoint_lt
    {m : ℕ} {w : Fin (m + 2) → ℂ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    coordinateSupportCard (leftExposedEndpoint w (exposedTheta w)) <
      coordinateSupportCard w := by
  have ht := exposedTheta_pos hX hY
  have hsubset : coordinateSupport (leftExposedEndpoint w (exposedTheta w)) ⊆
      coordinateSupport w := by
    intro i hi
    simp only [coordinateSupport, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi ⊢
    by_cases hiX : i = exposedXIndex m
    · simpa [hiX] using hX
    · by_cases hiY : i = exposedYIndex m
      · subst i
        simp at hi
      · simpa [leftExposedEndpoint, hiX, hiY] using hi
  have hYmem : exposedYIndex m ∈ coordinateSupport w := by
    simp [coordinateSupport, hY]
  have hYnot : exposedYIndex m ∉
      coordinateSupport (leftExposedEndpoint w (exposedTheta w)) := by
    simp [coordinateSupport]
  unfold coordinateSupportCard
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsubset, ?_⟩
  intro heq
  apply hYnot
  rw [heq]
  exact hYmem

theorem coordinateSupportCard_rightExposedEndpoint_lt
    {m : ℕ} {w : Fin (m + 2) → ℂ}
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    coordinateSupportCard (rightExposedEndpoint w (exposedTheta w)) <
      coordinateSupportCard w := by
  have ht1 : 0 < 1 - exposedTheta w := sub_pos.mpr
    (exposedTheta_lt_one hX hY)
  have hsubset : coordinateSupport (rightExposedEndpoint w (exposedTheta w)) ⊆
      coordinateSupport w := by
    intro i hi
    simp only [coordinateSupport, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi ⊢
    by_cases hiX : i = exposedXIndex m
    · subst i
      simp at hi
    · by_cases hiY : i = exposedYIndex m
      · simpa [hiY] using hY
      · simpa [rightExposedEndpoint, hiX, hiY] using hi
  have hXmem : exposedXIndex m ∈ coordinateSupport w := by
    simp [coordinateSupport, hX]
  have hXnot : exposedXIndex m ∉
      coordinateSupport (rightExposedEndpoint w (exposedTheta w)) := by
    simp [coordinateSupport]
  unfold coordinateSupportCard
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsubset, ?_⟩
  intro heq
  apply hXnot
  rw [heq]
  exact hXmem

/-- Direct distinguished-pair local compression interface consumed by
`CoordinateExposure.global_two_endpoints_of_penultimate_final`. -/
theorem finiteGramCofactorCharacteristic_penultimate_final_two_endpoints
    (m k : ℕ) (w : Fin (m + 2) → ℂ)
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    ∃ wLeft wRight : Fin (m + 2) → ℂ,
      coordinateSupportCard wLeft < coordinateSupportCard w ∧
      coordinateSupportCard wRight < coordinateSupportCard w ∧
      coordinateEnergy wLeft = coordinateEnergy w ∧
      coordinateEnergy wRight = coordinateEnergy w ∧
      ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k w‖ ≤
        max ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wLeft‖
          ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k wRight‖ := by
  let theta := exposedTheta w
  let wLeft := leftExposedEndpoint w theta
  let wRight := rightExposedEndpoint w theta
  have ht : 0 < theta := exposedTheta_pos hX hY
  have ht1 : theta < 1 := exposedTheta_lt_one hX hY
  refine ⟨wLeft, wRight,
    coordinateSupportCard_leftExposedEndpoint_lt hX hY,
    coordinateSupportCard_rightExposedEndpoint_lt hX hY,
    coordinateEnergy_leftExposedEndpoint hX hY,
    coordinateEnergy_rightExposedEndpoint hX hY, ?_⟩
  apply finiteGramCofactorCharacteristic_two_exposed_max
    w wLeft wRight theta ht ht1
  · intro i
    exact leftExposedEndpoint_background w theta i
  · intro i
    exact rightExposedEndpoint_background w theta i
  · exact leftExposedEndpoint_Y w theta
  · exact rightExposedEndpoint_X w theta
  · dsimp [wLeft]
    rw [leftExposedEndpoint_X]
    exact complexPhaseCoordinatesEuclidean_endpoint_scale ht _
  · dsimp [wRight]
    rw [rightExposedEndpoint_Y]
    exact complexPhaseCoordinatesEuclidean_endpoint_scale
      (sub_pos.mpr ht1) _

/-- The literal analytic input required by finite coordinate iteration, now
valid for an arbitrary Fourier vector: a permutation first exposes two
nonzero entries, and the completed-square/Hölder theorem compresses them. -/
theorem finiteGramCofactorCharacteristic_global_two_endpoints
    (m k : ℕ) :
    ∀ z : Fin (m + 2) → ℂ, 1 < coordinateSupportCard z →
      ∃ zLeft zRight : Fin (m + 2) → ℂ,
        coordinateSupportCard zLeft < coordinateSupportCard z ∧
        coordinateSupportCard zRight < coordinateSupportCard z ∧
        coordinateEnergy zLeft = coordinateEnergy z ∧
        coordinateEnergy zRight = coordinateEnergy z ∧
        ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k z‖ ≤
          max ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k zLeft‖
            ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k zRight‖ := by
  apply global_two_endpoints_of_penultimate_final
    (finiteGramCofactorCharacteristic (Fin (m + 2)) k)
  · intro σ z
    change finiteGramCofactorCharacteristic (Fin (m + 2)) k
      (fun i ↦ z (σ.symm i)) =
        finiteGramCofactorCharacteristic (Fin (m + 2)) k z
    exact finiteGramCofactorCharacteristic_reindex_perm
      (k := k) σ.symm z
  · intro w hPen hFinal
    apply finiteGramCofactorCharacteristic_penultimate_final_two_endpoints
      m k w
    · have hi : penultimateCoordinate m = exposedXIndex m := by
        apply Fin.ext
        rfl
      rwa [hi] at hPen
    · have hi : finalCoordinate m = exposedYIndex m := by
        apply Fin.ext
        rfl
      rwa [hi] at hFinal

/-- Full radial Fourier compression for the finite Gram-cofactor law.  The
parity hypothesis is exactly the odd-cofactor situation: `m+2` coordinates
with `m+1` even. -/
theorem finiteGramCofactorCharacteristic_radial_compression
    (m k : ℕ) (base : Fin (m + 2))
    (hEven : ∃ r : ℕ, m + 1 = 2 * r) :
    ∀ z : Fin (m + 2) → ℂ,
      ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k z‖ ≤
        ‖finiteGramCofactorCharacteristic (Fin (m + 2)) k
          (singleCoordinate base
            (Real.sqrt (coordinateEnergy z) : ℝ))‖ := by
  have hsym := finiteGramCofactorCharacteristic_compression_symmetries
    (k := k) (d := m + 1) (show Fintype.card (Fin (m + 2)) = m + 1 + 1 by
      simp) (by omega) hEven
  exact finite_coordinate_compression_of_two_endpoints
    (finiteGramCofactorCharacteristic (Fin (m + 2)) k) base
      hsym.1 hsym.2
      (finiteGramCofactorCharacteristic_global_two_endpoints m k)

end

end LogdetLean.GramHafnian
