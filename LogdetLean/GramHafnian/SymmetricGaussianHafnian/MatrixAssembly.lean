import LogdetLean.GramHafnian.SymmetricGaussianHafnian.CofactorAlgebra
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseBackground
/-!
# Independent-edge block assembly

The two exposed edge vectors and their joining edge are assembled directly
into a symmetric matrix.  These are deterministic identities for literal
matrix hafnians; no distributional assumption enters this file.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Append one symmetric zero-diagonal vertex to a matrix. -/
def appendMatrix {n : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin n) (Fin n) R) (g : Fin n → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j ↦ Fin.lastCases (Fin.lastCases 0 g j)
    (fun a ↦ Fin.lastCases (g a) (fun b ↦ A a b) j) i

@[simp] theorem appendMatrix_background {n : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin n) (Fin n) R) (g : Fin n → R) (i j : Fin n) :
    appendMatrix A g i.castSucc j.castSucc = A i j := by
  simp [appendMatrix]

@[simp] theorem appendMatrix_background_last {n : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin n) (Fin n) R) (g : Fin n → R) (i : Fin n) :
    appendMatrix A g i.castSucc (Fin.last n) = g i := by
  simp [appendMatrix]

@[simp] theorem appendMatrix_last_background {n : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin n) (Fin n) R) (g : Fin n → R) (i : Fin n) :
    appendMatrix A g (Fin.last n) i.castSucc = g i := by
  simp [appendMatrix]

@[simp] theorem appendMatrix_last_last {n : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin n) (Fin n) R) (g : Fin n → R) :
    appendMatrix A g (Fin.last n) (Fin.last n) = 0 := by
  simp [appendMatrix]

theorem appendMatrix_symmetric {n : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin n) (Fin n) R) (g : Fin n → R)
    (hA : ∀ i j, A i j = A j i) :
    ∀ i j, appendMatrix A g i j = appendMatrix A g j i := by
  intro i j
  refine Fin.lastCases ?_ (fun a ↦ ?_) i
  · refine Fin.lastCases ?_ (fun b ↦ ?_) j <;> simp
  · refine Fin.lastCases ?_ (fun b ↦ ?_) j
    · simp
    · simpa using hA a b

/-- Assemble the two exposed edge vectors and their independent joining edge. -/
def twoExposedMatrix {m : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  appendMatrix (appendMatrix A X) (Fin.lastCases u Y)

@[simp] theorem twoExposedMatrix_background
    {m : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R)
    (i j : Fin m) :
    twoExposedMatrix A u X Y (remainingIndex m i) (remainingIndex m j) = A i j := by
  change appendMatrix (appendMatrix A X) (Fin.lastCases u Y)
    i.castSucc.castSucc j.castSucc.castSucc = _
  simp

@[simp] theorem matrixX_twoExposedMatrix
    {m : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R) :
    matrixX (twoExposedMatrix A u X Y) = X := by
  funext a
  change appendMatrix (appendMatrix A X) (Fin.lastCases u Y)
    a.castSucc.castSucc (Fin.last m).castSucc = _
  simp

@[simp] theorem matrixY_twoExposedMatrix
    {m : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R) :
    matrixY (twoExposedMatrix A u X Y) = Y := by
  funext a
  change appendMatrix (appendMatrix A X) (Fin.lastCases u Y)
    a.castSucc.castSucc (Fin.last (m + 1)) = _
  simp

@[simp] theorem matrixU_twoExposedMatrix
    {m : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R) :
    matrixU (twoExposedMatrix A u X Y) = u := by
  change appendMatrix (appendMatrix A X) (Fin.lastCases u Y)
    (Fin.last m).castSucc (Fin.last (m + 1)) = _
  simp

@[simp] theorem backgroundQ_twoExposedMatrix
    {m : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R) :
    backgroundQ (twoExposedMatrix A u X Y) = matrixCofactor A := by
  funext j
  unfold backgroundQ matrixCofactor
  congr 1
  funext a b
  exact twoExposedMatrix_background A u X Y a.1 b.1

@[simp] theorem backgroundHafnianDeleteThree_twoExposedMatrix
    {m : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R)
    (j a b : Fin m) :
    backgroundHafnianDeleteThree (twoExposedMatrix A u X Y) j a b =
      typeHafnian (fun s t : {s : Fin m // s ≠ j ∧ s ≠ a ∧ s ≠ b} ↦ A s.1 t.1) := by
  unfold backgroundHafnianDeleteThree
  congr 1
  funext s t
  exact twoExposedMatrix_background A u X Y s.1 t.1

/-- The fixed-background matrix used by the conditional bilinear kernel. -/
def fixedBackgroundM {m : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin m) (Fin m) R) (j : Fin m) : Matrix (Fin m) (Fin m) R :=
  fun a b ↦ if b ≠ j ∧ a ≠ j ∧ a ≠ b then
    typeHafnian (fun s t : {s : Fin m // s ≠ j ∧ s ≠ a ∧ s ≠ b} ↦ A s.1 t.1)
  else 0

@[simp] theorem backgroundM_twoExposedMatrix
    {m : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R) :
    backgroundM (twoExposedMatrix A u X Y) = fixedBackgroundM A := by
  funext j a b
  simp [backgroundM, fixedBackgroundM]

theorem twoExposedMatrix_symmetric
    {m : ℕ} {R : Type*} [Zero R]
    (A : Matrix (Fin m) (Fin m) R) (u : R) (X Y : Fin m → R)
    (hA : ∀ i j, A i j = A j i) :
    ∀ i j, twoExposedMatrix A u X Y i j = twoExposedMatrix A u X Y j i :=
  appendMatrix_symmetric _ _ (appendMatrix_symmetric A X hA)

@[fun_prop] theorem continuous_matrixCofactor
    {ι : Type*} [Fintype ι] [LinearOrder ι] :
    Continuous (fun (A : ι → ι → ℂ) (j : ι) ↦ matrixCofactor A j) := by
  apply continuous_pi
  intro j
  unfold matrixCofactor
  apply continuous_typeHafnian.comp
  fun_prop

@[fun_prop] theorem measurable_matrixCofactor
    {ι : Type*} [Fintype ι] [LinearOrder ι] :
    Measurable (fun (A : ι → ι → ℂ) (j : ι) ↦ matrixCofactor A j) :=
  continuous_matrixCofactor.measurable

@[fun_prop] theorem continuous_fixedBackgroundM {m : ℕ} :
    Continuous (fun (A : Fin m → Fin m → ℂ) (j a b : Fin m) ↦
      fixedBackgroundM A j a b) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases h : b ≠ j ∧ a ≠ j ∧ a ≠ b
  · simp only [fixedBackgroundM, if_pos h]
    apply continuous_typeHafnian.comp
    fun_prop
  · simp only [fixedBackgroundM, if_neg h]
    exact continuous_const

@[fun_prop] theorem measurable_fixedBackgroundM {m : ℕ} :
    Measurable (fun (A : Fin m → Fin m → ℂ) (j a b : Fin m) ↦
      fixedBackgroundM A j a b) :=
  continuous_fixedBackgroundM.measurable

/-- Exact complex phase decomposition for a genuinely assembled symmetric
matrix.  The edge `u` has its own linear term, separate from the bilinear
kernel in the two independent edge vectors. -/
theorem weightedCofactorSum_twoExposedMatrix
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (u : ℂ)
    (X Y : Fin m → ℂ) (w : Fin (m + 2) → ℂ) :
    (∑ i : Fin (m + 2), w i * matrixCofactor (twoExposedMatrix A u X Y) i) =
      u * (∑ j : Fin m, w (remainingIndex m j) * matrixCofactor A j) +
        transposeBilinear X
          (fun a b ↦ ∑ j : Fin m, w (remainingIndex m j) * fixedBackgroundM A j a b) Y +
        w (exposedXIndex m) * transposeDot Y (matrixCofactor A) +
        w (exposedYIndex m) * transposeDot X (matrixCofactor A) := by
  have hscalar :
      (∑ j : Fin m, w (remainingIndex m j) * (u * matrixCofactor A j)) =
        u * ∑ j : Fin m, w (remainingIndex m j) * matrixCofactor A j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hscale (j : Fin m) :
      w (remainingIndex m j) * transposeBilinear X (fixedBackgroundM A j) Y =
        transposeBilinear X
          (fun a b ↦ w (remainingIndex m j) * fixedBackgroundM A j a b) Y := by
    unfold transposeBilinear
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  have hbilinear :
      (∑ j : Fin m, w (remainingIndex m j) *
        transposeBilinear X (fixedBackgroundM A j) Y) =
        transposeBilinear X
          (fun a b ↦ ∑ j : Fin m, w (remainingIndex m j) * fixedBackgroundM A j a b) Y := by
    simp_rw [hscale]
    exact (transposeBilinear_fintype_sum _ _ _).symm
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  change
    ((∑ j : Fin m, w (remainingIndex m j) *
      matrixCofactor (twoExposedMatrix A u X Y) (remainingIndex m j)) +
      w (exposedXIndex m) * matrixCofactor (twoExposedMatrix A u X Y) (exposedXIndex m)) +
      w (exposedYIndex m) * matrixCofactor (twoExposedMatrix A u X Y) (exposedYIndex m) = _
  rw [matrixCofactor_X_eq_sum_Y_Q, matrixCofactor_Y_eq_sum_X_Q]
  simp_rw [matrixCofactor_background_eq_UQ_add_transposeBilinear]
  simp only [matrixX_twoExposedMatrix, matrixY_twoExposedMatrix,
    matrixU_twoExposedMatrix, backgroundQ_twoExposedMatrix, backgroundM_twoExposedMatrix]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hscalar, hbilinear]
  rfl

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
