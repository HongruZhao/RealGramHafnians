import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.ScoreTransformPairing
/-!
# A fixed real basis decomposition of Hermitian rank-one directions

The conditional score theorem is applied with fixed Hermitian directions,
whereas the desired rank-one direction `c cᴴ` depends on the preserved
transpose Gram.  The finite expansion below separates those two roles.
-/

open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

variable {m : Type*} [Fintype m] [DecidableEq m]

set_option maxRecDepth 10000

/-- Real Hermitian coordinate direction supported at `(i,j)` and `(j,i)`. -/
def hermitianRealCoordinateDirection (i j : m) : Matrix m m ℂ :=
  Matrix.single i j 1 + Matrix.single j i 1

/-- Imaginary Hermitian coordinate direction supported at `(i,j)` and
`(j,i)`. -/
def hermitianImagCoordinateDirection (i j : m) : Matrix m m ℂ :=
  Complex.I • Matrix.single i j 1 -
    Complex.I • Matrix.single j i 1

theorem hermitianRealCoordinateDirection_isHermitian (i j : m) :
    (hermitianRealCoordinateDirection i j).IsHermitian := by
  unfold Matrix.IsHermitian hermitianRealCoordinateDirection
  simp [add_comm]

theorem hermitianImagCoordinateDirection_isHermitian (i j : m) :
    (hermitianImagCoordinateDirection i j).IsHermitian := by
  unfold Matrix.IsHermitian hermitianImagCoordinateDirection
  simp
  rw [← Matrix.single_neg, ← Matrix.single_neg]
  abel

theorem sum_realCoordinateDirections_apply (c : m → ℂ) (a b : m) :
    (∑ i, ∑ j,
        ((c i * star (c j)).re / 2 : ℝ) •
          hermitianRealCoordinateDirection i j) a b =
      (((c a * star (c b)).re / 2 : ℝ) : ℂ) +
        (((c b * star (c a)).re / 2 : ℝ) : ℂ) := by
  classical
  let f : m → m → ℝ := fun i j ↦ (c i * star (c j)).re / 2
  have hfirst :
      (∑ i, ∑ j, Matrix.single i j ((f i j : ℝ) : ℂ)) =
        (fun i j ↦ ((f i j : ℝ) : ℂ)) :=
    Matrix.sum_sum_single _
  have hsecond :
      (∑ i, ∑ j, Matrix.single j i ((f i j : ℝ) : ℂ)) =
        (fun i j ↦ ((f j i : ℝ) : ℂ)) := by
    rw [Finset.sum_comm]
    exact Matrix.sum_sum_single _
  have hone (i j : m) :
      f i j • hermitianRealCoordinateDirection i j =
        Matrix.single i j ((f i j : ℝ) : ℂ) +
          Matrix.single j i ((f i j : ℝ) : ℂ) := by
    ext x y
    simp only [hermitianRealCoordinateDirection, Matrix.smul_apply,
      Matrix.add_apply, Matrix.single_apply]
    simp only [Algebra.smul_def]
    split_ifs <;> norm_num [Complex.coe_algebraMap] <;> ring
  have hmatrix :
      (∑ i, ∑ j,
        f i j • hermitianRealCoordinateDirection i j) =
      (fun i j ↦ ((f i j : ℝ) : ℂ)) +
        (fun i j ↦ ((f j i : ℝ) : ℂ)) := by
    simp_rw [hone]
    rw [show (∑ i, ∑ j,
      (Matrix.single i j ((f i j : ℝ) : ℂ) +
        Matrix.single j i ((f i j : ℝ) : ℂ))) =
      (∑ i, ∑ j, Matrix.single i j ((f i j : ℝ) : ℂ)) +
        (∑ i, ∑ j, Matrix.single j i ((f i j : ℝ) : ℂ)) by
      simp_rw [Finset.sum_add_distrib]]
    rw [hfirst, hsecond]
    rfl
  rw [hmatrix]
  rfl

theorem sum_imagCoordinateDirections_apply (c : m → ℂ) (a b : m) :
    (∑ i, ∑ j,
        ((c i * star (c j)).im / 2 : ℝ) •
          hermitianImagCoordinateDirection i j) a b =
      (((c a * star (c b)).im / 2 : ℝ) : ℂ) * Complex.I -
        (((c b * star (c a)).im / 2 : ℝ) : ℂ) * Complex.I := by
  classical
  let f : m → m → ℝ := fun i j ↦ (c i * star (c j)).im / 2
  let z : m → m → ℂ := fun i j ↦ ((f i j : ℝ) : ℂ) * Complex.I
  have hfirst :
      (∑ i, ∑ j, Matrix.single i j (z i j)) = z :=
    Matrix.sum_sum_single _
  have hsecond :
      (∑ i, ∑ j, Matrix.single j i (z i j)) =
        (fun i j ↦ z j i) := by
    rw [Finset.sum_comm]
    exact Matrix.sum_sum_single _
  have hone (i j : m) :
      f i j • hermitianImagCoordinateDirection i j =
        Matrix.single i j (z i j) - Matrix.single j i (z i j) := by
    ext x y
    simp only [hermitianImagCoordinateDirection, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.single_apply]
    simp only [z, Algebra.smul_def]
    split_ifs <;> norm_num [Complex.coe_algebraMap] <;> ring
  have hmatrix :
      (∑ i, ∑ j,
        f i j • hermitianImagCoordinateDirection i j) =
      z - (fun i j ↦ z j i) := by
    simp_rw [hone]
    rw [show (∑ i, ∑ j,
      (Matrix.single i j (z i j) - Matrix.single j i (z i j))) =
      (∑ i, ∑ j, Matrix.single i j (z i j)) -
        (∑ i, ∑ j, Matrix.single j i (z i j)) by
      simp_rw [Finset.sum_sub_distrib]]
    rw [hfirst, hsecond]
    rfl
  rw [hmatrix]
  rfl

/-- Every Hermitian rank-one matrix is a finite real-linear combination of
the fixed real and imaginary coordinate directions.  Summing over ordered
pairs avoids choosing an ordering and supplies the factor `1/2`. -/
theorem hermitianRankOne_eq_sum_coordinateDirections (c : m → ℂ) :
    hermitianRankOne c =
      (∑ i, ∑ j,
        ((c i * star (c j)).re / 2 : ℝ) •
            hermitianRealCoordinateDirection i j) +
      (∑ i, ∑ j,
        ((c i * star (c j)).im / 2 : ℝ) •
            hermitianImagCoordinateDirection i j) := by
  ext a b
  classical
  rw [Matrix.add_apply, sum_realCoordinateDirections_apply,
    sum_imagCoordinateDirections_apply]
  unfold hermitianRankOne
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The real score-direction construction is additive. -/
theorem scoreDeltaM_add (H J : Matrix m m ℂ) :
    scoreDeltaM (H + J) = scoreDeltaM H + scoreDeltaM J := by
  ext i j
  cases i <;> cases j <;>
    simp [scoreDeltaM, realBlockMatrix, scoreDeltaU, scoreDeltaC,
      scoreDeltaV, recoverU, recoverC, recoverV]
  <;> ring

/-- The real score-direction construction is linear over real scalars. -/
theorem scoreDeltaM_real_smul (a : ℝ) (H : Matrix m m ℂ) :
    scoreDeltaM (a • H) = a • scoreDeltaM H := by
  ext i j
  cases i <;> cases j <;>
    simp [scoreDeltaM, realBlockMatrix, scoreDeltaU, scoreDeltaC,
      scoreDeltaV, recoverU, recoverC, recoverV]
  <;> ring

@[simp] theorem scoreDeltaM_zero :
    scoreDeltaM (0 : Matrix m m ℂ) = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [scoreDeltaM, realBlockMatrix, scoreDeltaU, scoreDeltaC,
      scoreDeltaV, recoverU, recoverC, recoverV]

theorem scoreDeltaM_sum
    {l : Type*} [Fintype l] (f : l → Matrix m m ℂ) :
    scoreDeltaM (∑ i, f i) = ∑ i, scoreDeltaM (f i) := by
  classical
  let s : Finset l := Finset.univ
  change scoreDeltaM (∑ i ∈ s, f i) = ∑ i ∈ s, scoreDeltaM (f i)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, scoreDeltaM_add, ih]

/-- Score-direction version of the fixed-coordinate expansion. -/
theorem scoreDeltaM_hermitianRankOne_eq_sum (c : m → ℂ) :
    scoreDeltaM (hermitianRankOne c) =
      (∑ i, ∑ j,
        ((c i * star (c j)).re / 2 : ℝ) •
            scoreDeltaM (hermitianRealCoordinateDirection i j)) +
      (∑ i, ∑ j,
        ((c i * star (c j)).im / 2 : ℝ) •
            scoreDeltaM (hermitianImagCoordinateDirection i j)) := by
  rw [hermitianRankOne_eq_sum_coordinateDirections]
  rw [scoreDeltaM_add]
  congr 1 <;>
    simp_rw [scoreDeltaM_sum, scoreDeltaM_real_smul]

/-- Pairing the variable rank-one score against a fixed real matrix reduces
to the same finite family of fixed Hermitian coordinate directions. -/
theorem trace_mul_scoreDeltaM_hermitianRankOne_eq_sum
    (G : Matrix (m ⊕ m) (m ⊕ m) ℝ) (c : m → ℂ) :
    Matrix.trace (G * scoreDeltaM (hermitianRankOne c)) =
      (∑ i, ∑ j,
        ((c i * star (c j)).re / 2 : ℝ) *
          Matrix.trace
            (G * scoreDeltaM (hermitianRealCoordinateDirection i j))) +
      (∑ i, ∑ j,
        ((c i * star (c j)).im / 2 : ℝ) *
          Matrix.trace
            (G * scoreDeltaM (hermitianImagCoordinateDirection i j))) := by
  rw [scoreDeltaM_hermitianRankOne_eq_sum]
  simp_rw [Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

/-- The trace of the rank-one score itself has the parallel fixed-coordinate
expansion. -/
theorem trace_scoreDeltaM_hermitianRankOne_eq_sum (c : m → ℂ) :
    Matrix.trace (scoreDeltaM (hermitianRankOne c)) =
      (∑ i, ∑ j,
        ((c i * star (c j)).re / 2 : ℝ) *
          Matrix.trace
            (scoreDeltaM (hermitianRealCoordinateDirection i j))) +
      (∑ i, ∑ j,
        ((c i * star (c j)).im / 2 : ℝ) *
          Matrix.trace
            (scoreDeltaM (hermitianImagCoordinateDirection i j))) := by
  rw [scoreDeltaM_hermitianRankOne_eq_sum]
  simp_rw [Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul]

/-- The trace of the real score in a Hermitian rank-one direction is the
squared Euclidean norm of that direction vector. -/
theorem trace_scoreDeltaM_hermitianRankOne_eq_vectorNormSq (c : m → ℂ) :
    Matrix.trace (scoreDeltaM (hermitianRankOne c)) = vectorNormSq c := by
  apply Complex.ofReal_injective
  rw [scoreDeltaM_trace (hermitianRankOne_isHermitian c)]
  unfold hermitianRankOne vectorNormSq
  simp [Matrix.trace, Matrix.diag, dotProduct, Complex.mul_conj,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]

end Wishart

end

end LogdetLean.GramHafnian
