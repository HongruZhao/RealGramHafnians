import LogdetLean.GramHafnian.SymmetricGaussianHafnian.EdgeSplitting
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.MatrixAssembly
/-!
# Reconstruction from independent edge blocks

The measure-preserving edge splits really recover the original symmetric
matrix.  These deterministic identities are the bridge from the product
Gaussian integrals to the literal hafnian and its cofactor vector.
-/

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- A symmetric matrix with zero last diagonal is recovered by adjoining
its last off-diagonal column to its principal background. -/
theorem appendMatrix_reconstruct {n : ℕ} {R : Type*} [Zero R]
    (S : Fin (n + 1) → Fin (n + 1) → R)
    (hS : ∀ i j, S i j = S j i) (hdiag : S (Fin.last n) (Fin.last n) = 0) :
    appendMatrix (fun i j : Fin n ↦ S i.castSucc j.castSucc)
      (fun i : Fin n ↦ S i.castSucc (Fin.last n)) = S := by
  funext i j
  refine Fin.lastCases ?_ (fun a ↦ ?_) i
  · refine Fin.lastCases ?_ (fun b ↦ ?_) j
    · simpa using hdiag.symm
    · simpa using hS b.castSucc (Fin.last n)
  · refine Fin.lastCases ?_ (fun b ↦ ?_) j <;> simp

/-- The one-vertex split and the symmetric block assembly exactly recover
the original independent-edge matrix. -/
theorem appendMatrix_lastVertexSplit (m : ℕ)
    (x : Edge (Fin (m + 1)) → ℂ) :
    appendMatrix (matrixOfEdges (lastVertexSplit m x).1)
      (lastVertexSplit m x).2 = matrixOfEdges x := by
  unfold lastVertexSplit
  rw [matrixOfEdges_restrict]
  exact appendMatrix_reconstruct (matrixOfEdges x)
    (matrixOfEdges_symmetric x) (matrixOfEdges_diag x (Fin.last m))

/-- The two-vertex split and direct symmetric block assembly exactly
recover every entry of the original independent-edge matrix. -/
theorem twoExposedMatrix_twoExposedSplit (m : ℕ)
    (x : Edge (Fin (m + 2)) → ℂ) :
    twoExposedMatrix (matrixOfEdges (twoExposedSplit m x).1)
      (twoExposedSplit m x).2.1
      (twoExposedSplit m x).2.2.1
      (twoExposedSplit m x).2.2.2 = matrixOfEdges x := by
  have hA : matrixOfEdges (twoExposedSplit m x).1 =
      fun i j : Fin m ↦ matrixOfEdges x (remainingIndex m i) (remainingIndex m j) := by
    rw [twoExposedSplit_background, matrixOfEdges_restrict]
    rfl
  have hX : (twoExposedSplit m x).2.2.1 =
      fun i : Fin m ↦ matrixOfEdges x (remainingIndex m i) (exposedXIndex m) := by
    funext i
    exact twoExposedSplit_X m x i
  have hY : (twoExposedSplit m x).2.2.2 =
      fun i : Fin m ↦ matrixOfEdges x (remainingIndex m i) (exposedYIndex m) := by
    funext i
    exact twoExposedSplit_Y m x i
  rw [hA, hX, hY, twoExposedSplit_scalar]
  unfold twoExposedMatrix
  let B : Fin (m + 1) → Fin (m + 1) → ℂ :=
    fun i j ↦ matrixOfEdges x i.castSucc j.castSucc
  have hB : appendMatrix
      (fun i j : Fin m ↦ matrixOfEdges x (remainingIndex m i) (remainingIndex m j))
      (fun i : Fin m ↦ matrixOfEdges x (remainingIndex m i) (exposedXIndex m)) = B := by
    exact appendMatrix_reconstruct B
      (fun i j ↦ matrixOfEdges_symmetric x i.castSucc j.castSucc)
      (matrixOfEdges_diag x (Fin.last m).castSucc)
  rw [hB]
  have hg : Fin.lastCases
      (matrixOfEdges x (exposedXIndex m) (exposedYIndex m))
      (fun i : Fin m ↦ matrixOfEdges x (remainingIndex m i) (exposedYIndex m)) =
      fun i : Fin (m + 1) ↦ matrixOfEdges x i.castSucc (Fin.last (m + 1)) := by
    funext i
    refine Fin.lastCases ?_ (fun a ↦ ?_) i <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc] <;> rfl
  rw [hg]
  exact appendMatrix_reconstruct (matrixOfEdges x)
    (matrixOfEdges_symmetric x) (matrixOfEdges_diag x (Fin.last (m + 1)))

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
