import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.CofactorPreservedCoordinate
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedRankOneScore
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
/-!
# Regularized preserved-coordinate cofactor weights

For `delta > 0` the weight `(W(S)+delta)^(-2)` regularizes the target
inverse-square cofactor weight.  Every coordinate coefficient in the fixed
Hermitian rank-one decomposition is then a bounded Borel function of the
preserved transpose-Gram coordinate `S`.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/- Mathlib does not install a coordinatewise measurable-space instance for
complex `Matrix`; mirror the existing real-matrix instance used throughout
the Wishart development. -/
instance complexMatrixMeasurableSpace (ι κ : Type*) :
    MeasurableSpace (Matrix ι κ ℂ) := by
  unfold Matrix
  infer_instance

variable {m : Type*} [Fintype m] [LinearOrder m]

/-- The cofactor vector as a function on the preserved `S` coordinate. -/
def preservedCofactorVector (S : Matrix m m ℂ) : m → ℂ :=
  transposeGramCofactorVector S

/-- The regularized inverse-square cofactor-energy weight. -/
def regularizedCofactorWeight (δ : ℝ) (S : Matrix m m ℂ) : ℝ :=
  (transposeGramCofactorW S + δ)⁻¹ ^ 2

theorem continuous_preservedCofactorVector_apply (j : m) :
    Continuous (fun S : Matrix m m ℂ ↦ preservedCofactorVector S j) := by
  unfold preservedCofactorVector transposeGramCofactorVector
  exact continuous_typeHafnian.comp (by fun_prop)

theorem continuous_preservedCofactorVector :
    Continuous (preservedCofactorVector : Matrix m m ℂ → m → ℂ) := by
  exact continuous_pi fun j ↦ continuous_preservedCofactorVector_apply j

theorem continuous_transposeGramCofactorW :
    Continuous (transposeGramCofactorW : Matrix m m ℂ → ℝ) := by
  unfold transposeGramCofactorW
  apply continuous_finsetSum
  intro j _
  exact Complex.continuous_normSq.comp
    (continuous_preservedCofactorVector_apply j)

theorem measurable_preservedCofactorVector :
    Measurable (preservedCofactorVector : Matrix m m ℂ → m → ℂ) := by
  unfold preservedCofactorVector transposeGramCofactorVector typeHafnian
    typeMatchingMonomial
  fun_prop

theorem measurable_transposeGramCofactorW :
    Measurable (transposeGramCofactorW : Matrix m m ℂ → ℝ) := by
  unfold transposeGramCofactorW transposeGramCofactorVector typeHafnian
    typeMatchingMonomial
  fun_prop

theorem continuous_regularizedCofactorWeight {δ : ℝ} (hδ : 0 < δ) :
    Continuous (regularizedCofactorWeight (m := m) δ) := by
  unfold regularizedCofactorWeight
  apply Continuous.pow
  apply Continuous.inv₀
  · exact continuous_transposeGramCofactorW.add continuous_const
  · intro S
    exact ne_of_gt (add_pos_of_nonneg_of_pos
      (transposeGramCofactorW_nonneg S) hδ)

theorem measurable_regularizedCofactorWeight {δ : ℝ} (hδ : 0 < δ) :
    Measurable (regularizedCofactorWeight (m := m) δ) := by
  unfold regularizedCofactorWeight
  exact (measurable_inv.comp
    (measurable_transposeGramCofactorW.add measurable_const)).pow_const 2

theorem regularizedCofactorWeight_nonneg (δ : ℝ) (S : Matrix m m ℂ) :
    0 ≤ regularizedCofactorWeight δ S := by
  unfold regularizedCofactorWeight
  positivity

/-- The cofactor energy is exactly the squared norm used by the rank-one
score assembly. -/
theorem vectorNormSq_preservedCofactorVector (S : Matrix m m ℂ) :
    vectorNormSq (preservedCofactorVector S) = transposeGramCofactorW S := by
  unfold vectorNormSq preservedCofactorVector transposeGramCofactorW
    transposeGramCofactorVector
  simp [dotProduct, Complex.normSq_apply]

theorem regularized_weight_mul_vectorNormSq (δ : ℝ)
    (S : Matrix m m ℂ) :
    regularizedCofactorWeight δ S *
        vectorNormSq (preservedCofactorVector S) =
      transposeGramCofactorW S /
        (transposeGramCofactorW S + δ) ^ 2 := by
  rw [vectorNormSq_preservedCofactorVector]
  unfold regularizedCofactorWeight
  rw [inv_pow]
  rw [div_eq_mul_inv]
  ring

/-- Real coordinate weight as a scalar function of `S`. -/
def regularizedCofactorRealCoordinateWeight
    (δ : ℝ) (i j : m) (S : Matrix m m ℂ) : ℝ :=
  rankOneRealCoordinateWeight
    (regularizedCofactorWeight δ) preservedCofactorVector i j S

/-- Imaginary coordinate weight as a scalar function of `S`. -/
def regularizedCofactorImagCoordinateWeight
    (δ : ℝ) (i j : m) (S : Matrix m m ℂ) : ℝ :=
  rankOneImagCoordinateWeight
    (regularizedCofactorWeight δ) preservedCofactorVector i j S

theorem continuous_regularizedCofactorRealCoordinateWeight
    {δ : ℝ} (hδ : 0 < δ) (i j : m) :
    Continuous (regularizedCofactorRealCoordinateWeight δ i j) := by
  unfold regularizedCofactorRealCoordinateWeight
    rankOneRealCoordinateWeight
  have hprod : Continuous (fun S : Matrix m m ℂ ↦
      preservedCofactorVector S i * star (preservedCofactorVector S j)) :=
    (continuous_preservedCofactorVector_apply i).mul
      ((continuous_preservedCofactorVector_apply j).star)
  exact (continuous_regularizedCofactorWeight hδ).mul
    ((Complex.continuous_re.comp hprod).div_const 2)

theorem continuous_regularizedCofactorImagCoordinateWeight
    {δ : ℝ} (hδ : 0 < δ) (i j : m) :
    Continuous (regularizedCofactorImagCoordinateWeight δ i j) := by
  unfold regularizedCofactorImagCoordinateWeight
    rankOneImagCoordinateWeight
  have hprod : Continuous (fun S : Matrix m m ℂ ↦
      preservedCofactorVector S i * star (preservedCofactorVector S j)) :=
    (continuous_preservedCofactorVector_apply i).mul
      ((continuous_preservedCofactorVector_apply j).star)
  exact (continuous_regularizedCofactorWeight hδ).mul
    ((Complex.continuous_im.comp hprod).div_const 2)

theorem measurable_regularizedCofactorRealCoordinateWeight
    {δ : ℝ} (hδ : 0 < δ) (i j : m) :
    Measurable (regularizedCofactorRealCoordinateWeight δ i j) := by
  unfold regularizedCofactorRealCoordinateWeight
    rankOneRealCoordinateWeight
  have hi : Measurable (fun S : Matrix m m ℂ ↦
      preservedCofactorVector S i) :=
    (measurable_pi_apply i).comp measurable_preservedCofactorVector
  have hj : Measurable (fun S : Matrix m m ℂ ↦
      preservedCofactorVector S j) :=
    (measurable_pi_apply j).comp measurable_preservedCofactorVector
  exact (measurable_regularizedCofactorWeight hδ).mul
    ((Complex.measurable_re.comp
      (hi.mul (continuous_star.measurable.comp hj))).div_const 2)

theorem measurable_regularizedCofactorImagCoordinateWeight
    {δ : ℝ} (hδ : 0 < δ) (i j : m) :
    Measurable (regularizedCofactorImagCoordinateWeight δ i j) := by
  unfold regularizedCofactorImagCoordinateWeight
    rankOneImagCoordinateWeight
  have hi : Measurable (fun S : Matrix m m ℂ ↦
      preservedCofactorVector S i) :=
    (measurable_pi_apply i).comp measurable_preservedCofactorVector
  have hj : Measurable (fun S : Matrix m m ℂ ↦
      preservedCofactorVector S j) :=
    (measurable_pi_apply j).comp measurable_preservedCofactorVector
  exact (measurable_regularizedCofactorWeight hδ).mul
    ((Complex.measurable_im.comp
      (hi.mul (continuous_star.measurable.comp hj))).div_const 2)

theorem preservedCofactorVector_normSq_le_W
    (S : Matrix m m ℂ) (i : m) :
    Complex.normSq (preservedCofactorVector S i) ≤
      transposeGramCofactorW S := by
  unfold transposeGramCofactorW
  exact Finset.single_le_sum
    (fun j _ ↦ Complex.normSq_nonneg (preservedCofactorVector S j))
    (Finset.mem_univ i)

theorem abs_re_cofactorProduct_div_two_le_W
    (S : Matrix m m ℂ) (i j : m) :
    |((preservedCofactorVector S i *
        star (preservedCofactorVector S j)).re / 2)| ≤
      transposeGramCofactorW S := by
  let ci := preservedCofactorVector S i
  let cj := preservedCofactorVector S j
  let W := transposeGramCofactorW S
  have hWi : Complex.normSq ci ≤ W :=
    preservedCofactorVector_normSq_le_W S i
  have hWj : Complex.normSq cj ≤ W :=
    preservedCofactorVector_normSq_le_W S j
  have hW : 0 ≤ W := transposeGramCofactorW_nonneg S
  have ham : 2 * (‖ci‖ * ‖cj‖) ≤
      Complex.normSq ci + Complex.normSq cj := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖ci‖ - ‖cj‖)]
  have hprod : ‖ci‖ * ‖cj‖ ≤ W := by
    nlinarith
  calc
    |((ci * star cj).re / 2)| = |(ci * star cj).re| / 2 := by
      rw [abs_div]
      norm_num
    _ ≤ ‖ci * star cj‖ / 2 := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ = (‖ci‖ * ‖cj‖) / 2 := by
      rw [Complex.norm_mul, norm_star]
    _ ≤ W := by nlinarith [norm_nonneg ci, norm_nonneg cj]

theorem abs_im_cofactorProduct_div_two_le_W
    (S : Matrix m m ℂ) (i j : m) :
    |((preservedCofactorVector S i *
        star (preservedCofactorVector S j)).im / 2)| ≤
      transposeGramCofactorW S := by
  let ci := preservedCofactorVector S i
  let cj := preservedCofactorVector S j
  let W := transposeGramCofactorW S
  have hWi : Complex.normSq ci ≤ W :=
    preservedCofactorVector_normSq_le_W S i
  have hWj : Complex.normSq cj ≤ W :=
    preservedCofactorVector_normSq_le_W S j
  have hW : 0 ≤ W := transposeGramCofactorW_nonneg S
  have ham : 2 * (‖ci‖ * ‖cj‖) ≤
      Complex.normSq ci + Complex.normSq cj := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖ci‖ - ‖cj‖)]
  have hprod : ‖ci‖ * ‖cj‖ ≤ W := by
    nlinarith
  calc
    |((ci * star cj).im / 2)| = |(ci * star cj).im| / 2 := by
      rw [abs_div]
      norm_num
    _ ≤ ‖ci * star cj‖ / 2 := by
      gcongr
      exact Complex.abs_im_le_norm _
    _ = (‖ci‖ * ‖cj‖) / 2 := by
      rw [Complex.norm_mul, norm_star]
    _ ≤ W := by nlinarith [norm_nonneg ci, norm_nonneg cj]

theorem cofactorEnergy_div_add_sq_le_inv
    {δ : ℝ} (hδ : 0 < δ) (S : Matrix m m ℂ) :
    transposeGramCofactorW S /
        (transposeGramCofactorW S + δ) ^ 2 ≤ δ⁻¹ := by
  let W := transposeGramCofactorW S
  have hW : 0 ≤ W := transposeGramCofactorW_nonneg S
  have hden : 0 < W + δ := add_pos_of_nonneg_of_pos hW hδ
  change W / (W + δ) ^ 2 ≤ δ⁻¹
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) hδ).2
  nlinarith [sq_nonneg W, sq_nonneg δ]

theorem abs_regularizedCofactorRealCoordinateWeight_le
    {δ : ℝ} (hδ : 0 < δ) (i j : m) (S : Matrix m m ℂ) :
    |regularizedCofactorRealCoordinateWeight δ i j S| ≤ δ⁻¹ := by
  let W := transposeGramCofactorW S
  have hweight : 0 ≤ regularizedCofactorWeight δ S :=
    regularizedCofactorWeight_nonneg δ S
  have hcoord := abs_re_cofactorProduct_div_two_le_W S i j
  unfold regularizedCofactorRealCoordinateWeight
    rankOneRealCoordinateWeight
  rw [abs_mul, abs_of_nonneg hweight]
  calc
    regularizedCofactorWeight δ S *
        |((preservedCofactorVector S i *
          star (preservedCofactorVector S j)).re / 2)| ≤
        regularizedCofactorWeight δ S * W := by
      exact mul_le_mul_of_nonneg_left hcoord hweight
    _ = W / (W + δ) ^ 2 := by
      unfold regularizedCofactorWeight
      rw [inv_pow, div_eq_mul_inv]
      ring
    _ ≤ δ⁻¹ := cofactorEnergy_div_add_sq_le_inv hδ S

theorem abs_regularizedCofactorImagCoordinateWeight_le
    {δ : ℝ} (hδ : 0 < δ) (i j : m) (S : Matrix m m ℂ) :
    |regularizedCofactorImagCoordinateWeight δ i j S| ≤ δ⁻¹ := by
  let W := transposeGramCofactorW S
  have hweight : 0 ≤ regularizedCofactorWeight δ S :=
    regularizedCofactorWeight_nonneg δ S
  have hcoord := abs_im_cofactorProduct_div_two_le_W S i j
  unfold regularizedCofactorImagCoordinateWeight
    rankOneImagCoordinateWeight
  rw [abs_mul, abs_of_nonneg hweight]
  calc
    regularizedCofactorWeight δ S *
        |((preservedCofactorVector S i *
          star (preservedCofactorVector S j)).im / 2)| ≤
        regularizedCofactorWeight δ S * W := by
      exact mul_le_mul_of_nonneg_left hcoord hweight
    _ = W / (W + δ) ^ 2 := by
      unfold regularizedCofactorWeight
      rw [inv_pow, div_eq_mul_inv]
      ring
    _ ≤ δ⁻¹ := cofactorEnergy_div_add_sq_le_inv hδ S

end Wishart

end

end LogdetLean.GramHafnian
