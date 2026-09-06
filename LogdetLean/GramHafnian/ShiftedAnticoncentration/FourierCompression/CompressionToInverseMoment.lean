import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CoordinateIteration
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.InverseRecurrence
/-!
# Coordinate compression to the inverse-moment inequality

This module is the end-to-end analytic interface for the cofactor-vector
law.  It combines finite coordinate iteration, the radial singleton mixture,
auxiliary-Gaussian Fourier averaging, and the exact `Gamma(d,1)` inverse
factor.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Real

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Raw coordinate energy agrees with squared Euclidean norm after viewing a
complex Euclidean vector as its coordinate function. -/
theorem coordinateEnergy_euclideanSpace_coe
    {d : ℕ} (xi : CircularEuclideanSpace d) :
    coordinateEnergy (fun i : Fin d => xi i) = ‖xi‖ ^ 2 := by
  unfold coordinateEnergy
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  exact Complex.normSq_eq_norm_sq (xi i)

/-- End-to-end inverse-moment consequence of finite Fourier-coordinate
compression for a complex `d`-vector law.

`rawPhi` is the same characteristic function written on ordinary coordinate
functions. `hsingleton` is the conditional circular-Gaussian mixture formula
on the positive first axis.  All finite iteration and the exact auxiliary
`1 / (d - 1)` Gamma factor are discharged here. -/
theorem ennInverse_norm_sq_le_auxiliaryGamma_factor_of_coordinate_compression
    {d : ℕ} (hd : 2 ≤ d) (base : Fin d)
    (mu : Measure (CircularEuclideanSpace d)) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (rawPhi : (Fin d → ℂ) → ℂ)
    (hrawPhi : ∀ xi : CircularEuclideanSpace d,
      rawPhi (fun i => xi i) = charFun mu xi)
    (hexchange : SingletonExchangeable rawPhi)
    (hphase : CommonPhaseInvariant rawPhi)
    (hstep : ∀ z : Fin d → ℂ, 1 < coordinateSupportCard z →
      ∃ z' : Fin d → ℂ,
        coordinateSupportCard z' < coordinateSupportCard z ∧
        coordinateEnergy z' = coordinateEnergy z ∧
        ‖rawPhi z‖ ≤ ‖rawPhi z'‖)
    (hsingleton : ∀ r : ℝ, 0 ≤ r →
      rawPhi (singleCoordinate base (r : ℂ)) =
        ((∫ w, Real.exp (-(V w * r ^ 2) / 4) ∂nu) : ℝ))
    (hnormpos : ∀ᵐ x ∂mu, 0 < ‖x‖ ^ 2) :
    ennInverseMoment mu (fun x => ‖x‖ ^ 2) ≤
      ennInverseMoment nu V * ENNReal.ofReal ((d : ℝ) - 1)⁻¹ := by
  letI : Nonempty (Fin d) := ⟨base⟩
  let radial : ℝ → ℝ := fun r =>
    ∫ w, Real.exp (-(V w * r ^ 2) / 4) ∂nu
  have hradial_nonneg : ∀ r : ℝ, 0 ≤ r → 0 ≤ radial r := by
    intro r hr
    dsimp [radial]
    apply integral_nonneg
    intro w
    exact (Real.exp_pos _).le
  have hradial : ∀ r : ℝ, 0 ≤ r →
      rawPhi (singleCoordinate base (r : ℂ)) =
        (radial r : ℂ) := by
    intro r hr
    exact hsingleton r hr
  have hrawCompression : ∀ z : Fin d → ℂ,
      ‖rawPhi z‖ ≤ radial (Real.sqrt (coordinateEnergy z)) :=
    finite_coordinate_compression_to_radial rawPhi base
      radial hexchange hphase hstep hradial hradial_nonneg
  have hcompression : ∀ xi : CircularEuclideanSpace d,
      (charFun mu xi).re ≤
        ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 4) ∂nu := by
    intro xi
    let z : Fin d → ℂ := fun i => xi i
    calc
      (charFun mu xi).re ≤ ‖charFun mu xi‖ := Complex.re_le_norm _
      _ = ‖rawPhi z‖ := by rw [hrawPhi xi]
      _ ≤ radial (Real.sqrt (coordinateEnergy z)) := hrawCompression z
      _ = ∫ w, Real.exp (-(V w * ‖xi‖ ^ 2) / 4) ∂nu := by
        dsimp [radial]
        apply integral_congr_ae
        filter_upwards [] with w
        congr 1
        rw [Real.sq_sqrt (coordinateEnergy_nonneg z),
          coordinateEnergy_euclideanSpace_coe xi]
  exact ennInverse_norm_sq_le_auxiliaryGamma_factor hd mu nu V hV
    hVnonneg hVpos hcompression hnormpos

/-- The same end-to-end theorem with the local analytic input supplied in
the paper's two-endpoint `max` form. -/
theorem ennInverse_norm_sq_le_auxiliaryGamma_factor_of_two_endpoints
    {d : ℕ} (hd : 2 ≤ d) (base : Fin d)
    (mu : Measure (CircularEuclideanSpace d)) [IsProbabilityMeasure mu]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (V : Omega → ℝ) (hV : Measurable V)
    (hVnonneg : ∀ w, 0 ≤ V w)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (rawPhi : (Fin d → ℂ) → ℂ)
    (hrawPhi : ∀ xi : CircularEuclideanSpace d,
      rawPhi (fun i => xi i) = charFun mu xi)
    (hexchange : SingletonExchangeable rawPhi)
    (hphase : CommonPhaseInvariant rawPhi)
    (htwo : ∀ z : Fin d → ℂ, 1 < coordinateSupportCard z →
      ∃ zLeft zRight : Fin d → ℂ,
        coordinateSupportCard zLeft < coordinateSupportCard z ∧
        coordinateSupportCard zRight < coordinateSupportCard z ∧
        coordinateEnergy zLeft = coordinateEnergy z ∧
        coordinateEnergy zRight = coordinateEnergy z ∧
        ‖rawPhi z‖ ≤ max ‖rawPhi zLeft‖ ‖rawPhi zRight‖)
    (hsingleton : ∀ r : ℝ, 0 ≤ r →
      rawPhi (singleCoordinate base (r : ℂ)) =
        ((∫ w, Real.exp (-(V w * r ^ 2) / 4) ∂nu) : ℝ))
    (hnormpos : ∀ᵐ x ∂mu, 0 < ‖x‖ ^ 2) :
    ennInverseMoment mu (fun x => ‖x‖ ^ 2) ≤
      ennInverseMoment nu V * ENNReal.ofReal ((d : ℝ) - 1)⁻¹ := by
  apply ennInverse_norm_sq_le_auxiliaryGamma_factor_of_coordinate_compression
    hd base mu nu V hV hVnonneg hVpos rawPhi hrawPhi hexchange hphase
  · intro z hz
    obtain ⟨zLeft, zRight, hsLeft, hsRight, heLeft, heRight, hmax⟩ :=
      htwo z hz
    exact compressionStep_of_two_endpoints rawPhi hsLeft hsRight
      heLeft heRight hmax
  · exact hsingleton
  · exact hnormpos

end

end LogdetLean.GramHafnian
