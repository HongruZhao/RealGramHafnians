import RealGramHafnians.Proofs.RowSuspensionLocalCompression
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealGlobalCofactorCompression
import LogdetLean.GramHafnian.RealComplexAnticoncentration.RealLiteralCofactorLaw
/-!
# Global row-suspension compression

This file supplies permutation symmetry, singleton identification, and the
finite-support iteration for the new row-suspension characteristic function.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real ENNReal ComplexConjugate

namespace LogdetLean.GramHafnian

noncomputable section

set_option maxHeartbeats 4000000

theorem finiteRealGramCofactorVector_rowSuspension_singleton
    {d k : ℕ} (j : Fin d) (s : ℝ)
    (B : Fin d → (Fin k → ℝ)) :
    finiteRealGramCofactorVector
        (rowSuspensionColumns (realSingleCoordinate j s) B) j =
      finiteRealGramCofactorVector B j := by
  unfold finiteRealGramCofactorVector
  congr 1
  funext a b
  unfold realColumnTransposeGram rowSuspensionColumns
  rw [Fin.sum_univ_succ]
  simp only [prependRealCoordinate_zero, prependRealCoordinate_succ]
  have ha : a.1 ≠ j := a.2
  have hb : b.1 ≠ j := b.2
  simp [realSingleCoordinate, ha, hb]

theorem rowSuspensionPhase_singleton
    {d k : ℕ} (j : Fin d) (s : ℝ)
    (B : Fin d → (Fin k → ℝ)) :
    rowSuspensionPhase (realSingleCoordinate j s) B =
      finiteRealGramCofactorPhase B (realSingleCoordinate j s) := by
  unfold rowSuspensionPhase finiteRealGramCofactorPhase
  calc
    (∑ i, realSingleCoordinate j s i *
        finiteRealGramCofactorVector
          (rowSuspensionColumns (realSingleCoordinate j s) B) i) =
      s * finiteRealGramCofactorVector
        (rowSuspensionColumns (realSingleCoordinate j s) B) j := by
        rw [Finset.sum_eq_single j]
        · simp [realSingleCoordinate]
        · intro b _hb hbj
          simp [realSingleCoordinate, hbj]
        · simp
    _ = s * finiteRealGramCofactorVector B j := by
      rw [finiteRealGramCofactorVector_rowSuspension_singleton]
    _ = ∑ i, realSingleCoordinate j s i *
        finiteRealGramCofactorVector B i := by
      rw [Finset.sum_eq_single j]
      · simp [realSingleCoordinate]
      · intro b _hb hbj
        simp [realSingleCoordinate, hbj]
      · simp

theorem rowSuspensionCharacteristic_singleton_eq_finite
    {d k : ℕ} (t : ℝ) (j : Fin d) (s : ℝ) :
    rowSuspensionCharacteristic d k t (realSingleCoordinate j s) =
      finiteRealGramCofactorCharacteristic (Fin d) k
        (realSingleCoordinate j (t * s)) := by
  unfold rowSuspensionCharacteristic finiteRealGramCofactorCharacteristic
  apply integral_congr_ae
  filter_upwards [] with B
  unfold rowSuspensionPhaseCharacter finiteRealGramCofactorPhaseCharacter
  rw [rowSuspensionPhase_singleton]
  congr 2
  unfold finiteRealGramCofactorPhase
  simp_rw [Finset.mul_sum]
  apply congrArg ((↑) : ℝ → ℂ)
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hij : i = j
  · subst i
    simp [realSingleCoordinate]
    ring
  · simp [realSingleCoordinate, hij]

theorem rowSuspensionCharacteristic_singletonEven
    {d k : ℕ} (t : ℝ) :
    RealSingletonEven (rowSuspensionCharacteristic d k t) := by
  intro i c
  rw [rowSuspensionCharacteristic_singleton_eq_finite,
    rowSuspensionCharacteristic_singleton_eq_finite]
  have h := finiteRealGramCofactorCharacteristic_singletonEven
    (iota := Fin d) (k := k) i (t * c)
  convert h using 1 <;> ring

theorem rowSuspensionPhase_reindex_perm
    {d k : ℕ} (sigma : Equiv.Perm (Fin d))
    (z : Fin d → ℝ) (B : Fin d → (Fin k → ℝ)) :
    rowSuspensionPhase (realPermuteCoordinates sigma z)
        (reindexFiniteRealColumnFamily sigma.symm B) =
      rowSuspensionPhase z B := by
  unfold rowSuspensionPhase realPermuteCoordinates
    reindexFiniteRealColumnFamily rowSuspensionColumns
  exact finiteRealGramCofactorPhase_reindex_equiv sigma.symm
    (rowSuspensionColumns z B) z

theorem rowSuspensionCharacteristic_permutationInvariant
    (d k : ℕ) (t : ℝ) :
    RealPermutationInvariant (rowSuspensionCharacteristic d k t) := by
  intro sigma z
  let e : (Fin d → (Fin k → ℝ)) ≃ᵐ (Fin d → (Fin k → ℝ)) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin d ↦ Fin k → ℝ) sigma
  have he : MeasurePreserving e
      (Measure.pi fun _ : Fin d ↦ standardRealGaussianVectorMeasure k)
      (Measure.pi fun _ : Fin d ↦ standardRealGaussianVectorMeasure k) := by
    simpa using (measurePreserving_piCongrLeft
      (fun _ : Fin d ↦ standardRealGaussianVectorMeasure k) sigma)
  unfold rowSuspensionCharacteristic
  rw [← he.integral_comp']
  apply integral_congr_ae
  filter_upwards [] with B
  have he_apply : e B = reindexFiniteRealColumnFamily sigma.symm B := by
    ext i p
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin d ↦ Fin k → ℝ) sigma B (sigma.symm i)
    simpa [e, reindexFiniteRealColumnFamily] using
      congrArg (fun f ↦ f p) h
  unfold rowSuspensionPhaseCharacter
  rw [he_apply]
  rw [rowSuspensionPhase_reindex_perm]

theorem rowSuspensionCharacteristic_singletonExchangeable
    {d k : ℕ} (t : ℝ) :
    RealSingletonExchangeable (rowSuspensionCharacteristic d k t) := by
  intro i j z
  classical
  by_cases hij : i = j
  · subst j
    rfl
  let sigma : Equiv.Perm (Fin d) := Equiv.swap i j
  have h := rowSuspensionCharacteristic_permutationInvariant d k t
    sigma (realSingleCoordinate j z)
  rw [show realPermuteCoordinates sigma (realSingleCoordinate j z) =
      realSingleCoordinate i z by
    funext l
    by_cases hli : l = i
    · subst l
      simp [sigma, realPermuteCoordinates, realSingleCoordinate, hij]
    · by_cases hlj : l = j
      · subst l
        simp [sigma, realPermuteCoordinates, realSingleCoordinate, hij, hli]
      · simp [sigma, realPermuteCoordinates, realSingleCoordinate,
          hli, hlj, Equiv.swap_apply_of_ne_of_ne]] at h
  exact h

theorem rowSuspensionCharacteristic_penultimate_final_two_endpoints
    (m k : ℕ) (t : ℝ) (w : Fin (m + 2) → ℝ)
    (hX : w (exposedXIndex m) ≠ 0)
    (hY : w (exposedYIndex m) ≠ 0) :
    ∃ wLeft wRight : Fin (m + 2) → ℝ,
      realCoordinateSupportCard wLeft < realCoordinateSupportCard w ∧
      realCoordinateSupportCard wRight < realCoordinateSupportCard w ∧
      realCoordinateEnergy wLeft = realCoordinateEnergy w ∧
      realCoordinateEnergy wRight = realCoordinateEnergy w ∧
      ‖rowSuspensionCharacteristic (m + 2) k t w‖ ≤
        max ‖rowSuspensionCharacteristic (m + 2) k t wLeft‖
          ‖rowSuspensionCharacteristic (m + 2) k t wRight‖ := by
  let theta := realExposedTheta w
  let wLeft := realLeftExposedEndpoint w theta
  let wRight := realRightExposedEndpoint w theta
  have ht : 0 < theta := realExposedTheta_pos hX hY
  have ht1 : theta < 1 := realExposedTheta_lt_one hX hY
  refine ⟨wLeft, wRight,
    realCoordinateSupportCard_leftExposedEndpoint_lt hX hY,
    realCoordinateSupportCard_rightExposedEndpoint_lt hX hY,
    realCoordinateEnergy_leftExposedEndpoint hX hY,
    realCoordinateEnergy_rightExposedEndpoint hX hY, ?_⟩
  apply rowSuspensionCharacteristic_two_exposed_max
    t w wLeft wRight theta ht ht1
  · intro i
    exact realLeftExposedEndpoint_background w theta i
  · intro i
    exact realRightExposedEndpoint_background w theta i
  · exact realLeftExposedEndpoint_Y w theta
  · exact realRightExposedEndpoint_X w theta
  · dsimp [wLeft]
    rw [realLeftExposedEndpoint_X]
    exact real_endpoint_scale ht _
  · dsimp [wRight]
    rw [realRightExposedEndpoint_Y]
    exact real_endpoint_scale (sub_pos.mpr ht1) _

theorem rowSuspensionCharacteristic_global_two_endpoints
    (m k : ℕ) (t : ℝ) :
    ∀ z : Fin (m + 2) → ℝ, 1 < realCoordinateSupportCard z →
      ∃ zLeft zRight : Fin (m + 2) → ℝ,
        realCoordinateSupportCard zLeft < realCoordinateSupportCard z ∧
        realCoordinateSupportCard zRight < realCoordinateSupportCard z ∧
        realCoordinateEnergy zLeft = realCoordinateEnergy z ∧
        realCoordinateEnergy zRight = realCoordinateEnergy z ∧
        ‖rowSuspensionCharacteristic (m + 2) k t z‖ ≤
          max ‖rowSuspensionCharacteristic (m + 2) k t zLeft‖
            ‖rowSuspensionCharacteristic (m + 2) k t zRight‖ := by
  apply global_real_two_endpoints_of_penultimate_final
    (rowSuspensionCharacteristic (m + 2) k t)
    (rowSuspensionCharacteristic_permutationInvariant (m + 2) k t)
  intro w hPen hFinal
  apply rowSuspensionCharacteristic_penultimate_final_two_endpoints m k t w
  · have hi : penultimateCoordinate m = exposedXIndex m := by
      apply Fin.ext
      rfl
    rwa [hi] at hPen
  · have hi : finalCoordinate m = exposedYIndex m := by
      apply Fin.ext
      rfl
    rwa [hi] at hFinal

/-- Full radial compression of the row-suspension characteristic. -/
theorem rowSuspensionCharacteristic_radial_compression
    (m k : ℕ) (t : ℝ) (base : Fin (m + 2))
    (z : Fin (m + 2) → ℝ) :
    ‖rowSuspensionCharacteristic (m + 2) k t z‖ ≤
      ‖rowSuspensionCharacteristic (m + 2) k t
        (realSingleCoordinate base
          (Real.sqrt (realCoordinateEnergy z)))‖ := by
  apply finite_real_coordinate_compression_iteration
    (rowSuspensionCharacteristic (m + 2) k t) base
    (rowSuspensionCharacteristic_singletonExchangeable t)
    (rowSuspensionCharacteristic_singletonEven t)
  intro w hw
  obtain ⟨wLeft, wRight, hsLeft, hsRight, heLeft, heRight, hmax⟩ :=
    rowSuspensionCharacteristic_global_two_endpoints m k t w hw
  exact realCompressionStep_of_two_endpoints
    (rowSuspensionCharacteristic (m + 2) k t)
    hsLeft hsRight heLeft heRight hmax

theorem rowSuspensionCharacteristic_radial_compression_dim
    (d k : ℕ) (hd : 2 ≤ d) (t : ℝ) (base : Fin d)
    (z : Fin d → ℝ) :
    ‖rowSuspensionCharacteristic d k t z‖ ≤
      ‖rowSuspensionCharacteristic d k t
        (realSingleCoordinate base
          (Real.sqrt (realCoordinateEnergy z)))‖ := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 2 := ⟨d - 2, by omega⟩
  exact rowSuspensionCharacteristic_radial_compression m k t base z

end

end LogdetLean.GramHafnian
