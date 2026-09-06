import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CoordinateIteration
/-!
# Exposing two nonzero Fourier coordinates

The analytic two-column compression is most conveniently stated for the last
two coordinates.  This file contains the finite permutation bookkeeping that
reduces the global two-endpoint hypothesis to that distinguished pair.
-/

open Complex
open scoped BigOperators Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- Reindex a finite Fourier vector by a permutation. -/
def permuteCoordinates {d : ℕ} (σ : Equiv.Perm (Fin d))
    (z : Fin d → ℂ) : Fin d → ℂ :=
  z ∘ σ.symm

@[simp]
theorem permuteCoordinates_apply {d : ℕ} (σ : Equiv.Perm (Fin d))
    (z : Fin d → ℂ) (i : Fin d) :
    permuteCoordinates σ z i = z (σ.symm i) := rfl

@[simp]
theorem permuteCoordinates_refl {d : ℕ} (z : Fin d → ℂ) :
    permuteCoordinates (Equiv.refl (Fin d)) z = z := by
  rfl

/-- Reindexing by the inverse permutation undoes reindexing. -/
@[simp]
theorem permuteCoordinates_symm_perm {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (z : Fin d → ℂ) :
    permuteCoordinates σ.symm (permuteCoordinates σ z) = z := by
  ext i
  simp [permuteCoordinates]

/-- A permutation preserves the squared Fourier radius. -/
theorem coordinateEnergy_permuteCoordinates {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (z : Fin d → ℂ) :
    coordinateEnergy (permuteCoordinates σ z) = coordinateEnergy z := by
  unfold coordinateEnergy permuteCoordinates
  simpa [Function.comp_def] using
    (σ.symm.sum_comp (fun i : Fin d ↦ Complex.normSq (z i)))

/-- The support itself is carried to its image under the permutation. -/
theorem coordinateSupport_permuteCoordinates {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (z : Fin d → ℂ) :
    coordinateSupport (permuteCoordinates σ z) =
      (coordinateSupport z).map σ.toEmbedding := by
  classical
  ext i
  constructor
  · intro hi
    have hi' : z (σ.symm i) ≠ 0 := by
      exact (Finset.mem_filter.mp hi).2
    apply Finset.mem_map.mpr
    refine ⟨σ.symm i, ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    have hj' : z j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hjeq : j = σ.symm i := by
      apply σ.injective
      simpa using hji
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change z (σ.symm i) ≠ 0
    simpa [hjeq] using hj'

/-- A permutation preserves the number of nonzero Fourier coordinates. -/
theorem coordinateSupportCard_permuteCoordinates {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (z : Fin d → ℂ) :
    coordinateSupportCard (permuteCoordinates σ z) =
      coordinateSupportCard z := by
  unfold coordinateSupportCard
  rw [coordinateSupport_permuteCoordinates]
  exact Finset.card_map _

/-- The penultimate coordinate of `Fin (n+2)`. -/
def penultimateCoordinate (n : ℕ) : Fin (n + 2) :=
  Fin.castSucc (Fin.last n)

/-- The final coordinate of `Fin (n+2)`. -/
def finalCoordinate (n : ℕ) : Fin (n + 2) :=
  Fin.last (n + 1)

theorem penultimateCoordinate_ne_finalCoordinate (n : ℕ) :
    penultimateCoordinate n ≠ finalCoordinate n := by
  exact Fin.castSucc_ne_last (Fin.last n)

/-- If at least two coordinates are nonzero, a permutation exposes two of
them in the distinguished penultimate and final positions. -/
theorem exists_permutation_nonzero_penultimate_final
    {n : ℕ} (z : Fin (n + 2) → ℂ)
    (hz : 1 < coordinateSupportCard z) :
    ∃ σ : Equiv.Perm (Fin (n + 2)),
      permuteCoordinates σ z (penultimateCoordinate n) ≠ 0 ∧
      permuteCoordinates σ z (finalCoordinate n) ≠ 0 := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ :=
    Finset.one_lt_card.mp (show 1 < (coordinateSupport z).card from hz)
  have hzi : z i ≠ 0 := by
    simpa [coordinateSupport] using hi
  have hzj : z j ≠ 0 := by
    simpa [coordinateSupport] using hj
  let f : Bool → Fin (n + 2) := fun b ↦ if b then j else i
  let g : Bool → Fin (n + 2) := fun b ↦
    if b then finalCoordinate n else penultimateCoordinate n
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b <;>
      simp_all [f]
  have hg : Function.Injective g := by
    intro a b hab
    cases a <;> cases b <;>
      simp_all [g, penultimateCoordinate_ne_finalCoordinate,
        Ne.symm (penultimateCoordinate_ne_finalCoordinate n)]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hσi : σ i = penultimateCoordinate n := by
    simpa [f, g] using hσ false
  have hσj : σ j = finalCoordinate n := by
    simpa [f, g] using hσ true
  refine ⟨σ, ?_, ?_⟩
  · have hinv : σ.symm (penultimateCoordinate n) = i := by
      rw [← hσi]
      simp
    simpa [permuteCoordinates, hinv] using hzi
  · have hinv : σ.symm (finalCoordinate n) = j := by
      rw [← hσj]
      simp
    simpa [permuteCoordinates, hinv] using hzj

/-- Invariance of a Fourier functional under coordinate permutations. -/
def PermutationInvariant {d : ℕ}
    (Φ : (Fin d → ℂ) → ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin d)) z,
    Φ (permuteCoordinates σ z) = Φ z

/-- Pull two compressed endpoints back through a coordinate permutation.
Support, energy, and the maximum bound are all preserved. -/
theorem pullback_two_endpoints_permutation
    {d : ℕ} (Φ : (Fin d → ℂ) → ℂ)
    (hperm : PermutationInvariant Φ)
    (σ : Equiv.Perm (Fin d)) (z wLeft wRight : Fin d → ℂ)
    (hsuppLeft : coordinateSupportCard wLeft <
      coordinateSupportCard (permuteCoordinates σ z))
    (hsuppRight : coordinateSupportCard wRight <
      coordinateSupportCard (permuteCoordinates σ z))
    (henergyLeft : coordinateEnergy wLeft =
      coordinateEnergy (permuteCoordinates σ z))
    (henergyRight : coordinateEnergy wRight =
      coordinateEnergy (permuteCoordinates σ z))
    (hbound : ‖Φ (permuteCoordinates σ z)‖ ≤
      max ‖Φ wLeft‖ ‖Φ wRight‖) :
    ∃ zLeft zRight : Fin d → ℂ,
      coordinateSupportCard zLeft < coordinateSupportCard z ∧
      coordinateSupportCard zRight < coordinateSupportCard z ∧
      coordinateEnergy zLeft = coordinateEnergy z ∧
      coordinateEnergy zRight = coordinateEnergy z ∧
      ‖Φ z‖ ≤ max ‖Φ zLeft‖ ‖Φ zRight‖ := by
  refine ⟨permuteCoordinates σ.symm wLeft,
    permuteCoordinates σ.symm wRight, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [coordinateSupportCard_permuteCoordinates] using
      (hsuppLeft.trans_eq
        (coordinateSupportCard_permuteCoordinates σ z))
  · simpa only [coordinateSupportCard_permuteCoordinates] using
      (hsuppRight.trans_eq
        (coordinateSupportCard_permuteCoordinates σ z))
  · rw [coordinateEnergy_permuteCoordinates, henergyLeft,
      coordinateEnergy_permuteCoordinates]
  · rw [coordinateEnergy_permuteCoordinates, henergyRight,
      coordinateEnergy_permuteCoordinates]
  · rw [← hperm σ z,
      hperm σ.symm wLeft, hperm σ.symm wRight]
    exact hbound

/-- A last-two analytic compression theorem implies the global two-endpoint
hypothesis consumed by `finite_coordinate_compression_of_two_endpoints`. -/
theorem global_two_endpoints_of_penultimate_final
    {n : ℕ} (Φ : (Fin (n + 2) → ℂ) → ℂ)
    (hperm : PermutationInvariant Φ)
    (hlocal : ∀ w : Fin (n + 2) → ℂ,
      w (penultimateCoordinate n) ≠ 0 →
      w (finalCoordinate n) ≠ 0 →
      ∃ wLeft wRight : Fin (n + 2) → ℂ,
        coordinateSupportCard wLeft < coordinateSupportCard w ∧
        coordinateSupportCard wRight < coordinateSupportCard w ∧
        coordinateEnergy wLeft = coordinateEnergy w ∧
        coordinateEnergy wRight = coordinateEnergy w ∧
        ‖Φ w‖ ≤ max ‖Φ wLeft‖ ‖Φ wRight‖) :
    ∀ z : Fin (n + 2) → ℂ, 1 < coordinateSupportCard z →
      ∃ zLeft zRight : Fin (n + 2) → ℂ,
        coordinateSupportCard zLeft < coordinateSupportCard z ∧
        coordinateSupportCard zRight < coordinateSupportCard z ∧
        coordinateEnergy zLeft = coordinateEnergy z ∧
        coordinateEnergy zRight = coordinateEnergy z ∧
        ‖Φ z‖ ≤ max ‖Φ zLeft‖ ‖Φ zRight‖ := by
  intro z hz
  obtain ⟨σ, hzPen, hzLast⟩ :=
    exists_permutation_nonzero_penultimate_final z hz
  obtain ⟨wLeft, wRight, hsLeft, hsRight, heLeft, heRight, hmax⟩ :=
    hlocal (permuteCoordinates σ z) hzPen hzLast
  exact pullback_two_endpoints_permutation Φ hperm σ z wLeft wRight
    hsLeft hsRight heLeft heRight hmax

end

end LogdetLean.GramHafnian
