import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Topology.Order.Basic
/-!
# From bivariate lower rectangle probabilities to weak convergence

This file supplies the convergence determining class argument needed to pass
from convergence of every bivariate distribution function to weak convergence
of the corresponding probability measures.  The proof uses bounded rectangles
of the form `(a, b] x (c, d]`, inclusion and exclusion, and Mathlib's
pi system form of the Portmanteau theorem.
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The family of nonempty real intervals of the form `(a, b]`. -/
def realIocSystem : Set (Set ℝ) :=
  {s | ∃ a b : ℝ, a < b ∧ Ioc a b = s}

/-- The family of nonempty bounded rectangles `(a, b] x (c, d]`. -/
def realIocRectangleSystem : Set (Set (ℝ × ℝ)) :=
  Set.image2 (· ×ˢ ·) realIocSystem realIocSystem

theorem isPiSystem_realIocSystem : IsPiSystem realIocSystem := by
  simpa [realIocSystem] using
    (isPiSystem_Ioc (fun x : ℝ ↦ x) (fun x : ℝ ↦ x))

theorem isPiSystem_realIocRectangleSystem :
    IsPiSystem realIocRectangleSystem := by
  exact isPiSystem_realIocSystem.prod isPiSystem_realIocSystem

theorem measurableSet_of_mem_realIocRectangleSystem
    {s : Set (ℝ × ℝ)} (hs : s ∈ realIocRectangleSystem) :
    MeasurableSet s := by
  rcases hs with ⟨u, ⟨a, b, hab, rfl⟩, v, ⟨c, d, hcd, rfl⟩, rfl⟩
  exact measurableSet_Ioc.prod measurableSet_Ioc

/-- Bounded half open rectangles give arbitrarily small neighborhoods in
`R x R`.  This is the topological input to the convergence determining class
argument. -/
theorem exists_realIocRectangle_mem_nhds_subset
    (u : Set (ℝ × ℝ)) (hu : IsOpen u) (x : ℝ × ℝ) (hx : x ∈ u) :
    ∃ s ∈ realIocRectangleSystem, s ∈ nhds x ∧ s ⊆ u := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hprod⟩ :=
    mem_nhds_prod_iff.mp (hu.mem_nhds hx)
  obtain ⟨a, b, hxab, hIcc₁, hsub₁⟩ :=
    exists_Icc_mem_subset_of_mem_nhds hu₁
  obtain ⟨c, d, hxcd, hIcc₂, hsub₂⟩ :=
    exists_Icc_mem_subset_of_mem_nhds hu₂
  have hab : a < x.1 ∧ x.1 < b := Icc_mem_nhds_iff.mp hIcc₁
  have hcd : c < x.2 ∧ x.2 < d := Icc_mem_nhds_iff.mp hIcc₂
  refine ⟨Ioc a b ×ˢ Ioc c d, ?_, ?_, ?_⟩
  · exact ⟨Ioc a b, ⟨a, b, hab.1.trans hab.2, rfl⟩,
      Ioc c d, ⟨c, d, hcd.1.trans hcd.2, rfl⟩, rfl⟩
  · exact prod_mem_nhds (Ioc_mem_nhds hab.1 hab.2)
      (Ioc_mem_nhds hcd.1 hcd.2)
  · exact (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self).trans
      ((Set.prod_mono hsub₁ hsub₂).trans hprod)

/-- Inclusion and exclusion for one bounded half open rectangle, written in
terms of the four lower left rectangle probabilities. -/
theorem measureReal_Ioc_prod_Ioc
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    μ.real (Ioc a b ×ˢ Ioc c d) =
      (μ.real (Iic b ×ˢ Iic d) - μ.real (Iic a ×ˢ Iic d)) -
        (μ.real (Iic b ×ˢ Iic c) - μ.real (Iic a ×ˢ Iic c)) := by
  have houter₁ : Iic a ×ˢ Iic d ⊆ Iic b ×ˢ Iic d :=
    Set.prod_mono (Iic_subset_Iic.mpr hab) Subset.rfl
  have houter₂ : Iic a ×ˢ Iic c ⊆ Iic b ×ˢ Iic c :=
    Set.prod_mono (Iic_subset_Iic.mpr hab) Subset.rfl
  have hvertical : Ioc a b ×ˢ Iic c ⊆ Ioc a b ×ˢ Iic d :=
    Set.prod_mono Subset.rfl (Iic_subset_Iic.mpr hcd)
  have h₁ : (Iic b ×ˢ Iic d) \ (Iic a ×ˢ Iic d) = Ioc a b ×ˢ Iic d := by
    ext y
    change ((y.1 ≤ b ∧ y.2 ≤ d) ∧ ¬ (y.1 ≤ a ∧ y.2 ≤ d)) ↔
      ((a < y.1 ∧ y.1 ≤ b) ∧ y.2 ≤ d)
    constructor
    · rintro ⟨⟨hyb, hyd⟩, hnot⟩
      exact ⟨⟨lt_of_not_ge (fun hya ↦ hnot ⟨hya, hyd⟩), hyb⟩, hyd⟩
    · rintro ⟨⟨hya, hyb⟩, hyd⟩
      exact ⟨⟨hyb, hyd⟩, fun ha ↦ (not_le_of_gt hya) ha.1⟩
  have h₂ : (Iic b ×ˢ Iic c) \ (Iic a ×ˢ Iic c) = Ioc a b ×ˢ Iic c := by
    ext y
    change ((y.1 ≤ b ∧ y.2 ≤ c) ∧ ¬ (y.1 ≤ a ∧ y.2 ≤ c)) ↔
      ((a < y.1 ∧ y.1 ≤ b) ∧ y.2 ≤ c)
    constructor
    · rintro ⟨⟨hyb, hyc⟩, hnot⟩
      exact ⟨⟨lt_of_not_ge (fun hya ↦ hnot ⟨hya, hyc⟩), hyb⟩, hyc⟩
    · rintro ⟨⟨hya, hyb⟩, hyc⟩
      exact ⟨⟨hyb, hyc⟩, fun ha ↦ (not_le_of_gt hya) ha.1⟩
  have h₃ : (Ioc a b ×ˢ Iic d) \ (Ioc a b ×ˢ Iic c) =
      Ioc a b ×ˢ Ioc c d := by
    ext y
    change (((a < y.1 ∧ y.1 ≤ b) ∧ y.2 ≤ d) ∧
      ¬ ((a < y.1 ∧ y.1 ≤ b) ∧ y.2 ≤ c)) ↔
      ((a < y.1 ∧ y.1 ≤ b) ∧ c < y.2 ∧ y.2 ≤ d)
    constructor
    · rintro ⟨⟨hab', hyd⟩, hnot⟩
      exact ⟨hab', lt_of_not_ge (fun hyc ↦ hnot ⟨hab', hyc⟩), hyd⟩
    · rintro ⟨hab', hyc, hyd⟩
      exact ⟨⟨hab', hyd⟩, fun h ↦ (not_le_of_gt hyc) h.2⟩
  rw [← h₃, measureReal_sdiff hvertical (measurableSet_Ioc.prod measurableSet_Iic),
    ← h₁, measureReal_sdiff houter₁ (measurableSet_Iic.prod measurableSet_Iic),
    ← h₂, measureReal_sdiff houter₂ (measurableSet_Iic.prod measurableSet_Iic)]

/-- Convergence of every bivariate lower rectangle probability implies weak
convergence of the probability measures.  No continuity or atomlessness
assumption on the limit is needed because convergence is assumed at every
pair of thresholds. -/
theorem tendsto_probabilityMeasure_of_tendsto_lowerLeftRectangle
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → ProbabilityMeasure (ℝ × ℝ)}
    {ν : ProbabilityMeasure (ℝ × ℝ)}
    (h : ∀ z x : ℝ,
      Tendsto
        (fun i ↦ ((μ i : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)).real
          (Iic z ×ˢ Iic x)) l
        (nhds (((ν : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)).real
          (Iic z ×ˢ Iic x)))) :
    Tendsto μ l (nhds ν) := by
  apply isPiSystem_realIocRectangleSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
  · exact fun s hs ↦ measurableSet_of_mem_realIocRectangleSystem hs
  · intro u hu x hx
    exact exists_realIocRectangle_mem_nhds_subset u hu x hx
  · intro s hs
    rcases hs with ⟨u, ⟨a, b, hab, rfl⟩, v, ⟨c, d, hcd, rfl⟩, rfl⟩
    have hbd := h b d
    have had := h a d
    have hbc := h b c
    have hac := h a c
    have hreal : Tendsto
        (fun i ↦ ((μ i : Measure (ℝ × ℝ)).real
          (Ioc a b ×ˢ Ioc c d))) l
        (nhds ((ν : Measure (ℝ × ℝ)).real
          (Ioc a b ×ˢ Ioc c d))) := by
      simpa only [measureReal_Ioc_prod_Ioc _ hab.le hcd.le] using
        (hbd.sub had).sub (hbc.sub hac)
    rw [← NNReal.tendsto_coe]
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using hreal

end

end LogdetLean.Coherence
