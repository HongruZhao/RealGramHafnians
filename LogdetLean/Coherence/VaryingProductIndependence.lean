import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic
/-!
# Mixing conditional product laws with a fixed second factor

If, for every value of a base variable, a fresh random input produces a
pair whose first marginal may depend on the base but whose second marginal
is fixed and independent, then the base together with the first output is
independent of the second output after mixing over the base.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {A B D S : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace D] [MeasurableSpace S]

/-- A varying conditional first factor and a fixed conditional second factor
remain a product after mixing over the base measure. -/
theorem map_baseFirst_second_eq_prod_of_conditional_products
    (mu : Measure A) (nu : Measure B) (tau : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure tau]
    (d : A → B → D) (s : A → B → S)
    (hd : Measurable (Function.uncurry d))
    (hs : Measurable (Function.uncurry s))
    (hlaw : ∀ᵐ a ∂mu,
      Measure.map (fun b ↦ (d a b, s a b)) nu =
        (Measure.map (d a) nu).prod tau) :
    Measure.map
        (fun p : A × B ↦ ((p.1, d p.1 p.2), s p.1 p.2))
        (mu.prod nu) =
      (Measure.map (fun p : A × B ↦ (p.1, d p.1 p.2))
        (mu.prod nu)).prod tau := by
  let joint : A × B → (A × D) × S :=
    fun p ↦ ((p.1, d p.1 p.2), s p.1 p.2)
  let orient : A × B → A × D :=
    fun p ↦ (p.1, d p.1 p.2)
  have hjoint : Measurable joint := by
    exact (measurable_fst.prodMk hd).prodMk hs
  have horient : Measurable orient := by
    exact measurable_fst.prodMk hd
  change Measure.map joint (mu.prod nu) = (Measure.map orient (mu.prod nu)).prod tau
  symm
  refine Measure.prod_eq (μ := Measure.map orient (mu.prod nu))
    (ν := tau) (μν := Measure.map joint (mu.prod nu)) fun U V hU hV ↦ ?_
  rw [Measure.map_apply hjoint (hU.prod hV)]
  rw [Measure.map_apply horient hU]
  rw [Measure.prod_apply (hjoint (hU.prod hV))]
  rw [Measure.prod_apply (horient hU)]
  have hpoint : ∀ᵐ a ∂mu,
      nu (Prod.mk a ⁻¹' (joint ⁻¹' (U ×ˢ V))) =
        nu (Prod.mk a ⁻¹' (orient ⁻¹' U)) * tau V := by
    filter_upwards [hlaw] with a ha
    let Ua : Set D := Prod.mk a ⁻¹' U
    have hUa : MeasurableSet Ua := measurable_prodMk_left hU
    have h := congrArg (fun M : Measure (D × S) ↦ M (Ua ×ˢ V)) ha
    rw [Measure.map_apply (hd.of_uncurry_left.prodMk hs.of_uncurry_left)
        (hUa.prod hV), Measure.prod_prod,
      Measure.map_apply hd.of_uncurry_left hUa] at h
    have hsetJoint :
        Prod.mk a ⁻¹' (joint ⁻¹' (U ×ˢ V)) =
          (fun b ↦ (d a b, s a b)) ⁻¹' (Ua ×ˢ V) := by
      ext b
      simp [joint, Ua]
    have hsetOrient :
        Prod.mk a ⁻¹' (orient ⁻¹' U) = d a ⁻¹' Ua := by
      ext b
      simp [orient, Ua]
    rw [hsetJoint, hsetOrient]
    exact h
  rw [lintegral_congr_ae hpoint, lintegral_mul_const]
  exact measurable_measure_prodMk_left (horient hU)

/-- Independence formulation of the same conditional-mixture theorem. -/
theorem indepFun_baseFirst_second_of_conditional_products
    (mu : Measure A) (nu : Measure B) (tau : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure tau]
    (d : A → B → D) (s : A → B → S)
    (hd : Measurable (Function.uncurry d))
    (hs : Measurable (Function.uncurry s))
    (hlaw : ∀ᵐ a ∂mu,
      Measure.map (fun b ↦ (d a b, s a b)) nu =
        (Measure.map (d a) nu).prod tau) :
    IndepFun (fun p : A × B ↦ (p.1, d p.1 p.2))
      (fun p : A × B ↦ s p.1 p.2) (mu.prod nu) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_fst.prodMk hd).aemeasurable hs.aemeasurable).2
  change Measure.map
      (fun p : A × B ↦ ((p.1, d p.1 p.2), s p.1 p.2)) (mu.prod nu) =
    (Measure.map (fun p : A × B ↦ (p.1, d p.1 p.2)) (mu.prod nu)).prod
      (Measure.map (fun p : A × B ↦ s p.1 p.2) (mu.prod nu))
  rw [map_baseFirst_second_eq_prod_of_conditional_products
    mu nu tau d s hd hs hlaw]
  congr 1
  have hsecond :
      Measure.map (fun p : A × B ↦ s p.1 p.2) (mu.prod nu) = tau := by
    apply Measure.ext
    intro V hV
    have hs' : Measurable (fun p : A × B ↦ s p.1 p.2) := hs
    rw [Measure.map_apply hs' hV, Measure.prod_apply (hs' hV)]
    have hpoint : ∀ᵐ a ∂mu, nu (s a ⁻¹' V) = tau V := by
      filter_upwards [hlaw] with a ha
      have h := congrArg (fun M : Measure (D × S) ↦ M (univ ×ˢ V)) ha
      rw [Measure.map_apply (hd.of_uncurry_left.prodMk hs.of_uncurry_left)
          (MeasurableSet.univ.prod hV), Measure.prod_prod,
        Measure.map_apply hd.of_uncurry_left MeasurableSet.univ] at h
      have hset :
          (fun b ↦ (d a b, s a b)) ⁻¹' (univ ×ˢ V) = s a ⁻¹' V := by
        ext b
        simp
      rw [hset] at h
      simpa using h
    have hsection : ∀ a : A,
        Prod.mk a ⁻¹' ((fun p : A × B ↦ s p.1 p.2) ⁻¹' V) =
          s a ⁻¹' V := by
      intro a
      ext b
      rfl
    simp_rw [hsection]
    rw [lintegral_congr_ae hpoint, lintegral_const, measure_univ, mul_one]
  exact hsecond.symm

/-- Independence transports backward through a measurable map with the
specified pushforward law. -/
theorem indepFun_comp_of_map_eq
    {Omega X Y Z : Type*}
    [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {nu : Measure X} [IsProbabilityMeasure nu]
    {F : Omega → X} {Afun : X → Y} {Bfun : X → Z}
    (hAB : IndepFun Afun Bfun nu)
    (hF : Measurable F) (hA : Measurable Afun) (hB : Measurable Bfun)
    (hmap : Measure.map F mu = nu) :
    IndepFun (Afun ∘ F) (Bfun ∘ F) mu := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hA.comp hF).aemeasurable (hB.comp hF).aemeasurable).2
  calc
    Measure.map (fun w ↦ ((Afun ∘ F) w, (Bfun ∘ F) w)) mu =
        Measure.map (fun x ↦ (Afun x, Bfun x)) (Measure.map F mu) := by
      rw [Measure.map_map (hA.prodMk hB) hF]
      rfl
    _ = Measure.map (fun x ↦ (Afun x, Bfun x)) nu := by rw [hmap]
    _ = (Measure.map Afun nu).prod (Measure.map Bfun nu) :=
      hAB.map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable
    _ = (Measure.map Afun (Measure.map F mu)).prod
        (Measure.map Bfun (Measure.map F mu)) := by rw [hmap]
    _ = (Measure.map (Afun ∘ F) mu).prod
        (Measure.map (Bfun ∘ F) mu) := by
      rw [Measure.map_map hA hF, Measure.map_map hB hF]

/-- If `X` and `Y` are independent and the pair `(X,Y)` is independent of
`Z`, then `X` is independent of the pair `(Y,Z)`. -/
theorem IndepFun.left_pair_of_pair_left
    {Omega X Y Z : Type*}
    [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {Xfun : Omega → X} {Yfun : Omega → Y} {Zfun : Omega → Z}
    (hXY : IndepFun Xfun Yfun mu)
    (hXYZ : IndepFun (fun w ↦ (Xfun w, Yfun w)) Zfun mu)
    (hX : Measurable Xfun) (hY : Measurable Yfun) (hZ : Measurable Zfun) :
    IndepFun Xfun (fun w ↦ (Yfun w, Zfun w)) mu := by
  have hYZ : IndepFun Yfun Zfun mu :=
    hXYZ.comp measurable_snd measurable_id
  apply (indepFun_iff_map_prod_eq_prod_map_map
    hX.aemeasurable (hY.prodMk hZ).aemeasurable).2
  have hmapXYZ := hXYZ.map_prod_eq_prod_map_map
    (hX.prodMk hY).aemeasurable hZ.aemeasurable
  have hmapXY := hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hmapYZ := hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable
  calc
    Measure.map (fun w ↦ (Xfun w, (Yfun w, Zfun w))) mu =
        Measure.map MeasurableEquiv.prodAssoc
          (Measure.map (fun w ↦ ((Xfun w, Yfun w), Zfun w)) mu) := by
      rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
        ((hX.prodMk hY).prodMk hZ)]
      rfl
    _ = Measure.map MeasurableEquiv.prodAssoc
        ((Measure.map (fun w ↦ (Xfun w, Yfun w)) mu).prod
          (Measure.map Zfun mu)) := by rw [hmapXYZ]
    _ = (Measure.map Xfun mu).prod
        ((Measure.map Yfun mu).prod (Measure.map Zfun mu)) := by
      rw [hmapXY, Measure.prodAssoc_prod]
    _ = (Measure.map Xfun mu).prod
        (Measure.map (fun w ↦ (Yfun w, Zfun w)) mu) := by rw [hmapYZ]

end

end LogdetLean.Coherence
