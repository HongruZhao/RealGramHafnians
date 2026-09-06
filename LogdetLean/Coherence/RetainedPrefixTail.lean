import LogdetLean.SequentialBeta
/-!
# A retained-prefix version of the sequential product-law theorem

`LogdetLean.SequentialBeta` proves that sequential statistics with a
past-independent one-step law have an independent product law.  For the
coherence problem one needs a slightly stronger, but still finite-horizon,
formulation: keep the first `q` observations themselves and retain only the
statistics produced by the later observations.

The theorem below proves exactly that product law.  Its proof is the same
skew-product induction as the original theorem, except that the induction
starts from the identity map on the first `q` observations.  No regular
conditional probability is used.
-/

namespace LogdetLean.Coherence

noncomputable section

open MeasureTheory ProbabilityTheory

universe u

/-- A right-nested tuple of tail statistics whose base is the retained prefix
of `q` original observations. -/
abbrev RetainedPrefixTailTuple (α : Type u) (β : Type u) (q : ℕ) :
    ℕ → Type u
  | 0 => NestedTuple α q
  | r + 1 => RetainedPrefixTailTuple α β q r × β

/-- Product measurable structure on a retained-prefix/tail tuple. -/
instance instMeasurableSpaceRetainedPrefixTailTuple
    {α : Type u} {β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (q : ℕ) : (r : ℕ) → MeasurableSpace (RetainedPrefixTailTuple α β q r)
  | 0 => instMeasurableSpaceNestedTuple q
  | r + 1 => @Prod.instMeasurableSpace
      (RetainedPrefixTailTuple α β q r) β
      (instMeasurableSpaceRetainedPrefixTailTuple q r) inferInstance

/-- The measure consisting of the original `q`-observation prefix followed
by independent tail coordinates with laws `ν q, ν (q+1), ...`. -/
def retainedPrefixTailProductMeasure
    {α : Type u} {β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : ℕ → Measure β) (q : ℕ) :
    (r : ℕ) → Measure (RetainedPrefixTailTuple α β q r)
  | 0 => nestedProductMeasure μ q
  | r + 1 => (retainedPrefixTailProductMeasure μ ν q r).prod (ν (q + r))

instance retainedPrefixTailProductMeasure_sFinite
    {α : Type u} {β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : ℕ → Measure β)
    [hν : ∀ n, SFinite (ν n)] (q r : ℕ) :
    SFinite (retainedPrefixTailProductMeasure μ ν q r) := by
  induction r with
  | zero =>
      simp only [retainedPrefixTailProductMeasure]
      infer_instance
  | succ r ih =>
      let _ : SFinite (retainedPrefixTailProductMeasure μ ν q r) := ih
      let _ : SFinite (ν (q + r)) := hν (q + r)
      simp only [retainedPrefixTailProductMeasure]
      infer_instance

/-- Start after `q` observations, retain that prefix, and append each later
stage statistic. -/
def retainedPrefixTailStatistic
    {α : Type u} {β : Type u}
    (g : ∀ n, NestedTuple α n → α → β) (q : ℕ) :
    ∀ r, NestedTuple α (q + r) → RetainedPrefixTailTuple α β q r
  | 0, z => z
  | r + 1, z =>
      (retainedPrefixTailStatistic g q r z.1, g (q + r) z.1 z.2)

/-- Joint measurability of the one-step statistic implies measurability of
the retained-prefix/tail map at every finite horizon. -/
theorem measurable_retainedPrefixTailStatistic
    {α : Type u} {β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (g : ∀ n, NestedTuple α n → α → β)
    (hg : ∀ n, Measurable (Function.uncurry (g n))) (q : ℕ) :
    ∀ r, Measurable (retainedPrefixTailStatistic g q r) := by
  intro r
  induction r with
  | zero => exact measurable_id
  | succ r ih =>
      exact (ih.comp measurable_fst).prodMk (hg (q + r))

/-- **Retained-prefix sequential product law.**  If each tail statistic has
a fixed one-step law for almost every full past, then the first `q`
observations have their original product law and are jointly independent of
all `r` tail statistics, which are themselves mutually independent.

Only the stages used before the finite horizon are assumed. -/
theorem measurePreserving_retainedPrefixTailStatistic_of_lt
    {α : Type u} {β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : ℕ → Measure β)
    [∀ n, SFinite (ν n)]
    (g : ∀ n, NestedTuple α n → α → β)
    (hg : ∀ n, Measurable (Function.uncurry (g n))) (q : ℕ) :
    ∀ r : ℕ,
      (∀ s, s < r → ∀ᵐ past ∂nestedProductMeasure μ (q + s),
        Measure.map (g (q + s) past) μ = ν (q + s)) →
      MeasurePreserving (retainedPrefixTailStatistic g q r)
        (nestedProductMeasure μ (q + r))
        (retainedPrefixTailProductMeasure μ ν q r) := by
  intro r
  induction r with
  | zero =>
      intro hlaw
      change MeasurePreserving id
        (nestedProductMeasure μ q) (nestedProductMeasure μ q)
      exact MeasurePreserving.id (nestedProductMeasure μ q)
  | succ r ih =>
      intro hlaw
      have hpast := ih (fun s hs => hlaw s (Nat.lt_succ_of_lt hs))
      change MeasurePreserving
        (fun z : NestedTuple α (q + r) × α =>
          (retainedPrefixTailStatistic g q r z.1,
            g (q + r) z.1 z.2))
        ((nestedProductMeasure μ (q + r)).prod μ)
        ((retainedPrefixTailProductMeasure μ ν q r).prod (ν (q + r)))
      exact hpast.skew_product (hg (q + r))
        (hlaw r (Nat.lt_add_one r))

/-- Pushforward form of
`measurePreserving_retainedPrefixTailStatistic_of_lt`. -/
theorem map_retainedPrefixTailStatistic_eq_product_of_lt
    {α : Type u} {β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : ℕ → Measure β)
    [∀ n, SFinite (ν n)]
    (g : ∀ n, NestedTuple α n → α → β)
    (hg : ∀ n, Measurable (Function.uncurry (g n)))
    (q r : ℕ)
    (hlaw : ∀ s, s < r → ∀ᵐ past ∂nestedProductMeasure μ (q + s),
      Measure.map (g (q + s) past) μ = ν (q + s)) :
    Measure.map (retainedPrefixTailStatistic g q r)
        (nestedProductMeasure μ (q + r)) =
      retainedPrefixTailProductMeasure μ ν q r :=
  (measurePreserving_retainedPrefixTailStatistic_of_lt
    μ ν g hg q r hlaw).map_eq

end

end LogdetLean.Coherence
