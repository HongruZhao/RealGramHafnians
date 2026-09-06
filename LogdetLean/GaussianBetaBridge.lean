import LogdetLean.FixedPastBeta
/-!
# The Gaussian normalized-Gram determinant has the independent Beta-product law

This file closes the sequential argument.  `FixedPastBeta` proves the exact
law of one new factor for every linearly independent fixed past;
`SequentialBeta` proves almost-sure rank, the skew-product independence
induction, telescoping, and the determinant identity.  Combining them leaves
no probabilistic hypotheses in the final theorems.

Exact published source: Rouault (2007), equations (2.4)--(2.7), printed
pp. 185--186, and Proposition 2.1(2), printed p. 187.  Detailed proof route
followed: Rouault (2005), Section 2.1, equations (4)--(10) and the proof of
Proposition 2.1, printed pp. 4--6.  Rouault describes the result as classical;
this project claims a Lean formalization, not discovery of the Beta-product
law.  See `PROVENANCE.md` for historical credit and the parameter dictionary.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The successive normalized-Gram determinant ratios of `p≤m` independent
standard Gaussian columns have the iterated product law consisting of a first
point mass at one followed by independent Beta factors.  At stage `n=j-1≥1`
the factor is
`Beta((m-j+1)/2,(j-1)/2)`. -/
theorem map_gaussianNormalizedGramFactors_eq_betaProduct
    (m p : ℕ) (hdim : finrank ℝ E = m) (hp : p ≤ m) :
    Measure.map
        (sequentialStatistic (nestedNormalizedGramFactor (E := E)) p)
        (nestedProductMeasure (stdGaussian E) p) =
      nestedProductMeasureFamily (gaussianGramSchmidtFactorMeasure m) p := by
  exact map_sequentialNormalizedGramFactors_eq_betaProduct_of_fixedPast
    m p hdim hp fun n past hpast hnm ↦
      map_nestedNormalizedGramFactor_stdGaussian_fixedPast
        m n hdim past hpast hnm

/-- Scalar form of the Gaussian Beta-product identity: the pushforward law of
the normalized Gram determinant is multiplication applied to the independent
factor-product measure. -/
theorem map_gaussianNormalizedGramDet_eq_map_product_betaFactors
    (m p : ℕ) (hdim : finrank ℝ E = m) (hp : p ≤ m) :
    Measure.map (nestedNormalizedGramDet (E := E) p)
        (nestedProductMeasure (stdGaussian E) p) =
      Measure.map (nestedRealProduct p)
        (nestedProductMeasureFamily (gaussianGramSchmidtFactorMeasure m) p) := by
  exact map_nestedNormalizedGramDet_eq_map_product_betaFactors
    m p hdim hp fun n past hpast hnm ↦
      map_nestedNormalizedGramFactor_stdGaussian_fixedPast
        m n hdim past hpast hnm

/-- `HasLaw` formulation of the scalar determinant theorem. -/
theorem hasLaw_gaussianNormalizedGramDet_betaProduct
    (m p : ℕ) (hdim : finrank ℝ E = m) (hp : p ≤ m) :
    HasLaw (nestedNormalizedGramDet (E := E) p)
      (Measure.map (nestedRealProduct p)
        (nestedProductMeasureFamily (gaussianGramSchmidtFactorMeasure m) p))
      (nestedProductMeasure (stdGaussian E) p) := by
  refine ⟨?_, map_gaussianNormalizedGramDet_eq_map_product_betaFactors
    m p hdim hp⟩
  change AEMeasurable
    (fun z : NestedTuple E p ↦ (normalizedGram (nestedTupleToFin p z)).det)
    (nestedProductMeasure (stdGaussian E) p)
  exact ((measurable_det_normalizedGram (E := E) p).comp
    (measurable_nestedTupleToFin (α := E) p)).aemeasurable

end

end LogdetLean
