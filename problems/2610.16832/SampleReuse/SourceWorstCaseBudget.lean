import SampleReuse.SourceMainLower

open SecondOrder MeasureTheory
open scoped ENNReal

namespace SampleReuse
noncomputable section

/-- A literal uniform stopping budget bounds the actual extended expectation,
including all private seeds and persistent oracle tapes. -/
theorem finiteInstanceCost_le_uniform_budget {M : Parameters} {d : ℕ}
    {H S Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (I : FiniteScalarInstance M d) (N : ℕ)
    (hcap : ∀ ξ tape, (P ξ).extendedCost (finiteInstanceReply I) tape ≤ (N : ℝ≥0∞)) :
    finiteInstanceCost μ P I ≤ (N : ℝ≥0∞) := by
  unfold finiteInstanceCost
  apply (lintegral_mono (μ := μ.prod (iidSampleTapeLaw I.law))
    (fun w : Ξ × (ℕ → I.Sample) => hcap w.1 w.2)).trans_eq
  simp

theorem separateFiniteInstanceCost_le_uniform_budget {M : Parameters} {d : ℕ}
    {H S Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (I : FiniteScalarInstance M d) (N : ℕ)
    (hcap : ∀ ξ tape, (P ξ).extendedCost (separateSampleReply I.sample) tape ≤ (N : ℝ≥0∞)) :
    separateFiniteInstanceCost μ P I ≤ (N : ℝ≥0∞) := by
  unfold separateFiniteInstanceCost
  apply (lintegral_mono (μ := μ.prod (iidSampleTapeLaw I.law))
    (fun w : Ξ × (ℕ → I.Sample) => hcap w.1 w.2)).trans_eq
  simp

theorem separate_expected_lower_implies_worst_case {M : Parameters} {d : ℕ}
    {H S Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S)
    (I : FiniteScalarInstance M d) (N : ℕ) {L : ℝ}
    (hlower : ENNReal.ofReal L ≤ separateFiniteInstanceCost μ P I)
    (hcap : ∀ ξ tape, (P ξ).extendedCost (separateSampleReply I.sample) tape ≤ (N : ℝ≥0∞)) :
    L ≤ (N : ℝ) := by
  have hh := hlower.trans (separateFiniteInstanceCost_le_uniform_budget μ P I N hcap)
  exact_mod_cast (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp hh

theorem fulljet_expected_lower_implies_worst_case {M : Parameters} {d : ℕ}
    {H S Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm (Point d) H (RichReply d) (Point d) S)
    (I : FiniteScalarInstance M d) (N : ℕ) {L : ℝ}
    (hlower : ENNReal.ofReal L ≤ finiteInstanceCost μ P I)
    (hcap : ∀ ξ tape, (P ξ).extendedCost (finiteInstanceReply I) tape ≤ (N : ℝ≥0∞)) :
    L ≤ (N : ℝ) := by
  have hh := hlower.trans (finiteInstanceCost_le_uniform_budget μ P I N hcap)
  exact_mod_cast (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp hh

end
end SampleReuse
