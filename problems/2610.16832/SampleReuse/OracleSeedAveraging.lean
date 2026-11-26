import SampleReuse.OracleFreshness

/-! Averaging a uniform fixed-seed or fixed-external-tape confidence bound.
The external parameter may contain the other estimator's entire independent
tape and private random bits. No trajectory-conditional independence is used. -/

open MeasureTheory
open scoped ENNReal

namespace SampleReuse
noncomputable section

theorem product_event_bound_of_sections {S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (bad : Set (S × Ω)) (hm : MeasurableSet bad) (δ : ℝ≥0∞)
    (hsections : ∀ s, μ {z | (s, z) ∈ bad} ≤ δ) :
    (ν.prod μ) bad ≤ δ := by
  rw [Measure.prod_apply hm]
  exact (lintegral_mono hsections).trans_eq (by simp)

theorem product_event_real_bound_of_sections {S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (bad : Set (S × Ω)) (hm : MeasurableSet bad) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsections : ∀ s, μ.real {z | (s, z) ∈ bad} ≤ δ) :
    (ν.prod μ).real bad ≤ δ := by
  have hb := product_event_bound_of_sections ν μ bad hm (ENNReal.ofReal δ) (fun s => by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hsections s))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hδ)

end
end SampleReuse
