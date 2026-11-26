import Bilevel.InvariantAdaptation

/-! Orbit concentration implies concentration after any invariant observation event. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Bilevel.InvariantConcentration

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
  (ν : Measure G) [IsProbabilityMeasure ν]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [MeasurableMul₂ G] [MeasurableSMul₂ G X] [MeasurableSpace G] [IsFiniteMeasure μ] in
theorem restricted_preserving
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (s : Set X) (hs : MeasurableSet s)
    (hinv : ∀ (g : G) (x : X), g • x ∈ s ↔ x ∈ s) (g : G) :
    MeasurePreserving (fun x : X => g • x) (μ.restrict s) (μ.restrict s) := by
  have he : (fun x : X => g • x) ⁻¹' s = s := Set.ext (hinv g)
  refine ⟨(hp g).measurable, ?_⟩
  rw [← he, ← Measure.restrict_map (hp g).measurable hs, (hp g).map_eq]
  rw [he]

include ν in
omit [MeasurableMul₂ G] in
theorem conditional_event_bound
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (s bad : Set X) (hs : MeasurableSet s) (hbad : MeasurableSet bad)
    (hinv : ∀ (g : G) (x : X), g • x ∈ s ↔ x ∈ s)
    (c : ℝ≥0∞) (horbit : ∀ x : X, ν {g : G | g • x ∈ bad} ≤ c) :
    μ (bad ∩ s) ≤ c * μ s := by
  let f : X → ℝ≥0∞ := bad.indicator 1
  have hf : Measurable f := measurable_const.indicator hbad
  have hp' := restricted_preserving μ hp s hs hinv
  have hi := InvariantAdaptation.lintegral_action_average ν (μ.restrict s) hp' f hf
  have hj : (∫⁻ g, ∫⁻ x, f (g • x) ∂μ.restrict s ∂ν) =
      ∫⁻ x, ∫⁻ g, f (g • x) ∂ν ∂μ.restrict s :=
    lintegral_lintegral_swap (hf.comp (measurable_fst.smul measurable_snd)).aemeasurable
  have hbound : (∫⁻ x, ∫⁻ g, f (g • x) ∂ν ∂μ.restrict s) ≤ c * μ s := by
    calc
      _ ≤ ∫⁻ _x, c ∂μ.restrict s := by
        apply lintegral_mono
        intro x
        change (∫⁻ g, f (g • x) ∂ν) ≤ c
        have he : (fun g : G => f (g • x)) = {g : G | g • x ∈ bad}.indicator 1 := by
          funext g
          by_cases h : g • x ∈ bad <;> simp [f, h]
        have hm : Measurable (fun g : G => g • x) := measurable_id.smul measurable_const
        rw [he]
        have hset : MeasurableSet {g : G | g • x ∈ bad} := hm hbad
        change (∫⁻ g, {g : G | g • x ∈ bad}.indicator 1 g ∂ν) ≤ c
        rw [lintegral_indicator_one hset]
        exact horbit x
      _ = c * μ s := by simp
  rw [← hj, hi] at hbound
  simpa only [f, lintegral_indicator_one hbad, Measure.restrict_apply hbad] using hbound

end Bilevel.InvariantConcentration
