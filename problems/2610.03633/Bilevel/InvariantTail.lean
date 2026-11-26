import Bilevel.InvariantConcentration

/-! Concentration from actual invariance and almost-everywhere orbit bounds. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Bilevel.InvariantTail

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace X]
  [MulAction G X] [MeasurableSMul₂ G X]
  (ν : Measure G) [IsProbabilityMeasure ν]
  (μ : Measure X) [IsProbabilityMeasure μ]

include ν in
theorem event_bound
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (bad : Set X) (hbad : MeasurableSet bad) (c : ℝ≥0∞)
    (horbit : ∀ᵐ x ∂μ, ν {g : G | g • x ∈ bad} ≤ c) : μ bad ≤ c := by
  let f : X → ℝ≥0∞ := bad.indicator 1
  have hf : Measurable f := measurable_const.indicator hbad
  have hi := InvariantAdaptation.lintegral_action_average ν μ hp f hf
  have hj : (∫⁻ g, ∫⁻ x, f (g • x) ∂μ ∂ν) = ∫⁻ x, ∫⁻ g, f (g • x) ∂ν ∂μ :=
    lintegral_lintegral_swap (hf.comp (measurable_fst.smul measurable_snd)).aemeasurable
  have hbound : (∫⁻ x, ∫⁻ g, f (g • x) ∂ν ∂μ) ≤ c := by
    calc
      _ ≤ ∫⁻ _x, c ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [horbit] with x hx
        have he : (fun g : G => f (g • x)) = {g : G | g • x ∈ bad}.indicator 1 := by
          funext g
          by_cases h : g • x ∈ bad <;> simp [f,h]
        have hm : Measurable (fun g : G => g • x) := measurable_id.smul measurable_const
        have hs : MeasurableSet {g : G | g • x ∈ bad} := hm hbad
        rw [he]
        change (∫⁻ g, {g : G | g • x ∈ bad}.indicator 1 g ∂ν) ≤ c
        rw [lintegral_indicator_one hs]
        exact hx
      _ = c := by simp
  rw [← hj, hi] at hbound
  simpa only [f, lintegral_indicator_one hbad] using hbound

include ν in
theorem real_event_bound
    (hp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (bad : Set X) (hbad : MeasurableSet bad) (c : ℝ) (hc : 0 ≤ c)
    (horbit : ∀ᵐ x ∂μ, ν.real {g : G | g • x ∈ bad} ≤ c) : μ.real bad ≤ c := by
  have he : ∀ᵐ x ∂μ, ν {g : G | g • x ∈ bad} ≤ ENNReal.ofReal c := by
    filter_upwards [horbit] with x hx
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.ofReal_le_ofReal hx
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (event_bound ν μ hp bad hbad _ he)
  simpa only [Measure.real, ENNReal.toReal_ofReal hc] using h

end Bilevel.InvariantTail
