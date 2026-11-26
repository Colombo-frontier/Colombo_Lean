import HeavyTail.AdaptiveSamplerExecution

/-! Adaptive testing lower bound from a local sampler agreement event. The
shared-noise transcript agreement and its probability are both derived. -/

open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel
noncomputable section
universe u

variable {Seed Noise Reply : Type u} {Query Output : Type*}
  [MeasurableSpace Seed] [MeasurableSpace Noise] [MeasurableSpace Reply]
  [MeasurableSpace Query] [MeasurableSpace Output] {T : ℕ}

theorem sampler_pair_testing_lower (A : Policy Seed Query Reply Output T)
    (P : Measure Seed) (ν : Measure Noise) [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {F G : Query × Noise → Reply} (hF : Measurable F) (hG : Measurable G)
    (B : Set Noise) (hFG : ∀ x z, z ∈ B → F (x, z) = G (x, z))
    (decode : History Seed Reply T → Bool) (hd : Measurable decode) (b : Bool) :
    (ν.real B) ^ T ≤
      (A.historyLaw P (kernelOfSampler ν F hF) T).real {h | decode h ≠ b} +
      (A.historyLaw P (kernelOfSampler ν G hG) T).real {h | decode h ≠ !b} := by
  have heF : MeasurableSet {h | decode h ≠ b} := (hd (MeasurableSet.singleton b)).compl
  have heG : MeasurableSet {h | decode h ≠ !b} := (hd (MeasurableSet.singleton (!b))).compl
  rw [← A.sampleHistory_law P ν hF T, ← A.sampleHistory_law P ν hG T]
  rw [map_measureReal_apply (A.sampleHistory_measurable hF T) heF,
    map_measureReal_apply (A.sampleHistory_measurable hG T) heG]
  rw [← goodNoiseHistory_probability P ν B T]
  calc
    _ ≤ (noiseHistoryLaw P ν T).real
        ((A.sampleHistory F T ⁻¹' {h | decode h ≠ b}) ∪
          (A.sampleHistory G T ⁻¹' {h | decode h ≠ !b})) := by
      apply measureReal_mono (μ := noiseHistoryLaw P ν T) _ (measure_ne_top _ _)
      intro ω hω
      have he := A.sampleHistory_noninterference hFG T ω hω
      change decode (A.sampleHistory F T ω) ≠ b ∨ decode (A.sampleHistory G T ω) ≠ !b
      rw [he]
      cases b <;> cases hd' : decode (A.sampleHistory G T ω) <;> simp
    _ ≤ _ := measureReal_union_le _ _

end
end HeavyTail.AdaptiveKernel
