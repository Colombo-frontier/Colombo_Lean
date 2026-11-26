import SecondOrder.LocalPrivateSeeds
import SecondOrder.BatchTape

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω]

theorem batchTapeProjection_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R m : ℕ) :
    MeasurePreserving (fun w : BatchTape Ω R => w m) (batchTapeLaw μ R)
      (drawsLaw (drawsLaw μ m) R) := by
  refine ⟨measurable_pi_apply m,?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply m) hs,batchTapeLaw_eval μ R m hs]

/-- A fixed private source works for every later choice of batch length. -/
def localPrivateSlots (V ρ δ : ℝ) (u : BatchTape Ω (confidenceRepeats δ)) :
    LocalReplySlot V ρ δ → Ω :=
  localReplySample (u (localBatchSize V ρ))

theorem localPrivateSlots_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V ρ δ : ℝ) :
    MeasurePreserving (localPrivateSlots V ρ δ) (batchTapeLaw μ (confidenceRepeats δ))
      (Measure.pi (fun _ : LocalReplySlot V ρ δ => μ)) :=
  (localReplySample_measurePreserving μ V ρ δ).comp
    (batchTapeProjection_measurePreserving μ (confidenceRepeats δ) (localBatchSize V ρ))

end
end SecondOrder
