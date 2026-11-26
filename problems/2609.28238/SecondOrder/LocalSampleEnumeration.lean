import SecondOrder.FiniteDrawsLaw
import SecondOrder.LocalReplyPrograms

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω]

theorem nestedDrawsSlots_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ] (m R : ℕ) :
    MeasurePreserving (fun w : Draws (Draws Ω m) R => fun i : Fin R × Fin m =>
      drawsVector id m (drawsVector id R w i.1) i.2)
      (drawsLaw (drawsLaw μ m) R) (Measure.pi (fun _ : Fin R × Fin m => μ)) := by
  have h₁ := drawsMap_measurePreserving (drawsVector_measurePreserving μ m) R
  have h₂ := drawsVector_measurePreserving (Measure.pi (fun _ : Fin m => μ)) R
  have h₃ := pi_uncurry_measurePreserving (I := Fin R) (J := Fin m) μ
  convert h₃.comp (h₂.comp h₁) using 1
  funext w i
  simp only [Function.comp_apply,drawsVector_drawsMap]

theorem localReplySample_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ] (V ρ δ : ℝ) :
    MeasurePreserving (@localReplySample Ω V ρ δ) (localLaw μ V ρ δ)
      (Measure.pi (fun _ : LocalReplySlot V ρ δ => μ)) :=
  nestedDrawsSlots_measurePreserving μ (localBatchSize V ρ) (confidenceRepeats δ)

def localReplyEnumeration (V ρ δ : ℝ) : LocalReplySlot V ρ δ ≃ Fin (localQueryCount V ρ δ) :=
  (Fintype.equivFin _).trans (finCongr (localReplySlot_count V ρ δ))

theorem localReplyEnumeration_val (V ρ δ : ℝ) (i : LocalReplySlot V ρ δ) :
    (localReplyEnumeration V ρ δ i : ℕ)=(Fintype.equivFin _ i : ℕ) := rfl

def localEnumeratedDraws (V ρ δ : ℝ) (w : LocalDraws Ω V ρ δ) : Draws Ω (localQueryCount V ρ δ) :=
  vectorDraws _ (fun i => localReplySample w ((localReplyEnumeration V ρ δ).symm i))

/-- The original nested robust-estimator batches, read in the program's
actual slot order, have precisely the ordinary sequential sample law. -/
theorem localEnumeratedDraws_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ] (V ρ δ : ℝ) :
    MeasurePreserving (localEnumeratedDraws V ρ δ) (localLaw μ V ρ δ)
      (drawsLaw μ (localQueryCount V ρ δ)) := by
  have h₁ := localReplySample_measurePreserving μ V ρ δ
  have h₂ := pi_reindex_measurePreserving μ (localReplyEnumeration V ρ δ)
  exact (vectorDraws_measurePreserving μ _).comp (h₂.comp h₁)

omit [MeasurableSpace Ω] in
theorem localEnumeratedDraws_sample (V ρ δ : ℝ) (w : LocalDraws Ω V ρ δ)
    (i : LocalReplySlot V ρ δ) :
    drawsVector id _ (localEnumeratedDraws V ρ δ w) (localReplyEnumeration V ρ δ i)=localReplySample w i := by
  simp only [localEnumeratedDraws,drawsVector_vectorDraws,Equiv.symm_apply_apply]

def drawsTape (a₀ : Ω) (n : ℕ) (w : Draws Ω n) : ℕ → Ω :=
  finiteHistoryTape a₀ n (drawsHistory n w)

omit [MeasurableSpace Ω] in
theorem drawsTape_apply (a₀ : Ω) (n : ℕ) (w : Draws Ω n) (i : Fin n) :
    drawsTape a₀ n w i=drawsVector id n w i := by
  exact (finiteHistoryTape_historyDraws a₀ n (drawsHistory n w) i).trans
    (congrArg (fun u => drawsVector id n u i) (historyDraws_drawsHistory n w))

omit [MeasurableSpace Ω] in
theorem localEnumeratedDraws_tape (a₀ : Ω) (V ρ δ : ℝ) (w : LocalDraws Ω V ρ δ)
    (i : LocalReplySlot V ρ δ) :
    drawsTape a₀ _ (localEnumeratedDraws V ρ δ w) (Fintype.equivFin _ i)=localReplySample w i := by
  rw [←localReplyEnumeration_val,drawsTape_apply,localEnumeratedDraws_sample]

end
end SecondOrder
