import SecondOrder.LocalReplyOutputLaw

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Read an arbitrary slot array in the actual query enumeration order. -/
def localSlotDraws (V ρ δ : ℝ) (z : LocalReplySlot V ρ δ → Ω) :
    Draws Ω (localQueryCount V ρ δ) :=
  vectorDraws _ (fun i => z ((localReplyEnumeration V ρ δ).symm i))

theorem localSlotDraws_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V ρ δ : ℝ) :
    MeasurePreserving (localSlotDraws V ρ δ) (Measure.pi (fun _ : LocalReplySlot V ρ δ => μ))
      (drawsLaw μ (localQueryCount V ρ δ)) :=
  (vectorDraws_measurePreserving μ _).comp
    (pi_reindex_measurePreserving μ (localReplyEnumeration V ρ δ))

omit [MeasurableSpace Ω] in
theorem localSlotDraws_tape (a₀ : Ω) (V ρ δ : ℝ) (z : LocalReplySlot V ρ δ → Ω)
    (i : LocalReplySlot V ρ δ) :
    drawsTape a₀ _ (localSlotDraws V ρ δ z) (Fintype.equivFin _ i)=z i := by
  rw [←localReplyEnumeration_val,drawsTape_apply]
  simp only [localSlotDraws,drawsVector_vectorDraws,Equiv.symm_apply_apply]

/-- Separate private randomness at each query from the unknown oracle sample. -/
def localPairedPack (V ρ δ : ℝ) (w : LocalDraws (S × Ω) V ρ δ) :
    (LocalReplySlot V ρ δ → S) × Draws Ω (localQueryCount V ρ δ) :=
  ((fun i => (localReplySample w i).1),
    localSlotDraws V ρ δ (fun i => (localReplySample w i).2))

theorem localPairedPack_measurePreserving (η : Measure S) (μ : Measure Ω)
    [IsProbabilityMeasure η] [IsProbabilityMeasure μ] (V ρ δ : ℝ) :
    MeasurePreserving (localPairedPack V ρ δ) (localLaw (η.prod μ) V ρ δ)
      ((Measure.pi (fun _ : LocalReplySlot V ρ δ => η)).prod (drawsLaw μ (localQueryCount V ρ δ))) := by
  have h₁ := localReplySample_measurePreserving (η.prod μ) V ρ δ
  have h₂ := measurePreserving_arrowProdEquivProdArrow S Ω (LocalReplySlot V ρ δ)
    (fun _ => η) (fun _ => μ)
  have h₃ := (MeasurePreserving.id (Measure.pi (fun _ : LocalReplySlot V ρ δ => η))).prod
    (localSlotDraws_measurePreserving μ V ρ δ)
  exact h₃.comp (h₂.comp h₁)

omit [MeasurableSpace Ω] in
theorem localReplyProgram_outputSlots {d : ℕ} (V ρ δ : ℝ)
    (qs : LocalReplySlot V ρ δ → HvpQuery d) (reply : HvpQuery d → Ω → Point d)
    (a₀ : Ω) (z : LocalReplySlot V ρ δ → Ω) :
    OracleProgram.output 0 (OracleProgram.runDraws (.grad 0) reply (localReplyProgram V ρ δ qs)
      (localQueryCount V ρ δ) (localSlotDraws V ρ δ z))=
        localReplyCenter V ρ δ (fun i => reply (qs i) (z i)) := by
  let zs := drawsTape a₀ _ (localSlotDraws V ρ δ z)
  have he := OracleProgram.run_eq_runDraws (HvpQuery.grad (0 : Point d)) reply zs
    (localReplyProgram V ρ δ qs) _ (localSlotDraws V ρ δ z) (drawsTape_apply a₀ _ _)
  have ha := OracleProgram.algorithm_output (HvpQuery.grad (0 : Point d)) 0 0
    (localReplyProgram V ρ δ qs) reply zs (localQueryCount V ρ δ)
  rw [he] at ha
  have hb := localReplyAlgorithm_output V ρ δ qs reply zs
  simp only [zs,localSlotDraws_tape] at hb
  exact ha.symm.trans hb

/-- Randomized query locations use private seeds independent of fresh samples;
the old paired sampling model and the reply-only program have the same law. -/
theorem localReplyProgram_private_outputLaw {d : ℕ} (η : Measure S) (μ : Measure Ω)
    [IsProbabilityMeasure η] [IsProbabilityMeasure μ] (V ρ δ : ℝ)
    (qs : (LocalReplySlot V ρ δ → S) → LocalReplySlot V ρ δ → HvpQuery d)
    (hq : ∀ i, Measurable (fun s => qs s i))
    (reply : HvpQuery d → Ω → Point d)
    (hr : Measurable (fun w : HvpQuery d × Ω => reply w.1 w.2)) (a₀ : Ω) :
    OracleProgram.seededOutputLaw μ (Measure.pi (fun _ : LocalReplySlot V ρ δ => η))
      (.grad 0) 0 reply (fun s => localReplyProgram V ρ δ (qs s)) (localQueryCount V ρ δ)=
      Measure.map (fun w : LocalDraws (S × Ω) V ρ δ => localReplyCenter V ρ δ
        (fun i => reply (qs (fun j => (localReplySample w j).1) i) (localReplySample w i).2))
        (localLaw (η.prod μ) V ρ δ) := by
  have hp := localReplyProgram_measurable V ρ δ qs hq
  have hm := hp.runDrawsOutput 0 a₀ reply hr (localQueryCount V ρ δ)
  have ht := localPairedPack_measurePreserving η μ V ρ δ
  unfold OracleProgram.seededOutputLaw
  rw [←ht.map_eq,Measure.map_map hm ht.measurable]
  apply congrArg (fun g : LocalDraws (S × Ω) V ρ δ → Point d =>
    Measure.map g (localLaw (η.prod μ) V ρ δ))
  funext w
  exact localReplyProgram_outputSlots V ρ δ _ reply a₀ _

end
end SecondOrder
