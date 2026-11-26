import SecondOrder.PacketProgramLaw
import SecondOrder.UniformUpperProgram

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d L : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Joint equality for the whole finite packet. Every uncreated coordinate
is zero on both sides, and each created node receives independent samples. -/
theorem CommonLoss.postChordPacketProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (Lip s τ ρ δ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    OracleProgram.seededOutputLaw μ (postChordSeedLaw L δ) (.grad 0) 0
      (fun q a => hvpReply f a q) (fun seeds => postChordPacketProgram P Lip s τ ρ δ (z,r,b,seeds))
      (Fintype.card (PostChordSlot P Lip s τ ρ δ z r b))=
      Measure.map (sampledChordPacket P f Lip s τ ρ δ z r b) (chordPacketLaw μ L δ) := by
  by_cases hr : (trackedNext Lip s τ z r b).running=true
  · let x := fun i : BinaryNode L =>
      trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i)
    let y := fun i : BinaryNode L =>
      trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i)
    let p := fun i (seed : BatchTape ℝ (confidenceRepeats δ)) =>
      adaptiveChordProgram P ρ δ (x i,y i,seed)
    let g := fun i (tape : BatchTape (ℝ × Ω) (confidenceRepeats δ)) =>
      sampleChordAt P f (x i) (y i) ρ δ tape
    let cost := fun i => localQueryCount (chordVariance P (x i) (y i)) ρ δ
    let is := (createdNodes L z.memory.length).toList
    have hp : ∀ i, OracleProgram.MeasurableFamily (.grad 0) 0 (p i) := by
      intro i
      exact (adaptiveChordProgram_measurable P ρ δ).comp
        (fun seed => (x i,y i,seed)) (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hc : ∀ i seed, OracleProgram.UsesAtMost (cost i) (p i seed) := by
      intro i seed
      exact (adaptiveChordProgram_usesExactly P ρ δ (x i,y i,seed)).usesAtMost
    have hg : ∀ i, Measurable (g i) := by
      intro i
      exact h.sampleChordAt_measurable measurable_const measurable_const ρ δ measurable_id
    have hl : ∀ i, OracleProgram.seededOutputLaw μ (batchTapeLaw unitLine (confidenceRepeats δ))
        (.grad 0) 0 (fun q a => hvpReply f a q) (p i) (cost i)=
        Measure.map (g i) (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) := by
      intro i
      exact h.adaptiveChordProgram_slice_outputLaw a₀ Prod.fst Prod.snd (x i,y i) ρ δ
    have hcount : Fintype.card (PostChordSlot P Lip s τ ρ δ z r b)=(is.map cost).sum := by
      rw [postChordCall_count P 0]
      change requestCharge (chordRequestCharge
        (fun x y => localQueryCount (chordVariance P x y) ρ δ)) _=_
      rw [trackedStepRequests_chordCharge,if_pos hr]
      exact (Finset.sum_map_toList _ _).symm
    have hh := OracleProgram.collectList_seededOutputLaw_samples μ
      (batchTapeLaw unitLine (confidenceRepeats δ))
      (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ))
      (.grad 0) 0 (0 : Point d) a₀ (fun q a => hvpReply f a q) h.hvpReply_joint_measurable
      p hp cost hc g hg hl is (Finset.nodup_toList _)
    have he : (fun seeds => postChordPacketProgram P Lip s τ ρ δ (z,r,b,seeds))=
        (fun seeds => OracleProgram.collectList (0 : Point d) (fun i => p i (seeds i)) is) := by
      funext seeds
      exact if_pos hr
    have ho : sampledChordPacket P f Lip s τ ρ δ z r b=
        (fun seeds i => if i∈is then g i (seeds i) else 0) := by
      funext seeds i
      simp only [sampledChordPacket,hr,true_and,is,Finset.mem_toList,g,x,y]
    rw [he,hcount,ho]
    refine hh.trans ?_
    apply congrArg (fun k : ChordPacketTape Ω L δ → BinaryNode L → Point d =>
      Measure.map k (chordPacketLaw μ L δ))
    funext seeds i
    by_cases hi : i∈is
    · simp only [if_pos hi]
    · simp only [if_neg hi]
  · have he : (fun seeds => postChordPacketProgram P Lip s τ ρ δ (z,r,b,seeds))=
        (fun _ : PostChordSeed L δ => .done (0 : BinaryNode L → Point d)) := by
      funext seeds
      exact if_neg hr
    have ho : sampledChordPacket P f Lip s τ ρ δ z r b=
        (fun _ : ChordPacketTape Ω L δ => (0 : BinaryNode L → Point d)) := by
      funext seeds i
      simp [sampledChordPacket,hr]
    rw [he,ho,OracleProgram.seededOutputLaw_done]
    simp

end
end SecondOrder
