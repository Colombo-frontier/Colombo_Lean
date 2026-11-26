import SecondOrder.PostChordOutputLaw
import SecondOrder.BudgetLocalOutputLaws
import SecondOrder.SampledKernelComposition

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d L : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The actual packet followed by conditional refresh has the same joint
state output as the independent post-move tape used in the analysis. -/
theorem CommonLoss.postMoveProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (q : ℕ) (Lip s τ ρ δ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    OracleProgram.seededOutputLaw μ (postChordSeedLaw L δ) (.grad 0) (trackedInitial 0)
      (fun q a => hvpReply f a q) (fun seeds => postMoveProgram P q Lip s τ ρ δ (z,r,b,seeds))
      (postRequestPrice P q Lip s τ ρ δ z r b)=
      Measure.map (sampledPostStep P f q Lip s τ ρ δ z r b) (postMoveLaw μ P L τ δ) := by
  let zeroSeed : PostChordSeed L δ := fun _ m =>
    vectorDraws (confidenceRepeats δ) (fun _ => vectorDraws m (fun _ => (0 : ℝ)))
  let w₀ : PostProgramInput d L δ := (z,r,b,zeroSeed)
  let pc := fun seeds => postChordPacketProgram P Lip s τ ρ δ (z,r,b,seeds)
  let pr := postRefreshProgram P q Lip s τ δ w₀
  let pf := fun packet : BinaryNode L → Point d =>
    OracleProgram.bind pr (fun anchor => .done (trackedStep q Lip s τ z r b packet anchor))
  let Nc := Fintype.card (PostChordSlot P Lip s τ ρ δ z r b)
  let Nr := Fintype.card (PostRefreshSlot P q Lip s τ δ z r b)
  have hpc : OracleProgram.MeasurableFamily (.grad 0) 0 pc :=
    (postChordPacketProgram_measurable P Lip s τ ρ δ).comp
      (fun seeds => (z,r,b,seeds))
      (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hpr : OracleProgram.MeasurableFamily (.grad 0) (0 : Point d) (fun _ : Unit => pr) :=
    (postRefreshProgram_measurable P q Lip s τ δ).comp (fun _ => w₀) measurable_const
  have hpf : OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0) pf := by
    apply (hpr.comp (fun _ : BinaryNode L → Point d => ()) measurable_const).bind
    apply OracleProgram.measurableFamily_done
    exact trackedStep_measurable q Lip s τ measurable_const measurable_const measurable_const
      measurable_fst measurable_snd
  have hc : ∀ seeds, OracleProgram.UsesAtMost Nc (pc seeds) := by
    intro seeds
    exact (postChordPacketProgram_usesExactly P Lip s τ ρ δ (z,r,b,seeds)).usesAtMost
  have hr : OracleProgram.UsesAtMost Nr pr :=
    (postRefreshProgram_usesExactly P q Lip s τ δ w₀).usesAtMost
  have hf : ∀ packet, OracleProgram.UsesAtMost Nr (pf packet) := by
    intro packet
    have hh := OracleProgram.usesAtMost_bind hr
      (fun anchor => .done (trackedStep q Lip s τ z r b packet anchor))
      (m := 0) (fun _ => trivial)
    simpa only [Nat.add_zero] using hh
  have hcomp := OracleProgram.seededOutputLaw_bind_fixed μ (postChordSeedLaw L δ)
    (.grad 0) 0 (0 : BinaryNode L → Point d) (trackedInitial 0) a₀
    (fun q a => hvpReply f a q) h.hvpReply_joint_measurable pc hpc Nc hc pf hpf Nr hf
  let step := fun (packet : BinaryNode L → Point d)
      (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) =>
    trackedStep q Lip s τ z r b packet (sampledRefreshAnchor P f q Lip s τ δ z r b a)
  have hs : Measurable (fun v : (BinaryNode L → Point d) × LocalDraws Ω (P.gradientNoise^2) (τ/4) δ =>
      step v.1 v.2) := by
    exact trackedStep_measurable q Lip s τ measurable_const measurable_const measurable_const
      measurable_fst (h.sampledRefreshAnchor_measurable q Lip s τ δ
        measurable_const measurable_const measurable_const measurable_snd)
  let K := sampledResponseKernel (localLaw μ (P.gradientNoise^2) (τ/4) δ) step hs
  have hk : (OracleProgram.outputKernel μ (.grad 0) 0 (trackedInitial 0) a₀
      (fun q a => hvpReply f a q) h.hvpReply_joint_measurable pf hpf Nr :
      (BinaryNode L → Point d) → Measure (TrackedState d L))=K := by
    funext packet
    have ht : Measurable (fun anchor => trackedStep q Lip s τ z r b packet anchor) :=
      trackedStep_measurable q Lip s τ measurable_const measurable_const measurable_const
        measurable_const measurable_id
    change OracleProgram.outputLaw μ (.grad 0) (trackedInitial 0)
      (fun q a => hvpReply f a q) (pf packet) Nr=K packet
    have hm := OracleProgram.outputLaw_bind_done μ (.grad 0) 0 (0 : Point d) (trackedInitial 0)
      a₀ (fun q a => hvpReply f a q) h.hvpReply_joint_measurable pr hpr Nr hr _ ht
    refine hm.trans ?_
    have ha : Measurable (fun a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ =>
        sampledRefreshAnchor P f q Lip s τ δ z r b a) :=
      h.sampledRefreshAnchor_measurable q Lip s τ δ
        measurable_const measurable_const measurable_const measurable_id
    rw [h.postRefreshProgram_outputLaw a₀ q Lip s τ δ w₀,Measure.map_map ht ha]
    rfl
  rw [hk] at hcomp
  have hpcl := h.postChordPacketProgram_outputLaw a₀ Lip s τ ρ δ z r b
  change OracleProgram.seededOutputLaw μ (postChordSeedLaw L δ) (.grad 0) 0
    (fun q a => hvpReply f a q) pc Nc=_ at hpcl
  rw [hpcl] at hcomp
  have hpct := h.sampledChordPacket_measurable Lip s τ ρ δ
    (z := fun _ : ChordPacketTape Ω L δ => z) (r := fun _ => r) (b := fun _ => b)
    measurable_const measurable_const measurable_const measurable_id
  have hm := map_bind_sampledResponse (chordPacketLaw μ L δ)
    (localLaw μ (P.gradientNoise^2) (τ/4) δ)
    (sampledChordPacket P f Lip s τ ρ δ z r b) hpct step hs
  have he : (fun seeds => postMoveProgram P q Lip s τ ρ δ (z,r,b,seeds))=
      (fun seeds => OracleProgram.bind (pc seeds) pf) := rfl
  rw [he,postRequestPrice_eq_oracle_slots]
  exact hcomp.trans hm

end
end SecondOrder
