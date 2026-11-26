import SecondOrder.LocalSampleEnumeration
import SecondOrder.OracleSeedTransport
import SecondOrder.OracleSuccessProbability

open MeasureTheory

namespace SecondOrder
noncomputable section

theorem localReplyProgram_measurable {S : Type} [MeasurableSpace S] {d : ℕ}
    (V ρ δ : ℝ) (qs : S → LocalReplySlot V ρ δ → HvpQuery d)
    (hq : ∀ i, Measurable (fun s => qs s i)) :
    OracleProgram.MeasurableFamily (.grad 0) 0 (fun s => localReplyProgram V ρ δ (qs s)) := by
  apply OracleProgram.batch_measurable
  · intro i
    exact hq _
  · apply (localReplyCenter_measurable V ρ δ).comp
    exact measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply (Fintype.equivFin _ i)).comp measurable_snd)

theorem localReplyProgram_usesExactly {d : ℕ} (V ρ δ : ℝ)
    (qs : LocalReplySlot V ρ δ → HvpQuery d) :
    OracleProgram.UsesExactly (localQueryCount V ρ δ) (localReplyProgram V ρ δ qs) := by
  rw [←localReplySlot_count]
  exact OracleProgram.batch_usesExactly _ _ _

theorem localReplyProgram_outputDraws {Ω : Type} {d : ℕ} (V ρ δ : ℝ)
    (qs : LocalReplySlot V ρ δ → HvpQuery d) (reply : HvpQuery d → Ω → Point d)
    (a₀ : Ω) (w : LocalDraws Ω V ρ δ) :
    OracleProgram.output 0 (OracleProgram.runDraws (.grad 0) reply (localReplyProgram V ρ δ qs)
      (localQueryCount V ρ δ) (localEnumeratedDraws V ρ δ w))=
        localReplyCenter V ρ δ (fun i => reply (qs i) (localReplySample w i)) := by
  let zs := drawsTape a₀ _ (localEnumeratedDraws V ρ δ w)
  have he := OracleProgram.run_eq_runDraws (HvpQuery.grad (0 : Point d)) reply zs
    (localReplyProgram V ρ δ qs) _ (localEnumeratedDraws V ρ δ w) (drawsTape_apply a₀ _ _)
  have ha := OracleProgram.algorithm_output (HvpQuery.grad (0 : Point d)) 0 0
    (localReplyProgram V ρ δ qs) reply zs (localQueryCount V ρ δ)
  rw [he] at ha
  have hb := localReplyAlgorithm_output V ρ δ qs reply zs
  simp only [zs,localEnumeratedDraws_tape] at hb
  exact ha.symm.trans hb

theorem localReplyProgram_outputLaw {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V ρ δ : ℝ)
    (qs : LocalReplySlot V ρ δ → HvpQuery d) (reply : HvpQuery d → Ω → Point d)
    (hr : Measurable (fun w : HvpQuery d × Ω => reply w.1 w.2)) (a₀ : Ω) :
    OracleProgram.outputLaw μ (.grad 0) 0 reply (localReplyProgram V ρ δ qs) (localQueryCount V ρ δ)=
      Measure.map (fun w => localReplyCenter V ρ δ (fun i => reply (qs i) (localReplySample w i)))
        (localLaw μ V ρ δ) := by
  have hp := localReplyProgram_measurable V ρ δ (fun _ : Unit => qs) (fun _ => measurable_const)
  have ht : Measurable (fun w : Draws Ω (localQueryCount V ρ δ) => ((),w)) :=
    measurable_const.prodMk measurable_id
  have hm := (hp.runDrawsOutput 0 a₀ reply hr _).comp ht
  change Measurable (fun w : Draws Ω (localQueryCount V ρ δ) =>
    OracleProgram.output 0 (OracleProgram.runDraws (.grad 0) reply (localReplyProgram V ρ δ qs) _ w)) at hm
  have hs := localEnumeratedDraws_measurePreserving μ V ρ δ
  unfold OracleProgram.outputLaw
  rw [←hs.map_eq,Measure.map_map hm hs.measurable]
  congr 1
  funext w
  exact localReplyProgram_outputDraws V ρ δ qs reply a₀ w

def gradientAnchorProgram {d : ℕ} (P : Parameters) (x : Point d) (ρ δ : ℝ) :
    OracleProgram (HvpQuery d) (Point d) (Point d) :=
  localReplyProgram (P.gradientNoise^2) ρ δ (fun _ => .grad x)

theorem gradientAnchorProgram_measurable {d : ℕ} (P : Parameters) (ρ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) 0 (fun x : Point d => gradientAnchorProgram P x ρ δ) := by
  apply localReplyProgram_measurable
  intro i
  exact (hvpQueryMeasurableEquiv d).symm.measurable.comp measurable_inl

theorem CommonLoss.gradientAnchorProgram_outputLaw {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {d : ℕ} {ν : ℝ}
    {F : Point d → ℝ} {f : Ω → Point d → ℝ} (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (x : Point d) (ρ δ : ℝ) :
    OracleProgram.outputLaw μ (.grad 0) 0 (fun q z => hvpReply f z q)
      (gradientAnchorProgram P x ρ δ) (localQueryCount (P.gradientNoise^2) ρ δ)=
      Measure.map (gradientAnchor P f x ρ δ) (localLaw μ (P.gradientNoise^2) ρ δ) := by
  have hh := localReplyProgram_outputLaw μ (P.gradientNoise^2) ρ δ (fun _ => .grad x)
    (fun q z => hvpReply f z q) h.hvpReply_joint_measurable a₀
  rw [gradientAnchorProgram,hh]
  apply congrArg (fun g : LocalDraws Ω (P.gradientNoise^2) ρ δ → Point d =>
    Measure.map g (localLaw μ (P.gradientNoise^2) ρ δ))
  funext w
  exact (freshEstimate_eq_localReplyCenter (fun z => gradient (f z) x)
    (P.gradientNoise^2) ρ δ w).symm

end
end SecondOrder
