import SecondOrder.OracleProgramHistory

open MeasureTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O O' Ω Ξ : Type}
variable [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O]
  [MeasurableSpace O'] [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Sequential composition feeds the first output into the second program
and samples the second block independently of the first block. -/
theorem outputLaw_bind (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (o₀' : O') (a₀ : Ω)
    (reply : Q → Ω → Y) (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : OracleProgram Q Y O) (f : O → OracleProgram Q Y O') (N M : ℕ)
    (hp : MeasurableFamily q₀ o₀ (fun _ : Unit => p))
    (hf : MeasurableFamily q₀ o₀' f) (hN : UsesExactly N p) :
    outputLaw μ q₀ o₀' reply (bind p f) (N+M)=
      Measure.map (fun w : Draws Ω N × Draws Ω M =>
        output o₀' (runDraws q₀ reply (f (output o₀ (runDraws q₀ reply p N w.1))) M w.2))
          ((drawsLaw μ N).prod (drawsLaw μ M)) := by
  have hf' := hf.comp (fun w : Unit × O => w.2) measurable_snd
  have hfull := hp.bind (f := fun (_ : Unit) o => f o) hf'
  have ht : Measurable (fun w : Draws Ω (N+M) => ((),w)) :=
    measurable_const.prodMk measurable_id
  have hm := (hfull.runDrawsOutput y₀ a₀ reply hr (N+M)).comp ht
  change Measurable (fun w : Draws Ω (N+M) => output o₀' (runDraws q₀ reply (bind p f) (N+M) w)) at hm
  unfold outputLaw
  rw [←(drawsAppend_measurePreserving μ N M).map_eq,
    Measure.map_map hm (drawsAppend_measurable N M)]
  congr 1
  funext w
  obtain ⟨o,ho⟩ := runDraws_done q₀ reply a₀ hN.usesAtMost w.1
  simp only [Function.comp_apply,runDraws_bind_of_exact q₀ reply a₀ hN f w.1 ho M w.2,
    ho,output]

def seededOutputLaw (μ : Measure Ω) (η : Measure Ξ) (q₀ : Q) (o₀ : O)
    (reply : Q → Ω → Y) (p : Ξ → OracleProgram Q Y O) (N : ℕ) : Measure O :=
  Measure.map (fun w : Ξ × Draws Ω N => output o₀ (runDraws q₀ reply (p w.1) N w.2))
    (η.prod (drawsLaw μ N))

theorem seededOutputLaw_probability (μ : Measure Ω) (η : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : Ξ → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) :
    IsProbabilityMeasure (seededOutputLaw μ η q₀ o₀ reply p N) := by
  unfold seededOutputLaw
  exact isProbabilityMeasure_map (hp.runDrawsOutput y₀ a₀ reply hr N).aemeasurable

/-- This includes arbitrary private random seeds independent of the loss
samples. It is the distribution identity needed by HvpSolves. -/
theorem algorithm_seeded_history_outputLaw (μ : Measure Ω) (η : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : Ξ → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ) :
    Measure.map (fun w : Ξ × FiniteHistory Unit Ω N =>
      oracleHistoryOutput (algorithm q₀ y₀ o₀ (p w.1)) reply N w.2)
        (η.prod (oracleHistoryLaw μ N))=
      seededOutputLaw μ η q₀ o₀ reply p N := by
  have htrans := (MeasurePreserving.id η).prod (historyDraws_measurePreserving μ N)
  unfold seededOutputLaw
  rw [←htrans.map_eq,Measure.map_map (hp.runDrawsOutput y₀ a₀ reply hr N) htrans.measurable]
  congr 1
  funext w
  exact algorithm_history_output q₀ y₀ o₀ (p w.1) reply a₀ N w.2

end
end OracleProgram
end SecondOrder
