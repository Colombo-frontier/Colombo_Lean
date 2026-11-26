import SecondOrder.OracleProgramLawComposition

open MeasureTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O Ω S T : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

theorem seededOutputLaw_mapSeed (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : T → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p)
    (g : S → T) (hg : Measurable g) (N : ℕ) :
    seededOutputLaw μ (Measure.map g η) q₀ o₀ reply p N=
      seededOutputLaw μ η q₀ o₀ reply (fun s => p (g s)) N := by
  have hs : MeasurePreserving g η (Measure.map g η) := ⟨hg,rfl⟩
  have ht := hs.prod (MeasurePreserving.id (drawsLaw μ N))
  unfold seededOutputLaw
  rw [←ht.map_eq,Measure.map_map (hp.runDrawsOutput y₀ a₀ reply hr N) ht.measurable]
  rfl

omit [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O] [MeasurableSpace Ω] in
theorem runDraws_done_program (q₀ : Q) (reply : Q → Ω → Y) (o : O) (N : ℕ) (w : Draws Ω N) :
    runDraws q₀ reply (.done o) N w=.done o := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [runDraws,ih w.1,advance]

theorem seededOutputLaw_done (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (o₀ o : O) (reply : Q → Ω → Y) (N : ℕ) :
    seededOutputLaw μ η q₀ o₀ reply (fun _ => .done o) N=Measure.dirac o := by
  unfold seededOutputLaw
  simp only [runDraws_done_program,output]
  simp

theorem algorithm_seeded_history_event (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p) (N : ℕ)
    (s : Set O) (hs : MeasurableSet s) :
    (η.prod (oracleHistoryLaw μ N))
      {w | oracleHistoryOutput (algorithm q₀ y₀ o₀ (p w.1)) reply N w.2 ∈ s}=
      seededOutputLaw μ η q₀ o₀ reply p N s := by
  have hm := oracleHistoryOutput_measurable (fun u => algorithm q₀ y₀ o₀ (p u))
    (algorithm_measurable y₀ hp) reply hr N
  rw [←algorithm_seeded_history_outputLaw μ η q₀ y₀ o₀ a₀ reply hr p hp N,
    Measure.map_apply hm hs]
  rfl

end
end OracleProgram
end SecondOrder
