import RandomizedFO2003.DecodedTrace

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- Adding the terminal round preserves each earlier inverse query and
authorization. The statements compare actual fixed-operator executions. -/
theorem MarkedProgram.withTerminal_prefix_traces (t : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram E t H) (A : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark)
    (output : ActionHistory E (markedActionCount t) H → E) (ho : Measurable output)
    (U : E →L[ℝ] E) (h : H) (i : Fin t) :
    let full := plan.withTerminal t output ho
    let p := (full.compile A (t + 1) mark hm).run (markedActionCount (t + 1)) U h
    let q := (plan.compile A t mark hm).run (markedActionCount t) U h
    markedQueryTrace E (t + 1) p i.castSucc = markedQueryTrace E t q i ∧
      full.authorizationTrace (t + 1) p i.castSucc = plan.authorizationTrace t q i := by
  dsimp only
  induction t generalizing H with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.castSucc_zero]
      constructor
      · rw [MarkedProgram.queryTrace_zero_run, MarkedProgram.queryTrace_zero_run]
        rfl
      · rw [MarkedProgram.authorizationTrace_zero_run, MarkedProgram.authorizationTrace_zero_run]
        rfl
    · exact ih plan.2 (mark ∘ ActionHistory.seed E 3) (hm.comp (ActionHistory.seed_measurable 3)) output ho
        ((plan.1.program A mark hm).run 3 U h) j

end RandomizedFO2003.Rotations
