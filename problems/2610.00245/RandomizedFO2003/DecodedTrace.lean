import RandomizedFO2003.MarkedDecoder

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E X R : Type} [MeasurableSpace E] [MeasurableSpace X] [MeasurableSpace R]

/-- The actual ordinary queries and authorization decisions along a run. -/
noncomputable def DecodedProgram.trace (oracle : X → R) : (t : ℕ) → {S : Type u} →
    [MeasurableSpace S] → DecodedProgram E X R t S → S → Fin t → X × Bool
  | 0, _, _, _, _ => Fin.elim0
  | t + 1, _, _, plan, s => Fin.cons (plan.1.query s, plan.1.authorized s)
      (trace oracle t plan.2 (s, oracle (plan.1.query s)))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

theorem MarkedProgram.queryTrace_zero_run (t : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram E (t + 1) H) (A U : E →L[ℝ] E)
    (mark : H → E) (hm : Measurable mark) (h : H) :
    markedQueryTrace E (t + 1) ((plan.compile A (t + 1) mark hm).run (markedActionCount (t + 1)) U h) 0 =
      U.adjoint (plan.1.query (h, if plan.1.authorized h = true then U (mark h) else 0)) := by
  change (ActionHistory.seed E (markedActionCount t)
    ((plan.2.compile A t (mark ∘ ActionHistory.seed E 3) (hm.comp (ActionHistory.seed_measurable 3))).run
      (markedActionCount t) U ((plan.1.program A mark hm).run 3 U h))).1.2 = _
  rw [ActionProgram.run_seed]
  by_cases ha : plan.1.authorized h = true <;>
    simp [MarkedRoundPolicy.program, ActionProgram.run, markedVectorRequest,
      matrixResponseRequest, ExposureKind.action, ha]

theorem MarkedProgram.authorizationTrace_zero_run (t : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : MarkedProgram E (t + 1) H) (A U : E →L[ℝ] E)
    (mark : H → E) (hm : Measurable mark) (h : H) :
    plan.authorizationTrace (t + 1)
      ((plan.compile A (t + 1) mark hm).run (markedActionCount (t + 1)) U h) 0 = plan.1.authorized h := by
  change plan.1.authorized (ActionHistory.seed E (markedActionCount (t + 1)) _) = _
  rw [ActionProgram.run_seed]

/-- Both traces of the compiled program agree, round by round, with the
ordinary oracle run. The current marked answer cannot alter its query. -/
theorem DecodedProgram.traces_run (t : ℕ) {S H : Type u}
    [MeasurableSpace S] [MeasurableSpace H] (plan : DecodedProgram E X R t S)
    (coordinate : X → E) (hc : Measurable coordinate) (view : H → S) (hv : Measurable view)
    (A U : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark) (oracle : X → R) (h : H)
    (hcorrect : plan.CorrectAlong coordinate A U (mark h) oracle t (view h)) (i : Fin t) :
    let q := ((plan.marked coordinate hc t view hv).compile A t mark hm).run (markedActionCount t) U h
    markedQueryTrace E t q i = U.adjoint (coordinate (plan.trace oracle t (view h) i).1) ∧
      (plan.marked coordinate hc t view hv).authorizationTrace t q i = (plan.trace oracle t (view h) i).2 := by
  dsimp only
  induction t generalizing S H with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [MarkedProgram.queryTrace_zero_run, MarkedProgram.authorizationTrace_zero_run]
      exact ⟨rfl, rfl⟩
    · let h' := ((plan.1.marked coordinate hc view hv).program A mark hm).run 3 U h
      have hs : plan.1.nextView view h' = (view h, oracle (plan.1.query (view h))) := by
        rw [plan.1.nextView_run coordinate hc view hv A U mark hm h, hcorrect.1]
      have hm' : (mark ∘ ActionHistory.seed E 3) h' = mark h :=
        congrArg mark (ActionProgram.run_seed 3 _ U h)
      have hct : plan.2.CorrectAlong coordinate A U ((mark ∘ ActionHistory.seed E 3) h') oracle t
          (plan.1.nextView view h') := by
        rw [hm', hs]
        exact hcorrect.2
      have hi := ih plan.2 (plan.1.nextView view) (plan.1.measurable_nextView view hv)
        (mark ∘ ActionHistory.seed E 3) (hm.comp (ActionHistory.seed_measurable 3)) h' hct j
      rw [hs] at hi
      exact hi

end RandomizedFO2003.Rotations
