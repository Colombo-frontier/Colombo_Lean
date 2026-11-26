import RandomizedFO2003.MarkedTerminal

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable (E X R : Type) [MeasurableSpace E] [MeasurableSpace X] [MeasurableSpace R]

/-- An ordinary full-history round with a decoder for the two physical
answers available from a marked matrix round. The inverse answer need not
be used by the decoder. -/
structure DecodedRound (S : Type u) [MeasurableSpace S] where
  query : S → X
  measurable_query : Measurable query
  authorized : S → Bool
  measurable_authorized : Measurable authorized
  response : (S × E) × E → R
  measurable_response : Measurable response

def DecodedProgram : (t : ℕ) → (S : Type u) → [MeasurableSpace S] → Type u
  | 0, _, _ => PUnit
  | t + 1, S, _ => DecodedRound E X R S × DecodedProgram t (S × R)

variable {E X R}

noncomputable def DecodedRound.marked {S H : Type u} [MeasurableSpace S] [MeasurableSpace H]
    (round : DecodedRound E X R S) (coordinate : X → E) (hc : Measurable coordinate)
    (view : H → S) (hv : Measurable view) : MarkedRoundPolicy E H where
  authorized := round.authorized ∘ view
  measurable_authorized := round.measurable_authorized.comp hv
  query := fun p => coordinate (round.query (view p.1))
  measurable_query := hc.comp (round.measurable_query.comp (hv.comp measurable_fst))

/-- Discard the latent inverse answer and append the reconstructed ordinary
response, retaining the complete older ordinary history. -/
noncomputable def DecodedRound.nextView {S H : Type u} [MeasurableSpace S] [MeasurableSpace H]
    (round : DecodedRound E X R S) (view : H → S) (p : MarkedRoundHistory E H) : S × R :=
  (view p.1.1.1, round.response ((view p.1.1.1, p.1.1.2), p.2))

theorem DecodedRound.measurable_nextView {S H : Type u} [MeasurableSpace S] [MeasurableSpace H]
    (round : DecodedRound E X R S) (view : H → S) (hv : Measurable view) :
    Measurable (round.nextView view) := by
  have hs : Measurable (fun p : MarkedRoundHistory E H => view p.1.1.1) :=
    hv.comp measurable_fst.fst.fst
  exact hs.prodMk (round.measurable_response.comp ((hs.prodMk measurable_fst.fst.snd).prodMk measurable_snd))

noncomputable def DecodedProgram.marked (coordinate : X → E) (hc : Measurable coordinate) :
    (t : ℕ) → {S H : Type u} → [MeasurableSpace S] → [MeasurableSpace H] →
    DecodedProgram E X R t S → (view : H → S) → Measurable view → MarkedProgram E t H
  | 0, _, _, _, _, _, _, _ => PUnit.unit
  | t + 1, _, _, _, _, plan, view, hv =>
      (plan.1.marked coordinate hc view hv,
        marked coordinate hc t plan.2 (plan.1.nextView view) (plan.1.measurable_nextView view hv))

noncomputable def DecodedProgram.decode : (t : ℕ) → {S H : Type u} →
    [MeasurableSpace S] → [MeasurableSpace H] → DecodedProgram E X R t S →
    (H → S) → ActionHistory E (markedActionCount t) H → ActionHistory R t S
  | 0, _, _, _, _, _, view => view
  | t + 1, _, _, _, _, plan, view => decode t plan.2 (plan.1.nextView view)

theorem DecodedProgram.measurable_decode (t : ℕ) {S H : Type u}
    [MeasurableSpace S] [MeasurableSpace H] (plan : DecodedProgram E X R t S)
    (view : H → S) (hv : Measurable view) : Measurable (plan.decode t view) := by
  induction t generalizing S H with
  | zero => exact hv
  | succ t ih => exact ih plan.2 _ (plan.1.measurable_nextView view hv)

/-- The ordinary oracle run, with no assumptions on linear spans, query
norms, or how the next query depends on the entire history. -/
noncomputable def DecodedProgram.run (oracle : X → R) : (t : ℕ) → {S : Type u} →
    [MeasurableSpace S] → DecodedProgram E X R t S → S → ActionHistory R t S
  | 0, _, _, _, s => s
  | t + 1, _, _, plan, s => run oracle t plan.2 (s, oracle (plan.1.query s))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

/-- Correctness is required only along this oracle trajectory. The initial
state can include fixed external parameters and arbitrary private randomness. -/
def DecodedProgram.CorrectAlong (coordinate : X → E) (A U : E →L[ℝ] E)
    (u : E) (oracle : X → R) : (t : ℕ) → {S : Type u} → [MeasurableSpace S] →
    DecodedProgram E X R t S → S → Prop
  | 0, _, _, _, _ => True
  | t + 1, _, _, plan, s =>
      plan.1.response ((s, if plan.1.authorized s = true then U u else 0),
        U (A (U.adjoint (coordinate (plan.1.query s))))) = oracle (plan.1.query s) ∧
      CorrectAlong coordinate A U u oracle t plan.2 (s, oracle (plan.1.query s))

theorem DecodedRound.nextView_run {S H : Type u} [MeasurableSpace S] [MeasurableSpace H]
    (round : DecodedRound E X R S) (coordinate : X → E) (hc : Measurable coordinate)
    (view : H → S) (hv : Measurable view) (A U : E →L[ℝ] E)
    (mark : H → E) (hm : Measurable mark) (h : H) :
    round.nextView view (((round.marked coordinate hc view hv).program A mark hm).run 3 U h) =
      (view h, round.response ((view h, if round.authorized (view h) = true then U (mark h) else 0),
        U (A (U.adjoint (coordinate (round.query (view h))))))) := by
  by_cases ha : round.authorized (view h) = true
  · simp [nextView, marked, MarkedRoundPolicy.program, ActionProgram.run,
      markedVectorRequest, matrixResponseRequest, ExposureKind.action, ha]
  · simp [nextView, marked, MarkedRoundPolicy.program, ActionProgram.run,
      markedVectorRequest, matrixResponseRequest, ExposureKind.action, ha]

/-- Compiling and decoding preserves the exact final full oracle history. -/
theorem DecodedProgram.decode_run (t : ℕ) {S H : Type u}
    [MeasurableSpace S] [MeasurableSpace H] (plan : DecodedProgram E X R t S)
    (coordinate : X → E) (hc : Measurable coordinate) (view : H → S) (hv : Measurable view)
    (A U : E →L[ℝ] E) (mark : H → E) (hm : Measurable mark) (oracle : X → R) (h : H)
    (hcorrect : plan.CorrectAlong coordinate A U (mark h) oracle t (view h)) :
    plan.decode t view (((plan.marked coordinate hc t view hv).compile A t mark hm).run
      (markedActionCount t) U h) = plan.run oracle t (view h) := by
  induction t generalizing S H with
  | zero => rfl
  | succ t ih =>
    let h' := ((plan.1.marked coordinate hc view hv).program A mark hm).run 3 U h
    have hs : plan.1.nextView view h' = (view h, oracle (plan.1.query (view h))) := by
      rw [plan.1.nextView_run coordinate hc view hv A U mark hm h, hcorrect.1]
    have hm' : (mark ∘ ActionHistory.seed E 3) h' = mark h := by
      exact congrArg mark (ActionProgram.run_seed 3 _ U h)
    change plan.2.decode t (plan.1.nextView view)
      (((plan.2.marked coordinate hc t (plan.1.nextView view) (plan.1.measurable_nextView view hv)).compile
        A t (mark ∘ ActionHistory.seed E 3) (hm.comp (ActionHistory.seed_measurable 3))).run
          (markedActionCount t) U h') = _
    rw [ih plan.2 (plan.1.nextView view) (plan.1.measurable_nextView view hv)
      (mark ∘ ActionHistory.seed E 3) (hm.comp (ActionHistory.seed_measurable 3)) h']
    · rw [hs]
      rfl
    · rw [hm', hs]
      exact hcorrect.2

end RandomizedFO2003.Rotations
