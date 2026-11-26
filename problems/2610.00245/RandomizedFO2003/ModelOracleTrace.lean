import RandomizedFO2003.DecodedTrace
import RandomizedFO2003.ModelOracleProgram

namespace RandomizedFO2003.Model

open MeasureTheory Rotations

variable {d : ℕ} {E P Seed : Type} [MeasurableSpace E] [MeasurableSpace P] [MeasurableSpace Seed]

theorem Algorithm.decodedProgram_trace (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (f : Space d → ℝ) (t n : ℕ) {S : Type} [MeasurableSpace S]
    (seed : S → Seed) (hs : Measurable seed) (history : S → Fin n → Response d) (hh : Measurable history)
    (param : S → P) (hp : Measurable param) (s : S)
    (hhistory : history s = transcript A f (seed s) n) (i : Fin t) :
    (A.decodedProgram codec t n seed hs history hh param hp).trace (oracle f) t s i =
      (A.query (n + i.val) (seed s) (transcript A f (seed s) (n + i.val)),
        codec.authorized (param s, A.query (n + i.val) (seed s) (transcript A f (seed s) (n + i.val)))) := by
  induction t generalizing n S with
  | zero => exact i.elim0
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (A.query n (seed s) (history s), codec.authorized (param s, A.query n (seed s) (history s))) = _
      rw [hhistory]
      rfl
    · let s' := (s, oracle f (A.query n (seed s) (history s)))
      have hh' : historyStep n history s' = transcript A f ((seed ∘ Prod.fst) s') (n + 1) := by
        simp only [historyStep, s', Function.comp_apply, transcript, hhistory]
      have hi := ih (n + 1) (seed ∘ Prod.fst) (hs.comp measurable_fst)
        (historyStep n history) (measurable_historyStep n history hh)
        (param ∘ Prod.fst) (hp.comp measurable_fst) s' hh' j
      have hindex : n + 1 + j.val = n + j.succ.val := by simp only [Fin.val_succ]; omega
      rw [hindex] at hi
      exact hi

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

/-- Each recorded latent query is the adjoint image of the original model's
query, and each recorded authorization uses exactly that same full query. -/
theorem Algorithm.markedOracle_traces (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (coordinate : Space d → E) (hc : Measurable coordinate) (T : ℕ)
    (M U : E →L[ℝ] E) (u : E) (p : P) (seed : Seed) (f : Space d → ℝ)
    (hcodec : ∀ x, codec.response ((p, x),
      (if codec.authorized (p, x) = true then U u else 0, U (M (U.adjoint (coordinate x))))) = oracle f x)
    (i : Fin T) :
    let plan := A.markedOracleProgram codec coordinate hc T
    let q := (plan.compile M T Prod.fst measurable_fst).run (markedActionCount T) U (u, p, seed)
    let x := A.query i.val seed (transcript A f seed i.val)
    markedQueryTrace E T q i = U.adjoint (coordinate x) ∧
      plan.authorizationTrace T q i = codec.authorized (p, x) := by
  dsimp only
  have hcorrect : (A.initialDecodedProgram codec T).CorrectAlong coordinate M U u (oracle f) T (u, p, seed) :=
    A.decodedProgram_correctAlong codec coordinate M U u f T 0
      (fun q : E × (P × Seed) => q.2.2) measurable_snd.snd (fun _ => Fin.elim0) measurable_empty_history
      (fun q => q.2.1) measurable_snd.fst (u, p, seed) hcodec
  have ht := (A.initialDecodedProgram codec T).traces_run T coordinate hc id measurable_id M U
    Prod.fst measurable_fst (oracle f) (u, p, seed) hcorrect i
  have htrace := A.decodedProgram_trace codec f T 0
    (fun q : E × (P × Seed) => q.2.2) measurable_snd.snd (fun _ => Fin.elim0) measurable_empty_history
    (fun q => q.2.1) measurable_snd.fst (u, p, seed) rfl i
  have htime := congrArg (fun j => (A.query j seed (transcript A f seed j),
    codec.authorized (p, A.query j seed (transcript A f seed j)))) (Nat.zero_add i.val)
  have he := htrace.trans htime
  change (A.initialDecodedProgram codec T).trace (oracle f) T (id (u, p, seed)) i = _ at he
  dsimp only at ht
  rw [he] at ht
  exact ht

end RandomizedFO2003.Model
