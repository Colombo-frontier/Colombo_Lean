import RandomizedFO2003.MarkedDecoder
import RandomizedFO2003.Model

namespace RandomizedFO2003.Model

open MeasureTheory Rotations

variable {d : ℕ} {E P Seed : Type} [MeasurableSpace E] [MeasurableSpace P] [MeasurableSpace Seed]

/-- The public parameters determine authorization and reconstruction. The
two vector inputs are the marked answer and physical matrix answer. -/
structure OracleCodec (d : ℕ) (E P : Type) [MeasurableSpace E] [MeasurableSpace P] where
  authorized : P × Space d → Bool
  measurable_authorized : Measurable authorized
  response : (P × Space d) × (E × E) → Response d
  measurable_response : Measurable response

noncomputable def historyStep {S : Type} (n : ℕ) (history : S → Fin n → Response d)
    (p : S × Response d) : Fin (n + 1) → Response d := Fin.snoc (history p.1) p.2

theorem measurable_historyStep {S : Type} [MeasurableSpace S] (n : ℕ)
    (history : S → Fin n → Response d) (hh : Measurable history) : Measurable (historyStep n history) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [historyStep, Fin.snoc_last] using
      (measurable_snd : Measurable (fun p : S × Response d => p.2))
  · simpa only [historyStep, Fin.snoc_castSucc] using ((measurable_pi_apply j).comp hh).comp measurable_fst

noncomputable def Algorithm.decodedRound (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (n : ℕ) {S : Type} [MeasurableSpace S] (seed : S → Seed) (hs : Measurable seed)
    (history : S → Fin n → Response d) (hh : Measurable history) (param : S → P) (hp : Measurable param) :
    DecodedRound E (Space d) (Response d) S where
  query := fun s => A.query n (seed s) (history s)
  measurable_query := (A.query_measurable n).comp (hs.prodMk hh)
  authorized := fun s => codec.authorized (param s, A.query n (seed s) (history s))
  measurable_authorized := codec.measurable_authorized.comp
    (hp.prodMk ((A.query_measurable n).comp (hs.prodMk hh)))
  response := fun p => codec.response ((param p.1.1, A.query n (seed p.1.1) (history p.1.1)), (p.1.2, p.2))
  measurable_response := codec.measurable_response.comp
    (((hp.comp measurable_fst.fst).prodMk
      (((A.query_measurable n).comp (hs.prodMk hh)).comp measurable_fst.fst)).prodMk
        (measurable_fst.snd.prodMk measurable_snd))

/-- This adapter retains every response from `Model.Algorithm`, including
the private seed and any independent public parameters carried initially. -/
noncomputable def Algorithm.decodedProgram (A : Algorithm d Seed) (codec : OracleCodec d E P) :
    (t n : ℕ) → {S : Type} → [MeasurableSpace S] →
    (seed : S → Seed) → Measurable seed → (history : S → Fin n → Response d) → Measurable history →
    (param : S → P) → Measurable param → DecodedProgram E (Space d) (Response d) t S
  | 0, _, _, _, _, _, _, _, _, _ => PUnit.unit
  | t + 1, n, _, _, seed, hs, history, hh, param, hp =>
      (A.decodedRound codec n seed hs history hh param hp,
        A.decodedProgram codec t (n + 1) (seed ∘ Prod.fst) (hs.comp measurable_fst)
          (historyStep n history) (measurable_historyStep n history hh)
          (param ∘ Prod.fst) (hp.comp measurable_fst))

/-- Read the original arbitrary terminal output from the reconstructed full
history. This imposes no requirement that it equal an earlier query. -/
noncomputable def Algorithm.decodedOutput (A : Algorithm d Seed) : (t n : ℕ) → {S : Type} →
    (S → Seed) → (S → Fin n → Response d) → ActionHistory (Response d) t S → Space d
  | 0, n, _, seed, history, s => A.output n (seed s) (history s)
  | t + 1, n, _, seed, history, p =>
      A.decodedOutput t (n + 1) (seed ∘ Prod.fst) (historyStep n history) p

theorem Algorithm.measurable_decodedOutput (A : Algorithm d Seed) (t n : ℕ) {S : Type}
    [MeasurableSpace S] (seed : S → Seed) (hs : Measurable seed)
    (history : S → Fin n → Response d) (hh : Measurable history) :
    Measurable (A.decodedOutput t n seed history) := by
  induction t generalizing n S with
  | zero => exact (A.output_measurable n).comp (hs.prodMk hh)
  | succ t ih =>
    exact ih (n + 1) (seed ∘ Prod.fst) (hs.comp measurable_fst)
      (historyStep n history) (measurable_historyStep n history hh)

theorem Algorithm.decodedOutput_run (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (f : Space d → ℝ) (t n : ℕ) {S : Type} [MeasurableSpace S]
    (seed : S → Seed) (hs : Measurable seed) (history : S → Fin n → Response d) (hh : Measurable history)
    (param : S → P) (hp : Measurable param) (s : S)
    (hhistory : history s = transcript A f (seed s) n) :
    A.decodedOutput t n seed history ((A.decodedProgram codec t n seed hs history hh param hp).run (oracle f) t s) =
      A.output (n + t) (seed s) (transcript A f (seed s) (n + t)) := by
  induction t generalizing n S with
  | zero => simp only [Algorithm.decodedOutput, DecodedProgram.run, Nat.add_zero, hhistory]
  | succ t ih =>
    let s' := (s, oracle f (A.query n (seed s) (history s)))
    have hh' : historyStep n history s' = transcript A f ((seed ∘ Prod.fst) s') (n + 1) := by
      simp only [historyStep, s', Function.comp_apply, transcript, hhistory]
    have hi := ih (n + 1) (seed ∘ Prod.fst) (hs.comp measurable_fst)
      (historyStep n history) (measurable_historyStep n history hh)
      (param ∘ Prod.fst) (hp.comp measurable_fst) s' hh'
    change A.decodedOutput t (n + 1) (seed ∘ Prod.fst) (historyStep n history)
      ((A.decodedProgram codec t (n + 1) (seed ∘ Prod.fst) (hs.comp measurable_fst)
        (historyStep n history) (measurable_historyStep n history hh)
        (param ∘ Prod.fst) (hp.comp measurable_fst)).run (oracle f) t s') = _
    have hnt : n + 1 + t = n + (t + 1) := by omega
    rw [hnt] at hi
    exact hi

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An everywhere-correct public response formula supplies the generic
compiler's pathwise premise; it is never postulated as a new oracle axiom. -/
theorem Algorithm.decodedProgram_correctAlong (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (coordinate : Space d → E) (M U : E →L[ℝ] E) (u : E) (f : Space d → ℝ)
    (t n : ℕ) {S : Type} [MeasurableSpace S] (seed : S → Seed) (hs : Measurable seed)
    (history : S → Fin n → Response d) (hh : Measurable history) (param : S → P) (hp : Measurable param) (s : S)
    (hcodec : ∀ x, codec.response ((param s, x),
      (if codec.authorized (param s, x) = true then U u else 0, U (M (U.adjoint (coordinate x))))) = oracle f x) :
    (A.decodedProgram codec t n seed hs history hh param hp).CorrectAlong coordinate M U u (oracle f) t s := by
  induction t generalizing n S with
  | zero => trivial
  | succ t ih =>
    refine ⟨hcodec _, ?_⟩
    exact ih (n + 1) (seed ∘ Prod.fst) (hs.comp measurable_fst)
      (historyStep n history) (measurable_historyStep n history hh)
      (param ∘ Prod.fst) (hp.comp measurable_fst)
      (s, oracle f (A.query n (seed s) (history s))) hcodec

end RandomizedFO2003.Model
