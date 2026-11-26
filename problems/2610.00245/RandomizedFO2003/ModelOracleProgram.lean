import RandomizedFO2003.ModelDecoder

namespace RandomizedFO2003.Model

open MeasureTheory Rotations

variable {d : ℕ} {E P Seed : Type} [MeasurableSpace E] [MeasurableSpace P] [MeasurableSpace Seed]

theorem measurable_empty_history :
    Measurable (fun _ : E × (P × Seed) => (Fin.elim0 : Fin 0 → Response d)) :=
  measurable_const

/-- The initial state comprises a latent mark, independent public
parameters, and the original algorithm's private seed. -/
noncomputable def Algorithm.initialDecodedProgram (A : Algorithm d Seed)
    (codec : OracleCodec d E P) (T : ℕ) : DecodedProgram E (Space d) (Response d) T (E × (P × Seed)) :=
  A.decodedProgram codec T 0 (fun p => p.2.2) measurable_snd.snd
    (fun _ => Fin.elim0) measurable_empty_history (fun p => p.2.1) measurable_snd.fst

noncomputable def Algorithm.markedOracleProgram (A : Algorithm d Seed)
    (codec : OracleCodec d E P) (coordinate : Space d → E) (hc : Measurable coordinate) (T : ℕ) :
    MarkedProgram E T (E × (P × Seed)) :=
  (A.initialDecodedProgram codec T).marked coordinate hc T id measurable_id

noncomputable def Algorithm.markedOracleOutput (A : Algorithm d Seed)
    (codec : OracleCodec d E P) (T : ℕ) :
    ActionHistory E (markedActionCount T) (E × (P × Seed)) → Space d :=
  A.decodedOutput T 0 (fun p => p.2.2) (fun _ => Fin.elim0) ∘
    (A.initialDecodedProgram codec T).decode T id

theorem Algorithm.measurable_markedOracleOutput (A : Algorithm d Seed)
    (codec : OracleCodec d E P) (T : ℕ) : Measurable (A.markedOracleOutput codec T) :=
  (A.measurable_decodedOutput T 0 _ measurable_snd.snd _ measurable_empty_history).comp
    ((A.initialDecodedProgram codec T).measurable_decode T id measurable_id)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

/-- The actual fixed-operator execution of the compiled program has exactly
the original model's arbitrary terminal output. -/
theorem Algorithm.markedOracleOutput_run (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (coordinate : Space d → E) (hc : Measurable coordinate) (T : ℕ)
    (M U : E →L[ℝ] E) (u : E) (p : P) (seed : Seed) (f : Space d → ℝ)
    (hcodec : ∀ x, codec.response ((p, x),
      (if codec.authorized (p, x) = true then U u else 0, U (M (U.adjoint (coordinate x))))) = oracle f x) :
    A.markedOracleOutput codec T
      (((A.markedOracleProgram codec coordinate hc T).compile M T Prod.fst measurable_fst).run
        (markedActionCount T) U (u, p, seed)) = A.output T seed (transcript A f seed T) := by
  have hcorrect : (A.initialDecodedProgram codec T).CorrectAlong coordinate M U u (oracle f) T (u, p, seed) :=
    A.decodedProgram_correctAlong codec coordinate M U u f T 0
      (fun q : E × (P × Seed) => q.2.2) measurable_snd.snd (fun _ => Fin.elim0) measurable_empty_history
      (fun q => q.2.1) measurable_snd.fst (u, p, seed) hcodec
  unfold Algorithm.markedOracleOutput Algorithm.markedOracleProgram
  rw [Function.comp_apply, (A.initialDecodedProgram codec T).decode_run T coordinate hc id measurable_id
    M U Prod.fst measurable_fst (oracle f) (u, p, seed) hcorrect]
  have hr := A.decodedOutput_run codec f T 0
    (fun q : E × (P × Seed) => q.2.2) measurable_snd.snd (fun _ => Fin.elim0) measurable_empty_history
    (fun q => q.2.1) measurable_snd.fst (u, p, seed) rfl
  exact hr.trans (congrArg (fun j => A.output j seed (transcript A f seed j)) (Nat.zero_add T))

/-- The appended query is precisely the chosen coordinate of the original
algorithm's output, pulled back by the unknown operator's adjoint. -/
theorem Algorithm.markedOracle_terminal_query (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (coordinate : Space d → E) (hc : Measurable coordinate) (T : ℕ)
    (M U : E →L[ℝ] E) (u : E) (p : P) (seed : Seed) (f : Space d → ℝ)
    (hcodec : ∀ x, codec.response ((p, x),
      (if codec.authorized (p, x) = true then U u else 0, U (M (U.adjoint (coordinate x))))) = oracle f x) :
    markedQueryTrace E (T + 1)
      ((((A.markedOracleProgram codec coordinate hc T).withTerminal T
        (coordinate ∘ A.markedOracleOutput codec T) (hc.comp (A.measurable_markedOracleOutput codec T))).compile
          M (T + 1) Prod.fst measurable_fst).run (markedActionCount (T + 1)) U (u, p, seed)) (Fin.last T) =
      U.adjoint (coordinate (A.output T seed (transcript A f seed T))) := by
  rw [MarkedProgram.withTerminal_last_query]
  simp only [Function.comp_apply]
  rw [A.markedOracleOutput_run codec coordinate hc T M U u p seed f hcodec]

end RandomizedFO2003.Model
