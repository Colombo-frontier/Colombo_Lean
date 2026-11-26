import FullJet.OracleRestart

namespace FullJet

variable {α E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}

/-- Each failed trial resets using the next private coordinate. Only the
current program and its replies enter the state or stopping decision. -/
def restartStoppingAlgorithm (index : Fin n)
    (trials : α → OracleProgram (Fin n × E) (JetPacket p E) (Option E)) :
    StoppingJetAlgorithm (ℕ → α) E n p where
  core := {
    State := RestartState (Fin n × E) (JetPacket p E) E
    query := fun _ => restartQuery (index, 0)
    update := fun seeds => restartUpdate (fun t => trials (seeds t))
    output := fun _ state => (restartResult state).getD 0
    initial := fun seeds => (0, trials (seeds 0)) }
  halt := fun _ => restartHalt

theorem restartStoppingAlgorithm_state (index : Fin n)
    (trials : α → OracleProgram (Fin n × E) (JetPacket p E) (Option E))
    (f : Fin n → E → ℝ) (seeds : ℕ → α) (q : ℕ) :
    (restartStoppingAlgorithm index trials).state f seeds q =
      oracleRun (restartQuery (index, 0)) (restartUpdate (fun t => trials (seeds t)))
        (fun query => fullJet p (f query.1) query.2) (0, trials (seeds 0)) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [StoppingJetAlgorithm.state_succ, ih]
    change (if restartHalt _ then _ else _) = _
    split
    · exact (restartUpdate_of_halted _ _ _ (by assumption)).symm
    · rfl

theorem restartStoppingAlgorithm_halts (index : Fin n)
    (trials : α → OracleProgram (Fin n × E) (JetPacket p E) (Option E))
    (f : Fin n → E → ℝ) (seeds : ℕ → α) (N : ℕ) (hN : 0 < N)
    (htrials : ∀ a, (trials a).Uses N) (K : ℕ)
    (hfail : ∀ t < K, (trials (seeds t)).eval (fun q => fullJet p (f q.1) q.2) = none)
    {x : E} (hgood : (trials (seeds K)).eval (fun q => fullJet p (f q.1) q.2) = some x) :
    let A := restartStoppingAlgorithm index trials
    A.Halts f seeds ∧ A.stopIndex f seeds ≤ (K + 1) * N ∧ A.stoppedResult f seeds = x := by
  let A := restartStoppingAlgorithm index trials
  have hs : A.state f seeds ((K + 1) * N) = (K, .done (some x)) := by
    rw [restartStoppingAlgorithm_state]
    exact oracleRun_restart_success _ _ _ N hN (fun t => htrials (seeds t)) K hfail hgood
  have hh : A.halt seeds (A.state f seeds ((K + 1) * N)) = true := by rw [hs]; rfl
  have ht : A.Halts f seeds := ⟨_, hh⟩
  have hc := A.stopIndex_le_of_halt f seeds hh
  refine ⟨ht, hc, ?_⟩
  rw [← A.capped_result_eq_stoppedResult f seeds ht hc]
  change (restartResult (A.state f seeds ((K + 1) * N))).getD 0 = x
  rw [hs]
  rfl

/-- Every halted output came from a successful trial, even at query times
inside a trial. This is independent of a prior termination argument. -/
theorem restartStoppingAlgorithm_certified (index : Fin n)
    (trials : α → OracleProgram (Fin n × E) (JetPacket p E) (Option E))
    (f : Fin n → E → ℝ) (valid : E → Prop)
    (hvalid : ∀ a x, (trials a).eval (fun q => fullJet p (f q.1) q.2) = some x → valid x)
    (seeds : ℕ → α) (hhalt : (restartStoppingAlgorithm index trials).Halts f seeds) :
    valid ((restartStoppingAlgorithm index trials).stoppedResult f seeds) := by
  let A := restartStoppingAlgorithm index trials
  let q := A.stopIndex f seeds
  have hh := A.stopIndex_spec f seeds hhalt
  have hi := oracleRun_restart_eval_invariant (fun t => trials (seeds t)) (index, (0 : E))
    (fun query => fullJet p (f query.1) query.2) q
  rw [← restartStoppingAlgorithm_state] at hi
  change (A.state f seeds q).2.eval _ = (trials (seeds (A.state f seeds q).1)).eval _ at hi
  change restartHalt (A.state f seeds q) = true at hh
  change valid ((restartResult (A.state f seeds q)).getD 0)
  rcases hs : A.state f seeds q with ⟨t, P⟩
  rw [hs] at hi hh
  cases P with
  | ask query k => simp [restartHalt, restartResult, OracleProgram.currentOutput] at hh
  | done value =>
    cases value with
    | none => simp [restartHalt, restartResult, OracleProgram.currentOutput] at hh
    | some x => exact hvalid (seeds t) x hi.symm

end FullJet
