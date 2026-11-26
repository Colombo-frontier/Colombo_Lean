import FullJet.OracleProgram

namespace FullJet.OracleProgram

variable {Q R X Y : Type}

/-- A uniform bound over all reply paths. A branch may terminate early. -/
inductive Within : OracleProgram Q R X → ℕ → Prop where
  | done (x : X) (N : ℕ) : Within (.done x) N
  | ask (q : Q) (k : R → OracleProgram Q R X) (N : ℕ)
      (next : ∀ r, Within (k r) N) : Within (.ask q k) (N + 1)

theorem Within.mono {P : OracleProgram Q R X} {N M : ℕ}
    (hP : P.Within N) (hNM : N ≤ M) : P.Within M := by
  induction hP generalizing M with
  | done x N => exact Within.done x M
  | ask q k N next ih =>
    cases M with
    | zero => omega
    | succ M => exact Within.ask q k M (fun r => ih r (by omega))

theorem Uses.within {P : OracleProgram Q R X} {N : ℕ} (hP : P.Uses N) : P.Within N := by
  induction hP with
  | done x => exact Within.done x 0
  | ask q k N next ih => exact Within.ask q k N ih

theorem within_bind {P : OracleProgram Q R X} {N M : ℕ}
    (hP : P.Within N) (f : X → OracleProgram Q R Y) (hf : ∀ x, (f x).Within M) :
    (P.bind f).Within (N + M) := by
  induction hP with
  | done x N => exact (hf x).mono (Nat.le_add_left M N)
  | ask q k N next ih =>
    simpa only [bind, Nat.add_assoc, Nat.add_comm 1 M] using Within.ask q
      (fun r => (k r).bind f) (N + M) ih

theorem run_eq_done_of_within (fallback : Q) (oracle : Q → R)
    {P : OracleProgram Q R X} {N : ℕ} (hP : P.Within N) :
    FullJet.oracleRun (currentQuery fallback) feed oracle P N = .done (P.eval oracle) := by
  induction hP with
  | done x N => exact run_done fallback oracle x N
  | ask q k N next ih =>
    rw [Nat.add_comm N 1, FullJet.oracleRun_add]
    exact ih (oracle q)

end FullJet.OracleProgram

namespace FullJet

variable {Ω E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}

theorem programJetAlgorithm_result_within (index : Fin n)
    (program : Ω → OracleProgram (Fin n × E) (JetPacket p E) E)
    (M : ℕ) (hM : ∀ s, (program s).Within M) (f : Fin n → E → ℝ) (s : Ω) :
    (programJetAlgorithm index program).result M f s =
      (program s).eval (fun q => fullJet p (f q.1) q.2) := by
  unfold JetAlgorithm.result componentJetOutput programJetAlgorithm
  rw [OracleProgram.run_eq_done_of_within (index, 0) _ (hM s)]
  rfl

end FullJet
