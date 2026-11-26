import FullJet.PaddedOracleProgram
import FullJet.StoppingAlgorithm

namespace FullJet

abbrev RestartState (Q R X : Type) := ℕ × OracleProgram Q R (Option X)

variable {Q R X : Type}

/-- A failed completed program resets immediately to the next trial. No
extra reply is charged for this internal transition. -/
def restartResume (trials : ℕ → OracleProgram Q R (Option X)) (t : ℕ)
    (P : OracleProgram Q R (Option X)) : RestartState Q R X :=
  match P with
  | .done none => (t + 1, trials (t + 1))
  | _ => (t, P)

def restartQuery (fallback : Q) (state : RestartState Q R X) : Q := state.2.currentQuery fallback

def restartUpdate (trials : ℕ → OracleProgram Q R (Option X))
    (state : RestartState Q R X) (reply : R) : RestartState Q R X :=
  restartResume trials state.1 (state.2.feed reply)

def restartResult (state : RestartState Q R X) : Option X := state.2.currentOutput none

def restartHalt (state : RestartState Q R X) : Bool := (restartResult state).isSome

theorem restartUpdate_of_halted (trials : ℕ → OracleProgram Q R (Option X))
    (state : RestartState Q R X) (reply : R) (h : restartHalt state = true) :
    restartUpdate trials state reply = state := by
  rcases state with ⟨t, P⟩
  cases P with
  | done x => cases x <;> simp_all [restartHalt, restartResult, restartUpdate, restartResume,
      OracleProgram.currentOutput, OracleProgram.feed]
  | ask q k => simp [restartHalt, restartResult, OracleProgram.currentOutput] at h

/-- One complete program is executed through single replies, with the
failed-trial reset included in its final update. -/
theorem oracleRun_restart_program (trials : ℕ → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (t : ℕ) {P : OracleProgram Q R (Option X)} {N : ℕ}
    (hP : P.Uses N) :
    oracleRun (restartQuery fallback) (restartUpdate trials) oracle (restartResume trials t P) N =
      restartResume trials t (.done (P.eval oracle)) := by
  induction hP with
  | done x => rfl
  | ask q k N next ih =>
    rw [Nat.add_comm N 1, oracleRun_add]
    exact ih (oracle q)

theorem restartResume_of_positive_cost (trials : ℕ → OracleProgram Q R (Option X))
    (t : ℕ) {P : OracleProgram Q R (Option X)} {N : ℕ} (hP : P.Uses N) (hN : 0 < N) :
    restartResume trials t P = (t, P) := by
  cases hP with
  | done x => omega
  | ask q k N next => rfl

theorem oracleRun_restart_trial (trials : ℕ → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (t N : ℕ) (hN : 0 < N) (htrial : (trials t).Uses N) :
    oracleRun (restartQuery fallback) (restartUpdate trials) oracle (t, trials t) N =
      restartResume trials t (.done ((trials t).eval oracle)) := by
  rw [← restartResume_of_positive_cost trials t htrial hN]
  exact oracleRun_restart_program trials fallback oracle t htrial

theorem oracleRun_restart_failures (trials : ℕ → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (N : ℕ) (hN : 0 < N) (htrials : ∀ t, (trials t).Uses N)
    (K : ℕ) (hfail : ∀ t < K, (trials t).eval oracle = none) :
    oracleRun (restartQuery fallback) (restartUpdate trials) oracle (0, trials 0) (K * N) =
      (K, trials K) := by
  induction K with
  | zero => simp only [Nat.zero_mul, oracleRun]
  | succ K ih =>
    rw [Nat.add_mul, Nat.one_mul, oracleRun_add, ih (fun t ht => hfail t (by omega)),
      oracleRun_restart_trial trials fallback oracle K N hN (htrials K), hfail K (by omega)]
    rfl

theorem oracleRun_restart_success (trials : ℕ → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (N : ℕ) (hN : 0 < N) (htrials : ∀ t, (trials t).Uses N)
    (K : ℕ) (hfail : ∀ t < K, (trials t).eval oracle = none) {x : X}
    (hgood : (trials K).eval oracle = some x) :
    oracleRun (restartQuery fallback) (restartUpdate trials) oracle (0, trials 0) ((K + 1) * N) =
      (K, .done (some x)) := by
  rw [Nat.add_mul, Nat.one_mul, oracleRun_add,
    oracleRun_restart_failures trials fallback oracle N hN htrials K hfail,
    oracleRun_restart_trial trials fallback oracle K N hN (htrials K), hgood]
  rfl

/-- The remaining program always has the same answer as its original trial.
This invariant certifies every actual halted output. -/
theorem restartUpdate_eval_invariant (trials : ℕ → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (state : RestartState Q R X)
    (h : state.2.eval oracle = (trials state.1).eval oracle) :
    let next := restartUpdate trials state (oracle (restartQuery fallback state))
    next.2.eval oracle = (trials next.1).eval oracle := by
  have he := state.2.eval_feed fallback oracle
  change (state.2.feed (oracle (restartQuery fallback state))).eval oracle = state.2.eval oracle at he
  unfold restartUpdate
  cases hnext : state.2.feed (oracle (restartQuery fallback state)) with
  | done value =>
    cases value with
    | none => rfl
    | some x =>
      change (OracleProgram.done (some x)).eval oracle = (trials state.1).eval oracle
      rw [hnext] at he
      exact he.trans h
  | ask q k =>
    change (OracleProgram.ask q k).eval oracle = (trials state.1).eval oracle
    rw [hnext] at he
    exact he.trans h

theorem oracleRun_restart_eval_invariant (trials : ℕ → OracleProgram Q R (Option X))
    (fallback : Q) (oracle : Q → R) (q : ℕ) :
    let state := oracleRun (restartQuery fallback) (restartUpdate trials) oracle (0, trials 0) q
    state.2.eval oracle = (trials state.1).eval oracle := by
  induction q with
  | zero => rfl
  | succ q ih => exact restartUpdate_eval_invariant trials fallback oracle _ ih

end FullJet
