import FullJet.AlgorithmModel

namespace FullJet

/-- A finite oracle program. Every query continuation receives only its reply;
the oracle itself is not available to the program. -/
inductive OracleProgram (Q R X : Type) : Type where
  | done : X → OracleProgram Q R X
  | ask : Q → (R → OracleProgram Q R X) → OracleProgram Q R X

namespace OracleProgram

variable {Q R X Y : Type}

def eval (oracle : Q → R) : OracleProgram Q R X → X
  | .done x => x
  | .ask q k => eval oracle (k (oracle q))

def bind : OracleProgram Q R X → (X → OracleProgram Q R Y) → OracleProgram Q R Y
  | .done x, f => f x
  | .ask q k, f => .ask q (fun r => bind (k r) f)

/-- Exact query count on every possible reply path, including replies that
do not arise from an admissible function. -/
inductive Uses : OracleProgram Q R X → ℕ → Prop where
  | done (x : X) : Uses (.done x) 0
  | ask (q : Q) (k : R → OracleProgram Q R X) (N : ℕ)
      (next : ∀ r, Uses (k r) N) : Uses (.ask q k) (N + 1)

theorem eval_bind (oracle : Q → R) (P : OracleProgram Q R X)
    (f : X → OracleProgram Q R Y) :
    (P.bind f).eval oracle = (f (P.eval oracle)).eval oracle := by
  induction P with
  | done x => rfl
  | ask q k ih => exact ih (oracle q)

theorem uses_bind {P : OracleProgram Q R X} {N M : ℕ}
    (hP : P.Uses N) (f : X → OracleProgram Q R Y) (hf : ∀ x, (f x).Uses M) :
    (P.bind f).Uses (N + M) := by
  induction hP with
  | done x => simpa only [bind, Nat.zero_add] using hf x
  | ask q k N next ih =>
    simpa only [bind, Nat.add_assoc, Nat.add_comm 1 M] using Uses.ask q
      (fun r => (k r).bind f) (N + M) ih

def currentQuery (fallback : Q) : OracleProgram Q R X → Q
  | .done _ => fallback
  | .ask q _ => q

def feed : OracleProgram Q R X → R → OracleProgram Q R X
  | .done x, _ => .done x
  | .ask _ k, r => k r

def currentOutput (fallback : X) : OracleProgram Q R X → X
  | .done x => x
  | .ask _ _ => fallback

theorem run_done (fallback : Q) (oracle : Q → R) (x : X) (N : ℕ) :
    oracleRun (currentQuery fallback) feed oracle (.done x) N = .done x := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [oracleRun, ih, feed]

theorem run_eq_done (fallback : Q) (oracle : Q → R) {P : OracleProgram Q R X}
    {N : ℕ} (hP : P.Uses N) :
    oracleRun (currentQuery fallback) feed oracle P N = .done (P.eval oracle) := by
  induction hP with
  | done x => rfl
  | ask q k N next ih =>
    rw [Nat.add_comm N 1, oracleRun_add]
    exact ih (oracle q)

theorem run_eq_done_of_le (fallback : Q) (oracle : Q → R) {P : OracleProgram Q R X}
    {N M : ℕ} (hP : P.Uses N) (hNM : N ≤ M) :
    oracleRun (currentQuery fallback) feed oracle P M = .done (P.eval oracle) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [oracleRun_add, run_eq_done fallback oracle hP, run_done]

/-- Read a fixed finite family of requests, retaining all actual replies. -/
def collect : (N : ℕ) → (Fin N → Q) → OracleProgram Q R (Fin N → R)
  | 0, _ => .done Fin.elim0
  | N + 1, q => (collect N (Fin.init q)).bind fun replies =>
      .ask (q (Fin.last N)) (fun r => .done (Fin.snoc replies r))

theorem collect_uses (N : ℕ) (q : Fin N → Q) : (collect (R := R) N q).Uses N := by
  induction N with
  | zero => exact Uses.done _
  | succ N ih =>
    exact uses_bind (ih (Fin.init q)) _ (fun replies => Uses.ask _ _ 0 (fun r => Uses.done _))

theorem eval_collect (oracle : Q → R) (N : ℕ) (q : Fin N → Q) :
    (collect N q).eval oracle = fun i => oracle (q i) := by
  induction N with
  | zero => exact Subsingleton.elim _ _
  | succ N ih =>
    simp only [collect, eval_bind, ih, eval]
    exact Fin.snoc_init_self (fun i => oracle (q i))

end OracleProgram

variable {Ω E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}

/-- Compile a reply-only program into the original one-query state machine.
After completion, further queries preserve the result. -/
def programJetAlgorithm (index : Fin n)
    (program : Ω → OracleProgram (Fin n × E) (JetPacket p E) E) : JetAlgorithm Ω E n p where
  State := OracleProgram (Fin n × E) (JetPacket p E) E
  query := fun _ => OracleProgram.currentQuery (index, 0)
  update := fun _ => OracleProgram.feed
  output := fun _ => OracleProgram.currentOutput 0
  initial := program

theorem programJetAlgorithm_result (index : Fin n)
    (program : Ω → OracleProgram (Fin n × E) (JetPacket p E) E)
    (N M : ℕ) (hN : ∀ s, (program s).Uses N) (hNM : N ≤ M)
    (f : Fin n → E → ℝ) (s : Ω) :
    (programJetAlgorithm index program).result M f s =
      (program s).eval (fun q => fullJet p (f q.1) q.2) := by
  unfold JetAlgorithm.result componentJetOutput programJetAlgorithm
  rw [OracleProgram.run_eq_done_of_le (index, 0) _ (hN s) hNM]
  rfl

theorem programJetAlgorithm_result_at (index : Fin n)
    (program : Ω → OracleProgram (Fin n × E) (JetPacket p E) E)
    (f : Fin n → E → ℝ) (s : Ω) (N M : ℕ)
    (hN : (program s).Uses N) (hNM : N ≤ M) :
    (programJetAlgorithm index program).result M f s =
      (program s).eval (fun q => fullJet p (f q.1) q.2) := by
  unfold JetAlgorithm.result componentJetOutput programJetAlgorithm
  rw [OracleProgram.run_eq_done_of_le (index, 0) _ hN hNM]
  rfl

end FullJet
