import SecondOrder.OracleAlgorithm

namespace SecondOrder

/-- A reply-driven oracle program. Its only external operation is one query;
the continuation receives the reply, never the hidden sample or its law. -/
inductive OracleProgram (Q Y O : Type*) where
  | done : O → OracleProgram Q Y O
  | request : Q → (Y → OracleProgram Q Y O) → OracleProgram Q Y O

namespace OracleProgram

variable {Q Y O O' Z : Type*}

def bind (p : OracleProgram Q Y O) (f : O → OracleProgram Q Y O') : OracleProgram Q Y O' :=
  match p with
  | .done o => f o
  | .request q k => .request q (fun y => bind (k y) f)

@[simp] theorem bind_done (o : O) (f : O → OracleProgram Q Y O') : bind (.done o) f=f o := rfl

@[simp] theorem bind_request (q : Q) (k : Y → OracleProgram Q Y O)
    (f : O → OracleProgram Q Y O') : bind (.request q k) f=.request q (fun y => bind (k y) f) := rfl

theorem bind_right_identity (p : OracleProgram Q Y O) : bind p .done=p := by
  induction p with
  | done o => rfl
  | request q k ih => simp only [bind_request,ih]

theorem bind_assoc {O'' : Type*} (p : OracleProgram Q Y O)
    (f : O → OracleProgram Q Y O') (g : O' → OracleProgram Q Y O'') :
    bind (bind p f) g=bind p (fun o => bind (f o) g) := by
  induction p with
  | done o => rfl
  | request q k ih => simp only [bind_request,ih]

def query (q₀ : Q) : OracleProgram Q Y O → Q
  | .done _ => q₀
  | .request q _ => q

def output (o₀ : O) : OracleProgram Q Y O → O
  | .done o => o
  | .request _ _ => o₀

def advance : OracleProgram Q Y O → Y → OracleProgram Q Y O
  | .done o, _ => .done o
  | .request _ k, y => k y

/-- Read exactly the available reply prefix; no future coordinate is used. -/
def readAnswers (p : OracleProgram Q Y O) (ys : ℕ → Y) : ℕ → OracleProgram Q Y O
  | 0 => p
  | n+1 => advance (readAnswers p ys n) (ys n)

theorem readAnswers_congr (p : OracleProgram Q Y O) (ys zs : ℕ → Y) (n : ℕ)
    (h : ∀ i, i<n → ys i=zs i) : readAnswers p ys n=readAnswers p zs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [readAnswers,readAnswers,ih (fun i hi => h i (by omega)),h n (by omega)]

theorem readAnswers_update (p : OracleProgram Q Y O) (ys : ℕ → Y) (n : ℕ) (y : Y) :
    readAnswers p (Function.update ys n y) n=readAnswers p ys n := by
  apply readAnswers_congr
  intro i hi
  exact Function.update_of_ne (by omega) _ _

def run (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z) (p : OracleProgram Q Y O) :
    ℕ → OracleProgram Q Y O
  | 0 => p
  | n+1 =>
    let s := run q₀ reply zs p n
    advance s (reply (query q₀ s) (zs n))

/-- Compile to the established adaptive algorithm interface. Its memory is
only a sequence of received replies; idle calls after completion are ignored. -/
def algorithm (q₀ : Q) (y₀ : Y) (o₀ : O) (p : OracleProgram Q Y O) :
    OracleAlgorithm Q Y O (ℕ → Y) where
  initial := fun _ => y₀
  query n ys := query q₀ (readAnswers p ys n)
  update n ys y := Function.update ys n y
  output n ys := output o₀ (readAnswers p ys n)

theorem algorithm_run (q₀ : Q) (y₀ : Y) (o₀ : O) (p : OracleProgram Q Y O)
    (reply : Q → Z → Y) (zs : ℕ → Z) (n : ℕ) :
    readAnswers p (queryPolicyRun (algorithm q₀ y₀ o₀ p).toQueryPolicy reply zs n) n=
      run q₀ reply zs p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [queryPolicyRun,algorithm,readAnswers]
    simp only [algorithm] at ih
    rw [readAnswers_update,Function.update_self,ih]
    rfl

theorem algorithm_output (q₀ : Q) (y₀ : Y) (o₀ : O) (p : OracleProgram Q Y O)
    (reply : Q → Z → Y) (zs : ℕ → Z) (n : ℕ) :
    oracleAlgorithmOutput (algorithm q₀ y₀ o₀ p) reply zs n=output o₀ (run q₀ reply zs p n) := by
  unfold oracleAlgorithmOutput
  change output o₀ (readAnswers p _ n)=_
  rw [algorithm_run]

/-- Uniform branchwise call bound, including replies of probability zero. -/
def UsesAtMost : ℕ → OracleProgram Q Y O → Prop
  | _, .done _ => True
  | 0, .request _ _ => False
  | n+1, .request _ k => ∀ y, UsesAtMost n (k y)

theorem usesAtMost_mono {n m : ℕ} {p : OracleProgram Q Y O}
    (h : UsesAtMost n p) (hnm : n≤m) : UsesAtMost m p := by
  induction n generalizing m p with
  | zero => cases p <;> simpa only [UsesAtMost] using h
  | succ n ih =>
    cases p with
    | done o => simp only [UsesAtMost]
    | request q k =>
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m≠0 by omega)
      exact fun y => ih (h y) (by omega)

theorem usesAtMost_bind {n m : ℕ} {p : OracleProgram Q Y O} (h : UsesAtMost n p)
    (f : O → OracleProgram Q Y O') (hf : ∀ o, UsesAtMost m (f o)) :
    UsesAtMost (n+m) (bind p f) := by
  induction n generalizing p with
  | zero =>
    cases p with
    | done o => simpa only [bind_done,Nat.zero_add] using hf o
    | request q k => exact False.elim h
  | succ n ih =>
    cases p with
    | done o => exact usesAtMost_mono (hf o) (by omega)
    | request q k =>
      rw [show n+1+m=n+m+1 by omega,bind_request]
      exact fun y => ih (h y)

theorem usesAtMost_advance {n : ℕ} {p : OracleProgram Q Y O}
    (h : UsesAtMost (n+1) p) (y : Y) : UsesAtMost n (advance p y) := by
  cases p with
  | done o => simp only [advance,UsesAtMost]
  | request q k => exact h y

theorem usesAtMost_run (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    {p : OracleProgram Q Y O} {N : ℕ} (h : UsesAtMost N p) (n : ℕ) :
    UsesAtMost (N-n) (run q₀ reply zs p n) := by
  induction n with
  | zero => simpa only [run,Nat.sub_zero] using h
  | succ n ih =>
    by_cases hn : n<N
    · have he : N-n=(N-(n+1))+1 := by omega
      rw [he] at ih
      exact usesAtMost_advance ih _
    · have he : N-n=0 := by omega
      rw [he] at ih
      cases hs : run q₀ reply zs p n with
      | done o => simp only [run,hs,advance,UsesAtMost]
      | request q k => simp only [hs,UsesAtMost] at ih

theorem run_done (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    {p : OracleProgram Q Y O} {N : ℕ} (h : UsesAtMost N p) :
    ∃ o, run q₀ reply zs p N=.done o := by
  have hh := usesAtMost_run q₀ reply zs h N
  rw [Nat.sub_self] at hh
  cases hs : run q₀ reply zs p N with
  | done o => exact ⟨o,rfl⟩
  | request q k => simp only [hs,UsesAtMost] at hh

end OracleProgram
end SecondOrder
