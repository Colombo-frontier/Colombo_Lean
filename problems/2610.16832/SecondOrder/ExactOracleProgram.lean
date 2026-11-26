import SecondOrder.OracleProgramComposition

namespace SecondOrder
namespace OracleProgram

variable {Q Y O O' Z : Type}

/-- Every possible reply branch uses exactly this many fresh calls. -/
def UsesExactly : ℕ → OracleProgram Q Y O → Prop
  | 0, .done _ => True
  | _+1, .done _ => False
  | 0, .request _ _ => False
  | n+1, .request _ k => ∀ y, UsesExactly n (k y)

theorem UsesExactly.usesAtMost {N : ℕ} {p : OracleProgram Q Y O} (h : UsesExactly N p) :
    UsesAtMost N p := by
  induction N generalizing p with
  | zero => cases p <;> simpa only [UsesExactly,UsesAtMost] using h
  | succ N ih =>
    cases p with
    | done o => exact False.elim h
    | request q k => exact fun y => ih (h y)

theorem UsesExactly.advance {N : ℕ} {p : OracleProgram Q Y O} (h : UsesExactly (N+1) p)
    (y : Y) : UsesExactly N (advance p y) := by
  cases p with
  | done o => exact False.elim h
  | request q k => exact h y

theorem UsesExactly.finished_false {N : ℕ} {p : OracleProgram Q Y O}
    (h : UsesExactly N p) (hN : 0<N) : finished p=false := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  cases p with
  | done o => exact False.elim h
  | request q k => rfl

theorem UsesExactly.run (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    {N : ℕ} {p : OracleProgram Q Y O} (h : UsesExactly N p) (n : ℕ) (hn : n≤N) :
    UsesExactly (N-n) (run q₀ reply zs p n) := by
  induction n with
  | zero => simpa only [OracleProgram.run,Nat.sub_zero] using h
  | succ n ih =>
    have hh := ih (by omega)
    rw [show N-n=N-(n+1)+1 by omega] at hh
    exact hh.advance _

theorem UsesExactly.bind {N M : ℕ} {p : OracleProgram Q Y O} (h : UsesExactly N p)
    (f : O → OracleProgram Q Y O') (hf : ∀ o, UsesExactly M (f o)) :
    UsesExactly (N+M) (bind p f) := by
  induction N generalizing p with
  | zero =>
    cases p with
    | done o => simpa only [bind_done,Nat.zero_add] using hf o
    | request q k => exact False.elim h
  | succ N ih =>
    cases p with
    | done o => exact False.elim h
    | request q k =>
      rw [bind_request,show N+1+M=N+M+1 by omega]
      exact fun y => ih (h y)

theorem run_add (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    (p : OracleProgram Q Y O) (n m : ℕ) :
    run q₀ reply zs p (n+m)=run q₀ reply (fun i => zs (n+i)) (run q₀ reply zs p n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact congrArg (fun s : OracleProgram Q Y O => advance s (reply (query q₀ s) (zs (n+m)))) ih

theorem run_bind_prefix (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    {p : OracleProgram Q Y O} {N : ℕ} (h : UsesExactly N p)
    (f : O → OracleProgram Q Y O') (n : ℕ) (hn : n≤N) :
    run q₀ reply zs (bind p f) n=bind (run q₀ reply zs p n) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh := (h.run q₀ reply zs n (by omega)).finished_false (by omega)
    simp only [run]
    rw [ih (by omega)]
    cases hs : run q₀ reply zs p n with
    | done o => simp [hs,finished] at hh
    | request q k => rfl

/-- Sequential execution consumes disjoint consecutive sample blocks. The
second program sees the first program's output and starts at the next sample. -/
theorem run_bind_of_exact (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    {p : OracleProgram Q Y O} {N : ℕ} (h : UsesExactly N p)
    (f : O → OracleProgram Q Y O') {o : O} (ho : run q₀ reply zs p N=.done o) (M : ℕ) :
    run q₀ reply zs (bind p f) (N+M)=run q₀ reply (fun i => zs (N+i)) (f o) M := by
  rw [run_add,run_bind_prefix q₀ reply zs h f N le_rfl,ho,bind_done]

theorem batch_usesExactly (n : ℕ) (qs : Fin n → Q) (finish : (Fin n → Y) → O) :
    UsesExactly n (batch n qs finish) := by
  induction n with
  | zero => trivial
  | succ n ih => exact fun y => ih _ _

theorem iterateQueries_usesExactly {S : Type} (q : S → Q) (update : S → Y → S) (finish : S → O)
    (n : ℕ) (s : S) : UsesExactly n (iterateQueries q update finish n s) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih => exact fun y => ih (update s y)

end OracleProgram
end SecondOrder
