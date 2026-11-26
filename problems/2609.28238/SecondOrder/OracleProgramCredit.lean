import SecondOrder.ExactOracleProgram

namespace SecondOrder
namespace OracleProgram

variable {Q Y O O' : Type}

/-- Charged queries plus the credit reserved for the continuation fit in
the initial budget on every possible reply branch. -/
def UsesWithCredit (n : ℕ) (p : OracleProgram Q Y O) (credit : O → ℕ) : Prop :=
  match p with
  | .done o => credit o≤n
  | .request _ k => match n with
    | 0 => False
    | n+1 => ∀ y, UsesWithCredit n (k y) credit
termination_by structural p

theorem UsesWithCredit.mono {n m : ℕ} {p : OracleProgram Q Y O} {credit : O → ℕ}
    (h : UsesWithCredit n p credit) (hnm : n≤m) : UsesWithCredit m p credit := by
  induction n generalizing m p with
  | zero =>
    cases p with
    | done o => exact h.trans hnm
    | request q k => exact False.elim h
  | succ n ih =>
    cases p with
    | done o => exact h.trans hnm
    | request q k =>
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m≠0 by omega)
      exact fun y => ih (h y) (by omega)

theorem UsesWithCredit.usesAtMost {n : ℕ} {p : OracleProgram Q Y O} {credit : O → ℕ}
    (h : UsesWithCredit n p credit) : UsesAtMost n p := by
  induction n generalizing p with
  | zero => cases p <;> trivial
  | succ n ih =>
    cases p with
    | done o => trivial
    | request q k => exact fun y => ih (h y)

theorem UsesWithCredit.bind {n : ℕ} {p : OracleProgram Q Y O} {credit : O → ℕ}
    (h : UsesWithCredit n p credit) (f : O → OracleProgram Q Y O') (out : O' → ℕ)
    (hf : ∀ o, UsesWithCredit (credit o) (f o) out) : UsesWithCredit n (bind p f) out := by
  induction n generalizing p with
  | zero =>
    cases p with
    | done o => exact (hf o).mono h
    | request q k => exact False.elim h
  | succ n ih =>
    cases p with
    | done o => exact (hf o).mono h
    | request q k => exact fun y => ih (h y)

theorem usesAtMost_bind_credit {n m : ℕ} {p : OracleProgram Q Y O} (h : UsesAtMost n p)
    (f : O → OracleProgram Q Y O') (out : O' → ℕ)
    (hf : ∀ o, UsesWithCredit m (f o) out) : UsesWithCredit (n+m) (bind p f) out := by
  induction n generalizing p with
  | zero =>
    cases p with
    | done o => simpa only [bind_done,Nat.zero_add] using hf o
    | request q k => exact False.elim h
  | succ n ih =>
    cases p with
    | done o => exact (hf o).mono (by omega)
    | request q k =>
      rw [show n+1+m=n+m+1 by omega,bind_request]
      exact fun y => ih (h y)

end OracleProgram
end SecondOrder
