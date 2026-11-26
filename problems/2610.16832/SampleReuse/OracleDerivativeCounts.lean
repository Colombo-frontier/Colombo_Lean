import SampleReuse.OracleDerivativeCaps
import SecondOrder.ExactOracleProgram

open SecondOrder

namespace SampleReuse.OracleDerivativeCaps

variable {Q Y O O' Z : Type}

theorem requestCounts_bind_of_exact (flag : Q → Bool) (q₀ : Q)
    (reply : Q → Z → Y) (zs : ℕ → Z) {p : OracleProgram Q Y O} {N : ℕ}
    (hp : OracleProgram.UsesExactly N p) (f : O → OracleProgram Q Y O') {o : O}
    (ho : OracleProgram.run q₀ reply zs p N = .done o) (M : ℕ) :
    requestCounts flag reply (N+M) zs (OracleProgram.bind p f) =
      ((requestCounts flag reply N zs p).1+
        (requestCounts flag reply M (fun i => zs (N+i)) (f o)).1,
       (requestCounts flag reply N zs p).2+
        (requestCounts flag reply M (fun i => zs (N+i)) (f o)).2) := by
  induction N generalizing p zs with
  | zero =>
    cases p with
    | done a =>
      change OracleProgram.done a = .done o at ho
      have he : a=o := OracleProgram.done.inj ho
      subst a
      simp only [OracleProgram.bind_done,requestCounts,Nat.zero_add]
    | request q k => exact False.elim hp
  | succ N ih =>
    cases p with
    | done a => exact False.elim hp
    | request q k =>
      rw [OracleProgram.run_request] at ho
      have hh := ih (fun i => zs (i+1)) (hp (reply q (zs 0))) ho
      rw [show N+1+M=(N+M)+1 by omega]
      simp only [OracleProgram.bind_request,requestCounts]
      rw [hh]
      by_cases hf : flag q = true <;>
        simp [hf,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem requestCounts_batch (flag : Q → Bool) (reply : Q → Z → Y)
    (zs : ℕ → Z) (n : ℕ) (qs : Fin n → Q) (finish : (Fin n → Y) → O)
    (b : Bool) (hb : ∀ i, flag (qs i)=b) :
    requestCounts flag reply n zs (OracleProgram.batch n qs finish) =
      if b then (n,0) else (0,n) := by
  induction n generalizing zs with
  | zero => cases b <;> rfl
  | succ n ih =>
    simp only [OracleProgram.batch,requestCounts]
    rw [ih (fun i => zs (i+1)) (fun i => qs i.succ)
      (fun ys => finish (Fin.cons (reply (qs 0) (zs 0)) ys)) (fun i => hb i.succ),hb 0]
    cases b <;> rfl

end SampleReuse.OracleDerivativeCaps
