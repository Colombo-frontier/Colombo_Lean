import NCConcave16991.DenseWeakFreshCompilerRun

/-! # Query times before the fresh-row quota belong to the recovered trace -/

namespace NCConcave16991.DenseWeakHiding.FreshCompiler

variable {S : Type*} {n D : ℕ}
  (request : S → Option (Fin n)) (advance : S → Reply D → S)

def actualStep (table : Fin n → Reply D) (s : S) : S :=
  advance s ((request s).elim (zeroReply D) table)

def actualRun (table : Fin n → Reply D) : ℕ → S → S
  | 0,s => s
  | t + 1,s => actualRun table t (actualStep request advance table s)

def readsBefore (table : Fin n → Reply D) : ℕ → S → ℕ
  | 0,_ => 0
  | t + 1,s =>
      (match request s with | none => 0 | some _ => 1) +
        readsBefore table t (actualStep request advance table s)

theorem self_mem_cutTrace (table : Fin n → Reply D) (quota fuel : ℕ) (s : S) :
    s ∈ cutTrace request advance table quota fuel s := by
  cases quota with
  | zero => simp [cutTrace]
  | succ q => cases fuel <;> simp [cutTrace]

/-- Every query-before-response state reached before r fresh rows have been
consumed, including an early terminal output, lies in the actual cut trace. -/
theorem actualRun_mem_cutTrace (table : Fin n → Reply D) (fuel quota t : ℕ) (s : S)
    (ht : t ≤ fuel) (hr : readsBefore request advance table t s < quota) :
    actualRun request advance table t s ∈ cutTrace request advance table quota fuel s := by
  induction t generalizing fuel quota s with
  | zero => exact self_mem_cutTrace request advance table quota fuel s
  | succ t ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases quota with
          | zero => omega
          | succ quota =>
              cases h : request s with
              | none =>
                  have hstep : actualStep request advance table s = advance s (zeroReply D) := by
                    simp [actualStep,h]
                  have hcount : readsBefore request advance table t (advance s (zeroReply D)) < quota + 1 := by
                    simpa only [readsBefore,h,hstep,Nat.zero_add] using hr
                  have hi := ih fuel (quota + 1) (advance s (zeroReply D)) (by omega) hcount
                  simpa only [actualRun,hstep,cutTrace,h,List.mem_cons] using Or.inr hi
              | some i =>
                  have hstep : actualStep request advance table s = advance s (table i) := by
                    simp [actualStep,h]
                  have hcount : readsBefore request advance table t (advance s (table i)) < quota := by
                    simp only [readsBefore,h,hstep] at hr
                    omega
                  have hi := ih fuel quota (advance s (table i)) (by omega) hcount
                  simpa only [actualRun,hstep,cutTrace,h,List.mem_cons] using Or.inr hi

end NCConcave16991.DenseWeakHiding.FreshCompiler
