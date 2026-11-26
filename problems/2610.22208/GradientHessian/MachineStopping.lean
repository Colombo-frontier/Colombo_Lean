import GradientHessian.MachineCompiler

/-! Removing internal-time cutoffs for the actual machine recursion. A run
that never halts has no output and is represented by the explicit false flag. -/

namespace GradientHessian.MachineCompiler

open MeasureTheory Filter
open scoped Topology
noncomputable section

variable {d : ℕ} {State O : Type*} [MeasurableSpace State] [MeasurableSpace O]

theorem Program.eval_eq_terminal_iterate (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    P.eval oracle n s = P.terminal ((P.step oracle)^[n] s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases h0 : P.mode s = 0
    · have hf : ∀ i, (P.step oracle)^[i] s = s :=
        Function.iterate_fixed (by simp [Program.step, h0])
      simp [Program.eval, h0, hf]
    · rw [Function.iterate_succ_apply]
      by_cases h1 : P.mode s = 1
      · simpa [Program.eval, Program.step, h0, h1] using ih (P.think s)
      · simpa [Program.eval, Program.step, h0, h1] using
          ih (P.next (s, oracle (P.query s)))

theorem Program.iterate_after_halt (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n m : ℕ) (s : State)
    (hh : P.mode ((P.step oracle)^[n] s) = 0) (hm : n ≤ m) :
    (P.step oracle)^[m] s = (P.step oracle)^[n] s := by
  have he : m = (m - n) + n := (Nat.sub_add_cancel hm).symm
  rw [he, Function.iterate_add_apply]
  apply Function.iterate_fixed
  simp [Program.step, hh]

def Program.stoppedResult (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : State) : Bool × O := by
  classical
  exact if h : ∃ n, P.mode ((P.step oracle)^[n] s) = 0 then
    (true, P.output ((P.step oracle)^[Nat.find h] s))
  else (false, P.fallback)

theorem Program.stoppedResult_at_halt (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State)
    (hh : P.mode ((P.step oracle)^[n] s) = 0) :
    P.stoppedResult oracle s = (true, P.output ((P.step oracle)^[n] s)) := by
  have hex : ∃ n, P.mode ((P.step oracle)^[n] s) = 0 := ⟨n, hh⟩
  rw [Program.stoppedResult, dif_pos hex]
  rw [P.iterate_after_halt oracle (Nat.find hex) n s (Nat.find_spec hex) (Nat.find_min' hex hh)]

/-- The cutoff sequence is eventually constant at the actual first-halt
output. This also holds for a nonhalting run, whose output flag stays false. -/
theorem Program.eventually_eval_eq_stopped (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : State) :
    ∀ᶠ n in atTop, P.eval oracle n s = P.stoppedResult oracle s := by
  by_cases hex : ∃ n, P.mode ((P.step oracle)^[n] s) = 0
  · filter_upwards [eventually_ge_atTop (Nat.find hex)] with n hn
    rw [P.eval_eq_terminal_iterate,
      P.iterate_after_halt oracle (Nat.find hex) n s (Nat.find_spec hex) hn,
      Program.terminal, if_pos (Nat.find_spec hex), Program.stoppedResult, dif_pos hex]
  · apply Filter.Eventually.of_forall
    intro n
    rw [P.eval_eq_terminal_iterate, Program.terminal, if_neg (fun h => hex ⟨n, h⟩),
      Program.stoppedResult, dif_neg hex]

theorem Program.eval_output_property (P : Program d State O) (R : O → Prop)
    (hout : ∀ s, R (P.output s)) (oracle : (Fin d → ℝ) → Fin d → ℝ)
    (n : ℕ) (s : State) : (P.eval oracle n s).1 = true → R (P.eval oracle n s).2 := by
  rw [P.eval_eq_terminal_iterate]
  exact P.terminal_property R hout _

end
end GradientHessian.MachineCompiler
