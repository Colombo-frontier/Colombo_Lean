import GradientHessian.DisclosureStopping

/-! Exact finite-state iteration and resource sums for disclosure programs.
Halted states are fixed, so all identities hold beyond the stopping time. -/

noncomputable section
namespace GradientHessian.DisclosureCompiler
open Classical Matrix

variable {d : ℕ} {S : Type*} [MeasurableSpace S]

def Program.tick (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) (s : S) : S :=
  if P.mode s=0 then s else if P.mode s=1 then P.think s
  else if P.mode s=2 then P.next (s,A*ᵥP.query s)
  else P.disclosed (s,readout (P.mark s))

variable (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
  (readout : (Fin d → ℝ) → Fin d → ℝ)

theorem Program.tick_halted {s : S} (hs : P.mode s=0) : P.tick A readout s=s := by
  simp [tick,hs]

theorem Program.iterate_halted {s : S} (hs : P.mode s=0) (N : ℕ) : (P.tick A readout)^[N] s=s :=
  Function.iterate_fixed (P.tick_halted A readout hs) N

theorem Program.eval_eq_terminal_tick_iterate (N : ℕ) (s : S) :
    P.eval A readout N s=P.terminal.1 ((P.tick A readout)^[N] s) := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    by_cases h0 : P.mode s=0
    · rw [P.iterate_halted A readout h0]
      simp [eval,h0]
    · rw [Function.iterate_succ_apply]
      simp only [eval,tick,h0,if_false]
      split_ifs <;> exact ih _

theorem Program.eval_state_iterate (N : ℕ) (s : S) :
    (P.eval A readout N s).2=(P.tick A readout)^[N] s := by
  rw [P.eval_eq_terminal_tick_iterate]
  rfl

theorem Program.eval_flag_iterate (N : ℕ) (s : S) :
    (P.eval A readout N s).1=true ↔ P.mode ((P.tick A readout)^[N] s)=0 := by
  rw [P.eval_eq_terminal_tick_iterate]
  simp [terminal,flag]

theorem Program.ordinaryCalls_halted {s : S} (hs : P.mode s=0) (N : ℕ) :
    P.ordinaryCalls A readout N s=0 := by
  cases N <;> simp [ordinaryCalls,hs]

theorem Program.disclosures_halted {s : S} (hs : P.mode s=0) (N : ℕ) :
    P.disclosures A readout N s=0 := by
  cases N <;> simp [disclosures,hs]

theorem Program.ordinaryCalls_succ_tick (N : ℕ) (s : S) :
    P.ordinaryCalls A readout (N+1) s=
      (if P.mode s=2 then 1 else 0)+P.ordinaryCalls A readout N (P.tick A readout s) := by
  by_cases h0 : P.mode s=0
  · simp [ordinaryCalls,tick,h0,P.ordinaryCalls_halted A readout h0]
  by_cases h1 : P.mode s=1
  · simp [ordinaryCalls,tick,h0,h1]
  by_cases h2 : P.mode s=2
  · simp [ordinaryCalls,tick,h0,h1,h2,Nat.add_comm]
  · simp [ordinaryCalls,tick,h0,h1,h2]

theorem Program.disclosures_succ_tick (N : ℕ) (s : S) :
    P.disclosures A readout (N+1) s=
      (if P.mode s=3 then 1 else 0)+P.disclosures A readout N (P.tick A readout s) := by
  by_cases h0 : P.mode s=0
  · simp [disclosures,tick,h0,P.disclosures_halted A readout h0]
  by_cases h1 : P.mode s=1
  · simp [disclosures,tick,h0,h1]
  by_cases h2 : P.mode s=2
  · simp [disclosures,tick,h0,h1,h2]
  · have h3 : P.mode s=3 := by omega
    simp [disclosures,tick,h0,h1,h2,h3,Nat.add_comm]

theorem Program.ordinaryCalls_eq_sum (N : ℕ) (s : S) :
    P.ordinaryCalls A readout N s=
      ∑ i∈Finset.range N,if P.mode ((P.tick A readout)^[i] s)=2 then 1 else 0 := by
  induction N generalizing s with
  | zero => simp [ordinaryCalls]
  | succ N ih =>
    rw [P.ordinaryCalls_succ_tick,Finset.sum_range_succ']
    simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,ih]
    omega

theorem Program.disclosures_eq_sum (N : ℕ) (s : S) :
    P.disclosures A readout N s=
      ∑ i∈Finset.range N,if P.mode ((P.tick A readout)^[i] s)=3 then 1 else 0 := by
  induction N generalizing s with
  | zero => simp [disclosures]
  | succ N ih =>
    rw [P.disclosures_succ_tick,Finset.sum_range_succ']
    simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,ih]
    omega

end GradientHessian.DisclosureCompiler
