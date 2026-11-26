import GradientHessian.Machine
import LowRank.StoppingGramSimulation

/-!
# Compiling internal computation into bounded matrix-oracle policies

The fuel is an internal-time cutoff, separate from the query budget. The
compiler skips internal steps without charging matrix products, stops on a
halt or exhausted fuel, and enforces the query cap on every counterfactual
reply history. An explicit Boolean distinguishes genuine outputs from cutoffs.
-/

namespace GradientHessian.MachineCompiler

open MeasureTheory Matrix LowRank
noncomputable section
universe u v w

structure Program (d : ℕ) (State : Type u) (O : Type v)
    [MeasurableSpace State] [MeasurableSpace O] where
  mode : State → Fin 3
  think : State → State
  query : State → Fin d → ℝ
  next : State × (Fin d → ℝ) → State
  output : State → O
  fallback : O
  mode_measurable : Measurable mode
  think_measurable : Measurable think
  query_measurable : Measurable query
  next_measurable : Measurable next
  output_measurable : Measurable output

variable {d : ℕ} {State : Type u} {O : Type v}
  [MeasurableSpace State] [MeasurableSpace O]

def Program.terminal (P : Program d State O) (s : State) : Bool × O :=
  if P.mode s = 0 then (true, P.output s) else (false, P.fallback)

theorem Program.terminal_measurable (P : Program d State O) :
    Measurable P.terminal := by
  exact Measurable.ite (P.mode_measurable (measurableSet_singleton 0))
    (measurable_const.prodMk P.output_measurable) measurable_const

def Program.eval (P : Program d State O) (oracle : (Fin d → ℝ) → Fin d → ℝ) :
    ℕ → State → Bool × O
  | 0, s => P.terminal s
  | n + 1, s => if P.mode s = 0 then P.terminal s
      else if P.mode s = 1 then P.eval oracle n (P.think s)
      else P.eval oracle n (P.next (s, oracle (P.query s)))

def Program.calls (P : Program d State O) (oracle : (Fin d → ℝ) → Fin d → ℝ) :
    ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => if P.mode s = 0 then 0
      else if P.mode s = 1 then P.calls oracle n (P.think s)
      else P.calls oracle n (P.next (s, oracle (P.query s))) + 1

/-- Skip only internal steps; retain both the remaining fuel and actual state. -/
def Program.advance (P : Program d State O) : ℕ → State → ℕ × State
  | 0, s => (0, s)
  | n + 1, s => if P.mode s = 1 then P.advance n (P.think s) else (n + 1, s)

theorem Program.advance_measurable (P : Program d State O) (n : ℕ) :
    Measurable (P.advance n) := by
  induction n with
  | zero => exact measurable_const.prodMk measurable_id
  | succ n ih =>
    exact Measurable.ite (P.mode_measurable (measurableSet_singleton 1))
      (ih.comp P.think_measurable) (measurable_const.prodMk measurable_id)

theorem Program.advance_joint_measurable (P : Program d State O) :
    Measurable (fun c : ℕ × State => P.advance c.1 c.2) := by
  have h : Measurable (fun c : State × ℕ => P.advance c.2 c.1) :=
    measurable_from_prod_countable P.advance_measurable
  exact h.comp measurable_swap

theorem Program.advance_ready (P : Program d State O) (n : ℕ) (s : State) :
    (P.advance n s).1 = 0 ∨ P.mode (P.advance n s).2 ≠ 1 := by
  induction n generalizing s with
  | zero => exact Or.inl rfl
  | succ n ih =>
    simp only [Program.advance]
    split_ifs with h
    · exact ih _
    · exact Or.inr h

theorem Program.eval_advance (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    P.eval oracle (P.advance n s).1 (P.advance n s).2 = P.eval oracle n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases h : P.mode s = 1
    · have h0 : P.mode s ≠ 0 := by omega
      simpa [Program.advance, Program.eval, h, h0] using ih (P.think s)
    · simp [Program.advance, h]

theorem Program.calls_advance (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    P.calls oracle (P.advance n s).1 (P.advance n s).2 = P.calls oracle n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases h : P.mode s = 1
    · have h0 : P.mode s ≠ 0 := by omega
      simpa [Program.advance, Program.calls, h, h0] using ih (P.think s)
    · simp [Program.advance, h]

def Program.ready (P : Program d State O) {S : Type w} [MeasurableSpace S]
    (c : MeasurableStateMap S (ℕ × State)) : MeasurableStateMap S (ℕ × State) :=
  ⟨fun x => P.advance (c.1 x).1 (c.1 x).2, P.advance_joint_measurable.comp c.2⟩

def Program.stage (P : Program d State O) {S : Type w} [MeasurableSpace S]
    (c : MeasurableStateMap S (ℕ × State)) : StoppingOracleStage d S (Bool × O) where
  stop := ⟨fun x => if ((P.ready c).1 x).1 = 0 ∨ P.mode ((P.ready c).1 x).2 = 0
      then true else false, by
    apply Measurable.ite
    · exact ((P.ready c).2.fst (measurableSet_singleton 0)).union
        ((P.mode_measurable.comp (P.ready c).2.snd) (measurableSet_singleton 0))
    · exact measurable_const
    · exact measurable_const⟩
  output := ⟨fun x => P.terminal ((P.ready c).1 x).2,
    P.terminal_measurable.comp (P.ready c).2.snd⟩
  query := ⟨fun x => (false, P.query ((P.ready c).1 x).2),
    measurable_const.prodMk (P.query_measurable.comp (P.ready c).2.snd)⟩

def Program.continueWith (P : Program d State O) {S : Type w} [MeasurableSpace S]
    (c : MeasurableStateMap S (ℕ × State)) :
    MeasurableStateMap (S × (Fin d → ℝ)) (ℕ × State) :=
  ⟨fun x => (((P.ready c).1 x.1).1 - 1, P.next (((P.ready c).1 x.1).2, x.2)),
    (((P.ready c).2.comp measurable_fst).fst.sub measurable_const).prodMk
      (P.next_measurable.comp (((P.ready c).2.comp measurable_fst).snd.prodMk measurable_snd))⟩

def Program.compile (P : Program d State O) : (q : ℕ) →
    {S : Type w} → [MeasurableSpace S] → MeasurableStateMap S (ℕ × State) →
      BoundedTwoSidedPolicy d (Bool × O) q S
  | 0, _, _, c => (P.stage c).output
  | q + 1, _, _, c => (P.stage c, P.compile q (P.continueWith c))

theorem Program.eval_of_halt (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State)
    (h : P.mode s = 0) : P.eval oracle n s = P.terminal s := by
  cases n <;> simp [Program.eval, h]

theorem Program.eval_of_ready_no_calls (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State)
    (hr : n = 0 ∨ P.mode s ≠ 1) (hc : P.calls oracle n s = 0) :
    P.eval oracle n s = P.terminal s := by
  cases n with
  | zero => rfl
  | succ n =>
    have h1 : P.mode s ≠ 1 := hr.resolve_left (by omega)
    by_cases h0 : P.mode s = 0
    · exact P.eval_of_halt oracle _ _ h0
    · simp [Program.calls, h0, h1] at hc

theorem Program.eval_query (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State)
    (hn : n ≠ 0) (h0 : P.mode s ≠ 0) (h1 : P.mode s ≠ 1) :
    P.eval oracle n s = P.eval oracle (n - 1) (P.next (s, oracle (P.query s))) := by
  cases n with
  | zero => contradiction
  | succ n => simp [Program.eval, h0, h1]

theorem Program.calls_query (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State)
    (hn : n ≠ 0) (h0 : P.mode s ≠ 0) (h1 : P.mode s ≠ 1) :
    P.calls oracle n s = P.calls oracle (n - 1) (P.next (s, oracle (P.query s))) + 1 := by
  cases n with
  | zero => contradiction
  | succ n => simp [Program.calls, h0, h1]

/-- Exact simulation at the internal-time cutoff whenever the actual run fits
the query cap. The compiled program still enforces that cap on all other reply
histories, independently of this preservation hypothesis. -/
theorem Program.compile_simulates (P : Program d State O) (q : ℕ)
    {S : Type w} [MeasurableSpace S] (c : MeasurableStateMap S (ℕ × State))
    (W : Matrix (Fin d) (Fin d) ℝ) (x : S)
    (hcap : P.calls (fun v => W *ᵥ v) (c.1 x).1 (c.1 x).2 ≤ q) :
    runBoundedTwoSided d q (P.compile q c) W x =
      P.eval (fun v => W *ᵥ v) (c.1 x).1 (c.1 x).2 := by
  induction q generalizing S with
  | zero =>
    change P.terminal (P.advance (c.1 x).1 (c.1 x).2).2 = _
    rw [← P.eval_advance (fun v => W *ᵥ v) (c.1 x).1 (c.1 x).2]
    symm
    apply P.eval_of_ready_no_calls _ _ _ (P.advance_ready _ _)
    rw [P.calls_advance]
    omega
  | succ q ih =>
    let z := (P.ready c).1 x
    have hr : z.1 = 0 ∨ P.mode z.2 ≠ 1 := P.advance_ready _ _
    have he : P.eval (fun v => W *ᵥ v) z.1 z.2 =
        P.eval (fun v => W *ᵥ v) (c.1 x).1 (c.1 x).2 := P.eval_advance _ _ _
    have hc : P.calls (fun v => W *ᵥ v) z.1 z.2 ≤ q + 1 := by
      simpa only [z, Program.ready, P.calls_advance] using hcap
    rw [← he]
    change runBoundedTwoSided d (q + 1) (P.stage c, P.compile q (P.continueWith c)) W x = _
    rw [runBoundedTwoSided_step]
    by_cases hs : z.1 = 0 ∨ P.mode z.2 = 0
    · have hstop : (P.stage c).stop.1 x = true := by
        simp only [Program.stage]; exact if_pos hs
      simp only [hstop, if_true]
      change P.terminal z.2 = _
      rcases hs with hf | hm
      · simp [hf, Program.eval]
      · exact (P.eval_of_halt _ _ _ hm).symm
    · have hn : z.1 ≠ 0 := fun h => hs (Or.inl h)
      have h0 : P.mode z.2 ≠ 0 := fun h => hs (Or.inr h)
      have h1 : P.mode z.2 ≠ 1 := hr.resolve_left hn
      have hstop : (P.stage c).stop.1 x = false := by
        simp only [Program.stage]; exact if_neg hs
      simp only [hstop, Bool.false_eq_true, if_false]
      rw [P.eval_query _ _ _ hn h0 h1]
      have hc' : P.calls (fun v => W *ᵥ v) (z.1 - 1)
          (P.next (z.2, W *ᵥ P.query z.2)) ≤ q := by
        rw [P.calls_query _ _ _ hn h0 h1] at hc
        omega
      simpa only [Program.continueWith, Program.stage, twoSidedOracle, if_false]
        using ih (P.continueWith c) (x, W *ᵥ P.query z.2) hc'

/-- Padding changes neither the computed result nor its dependence on the
seed and actual matrix replies. It now has exactly q matrix products. -/
theorem Program.padded_simulates (P : Program d State O) (q : ℕ)
    {S : Type w} [MeasurableSpace S] (c : MeasurableStateMap S (ℕ × State))
    (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ = W) (x : S)
    (hcap : P.calls (fun v => W *ᵥ v) (c.1 x).1 (c.1 x).2 ≤ q) :
    readPaddedSymmetricOutput d q (P.compile q c)
      (runAmbientOracle d q (padSymmetricPolicy d q (P.compile q c)) W x) =
      P.eval (fun v => W *ᵥ v) (c.1 x).1 (c.1 x).2 := by
  rw [padSymmetricPolicy_simulates d q (P.compile q c) W hW x]
  exact P.compile_simulates q c W x hcap

theorem Program.counterfactual_calls_le (P : Program d State O) (q : ℕ)
    {S : Type w} [MeasurableSpace S] (c : MeasurableStateMap S (ℕ × State))
    (W : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    ((P.compile q c).toProgram d q x).calls (twoSidedOracle W) ≤ q :=
  BoundedTwoSidedPolicy.calls_le d q (P.compile q c) W x

theorem Program.padded_calls_eq (P : Program d State O) (q : ℕ)
    {S : Type w} [MeasurableSpace S] (c : MeasurableStateMap S (ℕ × State))
    (W : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    ((padSymmetricPolicy d q (P.compile q c)).toProgram d q x).calls
      (fun v => W *ᵥ v) = q := padSymmetricPolicy_calls d q (P.compile q c) W x

def Program.step (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : State) : State :=
  if P.mode s = 0 then s else if P.mode s = 1 then P.think s
    else P.next (s, oracle (P.query s))

theorem Program.eval_eq_at_halt (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State)
    (hh : P.mode ((P.step oracle)^[n] s) = 0) :
    P.eval oracle n s = (true, P.output ((P.step oracle)^[n] s)) := by
  induction n generalizing s with
  | zero => simpa [Program.eval, Program.terminal] using hh
  | succ n ih =>
    by_cases h0 : P.mode s = 0
    · have hf : ∀ i, (P.step oracle)^[i] s = s :=
        Function.iterate_fixed (by simp [Program.step, h0])
      simp [Program.eval, Program.terminal, h0, hf]
    · rw [Function.iterate_succ_apply] at hh ⊢
      have h := ih (P.step oracle s) hh
      by_cases h1 : P.mode s = 1
      · simpa [Program.eval, Program.step, h0, h1] using h
      · simpa [Program.eval, Program.step, h0, h1] using h

theorem Program.calls_eq_sum (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    P.calls oracle n s = ∑ i ∈ Finset.range n,
      if P.mode ((P.step oracle)^[i] s) = 2 then 1 else 0 := by
  induction n generalizing s with
  | zero => simp [Program.calls]
  | succ n ih =>
    by_cases h0 : P.mode s = 0
    · have hf : ∀ i, (P.step oracle)^[i] s = s :=
        Function.iterate_fixed (by simp [Program.step, h0])
      simp [Program.calls, h0, hf]
    · rw [Finset.sum_range_succ']
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      rw [← ih (P.step oracle s)]
      by_cases h1 : P.mode s = 1
      · simp [Program.calls, Program.step, h0, h1]
      · have h2 : P.mode s = 2 := by omega
        simp [Program.calls, Program.step, h0, h1, h2]

theorem Program.terminal_property (P : Program d State O) (R : O → Prop)
    (hout : ∀ s, R (P.output s)) (s : State) :
    (P.terminal s).1 = true → R (P.terminal s).2 := by
  simp only [Program.terminal]
  split_ifs
  · exact fun _ => hout s
  · simp

/-- Output validity is checked for every history, including histories that
have zero probability under a particular matrix distribution. -/
theorem Program.compile_outputs (P : Program d State O) (R : O → Prop)
    (hout : ∀ s, R (P.output s)) (q : ℕ)
    {S : Type w} [MeasurableSpace S] (c : MeasurableStateMap S (ℕ × State)) :
    (P.compile q c).Outputs d (fun o => o.1 = true → R o.2) q := by
  induction q generalizing S with
  | zero => exact fun x => P.terminal_property R hout _
  | succ q ih =>
    exact ⟨fun x _ => P.terminal_property R hout _, ih (P.continueWith c)⟩

end
end GradientHessian.MachineCompiler
