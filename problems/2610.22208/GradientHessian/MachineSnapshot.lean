import GradientHessian.MachineCompiler
import GradientHessian.OracleComposition

/-! Finite cutoffs that retain the actual state, including accumulated tests.
The clocked machine halts at the cutoff and returns the current output. -/

namespace GradientHessian.MachineCompiler
open MeasureTheory Matrix LowRank OracleComposition
noncomputable section

variable {d : ℕ} {State O : Type*} [MeasurableSpace State] [MeasurableSpace O]

def Program.clocked (P : Program d State O) : Program d (ℕ × State) O where
  mode := fun s => if s.1 = 0 then 0 else P.mode s.2
  think := fun s => (s.1 - 1, P.think s.2)
  query := fun s => P.query s.2
  next := fun t => (t.1.1 - 1, P.next (t.1.2, t.2))
  output := fun s => P.output s.2
  fallback := P.fallback
  mode_measurable := Measurable.ite (measurable_fst (measurableSet_singleton 0))
    measurable_const (P.mode_measurable.comp measurable_snd)
  think_measurable := (measurable_fst.sub measurable_const).prodMk
    (P.think_measurable.comp measurable_snd)
  query_measurable := P.query_measurable.comp measurable_snd
  next_measurable := (measurable_fst.fst.sub measurable_const).prodMk
    (P.next_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  output_measurable := P.output_measurable.comp measurable_snd

theorem Program.clocked_eval (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    P.clocked.eval oracle n (n, s) = (true, P.output ((P.step oracle)^[n] s)) := by
  induction n generalizing s with
  | zero => simp [Program.eval, Program.terminal, Program.clocked]
  | succ n ih =>
      by_cases h0 : P.mode s = 0
      · have hf : ∀ i, (P.step oracle)^[i] s = s :=
          Function.iterate_fixed (by simp [Program.step, h0])
        simp [Program.eval, Program.terminal, Program.clocked, h0, hf]
      · rw [Function.iterate_succ_apply]
        by_cases h1 : P.mode s = 1
        · simpa [Program.eval, Program.clocked, Program.step, h0, h1] using ih (P.think s)
        · simpa [Program.eval, Program.clocked, Program.step, h0, h1] using
            ih (P.next (s, oracle (P.query s)))

theorem Program.clocked_calls (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    P.clocked.calls oracle n (n, s) = P.calls oracle n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      by_cases h0 : P.mode s = 0
      · simp [Program.calls, Program.clocked, h0]
      · by_cases h1 : P.mode s = 1
        · simpa [Program.calls, Program.clocked, h0, h1] using ih (P.think s)
        · simpa [Program.calls, Program.clocked, h0, h1] using
            ih (P.next (s, oracle (P.query s)))

def Program.snapshotProcedure (P : Program d State O) (q n : ℕ) : Procedure d q State O :=
  (Procedure.ofBounded (P.clocked.compile q
    ⟨fun s => (n, (n, s)), measurable_const.prodMk (measurable_const.prodMk measurable_id)⟩)).mapOutput
      ⟨Prod.snd, measurable_snd⟩

theorem Program.run_snapshotProcedure (P : Program d State O) (q n : ℕ)
    (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ = W) (s : State)
    (hcap : P.calls (fun v => W *ᵥ v) n s ≤ q) :
    (P.snapshotProcedure q n).run W s = P.output ((P.step (fun v => W *ᵥ v))^[n] s) := by
  rw [Program.snapshotProcedure, Procedure.run_mapOutput, Procedure.run_ofBounded _ W hW]
  rw [Program.compile_simulates]
  · simpa using congrArg Prod.snd (P.clocked_eval (fun v => W *ᵥ v) n s)
  · simpa only [Program.clocked_calls] using hcap

theorem Program.snapshotProcedure_calls (P : Program d State O) (q n : ℕ)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : State) :
    ((P.snapshotProcedure q n).toProgram s).calls oracle = q :=
  Procedure.calls_toProgram _ oracle s

theorem Program.step_joint_measurable (P : Program d State O) :
    Measurable (fun t : Matrix (Fin d) (Fin d) ℝ × State =>
      P.step (fun v => t.1 *ᵥ v) t.2) := by
  apply Measurable.ite ((P.mode_measurable.comp measurable_snd) (measurableSet_singleton 0))
    measurable_snd
  apply Measurable.ite ((P.mode_measurable.comp measurable_snd) (measurableSet_singleton 1))
    (P.think_measurable.comp measurable_snd)
  apply P.next_measurable.comp
  apply measurable_snd.prodMk
  have hquery : Measurable (fun t : Matrix (Fin d) (Fin d) ℝ × State => P.query t.2) :=
    P.query_measurable.comp measurable_snd
  apply measurable_pi_lambda
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

theorem Program.iterate_joint_measurable (P : Program d State O) (n : ℕ) :
    Measurable (fun t : Matrix (Fin d) (Fin d) ℝ × State =>
      (P.step (fun v => t.1 *ᵥ v))^[n] t.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        P.step_joint_measurable.comp (measurable_fst.prodMk ih)

theorem Program.snapshot_joint_measurable (P : Program d State O) (n : ℕ) :
    Measurable (fun t : Matrix (Fin d) (Fin d) ℝ × State =>
      P.output ((P.step (fun v => t.1 *ᵥ v))^[n] t.2)) :=
  P.output_measurable.comp (P.iterate_joint_measurable n)

theorem Program.snapshot_property_mono (P : Program d State O)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (R : State → Prop)
    (hretain : ∀ s, R s → R (P.step oracle s)) (s : State) {n m : ℕ} (hnm : n ≤ m)
    (hn : R ((P.step oracle)^[n] s)) : R ((P.step oracle)^[m] s) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => simpa using hn
  | succ k ih =>
      simpa only [Nat.add_succ, Function.iterate_succ_apply'] using
        hretain _ (ih (Nat.le_add_right n k))

end
end GradientHessian.MachineCompiler
