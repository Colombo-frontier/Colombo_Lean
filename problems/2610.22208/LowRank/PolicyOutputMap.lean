import LowRank.BoundedTwoSidedPolicy

/-! Measurable output postprocessing changes neither the chosen queries
nor their stopping times. Both the executable program and the policy
representation preserve the actual call count. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u v w

def OracleProgram.mapOutput {Q R O O' : Type*} (f : O → O') :
    OracleProgram Q R O → OracleProgram Q R O'
  | .done o => .done (f o)
  | .ask q next => .ask q (fun r => (next r).mapOutput f)

theorem OracleProgram.eval_mapOutput {Q R O O' : Type*} (f : O → O')
    (oracle : Q → R) (program : OracleProgram Q R O) :
    (program.mapOutput f).eval oracle = f (program.eval oracle) := by
  induction program with
  | done o => rfl
  | ask q next ih => exact ih (oracle q)

theorem OracleProgram.calls_mapOutput {Q R O O' : Type*} (f : O → O')
    (oracle : Q → R) (program : OracleProgram Q R O) :
    (program.mapOutput f).calls oracle = program.calls oracle := by
  induction program with
  | done o => rfl
  | ask q next ih => exact congrArg (· + 1) (ih (oracle q))

def BoundedTwoSidedPolicy.mapOutput (d : ℕ) {O : Type v} {O' : Type w}
    [MeasurableSpace O] [MeasurableSpace O'] (f : MeasurableStateMap O O') :
    (n : ℕ) → {S : Type u} → [MeasurableSpace S] → BoundedTwoSidedPolicy d O n S →
      BoundedTwoSidedPolicy d O' n S
  | 0, _, _, policy => ⟨fun x => f.1 (policy.1 x), f.2.comp policy.2⟩
  | n + 1, _, _, policy =>
      ({stop := policy.1.stop
        output := ⟨fun x => f.1 (policy.1.output.1 x), f.2.comp policy.1.output.2⟩
        query := policy.1.query}, policy.2.mapOutput d f n)

theorem BoundedTwoSidedPolicy.toProgram_mapOutput (d n : ℕ)
    {S : Type u} {O : Type v} {O' : Type w}
    [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace O']
    (f : MeasurableStateMap O O') (policy : BoundedTwoSidedPolicy d O n S) (x : S) :
    (policy.mapOutput d f n).toProgram d n x = (policy.toProgram d n x).mapOutput f.1 := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
      simp only [mapOutput, toProgram]
      split_ifs
      · rfl
      · simp only [OracleProgram.mapOutput]
        congr 1
        funext reply
        exact ih policy.2 (x, reply)

theorem runBoundedTwoSided_mapOutput (d n : ℕ) {S : Type u} {O : Type v} {O' : Type w}
    [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace O']
    (f : MeasurableStateMap O O') (policy : BoundedTwoSidedPolicy d O n S)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    runBoundedTwoSided d n (policy.mapOutput d f n) A x = f.1 (runBoundedTwoSided d n policy A x) := by
  simp only [runBoundedTwoSided, BoundedTwoSidedPolicy.toProgram_mapOutput, OracleProgram.eval_mapOutput]

theorem BoundedTwoSidedPolicy.calls_mapOutput (d n : ℕ)
    {S : Type u} {O : Type v} {O' : Type w}
    [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace O']
    (f : MeasurableStateMap O O') (policy : BoundedTwoSidedPolicy d O n S)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    ((policy.mapOutput d f n).toProgram d n x).calls (twoSidedOracle A) =
      (policy.toProgram d n x).calls (twoSidedOracle A) := by
  rw [toProgram_mapOutput, OracleProgram.calls_mapOutput]

theorem BoundedTwoSidedPolicy.mapOutput_outputs (d n : ℕ)
    {S : Type u} {O : Type v} {O' : Type w}
    [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace O']
    (f : MeasurableStateMap O O') (policy : BoundedTwoSidedPolicy d O n S)
    (P : O' → Prop) (hP : ∀ o, P (f.1 o)) :
    (policy.mapOutput d f n).Outputs d P n := by
  induction n generalizing S with
  | zero => exact fun x => hP (policy.1 x)
  | succ n ih => exact ⟨fun x _ => hP (policy.1.output.1 x), ih policy.2⟩

end
end LowRank
