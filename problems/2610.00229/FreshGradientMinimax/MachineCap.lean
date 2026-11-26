import FreshGradientMinimax.OracleMachine

/-! A completed branch is frozen while a deterministic budget is filled
with dummy queries. Its output is read only when completion fits the budget. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleMachine
variable {dx dy : ℕ} {State Seed : Type*} [MeasurableSpace State] [MeasurableSpace Seed]

def capped (M : OracleMachine dx dy State) (T : ℕ) (read : State → Euclid dx) (hr : Measurable read) :
    OracleMachine dx dy State where
  query n := if n < T then M.query n else fun _ => 0
  update n := if n < T then M.update n else Prod.fst
  output n := if T ≤ n then read else fun _ => 0
  query_measurable n := by split_ifs; exact M.query_measurable n; exact measurable_const
  update_measurable n := by split_ifs; exact M.update_measurable n; exact measurable_fst
  output_measurable n := by split_ifs; exact hr; exact measurable_const

theorem capped_step_before (M : OracleMachine dx dy State) (T : ℕ) (read : State → Euclid dx)
    (hr : Measurable read) (K : Kernel (Joint dx dy) (Joint dx dy)) {n : ℕ} (hn : n < T) :
    (M.capped T read hr).stepKernel K n = M.stepKernel K n := by
  simp only [stepKernel, capped, if_pos hn]

theorem capped_step_after (M : OracleMachine dx dy State) (T : ℕ) (read : State → Euclid dx)
    (hr : Measurable read) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    {n : ℕ} (hn : T ≤ n) : (M.capped T read hr).stepKernel K n = Kernel.id := by
  apply Kernel.ext
  intro s
  rw [stepKernel_apply]
  simp only [capped, if_neg (Nat.not_lt.mpr hn), Measure.map_const, measure_univ, one_smul, Kernel.id_apply]

theorem capped_run_before (M : OracleMachine dx dy State) (T : ℕ) (read : State → Euclid dx)
    (hr : Measurable read) (init : Seed → State) (hi : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) (hn : n ≤ T) :
    (M.capped T read hr).runKernel init hi K n = M.runKernel init hi K n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runKernel, capped_step_before M T read hr K (by omega), ih (by omega), runKernel]

theorem capped_run_after (M : OracleMachine dx dy State) (T : ℕ) (read : State → Euclid dx)
    (hr : Measurable read) (init : Seed → State) (hi : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) (hn : T ≤ n) :
    (M.capped T read hr).runKernel init hi K n = M.runKernel init hi K T := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => exact M.capped_run_before T read hr init hi K T le_rfl
  | succ d ih =>
    rw [Nat.add_succ, runKernel, capped_step_after M T read hr K (by omega), Kernel.id_comp, ih (by omega)]

theorem capped_output (M : OracleMachine dx dy State) (T : ℕ) (read : State → Euclid dx)
    (hr : Measurable read) (init : Seed → State) (hi : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    ((M.capped T read hr).runKernel init hi K n).map ((M.capped T read hr).output n) =
      ((M.runKernel init hi K T).map read).map (fun y => if T ≤ n then y else 0) := by
  by_cases hn : T ≤ n
  · rw [M.capped_run_after T read hr init hi K n hn]
    simp only [capped, if_pos hn, Kernel.map_id']
  · apply Kernel.ext
    intro s
    rw [Kernel.map_apply _ ((M.capped T read hr).output_measurable n),
      Kernel.map_apply _ (show Measurable (fun y : Euclid dx => if T ≤ n then y else 0) by
        simp only [if_neg hn]; exact measurable_const)]
    haveI := Kernel.IsMarkovKernel.map (M.runKernel init hi K T) hr
    simp only [capped, if_neg hn, Measure.map_const, measure_univ, one_smul]

end OracleMachine
end FreshGradientMinimax
