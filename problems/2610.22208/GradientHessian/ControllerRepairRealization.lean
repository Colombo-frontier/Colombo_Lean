import GradientHessian.ControllerPolicyExecution
import GradientHessian.ControllerRepairEvents

/-! Every action in an atomic repair trace is chosen at an actual finite
repairing phase of the chronological policy driver. -/

noncomputable section
namespace GradientHessian.ControllerRepairRealization
open Classical TaskState ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerRepairEvents

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

theorem point_action_realized (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (remaining : ℕ) (algorithm : S) (output : Bool) (p : Pending X)
    (cap : ℕ) (s : State L M ell) (a : A) (ha : a ∈ pointActions R p cap s) :
    ∃ i<cap, ∃ u : State L M ell,
      run P R (fun _ => false) ordinary rich i (.pending remaining algorithm output (.repairing p s))=
        .pending remaining algorithm output (.repairing p u) ∧ choose R p u=some a := by
  induction cap generalizing s with
  | zero => simp [pointActions,repairRun] at ha
  | succ cap ih =>
    cases hc : choose R p s with
    | none => simp [pointActions,repairRun,hc] at ha
    | some b =>
      have hm : a=b ∨ a ∈ pointActions R p cap (retireNode s (R.target b)) := by
        simpa [pointActions,repairRun,hc] using ha
      rcases hm with hab|hm
      · exact ⟨0,Nat.zero_lt_succ _,s,rfl,hab ▸ hc⟩
      · obtain ⟨i,hi,u,hu,hchoose⟩ := ih (retireNode s (R.target b)) hm
        refine ⟨i+1,Nat.succ_lt_succ hi,u,?_,hchoose⟩
        simpa only [run,step,guardedTick,freeze,Bool.false_eq_true,if_false,tick,hc] using hu

theorem query_action_realized (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (algorithm : S) (s : State L M ell) (a : A)
    (hquery : P.mode algorithm=2 ∨ P.mode algorithm=3)
    (ha : a ∈ pointActions R (ControllerPolicyExecution.queryPoint P algorithm) (8^L) s) :
    ∃ i<8^L+1, ∃ u : State L M ell,
      run P R (fun _ => false) ordinary rich i (.ready (n+1) algorithm s)=
        .pending (n+1) algorithm false (.repairing (ControllerPolicyExecution.queryPoint P algorithm) u) ∧
      choose R (ControllerPolicyExecution.queryPoint P algorithm) u=some a := by
  obtain ⟨i,hi,u,hu,hchoose⟩ := point_action_realized P R ordinary rich (n+1) algorithm false
    (ControllerPolicyExecution.queryPoint P algorithm) (8^L) s a ha
  refine ⟨i+1,Nat.succ_lt_succ hi,u,?_,hchoose⟩
  rcases hquery with hq|hq <;>
    simpa only [run,step,hq,ControllerPolicyExecution.queryPoint] using hu

theorem output_action_realized (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (algorithm : S) (s : State L M ell) (a : A)
    (houtput : n=0 ∨ P.mode algorithm=0)
    (ha : a ∈ pointActions R ⟨P.output algorithm,.ordinary⟩ (8^L) s) :
    ∃ i<8^L+1, ∃ u : State L M ell,
      run P R (fun _ => false) ordinary rich i (.ready n algorithm s)=
        .pending n algorithm true (.repairing ⟨P.output algorithm,.ordinary⟩ u) ∧
      choose R ⟨P.output algorithm,.ordinary⟩ u=some a := by
  obtain ⟨i,hi,u,hu,hchoose⟩ := point_action_realized P R ordinary rich n algorithm true
    ⟨P.output algorithm,.ordinary⟩ (8^L) s a ha
  refine ⟨i+1,Nat.succ_lt_succ hi,u,?_,hchoose⟩
  simpa only [run,step,Bool.false_eq_true,if_false,if_pos houtput] using hu

end GradientHessian.ControllerRepairRealization
