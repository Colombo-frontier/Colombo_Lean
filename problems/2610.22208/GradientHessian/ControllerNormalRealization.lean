import GradientHessian.ControllerPolicyExecution
import GradientHessian.ControllerEarlyEvents

/-! The normal phase is reached before the hit bit is used or any reply
is delivered. Its state is the exact atomic receipt's beforeNormal state. -/

noncomputable section
namespace GradientHessian.ControllerNormalRealization
open Classical FrontierState TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerPolicyExecution ComparisonControllerLedger

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

theorem repair_before_normal (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X)
    (fuel : ℕ) (s : State L M ell)
    (hf : (unretired (TaskState.retired s)).card≤fuel) :
    run P R (fun _ => false) ordinary rich ((repairRun R p fuel s).2.length+1)
      (.pending n a output (.repairing p s)) =
      .pending n a output (.normal p (repairRun R p fuel s).1) := by
  induction fuel generalizing s with
  | zero =>
    have hc := repairRun_terminal R p 0 s hf
    change choose R p s=none at hc
    simp [repairRun,run,step,guardedTick,freeze,tick,hc]
  | succ fuel ih =>
    cases hc : choose R p s with
    | none => simp [repairRun,run,step,guardedTick,freeze,tick,hc]
    | some b =>
      have hp := retirement_progress (TaskState.retired s) (R.target b) (choose_spec R p s hc).2.2
      have hb : (unretired (TaskState.retired (retireNode s (R.target b)))).card≤fuel := by
        rw [retireNode_retired]
        omega
      simpa only [repairRun,hc,List.length_cons,Nat.add_right_comm,run,step,guardedTick,
        freeze,Bool.false_eq_true,if_false,tick] using ih (retireNode s (R.target b)) hb

theorem serve_before_normal (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X) (s : State L M ell) :
    run P R (fun _ => false) ordinary rich ((serve R p s).repairs.length+1)
      (.pending n a output (.repairing p s)) =
      .pending n a output (.normal p (serve R p s).beforeNormal) :=
  repair_before_normal P R ordinary rich n a output p (8^L) s
    ((Finset.card_le_univ _).trans_eq (leaf_card L))

theorem query_before_normal (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (s : State L M ell) (ha : P.mode a=2 ∨ P.mode a=3) :
    run P R (fun _ => false) ordinary rich ((serve R (queryPoint P a) s).repairs.length+2)
      (.ready (n+1) a s) =
      .pending (n+1) a false (.normal (queryPoint P a) (serve R (queryPoint P a) s).beforeNormal) := by
  rw [show (serve R (queryPoint P a) s).repairs.length+2=
    1+((serve R (queryPoint P a) s).repairs.length+1) by omega,run_add]
  have hs : run P R (fun _ => false) ordinary rich 1 (.ready (n+1) a s)=
      .pending (n+1) a false (.repairing (queryPoint P a) s) := by
    rcases ha with ha|ha <;> simp [run,step,queryPoint,ha]
  rw [hs,serve_before_normal]

theorem output_before_normal (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (s : State L M ell) (ha : n=0 ∨ P.mode a=0) :
    run P R (fun _ => false) ordinary rich ((serve R ⟨P.output a,.ordinary⟩ s).repairs.length+2)
      (.ready n a s) =
      .pending n a true (.normal ⟨P.output a,.ordinary⟩ (serve R ⟨P.output a,.ordinary⟩ s).beforeNormal) := by
  rw [show (serve R ⟨P.output a,.ordinary⟩ s).repairs.length+2=
    1+((serve R ⟨P.output a,.ordinary⟩ s).repairs.length+1) by omega,run_add]
  have hs : run P R (fun _ => false) ordinary rich 1 (.ready n a s)=
      .pending n a true (.repairing ⟨P.output a,.ordinary⟩ s) := by simp [run,step,ha]
  rw [hs,serve_before_normal]

def IsEarlyFor (R : Rules L M ell X A) (p : Pending X) (u : State L M ell)
    (q : ControllerEarlyEvents.Task L M) : Prop :=
  TaskState.current u=some q.1 ∧ (u.completed q.1).val=q.2.val ∧ p.kind=.ordinary ∧
    R.hit u p.point=true ∧ (u.slots q.1).val+1<ell

theorem earlyFor_one_before (R : Rules L M ell X A) (p : Pending X)
    (s : State L M ell) (q : ControllerEarlyEvents.Task L M)
    (he : ControllerEarlyEvents.earlyFor R p s q=1) : IsEarlyFor R p (serve R p s).beforeNormal q := by
  obtain ⟨hc,hj,hcost⟩ := ControllerEarlyEvents.earlyFor_one_spec R p s q he
  cases hk : p.kind with
  | rich => simp [early,earlyCost,hk] at hcost
  | ordinary =>
    unfold early earlyCost at hcost
    simp only [hk,hc] at hcost
    split_ifs at hcost with hh
    exact ⟨hc,hj,hk,hh⟩

end GradientHessian.ControllerNormalRealization
