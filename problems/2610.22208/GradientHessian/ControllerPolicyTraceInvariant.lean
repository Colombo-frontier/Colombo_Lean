import GradientHessian.ControllerPolicyCoupling
import GradientHessian.ControllerRepairPrefix

/-! Every pending repair phase belongs to the atomic receipt of its actual
selected query. The current last query may be ghost-completed, preserving
the sharp existing visibility-window bound without duplicate test points. -/

noncomputable section
namespace GradientHessian.ControllerPolicyTraceInvariant
open Classical FrontierState TaskState ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerRepairPrefix VisibilityWindow

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def PhaseGood (R : Rules L M ell X A) (initialState : State L M ell) (ps : List (Pending X)) :
    Phase L M ell X A → Prop
  | .repairing p s => ∃ pre, ps=pre++[p] ∧ ∃ k≤8^L,
      s=(repairRun R p k (VisibilityWindow.run R pre initialState)).1
  | .normal p s => ∃ pre, ps=pre++[p] ∧ s=(serve R p (VisibilityWindow.run R pre initialState)).beforeNormal
  | .delivered p before after => ∃ pre, ps=pre++[p] ∧
      before=(serve R p (VisibilityWindow.run R pre initialState)).beforeNormal ∧
      after=(serve R p (VisibilityWindow.run R pre initialState)).afterNormal
  | .frozen _ _ => True

def Good (R : Rules L M ell X A) (initialState : State L M ell) (ps : List (Pending X)) :
    Config L M ell S X A → Prop
  | .ready _ _ s => s=VisibilityWindow.run R ps initialState
  | .pending _ _ _ q => PhaseGood R initialState ps q
  | .finished _ _ => True

theorem phase_freeze (R : Rules L M ell X A) (stop : State L M ell → Bool)
    (initialState : State L M ell) (ps : List (Pending X)) (q : Phase L M ell X A)
    (hq : PhaseGood R initialState ps q) : PhaseGood R initialState ps (freeze stop q) := by
  cases q <;> simp only [freeze] <;> first | exact hq | (split_ifs <;> first | trivial | exact hq)

theorem phase_tick (R : Rules L M ell X A) (initialState : State L M ell)
    (ps : List (Pending X)) (q : Phase L M ell X A) (hq : PhaseGood R initialState ps q) :
    PhaseGood R initialState ps (tick R q) := by
  cases q with
  | frozen p s => exact hq
  | delivered p before after => exact hq
  | normal p s =>
    obtain ⟨pre,hps,hs⟩ := hq
    refine ⟨pre,hps,hs,?_⟩
    exact congrArg (normal R p) hs
  | repairing p s =>
    obtain ⟨pre,hps,k,hk,hs⟩ := hq
    subst s
    cases hc : choose R p (repairRun R p k (VisibilityWindow.run R pre initialState)).1 with
    | none =>
      simp only [tick,hc]
      exact ⟨pre,hps,repair_state_terminal R p k (8^L) _ hk hc⟩
    | some a =>
      simp only [tick,hc]
      refine ⟨pre,hps,k+1,Nat.succ_le_of_lt (repair_prefix_lt_cap_of_choice R p k _ hk a hc),?_⟩
      rw [repair_state_succ,hc]

theorem phase_guardedTick (R : Rules L M ell X A) (stop : State L M ell → Bool)
    (initialState : State L M ell) (ps : List (Pending X)) (q : Phase L M ell X A)
    (hq : PhaseGood R initialState ps q) : PhaseGood R initialState ps (guardedTick R stop q) :=
  phase_freeze R stop initialState ps _
    (phase_tick R initialState ps _ (phase_freeze R stop initialState ps q hq))

theorem good_step (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (initialState : State L M ell) (ps : List (Pending X)) (q : Config L M ell S X A)
    (hq : Good R initialState ps q) :
    Good R initialState (ps++(selected P stop q).toList) (step P R stop ordinary rich q) := by
  cases q with
  | finished a s => trivial
  | ready n a s =>
    cases hs : stop s with
    | true => simp [step,selected,hs,Good]
    | false =>
      by_cases hf : n=0 ∨ P.mode a=0
      · simp only [step,selected,hs,Bool.false_eq_true,if_false,if_pos hf,Option.toList_some,Good,PhaseGood]
        exact ⟨ps,rfl,0,Nat.zero_le _,by simpa only [repairRun] using hq⟩
      · by_cases ht : P.mode a=1
        · simpa only [step,selected,hs,Bool.false_eq_true,if_false,if_neg hf,if_pos ht,
            Option.toList_none,List.append_nil,Good] using hq
        · simp only [step,selected,hs,Bool.false_eq_true,if_false,if_neg hf,if_neg ht,
            Option.toList_some,Good,PhaseGood]
          exact ⟨ps,rfl,0,Nat.zero_le _,by simpa only [repairRun] using hq⟩
  | pending n a output phase =>
    simp only [selected,Option.toList_none,List.append_nil]
    cases phase with
    | frozen p s => trivial
    | repairing p s => exact phase_guardedTick R stop initialState ps _ hq
    | normal p s => exact phase_guardedTick R stop initialState ps _ hq
    | delivered p before after =>
      obtain ⟨pre,hps,hbefore,hafter⟩ := hq
      simp only [step,deliver]
      split_ifs
      · trivial
      · trivial
      · cases p.kind <;> change after=VisibilityWindow.run R ps initialState
        all_goals rw [hps,controller_run_append]
        all_goals exact hafter

theorem selections_succ (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (q : Config L M ell S X A) :
    selections P R stop ordinary rich (n+1) q=
      selections P R stop ordinary rich n q ++
        (selected P stop (ControllerPolicyDriver.run P R stop ordinary rich n q)).toList := by
  simp only [selections,List.range_succ,List.filterMap_append,List.filterMap_cons,List.filterMap_nil]
  cases selected P stop (ControllerPolicyDriver.run P R stop ordinary rich n q) <;> rfl

theorem selections_prefix (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (i fuel : ℕ) (q : Config L M ell S X A) (hi : i≤fuel) :
    ∃ tail,selections P R stop ordinary rich fuel q=selections P R stop ordinary rich i q++tail := by
  induction fuel generalizing i with
  | zero =>
    have he : i=0 := by omega
    subst i
    exact ⟨[],by simp⟩
  | succ fuel ih =>
    by_cases he : i=fuel+1
    · subst i; exact ⟨[],by simp⟩
    · obtain ⟨tail,ht⟩ := ih i (by omega)
      refine ⟨tail++(selected P stop (ControllerPolicyDriver.run P R stop ordinary rich fuel q)).toList,?_⟩
      rw [selections_succ,ht,List.append_assoc]

theorem run_good (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (seed : Seed) (initialState : State L M ell) (fuel : ℕ) :
    Good R initialState
      (selections P R stop ordinary rich fuel (initial P N seed initialState))
      (ControllerPolicyDriver.run P R stop ordinary rich fuel (initial P N seed initialState)) := by
  induction fuel with
  | zero => simp [selections,ControllerPolicyDriver.run,ControllerPolicyDriver.initial,Good,VisibilityWindow.run]
  | succ fuel ih =>
    rw [ControllerPolicyCoupling.run_succ_end,selections_succ]
    exact good_step P R stop ordinary rich initialState _ _ ih

theorem repairing_visible_mem (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (seed : Seed) (initialState : State L M ell) (i fuel : ℕ) (hi : i≤fuel)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X) (s : State L M ell) (v : Node L)
    (hphase : ControllerPolicyDriver.run P R stop ordinary rich i (initial P N seed initialState)=
      .pending n a output (.repairing p s)) (hv : Visible (TaskState.retired s) v) :
    p.point ∈ seenPoints R v (selections P R stop ordinary rich fuel (initial P N seed initialState)) initialState := by
  have hg := run_good P R stop ordinary rich N seed initialState i
  rw [hphase] at hg
  obtain ⟨pre,hpre,k,hk,hs⟩ := hg
  obtain ⟨tail,htail⟩ := selections_prefix P R stop ordinary rich i fuel (initial P N seed initialState) hi
  have he : selections P R stop ordinary rich fuel (initial P N seed initialState)=pre++p::tail := by
    rw [htail,hpre,List.append_assoc]
    rfl
  rw [he]
  apply pending_visible_mem_seenPoints R v pre tail p initialState k hk
  rw [← hs]
  exact hv

end GradientHessian.ControllerPolicyTraceInvariant
