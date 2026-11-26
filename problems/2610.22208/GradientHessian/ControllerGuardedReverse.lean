import GradientHessian.ControllerDriverMonotonicity

/-! A finite guarded execution ending before disclosure is exactly the
unguarded execution, including its pending point and both receipt snapshots. -/

noncomputable section
namespace GradientHessian.ControllerGuardedReverse
open Classical TaskState ComparisonController ComparisonControllerReplay ControllerPolicyDriver
  ControllerDriverMonotonicity ControllerGuardedExecution

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def Safe (stop : State L M ell → Bool) : Config L M ell S X A → Prop
  | .pending _ _ _ (.delivered _ before after) => stop before=false ∨ stop after=true
  | _ => True

theorem phaseState_freeze (stop : State L M ell → Bool) (q : Phase L M ell X A) :
    phaseState (freeze stop q)=phaseState q := by
  cases q <;> simp only [freeze] <;> (try split_ifs) <;> rfl

theorem freeze_of_open (stop : State L M ell → Bool) (q : Phase L M ell X A)
    (hq : PhaseOpen stop q) : freeze stop q=q := by
  cases q with
  | repairing p s =>
      change stop s=false at hq
      simp only [freeze,hq,Bool.false_eq_true,if_false]
  | normal p s =>
      change stop s=false at hq
      simp only [freeze,hq,Bool.false_eq_true,if_false]
  | frozen p s => rfl
  | delivered p before after => simp only [freeze,hq.2,Bool.false_eq_true,if_false]

theorem guarded_phase_state (R : Rules L M ell X A) (stop : State L M ell → Bool)
    (q : Phase L M ell X A) (hq : PhaseOpen stop q) :
    phaseState (guardedTick R stop q)=phaseState (tick R q) := by
  rw [guardedTick,freeze_of_open stop q hq,phaseState_freeze]

theorem safe_step (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z) (q : Config L M ell S X A) :
    Safe stop (step P R stop ordinary rich q) := by
  cases q with
  | finished a s => trivial
  | ready n a s => simp only [step]; split_ifs <;> trivial
  | pending n a output phase =>
      cases phase with
      | frozen p s => trivial
      | delivered p before after =>
          simp only [step,deliver]
          split_ifs <;> try trivial
          cases p.kind <;> trivial
      | repairing p s =>
          cases hs : stop s
          · simp only [step,guardedTick,freeze,hs,Bool.false_eq_true,if_false,tick]
            cases choose R p s <;> simp only [freeze] <;> split_ifs <;> trivial
          · simp [step,guardedTick,freeze,hs,tick,Safe]
      | normal p s =>
          cases hs : stop s
          · simp only [step,guardedTick,freeze,hs,Bool.false_eq_true,if_false,tick]
            split_ifs
            · trivial
            · exact Or.inl hs
          · simp [step,guardedTick,freeze,hs,tick,Safe]

theorem closed_step (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (hs : stop (stateOf q)=true) :
    stop (stateOf (step P R stop ordinary rich q))=true := by
  cases q with
  | finished a s => exact hs
  | ready n a s =>
      change stop s=true at hs
      simpa only [step,hs,if_true,stateOf] using hs
  | pending n a output phase =>
      cases phase <;> simp only [stateOf,phaseState] at hs
      all_goals simpa [step,guardedTick,freeze,tick,deliver,hs,stateOf,phaseState] using hs

theorem closed_run (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (q : Config L M ell S X A) (hs : stop (stateOf q)=true) :
    stop (stateOf (run P R stop ordinary rich N q))=true := by
  induction N generalizing q with
  | zero => exact hs
  | succ N ih => exact ih _ (closed_step P R stop ordinary rich q hs)

theorem initial_open (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (q : Config L M ell S X A)
    (hN : stop (stateOf (run P R stop ordinary rich N q))=false) : stop (stateOf q)=false := by
  cases hs : stop (stateOf q) with
  | false => rfl
  | true => have hh := closed_run P R stop ordinary rich N q hs; rw [hN] at hh; cases hh

theorem safe_open (stop : State L M ell → Bool) (q : Config L M ell S X A)
    (hq : Safe stop q) (hs : stop (stateOf q)=false) : Open stop q := by
  cases q with
  | ready n a s => exact hs
  | finished a s => exact hs
  | pending n a output phase =>
      cases phase with
      | repairing p s => exact hs
      | normal p s => exact hs
      | frozen p s => exact hs
      | delivered p before after =>
          refine ⟨?_,hs⟩
          rcases hq with hq | hq
          · exact hq
          · change stop after=false at hs
            rw [hs] at hq
            cases hq

theorem step_eq_of_next_open (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (hq : Open stop q)
    (hn : stop (stateOf (step P R stop ordinary rich q))=false) :
    step P R stop ordinary rich q=step P R (fun _ => false) ordinary rich q := by
  apply ControllerGuardedExecution.step_eq_of_open P R stop ordinary rich q hq
  cases q with
  | finished a s => exact hq
  | ready n a s =>
      simp only [step,Bool.false_eq_true,if_false]
      split_ifs <;> exact hq
  | pending n a output phase =>
      cases phase with
      | frozen p s => exact hq
      | delivered p before after =>
          simp only [step,deliver,Bool.false_or,Bool.false_eq_true,if_false]
          cases output <;> cases p.kind <;> exact hq.2
      | repairing p s =>
          change stop (phaseState (guardedTick R stop (.repairing p s)))=false at hn
          rw [guarded_phase_state R stop (.repairing p s) hq] at hn
          change PhaseOpen stop (guardedTick R (fun _ => false) (.repairing p s))
          rw [guardedTick_false]
          cases hh : choose R p s <;> simpa only [tick,hh,PhaseOpen,phaseState] using hn
      | normal p s =>
          change stop (phaseState (guardedTick R stop (.normal p s)))=false at hn
          rw [guarded_phase_state R stop (.normal p s) hq] at hn
          change PhaseOpen stop (guardedTick R (fun _ => false) (.normal p s))
          rw [guardedTick_false]
          exact ⟨hq,hn⟩

theorem run_eq_of_open_endpoint (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (q : Config L M ell S X A) (hq : Safe stop q)
    (hN : stop (stateOf (run P R stop ordinary rich N q))=false) :
    run P R stop ordinary rich N q=run P R (fun _ => false) ordinary rich N q := by
  induction N generalizing q with
  | zero => rfl
  | succ N ih =>
      have hn := initial_open P R stop ordinary rich N (step P R stop ordinary rich q) hN
      have ho := initial_open P R stop ordinary rich (N+1) q hN
      have he := step_eq_of_next_open P R stop ordinary rich q (safe_open stop q hq ho) hn
      exact (ih _ (safe_step P R stop ordinary rich q) hN).trans
        (congrArg (run P R (fun _ => false) ordinary rich N) he)

end GradientHessian.ControllerGuardedReverse
