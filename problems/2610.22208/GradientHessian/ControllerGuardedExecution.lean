import GradientHessian.ControllerPolicyCoupling

/-! An actual unguarded driver prefix is unchanged by disclosure guards
whenever both stored snapshots are still open. This covers exit guards in
repair/normal transitions as well as reply delivery. -/

noncomputable section
namespace GradientHessian.ControllerGuardedExecution
open Classical TaskState ComparisonController ComparisonControllerReplay ControllerPolicyDriver

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def PhaseOpen (stop : State L M ell → Bool) : Phase L M ell X A → Prop
  | .repairing _ s | .normal _ s | .frozen _ s => stop s=false
  | .delivered _ before after => stop before=false ∧ stop after=false

def Open (stop : State L M ell → Bool) : Config L M ell S X A → Prop
  | .ready _ _ s | .finished _ s => stop s=false
  | .pending _ _ _ phase => PhaseOpen stop phase

theorem guardedTick_eq_tick (R : Rules L M ell X A) (stop : State L M ell → Bool)
    (phase : Phase L M ell X A) (hphase : PhaseOpen stop phase) (hnext : PhaseOpen stop (tick R phase)) :
    guardedTick R stop phase=tick R phase := by
  cases phase with
  | frozen p s => rfl
  | delivered p before after => simp [guardedTick,freeze,tick,hphase.2]
  | normal p s =>
    change stop s=false at hphase
    simp [guardedTick,freeze,tick,hphase,hnext.2]
  | repairing p s =>
    change stop s=false at hphase
    cases hc : choose R p s with
    | none => simp [guardedTick,freeze,tick,hphase,hc]
    | some a =>
      simp only [tick,hc,PhaseOpen] at hnext
      simp [guardedTick,freeze,tick,hphase,hc,hnext]

theorem step_eq_of_open (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (hq : Open stop q)
    (hnext : Open stop (step P R (fun _ => false) ordinary rich q)) :
    step P R stop ordinary rich q=step P R (fun _ => false) ordinary rich q := by
  cases q with
  | finished a s => rfl
  | ready n a s =>
    change stop s=false at hq
    simp only [step,hq,Bool.false_eq_true,if_false]
  | pending n a output phase =>
    cases phase with
    | frozen p s => rfl
    | delivered p before after =>
      simp only [step,deliver,hq.1,hq.2,Bool.or_false,Bool.false_eq_true,if_false]
    | repairing p s =>
      have hf : guardedTick R (fun _ => false) (.repairing p s)=tick R (.repairing p s) := by
        simp [guardedTick,freeze,tick]
        cases choose R p s <;> rfl
      change PhaseOpen stop (guardedTick R (fun _ => false) (.repairing p s)) at hnext
      rw [hf] at hnext
      exact congrArg (Config.pending n a output)
        ((guardedTick_eq_tick R stop (.repairing p s) hq hnext).trans hf.symm)
    | normal p s =>
      have hf : guardedTick R (fun _ => false) (.normal p s)=tick R (.normal p s) := rfl
      change PhaseOpen stop (tick R (.normal p s)) at hnext
      exact congrArg (Config.pending n a output)
        ((guardedTick_eq_tick R stop (.normal p s) hq hnext).trans hf.symm)

theorem run_eq_before_stop (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (N : ℕ)
    (hopen : ∀ i≤N,Open stop (run P R (fun _ => false) ordinary rich i q)) :
    ∀ i≤N,run P R stop ordinary rich i q=run P R (fun _ => false) ordinary rich i q := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [ControllerPolicyCoupling.run_succ_end,ControllerPolicyCoupling.run_succ_end,ih (by omega)]
    apply step_eq_of_open P R stop ordinary rich _ (hopen i (by omega))
    rw [← ControllerPolicyCoupling.run_succ_end]
    exact hopen (i+1) hi

end GradientHessian.ControllerGuardedExecution
