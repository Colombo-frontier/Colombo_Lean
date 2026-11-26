import GradientHessian.ControllerGuardedExecution

/-! Disclosure that persists through retirement and normal progress cannot
have occurred before an open endpoint of the actual policy driver. Both
delivery snapshots are tracked, so entry and exit guards are discharged. -/

noncomputable section
namespace GradientHessian.ControllerDriverMonotonicity
open Classical TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerGuardedExecution

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def phaseState : Phase L M ell X A → State L M ell
  | .repairing _ s | .normal _ s | .frozen _ s => s
  | .delivered _ _ after => after

def stateOf : Config L M ell S X A → State L M ell
  | .ready _ _ s | .finished _ s => s
  | .pending _ _ _ phase => phaseState phase

def PhaseCoherent (stop : State L M ell → Bool) : Phase L M ell X A → Prop
  | .repairing _ s | .normal _ s | .frozen _ s => Ready s
  | .delivered _ before after => Ready before ∧ Ready after ∧ (stop before=true → stop after=true)

def Coherent (stop : State L M ell → Bool) : Config L M ell S X A → Prop
  | .ready _ _ s | .finished _ s => Ready s
  | .pending _ _ _ phase => PhaseCoherent stop phase

theorem freeze_false (q : Phase L M ell X A) : freeze (fun _ => false) q=q := by cases q <;> rfl
theorem guardedTick_false (R : Rules L M ell X A) (q : Phase L M ell X A) :
    guardedTick R (fun _ => false) q=tick R q := by simp only [guardedTick,freeze_false]

variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A) (stop : State L M ell → Bool)
  (ordinary : State L M ell → State L M ell → X → Y)
  (rich : State L M ell → State L M ell → X → Z)
  (hell : 0<ell)
  (hretire : ∀ s,Ready s → ∀ a,stop s=true → stop (retireNode s (R.target a))=true)
  (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)

include hell hnormal in
theorem phase_coherent_tick (q : Phase L M ell X A) (hq : PhaseCoherent stop q) :
    PhaseCoherent stop (tick R q) := by
  cases q with
  | frozen p s => exact hq
  | delivered p before after => exact hq
  | normal p s => exact ⟨hq,normal_ready R p hq hell,hnormal s hq p⟩
  | repairing p s =>
    cases hc : choose R p s with
    | none => simpa only [tick,hc,PhaseCoherent] using hq
    | some a => simpa only [tick,hc,PhaseCoherent] using retireSet_ready hq (FrontierState.subtree (R.target a))

include hretire hnormal in
theorem phase_stop_tick (q : Phase L M ell X A) (hq : PhaseCoherent stop q)
    (hs : stop (phaseState q)=true) : stop (phaseState (tick R q))=true := by
  cases q with
  | frozen p s => exact hs
  | delivered p before after => exact hs
  | normal p s => exact hnormal s hq p hs
  | repairing p s =>
    cases hc : choose R p s with
    | none => simpa only [tick,hc,phaseState] using hs
    | some a => simpa only [tick,hc,phaseState] using hretire s hq a hs

include hell hnormal in
theorem step_coherent (q : Config L M ell S X A) (hq : Coherent stop q) :
    Coherent stop (step P R (fun _ => false) ordinary rich q) := by
  cases q with
  | finished a s => exact hq
  | ready n a s =>
    simp only [step,Bool.false_eq_true,if_false]
    split_ifs <;> exact hq
  | pending n a output phase =>
    cases phase with
    | frozen p s => exact hq
    | repairing p s =>
      simpa only [step,guardedTick_false,Coherent] using phase_coherent_tick R stop hell hnormal (.repairing p s) hq
    | normal p s =>
      simpa only [step,guardedTick_false,Coherent] using phase_coherent_tick R stop hell hnormal (.normal p s) hq
    | delivered p before after =>
      cases output <;> cases hk : p.kind <;> simpa [step,deliver,hk,Coherent] using hq.2.1

include hretire hnormal in
theorem step_stop (q : Config L M ell S X A) (hq : Coherent stop q)
    (hs : stop (stateOf q)=true) : stop (stateOf (step P R (fun _ => false) ordinary rich q))=true := by
  cases q with
  | finished a s => exact hs
  | ready n a s =>
    simp only [step,Bool.false_eq_true,if_false]
    split_ifs <;> exact hs
  | pending n a output phase =>
    cases phase with
    | frozen p s => exact hs
    | repairing p s =>
      simpa only [step,guardedTick_false,stateOf] using phase_stop_tick R stop hretire hnormal (.repairing p s) hq hs
    | normal p s =>
      simpa only [step,guardedTick_false,stateOf] using phase_stop_tick R stop hretire hnormal (.normal p s) hq hs
    | delivered p before after =>
      cases output <;> cases hk : p.kind <;> simpa [step,deliver,hk,stateOf,phaseState] using hs

theorem coherent_open (q : Config L M ell S X A) (hq : Coherent stop q)
    (hs : stop (stateOf q)=false) : Open stop q := by
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
      cases hb : stop before with
      | false => rfl
      | true => have hh := hq.2.2 hb; simp_all [stateOf,phaseState]

include hell hnormal in
theorem run_coherent (q : Config L M ell S X A) (hq : Coherent stop q) (n : ℕ) :
    Coherent stop (run P R (fun _ => false) ordinary rich n q) := by
  induction n generalizing q with
  | zero => exact hq
  | succ n ih => exact ih _ (step_coherent P R stop ordinary rich hell hnormal q hq)

include hell hretire hnormal in
theorem stop_persists_run (q : Config L M ell S X A) (hq : Coherent stop q)
    (hs : stop (stateOf q)=true) (n : ℕ) :
    stop (stateOf (run P R (fun _ => false) ordinary rich n q))=true := by
  induction n generalizing q with
  | zero => exact hs
  | succ n ih =>
    exact ih _ (step_coherent P R stop ordinary rich hell hnormal q hq)
      (step_stop P R stop ordinary rich hretire hnormal q hq hs)

include hell hretire hnormal in
theorem guarded_eq_at_open_endpoint (q : Config L M ell S X A) (hq : Coherent stop q) (N : ℕ)
    (hN : stop (stateOf (run P R (fun _ => false) ordinary rich N q))=false) :
    run P R stop ordinary rich N q=run P R (fun _ => false) ordinary rich N q := by
  apply run_eq_before_stop P R stop ordinary rich q N _ N le_rfl
  intro i hi
  have hc := run_coherent P R stop ordinary rich hell hnormal q hq i
  apply coherent_open stop _ hc
  cases hs : stop (stateOf (run P R (fun _ => false) ordinary rich i q)) with
  | false => rfl
  | true =>
    have ht := stop_persists_run P R stop ordinary rich hell hretire hnormal _ hc hs (N-i)
    rw [← run_add,show i+(N-i)=N by omega,hN] at ht
    contradiction

end GradientHessian.ControllerDriverMonotonicity
