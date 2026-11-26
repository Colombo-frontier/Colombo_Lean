import GradientHessian.ControllerChosenSuppression
import GradientHessian.ControllerDriverMonotonicity

/-! A chosen blocked action closes its target stop permanently. If the
actual final state is still open, none was chosen and suppression preserves
the complete original execution up to that state. -/

noncomputable section
namespace GradientHessian.ControllerOpenSuppression
open Classical TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerPolicyCoupling ControllerChosenSuppression
  ControllerDriverMonotonicity

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (blocked : A → Bool) (stop : State L M ell → Bool)
  (ordinary : State L M ell → State L M ell → X → Y)
  (rich : State L M ell → State L M ell → X → Z)

theorem chosen_closes_next
    (hkill : ∀ s a,blocked a=true → stop (retireNode s (R.target a))=true)
    (q : Config L M ell S X A) (hq : ChosenBlocked R blocked q) :
    stop (stateOf (step P R (fun _ => false) ordinary rich q))=true := by
  cases q with
  | ready n a s => exact hq.elim
  | finished a s => exact hq.elim
  | pending n a output phase =>
    cases phase with
    | normal p s => exact hq.elim
    | frozen p s => exact hq.elim
    | delivered p before after => exact hq.elim
    | repairing p s =>
      obtain ⟨b,hb,hblocked⟩ := hq
      simpa only [step,guardedTick,freeze,Bool.false_eq_true,if_false,tick,hb,stateOf,phaseState] using
        hkill s b hblocked

theorem run_eq_of_open_endpoint (hell : 0<ell)
    (hretire : ∀ s,Ready s → ∀ a,stop s=true → stop (retireNode s (R.target a))=true)
    (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)
    (hkill : ∀ s a,blocked a=true → stop (retireNode s (R.target a))=true)
    (q : Config L M ell S X A) (hq : Coherent stop q) (N : ℕ)
    (hN : stop (stateOf (run P R (fun _ => false) ordinary rich N q))=false) :
    run P R (fun _ => false) ordinary rich N q=
      run P (suppress R blocked) (fun _ => false) ordinary rich N q := by
  apply run_eq_of_no_chosen P R blocked (fun _ => false) ordinary rich q N
  intro i hi hchosen
  have hc := run_coherent P R stop ordinary rich hell hnormal q hq i
  have hn := chosen_closes_next P R blocked stop ordinary rich hkill _ hchosen
  have hcn := step_coherent P R stop ordinary rich hell hnormal _ hc
  have hp := stop_persists_run P R stop ordinary rich hell hretire hnormal _ hcn hn (N-(i+1))
  rw [← run_succ_end,← run_add,Nat.add_sub_of_le (Nat.succ_le_of_lt hi),hN] at hp
  contradiction

theorem guarded_run_eq_of_open_endpoint (hell : 0<ell)
    (hretire : ∀ s,Ready s → ∀ a,stop s=true → stop (retireNode s (R.target a))=true)
    (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)
    (hkill : ∀ s a,blocked a=true → stop (retireNode s (R.target a))=true)
    (q : Config L M ell S X A) (hq : Coherent stop q) (N : ℕ)
    (hN : stop (stateOf (run P R (fun _ => false) ordinary rich N q))=false) :
    run P (suppress R blocked) stop ordinary rich N q=
      run P R (fun _ => false) ordinary rich N q := by
  have he := run_eq_of_open_endpoint P R blocked stop ordinary rich hell hretire hnormal hkill q hq N hN
  have hnormal' : ∀ s,Ready s → ∀ p,stop s=true → stop (normal (suppress R blocked) p s)=true := by
    intro s hs p hstop
    rw [normal_congr (suppress R blocked) R p s (by rfl)]
    exact hnormal s hs p hstop
  rw [guarded_eq_at_open_endpoint P (suppress R blocked) stop ordinary rich hell
    hretire hnormal' q hq N (by rw [← he]; exact hN)]
  exact he.symm

end GradientHessian.ControllerOpenSuppression
