import GradientHessian.ControllerPolicyDriver

/-! Callback congruence along actual receipts. Rich callbacks need agree only
on the snapshots produced by the corresponding normal operation. -/

noncomputable section
namespace GradientHessian.ControllerReceiptCongruence
open Classical TaskState ComparisonController ComparisonControllerReplay ControllerPolicyDriver

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def PhaseReceipt (R : Rules L M ell X A) : Phase L M ell X A → Prop
  | .delivered p before after => after=normal R p before
  | _ => True

def Receipt (R : Rules L M ell X A) : Config L M ell S X A → Prop
  | .pending _ _ _ phase => PhaseReceipt R phase
  | _ => True

theorem receipt_freeze (R : Rules L M ell X A) (stop : State L M ell → Bool)
    (q : Phase L M ell X A) (hq : PhaseReceipt R q) : PhaseReceipt R (freeze stop q) := by
  cases q <;> simp only [freeze] <;> (try split_ifs) <;> trivial

theorem receipt_tick (R : Rules L M ell X A)
    (q : Phase L M ell X A) (hq : PhaseReceipt R q) : PhaseReceipt R (tick R q) := by
  cases q with
  | delivered p before after => exact hq
  | frozen p s => trivial
  | normal p s => rfl
  | repairing p s => cases hc : choose R p s <;> simp [tick,hc,PhaseReceipt]

theorem receipt_guardedTick (R : Rules L M ell X A) (stop : State L M ell → Bool)
    (q : Phase L M ell X A) (hq : PhaseReceipt R q) : PhaseReceipt R (guardedTick R stop q) :=
  receipt_freeze R stop _ (receipt_tick R _ (receipt_freeze R stop q hq))

theorem receipt_step (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (hq : Receipt R q) :
    Receipt R (step P R stop ordinary rich q) := by
  cases q with
  | ready n a s => simp only [step]; split_ifs <;> trivial
  | finished a s => trivial
  | pending n a output phase =>
      cases phase with
      | repairing p s => exact receipt_guardedTick R stop _ hq
      | normal p s => exact receipt_guardedTick R stop _ hq
      | frozen p s => trivial
      | delivered p before after =>
          simp only [step,deliver]
          split_ifs <;> try trivial
          cases p.kind <;> trivial

theorem receipt_run (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (q : Config L M ell S X A) (hq : Receipt R q) :
    Receipt R (run P R stop ordinary rich N q) := by
  induction N generalizing q with
  | zero => exact hq
  | succ N ih => exact ih _ (receipt_step P R stop ordinary rich q hq)

theorem initial_receipt (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (N : ℕ) (seed : Seed) (s : State L M ell) : Receipt R (initial P N seed s) := trivial

theorem deliver_congr (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ (p : Pending X) b a,p.kind=.rich → a=normal R p b →
      stop b=false → stop a=false → r₁ b a p.point=r₂ b a p.point)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X)
    (before after : State L M ell) (he : after=normal R p before) :
    deliver (Action := A) P stop o₁ r₁ n a output p before after=
      deliver P stop o₂ r₂ n a output p before after := by
  cases hb : stop before <;> cases ha : stop after
  · simp only [deliver,hb,ha,Bool.or_false,Bool.false_eq_true,if_false]
    cases output
    · simp only [Bool.false_eq_true,if_false]
      cases hk : p.kind
      · rw [ho before after hb ha]
      · rw [hr p before after hk he hb ha]
    · rfl
  all_goals simp [deliver,hb,ha]

theorem step_congr (P : Machine.Policy Seed S X Y Z) (R T : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (hp : R.priority=T.priority) (ht : R.target=T.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=T.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=T.hit s x)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ (p : Pending X) b a,p.kind=.rich → a=normal R p b →
      stop b=false → stop a=false → r₁ b a p.point=r₂ b a p.point)
    (q : Config L M ell S X A) (hq : Receipt R q) :
    step P R stop o₁ r₁ q=step P T stop o₂ r₂ q := by
  cases q with
  | ready n a s => rfl
  | finished a s => rfl
  | pending n a output phase =>
      cases phase with
      | repairing p s =>
          exact congrArg (Config.pending n a output)
            (guardedTick_congr R T stop hp ht htrigger hhit (.repairing p s))
      | normal p s =>
          exact congrArg (Config.pending n a output)
            (guardedTick_congr R T stop hp ht htrigger hhit (.normal p s))
      | frozen p s => rfl
      | delivered p before after =>
          exact deliver_congr P R stop o₁ o₂ r₁ r₂ ho hr n a output p before after hq

theorem run_congr (P : Machine.Policy Seed S X Y Z) (R T : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (hp : R.priority=T.priority) (ht : R.target=T.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=T.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=T.hit s x)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ (p : Pending X) b a,p.kind=.rich → a=normal R p b →
      stop b=false → stop a=false → r₁ b a p.point=r₂ b a p.point)
    (N : ℕ) (q : Config L M ell S X A) (hq : Receipt R q) :
    run P R stop o₁ r₁ N q=run P T stop o₂ r₂ N q := by
  induction N generalizing q with
  | zero => rfl
  | succ N ih =>
      simp only [run]
      rw [← step_congr P R T stop hp ht htrigger hhit o₁ o₂ r₁ r₂ ho hr q hq]
      exact ih _ (receipt_step P R stop o₁ r₁ q hq)

end GradientHessian.ControllerReceiptCongruence
