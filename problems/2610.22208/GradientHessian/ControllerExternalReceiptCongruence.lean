import GradientHessian.ControllerReceiptCongruence
import GradientHessian.ControllerDriverMonotonicity
import GradientHessian.ExternalHaltIteration

/-! External stopping compares unguarded transitions and retains the complete
receipt of the operation that first supplies the target datum. -/

noncomputable section
namespace GradientHessian.ControllerExternalReceiptCongruence
open Classical TaskState TaskSlots ComparisonController ComparisonControllerReplay ControllerPolicyDriver
  ControllerDriverMonotonicity ControllerReceiptCongruence

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

theorem step_open_congr (P : Machine.Policy Seed S X Y Z) (R T : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (hp : R.priority=T.priority) (ht : R.target=T.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=T.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=T.hit s x)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ (p : Pending X) b a,p.kind=.rich → a=normal R p b →
      stop b=false → stop a=false → r₁ b a p.point=r₂ b a p.point)
    (q : Config L M ell S X A) (hc : Coherent stop q) (hq : Receipt R q)
    (hs : stop (stateOf q)=false) :
    step P R (fun _ => false) o₁ r₁ q=step P T (fun _ => false) o₂ r₂ q := by
  have hopen := coherent_open stop q hc hs
  cases q with
  | ready n a s => rfl
  | finished a s => rfl
  | pending n a output phase =>
      cases phase with
      | repairing p s =>
          have he := choose_congr R T p s hp ht (htrigger s hs p.point)
          simp only [step,guardedTick_false,tick,he,ht]
      | normal p s =>
          have he := normal_congr R T p s (hhit s hs p.point)
          simp only [step,guardedTick_false,tick,he]
      | frozen p s => rfl
      | delivered p before after =>
          change stop before=false ∧ stop after=false at hopen
          simp only [step,deliver,Bool.false_or,Bool.false_eq_true,if_false]
          cases output
          · simp only [Bool.false_eq_true,if_false]
            cases hk : p.kind
            · rw [ho before after hopen.1 hopen.2]
            · rw [hr p before after hk hq hopen.1 hopen.2]
          · rfl

def external (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool) (extra : Config L M ell S X A → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z) : Config L M ell S X A → Config L M ell S X A :=
  ExternalHaltIteration.step (step P R (fun _ => false) ordinary rich)
    (fun q => extra q || stop (stateOf q))

theorem external_receipt (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool) (extra : Config L M ell S X A → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (hq : Receipt R q) :
    Receipt R (external P R stop extra ordinary rich q) := by
  unfold external ExternalHaltIteration.step
  split_ifs
  · exact hq
  · exact receipt_step P R (fun _ => false) ordinary rich q hq

theorem external_coherent (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool) (extra : Config L M ell S X A → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (hell : 0<ell)
    (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)
    (q : Config L M ell S X A) (hq : Coherent stop q) :
    Coherent stop (external P R stop extra ordinary rich q) := by
  unfold external ExternalHaltIteration.step
  split_ifs
  · exact hq
  · exact step_coherent P R stop ordinary rich hell hnormal q hq

theorem external_step_congr (P : Machine.Policy Seed S X Y Z) (R T : Rules L M ell X A)
    (stop : State L M ell → Bool) (extra : Config L M ell S X A → Bool)
    (hp : R.priority=T.priority) (ht : R.target=T.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=T.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=T.hit s x)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ (p : Pending X) b a,p.kind=.rich → a=normal R p b →
      stop b=false → stop a=false → r₁ b a p.point=r₂ b a p.point)
    (q : Config L M ell S X A) (hc : Coherent stop q) (hq : Receipt R q) :
    external P R stop extra o₁ r₁ q=external P T stop extra o₂ r₂ q := by
  cases he : extra q <;> cases hs : stop (stateOf q)
  · simpa only [external,ExternalHaltIteration.step,he,hs,Bool.false_or,Bool.false_eq_true,if_false] using
      step_open_congr P R T stop hp ht htrigger hhit o₁ o₂ r₁ r₂ ho hr q hc hq hs
  all_goals simp [external,ExternalHaltIteration.step,he,hs]

theorem external_iterate_congr (P : Machine.Policy Seed S X Y Z) (R T : Rules L M ell X A)
    (stop : State L M ell → Bool) (extra : Config L M ell S X A → Bool)
    (hp : R.priority=T.priority) (ht : R.target=T.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=T.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=T.hit s x)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ (p : Pending X) b a,p.kind=.rich → a=normal R p b →
      stop b=false → stop a=false → r₁ b a p.point=r₂ b a p.point)
    (hell : 0<ell)
    (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)
    (N : ℕ) (q : Config L M ell S X A) (hc : Coherent stop q) (hq : Receipt R q) :
    (external P R stop extra o₁ r₁)^[N] q=(external P T stop extra o₂ r₂)^[N] q := by
  induction N generalizing q with
  | zero => rfl
  | succ N ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply,
        ← external_step_congr P R T stop extra hp ht htrigger hhit o₁ o₂ r₁ r₂ ho hr q hc hq]
      exact ih _ (external_coherent P R stop extra o₁ r₁ hell hnormal q hc)
        (external_receipt P R stop extra o₁ r₁ q hq)

end GradientHessian.ControllerExternalReceiptCongruence
