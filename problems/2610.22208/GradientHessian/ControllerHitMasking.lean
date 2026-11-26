import GradientHessian.ControllerDriverMonotonicity

/-! Removing target hit feedback preserves an execution up to any endpoint
whose disclosure stop remains open, when every removed hit closes that stop. -/

noncomputable section
namespace GradientHessian.ControllerHitMasking
open Classical FrontierState TaskState TaskSlots ComparisonController
  ComparisonControllerReplay ControllerPolicyDriver ControllerPolicyCoupling
  ControllerDriverMonotonicity

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def mask (R : Rules L M ell X A) (blocked : State L M ell → Bool) : Rules L M ell X A :=
  { R with hit := fun s x => if blocked s then false else R.hit s x }

def BlockedHit (R : Rules L M ell X A) (blocked : State L M ell → Bool) : Config L M ell S X A → Prop
  | .pending _ _ _ (.normal p s) => p.kind=.ordinary ∧ blocked s=true ∧ R.hit s p.point=true
  | _ => False

theorem normal_eq (R : Rules L M ell X A) (blocked : State L M ell → Bool)
    (p : Pending X) (s : State L M ell)
    (h : ¬(p.kind=.ordinary ∧ blocked s=true ∧ R.hit s p.point=true)) :
    normal R p s=normal (mask R blocked) p s := by
  cases hk : p.kind with
  | rich => simp only [normal,hk]
  | ordinary =>
    cases hb : blocked s with
    | false => simp [normal,hk,mask,hb]
    | true =>
      have hh : R.hit s p.point=false := by
        cases he : R.hit s p.point with
        | false => rfl
        | true => exact (h ⟨hk,hb,he⟩).elim
      simp [normal,hk,mask,hb,hh]

variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (blocked : State L M ell → Bool) (stop : State L M ell → Bool)
  (ordinary : State L M ell → State L M ell → X → Y)
  (rich : State L M ell → State L M ell → X → Z)

theorem step_eq_of_no_hit (q : Config L M ell S X A) (hq : ¬BlockedHit R blocked q) :
    step P R stop ordinary rich q=step P (mask R blocked) stop ordinary rich q := by
  cases q with
  | ready n a s => rfl
  | finished a s => rfl
  | pending n a output phase =>
    cases phase with
    | delivered p before after => rfl
    | frozen p s => rfl
    | repairing p s =>
      cases hs : stop s <;> simp [step,guardedTick,freeze,hs,tick,ComparisonController.choose,mask]
    | normal p s =>
      have hn := normal_eq R blocked p s hq
      cases hs : stop s with
      | true => simp [step,guardedTick,freeze,hs,tick]
      | false => simp only [step,guardedTick,freeze,hs,Bool.false_eq_true,if_false,tick,hn]

theorem run_eq_of_no_hit (q : Config L M ell S X A) (N : ℕ)
    (h : ∀ i<N,¬BlockedHit R blocked (run P R stop ordinary rich i q)) :
    run P R stop ordinary rich N q=run P (mask R blocked) stop ordinary rich N q := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [run_succ_end,run_succ_end,← ih (fun i hi => h i (by omega))]
    exact step_eq_of_no_hit P R blocked stop ordinary rich _ (h N (by omega))

theorem hit_closes_next
    (hkill : ∀ s,Ready s → ∀ p,p.kind=.ordinary → blocked s=true → R.hit s p.point=true →
      stop (normal R p s)=true)
    (q : Config L M ell S X A) (hready : Coherent stop q) (hq : BlockedHit R blocked q) :
    stop (stateOf (step P R (fun _ => false) ordinary rich q))=true := by
  cases q with
  | ready n a s => exact hq.elim
  | finished a s => exact hq.elim
  | pending n a output phase =>
    cases phase with
    | repairing p s => exact hq.elim
    | frozen p s => exact hq.elim
    | delivered p before after => exact hq.elim
    | normal p s =>
      exact hkill s hready p hq.1 hq.2.1 hq.2.2

theorem run_eq_of_open_endpoint (hell : 0<ell)
    (hretire : ∀ s,Ready s → ∀ a,stop s=true → stop (retireNode s (R.target a))=true)
    (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)
    (hkill : ∀ s,Ready s → ∀ p,p.kind=.ordinary → blocked s=true → R.hit s p.point=true →
      stop (normal R p s)=true)
    (q : Config L M ell S X A) (hq : Coherent stop q) (N : ℕ)
    (hN : stop (stateOf (run P R (fun _ => false) ordinary rich N q))=false) :
    run P R (fun _ => false) ordinary rich N q=
      run P (mask R blocked) (fun _ => false) ordinary rich N q := by
  apply run_eq_of_no_hit P R blocked (fun _ => false) ordinary rich q N
  intro i hi hhit
  have hc := run_coherent P R stop ordinary rich hell hnormal q hq i
  have hn := hit_closes_next P R blocked stop ordinary rich hkill _ hc hhit
  have hcn := step_coherent P R stop ordinary rich hell hnormal _ hc
  have hp := stop_persists_run P R stop ordinary rich hell hretire hnormal _ hcn hn (N-(i+1))
  rw [← run_succ_end,← run_add,Nat.add_sub_of_le (Nat.succ_le_of_lt hi),hN] at hp
  contradiction

end GradientHessian.ControllerHitMasking
