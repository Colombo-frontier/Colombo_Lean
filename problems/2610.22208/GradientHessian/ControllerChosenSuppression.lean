import GradientHessian.ControllerPolicyCoupling

/-! Suppression preserves the next action whenever the actually chosen
action is unblocked. Unselected tests need not all be false. -/

noncomputable section
namespace GradientHessian.ControllerChosenSuppression
open Classical FrontierState TaskState TaskSlots ComparisonController
  ComparisonControllerReplay ControllerPolicyDriver ControllerPolicyCoupling

theorem find_restrict {A : Type*} (xs : List A) (f g : A → Bool) (a : A)
    (hf : xs.find? f=some a) (hg : g a=true) : xs.find? (fun b => f b && g b)=some a := by
  induction xs with
  | nil => simp at hf
  | cons b xs ih =>
    cases hb : f b with
    | false => simpa [hb] using ih (by simpa [hb] using hf)
    | true =>
      have he : b=a := by simpa [hb] using hf
      subst b
      simp [hb,hg]

variable {L M ell : ℕ} {X A : Type*}

theorem choose_suppress_some (R : Rules L M ell X A) (blocked : A → Bool)
    (p : Pending X) (s : State L M ell) (a : A)
    (hc : choose R p s=some a) (ha : blocked a=false) : choose (suppress R blocked) p s=some a := by
  have h := find_restrict R.priority
    (fun b => R.trigger s p.point b && decide ((subtree (R.target b) \ TaskState.retired s).Nonempty))
    (fun b => !blocked b) a hc (by simp [ha])
  convert h using 1
  unfold ComparisonController.choose
  simp only [suppress]
  congr 1
  funext b
  cases hb : blocked b <;> simp [suppress,hb,Bool.and_comm]

theorem choose_suppress_none (R : Rules L M ell X A) (blocked : A → Bool)
    (p : Pending X) (s : State L M ell) (hc : choose R p s=none) : choose (suppress R blocked) p s=none := by
  apply (choose_none_iff _ p s).mpr
  intro a ha ht
  have htr : R.trigger s p.point a=true := by
    cases hb : blocked a <;> simp_all [suppress]
  exact (choose_none_iff R p s).mp hc a ha htr

theorem choose_suppress_eq (R : Rules L M ell X A) (blocked : A → Bool)
    (p : Pending X) (s : State L M ell)
    (h : ∀ a,choose R p s=some a → blocked a=false) : choose (suppress R blocked) p s=choose R p s := by
  cases hc : choose R p s with
  | none => exact choose_suppress_none R blocked p s hc
  | some a => exact choose_suppress_some R blocked p s a hc (h a hc)

variable {Seed S Y Z : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def ChosenBlocked (R : Rules L M ell X A) (blocked : A → Bool) : Config L M ell S X A → Prop
  | .pending _ _ _ (.repairing p s) => ∃ a,choose R p s=some a ∧ blocked a=true
  | _ => False

theorem step_eq_of_no_chosen (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (blocked : A → Bool) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (hq : ¬ChosenBlocked R blocked q) :
    step P R stop ordinary rich q=step P (suppress R blocked) stop ordinary rich q := by
  cases q with
  | ready n a s => rfl
  | finished a s => rfl
  | pending n a output phase =>
    cases phase with
    | delivered p before after => rfl
    | frozen p s => rfl
    | normal p s =>
      cases hs : stop s <;> simp [step,guardedTick,freeze,hs,tick,normal,suppress]
    | repairing p s =>
      have hc := choose_suppress_eq R blocked p s (fun a ha => by
        cases hb : blocked a with
        | false => rfl
        | true => exact (hq ⟨a,ha,hb⟩).elim)
      cases hs : stop s with
      | true => simp [step,guardedTick,freeze,hs,tick]
      | false =>
        simp only [step,guardedTick,freeze,hs,Bool.false_eq_true,if_false,tick,hc]
        rfl

theorem run_eq_of_no_chosen (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (blocked : A → Bool) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (N : ℕ)
    (h : ∀ i<N,¬ChosenBlocked R blocked (run P R stop ordinary rich i q)) :
    run P R stop ordinary rich N q=run P (suppress R blocked) stop ordinary rich N q := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [run_succ_end,run_succ_end,← ih (fun i hi => h i (by omega))]
    exact step_eq_of_no_chosen P R blocked stop ordinary rich _ (h N (by omega))

end GradientHessian.ControllerChosenSuppression
