import GradientHessian.ControllerPolicyDriver

/-! First-hit coupling for the literal phase driver. A suppressed repair
can affect the trajectory only after its predicate is true at an actual
shadow repairing phase. No reply agreement is postulated here: both runs
use the same state-dependent decoder functions. -/

noncomputable section
namespace GradientHessian.ControllerPolicyCoupling
open Classical FrontierState TaskState TaskSlots ComparisonController
  ComparisonControllerReplay ControllerPolicyDriver

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def BlockedHit (R : Rules L M ell X A) (blocked : A → Bool)
    (stop : State L M ell → Bool) : Config L M ell S X A → Prop
  | .pending _ _ _ (.repairing p s) =>
    stop s=false ∧ ∃ a, blocked a=true ∧ R.trigger s p.point a=true
  | _ => False

theorem step_eq_of_no_hit (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (blocked : A → Bool) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (hq : ¬ BlockedHit R blocked stop q) :
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
      cases hs : stop s with
      | true => simp [step,guardedTick,freeze,hs,tick]
      | false =>
        have ht (b : A) : R.trigger s p.point b=(suppress R blocked).trigger s p.point b := by
          cases hb : blocked b with
          | false => simp [suppress,hb]
          | true =>
            have hm : R.trigger s p.point b=false := by
              cases hh : R.trigger s p.point b with
              | false => rfl
              | true => exact (hq ⟨hs,b,hb,hh⟩).elim
            simp [suppress,hb,hm]
        have hc := choose_congr R (suppress R blocked) p s rfl rfl ht
        simp only [step,guardedTick,freeze,hs,Bool.false_eq_true,if_false,tick,hc]
        rfl

theorem run_succ_end (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (q : Config L M ell S X A) :
    run P R stop ordinary rich (n+1) q=step P R stop ordinary rich (run P R stop ordinary rich n q) := by
  simpa only [run] using ControllerPolicyDriver.run_add P R stop ordinary rich n 1 q

theorem run_eq_before_hit (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (blocked : A → Bool) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (N : ℕ)
    (hmiss : ∀ i<N, ¬ BlockedHit R blocked stop (run P (suppress R blocked) stop ordinary rich i q)) :
    ∀ n≤N, run P R stop ordinary rich n q=run P (suppress R blocked) stop ordinary rich n q := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [run_succ_end,run_succ_end,ih (by omega)]
    exact step_eq_of_no_hit P R blocked stop ordinary rich _ (hmiss n (by omega))

theorem first_difference_has_shadow_hit (P : Machine.Policy Seed S X Y Z)
    (R : Rules L M ell X A) (blocked : A → Bool) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (N : ℕ)
    (hdiff : run P R stop ordinary rich N q≠run P (suppress R blocked) stop ordinary rich N q) :
    ∃ i<N, BlockedHit R blocked stop (run P (suppress R blocked) stop ordinary rich i q) := by
  by_contra hh
  apply hdiff
  exact run_eq_before_hit P R blocked stop ordinary rich q N
    (fun i hi hb => hh ⟨i,hi,hb⟩) N le_rfl

theorem actual_hit_has_shadow_hit (P : Machine.Policy Seed S X Y Z)
    (R : Rules L M ell X A) (blocked : A → Bool) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (N : ℕ)
    (hhit : BlockedHit R blocked stop (run P R stop ordinary rich N q)) :
    ∃ i≤N, BlockedHit R blocked stop (run P (suppress R blocked) stop ordinary rich i q) := by
  by_cases hh : ∃ i<N, BlockedHit R blocked stop (run P (suppress R blocked) stop ordinary rich i q)
  · obtain ⟨i,hi,hb⟩ := hh
    exact ⟨i,hi.le,hb⟩
  · have he := run_eq_before_hit P R blocked stop ordinary rich q N
      (fun i hi hb => hh ⟨i,hi,hb⟩) N le_rfl
    exact ⟨N,le_rfl,he ▸ hhit⟩

theorem chosen_blocked_has_shadow_hit (P : Machine.Policy Seed S X Y Z)
    (R : Rules L M ell X A) (blocked : A → Bool) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (q : Config L M ell S X A) (N n : ℕ) (algorithm : S) (output : Bool)
    (p : Pending X) (s : State L M ell) (a : A)
    (hrun : run P R stop ordinary rich N q=.pending n algorithm output (.repairing p s))
    (hstop : stop s=false) (hchoose : choose R p s=some a) (hb : blocked a=true) :
    ∃ i≤N, BlockedHit R blocked stop (run P (suppress R blocked) stop ordinary rich i q) := by
  apply actual_hit_has_shadow_hit P R blocked stop ordinary rich q N
  rw [hrun]
  exact ⟨hstop,a,hb,(choose_spec R p s hchoose).2.1⟩

end GradientHessian.ControllerPolicyCoupling
