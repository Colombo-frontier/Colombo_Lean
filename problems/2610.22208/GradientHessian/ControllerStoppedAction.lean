import GradientHessian.ControllerActionRealization
import GradientHessian.ControllerDriverMonotonicity

/-! Original-policy repair events embed into the suppressed stopped driver.
The finite time cap is explicit; disclosure persistence and receipt-local
decoder correctness are the only structural premises, instantiated by the
literal geometric controller. -/

noncomputable section
namespace GradientHessian.ControllerStoppedAction
open Classical TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerRepairEvents ControllerDriverMonotonicity

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

theorem original_action_has_shadow_hit (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (o : X → Y) (r : X → Z)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (Inv : State L M ell → Prop)
    (hready : ∀ s,Inv s → Ready s)
    (hInv : ∀ s,Inv s → ∀ p,Inv (serve R p s).afterNormal)
    (ho : ∀ s,Inv s → ∀ p,ordinary (serve R p s).beforeNormal (serve R p s).afterNormal p.point=o p.point)
    (hr : ∀ s,Inv s → ∀ p,rich (serve R p s).beforeNormal (serve R p s).afterNormal p.point=r p.point)
    (a : A) (blocked : A → Bool) (hb : blocked a=true) (stop : State L M ell → Bool)
    (hretire : ∀ s,Ready s → ∀ b,stop s=true → stop (retireNode s (R.target b))=true)
    (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)
    (hchosen : ∀ p s,choose R p s=some a → stop s=false)
    (hell : 0<ell) (N : ℕ) (seed : Seed) (s : State L M ell) (hs : Inv s)
    (ha : a ∈ actions R (ControllerPolicyTrace.withOutput P o r N seed) s) :
    ∃ j<(N+1)*(8^L+4), ControllerPolicyCoupling.BlockedHit R blocked stop
      (run P (suppress R blocked) stop ordinary rich j (ControllerPolicyDriver.initial P N seed s)) := by
  obtain ⟨i,hi,n,b,output,p,u,hu,hchoose⟩ :=
    ControllerActionRealization.original_action_realized P R o r ordinary rich Inv hInv ho hr N seed s hs a ha
  have hphase : run P R stop ordinary rich i (ControllerPolicyDriver.initial P N seed s)=
      .pending n b output (.repairing p u) := by
    have he := guarded_eq_at_open_endpoint P R stop ordinary rich hell hretire hnormal
      (ControllerPolicyDriver.initial P N seed s) (hready s hs) i
      (show stop (stateOf (run P R (fun _ => false) ordinary rich i
        (ControllerPolicyDriver.initial P N seed s)))=false from by
        rw [hu]
        exact hchosen p u hchoose)
    exact he.trans hu
  obtain ⟨j,hj,hjhit⟩ := ControllerPolicyCoupling.chosen_blocked_has_shadow_hit P R blocked stop ordinary rich
    (ControllerPolicyDriver.initial P N seed s) i n b output p u a hphase (hchosen p u hchoose) hchoose hb
  exact ⟨j,hj.trans_lt hi,hjhit⟩

end GradientHessian.ControllerStoppedAction
