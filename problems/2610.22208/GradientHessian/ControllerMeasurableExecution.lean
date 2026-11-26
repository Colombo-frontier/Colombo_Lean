import GradientHessian.ControllerMeasurableTypes

/-! Measurability of the executable finite-priority repair controller.
The only inputs are measurable literal trigger and normal-hit functions;
all finite branches, retirement updates and snapshot records are compiled. -/

noncomputable section
namespace GradientHessian.ControllerMeasurable
open Classical TaskState ComparisonController

variable {Ω X A : Type*} {L M ell : ℕ}
variable [MeasurableSpace Ω] [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

def parameterRules (priority : List A) (target : A → FrontierState.Node L)
    (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
    (w : Ω) : Rules L M ell X A := ⟨priority,target,trigger w,hit w⟩

variable (priority : List A) (target : A → FrontierState.Node L)
  (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
  (htrigger : ∀ s a, Measurable (fun p : Ω × X => trigger p.1 s p.2 a))
  (hhit : ∀ s, Measurable (fun p : Ω × X => hit p.1 s p.2))

include htrigger in
theorem choose_fixed_measurable (s : State L M ell) :
    Measurable (fun q : Ω × Pending X => choose (parameterRules priority target trigger hit q.1) q.2 s) := by
  let f : (A → Bool) → Option A := fun values => List.find? (fun a =>
    values a && decide ((FrontierState.subtree (target a) \ TaskState.retired s).Nonempty)) priority
  have hv : Measurable (fun q : Ω × Pending X => fun a => trigger q.1 s q.2.point a) := by
    apply measurable_pi_lambda
    intro a
    exact (htrigger s a).comp (measurable_fst.prodMk (measurable_pending_point.comp measurable_snd))
  exact (measurable_of_countable f).comp hv

include htrigger in
theorem repairRun_fixed_measurable (n : ℕ) : ∀ s : State L M ell,
    Measurable (fun q : Ω × Pending X => repairRun (parameterRules priority target trigger hit q.1) q.2 n s) := by
  induction n with
  | zero => intro s; exact measurable_const
  | succ n ih =>
    intro s
    let step : (Ω × Pending X) × Option A → State L M ell × List (State L M ell × A) := fun q =>
      match q.2 with
      | none => (s,[])
      | some a =>
        let out := repairRun (parameterRules priority target trigger hit q.1.1) q.1.2 n (retireNode s (target a))
        (out.1,(s,a)::out.2)
    have hstep : Measurable step := by
      apply measurable_from_prod_countable
      intro a
      cases a with
      | none => exact measurable_const
      | some a =>
        exact (measurable_of_countable (fun out : State L M ell × List (State L M ell × A) =>
          (out.1,(s,a)::out.2))).comp (ih (retireNode s (target a)))
    exact hstep.comp (measurable_id.prodMk (choose_fixed_measurable priority target trigger hit htrigger s))

include htrigger in
theorem repairRun_joint_measurable (n : ℕ) :
    Measurable (fun q : (Ω × Pending X) × State L M ell =>
      repairRun (parameterRules priority target trigger hit q.1.1) q.1.2 n q.2) :=
  measurable_from_prod_countable (repairRun_fixed_measurable priority target trigger hit htrigger n)

include hhit in
theorem normal_fixed_measurable (s : State L M ell) :
    Measurable (fun q : Ω × Pending X => normal (parameterRules priority target trigger hit q.1) q.2 s) := by
  have hh := (hhit s).comp (measurable_fst.prodMk (measurable_pending_point.comp measurable_snd))
  have hk := measurable_pending_kind.comp (measurable_snd : Measurable (Prod.snd : Ω × Pending X → Pending X))
  exact (measurable_of_countable (fun q : Kind × Bool => match q.1 with
    | .ordinary => TaskSlots.ordinaryStep q.2 s
    | .rich => richComplete s)).comp (hk.prodMk hh)

include hhit in
theorem normal_joint_measurable :
    Measurable (fun q : (Ω × Pending X) × State L M ell =>
      normal (parameterRules priority target trigger hit q.1.1) q.1.2 q.2) :=
  measurable_from_prod_countable (normal_fixed_measurable priority target trigger hit hhit)

include htrigger hhit in
theorem serve_fixed_measurable (s : State L M ell) :
    Measurable (fun q : Ω × Pending X => serve (parameterRules priority target trigger hit q.1) q.2 s) := by
  have hr := repairRun_fixed_measurable priority target trigger hit htrigger (8^L) s
  have hb := measurable_fst.comp hr
  have ht := measurable_snd.comp hr
  have ha := (normal_joint_measurable priority target trigger hit hhit).comp (measurable_id.prodMk hb)
  exact (receiptMeasurableEquiv L M ell X A).symm.measurable.comp
    (measurable_snd.prodMk (hb.prodMk (ha.prodMk ht)))

include htrigger hhit in
theorem serve_joint_measurable :
    Measurable (fun q : (Ω × Pending X) × State L M ell =>
      serve (parameterRules priority target trigger hit q.1.1) q.1.2 q.2) :=
  measurable_from_prod_countable (serve_fixed_measurable priority target trigger hit htrigger hhit)

end GradientHessian.ControllerMeasurable
