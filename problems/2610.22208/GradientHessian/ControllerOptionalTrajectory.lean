import GradientHessian.ControllerTrajectoryMeasurability

/-! Measurability for a finite schedule with measurable query-presence
bits. This permits actual policies to skip halt/internal steps, so the
selected list can have parameter-dependent length. -/

noncomputable section
namespace GradientHessian.ControllerOptionalTrajectory
open Classical MeasureTheory TaskState ComparisonController ComparisonControllerLedger
  ControllerRepairEvents ControllerMeasurable

variable {Ω X A : Type*} {L M ell : ℕ}
variable [MeasurableSpace Ω] [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

abbrev Schedule (Ω X : Type*) := List ((Ω → Bool) × (Ω → Pending X))

def selected : Schedule Ω X → Ω → List (Pending X)
  | [],_ => []
  | e::es,w => if e.1 w then e.2 w::selected es w else selected es w

def IsMeasurable (es : Schedule Ω X) : Prop :=
  ∀ e ∈ es,Measurable e.1 ∧ Measurable e.2

variable (priority : List A) (target : A → FrontierState.Node L)
  (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
  (htrigger : ∀ s a, Measurable (fun p : Ω × X => trigger p.1 s p.2 a))
  (hhit : ∀ s, Measurable (fun p : Ω × X => hit p.1 s p.2))

include htrigger hhit in
theorem run_measurable (es : Schedule Ω X) (hes : IsMeasurable es)
    (s : Ω → State L M ell) (hs : Measurable s) :
    Measurable (fun w => VisibilityWindow.run (parameterRules priority target trigger hit w) (selected es w) (s w)) := by
  classical
  induction es generalizing s with
  | nil => exact hs
  | cons e es ih =>
    have he := hes e List.mem_cons_self
    have htail : IsMeasurable es := fun q hq => hes q (List.mem_cons_of_mem e hq)
    have hr := serve_along_measurable priority target trigger hit htrigger hhit e.2 he.2 s hs
    have ha := measurable_receipt_afterNormal.comp hr
    have ht := ih htail _ ha
    have hf := ih htail s hs
    have hbranch : Measurable (fun w => if e.1 w=true then
        VisibilityWindow.run (parameterRules priority target trigger hit w) (selected es w)
          (serve (parameterRules priority target trigger hit w) (e.2 w) (s w)).afterNormal
        else VisibilityWindow.run (parameterRules priority target trigger hit w) (selected es w) (s w)) :=
      Measurable.ite (he.1 (measurableSet_singleton true)) ht hf
    convert hbranch using 1
    funext w
    by_cases hb : e.1 w=true <;> simp [selected,hb,VisibilityWindow.run]

include htrigger hhit in
theorem tally_measurable (cost : Ω → Pending X → State L M ell → ℕ)
    (hcost : ∀ (p : Ω → Pending X),Measurable p → ∀ (s : Ω → State L M ell),Measurable s →
      Measurable (fun w => cost w (p w) (s w)))
    (es : Schedule Ω X) (hes : IsMeasurable es) (s : Ω → State L M ell) (hs : Measurable s) :
    Measurable (fun w => tally (parameterRules priority target trigger hit w) (cost w) (selected es w) (s w)) := by
  classical
  induction es generalizing s with
  | nil => exact measurable_const
  | cons e es ih =>
    have he := hes e List.mem_cons_self
    have htail : IsMeasurable es := fun q hq => hes q (List.mem_cons_of_mem e hq)
    have hr := serve_along_measurable priority target trigger hit htrigger hhit e.2 he.2 s hs
    have ha := measurable_receipt_afterNormal.comp hr
    have ht := (hcost e.2 he.2 s hs).add (ih htail _ ha)
    have hf := ih htail s hs
    have hbranch : Measurable (fun w => if e.1 w=true then
        cost w (e.2 w) (s w)+tally (parameterRules priority target trigger hit w) (cost w) (selected es w)
          (serve (parameterRules priority target trigger hit w) (e.2 w) (s w)).afterNormal
        else tally (parameterRules priority target trigger hit w) (cost w) (selected es w) (s w)) :=
      Measurable.ite (he.1 (measurableSet_singleton true)) ht hf
    convert hbranch using 1
    funext w
    by_cases hb : e.1 w=true <;> simp [selected,hb,tally]

include htrigger hhit in
theorem repair_tally_measurable (es : Schedule Ω X) (hes : IsMeasurable es)
    (s : Ω → State L M ell) (hs : Measurable s) :
    Measurable (fun w => tally (parameterRules priority target trigger hit w)
      (repairs (parameterRules priority target trigger hit w)) (selected es w) (s w)) :=
  tally_measurable priority target trigger hit htrigger hhit
    (fun w => repairs (parameterRules priority target trigger hit w))
    (repairs_along_measurable priority target trigger hit htrigger) es hes s hs

include htrigger hhit in
theorem action_event_measurable (es : Schedule Ω X) (hes : IsMeasurable es)
    (s : Ω → State L M ell) (hs : Measurable s) (a : A) :
    MeasurableSet {w | a ∈ actions (parameterRules priority target trigger hit w) (selected es w) (s w)} := by
  classical
  induction es generalizing s with
  | nil => simp [selected,actions]
  | cons e es ih =>
    have he := hes e List.mem_cons_self
    have htail : IsMeasurable es := fun q hq => hes q (List.mem_cons_of_mem e hq)
    have hr := serve_along_measurable priority target trigger hit htrigger hhit e.2 he.2 s hs
    have ha := measurable_receipt_afterNormal.comp hr
    have ht := ih htail _ ha
    have hf := ih htail s hs
    have hp := point_action_event_measurable priority target trigger hit htrigger e.2 he.2 s hs (8^L) a
    have hb := he.1 (measurableSet_singleton true)
    have hset := (hb.inter (hp.union ht)).union (hb.compl.inter hf)
    convert hset using 1
    ext w
    by_cases h : e.1 w=true <;> simp [selected,h,actions,List.mem_append]

end GradientHessian.ControllerOptionalTrajectory
