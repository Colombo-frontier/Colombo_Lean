import GradientHessian.ControllerAdaptiveMeasurability
import GradientHessian.PolicyEarlyExpectation

noncomputable section
namespace GradientHessian.ControllerAdaptiveExecution
open Classical TaskState ComparisonController ComparisonControllerLedger ControllerMeasurable

variable {Ω Seed S X Y Z A : Type*} {L M ell : ℕ}
variable [MeasurableSpace Ω] [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable (priority : List A) (target : A → FrontierState.Node L)
  (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
  (htrigger : ∀ s a,Measurable (fun q : Ω × X => trigger q.1 s q.2 a))
  (hhit : ∀ s,Measurable (fun q : Ω × X => hit q.1 s q.2))
  (P : Machine.Policy Seed S X Y Z)
  (ordinary : Ω → State L M ell → State L M ell → X → Y)
  (rich : Ω → State L M ell → State L M ell → X → Z)
  (ho : ∀ b a,Measurable (fun q : Ω × X => ordinary q.1 b a q.2))
  (hr : ∀ b a,Measurable (fun q : Ω × X => rich q.1 b a q.2))
  (charge : Ω → Pending X → State L M ell → ℕ)
  (hcharge : ∀ (p : Ω → Pending X),Measurable p → ∀ (s : Ω → State L M ell),Measurable s →
    Measurable (fun w => charge w (p w) (s w)))

include htrigger hhit ho hr hcharge in
theorem adaptive_tally_measurable (N : ℕ) (a : Ω → S) (ha : Measurable a)
    (s : Ω → State L M ell) (hs : Measurable s) :
    Measurable (fun w => tally (parameterRules priority target trigger hit w) (charge w)
      (queries P (parameterRules priority target trigger hit w) (ordinary w) (rich w) N (a w) (s w)) (s w)) := by
  induction N generalizing a s with
  | zero =>
    simpa only [queries,tally,Nat.add_zero] using hcharge
      (fun w => Pending.mk (P.output (a w)) .ordinary)
      (measurable_pending_mk (P.output_measurable.comp ha) measurable_const) s hs
  | succ N ih =>
    have hm := P.mode_measurable.comp ha
    have hq := queryPoint_measurable P a ha
    have hc := serve_along_measurable priority target trigger hit htrigger hhit _ hq s hs
    have hn := replyNext_measurable priority target trigger hit htrigger hhit P ordinary rich ho hr a ha s hs
    have hout := hcharge (fun w => Pending.mk (P.output (a w)) .ordinary)
      (measurable_pending_mk (P.output_measurable.comp ha) measurable_const) s hs
    have ht := ih (fun w => P.think (a w)) (P.think_measurable.comp ha) s hs
    have hquery := (hcharge _ hq s hs).add (ih _ hn _ (measurable_receipt_afterNormal.comp hc))
    have hf := Measurable.ite (p := fun w => P.mode (a w)=0) (hm (measurableSet_singleton 0)) hout
      (Measurable.ite (p := fun w => P.mode (a w)=1) (hm (measurableSet_singleton 1)) ht hquery)
    convert hf using 1
    funext w
    by_cases h0 : P.mode (a w)=0
    · simp only [queries,if_pos h0,tally,Nat.add_zero]
    · by_cases h1 : P.mode (a w)=1 <;> simp [queries,h0,h1,tally,Function.comp_def]

include htrigger hhit ho hr in
theorem adaptive_task_count_measurable (N : ℕ) (a : Ω → S) (ha : Measurable a)
    (s : Ω → State L M ell) (hs : Measurable s) (q : ControllerEarlyEvents.Task L M) :
    Measurable (fun w => ControllerEarlyEvents.count (parameterRules priority target trigger hit w)
      (queries P (parameterRules priority target trigger hit w) (ordinary w) (rich w) N (a w) (s w)) (s w) q) := by
  exact adaptive_tally_measurable priority target trigger hit htrigger hhit P ordinary rich ho hr
    (fun w p s => ControllerEarlyEvents.earlyFor (parameterRules priority target trigger hit w) p s q)
    (fun p hp s hs => PolicyEarlyExpectation.earlyFor_along_measurable
      priority target trigger hit htrigger hhit p hp s hs q) N a ha s hs

end GradientHessian.ControllerAdaptiveExecution
