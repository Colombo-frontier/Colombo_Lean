import GradientHessian.ControllerAdaptiveExecution
import GradientHessian.ControllerTrajectoryMeasurability

/-! Measurable repair tallies for receipt-dependent policies. The proof
follows the actual policy/controller recursion, including halt, internal
steps, and the single virtual output. -/

noncomputable section
namespace GradientHessian.ControllerAdaptiveExecution
open Classical TaskState ComparisonController ComparisonControllerLedger ControllerRepairEvents ControllerMeasurable

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

theorem queryPoint_measurable (a : Ω → S) (ha : Measurable a) :
    Measurable (fun w => ControllerPolicyExecution.queryPoint P (a w)) :=
  measurable_pending_mk (P.point_measurable.comp ha)
    (Measurable.ite ((P.mode_measurable.comp ha) (measurableSet_singleton 2)) measurable_const measurable_const)

include htrigger hhit ho hr in
theorem replyNext_measurable (a : Ω → S) (ha : Measurable a) (s : Ω → State L M ell) (hs : Measurable s) :
    Measurable (fun w => replyNext P (parameterRules priority target trigger hit w) (ordinary w) (rich w) (a w) (s w)) := by
  have hc := serve_along_measurable priority target trigger hit htrigger hhit
    (fun w => ControllerPolicyExecution.queryPoint P (a w)) (queryPoint_measurable P a ha) s hs
  have hb := measurable_receipt_beforeNormal.comp hc
  have he := measurable_receipt_afterNormal.comp hc
  have hxy := measurable_id.prodMk (P.point_measurable.comp ha)
  have hf : Measurable (fun q : (Ω × X) × (State L M ell × State L M ell) => ordinary q.1.1 q.2.1 q.2.2 q.1.2) :=
    measurable_from_prod_countable (fun s => ho s.1 s.2)
  have hg : Measurable (fun q : (Ω × X) × (State L M ell × State L M ell) => rich q.1.1 q.2.1 q.2.2 q.1.2) :=
    measurable_from_prod_countable (fun s => hr s.1 s.2)
  exact Measurable.ite ((P.mode_measurable.comp ha) (measurableSet_singleton 2))
    (P.ordinaryNext_measurable.comp (ha.prodMk (hf.comp (hxy.prodMk (hb.prodMk he)))))
    (P.richNext_measurable.comp (ha.prodMk (hg.comp (hxy.prodMk (hb.prodMk he)))))

include htrigger hhit ho hr in
theorem repair_count_measurable (N : ℕ) (a : Ω → S) (ha : Measurable a)
    (s : Ω → State L M ell) (hs : Measurable s) :
    Measurable (fun w => tally (parameterRules priority target trigger hit w)
      (repairs (parameterRules priority target trigger hit w))
      (queries P (parameterRules priority target trigger hit w) (ordinary w) (rich w) N (a w) (s w)) (s w)) := by
  classical
  induction N generalizing a s with
  | zero =>
    simpa only [queries,tally,Nat.add_zero] using repairs_along_measurable priority target trigger hit htrigger
      (fun w => Pending.mk (P.output (a w)) .ordinary) (measurable_pending_mk (P.output_measurable.comp ha) measurable_const) s hs
  | succ N ih =>
    have hm := P.mode_measurable.comp ha
    have hq := queryPoint_measurable P a ha
    have hc := serve_along_measurable priority target trigger hit htrigger hhit _ hq s hs
    have hn := replyNext_measurable priority target trigger hit htrigger hhit P ordinary rich ho hr a ha s hs
    have hout := repairs_along_measurable priority target trigger hit htrigger
      (fun w => Pending.mk (P.output (a w)) .ordinary) (measurable_pending_mk (P.output_measurable.comp ha) measurable_const) s hs
    have ht := ih (fun w => P.think (a w)) (P.think_measurable.comp ha) s hs
    have hquery := (repairs_along_measurable priority target trigger hit htrigger _ hq s hs).add
      (ih _ hn _ (measurable_receipt_afterNormal.comp hc))
    have hf := Measurable.ite (p := fun w => P.mode (a w)=0) (hm (measurableSet_singleton 0)) hout
      (Measurable.ite (p := fun w => P.mode (a w)=1) (hm (measurableSet_singleton 1)) ht hquery)
    convert hf using 1
    funext w
    by_cases h0 : P.mode (a w)=0
    · simp only [queries,if_pos h0,tally,Nat.add_zero]
    · by_cases h1 : P.mode (a w)=1 <;> simp [queries,h0,h1,tally,Function.comp_def]

theorem decide_event_measurable {p : Ω → Prop} [DecidablePred p] (hp : MeasurableSet {w | p w}) :
    Measurable (fun w => decide (p w)) := by
  have h : Measurable (fun w => if p w then true else false) := Measurable.ite hp measurable_const measurable_const
  convert h using 1

include htrigger hhit ho hr in
theorem action_decide_measurable (N : ℕ) (a : Ω → S) (ha : Measurable a)
    (s : Ω → State L M ell) (hs : Measurable s) (b : A) :
    Measurable (fun w => decide (b ∈ actions (parameterRules priority target trigger hit w)
      (queries P (parameterRules priority target trigger hit w) (ordinary w) (rich w) N (a w) (s w)) (s w))) := by
  classical
  induction N generalizing a s with
  | zero =>
    have h := point_action_event_measurable priority target trigger hit htrigger
      (fun w => Pending.mk (P.output (a w)) .ordinary) (measurable_pending_mk (P.output_measurable.comp ha) measurable_const) s hs (8^L) b
    simpa only [queries,actions,List.append_nil] using decide_event_measurable h
  | succ N ih =>
    have hm := P.mode_measurable.comp ha
    have hq := queryPoint_measurable P a ha
    have hc := serve_along_measurable priority target trigger hit htrigger hhit _ hq s hs
    have hn := replyNext_measurable priority target trigger hit htrigger hhit P ordinary rich ho hr a ha s hs
    have hout := decide_event_measurable (point_action_event_measurable priority target trigger hit htrigger
      (fun w => Pending.mk (P.output (a w)) .ordinary) (measurable_pending_mk (P.output_measurable.comp ha) measurable_const) s hs (8^L) b)
    have ht := ih (fun w => P.think (a w)) (P.think_measurable.comp ha) s hs
    have hhead := decide_event_measurable (point_action_event_measurable priority target trigger hit htrigger _ hq s hs (8^L) b)
    have htail := ih _ hn _ (measurable_receipt_afterNormal.comp hc)
    have hquery := (measurable_of_countable (fun z : Bool × Bool => z.1 || z.2)).comp (hhead.prodMk htail)
    have hf := Measurable.ite (p := fun w => P.mode (a w)=0) (hm (measurableSet_singleton 0)) hout
      (Measurable.ite (p := fun w => P.mode (a w)=1) (hm (measurableSet_singleton 1)) ht hquery)
    convert hf using 1
    funext w
    by_cases h0 : P.mode (a w)=0
    · simp only [queries,if_pos h0,actions,List.append_nil]
    · by_cases h1 : P.mode (a w)=1
      · simp only [queries,if_neg h0,if_pos h1]
      · simp [queries,h0,h1,actions,Function.comp_def]

include htrigger hhit ho hr in
theorem action_event_measurable (N : ℕ) (a : Ω → S) (ha : Measurable a)
    (s : Ω → State L M ell) (hs : Measurable s) (b : A) :
    MeasurableSet {w | b ∈ actions (parameterRules priority target trigger hit w)
      (queries P (parameterRules priority target trigger hit w) (ordinary w) (rich w) N (a w) (s w)) (s w)} := by
  have h := (action_decide_measurable priority target trigger hit htrigger hhit P ordinary rich ho hr N a ha s hs b)
    (measurableSet_singleton true)
  convert h using 1
  ext w
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_setOf_eq,decide_eq_true_eq]

end GradientHessian.ControllerAdaptiveExecution
