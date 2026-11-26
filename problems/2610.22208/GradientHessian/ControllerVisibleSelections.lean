import GradientHessian.ControllerPolicySelections
import Mathlib.Data.List.GetD

/-! Measurable bounded arrays obtained from the actual visible query list.
The list has variable length, but every padded coordinate is measurable;
its array size is the proved deterministic subtree visibility budget. -/

noncomputable section
namespace GradientHessian.ControllerVisibleSelections
open Classical FrontierState TaskState ComparisonController ComparisonControllerReplay
open ControllerMeasurable ControllerOptionalTrajectory VisibilityWindow

variable {Ω X A : Type*} {L M ell : ℕ}
variable [MeasurableSpace Ω] [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]
variable (priority : List A) (target : A → Node L)
  (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
  (htrigger : ∀ s a,Measurable (fun q : Ω × X => trigger q.1 s q.2 a))
  (hhit : ∀ s,Measurable (fun q : Ω × X => hit q.1 s q.2))

include htrigger in
theorem seen_along_measurable (v : Node L) (p : Ω → Pending X) (hp : Measurable p)
    (s : Ω → State L M ell) (hs : Measurable s) :
    MeasurableSet {w | Seen (parameterRules priority target trigger hit w) (p w) (s w) v} := by
  have hr := (repairRun_joint_measurable priority target trigger hit htrigger (8^L)).comp
    ((measurable_id.prodMk hp).prodMk hs)
  let event : State L M ell × List (State L M ell × A) → Bool :=
    fun q => decide (∃ u ∈ q.2.map Prod.fst ++ [q.1],Visible (TaskState.retired u) v)
  have hm := (measurable_of_countable event).comp hr
  convert hm (measurableSet_singleton true) using 1
  ext w
  simp only [Seen,visits,Set.mem_preimage,Set.mem_singleton_iff,Function.comp_apply,event,decide_eq_true_eq,
    Set.mem_setOf_eq,id_eq]

def queryAt (v : Node L) (es : Schedule Ω X) (s : Ω → State L M ell)
    (fallback : X) (i : ℕ) (w : Ω) : X :=
  (seenPoints (parameterRules priority target trigger hit w) v (selected es w) (s w)).getD i fallback

include htrigger hhit in
theorem queryAt_measurable (v : Node L) (es : Schedule Ω X) (hes : IsMeasurable es)
    (s : Ω → State L M ell) (hs : Measurable s) (fallback : X) (i : ℕ) :
    Measurable (queryAt priority target trigger hit v es s fallback i) := by
  induction es generalizing s i with
  | nil => exact measurable_const
  | cons e es ih =>
    have he := hes e List.mem_cons_self
    have ht : IsMeasurable es := fun f hf => hes f (List.mem_cons_of_mem e hf)
    let next : Ω → State L M ell := fun w =>
      (serve (parameterRules priority target trigger hit w) (e.2 w) (s w)).afterNormal
    have hn : Measurable next := measurable_receipt_afterNormal.comp
      (serve_along_measurable priority target trigger hit htrigger hhit e.2 he.2 s hs)
    have hseen := seen_along_measurable priority target trigger hit htrigger v e.2 he.2 s hs
    have hskip := ih ht s hs i
    have hnext := ih ht next hn i
    have htake : Measurable (fun w =>
        match i with
        | 0 => (e.2 w).point
        | k+1 => queryAt priority target trigger hit v es next fallback k w) := by
      cases i with
      | zero => exact measurable_pending_point.comp he.2
      | succ i => exact ih ht next hn i
    have h : Measurable (fun w => if e.1 w=true then
        if Seen (parameterRules priority target trigger hit w) (e.2 w) (s w) v then
          (match i with | 0 => (e.2 w).point | k+1 => queryAt priority target trigger hit v es next fallback k w)
        else queryAt priority target trigger hit v es next fallback i w
        else queryAt priority target trigger hit v es s fallback i w) :=
      Measurable.ite (he.1 (measurableSet_singleton true)) (Measurable.ite hseen htake hnext) hskip
    convert h using 1
    funext w
    by_cases hb : e.1 w=true
    · by_cases hv : Seen (parameterRules priority target trigger hit w) (e.2 w) (s w) v
      · cases i <;> simp [queryAt,selected,hb,seenPoints,hv,next]
      · simp [queryAt,selected,hb,seenPoints,hv,next]
    · simp [queryAt,selected,hb]

omit [MeasurableSpace Ω] [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem mem_padded_array {l : List X} {N : ℕ} (hN : l.length≤N) (fallback : X) {x : X}
    (hx : x ∈ l) : ∃ i : Fin N,l.getD i.val fallback=x := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  refine ⟨⟨i,hi.trans_le hN⟩,?_⟩
  rw [List.getD_eq_getElem l fallback hi]
  exact he

omit [MeasurableSpace Ω] [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem visible_array_covers (v : Node L) (es : Schedule Ω X) (s : Ω → State L M ell)
    (fallback : X) (w : Ω) (hs : TaskSlots.Ready (s w)) (hell : 0<ell) {x : X}
    (hx : x ∈ seenPoints (parameterRules priority target trigger hit w) v (selected es w) (s w)) :
    ∃ i : Fin (8^(L-v.1.val)*M*ell),queryAt priority target trigger hit v es s fallback i.val w=x :=
  mem_padded_array (seenPoints_length_le _ v _ hs hell) fallback hx

end GradientHessian.ControllerVisibleSelections
