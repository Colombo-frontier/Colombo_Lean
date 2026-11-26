import GradientHessian.ControllerDriverResource

/-! Literal matrix-product and selected-test bounds for the chronological
driver. They hold at every finite cutoff and permit an initially pending
query. -/

noncomputable section
namespace GradientHessian.ControllerDriverResource
open Classical FrontierState TaskState TaskSlots ComparisonController
  ComparisonControllerReplay ControllerPolicyDriver ControllerDriverMonotonicity
  VisibilityWindow VisibilityTaskWindow

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def onLeaf (leaf : Leaf L) (s : State L M ell) : Bool := decide (TaskState.current s=some leaf)
def onTask (leaf : Leaf L) (j : Fin M) (s : State L M ell) : Bool :=
  decide (TaskState.current s=some leaf ∧ (s.completed leaf).val=j.val)

variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (stop : State L M ell → Bool)
  (o : State L M ell → State L M ell → X → Y)
  (v : State L M ell → State L M ell → X → Z)

theorem leaf_delivery_bound (hell : 0<ell) (leaf : Leaf L)
    (N : ℕ) (q : Config L M ell S X A) (hq : Good q) :
    count P R stop o v (deliveryBit (onLeaf leaf) stop) N q≤M*ell+1 := by
  apply delivery_count_bound P R stop o v (onLeaf leaf) (fun s => work s leaf)
    (fun s hs a => retireSet_work_mono hs.1 (subtree (R.target a)) leaf)
    (fun s hs p => normal_work_mono R p hs leaf)
    (fun s hs p _ hh => normal_current_progress R p hs (of_decide_eq_true hh))
    hell (M*ell) (fun s hs => work_le hs.1 leaf) N q hq

theorem product_deliveryBit (leaf : Leaf L) (q : Config L M ell S X A) :
    (if NumericalDriverInstructions.product leaf stop q=true then 1 else 0)=
      deliveryBit (onLeaf leaf) stop q := by
  cases q with
  | ready n a s => simp [NumericalDriverInstructions.product,deliveryBit]
  | finished a s => simp [NumericalDriverInstructions.product,deliveryBit]
  | pending n a output phase =>
    cases phase <;> simp [NumericalDriverInstructions.product,deliveryBit,onLeaf]

theorem actual_product_bound (hell : 0<ell) (leaf : Leaf L)
    (N : ℕ) (q : Config L M ell S X A) (hq : Good q) :
    (∑ i∈Finset.range N,if NumericalDriverInstructions.product leaf stop
      (ControllerPolicyDriver.run P R stop o v i q)=true then 1 else 0)≤M*ell+1 := by
  simp_rw [product_deliveryBit]
  rw [← count_eq_sum]
  exact leaf_delivery_bound P R stop o v hell leaf N q hq

theorem task_retire_credit (leaf : Leaf L) (j : Fin M) (s : State L M ell)
    (hs : Ready s) (a : A) :
    taskCredit s leaf j≤taskCredit (retireNode s (R.target a)) leaf j :=
  taskCredit_mono leaf j (retireSet_completed_mono s (subtree (R.target a)) leaf)
    (retireSet_work_mono hs.1 (subtree (R.target a)) leaf)

theorem task_normal_credit (leaf : Leaf L) (j : Fin M) (s : State L M ell)
    (hs : Ready s) (p : Pending X) :
    taskCredit s leaf j≤taskCredit (normal R p s) leaf j :=
  taskCredit_mono leaf j (normal_completed_mono R p hs leaf) (normal_work_mono R p hs leaf)

theorem task_normal_progress (leaf : Leaf L) (j : Fin M) (s : State L M ell)
    (hs : Ready s) (p : Pending X) (hh : onTask leaf j s=true) :
    taskCredit s leaf j<taskCredit (normal R p s) leaf j := by
  obtain ⟨hc,hj⟩ := of_decide_eq_true hh
  exact normal_current_task_progress R p hs j hc hj

theorem task_delivery_bound (hell : 0<ell) (leaf : Leaf L) (j : Fin M)
    (N : ℕ) (q : Config L M ell S X A) (hq : Good q) :
    count P R stop o v (deliveryBit (onTask leaf j) stop) N q≤ell+1 := by
  exact delivery_count_bound P R stop o v (onTask leaf j) (fun s => taskCredit s leaf j)
    (task_retire_credit R leaf j) (task_normal_credit R leaf j)
    (fun s hs p _ hh => task_normal_progress R leaf j s hs p hh)
    hell ell (fun s _ => taskCredit_le s leaf j) N q hq

theorem task_normal_bound (hell : 0<ell) (leaf : Leaf L) (j : Fin M)
    (N : ℕ) (q : Config L M ell S X A) (hq : Good q) :
    count P R stop o v (normalBit (onTask leaf j) stop) N q≤ell := by
  exact normal_count_bound P R stop o v (onTask leaf j) (fun s => taskCredit s leaf j)
    (task_retire_credit R leaf j) (task_normal_credit R leaf j)
    (fun s hs p _ hh => task_normal_progress R leaf j s hs p hh)
    hell ell (fun s _ => taskCredit_le s leaf j) N q hq

end GradientHessian.ControllerDriverResource
