import GradientHessian.ControllerDeliveryBalance

/-! The post-mark driver stays in its initial task while the disclosure
guard is open. Its ordinary normal phases and numerical replies therefore
have the literal per-task caps, even from a pending prior-task delivery. -/

noncomputable section
namespace GradientHessian.ControllerDriverResource
open Classical FrontierState TaskState TaskSlots ComparisonController
  ComparisonControllerReplay ControllerPolicyDriver ControllerDriverMonotonicity
  VisibilityWindow VisibilityTaskWindow

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (stop : State L M ell → Bool)
  (o : State L M ell → State L M ell → X → Y)
  (v : State L M ell → State L M ell → X → Z)

theorem state_value_step (W : State L M ell → ℕ)
    (hr : ∀ s,Ready s → ∀ a,W s≤W (retireNode s (R.target a)))
    (hn : ∀ s,Ready s → ∀ p,W s≤W (normal R p s))
    (q : Config L M ell S X A) (hq : Good q) :
    W (stateOf q)≤W (stateOf (step P R stop o v q)) := by
  have hp : ∀ s,Ready s → ∀ p : Pending X,p.kind=.ordinary → (false : Bool)=true → W s<W (normal R p s) := by
    intro s hs p hk hh
    cases hh
  have h := normal_step_credit P R stop o v (fun _ => false) W hr hn hp q hq
  omega

theorem state_value_run (hell : 0<ell) (W : State L M ell → ℕ)
    (hr : ∀ s,Ready s → ∀ a,W s≤W (retireNode s (R.target a)))
    (hn : ∀ s,Ready s → ∀ p,W s≤W (normal R p s))
    (q : Config L M ell S X A) (hq : Good q) (N : ℕ) :
    W (stateOf q)≤W (stateOf (ControllerPolicyDriver.run P R stop o v N q)) := by
  induction N generalizing q with
  | zero => exact le_rfl
  | succ N ih =>
    exact (state_value_step P R stop o v W hr hn q hq).trans
      (ih _ (step_good P R stop o v hell q hq))

theorem run_completed_mono (hell : 0<ell) (q : Config L M ell S X A)
    (hq : Good q) (N : ℕ) (leaf : Leaf L) :
    ((stateOf q).completed leaf).val≤
      ((stateOf (ControllerPolicyDriver.run P R stop o v N q)).completed leaf).val :=
  state_value_run P R stop o v hell (fun s => (s.completed leaf).val)
    (fun s _ a => retireSet_completed_mono s (subtree (R.target a)) leaf)
    (fun s hs p => normal_completed_mono R p hs leaf) q hq N

theorem run_retired_mono (hell : 0<ell) (q : Config L M ell S X A)
    (hq : Good q) (N : ℕ) :
    TaskState.retired (stateOf q)⊆TaskState.retired (stateOf (ControllerPolicyDriver.run P R stop o v N q)) := by
  intro leaf hl
  have hm := run_completed_mono P R stop o v hell q hq N leaf
  have he := (mem_retired _ _).mp hl
  have hb := ((stateOf (ControllerPolicyDriver.run P R stop o v N q)).completed leaf).isLt
  apply (mem_retired _ _).mpr
  omega

theorem post_window (hell : 0<ell) (leaf : Leaf L) (j : Fin M)
    (q : Config L M ell S X A) (hq : Good q)
    (hcur : TaskState.current (stateOf q)=some leaf)
    (hindex : ((stateOf q).completed leaf).val=j.val) (N : ℕ)
    (hopen : taskDisclosed leaf j (stateOf (ControllerPolicyDriver.run P R stop o v N q))=false) :
    onTask leaf j (stateOf (ControllerPolicyDriver.run P R stop o v N q))=true := by
  have hm := run_completed_mono P R stop o v hell q hq N leaf
  have hle := of_decide_eq_false hopen
  have hj : ((stateOf (ControllerPolicyDriver.run P R stop o v N q)).completed leaf).val=j.val := by
    change ¬j.val<((stateOf (ControllerPolicyDriver.run P R stop o v N q)).completed leaf).val at hle
    omega
  have hnr : leaf∉TaskState.retired (stateOf (ControllerPolicyDriver.run P R stop o v N q)) := by
    intro hh
    have he := (mem_retired _ _).mp hh
    have := j.isLt
    omega
  have hc := current_preserved (run_retired_mono P R stop o v hell q hq N) hcur hnr
  simp [onTask,hc,hj]

theorem normalBit_eq_task (leaf : Leaf L) (j : Fin M) (q : Config L M ell S X A)
    (hw : taskDisclosed leaf j (stateOf q)=false → onTask leaf j (stateOf q)=true) :
    normalBit (fun _ => true) (taskDisclosed leaf j) q=normalBit (onTask leaf j) (taskDisclosed leaf j) q ∧
    normalBit (onLeaf leaf) (taskDisclosed leaf j) q=normalBit (onTask leaf j) (taskDisclosed leaf j) q := by
  cases q with
  | ready n a s => exact ⟨rfl,rfl⟩
  | finished a s => exact ⟨rfl,rfl⟩
  | pending n a output phase =>
    cases phase with
    | repairing p s => exact ⟨rfl,rfl⟩
    | delivered p before after => exact ⟨rfl,rfl⟩
    | frozen p s => exact ⟨rfl,rfl⟩
    | normal p s =>
      cases hs : taskDisclosed leaf j s with
      | true => simp [normalBit,hs]
      | false =>
        have ht : onTask leaf j s=true := hw hs
        have hh := of_decide_eq_true ht
        have hl : onLeaf leaf s=true := by simp [onLeaf,hh.1]
        simp [normalBit,hs,ht,hl]

theorem post_normal_bound (hell : 0<ell) (leaf : Leaf L) (j : Fin M)
    (q : Config L M ell S X A) (hq : Good q)
    (hcur : TaskState.current (stateOf q)=some leaf)
    (hindex : ((stateOf q).completed leaf).val=j.val) (N : ℕ) :
    count P R (taskDisclosed leaf j) o v (normalBit (fun _ => true) (taskDisclosed leaf j)) N q≤ell ∧
    count P R (taskDisclosed leaf j) o v (normalBit (onLeaf leaf) (taskDisclosed leaf j)) N q≤ell := by
  have he (i : ℕ) := normalBit_eq_task leaf j (ControllerPolicyDriver.run P R (taskDisclosed leaf j) o v i q)
    (post_window P R (taskDisclosed leaf j) o v hell leaf j q hq hcur hindex i)
  have ht := task_normal_bound P R (taskDisclosed leaf j) o v hell leaf j N q hq
  rw [count_eq_sum] at ht
  constructor
  · rw [count_eq_sum]
    simpa only [fun i => (he i).1] using ht
  · rw [count_eq_sum]
    simpa only [fun i => (he i).2] using ht

theorem post_product_bound (hell : 0<ell) (leaf : Leaf L) (j : Fin M)
    (q : Config L M ell S X A) (hq : Good q)
    (hcur : TaskState.current (stateOf q)=some leaf)
    (hindex : ((stateOf q).completed leaf).val=j.val) (N : ℕ) :
    (∑ i∈Finset.range N,if NumericalDriverInstructions.product leaf (taskDisclosed leaf j)
      (ControllerPolicyDriver.run P R (taskDisclosed leaf j) o v i q)=true then 1 else 0)≤ell+1 := by
  simp_rw [product_deliveryBit]
  rw [← count_eq_sum]
  have hd := delivery_count_le_normal_add_one P R (taskDisclosed leaf j) o v (onLeaf leaf) N q
  have hn := (post_normal_bound P R o v hell leaf j q hq hcur hindex N).2
  omega

end GradientHessian.ControllerDriverResource
