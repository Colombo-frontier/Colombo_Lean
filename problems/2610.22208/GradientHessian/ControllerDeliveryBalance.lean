import GradientHessian.ControllerDriverTaskBounds

/-! Every charged delivery after the initial pending point has a preceding
normal operation. This accounting does not require a relation between the
two snapshots stored in the initial configuration. -/

noncomputable section
namespace GradientHessian.ControllerDriverResource
open Classical TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerDriverMonotonicity

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (stop : State L M ell → Bool)
  (o : State L M ell → State L M ell → X → Y)
  (v : State L M ell → State L M ell → X → Z)
  (qual : State L M ell → Bool)

theorem next_delivery_le_normal (q : Config L M ell S X A) :
    deliveryBit qual stop (step P R stop o v q)≤normalBit qual stop q := by
  cases q with
  | finished a s => rfl
  | ready n a s => simp only [step]; split_ifs <;> exact Nat.le_refl _
  | pending n a output phase =>
    cases phase with
    | frozen p s => rfl
    | delivered p before after =>
      simp only [step,deliver]
      split_ifs <;> try exact Nat.le_refl _
      cases p.kind <;> exact Nat.le_refl _
    | repairing p s =>
      cases hs : stop s with
      | true => simp [step,guardedTick,freeze,hs,tick,normalBit,deliveryBit]
      | false =>
        cases hc : choose R p s with
        | none => simp [step,guardedTick,freeze,hs,tick,hc,normalBit,deliveryBit]
        | some b =>
          cases ht : stop (retireNode s (R.target b)) <;>
            simp [step,guardedTick,freeze,hs,tick,hc,ht,normalBit,deliveryBit]
    | normal p s =>
      cases hs : stop s <;> cases ht : stop (normal R p s) <;>
        cases output <;> cases hk : p.kind <;> cases hh : qual s <;>
          simp [step,guardedTick,freeze,hs,tick,ht,hk,hh,normalBit,deliveryBit]

theorem delivery_count_le_normal (N : ℕ) (q : Config L M ell S X A) :
    count P R stop o v (deliveryBit qual stop) N q≤
      count P R stop o v (normalBit qual stop) N q+deliveryBit qual stop q := by
  induction N generalizing q with
  | zero => simp [count]
  | succ N ih =>
    have hi := ih (step P R stop o v q)
    have hs := next_delivery_le_normal P R stop o v qual q
    simp only [count]
    omega

theorem delivery_count_le_normal_add_one (N : ℕ) (q : Config L M ell S X A) :
    count P R stop o v (deliveryBit qual stop) N q≤
      count P R stop o v (normalBit qual stop) N q+1 := by
  have hc := delivery_count_le_normal P R stop o v qual N q
  have hb := deliveryBit_le_one stop qual q
  omega

end GradientHessian.ControllerDriverResource
