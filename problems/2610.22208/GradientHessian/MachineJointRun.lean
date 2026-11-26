import GradientHessian.Machine

/-! Joint measurability of the original mixed policy in its raw objective
parameter and private seed. The seed is unchanged, and internal steps are
retained in the actual state recursion. -/

namespace GradientHessian.Machine
open MeasureTheory

variable {Ω Seed S X Y Z : Type*} [MeasurableSpace Ω]
  [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

theorem Policy.step_joint_measurable (P : Policy Seed S X Y Z)
    (o : Ω → X → Y) (r : Ω → X → Z)
    (ho : Measurable (fun q : Ω × X => o q.1 q.2))
    (hr : Measurable (fun q : Ω × X => r q.1 q.2)) :
    Measurable (fun q : Ω × S => P.step (o q.1) (r q.1) q.2) := by
  have hm := P.mode_measurable.comp (measurable_snd : Measurable (Prod.snd : Ω × S → S))
  have hp := P.point_measurable.comp (measurable_snd : Measurable (Prod.snd : Ω × S → S))
  unfold Policy.step
  apply Measurable.ite (hm (measurableSet_singleton 0)) measurable_snd
  apply Measurable.ite (hm (measurableSet_singleton 1)) (P.think_measurable.comp measurable_snd)
  apply Measurable.ite (hm (measurableSet_singleton 2))
  · exact P.ordinaryNext_measurable.comp (measurable_snd.prodMk (ho.comp (measurable_fst.prodMk hp)))
  · exact P.richNext_measurable.comp (measurable_snd.prodMk (hr.comp (measurable_fst.prodMk hp)))

theorem Policy.run_joint_measurable (P : Policy Seed S X Y Z)
    (o : Ω → X → Y) (r : Ω → X → Z)
    (ho : Measurable (fun q : Ω × X => o q.1 q.2))
    (hr : Measurable (fun q : Ω × X => r q.1 q.2)) (n : ℕ) :
    Measurable (fun q : Ω × Seed => P.run (o q.1) (r q.1) n q.2) := by
  induction n with
  | zero => exact P.initial_measurable.comp measurable_snd
  | succ n ih => exact (P.step_joint_measurable o r ho hr).comp (measurable_fst.prodMk ih)

theorem Policy.output_joint_measurable (P : Policy Seed S X Y Z)
    (o : Ω → X → Y) (r : Ω → X → Z)
    (ho : Measurable (fun q : Ω × X => o q.1 q.2))
    (hr : Measurable (fun q : Ω × X => r q.1 q.2)) (n : ℕ) :
    Measurable (fun q : Ω × Seed => P.output (P.run (o q.1) (r q.1) n q.2)) :=
  P.output_measurable.comp (P.run_joint_measurable o r ho hr n)

theorem Policy.ordinaryCount_joint_measurable (P : Policy Seed S X Y Z)
    (o : Ω → X → Y) (r : Ω → X → Z)
    (ho : Measurable (fun q : Ω × X => o q.1 q.2))
    (hr : Measurable (fun q : Ω × X => r q.1 q.2)) (n : ℕ) :
    Measurable (fun q : Ω × Seed => P.ordinaryCount (o q.1) (r q.1) n q.2) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite ((P.mode_measurable.comp (P.run_joint_measurable o r ho hr i))
    (measurableSet_singleton 2)) measurable_const measurable_const

theorem Policy.richCount_joint_measurable (P : Policy Seed S X Y Z)
    (o : Ω → X → Y) (r : Ω → X → Z)
    (ho : Measurable (fun q : Ω × X => o q.1 q.2))
    (hr : Measurable (fun q : Ω × X => r q.1 q.2)) (n : ℕ) :
    Measurable (fun q : Ω × Seed => P.richCount (o q.1) (r q.1) n q.2) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite ((P.mode_measurable.comp (P.run_joint_measurable o r ho hr i))
    (measurableSet_singleton 3)) measurable_const measurable_const

end GradientHessian.Machine
