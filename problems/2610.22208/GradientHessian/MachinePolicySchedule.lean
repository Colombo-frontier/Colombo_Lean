import GradientHessian.MachineJointRun
import GradientHessian.ControllerOptionalTrajectory
import GradientHessian.ControllerPolicyTrace

/-! The original policy query trace is an actual measurable optional
schedule, jointly in raw objective parameters and its independent private
seed. An output entry contributes exactly one final ordinary point. -/

noncomputable section
namespace GradientHessian.MachinePolicySchedule
open Classical Machine ComparisonController ControllerOptionalTrajectory ControllerMeasurable

variable {Ω Seed S X Y Z : Type*} [MeasurableSpace Ω]
  [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def entry (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z) (n : ℕ) :
    (Ω × Seed → Bool) × (Ω × Seed → Pending X) :=
  (fun q => decide (P.mode (P.run (o q.1) (r q.1) n q.2)=2 ∨ P.mode (P.run (o q.1) (r q.1) n q.2)=3),
   fun q => ⟨P.point (P.run (o q.1) (r q.1) n q.2),
     if P.mode (P.run (o q.1) (r q.1) n q.2)=2 then .ordinary else .rich⟩)

def entries (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z) (n : ℕ) : Schedule (Ω × Seed) X :=
  (List.range n).map (entry P o r)

def outputEntry (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z) (n : ℕ) :
    (Ω × Seed → Bool) × (Ω × Seed → Pending X) :=
  (fun _ => true,fun q => ⟨P.output (P.run (o q.1) (r q.1) n q.2),.ordinary⟩)

def withOutput (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z) (n : ℕ) : Schedule (Ω × Seed) X :=
  entries P o r n ++ [outputEntry P o r n]

omit [MeasurableSpace Ω] [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z] in
theorem selected_append (es fs : Schedule Ω X) (w : Ω) :
    selected (es++fs) w=selected es w++selected fs w := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases hb : e.1 w <;> simp only [List.cons_append,selected,hb,Bool.false_eq_true,ite_false,ite_true,ih]

theorem entry_selected (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z) (n : ℕ) (q : Ω × Seed) :
    selected [entry P o r n] q=ControllerPolicyTrace.selected P (P.run (o q.1) (r q.1) n q.2) := by
  by_cases h2 : P.mode (P.run (o q.1) (r q.1) n q.2)=2
  · simp [entry,selected,ControllerPolicyTrace.selected,h2]
  · by_cases h3 : P.mode (P.run (o q.1) (r q.1) n q.2)=3 <;>
      simp [entry,selected,ControllerPolicyTrace.selected,h2,h3]

theorem entries_selected (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z) (n : ℕ) (q : Ω × Seed) :
    selected (entries P o r n) q=ControllerPolicyTrace.trace P (o q.1) (r q.1) n q.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [entries,List.range_succ,List.map_append,List.map_singleton,selected_append,
      entry_selected,ControllerPolicyTrace.trace]
    exact congrArg (fun ps => ps++ControllerPolicyTrace.selected P (P.run (o q.1) (r q.1) n q.2)) ih

theorem withOutput_selected (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z) (n : ℕ) (q : Ω × Seed) :
    selected (withOutput P o r n) q=ControllerPolicyTrace.withOutput P (o q.1) (r q.1) n q.2 := by
  simp only [withOutput,selected_append,entries_selected,outputEntry,selected,ite_true,ControllerPolicyTrace.withOutput]

theorem entry_measurable (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z)
    (ho : Measurable (fun q : Ω × X => o q.1 q.2)) (hr : Measurable (fun q : Ω × X => r q.1 q.2)) (n : ℕ) :
    Measurable (entry P o r n).1 ∧ Measurable (entry P o r n).2 := by
  have hs := P.run_joint_measurable o r ho hr n
  have hm := P.mode_measurable.comp hs
  constructor
  · exact (measurable_of_countable (fun k : Fin 4 => decide (k=2 ∨ k=3))).comp hm
  · exact measurable_pending_mk (P.point_measurable.comp hs)
      ((measurable_of_countable (fun k : Fin 4 => if k=2 then Kind.ordinary else Kind.rich)).comp hm)

theorem entries_measurable (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z)
    (ho : Measurable (fun q : Ω × X => o q.1 q.2)) (hr : Measurable (fun q : Ω × X => r q.1 q.2)) (n : ℕ) :
    IsMeasurable (entries P o r n) := by
  intro e he
  obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp he
  exact entry_measurable P o r ho hr i

theorem withOutput_measurable (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z)
    (ho : Measurable (fun q : Ω × X => o q.1 q.2)) (hr : Measurable (fun q : Ω × X => r q.1 q.2)) (n : ℕ) :
    IsMeasurable (withOutput P o r n) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact entries_measurable P o r ho hr n e he
  · have heq : e=outputEntry P o r n := List.mem_singleton.mp he
    subst e
    exact ⟨measurable_const,measurable_pending_mk (P.output_joint_measurable o r ho hr n) measurable_const⟩

end GradientHessian.MachinePolicySchedule
